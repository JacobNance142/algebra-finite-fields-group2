#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <mutex>
#include <ostream>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>
#include <algebra/finite_fields/modulus.hpp>

namespace algebra {

template<std::uint32_t P, std::size_t K = 1, class ModulusPolicy = FirstEnumeratedIrreducible>
class FiniteField;

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class FiniteFieldElement : public AdditiveOperators<FiniteFieldElement<P, K, ModulusPolicy>>,
                           public MultiplicativeOperators<FiniteFieldElement<P, K, ModulusPolicy>>,
                           public DivisionOperators<FiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    struct CacheKey {
        FiniteFieldElement<P, K, ModulusPolicy> firstOperand;
        FiniteFieldElement<P, K, ModulusPolicy> secondOperand;

        bool operator==(const CacheKey& other) const {
            return firstOperand == other.firstOperand && secondOperand == other.secondOperand;
        };
    };
    using parent_type = FiniteField<P, K, ModulusPolicy>;
    using algebra = FieldDescriptor;
    using coefficient_type = PrimeFieldElement<P>;
    using polynomial_type = Polynomial<coefficient_type>;
private:
    mutable polynomial_type value_;
    std::uint16_t index_ = 0;
    mutable bool value_ready_ = false;
    struct Reduced {};
    struct CachedIndex {};

    FiniteFieldElement(polynomial_type value, Reduced) : value_(std::move(value)), value_ready_(true) {}
    FiniteFieldElement(std::uint16_t index, CachedIndex) : index_(index) {}
    inline static std::vector<std::uint16_t> addition_table_{};
    inline static std::vector<std::uint16_t> multiplication_table_{};
    inline static std::vector<std::uint16_t> reciprocal_table_{};
    inline static std::vector<std::uint16_t> negation_table_{};
    inline static bool caches_ready_{false};

    std::uint16_t index_from_value() const {
        std::uint64_t result = 0;
        std::uint64_t mult = 1;
        for (std::size_t i = 0; i < K; i++) {
            result += value_.coefficient(i).representative() * mult;
            mult *= P;
        }
        return static_cast<std::uint16_t>(result);
    }

    void ensure_value() const {
        if (value_ready_) {
            return;
        }
        polynomial_type value;
        auto index = static_cast<std::uint64_t>(index_);
        for (std::size_t i = 0; i < K; ++i) {
            value.set_coefficient(i, coefficient_type::from_index(index % P));
            index /= P;
        }
        value_ = std::move(value);
        value_ready_ = true;
    }

    static FiniteFieldElement from_cached_index(std::uint16_t index) {
        return FiniteFieldElement(index, CachedIndex{});
    }

public:
    FiniteFieldElement() {
        static_cast<void>(parent_type::modulus());
    }

    std::uint64_t index() const {
        return index_;
    }

    static FiniteFieldElement from_polynomial(const polynomial_type& value) {
        polynomial_type remainder = value % parent_type::modulus();
        FiniteFieldElement element(std::move(remainder), Reduced{});
        element.index_ = element.index_from_value();
        return element;
    }

    static FiniteFieldElement from_coefficients(std::initializer_list<std::int64_t> values) {
        polynomial_type value;
        std::size_t index = 0;
        for (const auto coefficient : values) {
            value.set_coefficient(index++, coefficient_type::from_integer(coefficient));
        }
        return from_polynomial(value);
    }

    static FiniteFieldElement from_integer(std::int64_t value) {
        return from_polynomial(polynomial_type{coefficient_type::from_integer(value)});
    }

    static FiniteFieldElement from_index(std::uint64_t index) {
        if (index >= parent_type::cardinality()) {
            throw std::out_of_range("Finite field element index is out of range");
        }
        if (caches_ready_) {
            return from_cached_index(static_cast<std::uint16_t>(index));
        }
        polynomial_type value;
        for (std::size_t i = 0; i < K; ++i) {
            value.set_coefficient(i, coefficient_type::from_index(index % P));
            index /= P;
        }
        return from_polynomial(value);
    }

    static void fill_caches()
    {
        static std::once_flag flag;
        std::call_once(flag, [] {
            const auto cardinality = parent_type::cardinality();
            addition_table_.resize(cardinality * cardinality);
            multiplication_table_.resize(cardinality * cardinality);
            reciprocal_table_.resize(cardinality);
            negation_table_.resize(cardinality);
            for (std::uint64_t i = 0; i < cardinality; i++)
            {
                const auto a = from_index(i);
                negation_table_[i] = static_cast<std::uint16_t>(a.negate().index_);
                if (i != 0)
                {
                    reciprocal_table_[i] = static_cast<std::uint16_t>(a.reciprocal().index_);
                }
                for (std::uint64_t j = 0; j < cardinality; j++)
                {
                    const auto b = from_index(j);
                    const auto slot = i * cardinality + j;
                    addition_table_[slot] = static_cast<std::uint16_t>(
                        from_polynomial(a.value_.add(b.value_)).index_);
                    multiplication_table_[slot] = static_cast<std::uint16_t>(
                        from_polynomial(a.value_.multiply(b.value_)).index_);
                }
            }
            caches_ready_ = true;
        });
    }

    static FiniteFieldElement zero() {
        return FiniteFieldElement{};
    }

    static FiniteFieldElement one() {
        return from_integer(1);
    }

    FiniteFieldElement add(const FiniteFieldElement& other) const {
        if (caches_ready_) {
            const auto cardinality = parent_type::cardinality();
            return from_cached_index(addition_table_[index_ * cardinality + other.index_]);
        }
        ensure_value();
        other.ensure_value();
        return from_polynomial(value_.add(other.value_));
    }

    FiniteFieldElement negate() const {
        if (caches_ready_) {
            return from_cached_index(negation_table_[index_]);
        }
        ensure_value();
        return from_polynomial(value_.negate());
    }

    FiniteFieldElement multiply(const FiniteFieldElement& other) const {
        if (caches_ready_) {
            const auto cardinality = parent_type::cardinality();
            return from_cached_index(multiplication_table_[index_ * cardinality + other.index_]);
        }
        ensure_value();
        other.ensure_value();
        return from_polynomial(value_.multiply(other.value_));
    }

    FiniteFieldElement reciprocal() const {
        if (is_zero()) {
            throw std::domain_error("Zero has no reciprocal");
        }
        if (caches_ready_) {
            return from_cached_index(reciprocal_table_[index_]);
        }
        ensure_value();
        polynomial_type previous_remainder = parent_type::modulus();
        polynomial_type remainder = value_;
        polynomial_type previous_coefficient = polynomial_type::zero();
        polynomial_type coefficient = polynomial_type::one();
        while (!remainder.is_zero()) {
            auto division = previous_remainder.divmod(remainder);
            polynomial_type next_remainder = std::move(division.second);
            polynomial_type next_coefficient =
                previous_coefficient - division.first.multiply(coefficient);
            previous_remainder = std::move(remainder);
            remainder = std::move(next_remainder);
            previous_coefficient = std::move(coefficient);
            coefficient = std::move(next_coefficient);
        }
        if (previous_remainder.degree() != 0) {
            throw std::logic_error("The element is not invertible for this modulus");
        }
        const coefficient_type scale = previous_remainder.coefficient(0).reciprocal();
        return from_polynomial(previous_coefficient.scale_left(scale));
    }

    bool is_zero() const {
        return index_ == 0;
    }

    bool is_one() const {
        return index_ == 1;
    }

    coefficient_type coefficient(std::size_t index) const {
        if (index >= K) {
            throw std::out_of_range("Finite field coefficient index is out of range");
        }
        ensure_value();
        return value_.coefficient(index);
    }

    std::array<coefficient_type, K> coefficients() const {
        std::array<coefficient_type, K> result{};
        for (std::size_t i = 0; i < K; ++i) {
            ensure_value();
        result[i] = value_.coefficient(i);
        }
        return result;
    }

    const polynomial_type& representative() const {
        ensure_value();
        return value_;
    }

    const parent_type& parent() const {
        static const parent_type instance;
        return instance;
    }

    bool operator==(const FiniteFieldElement& other) const {
        return index_ == other.index_;
    }

    friend std::ostream& operator<<(std::ostream& out, const FiniteFieldElement& value) {
        value.ensure_value();
        return out << value.value_;
    }
};

template<std::uint32_t P, std::size_t K, class ModulusPolicy>
class FiniteField : public FieldStructure<FiniteFieldElement<P, K, ModulusPolicy>> {
    static_assert(is_prime(P));
    static_assert(K > 0);

public:
    using Element = FiniteFieldElement<P, K, ModulusPolicy>;
    using Base = PrimeField<Cyclic<P>>;
    using PolynomialType = typename Element::polynomial_type;
    static constexpr std::uint32_t characteristic = P;
    static constexpr std::size_t extension_degree = K;

    FiniteField() {
        initialize();
    }

    static const PolynomialType& modulus() {
        static const PolynomialType value = [] {
            PolynomialType candidate = ModulusPolicy::template polynomial<P, K>();
            if (candidate.degree() != K || !candidate.leading_coefficient().is_one() ||
                !is_irreducible(candidate)) {
                throw std::invalid_argument("The modulus must be monic and irreducible with degree K");
            }
            return candidate;
        }();
        return value;
    }

    static void initialize() {
        static_cast<void>(modulus());
        Element::fill_caches();
    }

    static std::uint64_t cardinality() {
        return checked_power(P, K);
    }

    static Element element(std::initializer_list<std::int64_t> values) {
        return Element::from_coefficients(values);
    }

    static Element element(std::int64_t value) {
        return Element::from_integer(value);
    }

    static Element zero() {
        return Element::zero();
    }

    static Element one() {
        return Element::one();
    }

    static Element alpha() {
        return Element::from_polynomial(PolynomialType::variable());
    }
};

}
