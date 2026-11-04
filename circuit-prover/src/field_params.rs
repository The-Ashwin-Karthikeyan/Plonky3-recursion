//! Utilities for extracting extension field parameters.
//!
//! Glossary:
//! - `F`: Base field (BabyBear/KoalaBear/Goldilocks) that extension fields are built over.
//! - `EF`: Element field for circuit traces. If `EF = F`, there is no binomial parameter. If
//!   `EF = BinomialExtensionField<F, D>`, then there is a binomial parameter `W` with `x^D = W`.
//!   If `EF` is a cubic or quintic trinomial extension, there is no `W` and the ALU uses the
//!   trinomial reduction for that degree.
//! - `D`: Element-field extension degree.
//!
//! Provides traits to dynamically determine binomial extension parameters
//! from field types at runtime, supporting both base fields and extension fields.

use p3_field::Field;
use p3_field::extension::{
    BinomialExtensionField, BinomiallyExtendable, CubicTrinomialExtendable,
    CubicTrinomialExtensionField, QuinticTrinomialExtendable, QuinticTrinomialExtensionField,
};

/// Extract binomial parameters from field types.
///
/// Enables runtime detection of extension field parameters without
/// requiring compile-time knowledge of the field structure.
pub trait ExtractBinomialW<F: Field> {
    /// Extract the binomial parameter W for the current extension degree (e.g., x^D = W).
    /// Returns None for base fields, Some(W) for supported binomial extensions.
    fn extract_w() -> Option<F>;

    /// When true, the ALU uses the trinomial reduction for this degree instead of a binomial
    /// `x^D = W`: `X^3 - X - 1` for `D == 3`, `X^5 + X^2 - 1` for `D == 5`.
    ///
    /// Only trinomial extensions return true; this is the value recorded in the proof's
    /// `alu_quintic_trinomial` flag.
    fn alu_is_trinomial() -> bool {
        false
    }
}

/// When the element field is the same as the base field (no extension), there's no binomial parameter W.
impl<F> ExtractBinomialW<F> for F
where
    F: Field,
{
    fn extract_w() -> Option<F> {
        None
    }
}

/// Binomial extension fields (for any supported degree D) provide their parameter W.
impl<F, const D: usize> ExtractBinomialW<F> for BinomialExtensionField<F, D>
where
    F: Field + BinomiallyExtendable<D>,
{
    fn extract_w() -> Option<F> {
        Some(F::W)
    }
}

impl<F> ExtractBinomialW<F> for QuinticTrinomialExtensionField<F>
where
    F: Field + QuinticTrinomialExtendable,
{
    fn extract_w() -> Option<F> {
        None
    }

    fn alu_is_trinomial() -> bool {
        true
    }
}

impl<F> ExtractBinomialW<F> for CubicTrinomialExtensionField<F>
where
    F: Field + CubicTrinomialExtendable,
{
    fn extract_w() -> Option<F> {
        None
    }

    fn alu_is_trinomial() -> bool {
        true
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::extension::{
        BinomialExtensionField, CubicTrinomialExtensionField, QuinticTrinomialExtensionField,
    };
    use p3_goldilocks::Goldilocks;
    use p3_koala_bear::KoalaBear;

    use super::*;

    #[test]
    fn test_base_field_returns_none() {
        assert!(<BabyBear as ExtractBinomialW<BabyBear>>::extract_w().is_none());
    }

    #[test]
    fn test_binomial_extension_returns_some() {
        assert!(
            <BinomialExtensionField<BabyBear, 4> as ExtractBinomialW<BabyBear>>::extract_w()
                .is_some()
        );
    }

    #[test]
    fn test_quintic_extension_returns_none() {
        assert!(
            <QuinticTrinomialExtensionField<KoalaBear> as ExtractBinomialW<KoalaBear>>::extract_w()
                .is_none()
        );
    }

    #[test]
    fn test_quintic_is_trinomial_true() {
        assert!(
            <QuinticTrinomialExtensionField<KoalaBear> as ExtractBinomialW<KoalaBear>>::alu_is_trinomial()
        );
    }

    #[test]
    fn test_base_field_not_trinomial() {
        assert!(!<BabyBear as ExtractBinomialW<BabyBear>>::alu_is_trinomial());
    }

    #[test]
    fn test_binomial_extension_not_trinomial() {
        assert!(!<BinomialExtensionField<BabyBear, 4> as ExtractBinomialW<
            BabyBear,
        >>::alu_is_trinomial());
    }

    #[test]
    fn test_cubic_extension_returns_none() {
        assert!(
            <CubicTrinomialExtensionField<Goldilocks> as ExtractBinomialW<Goldilocks>>::extract_w()
                .is_none()
        );
    }

    #[test]
    fn test_cubic_is_trinomial_true() {
        assert!(
            <CubicTrinomialExtensionField<Goldilocks> as ExtractBinomialW<Goldilocks>>::alu_is_trinomial()
        );
    }

    #[test]
    fn test_goldilocks_quadratic_not_trinomial() {
        assert!(!<BinomialExtensionField<Goldilocks, 2> as ExtractBinomialW<
            Goldilocks,
        >>::alu_is_trinomial());
    }
}
