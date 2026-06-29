import Mathlib

/-!
# Invariants of `p`-adic fields: the field and its normalized valuation

This file begins the formalization of the blueprint
`numina/blueprints/padicinv/padicinv.tex` (Invariants of a finite extension of
`p`-adic fields). It covers the first two items:

* `PadicField` (blueprint `def:padic-field`): a `p`-adic field is a finite
  extension `K / ℚ_[p]`.
* `PadicField.normalizedValuation` (the `v_K` of `def:padic-field`): the
  normalized valuation `K → ℤᵐ⁰` attached to the unique maximal ideal of the
  ring of integers `𝒪_K`.

The ring of integers `𝒪_K` is the integral closure of `ℤ_[p]` in `K`. That it is
a (complete) discrete valuation ring is blueprint `prop:padic-is-dvf`; it is the
only fact still left as `sorry` here, and it is exactly what licenses the
construction of the normalized valuation. Everything else is supplied by the
char-`0` separability of `K / ℚ_[p]` and the Dedekind / fraction-ring API for
integral closures in finite extensions.
-/

noncomputable section

open scoped Multiplicative

/-- A *`p`-adic field* is a finite extension `K / ℚ_[p]`. -/
class PadicField (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] : Prop
    extends Module.Finite ℚ_[p] K

namespace PadicField

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [PadicField p K]

/-- The canonical `ℤ_[p]`-algebra structure on a `p`-adic field, obtained by
restricting scalars along `ℤ_[p] → ℚ_[p]`. -/
instance instAlgebraPadicInt : Algebra ℤ_[p] K :=
  ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

instance instIsScalarTower : IsScalarTower ℤ_[p] ℚ_[p] K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The ring of integers `𝒪_K` of a `p`-adic field `K`: the integral closure of
`ℤ_[p]` (the integers of `ℚ_[p]`) in `K`. -/
def ringOfIntegers : Subalgebra ℤ_[p] K := integralClosure ℤ_[p] K

@[inherit_doc] scoped notation "𝒪[" K "]" => PadicField.ringOfIntegers _ K

instance : IsFractionRing (ringOfIntegers p K) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] K

/-- The ring of integers of a `p`-adic field is a discrete valuation ring.

This is blueprint `prop:padic-is-dvf` (a `p`-adic field is a complete DVF):
the integral closure of the complete DVR `ℤ_[p]` in a finite extension is again
a complete DVR. It is left as the next target to prove; it is the single fact on
which the normalized valuation below rests. -/
instance instIsDiscreteValuationRing :
    IsDiscreteValuationRing (ringOfIntegers p K) := by
  sorry

/-- The unique maximal ideal `𝔪_K` of `𝒪_K`, packaged as the height-one prime of
the Dedekind domain `𝒪_K` whose adic valuation is the normalized valuation. -/
def maximalSpectrum : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers p K) where
  asIdeal := IsLocalRing.maximalIdeal (ringOfIntegers p K)
  isPrime := (IsLocalRing.maximalIdeal.isMaximal (ringOfIntegers p K)).isPrime
  ne_bot := by
    intro h
    exact IsDiscreteValuationRing.not_isField (ringOfIntegers p K)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)

/-- The *normalized valuation* `v_K : K → ℤᵐ⁰` of a `p`-adic field `K`: the
`𝔪_K`-adic valuation of the ring of integers, extended to `K = Frac 𝒪_K`. It is
normalized so that a uniformizer has valuation the generator of `Multiplicative ℤ`
(equivalently `v_K(K^×) = ℤ` additively). -/
def normalizedValuation : Valuation K (WithZero (Multiplicative ℤ)) :=
  (maximalSpectrum p K).valuation K

end PadicField
