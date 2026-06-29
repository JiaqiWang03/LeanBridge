import Mathlib

/-!
# Invariants of `p`-adic fields: the field and its ring of integers

This file begins the formalization of the blueprint
`numina/blueprints/padicinv/padicinv.tex` (Invariants of a finite extension of
`p`-adic fields):

* `PadicField` (blueprint `def:padic-field`): a `p`-adic field is a finite
  extension `K / ℚ_[p]`.
* `PadicField.ringOfIntegers` (`𝒪_K`): the integral closure of `ℤ_[p]` in `K`,
  together with `IsFractionRing 𝒪_K K`.
* `PadicField.instIsDiscreteValuationRing` (blueprint `prop:padic-is-dvf`):
  `𝒪_K` is a discrete valuation ring. This is the only fact left as `sorry`.

Once `𝒪_K` is a DVR it is in particular a local Dedekind domain with fraction
field `K`, so the normalized valuation `v_K : K → ℤᵐ⁰` of `def:padic-field` is
just Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuation` for the maximal
ideal of `𝒪_K`; no dedicated wrapper is introduced here.
-/

noncomputable section

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

/-- The ramification index `e(K / ℚ_[p])` of a `p`-adic field over `ℚ_[p]`,
i.e. the ramification index of the maximal ideal `(p)` of `ℤ_[p]` in `𝒪_K`.
This is the absolute ramification index used in `def:base-absolute`. -/
def ramificationIdxOverQp : ℕ :=
  Ideal.ramificationIdx (R := ℤ_[p]) (S := ringOfIntegers p K)
    (IsLocalRing.maximalIdeal ℤ_[p]) (IsLocalRing.maximalIdeal (ringOfIntegers p K))

/-!
## The ramification index of an extension `L / K` (blueprint §1.2, §1.3)
-/

namespace Extension

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [PadicField p L]
  [Algebra K L] [Module.Finite K L] [IsScalarTower ℚ_[p] K L]

/-- `ℤ_[p]` acts on `L` through `K`, compatibly with its action through `ℚ_[p]`. -/
instance instIsScalarTowerPadicInt : IsScalarTower ℤ_[p] K L :=
  IsScalarTower.of_algebraMap_eq fun x => by
    have hK : algebraMap ℤ_[p] K x = algebraMap ℚ_[p] K (algebraMap ℤ_[p] ℚ_[p] x) := rfl
    have hL : algebraMap ℤ_[p] L x = algebraMap ℚ_[p] L (algebraMap ℤ_[p] ℚ_[p] x) := rfl
    rw [hK, hL, IsScalarTower.algebraMap_apply ℚ_[p] K L]

/-- The inclusion `𝒪_K → 𝒪_L` of rings of integers induced by `K → L`: an
element integral over `ℤ_[p]` stays integral after embedding into `L`. -/
def ringOfIntegersMap : ringOfIntegers p K →+* ringOfIntegers p L where
  toFun x := ⟨algebraMap K L (x : K), by
    have hx : IsIntegral ℤ_[p] (x : K) := x.2
    have h2 := hx.map (IsScalarTower.toAlgHom ℤ_[p] K L)
    rwa [IsScalarTower.toAlgHom_apply] at h2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

/-- The `ℤ_[p]`-algebra structure on the pair `𝒪_K → 𝒪_L`, used to form the
relative ramification index. -/
instance instAlgebraRingOfIntegers : Algebra (ringOfIntegers p K) (ringOfIntegers p L) :=
  (ringOfIntegersMap p K L).toAlgebra

/-- The *ramification index* `e(L / K)` of an extension of `p`-adic fields
(blueprint `def:ramification-index`): the ramification index of the maximal
ideal `𝔪_K` of `𝒪_K` in `𝒪_L`. Equivalently `v_L(π_K) = e`, `𝔪_K 𝒪_L = 𝔪_L ^ e`. -/
def ramificationIdx : ℕ :=
  Ideal.ramificationIdx (R := ringOfIntegers p K) (S := ringOfIntegers p L)
    (IsLocalRing.maximalIdeal (ringOfIntegers p K))
    (IsLocalRing.maximalIdeal (ringOfIntegers p L))

/-- The *wild ramification exponent* `w` of `L / K` (blueprint `def:tame-wild`):
the exponent of `p` in `e`, so that `e = p ^ w * e_tame` with `p ∤ e_tame`. -/
def wildRamificationExponent : ℕ := (ramificationIdx p K L).factorization p

/-- The *tame ramification index* `e_tame` of `L / K` (blueprint `def:tame-wild`):
the prime-to-`p` part of `e`. -/
def tameRamificationIndex : ℕ :=
  ramificationIdx p K L / p ^ wildRamificationExponent p K L

/-- `L / K` is *unramified* when `e = 1` (blueprint `def:tame-wild`). -/
def IsUnramified : Prop := ramificationIdx p K L = 1

/-- `L / K` is *ramified* when `e > 1` (blueprint `def:tame-wild`). -/
def IsRamified : Prop := 1 < ramificationIdx p K L

/-- `L / K` is *tamely ramified* when `p ∤ e` (blueprint `def:tame-wild`). -/
def IsTamelyRamified : Prop := ¬ (p : ℕ) ∣ ramificationIdx p K L

/-- `L / K` is *wildly ramified* when `p ∣ e` (blueprint `def:tame-wild`). -/
def IsWildlyRamified : Prop := (p : ℕ) ∣ ramificationIdx p K L

/-- The *base ramification index* `e₀` of `L / K` (blueprint `def:base-absolute`):
the ramification index of `K / ℚ_[p]`. -/
def baseRamificationIdx : ℕ := ramificationIdxOverQp p K

/-- The *absolute ramification index* `e_abs` of `L / K`
(blueprint `def:base-absolute`): the ramification index of `L / ℚ_[p]`. By
transitivity `e_abs = e * e₀`. -/
def absoluteRamificationIdx : ℕ := ramificationIdxOverQp p L

end Extension

end PadicField
