import Mathlib
-- Adjust this import to the module that defines `PadicField` (the file you shared),
-- likely `LeanBridge.PadicInv` given the blueprint path `numina/blueprints/padicinv/`.
import LeanBridge.PadicInv

/-!
# Concrete test cases for `p`-adic field invariants (issue #63)

The three concrete extensions from the issue, built explicitly as
`ℚ_p[X]/(f) = AdjoinRoot f`:

1. **Unramified** `ℚ_p[X]/(g)` for `g` a lift of an irreducible degree-`n`
   polynomial mod `p`  →  `e = 1`, `f = n = [L:K]`, `d = 0`.
2. **Totally tamely ramified** `ℚ_p(p^{1/e}) = ℚ_p[X]/(X^e − p)` (Eisenstein)
   →  `f = 1`, `e = [L:K]`, and `d = e − 1` when `p ∤ e`.
3. **Wildly ramified** `ℚ_2(√2) = ℚ_2[X]/(X² − 2)`  →  `p = 2 ∣ e = 2`, wild,
   with `δ = 3`, `d = 3`.

What is `sorry`'d and why:
* `Fact (Irreducible …)` — true by Eisenstein / reduction-mod-`p`, proof omitted.
* `Module.Finite` instances — true (`AdjoinRoot` of a nonzero poly over a field
  is finite), proof omitted.
* the numeric invariant theorems (`e`, `f`, `d`, `δ`) — these are genuine
  ramification computations not yet available in Mathlib.

NOTE: written against the API in the shared file, NOT compiled here; instance /
lemma names may need small adjustments.
-/

open scoped PadicField
open Polynomial PadicField PadicField.Extension

noncomputable section

namespace PadicFieldTests

/-- `ℚ_p` is itself a `p`-adic field; needed as the base `K = ℚ_p`. -/
instance instPadicFieldSelf (p : ℕ) [Fact p.Prime] : PadicField ℚ_[p] p :=
  PadicField.mk

/-- The trivial scalar tower `ℚ_p ⊆ ℚ_p ⊆ L` used for every extension of `ℚ_p`. -/
instance instTowerSelf (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra ℚ_[p] L] :
    IsScalarTower ℚ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq fun x => by simp

/-! ## Case 1 — unramified `ℚ_p[X]/(g)`  (`e = 1`, `f = n`, `d = 0`)

Concretely: take `g : ℚ_p[X]` monic of degree `n` that reduces mod `p` to an
irreducible polynomial over the residue field `𝔽_p`. Then `L = ℚ_p[X]/(g)` is the
unramified extension of degree `n` (`e = 1`, residue field grows to degree `n`).
Here `g` is carried as an explicit polynomial with its irreducibility as a `Fact`. -/
section Unramified

variable {p : ℕ} [Fact p.Prime] (n : ℕ)
  (g : Polynomial ℚ_[p]) [Fact (Irreducible g)]

/-- `L = ℚ_p[X]/(g)`, the unramified extension of degree `n = deg g`. -/
abbrev Unr : Type _ := AdjoinRoot g

instance : Module.Finite ℚ_[p] (Unr g) :=
  PowerBasis.finite (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible g)))

instance : PadicField (Unr g) p := PadicField.mk

/-- Residue degree is the full degree: `f = n = [L:K]`. -/
theorem Unr_inertiaDeg (hg : g.natDegree = n) :
    inertiaDeg ℚ_[p] (Unr g) = n := sorry

/-- Ramification index is `1`. -/
theorem Unr_ramificationIdx : ramificationIdx ℚ_[p] (Unr g) = 1 := sorry

/-- `L/ℚ_p` is unramified. -/
theorem Unr_isUnramified : IsUnramified ℚ_[p] (Unr g) := Unr_ramificationIdx g

/-- Discriminant exponent vanishes: `d = 0`. -/
theorem Unr_discriminantExponent : discriminantExponent ℚ_[p] (Unr g) = 0 :=
  (discExponent_eq_zero_iff_unramified ℚ_[p] (Unr g)).mpr (Unr_isUnramified g)

end Unramified

/-! ## Case 2 — `ℚ_p(p^{1/e}) = ℚ_p[X]/(Xᵉ − p)`  (`d = e − 1`)

Eisenstein, hence irreducible for `e ≥ 1`; the extension is totally ramified
(`f = 1`, `e = [L:K]`) and tame when `p ∤ e`, giving `d = e − 1`. -/
section Eisenstein

variable {p : ℕ} [Fact p.Prime] (e : ℕ)

/-- The Eisenstein polynomial `Xᵉ − p ∈ ℚ_p[X]`. -/
def eisenstein : Polynomial ℚ_[p] := X ^ e - C (p : ℚ_[p])

variable [Fact (Irreducible (eisenstein (p := p) e))]

/-- `ℚ_p(p^{1/e}) := ℚ_p[X]/(Xᵉ − p)`. -/
abbrev Qpe : Type _ := AdjoinRoot (eisenstein (p := p) e)

instance : Module.Finite ℚ_[p] (Qpe (p := p) e) :=
  PowerBasis.finite
    (AdjoinRoot.powerBasis
      (Irreducible.ne_zero (Fact.out : Irreducible (eisenstein (p := p) e))))

instance : PadicField (Qpe (p := p) e) p := PadicField.mk

/-- `[ℚ_p(p^{1/e}) : ℚ_p] = e`. -/
theorem Qpe_finrank : Module.finrank ℚ_[p] (Qpe (p := p) e) = e := by
  rw [PowerBasis.finrank
      (AdjoinRoot.powerBasis
        (Irreducible.ne_zero (Fact.out : Irreducible (eisenstein (p := p) e)))),
    AdjoinRoot.powerBasis_dim]
  simpa [eisenstein] using
    (Polynomial.natDegree_X_pow_sub_C (R := ℚ_[p]) (n := e) (r := (p : ℚ_[p])))

/-- Totally ramified: `f = 1`. -/
theorem Qpe_inertiaDeg : inertiaDeg ℚ_[p] (Qpe (p := p) e) = 1 := sorry

/-- Ramification index is the full degree: `e = [L:K]`. -/
theorem Qpe_ramificationIdx : ramificationIdx ℚ_[p] (Qpe (p := p) e) = e := sorry

/-- Tame when `p ∤ e`. -/
theorem Qpe_isTamelyRamified (hpe : ¬ (p ∣ e)) :
    IsTamelyRamified ℚ_[p] (Qpe (p := p) e) := by
  show ¬ (p ∣ ramificationIdx ℚ_[p] (Qpe (p := p) e))
  rw [Qpe_ramificationIdx e]; exact hpe

/-- The headline identity: `d = e − 1` for `ℚ_p(p^{1/e})` with `p ∤ e`.
Derived from `discExponent_tame` (`d = f·(e−1)`) with `f = 1`. -/
theorem Qpe_discriminantExponent (hpe : ¬ (p ∣ e)) :
    discriminantExponent ℚ_[p] (Qpe (p := p) e) = e - 1 := by
  rw [discExponent_tame ℚ_[p] (Qpe (p := p) e) (Qpe_isTamelyRamified e hpe),
      Qpe_inertiaDeg e, one_mul, Qpe_ramificationIdx e]

end Eisenstein

/-! ## Case 3 — wildly ramified `ℚ_2(√2) = ℚ_2[X]/(X² − 2)`

`X² − 2` is Eisenstein at `2`, so this is ramified of degree `2`; since `p = 2 ∣ 2`
it is wildly ramified. One computes `δ = v_L(2√2) = 3` and `d = f·δ = 3`. -/
section WildQ2

/-- `X² − 2 ∈ ℚ_2[X]`. -/
def sqrtTwoPoly : Polynomial ℚ_[2] := X ^ 2 - C (2 : ℚ_[2])

instance : Fact (Irreducible sqrtTwoPoly) := ⟨by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [sqrtTwoPoly]
  · intro x hx
    have hx_sq : x ^ 2 = (2 : ℚ_[2]) := by
      apply sub_eq_zero.mp
      simpa [sqrtTwoPoly, Polynomial.IsRoot.def] using hx
    have hv : (2 : ℤ) * Padic.valuation x = 1 := by
      have h := congrArg (fun y : ℚ_[2] => Padic.valuation y) hx_sq
      simpa using h
    omega⟩

/-- `ℚ_2(√2) := ℚ_2[X]/(X² − 2)`. -/
abbrev Q2sqrt2 : Type _ := AdjoinRoot sqrtTwoPoly

instance : Module.Finite ℚ_[2] Q2sqrt2 :=
  PowerBasis.finite
    (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible sqrtTwoPoly)))

instance : PadicField Q2sqrt2 2 := inferInstance

/-- `[ℚ_2(√2) : ℚ_2] = 2`. -/
theorem Q2sqrt2_finrank : Module.finrank ℚ_[2] Q2sqrt2 = 2 := by
  rw [PowerBasis.finrank
      (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible sqrtTwoPoly))),
    AdjoinRoot.powerBasis_dim]
  simp [sqrtTwoPoly]

/-- Ramified of degree `2`: `e = 2`. -/
theorem Q2sqrt2_ramificationIdx : ramificationIdx ℚ_[2] Q2sqrt2 = 2 := sorry

/-- Totally ramified: `f = 1`. -/
theorem Q2sqrt2_inertiaDeg : inertiaDeg ℚ_[2] Q2sqrt2 = 1 := sorry

/-- Wildly ramified: `2 ∣ e`. -/
theorem Q2sqrt2_isWildlyRamified : IsWildlyRamified ℚ_[2] Q2sqrt2 := by
  show (2 : ℕ) ∣ ramificationIdx ℚ_[2] Q2sqrt2
  simp [Q2sqrt2_ramificationIdx]

/-- Not tamely ramified (consistency check against the wild statement). -/
theorem Q2sqrt2_not_tame : ¬ IsTamelyRamified ℚ_[2] Q2sqrt2 := by
  have h := Q2sqrt2_isWildlyRamified
  unfold IsWildlyRamified at h
  exact not_not_intro h

/-- Different exponent `δ = 3` (from `v_L(f'(√2)) = v_L(2√2) = 3`). -/
theorem Q2sqrt2_differentExponent : differentExponent ℚ_[2] Q2sqrt2 = 3 := sorry

/-- Discriminant exponent `d = f·δ = 3`. -/
theorem Q2sqrt2_discriminantExponent : discriminantExponent ℚ_[2] Q2sqrt2 = 3 := by
  rw [discExponent_eq_inertiaDeg_mul_differentExponent ℚ_[2] Q2sqrt2,
      Q2sqrt2_inertiaDeg, Q2sqrt2_differentExponent]

/-- Strictly wild: `δ = 3 > 1 = e − 1`, i.e. the tame equality fails. -/
theorem Q2sqrt2_wild_strict :
    ramificationIdx ℚ_[2] Q2sqrt2 - 1 < differentExponent ℚ_[2] Q2sqrt2 := by
  rw [Q2sqrt2_ramificationIdx, Q2sqrt2_differentExponent]
  omega

end WildQ2

end PadicFieldTests

end
