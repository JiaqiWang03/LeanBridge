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

/-- Ramification index is `1`. -/
theorem Unr_ramificationIdx : ramificationIdx ℚ_[p] (Unr g) = 1 := sorry

/-- Residue degree is the full degree: `f = n = [L:K]`. -/
theorem Unr_inertiaDeg (hg : g.natDegree = n) :
    inertiaDeg ℚ_[p] (Unr g) = n := by
  have hfr : Module.finrank ℚ_[p] (Unr g) = n := by
    rw [PowerBasis.finrank
        (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible g))),
      AdjoinRoot.powerBasis_dim]
    exact hg
  have h := ramificationIdx_mul_inertiaDeg ℚ_[p] (Unr g)
  rw [Unr_ramificationIdx g, one_mul, hfr] at h
  exact h

/-- `L/ℚ_p` is unramified. -/
theorem Unr_isUnramified : IsUnramified ℚ_[p] (Unr g) := Unr_ramificationIdx g

/-- Discriminant exponent vanishes: `d = 0`. -/
theorem Unr_discriminantExponent : discriminantExponent ℚ_[p] (Unr g) = 0 :=
  (discExponent_eq_zero_iff_unramified ℚ_[p] (Unr g)).mpr (Unr_isUnramified g)

end Unramified

/-! ## Case 2 — `ℚ_p(p^{1/e}) = ℚ_p[X]/(Xᵉ − p)`  (`d = e − 1`)

Eisenstein, hence irreducible for `e ≥ 1`; the extension is totally ramified
(`f = 1`, `e = [L:K]`) and tame when `p ∤ e`, giving `d = e − 1`. -/
/-! ## Case 2 — `ℚ_p(p^{1/e}) = ℚ_p[X]/(Xᵉ − p)`  (`d = e − 1`) -/
section Eisenstein

variable {p : ℕ} [Fact p.Prime] (e : ℕ) [NeZero e]

/-- The Eisenstein polynomial `Xᵉ − p ∈ ℚ_p[X]`。 -/
def eisenstein : Polynomial ℚ_[p] := X ^ e - C (p : ℚ_[p])

instance : Fact (Irreducible (eisenstein (p := p) e)) := by
  have he : e ≠ 0 := NeZero.ne e
  refine ⟨?_⟩
  -- Integral model: `f₀ = Xᵉ − p ∈ ℤ_[p][X]`, Eisenstein at `𝔪 = (p)`.
  set f₀ : ℤ_[p][X] := X ^ e - C (p : ℤ_[p]) with hf₀
  have hmonic : f₀.Monic := by rw [hf₀]; exact monic_X_pow_sub_C _ he
  have hdeg : f₀.natDegree = e := by rw [hf₀]; exact natDegree_X_pow_sub_C
  have hprim : f₀.IsPrimitive := hmonic.isPrimitive
  have hp_mem : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).pos.ne'
  have hEis : f₀.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p]) := by
    refine ⟨?_, ?_, ?_⟩
    · -- leading coefficient `1 ∉ 𝔪`
      rw [hmonic.leadingCoeff]
      intro h1
      exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · -- every strictly-lower coefficient lies in `𝔪`
      intro n hn
      rw [hdeg] at hn
      rw [hf₀, coeff_sub, coeff_X_pow, coeff_C, if_neg hn.ne, zero_sub]
      by_cases hn0 : n = 0
      · rw [if_pos hn0]; exact (IsLocalRing.maximalIdeal ℤ_[p]).neg_mem hp_mem
      · rw [if_neg hn0, neg_zero]; exact Ideal.zero_mem _
    · -- constant coefficient `−p ∉ 𝔪²`
      rw [hf₀, coeff_sub, coeff_X_pow, coeff_C, if_neg he.symm, if_pos rfl, zero_sub]
      intro hmem
      rw [Ideal.neg_mem_iff, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have key : (p : ℤ_[p]) * ((p : ℤ_[p]) * c) = (p : ℤ_[p]) := by
        have e2 : (p : ℤ_[p]) * ((p : ℤ_[p]) * c) = (p : ℤ_[p]) ^ 2 * c := by ring
        rw [e2, ← hc]
      have hpc1 : (p : ℤ_[p]) * c = 1 := mul_left_cancel₀ hp0 (key.trans (mul_one _).symm)
      exact ((IsLocalRing.mem_maximalIdeal _).mp hp_mem) (IsUnit.of_mul_eq_one c hpc1)
  -- Eisenstein ⇒ irreducible over `ℤ_[p]`.
  have hirr₀ : Irreducible f₀ :=
    hEis.irreducible (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).isPrime hprim
      (by rw [hdeg]; exact Nat.pos_of_ne_zero he)
  -- Descend to `ℚ_[p]` by Gauss's lemma.
  have hmapeq : f₀.map (algebraMap ℤ_[p] ℚ_[p]) = eisenstein (p := p) e := by
    ext n
    simp [hf₀, eisenstein, coeff_sub, coeff_X_pow]
  rw [← hmapeq]
  exact (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirr₀

variable [Fact (Irreducible (eisenstein (p := p) e))]

/-- `ℚ_p(p^{1/e}) := ℚ_p[X]/(Xᵉ − p)`。 -/
abbrev Qpe : Type _ := AdjoinRoot (eisenstein (p := p) e)

instance : Module.Finite ℚ_[p] (Qpe (p := p) e) :=
  PowerBasis.finite
    (AdjoinRoot.powerBasis
      (Irreducible.ne_zero (Fact.out : Irreducible (eisenstein (p := p) e))))

instance : PadicField (Qpe (p := p) e) p := PadicField.mk

omit [NeZero e] in
/-- `[ℚ_p(p^{1/e}) : ℚ_p] = e`。 -/
theorem Qpe_finrank : Module.finrank ℚ_[p] (Qpe (p := p) e) = e := by
  rw [PowerBasis.finrank
      (AdjoinRoot.powerBasis
        (Irreducible.ne_zero (Fact.out : Irreducible (eisenstein (p := p) e)))),
    AdjoinRoot.powerBasis_dim]
  simpa [eisenstein] using
    (Polynomial.natDegree_X_pow_sub_C (R := ℚ_[p]) (n := e) (r := (p : ℚ_[p])))

lemma pow_maximalIdeal_antitone {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] {a b : ℕ} :
    (IsLocalRing.maximalIdeal S) ^ a ≤ (IsLocalRing.maximalIdeal S) ^ b ↔ b ≤ a := by
  exact (Ideal.pow_right_strictAnti (IsLocalRing.maximalIdeal S)
    (IsDiscreteValuationRing.not_a_field S)
    (IsLocalRing.maximalIdeal.isMaximal S).ne_top).le_iff_ge

lemma le_ramificationIdx_of_map_le_pow
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] (p : Ideal R) {n : ℕ}
    (hne : p.map (algebraMap R S) ≠ ⊥)
    (hle : p.map (algebraMap R S) ≤ (IsLocalRing.maximalIdeal S) ^ n) :
    n ≤ Ideal.ramificationIdx p (IsLocalRing.maximalIdeal S) := by
  set P := IsLocalRing.maximalIdeal S with hPdef
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hmapP : p.map (algebraMap R S) = P ^ k := by
    rw [hk, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  have hram : Ideal.ramificationIdx p P = k := by
    apply Ideal.ramificationIdx_spec
    · exact le_of_eq hmapP
    · rw [hmapP]
      intro hcon
      have : k + 1 ≤ k := pow_maximalIdeal_antitone.mp hcon
      omega
  have hnk : n ≤ k := by
    rw [hmapP] at hle
    exact pow_maximalIdeal_antitone.mp hle
  omega

lemma span_pow_le_pow {S : Type*} [CommRing S] {θ : S} {I : Ideal S} (m : ℕ)
    (h : θ ∈ I) : Ideal.span {θ ^ m} ≤ I ^ m := by
  rw [← Ideal.span_singleton_pow]
  have hbase : Ideal.span {θ} ≤ I := (Submodule.span_singleton_le_iff_mem θ I).mpr h
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ]; exact Ideal.mul_mono ih hbase

abbrev pElt (p : ℕ) [Fact p.Prime] : 𝒪 ℚ_[p] := algebraMap ℤ_[p] (𝒪 ℚ_[p]) (p : ℤ_[p])

theorem Qpe_maximalIdeal_eq_span :
    IsLocalRing.maximalIdeal (𝒪 ℚ_[p]) = Ideal.span {pElt p} := by
  have hpmem : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  have hinj : Function.Injective (algebraMap ℤ_[p] (𝒪 ℚ_[p])) := by
    exact FaithfulSMul.algebraMap_injective _ _
  have hsurj : Function.Surjective (algebraMap ℤ_[p] (𝒪 ℚ_[p])) := by
    rintro ⟨x, hx⟩
    have hfr : IsFractionRing ℤ_[p] ℚ_[p] := by infer_instance
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ_[p]) (K := ℚ_[p])).mp hx
    refine ⟨a, Subtype.ext ?_⟩
    exact ha
  let equivOI : ℤ_[p] ≃+* 𝒪 ℚ_[p] :=
    RingEquiv.ofBijective (algebraMap ℤ_[p] (𝒪 ℚ_[p])) ⟨hinj, hsurj⟩
  have hep : equivOI (p : ℤ_[p]) = pElt p := rfl
  have hpElt_mem : pElt p ∈ IsLocalRing.maximalIdeal (𝒪 ℚ_[p]) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hunit_p : IsUnit (p : ℤ_[p]) := by
      have hmap : IsUnit (equivOI.symm (pElt p)) := hu.map equivOI.symm.toMonoidHom
      rwa [← hep, equivOI.symm_apply_apply] at hmap
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hpmem)) hunit_p
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨b, rfl⟩ := hsurj y
    have hb_mem : b ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hbu
      have hunit_y : IsUnit (algebraMap ℤ_[p] (𝒪 ℚ_[p]) b) := hbu.map _
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hy)) hunit_y
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hb_mem
    obtain ⟨c, hc⟩ := hb_mem
    rw [hc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self (pElt p))
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hpElt_mem

theorem Qpe_exists_integral_root : ∃ θ : 𝒪 (Qpe (p := p) e),
      θ ∈ IsLocalRing.maximalIdeal (𝒪 (Qpe (p := p) e)) ∧
      θ ^ e = algebraMap (𝒪 ℚ_[p]) (𝒪 (Qpe (p := p) e)) (pElt p) := by
  let π : Qpe (p := p) e := AdjoinRoot.root (eisenstein (p := p) e)
  have hπe : π ^ e = algebraMap ℚ_[p] (Qpe (p := p) e) (p : ℚ_[p]) := by
    dsimp [π, Qpe, eisenstein]
    change AdjoinRoot.root (X ^ e - C (p : ℚ_[p])) ^ e =
      AdjoinRoot.of (X ^ e - C (p : ℚ_[p])) (p : ℚ_[p])
    exact root_X_pow_sub_C_pow (K := ℚ_[p]) e (p : ℚ_[p])
  have hπ_int : IsIntegral ℤ_[p] π := by
    refine ⟨X ^ e - C (p : ℤ_[p]), ?_, ?_⟩
    · exact monic_X_pow_sub_C _ (NeZero.ne e)
    · rw [← Polynomial.aeval_def]
      simp only [Polynomial.aeval_sub, Polynomial.aeval_X, map_pow, Polynomial.aeval_C]
      rw [sub_eq_zero, hπe]
      exact (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Qpe (p := p) e) (p : ℤ_[p])).symm
  refine ⟨⟨π, hπ_int⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hue : IsUnit ((⟨π, hπ_int⟩ : 𝒪 (Qpe (p := p) e)) ^ e) := hu.pow e
    have hval : (⟨π, hπ_int⟩ : 𝒪 (Qpe (p := p) e)) ^ e =
        algebraMap (𝒪 ℚ_[p]) (𝒪 (Qpe (p := p) e)) (pElt p) := by
      apply Subtype.ext
      rw [Subalgebra.coe_pow, hπe]
      simp
    rw [hval] at hue
    have hp_mem : pElt p ∈ IsLocalRing.maximalIdeal (𝒪 ℚ_[p]) := by
      rw [Qpe_maximalIdeal_eq_span (p := p)]
      exact Ideal.mem_span_singleton_self _
    have hp_nonunit : ¬ IsUnit (pElt p) :=
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hp_mem)
    exact hp_nonunit
      (IsLocalHom.map_nonunit
        (f := algebraMap (𝒪 ℚ_[p]) (𝒪 (Qpe (p := p) e))) (pElt p) hue)
  · apply Subtype.ext
    rw [Subalgebra.coe_pow, hπe]
    simp

theorem Qpe_map_maximalIdeal_le_pow :
    (IsLocalRing.maximalIdeal (𝒪 ℚ_[p])).map
        (algebraMap (𝒪 ℚ_[p]) (𝒪 (Qpe (p := p) e)))
      ≤ (IsLocalRing.maximalIdeal (𝒪 (Qpe (p := p) e))) ^ e := by
  obtain ⟨θ, hθmem, hθpow⟩ := Qpe_exists_integral_root (p := p) e
  rw [Qpe_maximalIdeal_eq_span (p := p), Ideal.map_span, Set.image_singleton, ← hθpow]
  exact span_pow_le_pow e hθmem

theorem Qpe_le_ramificationIdx :
    e ≤ ramificationIdx ℚ_[p] (Qpe (p := p) e) := by
  have hinj : Function.Injective (algebraMap (𝒪 ℚ_[p]) (𝒪 (Qpe (p := p) e))) :=
    FaithfulSMul.algebraMap_injective _ _
  have hmK_ne_bot : IsLocalRing.maximalIdeal (𝒪 ℚ_[p]) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field (𝒪 ℚ_[p])
  have hne : (IsLocalRing.maximalIdeal (𝒪 ℚ_[p])).map
      (algebraMap (𝒪 ℚ_[p]) (𝒪 (Qpe (p := p) e))) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact hmK_ne_bot
  exact le_ramificationIdx_of_map_le_pow
    (IsLocalRing.maximalIdeal (𝒪 ℚ_[p])) hne (Qpe_map_maximalIdeal_le_pow (p := p) e)

theorem Qpe_inertiaDeg : inertiaDeg ℚ_[p] (Qpe (p := p) e) = 1 := by
  have hef : ramificationIdx ℚ_[p] (Qpe (p := p) e)
        * inertiaDeg ℚ_[p] (Qpe (p := p) e) = e := by
    have h := ramificationIdx_mul_inertiaDeg ℚ_[p] (Qpe (p := p) e)
    rwa [Qpe_finrank e] at h
  have he_pos : 0 < e := by
    have hpos : 0 < Module.finrank ℚ_[p] (Qpe (p := p) e) := Module.finrank_pos
    rwa [Qpe_finrank e] at hpos
  have hlb := Qpe_le_ramificationIdx (p := p) e
  have hr_pos : 0 < ramificationIdx ℚ_[p] (Qpe (p := p) e) := lt_of_lt_of_le he_pos hlb
  have hfle : inertiaDeg ℚ_[p] (Qpe (p := p) e) ≤ 1 := by
    apply Nat.le_of_mul_le_mul_left _ hr_pos
    calc ramificationIdx ℚ_[p] (Qpe (p := p) e) * inertiaDeg ℚ_[p] (Qpe (p := p) e)
          = e := hef
      _ ≤ ramificationIdx ℚ_[p] (Qpe (p := p) e) := hlb
      _ = ramificationIdx ℚ_[p] (Qpe (p := p) e) * 1 := (mul_one _).symm
  have hf_pos : 0 < inertiaDeg ℚ_[p] (Qpe (p := p) e) :=
    Nat.pos_of_ne_zero (inertiaDeg_ne_zero ℚ_[p] (Qpe (p := p) e))
  omega

/-- Ramification index is the full degree: `e = [L:K]`。 -/
theorem Qpe_ramificationIdx : ramificationIdx ℚ_[p] (Qpe (p := p) e) = e := by
  have h := ramificationIdx_mul_inertiaDeg ℚ_[p] (Qpe (p := p) e)
  rw [Qpe_inertiaDeg (p := p) e, mul_one, Qpe_finrank (p := p) e] at h
  exact h

/-- Tame when `p ∤ e`。 -/
theorem Qpe_isTamelyRamified (hpe : ¬ (p ∣ e)) :
    IsTamelyRamified ℚ_[p] (Qpe (p := p) e) := by
  show ¬ (p ∣ ramificationIdx ℚ_[p] (Qpe (p := p) e))
  rw [Qpe_ramificationIdx (p := p) e]; exact hpe

/-- The headline identity: `d = e − 1` for `ℚ_p(p^{1/e})` with `p ∤ e`。 -/
theorem Qpe_discriminantExponent (hpe : ¬ (p ∣ e)) :
    discriminantExponent ℚ_[p] (Qpe (p := p) e) = e - 1 := by
  rw [discExponent_tame ℚ_[p] (Qpe (p := p) e) (Qpe_isTamelyRamified (p := p) e hpe),
      Qpe_inertiaDeg (p := p) e, one_mul, Qpe_ramificationIdx (p := p) e]

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

/-- Totally ramified: `f = 1`. -/
theorem Q2sqrt2_inertiaDeg : inertiaDeg ℚ_[2] Q2sqrt2 = 1 := sorry

/-- Ramified of degree `2`: `e = 2`. -/
theorem Q2sqrt2_ramificationIdx : ramificationIdx ℚ_[2] Q2sqrt2 = 2 := by
  have h := ramificationIdx_mul_inertiaDeg ℚ_[2] Q2sqrt2
  rw [Q2sqrt2_inertiaDeg, mul_one, Q2sqrt2_finrank] at h
  exact h

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
