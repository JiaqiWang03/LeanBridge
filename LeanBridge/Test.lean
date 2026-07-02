import Mathlib
import LeanBridge.PadicInv

/-!
# Concrete test cases for `p`-adic field invariants (issue #63)

This file contains compiled examples for the invariants defined in
`LeanBridge.PadicInv`.  Each extension is presented explicitly as an
`AdjoinRoot f`, so the field is literally `ℚ_p[X]/(f)`.

The three examples are:

1. **Unramified quadratic over `ℚ_2`**:
   `ℚ_2[X]/(X^2 + X + 1)`.  The integral polynomial reduces to the irreducible
   polynomial `X^2 + X + 1` over `𝔽_2`; the residue degree is at least `2`, and
   the identity `e * f = [L : K]` forces `e = 1`, `f = 2`, and `d = 0`.
2. **Totally ramified Eisenstein extensions**:
   `ℚ_p[X]/(X^e - p)`.  The root is integral, its `e`-th power is the image of
   `p`, and the induced ideal containment gives `e ≤ e(L/K)`.  Since the degree
   is `e`, this yields `f = 1`, `e(L/K) = e`, and in the tame case `d = e - 1`.
3. **Wild quadratic over `ℚ_2`**:
   `ℚ_2[X]/(X^2 - 2)`.  This is the `p = e = 2` specialization of the
   Eisenstein construction, hence totally and wildly ramified.  The different is
   computed from the monogenic presentation and the derivative `2θ`, giving
   `δ = 3` and therefore `d = fδ = 3`.
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

/-! ## Case 1 — unramified `ℚ_2[X]/(X² + X + 1)`  (`e = 1`, `f = 2`, `d = 0`)

We use the integral polynomial `X² + X + 1 ∈ ℤ_2[X]`. Its reduction mod `2` has
no root in `𝔽_2`, hence is irreducible.  The integral root gives an element of
the residue field of `𝒪_L` whose minimal polynomial has degree `2`; therefore
`f ≥ 2`.  Since `[L : ℚ_2] = 2`, the identity `e * f = [L : K]` forces `e = 1`. -/
section UnramifiedConcrete

def zeta3PolyZ : Polynomial ℤ_[2] := X ^ 2 + C 1 * X + C 1

abbrev zeta3Poly : Polynomial ℚ_[2] := zeta3PolyZ.map (algebraMap ℤ_[2] ℚ_[2])

theorem zeta3PolyZ_monic : zeta3PolyZ.Monic := by
  unfold zeta3PolyZ
  monicity!

theorem zeta3_reduction_irreducible :
    Irreducible (zeta3PolyZ.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) := by
  have hmap : zeta3PolyZ.map (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)
      = X ^ 2 + X + 1 := by
    unfold zeta3PolyZ
    simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.C_1, one_mul]
  rw [hmap]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : (X ^ 2 + X + 1 : Polynomial (ZMod 2)).natDegree = 2 := by
      compute_degree!
    rw [hdeg]
    norm_num
  · intro x hx
    simp only [Polynomial.IsRoot.def] at hx
    fin_cases x <;>
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one] at hx <;>
      revert hx <;> decide

instance instFactIrreducibleZeta3 : Fact (Irreducible zeta3Poly) := ⟨by
  have hmon : zeta3PolyZ.Monic := zeta3PolyZ_monic
  have hZ : Irreducible zeta3PolyZ :=
    Polynomial.Monic.irreducible_of_irreducible_map
      PadicInt.toZMod zeta3PolyZ hmon zeta3_reduction_irreducible
  exact (hmon.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[2])).mp hZ⟩

abbrev Q2zeta3 : Type _ := AdjoinRoot zeta3Poly

instance : Module.Finite ℚ_[2] Q2zeta3 :=
  PowerBasis.finite
    (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible zeta3Poly)))

instance : PadicField Q2zeta3 2 := PadicField.mk

theorem Q2zeta3_finrank : Module.finrank ℚ_[2] Q2zeta3 = 2 := by
  rw [PowerBasis.finrank
      (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible zeta3Poly))),
    AdjoinRoot.powerBasis_dim]
  show (zeta3PolyZ.map (algebraMap ℤ_[2] ℚ_[2])).natDegree = 2
  rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective ℤ_[2] ℚ_[2])]
  unfold zeta3PolyZ
  compute_degree!

open IsLocalRing in
theorem Q2zeta3_inertiaDeg_ge : 2 ≤ inertiaDeg ℚ_[2] Q2zeta3 := by
  classical
  set R := 𝒪 ℚ_[2]; set S := 𝒪 Q2zeta3
  set kR := IsLocalRing.ResidueField R; set kS := IsLocalRing.ResidueField S
  have hconv : inertiaDeg ℚ_[2] Q2zeta3 = Module.finrank kR kS := by
    show Ideal.inertiaDeg (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) = _
    rw [Ideal.inertiaDeg_algebraMap]
    rfl
  rw [hconv]
  haveI : Module.Finite kR kS := IsLocalRing.ResidueField.finite_of_module_finite
  have hroot0 : Polynomial.aeval (AdjoinRoot.root zeta3Poly) zeta3Poly = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hrootL : Polynomial.aeval (AdjoinRoot.root zeta3Poly) zeta3PolyZ = 0 := by
    have h := hroot0; rwa [Polynomial.aeval_map_algebraMap] at h
  have hint : IsIntegral ℤ_[2] (AdjoinRoot.root zeta3Poly) :=
    ⟨zeta3PolyZ, zeta3PolyZ_monic, hrootL⟩
  set θ : S := ⟨AdjoinRoot.root zeta3Poly, hint⟩
  have hrootS : Polynomial.aeval θ zeta3PolyZ = 0 := by
    apply Subtype.ext
    have h : (Subalgebra.val (𝒪 Q2zeta3)) (Polynomial.aeval θ zeta3PolyZ)
        = Polynomial.aeval (AdjoinRoot.root zeta3Poly) zeta3PolyZ :=
      (Polynomial.aeval_algHom_apply (Subalgebra.val (𝒪 Q2zeta3)) θ zeta3PolyZ).symm
    rw [hrootL] at h
    simpa using h
  set θbar : kS := IsLocalRing.residue S θ
  set φR : ℤ_[2] →+* kR := (IsLocalRing.residue R).comp (algebraMap ℤ_[2] R)
  set gbar : Polynomial kR := zeta3PolyZ.map φR
  have gbar_monic : gbar.Monic := zeta3PolyZ_monic.map φR
  have gbar_irred : Irreducible gbar := by
    have hsurj : Function.Surjective (algebraMap ℤ_[2] (𝒪 ℚ_[2])) := by
      rintro ⟨y, hy⟩
      obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ_[2]) (K := ℚ_[2])).mp hy
      exact ⟨a, Subtype.ext ha⟩
    let eOI : ℤ_[2] ≃+* (𝒪 ℚ_[2]) :=
      RingEquiv.ofBijective (algebraMap ℤ_[2] (𝒪 ℚ_[2]))
        ⟨FaithfulSMul.algebraMap_injective _ _, hsurj⟩
    haveI : IsLocalHom (eOI.symm) := isLocalHom_equiv eOI.symm
    haveI : IsLocalHom (↑(eOI.symm) : (𝒪 ℚ_[2]) →+* ℤ_[2]) := isLocalHom_toRingHom eOI.symm
    set ε : kR ≃+* ZMod 2 :=
      (IsLocalRing.ResidueField.mapEquiv eOI.symm).trans PadicInt.residueField with hε
    have hcomp2 : (↑ε : kR →+* ZMod 2).comp φR = PadicInt.toZMod := by
      ext x
      show ε (φR x) = PadicInt.toZMod x
      rw [hε]
      show PadicInt.residueField (IsLocalRing.ResidueField.mapEquiv eOI.symm
          (IsLocalRing.residue (𝒪 ℚ_[2]) (eOI x))) = PadicInt.toZMod x
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue,
          PadicInt.toZMod_eq_residueField_comp_residue]
      simp only [RingHom.coe_coe, RingEquiv.symm_apply_apply, RingHom.comp_apply]
      rfl
    apply (MulEquiv.irreducible_iff (Polynomial.mapEquiv ε)).mp
    rw [Polynomial.mapEquiv_apply]
    show Irreducible (Polynomial.map (↑ε : kR →+* ZMod 2) (zeta3PolyZ.map φR))
    rw [Polynomial.map_map, hcomp2]
    exact zeta3_reduction_irreducible
  have gbar_root : Polynomial.aeval θbar gbar = 0 := by
    show Polynomial.aeval θbar (zeta3PolyZ.map φR) = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap kR kS).comp φR
        = (IsLocalRing.residue S).comp (algebraMap ℤ_[2] S) := by
      ext x
      show algebraMap kR kS (IsLocalRing.residue R (algebraMap ℤ_[2] R x))
          = IsLocalRing.residue S (algebraMap ℤ_[2] S x)
      rw [IsLocalRing.ResidueField.algebraMap_residue,
          ← IsScalarTower.algebraMap_apply ℤ_[2] (↥R) (↥S)]
    rw [hcomp, ← Polynomial.hom_eval₂ zeta3PolyZ (algebraMap ℤ_[2] S) (IsLocalRing.residue S) θ,
      ← Polynomial.aeval_def, hrootS, map_zero]
  have hmin : minpoly kR θbar = gbar :=
    (minpoly.eq_of_irreducible_of_monic gbar_irred gbar_root gbar_monic).symm
  have hdegZ : zeta3PolyZ.natDegree = 2 := by unfold zeta3PolyZ; compute_degree!
  have hdeg : (minpoly kR θbar).natDegree = 2 := by
    rw [hmin]; show (zeta3PolyZ.map φR).natDegree = 2
    rw [zeta3PolyZ_monic.natDegree_map, hdegZ]
  calc (2 : ℕ) = (minpoly kR θbar).natDegree := hdeg.symm
    _ ≤ Module.finrank kR kS := minpoly.natDegree_le θbar

theorem Q2zeta3_ramificationIdx : ramificationIdx ℚ_[2] Q2zeta3 = 1 := by
  have hef : ramificationIdx ℚ_[2] Q2zeta3 * inertiaDeg ℚ_[2] Q2zeta3 = 2 := by
    have h := ramificationIdx_mul_inertiaDeg ℚ_[2] Q2zeta3
    rwa [Q2zeta3_finrank] at h
  have hfge : 2 ≤ inertiaDeg ℚ_[2] Q2zeta3 := Q2zeta3_inertiaDeg_ge
  have he_le : ramificationIdx ℚ_[2] Q2zeta3 ≤ 1 :=
    Nat.le_of_mul_le_mul_right
      (by calc ramificationIdx ℚ_[2] Q2zeta3 * inertiaDeg ℚ_[2] Q2zeta3
              = 2 := hef
            _ ≤ inertiaDeg ℚ_[2] Q2zeta3 := hfge
            _ = 1 * inertiaDeg ℚ_[2] Q2zeta3 := (one_mul _).symm)
      (by omega)
  have he_pos : 0 < ramificationIdx ℚ_[2] Q2zeta3 := by
    rcases Nat.eq_zero_or_pos (ramificationIdx ℚ_[2] Q2zeta3) with h | h
    · rw [h, zero_mul] at hef; omega
    · exact h
  omega

theorem Q2zeta3_isUnramified : IsUnramified ℚ_[2] Q2zeta3 := Q2zeta3_ramificationIdx

theorem Q2zeta3_inertiaDeg : inertiaDeg ℚ_[2] Q2zeta3 = 2 := by
  have h := ramificationIdx_mul_inertiaDeg ℚ_[2] Q2zeta3
  rw [Q2zeta3_ramificationIdx, one_mul, Q2zeta3_finrank] at h
  exact h

theorem Q2zeta3_discriminantExponent : discriminantExponent ℚ_[2] Q2zeta3 = 0 :=
  (discExponent_eq_zero_iff_unramified ℚ_[2] Q2zeta3).mpr Q2zeta3_isUnramified

end UnramifiedConcrete

/-! ## Case 2 — Eisenstein extensions `ℚ_p[X]/(Xᵉ − p)`  (`f = 1`, `d = e − 1`)

For nonzero `e`, `Xᵉ − p` is proved irreducible by applying Eisenstein's
criterion over `ℤ_p` and then Gauss's lemma.  The root is lifted to the ring of
integers, satisfies `θᵉ = p`, and lies in the maximal ideal.  This gives
`𝔪_K 𝒪_L ≤ 𝔪_L^e`, hence `e ≤ e(L/K)`; together with `[L : K] = e` and
`e(L/K) * f(L/K) = [L : K]`, the extension is totally ramified.  When `p ∤ e`,
the tame discriminant formula from `PadicInv` gives `d = e - 1`. -/
section Eisenstein

variable {p : ℕ} [Fact p.Prime] (e : ℕ) [NeZero e]

/-- The Eisenstein polynomial `Xᵉ − p ∈ ℚ_p[X]`. -/
def eisenstein : Polynomial ℚ_[p] := X ^ e - C (p : ℚ_[p])

instance : Fact (Irreducible (eisenstein (p := p) e)) := by
  have he : e ≠ 0 := NeZero.ne e
  refine ⟨?_⟩
  set f₀ : ℤ_[p][X] := X ^ e - C (p : ℤ_[p]) with hf₀
  have hmonic : f₀.Monic := by
    rw [hf₀]
    exact monic_X_pow_sub_C _ he
  have hdeg : f₀.natDegree = e := by
    rw [hf₀]
    exact natDegree_X_pow_sub_C
  have hprim : f₀.IsPrimitive := hmonic.isPrimitive
  have hp_mem : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hEis : f₀.IsEisensteinAt (IsLocalRing.maximalIdeal ℤ_[p]) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmonic.leadingCoeff]
      intro h1
      exact (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    · intro n hn
      rw [hdeg] at hn
      rw [hf₀, coeff_sub, coeff_X_pow, coeff_C, if_neg hn.ne, zero_sub]
      by_cases hn0 : n = 0
      · rw [if_pos hn0];
        exact (IsLocalRing.maximalIdeal ℤ_[p]).neg_mem hp_mem
      · rw [if_neg hn0, neg_zero]
        exact Ideal.zero_mem _
    · rw [hf₀, coeff_sub, coeff_X_pow, coeff_C, if_neg he.symm, if_pos rfl, zero_sub]
      intro hmem
      rw [Ideal.neg_mem_iff, PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have key : (p : ℤ_[p]) * ((p : ℤ_[p]) * c) = (p : ℤ_[p]) := by
        have e2 : (p : ℤ_[p]) * ((p : ℤ_[p]) * c) = (p : ℤ_[p]) ^ 2 * c := by ring
        rw [e2, ← hc]
      have hpc1 : (p : ℤ_[p]) * c = 1 := mul_left_cancel₀
        (by exact_mod_cast (Fact.out : p.Prime).pos.ne') (key.trans (mul_one _).symm)
      exact ((IsLocalRing.mem_maximalIdeal _).mp hp_mem) (IsUnit.of_mul_eq_one c hpc1)
  rw [show eisenstein (p := p) e = f₀.map (algebraMap ℤ_[p] ℚ_[p]) from by
    ext n
    simp [hf₀, eisenstein, coeff_sub, coeff_X_pow]]
  exact (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp
    (hEis.irreducible (IsLocalRing.maximalIdeal.isMaximal ℤ_[p]).isPrime hprim
      (by rw [hdeg]; exact Nat.pos_of_ne_zero he))

variable [Fact (Irreducible (eisenstein (p := p) e))]

/-- `ℚ_p(p^{1/e}) := ℚ_p[X]/(Xᵉ − p)`. -/
abbrev Qpe : Type _ := AdjoinRoot (eisenstein (p := p) e)

instance : Module.Finite ℚ_[p] (Qpe (p := p) e) :=
  PowerBasis.finite (AdjoinRoot.powerBasis
      (Irreducible.ne_zero (Fact.out : Irreducible (eisenstein (p := p) e))))

instance : PadicField (Qpe (p := p) e) p := PadicField.mk

omit [NeZero e] in
/-- `[ℚ_p(p^{1/e}) : ℚ_p] = e`. -/
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
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hsurj : Function.Surjective (algebraMap ℤ_[p] (𝒪 ℚ_[p])) := by
    rintro ⟨x, hx⟩
    have hfr : IsFractionRing ℤ_[p] ℚ_[p] := by infer_instance
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ_[p]) (K := ℚ_[p])).mp hx
    refine ⟨a, Subtype.ext ?_⟩
    exact ha
  let equivOI : ℤ_[p] ≃+* 𝒪 ℚ_[p] :=
    RingEquiv.ofBijective (algebraMap ℤ_[p] (𝒪 ℚ_[p]))
    ⟨FaithfulSMul.algebraMap_injective _ _, hsurj⟩
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

/-- Ramification index is the full degree: `e(L/K) = e = [L : K]`. -/
theorem Qpe_ramificationIdx : ramificationIdx ℚ_[p] (Qpe (p := p) e) = e := by
  have h := ramificationIdx_mul_inertiaDeg ℚ_[p] (Qpe (p := p) e)
  rw [Qpe_inertiaDeg (p := p) e, mul_one, Qpe_finrank (p := p) e] at h
  exact h

/-- The Eisenstein extension is tame when `p ∤ e`. -/
theorem Qpe_isTamelyRamified (hpe : ¬ (p ∣ e)) :
    IsTamelyRamified ℚ_[p] (Qpe (p := p) e) := by
  show ¬ (p ∣ ramificationIdx ℚ_[p] (Qpe (p := p) e))
  rw [Qpe_ramificationIdx (p := p) e]; exact hpe

/-- The tame discriminant identity: `d = e − 1` for `ℚ_p(p^{1/e})` with `p ∤ e`. -/
theorem Qpe_discriminantExponent (hpe : ¬ (p ∣ e)) :
    discriminantExponent ℚ_[p] (Qpe (p := p) e) = e - 1 := by
  rw [discExponent_tame ℚ_[p] (Qpe (p := p) e) (Qpe_isTamelyRamified (p := p) e hpe),
      Qpe_inertiaDeg (p := p) e, one_mul, Qpe_ramificationIdx (p := p) e]

end Eisenstein

/-! ## Case 3 — wild quadratic `ℚ_2(√2) = ℚ_2[X]/(X² − 2)`

This is the specialization of Case 2 to `p = e = 2`.  The extension has
`[L : ℚ_2] = 2`, `f = 1`, and `e = 2`, so it is wildly ramified.  The proof of
`δ = 3` identifies the integral root `θ` as a uniformizer, proves the extension
of rings of integers is monogenic, computes the different as
`(f'(θ)) = (2θ) = (θ³)`, and then reads off the multiplicity. -/
section WildQ2

/-- `X² − 2 ∈ ℚ_2[X]`. -/
abbrev sqrtTwoPoly : Polynomial ℚ_[2] := X ^ 2 - C (2 : ℚ_[2])

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

instance : PadicField Q2sqrt2 2 := PadicField.mk

/-- `[ℚ_2(√2) : ℚ_2] = 2`. -/
theorem Q2sqrt2_finrank : Module.finrank ℚ_[2] Q2sqrt2 = 2 := by
  rw [PowerBasis.finrank
      (AdjoinRoot.powerBasis (Irreducible.ne_zero (Fact.out : Irreducible sqrtTwoPoly))),
    AdjoinRoot.powerBasis_dim]
  simp [sqrtTwoPoly]

/-- An integral square-root element: `θ ∈ 𝔪_L` and `θ²` is the image of `2`. -/
theorem Q2sqrt2_exists_integral_root :
    ∃ θ : 𝒪 Q2sqrt2,
      θ ∈ IsLocalRing.maximalIdeal (𝒪 Q2sqrt2) ∧
      θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2) := by
  exact Qpe_exists_integral_root (p := 2) 2

/-- The maximal ideal of `𝒪_{ℚ_2}` maps into `𝔪_L²`, using `θ² = 2`. -/
theorem Q2sqrt2_map_maximalIdeal_le_pow :
    (IsLocalRing.maximalIdeal (𝒪 ℚ_[2])).map (algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2))
      ≤ (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ 2 := by
  obtain ⟨θ, hθmem, hθpow⟩ := Q2sqrt2_exists_integral_root
  rw [Qpe_maximalIdeal_eq_span (p := 2), Ideal.map_span, Set.image_singleton, ← hθpow]
  exact span_pow_le_pow 2 hθmem

/-- The ideal containment gives the lower bound `2 ≤ e(L/K)`. -/
theorem Q2sqrt2_le_ramificationIdx : 2 ≤ ramificationIdx ℚ_[2] Q2sqrt2 := by
  have hinj : Function.Injective (algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hne : (IsLocalRing.maximalIdeal (𝒪 ℚ_[2])).map
      (algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact IsDiscreteValuationRing.not_a_field (𝒪 ℚ_[2])
  exact le_ramificationIdx_of_map_le_pow
    (IsLocalRing.maximalIdeal (𝒪 ℚ_[2])) hne Q2sqrt2_map_maximalIdeal_le_pow

/-- Totally ramified: `f = 1`. -/
theorem Q2sqrt2_inertiaDeg : inertiaDeg ℚ_[2] Q2sqrt2 = 1 := by
  have hef : ramificationIdx ℚ_[2] Q2sqrt2 * inertiaDeg ℚ_[2] Q2sqrt2 = 2 := by
    have h := ramificationIdx_mul_inertiaDeg ℚ_[2] Q2sqrt2
    rwa [Q2sqrt2_finrank] at h
  have hlb := Q2sqrt2_le_ramificationIdx
  have hr_pos : 0 < ramificationIdx ℚ_[2] Q2sqrt2 := by omega
  have hfle : inertiaDeg ℚ_[2] Q2sqrt2 ≤ 1 := by
    apply Nat.le_of_mul_le_mul_left _ hr_pos
    calc ramificationIdx ℚ_[2] Q2sqrt2 * inertiaDeg ℚ_[2] Q2sqrt2
          = 2 := hef
      _ ≤ ramificationIdx ℚ_[2] Q2sqrt2 := hlb
      _ = ramificationIdx ℚ_[2] Q2sqrt2 * 1 := (mul_one _).symm
  have hf_pos : 0 < inertiaDeg ℚ_[2] Q2sqrt2 :=
    Nat.pos_of_ne_zero (inertiaDeg_ne_zero ℚ_[2] Q2sqrt2)
  omega

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

/-- In a DVR, every nonzero ideal is a power of the maximal ideal. -/
lemma exists_maximalIdeal_pow_of_ne_bot {S : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] {I : Ideal S} (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = (IsLocalRing.maximalIdeal S) ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  exact ⟨n, by rw [hn, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]⟩

/-- The ramification computation identifies the extension of the base maximal ideal. -/
lemma Q2sqrt2_map_maximalIdeal_eq_pow :
    (IsLocalRing.maximalIdeal (𝒪 ℚ_[2])).map (algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2))
      = (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ 2 := by
  obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_of_ne_bot (by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝒪 ℚ_[2]) (𝒪 Q2sqrt2))]
    exact IsDiscreteValuationRing.not_a_field (𝒪 ℚ_[2]))
  have hstrictL : StrictAnti (fun n : ℕ => (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ n) :=
    Ideal.pow_right_strictAnti _ (IsDiscreteValuationRing.not_a_field _)
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hram : ramificationIdx ℚ_[2] Q2sqrt2 = m := by
    show Ideal.ramificationIdx (R := 𝒪 ℚ_[2]) (S := 𝒪 Q2sqrt2)
      (IsLocalRing.maximalIdeal (𝒪 ℚ_[2])) (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) = m
    refine Ideal.ramificationIdx_spec (le_of_eq hm) ?_
    rw [hm]
    exact (hstrictL (Nat.lt_succ_self m)).2
  rw [Q2sqrt2_ramificationIdx] at hram
  rw [hm, ← hram]

/-- Any integral root with square `2` is nonzero. -/
lemma Q2sqrt2_integral_root_ne_zero {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) : θ ≠ 0 := fun h => by
  rw [h, zero_pow (by norm_num)] at hθpow
  exact absurd ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mp hθpow.symm)
    (by
      simp only [pElt]
      rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[2] _)]
      norm_num)

/-- The integral square root of `2` is a uniformizer of `𝒪_{ℚ_2(√2)}`. -/
lemma Q2sqrt2_maximalIdeal_eq_span_root {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    IsLocalRing.maximalIdeal (𝒪 Q2sqrt2) = Ideal.span {θ} := by
  have hstrictL : StrictAnti (fun n : ℕ => (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ n) :=
    Ideal.pow_right_strictAnti _ (IsDiscreteValuationRing.not_a_field _)
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hsqfull : Ideal.span {θ} ^ 2 = (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ 2 := by
    rw [← Q2sqrt2_map_maximalIdeal_eq_pow, Ideal.span_singleton_pow, hθpow,
      Qpe_maximalIdeal_eq_span (p := 2), Ideal.map_span, Set.image_singleton]
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_of_ne_bot (I := Ideal.span {θ})
    (by simpa [Ideal.span_singleton_eq_bot] using Q2sqrt2_integral_root_ne_zero hθpow)
  have hn1 : n = 1 := by
    have hpow : (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ (n * 2)
        = (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ 2 := by
      rw [← hsqfull, hn, ← pow_mul]
    have := hstrictL.injective hpow
    omega
  rw [hn, hn1, pow_one]

/-- The integral square root of `2` is irreducible in the DVR `𝒪_{ℚ_2(√2)}`. -/
lemma Q2sqrt2_integral_root_irreducible {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    Irreducible θ :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal θ
    (Q2sqrt2_integral_root_ne_zero hθpow) (Q2sqrt2_maximalIdeal_eq_span_root hθpow)

instance instQ2sqrt2IsLocalHom :
    IsLocalHom (algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2)) := by
  have hcomap : Ideal.comap (algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2))
      (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) = IsLocalRing.maximalIdeal (𝒪 ℚ_[2]) :=
    Ideal.LiesOver.over.symm
  exact ((IsLocalRing.local_hom_TFAE (algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2))).out 4 0).mp hcomap

lemma Q2sqrt2_residue_finrank :
    Module.finrank (IsLocalRing.ResidueField (𝒪 ℚ_[2]))
      (IsLocalRing.ResidueField (𝒪 Q2sqrt2)) = 1 := by
  have h : Ideal.inertiaDeg (IsLocalRing.maximalIdeal (𝒪 ℚ_[2]))
      (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) = 1 := Q2sqrt2_inertiaDeg
  rwa [Ideal.inertiaDeg_algebraMap] at h

/-- In this totally ramified quadratic, any residue element already generates the residue field. -/
lemma Q2sqrt2_residue_adjoin_eq_top (θ : 𝒪 Q2sqrt2) :
    IntermediateField.adjoin (IsLocalRing.ResidueField (𝒪 ℚ_[2]))
      ({IsLocalRing.residue (𝒪 Q2sqrt2) θ} :
        Set (IsLocalRing.ResidueField (𝒪 Q2sqrt2))) = ⊤ := by
  have hbot : (⊤ : IntermediateField (IsLocalRing.ResidueField (𝒪 ℚ_[2]))
      (IsLocalRing.ResidueField (𝒪 Q2sqrt2))) = ⊥ := by
    rw [← IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_top']
    exact Q2sqrt2_residue_finrank
  rw [eq_top_iff, hbot]
  exact bot_le

/-- The integral square root generates the ring of integers. -/
lemma Q2sqrt2_adjoin_integral_root_eq_top {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    Algebra.adjoin (𝒪 ℚ_[2]) ({θ} : Set (𝒪 Q2sqrt2)) = ⊤ := by
  have h := Monogenicity.mono_adjoin_two_gen θ θ
    (Q2sqrt2_residue_adjoin_eq_top θ) (Q2sqrt2_integral_root_irreducible hθpow)
  rwa [Set.pair_eq_singleton] at h

/-- The conductor of the integral square-root order is the unit ideal. -/
lemma Q2sqrt2_conductor_eq_top {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    conductor (𝒪 ℚ_[2]) θ = ⊤ := by
  rw [Ideal.eq_top_iff_one, mem_conductor_iff]
  intro b
  rw [one_mul, Q2sqrt2_adjoin_integral_root_eq_top hθpow]
  exact Algebra.mem_top

instance instQ2sqrt2IntegralIntegers :
    Algebra.IsIntegral (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) :=
  Algebra.IsIntegral.of_finite _ _

instance instQ2sqrt2IntegralField :
    Algebra.IsIntegral ℚ_[2] Q2sqrt2 :=
  Algebra.IsIntegral.of_finite _ _

instance instQ2sqrt2IntegerFieldTower :
    IsScalarTower (𝒪 ℚ_[2]) ℚ_[2] Q2sqrt2 :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance instQ2sqrt2TorsionFreeIntegers :
    Module.IsTorsionFree (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective _ _)

/-- The field image of an integral square root still squares to `2`. -/
lemma Q2sqrt2_field_root_sq {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    (algebraMap (𝒪 Q2sqrt2) Q2sqrt2 θ) ^ 2 = (2 : Q2sqrt2) := by
  rw [← map_pow, hθpow, (show pElt 2 = (2 : 𝒪 ℚ_[2]) from Subtype.ext rfl),
    (show algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (2 : 𝒪 ℚ_[2]) = (2 : 𝒪 Q2sqrt2) from
      Subtype.ext rfl)]
  rfl

/-- The field minimal polynomial of the integral square root is `X² - 2`. -/
lemma Q2sqrt2_minpoly_field_root {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    minpoly ℚ_[2] (algebraMap (𝒪 Q2sqrt2) Q2sqrt2 θ) = sqrtTwoPoly := by
  refine (minpoly.eq_of_irreducible_of_monic (Fact.out : Irreducible sqrtTwoPoly) ?_ ?_).symm
  · change Polynomial.aeval (algebraMap (𝒪 Q2sqrt2) Q2sqrt2 θ)
      (X ^ 2 - C (2 : ℚ_[2])) = 0
    simp only [Polynomial.aeval_sub, Polynomial.aeval_X, map_pow, Polynomial.aeval_C]
    rw [Q2sqrt2_field_root_sq hθpow]
    change (2 : Q2sqrt2) - (2 : Q2sqrt2) = 0
    norm_num
  · exact monic_X_pow_sub_C _ (by norm_num)

/-- The field image of the integral square root generates `ℚ_2(√2)`. -/
lemma Q2sqrt2_adjoin_field_root_eq_top {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    Algebra.adjoin ℚ_[2] {algebraMap (𝒪 Q2sqrt2) Q2sqrt2 θ} = ⊤ := by
  have hsub : (Algebra.adjoin ℚ_[2] {algebraMap (𝒪 Q2sqrt2) Q2sqrt2 θ}).toSubmodule = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    show Module.finrank ℚ_[2]
        ↥(Algebra.adjoin ℚ_[2] {algebraMap (𝒪 Q2sqrt2) Q2sqrt2 θ}) =
      Module.finrank ℚ_[2] Q2sqrt2
    rw [(Algebra.adjoin.powerBasis' (Algebra.IsIntegral.isIntegral
        (algebraMap (𝒪 Q2sqrt2) Q2sqrt2 θ))).finrank,
      Algebra.adjoin.powerBasis'_dim, Q2sqrt2_minpoly_field_root hθpow, Q2sqrt2_finrank]
    simp [sqrtTwoPoly]
  have htop : (⊤ : Subalgebra ℚ_[2] Q2sqrt2).toSubmodule =
      (⊤ : Submodule ℚ_[2] Q2sqrt2) := by
    ext y
    simp
  exact Subalgebra.toSubmodule_injective (hsub.trans htop.symm)

/-- The integral minimal polynomial of the square-root generator is `X² - 2`. -/
lemma Q2sqrt2_minpoly_integral_root {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    minpoly (𝒪 ℚ_[2]) θ = X ^ 2 - C (pElt 2) := by
  have hmapC : (X ^ 2 - C (pElt 2) : Polynomial (𝒪 ℚ_[2])).map
      (algebraMap (𝒪 ℚ_[2]) ℚ_[2]) = sqrtTwoPoly := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      sqrtTwoPoly, (show pElt 2 = (2 : 𝒪 ℚ_[2]) from Subtype.ext rfl), map_ofNat]
  have hmap_min : (minpoly (𝒪 ℚ_[2]) θ).map (algebraMap (𝒪 ℚ_[2]) ℚ_[2]) =
      sqrtTwoPoly := by
    have h := minpoly.isIntegrallyClosed_eq_field_fractions ℚ_[2] Q2sqrt2
      (Algebra.IsIntegral.isIntegral (R := 𝒪 ℚ_[2]) θ)
    rw [Q2sqrt2_minpoly_field_root hθpow] at h
    exact h.symm
  apply Polynomial.map_injective _ (IsFractionRing.injective (𝒪 ℚ_[2]) ℚ_[2])
  rw [hmap_min, hmapC]

/-- The derivative of the integral minimal polynomial evaluates to `θ³`. -/
lemma Q2sqrt2_aeval_derivative_minpoly {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    Polynomial.aeval θ (Polynomial.derivative (minpoly (𝒪 ℚ_[2]) θ)) = θ ^ 3 := by
  rw [Q2sqrt2_minpoly_integral_root hθpow, Polynomial.derivative_sub,
    Polynomial.derivative_X_pow, Polynomial.derivative_C, sub_zero]
  norm_num [Polynomial.aeval_mul,
    (show algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (2 : 𝒪 ℚ_[2]) = (2 : 𝒪 Q2sqrt2) from
      Subtype.ext rfl)]
  rw [(show (2 : 𝒪 Q2sqrt2) = θ ^ 2 by
    rw [hθpow, (show pElt 2 = (2 : 𝒪 ℚ_[2]) from Subtype.ext rfl), map_ofNat])]
  ring

/-- The different ideal is generated by the derivative at the square-root generator. -/
lemma Q2sqrt2_differentIdeal_eq_span_derivative {θ : 𝒪 Q2sqrt2}
    (hθpow : θ ^ 2 = algebraMap (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) (pElt 2)) :
    differentIdeal (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) =
      Ideal.span {Polynomial.aeval θ (Polynomial.derivative (minpoly (𝒪 ℚ_[2]) θ))} := by
  have h := conductor_mul_differentIdeal (𝒪 ℚ_[2]) ℚ_[2] Q2sqrt2 θ
    (Q2sqrt2_adjoin_field_root_eq_top hθpow)
  rwa [Q2sqrt2_conductor_eq_top hθpow, Ideal.top_mul] at h

/-- The different ideal of `ℚ_2(√2)/ℚ_2` is `𝔪_L³`. -/
lemma Q2sqrt2_differentIdeal_eq_pow :
    differentIdeal (𝒪 ℚ_[2]) (𝒪 Q2sqrt2) =
      (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ 3 := by
  obtain ⟨θ, _hθmem, hθpow⟩ := Q2sqrt2_exists_integral_root
  rw [Q2sqrt2_differentIdeal_eq_span_derivative (θ := θ) hθpow,
    Q2sqrt2_aeval_derivative_minpoly hθpow, ← Ideal.span_singleton_pow,
    ← Q2sqrt2_maximalIdeal_eq_span_root hθpow]

/-- Multiplicity of the third power of the maximal ideal is `3`. -/
lemma Q2sqrt2_multiplicity_maximalIdeal_pow_three :
    multiplicity (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2))
      ((IsLocalRing.maximalIdeal (𝒪 Q2sqrt2)) ^ 3) = 3 :=
  multiplicity_pow_self
    (by rw [Ideal.zero_eq_bot]; exact IsDiscreteValuationRing.not_a_field (𝒪 Q2sqrt2))
    (Ideal.isUnit_iff.not.mpr (IsLocalRing.maximalIdeal.isMaximal (𝒪 Q2sqrt2)).ne_top) 3

/-- Different exponent `δ = 3`, computed from `𝔡_{L/K} = 𝔪_L³`. -/
theorem Q2sqrt2_differentExponent : differentExponent ℚ_[2] Q2sqrt2 = 3 := by
  change multiplicity (IsLocalRing.maximalIdeal (𝒪 Q2sqrt2))
    (differentIdeal (𝒪 ℚ_[2]) (𝒪 Q2sqrt2)) = 3
  rw [Q2sqrt2_differentIdeal_eq_pow]
  exact Q2sqrt2_multiplicity_maximalIdeal_pow_three

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
