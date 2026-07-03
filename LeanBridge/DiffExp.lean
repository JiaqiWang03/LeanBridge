import LeanBridge.Ramification
import LeanBridge.Monogenicity
import LeanBridge.TraceFiltration

/-!
# Different and discriminant exponents of extensions of `p`-adic fields
-/

noncomputable section

open Polynomial

/-- Two `R`-bases of `S` give associated discriminants; they differ by a unit
square, namely the square of the change-of-basis determinant. -/
theorem Algebra.discr_associated_of_basis
    {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι R S) (b' : Module.Basis κ R S) :
    Associated (Algebra.discr R ⇑b) (Algebra.discr R ⇑b') := by
  classical
  set e : ι ≃ κ := b.indexEquiv b' with he
  set c' : Module.Basis ι R S := b'.reindex e.symm with hc'def
  have hcoe : (⇑c' : ι → S) = ⇑b' ∘ ⇑e := by
    rw [hc'def]; ext i; simp
  have hc'discr : Algebra.discr R ⇑c' = Algebra.discr R ⇑b' := by
    rw [hcoe]
    have h := Algebra.discr_reindex R b' e.symm
    simpa using h
  set P : Matrix ι ι R := b.toMatrix c' with hP
  have hvec : (⇑c' : ι → S) = Matrix.vecMul (⇑b) (P.map (algebraMap R S)) := by
    funext j
    rw [Matrix.vecMul_eq_sum, Finset.sum_apply, ← Module.Basis.sum_repr b (c' j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Matrix.map_apply, hP, Module.Basis.toMatrix_apply, smul_eq_mul,
      Algebra.smul_def]
    ring
  have hdiscr : Algebra.discr R ⇑c' = P.det ^ 2 * Algebra.discr R ⇑b := by
    rw [hvec]; exact Algebra.discr_of_matrix_vecMul (⇑b) P
  have hPunit : IsUnit P.det := by
    rw [hP, ← Module.Basis.det_apply]; exact b.isUnit_det c'
  refine ⟨(hPunit.pow 2).unit, ?_⟩
  rw [IsUnit.unit_spec, ← hc'discr, hdiscr]; ring

/-- The discriminant of an integral power basis is associated to
`intNorm A B (f'(θ))`, with `θ = pb.gen` and `f = minpoly A θ`. -/
theorem intNorm_deriv_minpoly_associated_discr
    {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsDomain A] [IsDomain B] [IsFractionRing A K] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsIntegrallyClosed A]
    [IsIntegrallyClosed B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    [Module.Finite A B] [Module.Free A B]
    (pb : PowerBasis A B) :
    Associated
      (Algebra.intNorm A B (aeval pb.gen (derivative (minpoly A pb.gen))))
      (Algebra.discr A ⇑pb.basis) := by
  classical
  set θ : B := pb.gen with hθ
  set f : Polynomial A := minpoly A θ with hf
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L B
  have hθint : IsIntegral A θ := Algebra.IsIntegral.isIntegral θ
  set θL : L := algebraMap B L θ with hθL
  set k : ℕ := Module.finrank K L * (Module.finrank K L - 1) / 2 with hk
  set bLoc : Module.Basis (Fin pb.dim) K L :=
    Module.Basis.localizationLocalization K (nonZeroDivisors A) L pb.basis with hbLoc
  have hbLoc_pow : ∀ i, bLoc i = θL ^ (i : ℕ) := by
    intro i
    rw [hbLoc, Module.Basis.localizationLocalization_apply, pb.basis_eq_pow, map_pow, ← hθ, ← hθL]
  let pbL : PowerBasis K L :=
    { gen := θL, dim := pb.dim, basis := bLoc, basis_eq_pow := hbLoc_pow }
  have hpbLgen : pbL.gen = θL := rfl
  have hdiscrK : Algebra.discr K ⇑bLoc = algebraMap A K (Algebra.discr A ⇑pb.basis) := by
    rw [hbLoc]; exact Algebra.discr_localizationLocalization A (nonZeroDivisors A) L pb.basis
  have hnorm : Algebra.discr K ⇑pbL.basis
      = (-1) ^ k * (Algebra.norm K)
          (aeval pbL.gen (derivative (minpoly K pbL.gen))) :=
    Algebra.discr_powerBasis_eq_norm K pbL
  have hmin : minpoly K θL = Polynomial.map (algebraMap A K) f := by
    rw [hθL, hf]; exact minpoly.isIntegrallyClosed_eq_field_fractions K L hθint
  have haeval : aeval θL (derivative (minpoly K θL))
      = algebraMap B L (aeval θ (derivative f)) := by
    rw [hmin, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap, hθL,
      Polynomial.aeval_algebraMap_apply]
  have hintnorm : algebraMap A K (Algebra.intNorm A B (aeval θ (derivative f)))
      = (Algebra.norm K) (algebraMap B L (aeval θ (derivative f))) :=
    Algebra.algebraMap_intNorm (K := K) (L := L) _
  have hKeq : algebraMap A K (Algebra.discr A ⇑pb.basis)
      = algebraMap A K ((-1) ^ k * Algebra.intNorm A B (aeval θ (derivative f))) := by
    rw [← hdiscrK]
    show Algebra.discr K ⇑pbL.basis = _
    rw [hnorm, hpbLgen, haeval, ← hintnorm, map_mul, map_pow, map_neg, map_one]
  have hAeq : Algebra.discr A ⇑pb.basis
      = (-1) ^ k * Algebra.intNorm A B (aeval θ (derivative f)) :=
    IsFractionRing.injective A K hKeq
  refine ⟨(isUnit_one.neg.pow k).unit, ?_⟩
  rw [IsUnit.unit_spec, hAeq]; ring

namespace PadicField

variable (K : Type*) [Field K] {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K] [PadicField K p]

namespace Extension

variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [PadicField L p]
  [Algebra K L] [Module.Finite K L] [IsScalarTower ℚ_[p] K L]

/-- The *different exponent* `δ(L / K)` : the
exponent of `𝔪_L` in the different ideal `𝔡_{L/K} = differentIdeal 𝒪_K 𝒪_L`, i.e.
the integer `δ` with `𝔡_{L/K} = 𝔪_L ^ δ`. -/
def differentExponent : ℕ :=
  multiplicity (IsLocalRing.maximalIdeal (𝒪 L)) (differentIdeal (𝒪 K) (𝒪 L))

/-- The *discriminant exponent* `d(L / K) = v_K(disc(L/K))` :
the exponent of `𝔪_K` in the ideal generated by the discriminant of an `𝒪_K`-basis of `𝒪_L`.  -/
def discriminantExponent : ℕ :=
  multiplicity (IsLocalRing.maximalIdeal (𝒪 K))
    (Ideal.span {Algebra.discr (𝒪 K)
      ⇑(Module.Free.chooseBasis (𝒪 K) (𝒪 L))})

/-! ### Reduction of the discriminant identities to a single bridge lemma

The discriminant statements below rest on the relative identity `disc(L/K) =
N_{L/K}(𝔡_{L/K})` (`relNorm_differentIdeal_eq_span_discr`). Given that identity,
`d = f · δ` and `d = 0 ↔ e = 1` are valuation-theoretic computations in the DVRs
`𝒪_K`, `𝒪_L`, using `N_{L/K}(𝔪_L) = 𝔪_K ^ f` and multiplicities. -/

attribute [local instance] FractionRing.liftAlgebra


/-- Separability of `L / K` transported to the canonical fraction rings of `𝒪_K`,
`𝒪_L`, as required by Mathlib's relative different-ideal API. -/
instance separable_fractionRing :
    Algebra.IsSeparable (FractionRing (𝒪 K)) (FractionRing (𝒪 L)) := by
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  refine Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv (𝒪 K) K).symm.toRingEquiv
    (FractionRing.algEquiv (𝒪 L) L).symm.toRingEquiv ?_
  ext x
  have h := IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝒪 K) K)
    (FractionRing.algEquiv (𝒪 L) L) ((FractionRing.algEquiv (𝒪 K) K).symm x)
  simp only [AlgEquiv.apply_symm_apply] at h
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact (AlgEquiv.eq_symm_apply _).mpr h.symm

theorem inertiaDeg_ne_zero : inertiaDeg K L ≠ 0 :=
  (Ideal.inertiaDeg_pos (IsLocalRing.maximalIdeal (𝒪 K))
    (IsLocalRing.maximalIdeal (𝒪 L))).ne'

/-- The relative "discriminant equals the norm of the different":
  `N_{L/K}(𝔡_{L/K}) = (disc(L/K))` as ideals of `𝒪_K`.-/
theorem relNorm_differentIdeal_eq_span_discr :
    Ideal.relNorm (𝒪 K) (differentIdeal (𝒪 K) (𝒪 L)) =
      Ideal.span {Algebra.discr (𝒪 K) ⇑(Module.Free.chooseBasis (𝒪 K) (𝒪 L))} := by
  classical
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  obtain ⟨θ, hθtop⟩ : ∃ θ : 𝒪 L, Algebra.adjoin (𝒪 K) ({θ} : Set (𝒪 L)) = ⊤ :=
    Monogenicity.mono_exists_primitive
  have hθ_int : IsIntegral (𝒪 K) θ := Algebra.IsIntegral.isIntegral θ
  let e : ↥(Algebra.adjoin (𝒪 K) ({θ} : Set (𝒪 L))) ≃ₐ[𝒪 K] (𝒪 L) :=
    (Subalgebra.equivOfEq _ _ hθtop).trans Subalgebra.topEquiv
  let pb : PowerBasis (𝒪 K) (𝒪 L) := (Algebra.adjoin.powerBasis' hθ_int).map e
  have hpb_gen : pb.gen = θ := by
    show e (Algebra.adjoin.powerBasis' hθ_int).gen = θ
    rw [Algebra.adjoin.powerBasis'_gen]; rfl
  have hθL_int : IsIntegral K (algebraMap (𝒪 L) L θ) := Algebra.IsIntegral.isIntegral _
  have hmin : minpoly K (algebraMap (𝒪 L) L θ) =
      Polynomial.map (algebraMap (𝒪 K) K) (minpoly (𝒪 K) θ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hθ_int
  have hfdeg : (minpoly (𝒪 K) θ).natDegree = Module.finrank K L := by
    have h1 : pb.dim = (minpoly (𝒪 K) θ).natDegree := by
      show (Algebra.adjoin.powerBasis' hθ_int).dim = _
      rw [Algebra.adjoin.powerBasis'_dim]
    have h2 : Module.finrank (𝒪 K) (𝒪 L) = pb.dim := pb.finrank
    rw [← h1, ← h2]; exact (free_finrank K L).2
  have hdegK : (minpoly K (algebraMap (𝒪 L) L θ)).natDegree =
      (minpoly (𝒪 K) θ).natDegree := by
    rw [hmin, Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective (𝒪 K) K)]
  have hxK : Algebra.adjoin K {algebraMap (𝒪 L) L θ} = ⊤ := by
    have hsub : (Algebra.adjoin K {algebraMap (𝒪 L) L θ}).toSubmodule = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      show Module.finrank K ↥(Algebra.adjoin K {algebraMap (𝒪 L) L θ}) = Module.finrank K L
      rw [(Algebra.adjoin.powerBasis' hθL_int).finrank, Algebra.adjoin.powerBasis'_dim,
        hdegK, hfdeg]
    have htop : (⊤ : Subalgebra K L).toSubmodule = (⊤ : Submodule K L) := by ext x; simp
    exact Subalgebra.toSubmodule_injective (hsub.trans htop.symm)
  have hcond : conductor (𝒪 K) θ = ⊤ := by
    rw [Ideal.eq_top_iff_one, mem_conductor_iff]
    intro b
    rw [one_mul, hθtop]
    exact Algebra.mem_top
  have hdiff : differentIdeal (𝒪 K) (𝒪 L) =
      Ideal.span {Polynomial.aeval θ (Polynomial.derivative (minpoly (𝒪 K) θ))} := by
    have h := conductor_mul_differentIdeal (𝒪 K) K L θ hxK
    rwa [hcond, Ideal.top_mul] at h
  have hG2 := intNorm_deriv_minpoly_associated_discr (K := K) (L := L) pb
  rw [hpb_gen] at hG2
  have hG1 := Algebra.discr_associated_of_basis (R := 𝒪 K)
    pb.basis (Module.Free.chooseBasis (𝒪 K) (𝒪 L))
  rw [hdiff, Ideal.relNorm_singleton]
  exact Ideal.span_singleton_eq_span_singleton.mpr (hG2.trans hG1)

open IsLocalRing in
/-- `𝔪_L` is unramified over `𝒪_K` iff `e(L/K) = 1`. -/
theorem isUnramifiedAt_maximalIdeal_iff :
    Algebra.IsUnramifiedAt (𝒪 K) (IsLocalRing.maximalIdeal (𝒪 L)) ↔ IsUnramified K L := by
  have hp : maximalIdeal (𝒪 L) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝒪 L)
  have hover : Ideal.under (𝒪 K) (maximalIdeal (𝒪 L)) = maximalIdeal (𝒪 K) :=
    Ideal.LiesOver.over.symm
  letI := Localization.AtPrime.algebraOfLiesOver
    (Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))) (maximalIdeal (𝒪 L))
  haveI : Finite (𝒪 K ⧸ Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))) := by
    rw [hover]
    exact inferInstanceAs (Finite (IsLocalRing.ResidueField (𝒪 K)))
  haveI : Finite ((Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))).ResidueField) := inferInstance
  haveI : Finite (𝒪 L ⧸ maximalIdeal (𝒪 L)) := inferInstanceAs
    (Finite (IsLocalRing.ResidueField (𝒪 L)))
  haveI : Finite ((maximalIdeal (𝒪 L)).ResidueField) := inferInstance
  haveI : PerfectField ((Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))).ResidueField) := inferInstance
  haveI : Algebra.IsAlgebraic ((Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))).ResidueField)
      ((maximalIdeal (𝒪 L)).ResidueField) := inferInstance
  rw [Algebra.isUnramifiedAt_iff_map_eq (𝒪 K)
      (Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))) (maximalIdeal (𝒪 L)),
    and_iff_right (Algebra.IsAlgebraic.isSeparable_of_perfectField :
      Algebra.IsSeparable ((Ideal.under (𝒪 K) (maximalIdeal (𝒪 L))).ResidueField)
        ((maximalIdeal (𝒪 L)).ResidueField)),
    ← Ideal.IsDedekindDomain.ramificationIdx_eq_one_iff hp Ideal.map_comap_le]
  show Ideal.ramificationIdx (Ideal.under (𝒪 K) (maximalIdeal (𝒪 L)))
      (maximalIdeal (𝒪 L)) = 1 ↔ IsUnramified K L
  rw [hover]
  exact Iff.rfl

/-- The discriminant exponent equals the residue degree times the different exponent:
`d = f · δ`, since `N_{L/K}(𝔪_L) = 𝔪_K ^ f` and the discriminant is the norm of the different. -/
theorem discExponent_eq_inertiaDeg_mul_differentExponent :
    discriminantExponent K L = inertiaDeg K L * differentExponent K L := by
  have hd : differentIdeal (𝒪 K) (𝒪 L) ≠ ⊥ := differentIdeal_ne_bot
  have hdpow : differentIdeal (𝒪 K) (𝒪 L) =
      (IsLocalRing.maximalIdeal (𝒪 L)) ^ (differentExponent K L) :=
    eq_maximalIdeal_pow_multiplicity hd
  have hrelmax : Ideal.relNorm (𝒪 K) (IsLocalRing.maximalIdeal (𝒪 L)) =
      (IsLocalRing.maximalIdeal (𝒪 K)) ^ (inertiaDeg K L) :=
    Ideal.relNorm_eq_pow_of_isMaximal _ _
  have key : Ideal.span {Algebra.discr (𝒪 K) ⇑(Module.Free.chooseBasis (𝒪 K) (𝒪 L))}
      = (IsLocalRing.maximalIdeal (𝒪 K)) ^ (inertiaDeg K L * differentExponent K L) := by
    rw [← relNorm_differentIdeal_eq_span_discr K L, hdpow, map_pow, hrelmax, ← pow_mul]
  show multiplicity (IsLocalRing.maximalIdeal (𝒪 K))
      (Ideal.span {Algebra.discr (𝒪 K) ⇑(Module.Free.chooseBasis (𝒪 K) (𝒪 L))}) = _
  rw [key]; exact multiplicity_maximalIdeal_pow _


open IsLocalRing in
/-- Lower bound of Dedekind's different theorem: `e - 1 ≤ δ`. -/
lemma ramificationIdx_sub_one_le_differentExponent :
    ramificationIdx K L - 1 ≤ differentExponent K L := by
  have hmK : maximalIdeal (𝒪 K) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝒪 K)
  have hd : differentIdeal (𝒪 K) (𝒪 L) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : FiniteMultiplicity (maximalIdeal (𝒪 L)) (differentIdeal (𝒪 K) (𝒪 L)) :=
    FiniteMultiplicity.of_not_isUnit
      (Ideal.isUnit_iff.not.mpr (IsLocalRing.maximalIdeal.isMaximal (𝒪 L)).ne_top)
      (by rw [Ideal.zero_eq_bot]; exact hd)
  have hdvd : (maximalIdeal (𝒪 L)) ^ (ramificationIdx K L) ∣
      (maximalIdeal (𝒪 K)).map (algebraMap (𝒪 K) (𝒪 L)) :=
    Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx
  have hdvd' : (maximalIdeal (𝒪 L)) ^ (ramificationIdx K L - 1) ∣
      differentIdeal (𝒪 K) (𝒪 L) :=
    pow_sub_one_dvd_differentIdeal (P := maximalIdeal (𝒪 L)) (e := ramificationIdx K L)
      (hp := hmK) (hP := hdvd)
  exact hfin.le_multiplicity_of_pow_dvd hdvd'

open IsLocalRing in
/-- Wild residue-trace fact: when `p ∣ e`, every integral trace lands in `𝔪_K`.
Uses the residue-trace scaling `mk(Tr x) = e • Tr_{k_L/k_K}(x̄)` and `e = 0` in
characteristic `p`. -/
lemma intTrace_mem_maximalIdeal_of_dvd_ramificationIdx
    (hdvd : (p : ℕ) ∣ ramificationIdx K L) :
    ∀ b : 𝒪 L, Algebra.intTrace (𝒪 K) (𝒪 L) b ∈ IsLocalRing.maximalIdeal (𝒪 K) := by
  have hP0 : maximalIdeal (𝒪 L) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝒪 L)
  have hPe := map_maximalIdeal_eq_pow_ramificationIdx K L
  haveI hene : NeZero (ramificationIdx K L) := ramificationIdx_ne_zero K L
  haveI hene2 : NeZero (Ideal.ramificationIdx (R := 𝒪 K) (S := 𝒪 L)
    (maximalIdeal (𝒪 K)) (maximalIdeal (𝒪 L))) := hene
  haveI hmaxK : (maximalIdeal (𝒪 K)).IsMaximal := IsLocalRing.maximalIdeal.isMaximal (𝒪 K)
  haveI hmaxL : (maximalIdeal (𝒪 L)).IsMaximal := IsLocalRing.maximalIdeal.isMaximal (𝒪 L)
  letI : Field (𝒪 K ⧸ maximalIdeal (𝒪 K)) := Ideal.Quotient.field _
  letI : Field (𝒪 L ⧸ maximalIdeal (𝒪 L)) := Ideal.Quotient.field _
  haveI : Finite (𝒪 K ⧸ maximalIdeal (𝒪 K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (𝒪 K)))
  haveI : Finite (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (𝒪 L)))
  letI hAlg : Algebra (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
      (maximalIdeal (𝒪 K)) (maximalIdeal (𝒪 L))
  letI : Module (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) := hAlg.toModule
  haveI : Module.Finite (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : PerfectField (𝒪 K ⧸ maximalIdeal (𝒪 K)) := inferInstance
  haveI hsep : Algebra.IsSeparable (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hcharK : CharP (𝒪 K ⧸ maximalIdeal (𝒪 K)) p := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out (p := p.Prime))).mpr ?_
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal (𝒪 K))) p,
      Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [show (p : 𝒪 K) = algebraMap ℤ_[p] (𝒪 K) (p : ℤ_[p]) from (map_natCast _ p).symm] at hu
    have hunit : IsUnit (p : ℤ_[p]) := IsLocalHom.map_nonunit _ hu
    have hmem : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunit
  have hcore := fun x => TraceFiltration.intTrace_residue_scaling
    (p := maximalIdeal (𝒪 K)) (P := maximalIdeal (𝒪 L)) x hP0 hPe
  intro b
  rw [← Ideal.Quotient.eq_zero_iff_mem, hcore b, nsmul_eq_mul]
  apply mul_eq_zero_of_left
  rw [CharP.cast_eq_zero_iff (𝒪 K ⧸ maximalIdeal (𝒪 K)) p]
  exact hdvd

open IsLocalRing in
/-- Tame residue-trace fact: when `p ∤ e`, some integral trace avoids `𝔪_K`.
Uses surjectivity of the residue trace and `e ≠ 0` in characteristic `p`. -/
lemma exists_intTrace_not_mem_maximalIdeal_of_not_dvd
    (htame : IsTamelyRamified K L) :
    ∃ x : 𝒪 L, Algebra.intTrace (𝒪 K) (𝒪 L) x ∉ IsLocalRing.maximalIdeal (𝒪 K) := by
  have hP0 : maximalIdeal (𝒪 L) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝒪 L)
  have hPe := map_maximalIdeal_eq_pow_ramificationIdx K L
  haveI hene : NeZero (ramificationIdx K L) := ramificationIdx_ne_zero K L
  haveI hene2 : NeZero (Ideal.ramificationIdx (R := 𝒪 K) (S := 𝒪 L)
    (maximalIdeal (𝒪 K)) (maximalIdeal (𝒪 L))) := hene
  haveI hmaxK : (maximalIdeal (𝒪 K)).IsMaximal := IsLocalRing.maximalIdeal.isMaximal (𝒪 K)
  haveI hmaxL : (maximalIdeal (𝒪 L)).IsMaximal := IsLocalRing.maximalIdeal.isMaximal (𝒪 L)
  letI : Field (𝒪 K ⧸ maximalIdeal (𝒪 K)) := Ideal.Quotient.field _
  letI : Field (𝒪 L ⧸ maximalIdeal (𝒪 L)) := Ideal.Quotient.field _
  haveI : Finite (𝒪 K ⧸ maximalIdeal (𝒪 K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (𝒪 K)))
  haveI : Finite (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (𝒪 L)))
  letI hAlg : Algebra (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero
      (maximalIdeal (𝒪 K)) (maximalIdeal (𝒪 L))
  letI : Module (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) := hAlg.toModule
  haveI : Module.Finite (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : PerfectField (𝒪 K ⧸ maximalIdeal (𝒪 K)) := inferInstance
  haveI hsep : Algebra.IsSeparable (𝒪 K ⧸ maximalIdeal (𝒪 K)) (𝒪 L ⧸ maximalIdeal (𝒪 L)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hcharK : CharP (𝒪 K ⧸ maximalIdeal (𝒪 K)) p := by
    refine (CharP.charP_iff_prime_eq_zero (Fact.out (p := p.Prime))).mpr ?_
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal (𝒪 K))) p,
      Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [show (p : 𝒪 K) = algebraMap ℤ_[p] (𝒪 K) (p : ℤ_[p]) from (map_natCast _ p).symm] at hu
    have hunit : IsUnit (p : ℤ_[p]) := IsLocalHom.map_nonunit _ hu
    have hmem : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hunit
  have hcore := fun x => TraceFiltration.intTrace_residue_scaling
    (p := maximalIdeal (𝒪 K)) (P := maximalIdeal (𝒪 L)) x hP0 hPe
  obtain ⟨y, hy⟩ := Algebra.trace_surjective
    (K := 𝒪 K ⧸ maximalIdeal (𝒪 K)) (L := 𝒪 L ⧸ maximalIdeal (𝒪 L)) 1
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y
  have htr : (Ideal.Quotient.mk (maximalIdeal (𝒪 K)))
      (Algebra.intTrace (𝒪 K) (𝒪 L) x) ≠ 0 := by
    rw [hcore x, hx, hy, nsmul_eq_mul, mul_one, ne_eq,
      CharP.cast_eq_zero_iff (𝒪 K ⧸ maximalIdeal (𝒪 K)) p]
    exact htame
  exact ⟨x, by rw [← Ideal.Quotient.eq_zero_iff_mem]; exact htr⟩

open scoped nonZeroDivisors in
open IsLocalRing in
/-- Wild case of Dedekind's different theorem: when `p ∣ e`, `e ≤ δ`. -/
lemma ramificationIdx_le_differentExponent_of_dvd
    (hdvd : (p : ℕ) ∣ ramificationIdx K L) :
    ramificationIdx K L ≤ differentExponent K L := by
  haveI : Algebra.IsSeparable K L := isSeparable_of_padicExtension p K L
  have hP0 : maximalIdeal (𝒪 L) ≠ ⊥ := IsDiscreteValuationRing.not_a_field (𝒪 L)
  have hd : differentIdeal (𝒪 K) (𝒪 L) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : FiniteMultiplicity (maximalIdeal (𝒪 L)) (differentIdeal (𝒪 K) (𝒪 L)) :=
    FiniteMultiplicity.of_not_isUnit
      (Ideal.isUnit_iff.not.mpr (IsLocalRing.maximalIdeal.isMaximal (𝒪 L)).ne_top)
      (by rw [Ideal.zero_eq_bot]; exact hd)
  have hPe := map_maximalIdeal_eq_pow_ramificationIdx K L
  have hmem : ∀ b : 𝒪 L, Algebra.intTrace (𝒪 K) (𝒪 L) b ∈ maximalIdeal (𝒪 K) :=
    intTrace_mem_maximalIdeal_of_dvd_ramificationIdx K L hdvd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (𝒪 K)
  have hspan : maximalIdeal (𝒪 K) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖne : (algebraMap (𝒪 K) K) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝒪 K) K)).mpr hϖ.ne_zero
  have hIne : (↑(maximalIdeal (𝒪 L) ^ ramificationIdx K L) : FractionalIdeal (𝒪 L)⁰ L) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ hP0)
  have hle_id : differentIdeal (𝒪 K) (𝒪 L) ≤ maximalIdeal (𝒪 L) ^ ramificationIdx K L := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal L,
      differentialIdeal_le_fractionalIdeal_iff (K := K) (L := L) hIne,
      Submodule.map_le_iff_le_comap]
    intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply]
    have hyϖmem : algebraMap (𝒪 L) L (algebraMap (𝒪 K) (𝒪 L) ϖ) ∈
        (↑(maximalIdeal (𝒪 L) ^ ramificationIdx K L) : FractionalIdeal (𝒪 L)⁰ L) := by
      rw [FractionalIdeal.mem_coeIdeal]
      refine ⟨algebraMap (𝒪 K) (𝒪 L) ϖ, ?_, rfl⟩
      rw [← hPe]
      exact Ideal.mem_map_of_mem _ (hspan ▸ Ideal.mem_span_singleton_self ϖ)
    obtain ⟨c₀, hc₀⟩ := (FractionalIdeal.mem_one_iff _).mp
      ((FractionalIdeal.mem_inv_iff hIne).mp hz _ hyϖmem)
    have htower : algebraMap (𝒪 L) L (algebraMap (𝒪 K) (𝒪 L) ϖ)
        = algebraMap K L (algebraMap (𝒪 K) K ϖ) := by
      rw [← IsScalarTower.algebraMap_apply (𝒪 K) (𝒪 L) L,
        ← IsScalarTower.algebraMap_apply (𝒪 K) K L]
    rw [htower] at hc₀
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hspan ▸ hmem c₀)
    have hkey : (algebraMap (𝒪 K) K ϖ) * Algebra.trace K L z
        = (algebraMap (𝒪 K) K ϖ) * algebraMap (𝒪 K) K d := by
      have h1 : Algebra.trace K L (z * algebraMap K L (algebraMap (𝒪 K) K ϖ))
          = (algebraMap (𝒪 K) K ϖ) * Algebra.trace K L z := by
        rw [mul_comm z, ← Algebra.smul_def, map_smul, smul_eq_mul]
      have h2 : Algebra.trace K L (z * algebraMap K L (algebraMap (𝒪 K) K ϖ))
          = algebraMap (𝒪 K) K (Algebra.intTrace (𝒪 K) (𝒪 L) c₀) := by
        rw [← hc₀]; exact (Algebra.algebraMap_intTrace c₀).symm
      rw [h1] at h2
      rw [h2, hd, map_mul]
    rw [Submodule.mem_one]
    exact ⟨d, (mul_left_cancel₀ hϖne hkey).symm⟩
  exact hfin.pow_dvd_iff_le_multiplicity.mp (Ideal.dvd_iff_le.mpr hle_id)

open IsLocalRing in
/-- Tame case of Dedekind's different theorem: when `p ∤ e`, `δ < e`, hence the lower
bound `e - 1 ≤ δ` is an equality. -/
lemma differentExponent_lt_ramificationIdx_of_not_dvd
    (htame : IsTamelyRamified K L) :
    differentExponent K L < ramificationIdx K L := by
  have hd : differentIdeal (𝒪 K) (𝒪 L) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : FiniteMultiplicity (maximalIdeal (𝒪 L)) (differentIdeal (𝒪 K) (𝒪 L)) :=
    FiniteMultiplicity.of_not_isUnit
      (Ideal.isUnit_iff.not.mpr (IsLocalRing.maximalIdeal.isMaximal (𝒪 L)).ne_top)
      (by rw [Ideal.zero_eq_bot]; exact hd)
  have hPe := map_maximalIdeal_eq_pow_ramificationIdx K L
  obtain ⟨x, hnotmem⟩ := exists_intTrace_not_mem_maximalIdeal_of_not_dvd K L htame
  have hPmul : (maximalIdeal (𝒪 L)) ^ (ramificationIdx K L) * (⊤ : Ideal (𝒪 L))
      = Ideal.map (algebraMap (𝒪 K) (𝒪 L)) (maximalIdeal (𝒪 K)) := by
    rw [Ideal.mul_top]; exact hPe.symm
  have hndvd : ¬ (maximalIdeal (𝒪 L)) ^ (ramificationIdx K L) ∣
      differentIdeal (𝒪 K) (𝒪 L) :=
    not_dvd_differentIdeal_of_intTrace_not_mem
      (P := maximalIdeal (𝒪 L) ^ ramificationIdx K L) (Q := ⊤)
      (hP := hPmul) (x := x) (hxQ := Submodule.mem_top) (hx := hnotmem)
  by_contra hle2
  push Not at hle2
  exact hndvd (hfin.pow_dvd_iff_le_multiplicity.mpr hle2)

open IsLocalRing in
/-- Dedekind's different theorem: the different exponent
satisfies `δ ≥ e - 1`, with equality exactly when `L / K` is tamely ramified (`p ∤ e`). -/
theorem differentExponent_tame :
    ramificationIdx K L - 1 ≤ differentExponent K L ∧
      (differentExponent K L = ramificationIdx K L - 1 ↔ IsTamelyRamified K L) := by
  have hge := ramificationIdx_sub_one_le_differentExponent K L
  haveI hene : NeZero (ramificationIdx K L) := ramificationIdx_ne_zero K L
  refine ⟨hge, ?_, ?_⟩
  · intro hδ
    by_contra htame'
    rw [IsTamelyRamified, not_not] at htame'
    have hple := ramificationIdx_le_differentExponent_of_dvd K L htame'
    have he1 : 1 ≤ ramificationIdx K L := Nat.one_le_iff_ne_zero.mpr hene.out
    omega
  · intro htame
    have hlt := differentExponent_lt_ramificationIdx_of_not_dvd K L htame
    exact le_antisymm (Nat.le_pred_of_lt hlt) hge

/-- The discriminant exponent vanishes exactly when `L / K` is unramified : `d = 0 ↔ e = 1`. -/
theorem discExponent_eq_zero_iff_unramified :
    discriminantExponent K L = 0 ↔ IsUnramified K L := by
  have hd : differentIdeal (𝒪 K) (𝒪 L) ≠ ⊥ := differentIdeal_ne_bot
  rw [discExponent_eq_inertiaDeg_mul_differentExponent K L, Nat.mul_eq_zero,
    or_iff_right (inertiaDeg_ne_zero K L)]
  show multiplicity (IsLocalRing.maximalIdeal (𝒪 L)) (differentIdeal (𝒪 K) (𝒪 L)) = 0 ↔ _
  rw [multiplicity_eq_zero, not_dvd_differentIdeal_iff]
  exact isUnramifiedAt_maximalIdeal_iff K L

/-- Tame discriminant exponent : if `L / K` is tamely ramified then `d = f · (e - 1)`.  -/
theorem discExponent_tame (h : IsTamelyRamified K L) :
    discriminantExponent K L = inertiaDeg K L * (ramificationIdx K L - 1) := by
  rw [discExponent_eq_inertiaDeg_mul_differentExponent K L,
    (differentExponent_tame K L).2.mpr h]

end Extension

end PadicField
