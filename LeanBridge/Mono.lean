import Mathlib

namespace Neukirch.Chapter2.Sections8to10

open scoped WithZero

/-!
# §10 Monogenicity — Neukirch II.10.4 structure theorem (bottom-up build)

This file develops, **bottom-up and non-circularly**, the irreducible kernel of
Neukirch II.10.4: the *structure theorem* that the family of monomials
`{ξ^j · π^k : j < f, k < e}` is a `κ`-basis of

  `Q := 𝒪 ⧸ Ideal.map (algebraMap 𝒪K 𝒪) (𝔪K)`,

where `κ = ResidueField 𝒪K`, `λ = ResidueField 𝒪`, `f = [λ : κ]`, `e` the
ramification index, `ξ` a lift of a primitive element `ξ̄` of `λ/κ`, and `π` a
uniformizer of `𝒪`.

Roughly ~12 prior agents established that the §10 keystone
`thm_10_4_aux_iterate_h_lift_coeff_mem` (in `Chapter2_Section10.lean`) reduces
to exactly this structure theorem, with **no** Mathlib lemma and **no**
decomposition shortcut available — every Hensel/Newton/spanning route bottoms
out here.  This file builds the structure theorem *directly*.

* **Non-circular by construction.**  It imports only `Mathlib`; it does NOT
  import `Chapter2_Section10` (nor §6/§7/§9).  It is therefore importable *by*
  `Chapter2_Section10` later, with zero risk of a cycle.

* **Milestones.**
  - **M1 (this milestone).** State the generic target theorem with the exact
    keystone typeclass setup (body `sorry`, the only allowed `sorry`); prove
    sorry-free the foundational DVR/ramification facts everything else consumes:
    `𝔪 = (π)`, `𝔪K·𝒪 = 𝔪^e`, the dimension anchor `dim_κ Q = [𝒪 : 𝒪K]`, and
    `π^e ∈ 𝔪K·𝒪` (nilpotency of `π̄` in `Q`).
  - **M2–M5.** Fill the target theorem (linear independence + spanning of the
    `{ξ^j π^k}` family, then wire it into the keystone).

The typeclass conventions below mirror **exactly** the keystone
`thm_10_4_aux_iterate_h_lift_coeff_mem` and the proved helpers
`thm_10_4_aux_finrank_quot`, `thm_10_4_aux_quot_free`,
`thm_10_4_aux_primitive_powers_span`, so M5 can wire this in without friction.
-/

/-! ## M1 foundation lemmas — DVR / ramification bedrock (all sorry-free) -/

/-- **M1-(a)** A uniformizer `π` of the DVR `𝒪` (`Irreducible π`) generates the
maximal ideal: `𝔪 = (π)`.

Mathlib: `Irreducible.maximalIdeal_eq` (equivalently
`IsDiscreteValuationRing.irreducible_iff_uniformizer`). -/
theorem mono_maximalIdeal_eq_span
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [IsDiscreteValuationRing 𝒪]
    {π : 𝒪} (hπ : Irreducible π) :
    IsLocalRing.maximalIdeal 𝒪 = Ideal.span {π} :=
  hπ.maximalIdeal_eq

/-- **M1-(b)-def** The ramification index `e` of the finite local DVR extension
`𝒪K → 𝒪`.

Defined **DVR-directly** (NOT via the Dedekind `Ideal.ramificationIdx`, whose
Mathlib API needs `IsFractionRing`/Dedekind apparatus unavailable here — a
known friction prior agents hit with `ramificationIdx_mul_inertiaDeg_of_isLocalRing`).
Concretely: `Ideal.map (algebraMap 𝒪K 𝒪) 𝔪K` is a *nonzero* ideal of the DVR
`𝒪` (nonzero because `algebraMap` is injective via `[FaithfulSMul 𝒪K 𝒪]`), so by
`IsDiscreteValuationRing.ideal_eq_span_pow_irreducible` it equals `(π)^n` for a
unique `n : ℕ`; `e` is that `n`. -/
noncomputable def mono_ramificationIdx
    (𝒪K : Type*) [CommRing 𝒪K] [IsDomain 𝒪K] [IsLocalRing 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪]
    {π : 𝒪} (hπ : Irreducible π) : ℕ :=
  Classical.choose
    (IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K))
      (by
        have hmK : IsLocalRing.maximalIdeal 𝒪K ≠ ⊥ :=
          IsDiscreteValuationRing.not_a_field 𝒪K
        exact Ideal.map_ne_bot_of_ne_bot hmK)
      hπ)

/-- **M1-(b)** `𝔪K · 𝒪 = 𝔪^e` for the ramification index `e`.

Here `𝔪K · 𝒪 = Ideal.map (algebraMap 𝒪K 𝒪) 𝔪K`.  Immediate from the definition
of `e := mono_ramificationIdx` (`Classical.choose_spec` gives
`map … 𝔪K = (π)^e`) combined with `mono_maximalIdeal_eq_span`
(`𝔪 = (π)`) and `Ideal.span_singleton_pow`. -/
theorem mono_mapMK_eq_pow
    {𝒪K : Type*} [CommRing 𝒪K] [IsDomain 𝒪K] [IsLocalRing 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪]
    {π : 𝒪} (hπ : Irreducible π) :
    Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K) =
      (IsLocalRing.maximalIdeal 𝒪) ^
        (mono_ramificationIdx 𝒪K 𝒪 hπ) := by
  have hspec :
      Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K) =
        Ideal.span {π ^ (mono_ramificationIdx 𝒪K 𝒪 hπ)} :=
    Classical.choose_spec
      (IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
        (s := Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K))
        (by
          have hmK : IsLocalRing.maximalIdeal 𝒪K ≠ ⊥ :=
            IsDiscreteValuationRing.not_a_field 𝒪K
          exact Ideal.map_ne_bot_of_ne_bot hmK)
        hπ)
  rw [hspec, mono_maximalIdeal_eq_span hπ, Ideal.span_singleton_pow]

/-- **M1-(c)** Dimension anchor: `dim_κ Q = [𝒪 : 𝒪K]`, where
`Q := 𝒪 ⧸ Ideal.map (algebraMap 𝒪K 𝒪) 𝔪K` and `κ := 𝒪K ⧸ 𝔪K`.

This is the pure DVR/ramification anchor for the count `[𝒪 : 𝒪K] = e · f`
(the missing factor `dim_κ Q = e · f` is M2/M3 content).  Proved by the exact
technique of the keystone helper `thm_10_4_aux_finrank_quot`, specialised to
the *ring*-quotient picture `Q` (no `restrictScalars`/`smul_top` bridge needed):
free over the DVR `𝒪K` + Mathlib `IsLocalRing.finrank_quotient_map`. -/
theorem mono_finrank_quot_eq_finrank
    {𝒪K : Type*} [CommRing 𝒪K] [IsDomain 𝒪K] [IsLocalRing 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪] :
    Module.finrank (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K)
      (𝒪 ⧸ (Ideal.map (algebraMap 𝒪K 𝒪)
        (IsLocalRing.maximalIdeal 𝒪K))) =
    Module.finrank 𝒪K 𝒪 := by
  -- `𝒪` is torsion-free over `𝒪K` (algebraMap injective via `FaithfulSMul`),
  -- finite over the DVR (hence PID) `𝒪K`, so free.
  have _hTF : Module.IsTorsionFree 𝒪K 𝒪 :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := 𝒪K) (A := 𝒪)).mpr
      (FaithfulSMul.algebraMap_injective 𝒪K 𝒪)
  haveI _hFree : Module.Free 𝒪K 𝒪 :=
    Module.free_of_finite_type_torsion_free'
  -- Mathlib closes the ring-quotient shape directly.
  exact IsLocalRing.finrank_quotient_map (R := 𝒪K) (S := 𝒪)

/-- **M1-(d)** Nilpotency seed: `π^e ∈ 𝔪K · 𝒪`.

Hence `π̄^e = 0` in `Q := 𝒪 ⧸ 𝔪K·𝒪`.  Immediate from `mono_mapMK_eq_pow`
(`𝔪K·𝒪 = 𝔪^e`) and `mono_maximalIdeal_eq_span` (`𝔪 = (π)`), since
`π^e ∈ (π)^e = 𝔪^e`. -/
theorem mono_pi_pow_e_mem_mapMK
    {𝒪K : Type*} [CommRing 𝒪K] [IsDomain 𝒪K] [IsLocalRing 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪]
    {π : 𝒪} (hπ : Irreducible π) :
    π ^ (mono_ramificationIdx 𝒪K 𝒪 hπ) ∈
      Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K) := by
  rw [mono_mapMK_eq_pow hπ, mono_maximalIdeal_eq_span hπ,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- Corollary of **M1-(d)**: in `Q := 𝒪 ⧸ 𝔪K·𝒪` the class of `π` is
`e`-nilpotent: `(π̄)^e = 0`. -/
theorem mono_pi_bar_pow_e_eq_zero
    {𝒪K : Type*} [CommRing 𝒪K] [IsDomain 𝒪K] [IsLocalRing 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪]
    {π : 𝒪} (hπ : Irreducible π) :
    (Ideal.Quotient.mk
        (Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)) π)
      ^ (mono_ramificationIdx 𝒪K 𝒪 hπ) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact mono_pi_pow_e_mem_mapMK hπ

/-! ## M2 — the graded-piece isomorphism `λ ≃ₗ[κ] 𝔪^k/𝔪^{k+1}` and its dimension

Fix a uniformizer `π` of the DVR domain `𝒪` (`Irreducible π`).  By **M1**
(`mono_maximalIdeal_eq_span`) the maximal ideal is `𝔪 = (π)`, so the `k`-th
*graded piece* of the `𝔪`-adic filtration is

  `gr_k := 𝔪^k / 𝔪^{k+1} = (π)^k / (π)^{k+1}`.

The standard DVR fact (Neukirch II.10, the "graded ≅ residue field" step):
multiplication by `π^k` induces a `κ`-linear isomorphism

  `λ := ResidueField 𝒪  ≃ₗ[κ]  gr_k`,    `x mod 𝔪 ↦ π^k · x mod 𝔪^{k+1}`,

where `κ := ResidueField 𝒪K = 𝒪K ⧸ 𝔪K` acts on the (residue-field-coefficient)
modules through `𝒪K → 𝒪`, the maximal ideal `𝔪K` annihilating both sides
(it lands in `𝔪` because `algebraMap 𝒪K 𝒪` is a local hom).  Well-definedness
and injectivity use that, in the domain `𝒪`, `π^k x ∈ (π^{k+1}) ↔ x ∈ (π)`
(cancel the non-zero-divisor `π^k`); surjectivity is `(π^k)`'s being principal.

These lemmas are stated for **arbitrary `k : ℕ`** (no `k < e` restriction —
that only enters the later basis count).  Consumed downstream:
* **M3** turns a `κ`-basis `{ξ̄^j : j<f}` of `λ` into the `κ`-basis
  `{ξ^j π^k mod 𝔪^{k+1} : j<f}` of `gr_k` via `mono_gradedPiece_equiv`,
  using the explicit image formula `mono_gradedPiece_equiv_apply`;
* **M4** glues the `gr_k` (`k<e`) into a `κ`-basis of `Q = 𝒪/𝔪K·𝒪`.

The whole development imports only `Mathlib`; it adds **no** new `sorry`
(the sole permitted `sorry` remains the top theorem below).
-/

/-- **M2-(0)** The underlying `𝒪`-linear map of the graded-piece iso:
`mono_gr_lmap π k : 𝒪 →ₗ[𝒪] 𝒪 ⧸ (π)^{k+1}`, `x ↦ π^k · x mod (π)^{k+1}`.

Its range is the graded piece `(π)^k/(π)^{k+1}` (as a submodule of the ring
quotient `𝒪 ⧸ (π)^{k+1}`) and — once `π` is irreducible — its kernel is
exactly `𝔪 = (π)` (`mono_gr_lmap_ker`). -/
noncomputable def mono_gr_lmap
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    (π : 𝒪) (k : ℕ) :
    𝒪 →ₗ[𝒪] (𝒪 ⧸ (Ideal.span {π} ^ (k + 1) : Ideal 𝒪)) :=
  (Ideal.span {π} ^ (k + 1) : Ideal 𝒪).mkQ.comp (LinearMap.mulLeft 𝒪 (π ^ k))

@[simp] theorem mono_gr_lmap_apply
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    (π : 𝒪) (k : ℕ) (x : 𝒪) :
    mono_gr_lmap π k x =
      Ideal.Quotient.mk (Ideal.span {π} ^ (k + 1) : Ideal 𝒪) (π ^ k * x) :=
  rfl

/-- **M2-(1a)** Kernel of `mono_gr_lmap`: in the domain `𝒪`, with `π`
irreducible (hence a non-zero-divisor), `π^k x ∈ (π^{k+1}) ↔ x ∈ (π)`, so the
kernel is exactly `Ideal.span {π}` (`= 𝔪` by M1). -/
theorem mono_gr_lmap_ker
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    {π : 𝒪} (hπ : Irreducible π) (k : ℕ) :
    LinearMap.ker (mono_gr_lmap π k) = (Ideal.span {π} : Ideal 𝒪) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  ext x
  simp only [LinearMap.mem_ker, mono_gr_lmap, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  rw [show (Ideal.span {π} ^ (k + 1) : Ideal 𝒪) = Ideal.span {π ^ (k + 1)} from
        (Ideal.span_singleton_pow π (k + 1))]
  rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    rw [pow_succ] at hc
    exact ⟨c, by
      apply mul_left_cancel₀ (pow_ne_zero k hπ0); rw [hc]; ring⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [pow_succ]; ring⟩

variable {𝒪K : Type*} [CommRing 𝒪K] [IsDomain 𝒪K] [IsLocalRing 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [IsDiscreteValuationRing 𝒪]
variable [Algebra 𝒪K 𝒪] [Module.Finite 𝒪K 𝒪] [FaithfulSMul 𝒪K 𝒪]
variable [IsLocalHom (algebraMap 𝒪K 𝒪)]

/-- **M2-(1)** The graded piece `gr_k = 𝔪^k/𝔪^{k+1}`, encoded as the range
submodule `(π)^k/(π)^{k+1} ⊆ 𝒪 ⧸ (π)^{k+1}` of `mono_gr_lmap` (a principal
`𝒪`-submodule, generated by the class of `π^k`).  As an `𝒪`-module it is
killed by `𝔪 = (π)`, hence is a `λ = ResidueField 𝒪`-vector space; through the
local hom `𝒪K → 𝒪` it is also killed by `𝔪K`, hence a
`κ = ResidueField 𝒪K = 𝒪K ⧸ 𝔪K`-vector space (the structure used below). -/
noncomputable def mono_gradedPiece (π : 𝒪) (k : ℕ) :
    Submodule 𝒪 (𝒪 ⧸ (Ideal.span {π} ^ (k + 1) : Ideal 𝒪)) :=
  LinearMap.range (mono_gr_lmap π k)

omit [IsDomain 𝒪K] [IsDiscreteValuationRing 𝒪K] [Module.Finite 𝒪K 𝒪]
  [FaithfulSMul 𝒪K 𝒪] in
/-- **M2-(2a)** `𝔪K` annihilates the graded piece `gr_k`: its image under
`algebraMap 𝒪K 𝒪` lands in `𝔪 = (π)` (local hom + M1), so it multiplies
`(π)^k` into `(π)^{k+1}`, i.e. it acts as `0` on `gr_k`.  This is the torsion
fact that equips `gr_k` with its `κ = 𝒪K ⧸ 𝔪K`-module structure. -/
theorem mono_gradedPiece_isTorsion
    {π : 𝒪} (hπ : Irreducible π) (k : ℕ) :
    Module.IsTorsionBySet 𝒪K (mono_gradedPiece π k)
      (IsLocalRing.maximalIdeal 𝒪K : Set 𝒪K) := by
  -- `𝔪K · 𝒪 ⊆ 𝔪 = (π)`.
  have hmap : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} : Ideal 𝒪) := by
    rw [← mono_maximalIdeal_eq_span hπ]
    exact IsLocalRing.map_maximalIdeal_le (algebraMap 𝒪K 𝒪)
  intro y c
  -- `algebraMap c ∈ 𝔪 = (π)`, so write `algebraMap c = π * d`.
  have hc : algebraMap 𝒪K 𝒪 (c : 𝒪K) ∈ (Ideal.span {π} : Ideal 𝒪) :=
    hmap (Ideal.mem_map_of_mem _ c.2)
  rw [Ideal.mem_span_singleton] at hc
  obtain ⟨d, hd⟩ := hc
  -- represent `y ∈ gr_k` as a class `mk (π^k * x)`.
  obtain ⟨x, hx⟩ := y.2
  apply Subtype.ext
  -- compute the `𝒪K`-scalar action explicitly and show it is `0` in gr_k.
  have hxval : (y : 𝒪 ⧸ (Ideal.span {π} ^ (k + 1) : Ideal 𝒪)) =
      Ideal.Quotient.mk (Ideal.span {π} ^ (k + 1) : Ideal 𝒪) (π ^ k * x) := by
    rw [← hx]; rfl
  rw [Submodule.coe_smul_of_tower, ZeroMemClass.coe_zero, hxval]
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap 𝒪K
        (Ideal.span {π} ^ (k + 1) : Ideal 𝒪) (c : 𝒪K), ← map_mul]
  rw [show (algebraMap 𝒪K 𝒪 (c : 𝒪K)) * (π ^ k * x)
        = π ^ (k + 1) * (d * x) by rw [hd]; ring]
  rw [Ideal.Quotient.eq_zero_iff_mem,
    show (Ideal.span {π} ^ (k + 1) : Ideal 𝒪) = Ideal.span {π ^ (k + 1)} from
      (Ideal.span_singleton_pow π (k + 1)),
    Ideal.mem_span_singleton]
  exact ⟨d * x, rfl⟩

/-- The `κ = 𝒪K ⧸ 𝔪K`-module structure on the graded piece `gr_k`, obtained
from `mono_gradedPiece_isTorsion` via `Module.IsTorsionBySet.module`.  This is
the structure carried by `mono_gradedPiece_equiv` / `mono_finrank_gradedPiece`
(and consumed by M3/M4). -/
@[reducible] noncomputable def mono_gradedPiece_kappaModule
    {π : 𝒪} (hπ : Irreducible π) (k : ℕ) :
    Module (IsLocalRing.ResidueField 𝒪K) (mono_gradedPiece π k) :=
  (mono_gradedPiece_isTorsion hπ k).module

/-- **M2-(2)** The graded-piece isomorphism: the `κ`-linear equivalence

  `λ = ResidueField 𝒪  ≃ₗ[κ]  gr_k = 𝔪^k/𝔪^{k+1}`,

induced by `x ↦ π^k · x`.  Built from the `𝒪`-linear equivalence
`λ ≃ₗ[𝒪] gr_k` (`Submodule.quotEquivOfEq` with `𝔪 = (π)` and M1, then
`LinearMap.quotKerEquivRange` with the kernel computation
`mono_gr_lmap_ker`), upgraded to `κ`-linearity: every `κ`-scalar is a class
`Ideal.Quotient.mk 𝔪K c`, whose action on **both** sides reduces to the
`𝒪K`-action (`Module.IsTorsionBySet.mk_smul`, resp. the residue-field scalar
tower), where the underlying `𝒪K`-linear equivalence is equivariant.

Stated for arbitrary `k : ℕ`. -/
noncomputable def mono_gradedPiece_equiv
    {π : 𝒪} (hπ : Irreducible π) (k : ℕ) :
    letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
    IsLocalRing.ResidueField 𝒪 ≃ₗ[IsLocalRing.ResidueField 𝒪K]
      (mono_gradedPiece π k) :=
  letI instκGr := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
  -- Step 1: the `𝒪`-linear core equivalence `λ ≃ₗ[𝒪] gr_k`.
  let eO : IsLocalRing.ResidueField 𝒪 ≃ₗ[𝒪] (mono_gradedPiece π k) :=
    (Submodule.quotEquivOfEq _ _
      ((mono_maximalIdeal_eq_span hπ).trans
        (mono_gr_lmap_ker hπ k).symm)) ≪≫ₗ
      (mono_gr_lmap π k).quotKerEquivRange
  -- Step 2: restrict scalars to `𝒪K`.
  let eOK : IsLocalRing.ResidueField 𝒪 ≃ₗ[𝒪K] (mono_gradedPiece π k) :=
    eO.restrictScalars 𝒪K
  -- Step 3: upgrade `𝒪K`-linearity to `κ = 𝒪K ⧸ 𝔪K`-linearity.
  { toFun := eOK
    invFun := eOK.symm
    left_inv := eOK.left_inv
    right_inv := eOK.right_inv
    map_add' := eOK.map_add
    map_smul' := by
      intro r y
      -- write the `κ`-scalar `r` as a residue `residue 𝒪K c` of some `c : 𝒪K`.
      obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective (R := 𝒪K) r
      simp only [RingHom.id_apply]
      -- RHS scalar on `gr_k` (its `κ`-module is the `IsTorsionBySet`
      -- one) reduces to the `𝒪K`-scalar (`residue = Quotient.mk`).
      have hgr : (IsLocalRing.residue 𝒪K c) • (eOK y) = c • (eOK y) :=
        Module.IsTorsionBySet.mk_smul (mono_gradedPiece_isTorsion hπ k) c (eOK y)
      -- LHS scalar on `λ = ResidueField 𝒪` reduces via the residue-field
      -- scalar tower `𝒪K → ResidueField 𝒪K → ResidueField 𝒪`.
      have hlam : (IsLocalRing.residue 𝒪K c)
            • (y : IsLocalRing.ResidueField 𝒪) = c • y := by
        have h := IsScalarTower.algebraMap_smul
          (IsLocalRing.ResidueField 𝒪K) c y
        rw [← h]
        rfl
      rw [hgr, hlam]
      -- now both sides are `𝒪K`-scalars; use `𝒪K`-linearity of `eOK`.
      exact eOK.map_smul c y }

omit [IsDomain 𝒪K] [IsDiscreteValuationRing 𝒪K] [Module.Finite 𝒪K 𝒪]
  [FaithfulSMul 𝒪K 𝒪] in
/-- **M2-(2)-apply** Explicit image formula (a `simp` lemma for M3):
`mono_gradedPiece_equiv` sends the class of `x : 𝒪` (`= residue 𝒪 x ∈ λ`) to
the class of `π^k · x` in `gr_k`.  This is what lets M3 compute
`ξ̄^j ↦ ξ^j · π^k mod 𝔪^{k+1}`. -/
@[simp] theorem mono_gradedPiece_equiv_apply
    {π : 𝒪} (hπ : Irreducible π) (k : ℕ) (x : 𝒪) :
    letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
    ((mono_gradedPiece_equiv (𝒪K := 𝒪K) hπ k)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪) x) :
      mono_gradedPiece π k) =
      ⟨Ideal.Quotient.mk (Ideal.span {π} ^ (k + 1) : Ideal 𝒪) (π ^ k * x),
        ⟨x, rfl⟩⟩ := by
  apply Subtype.ext
  rfl

omit [IsDomain 𝒪K] [IsDiscreteValuationRing 𝒪K] [Module.Finite 𝒪K 𝒪]
  [FaithfulSMul 𝒪K 𝒪] in
/-- **M2-(3)** Dimension of the graded piece:
`dim_κ (𝔪^k/𝔪^{k+1}) = dim_κ λ` for every `k : ℕ`
(equal to the inertia degree `f := [λ : κ]`).  Immediate from the
`κ`-linear equivalence `mono_gradedPiece_equiv`. -/
theorem mono_finrank_gradedPiece
    {π : 𝒪} (hπ : Irreducible π) (k : ℕ) :
    letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
    Module.finrank (IsLocalRing.ResidueField 𝒪K)
        (mono_gradedPiece π k) =
      Module.finrank (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.ResidueField 𝒪) := by
  letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
  exact ((mono_gradedPiece_equiv (𝒪K := 𝒪K) hπ k).finrank_eq).symm

/-! ## M3 — a `κ`-basis `{ξ^j π^k : j < f}` of every graded piece `gr_k`

With `κ := ResidueField 𝒪K`, `λ := ResidueField 𝒪`, `f := [λ : κ]`, fix a lift
`ξ : 𝒪` of a *primitive element* `ξ̄ := residue 𝒪 ξ` of `λ/κ`
(`hξ_prim : κ⟮ξ̄⟯ = ⊤`).  Two purely-Mathlib steps:

1. **`λ/κ` is finite, `ξ̄` integral.**  `Module.Finite 𝒪K 𝒪` gives
   `Module.Finite κ λ` (Mathlib instance
   `IsLocalRing.ResidueField.finite_of_module_finite`); a finite algebra over a
   field is integral, so `IsIntegral κ ξ̄`.

2. **Primitive element ⟹ power basis.**  `IntermediateField.adjoin.powerBasis`
   gives a `κ`-`PowerBasis` of `κ⟮ξ̄⟯` with generator `ξ̄`; transporting it along
   `(equivOfEq hξ_prim).trans topEquiv : κ⟮ξ̄⟯ ≃ₐ[κ] λ` (the
   `Field.powerBasisOfFiniteOfSeparable` recipe, re-derived here without using
   separability — `hξ_prim` alone suffices) yields `mono_lambda_powerBasis`,
   a `PowerBasis κ λ` with `gen = ξ̄` and `dim = finrank κ λ`.

3. **Transport to `gr_k`.**  Pushing the resulting `κ`-basis `{ξ̄^j : j<f}` of
   `λ` through M2's `mono_gradedPiece_equiv hπ k : λ ≃ₗ[κ] gr_k` (`Basis.map`),
   and computing the image with `mono_gradedPiece_equiv_apply`
   (`ξ̄^j ↦ π^k·ξ^j mod 𝔪^{k+1}`), gives `mono_gradedPiece_basis hπ k`, a
   `κ`-basis of `gr_k` indexed by `Fin (finrank κ λ)` whose `j`-th vector is the
   class of `ξ^j·π^k`.  No `k < e` restriction (it holds for all `k`; the count
   enters only at the M4 glue).  Adds no `sorry`.
-/

section M3

-- The DVR/finiteness section variables are present in the ambient `variable`
-- block (mirroring the keystone setup) but several M3 lemmas only need the
-- field/algebra structure of the residue extension; silence the resulting
-- "unused section variable" linter noise locally (no statement is weakened).
set_option linter.unusedSectionVars false

variable {ξ : 𝒪}

/-- **M3-(0)** The residue extension `λ/κ` is module-finite: from
`Module.Finite 𝒪K 𝒪` via the Mathlib instance
`IsLocalRing.ResidueField.finite_of_module_finite`.  Recorded as a named lemma
(it is already an instance; this just pins the precise statement M3 consumes,
and supplies `FiniteDimensional`/integrality of `ξ̄`). -/
theorem mono_residueField_finite :
    Module.Finite (IsLocalRing.ResidueField 𝒪K) (IsLocalRing.ResidueField 𝒪) :=
  inferInstance

/-- **M3-(1)** A `κ`-`PowerBasis` of `λ = ResidueField 𝒪` generated by the
primitive element `ξ̄ := residue 𝒪 ξ`.  Built by transporting
`IntermediateField.adjoin.powerBasis` for `κ⟮ξ̄⟯` along
`(equivOfEq hξ_prim).trans topEquiv : κ⟮ξ̄⟯ ≃ₐ[κ] λ`. -/
noncomputable def mono_lambda_powerBasis
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤) :
    PowerBasis (IsLocalRing.ResidueField 𝒪K) (IsLocalRing.ResidueField 𝒪) :=
  haveI : Module.Finite (IsLocalRing.ResidueField 𝒪K)
      (IsLocalRing.ResidueField 𝒪) := inferInstance
  have hξint : IsIntegral (IsLocalRing.ResidueField 𝒪K)
      (IsLocalRing.residue 𝒪 ξ) :=
    Algebra.IsIntegral.isIntegral (IsLocalRing.residue 𝒪 ξ)
  (IntermediateField.adjoin.powerBasis hξint).map
    ((IntermediateField.equivOfEq hξ_prim).trans IntermediateField.topEquiv)

/-- The generator of `mono_lambda_powerBasis` is `ξ̄ := residue 𝒪 ξ`. -/
@[simp] theorem mono_lambda_powerBasis_gen
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤) :
    (mono_lambda_powerBasis (ξ := ξ) hξ_prim).gen = IsLocalRing.residue 𝒪 ξ := by
  unfold mono_lambda_powerBasis
  simp [PowerBasis.map, IntermediateField.adjoin.powerBasis,
    IntermediateField.AdjoinSimple.gen]

/-- The dimension of `mono_lambda_powerBasis` is `finrank κ λ`. -/
theorem mono_lambda_powerBasis_dim
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤) :
    (mono_lambda_powerBasis (ξ := ξ) hξ_prim).dim =
      Module.finrank (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.ResidueField 𝒪) :=
  ((mono_lambda_powerBasis (ξ := ξ) hξ_prim).finrank).symm

/-- The `j`-th vector of `mono_lambda_powerBasis` is `ξ̄^j`. -/
theorem mono_lambda_powerBasis_basis_apply
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤)
    (i : Fin (mono_lambda_powerBasis (ξ := ξ) hξ_prim).dim) :
    (mono_lambda_powerBasis (ξ := ξ) hξ_prim).basis i =
      (IsLocalRing.residue 𝒪 ξ) ^ (i : ℕ) := by
  rw [(mono_lambda_powerBasis (ξ := ξ) hξ_prim).basis_eq_pow i,
    mono_lambda_powerBasis_gen]

/-- **M3-(2)** A `κ`-basis of `λ = ResidueField 𝒪` indexed by
`Fin (finrank κ λ)` whose `j`-th vector is `ξ̄^j`.  This is
`mono_lambda_powerBasis.basis` reindexed along the dimension identity
`finrank κ λ = dim`. -/
noncomputable def mono_lambda_basis
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤) :
    Module.Basis
      (Fin (Module.finrank (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.ResidueField 𝒪)))
      (IsLocalRing.ResidueField 𝒪K) (IsLocalRing.ResidueField 𝒪) :=
  (mono_lambda_powerBasis (ξ := ξ) hξ_prim).basis.reindex
    (finCongr (mono_lambda_powerBasis_dim (ξ := ξ) hξ_prim))

/-- The `j`-th vector of `mono_lambda_basis` is `ξ̄^j`. -/
@[simp] theorem mono_lambda_basis_apply
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤)
    (j : Fin (Module.finrank (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.ResidueField 𝒪))) :
    mono_lambda_basis (ξ := ξ) hξ_prim j =
      (IsLocalRing.residue 𝒪 ξ) ^ (j : ℕ) := by
  rw [mono_lambda_basis, Module.Basis.reindex_apply,
    mono_lambda_powerBasis_basis_apply, finCongr_symm_apply_coe]

/-- **M3-(3)** The headline `κ`-basis of the graded piece
`gr_k = 𝔪^k/𝔪^{k+1}`, indexed by `Fin (finrank κ λ)`, obtained by transporting
`mono_lambda_basis` through the `κ`-linear equivalence
`mono_gradedPiece_equiv hπ k : λ ≃ₗ[κ] gr_k`.  Its `j`-th vector is the class
of `ξ^j·π^k` in `𝒪 ⧸ (π)^{k+1}` (see `mono_gradedPiece_basis_apply`).  Stated
for arbitrary `k : ℕ` (no `k < e`). -/
noncomputable def mono_gradedPiece_basis
    {π : 𝒪} (hπ : Irreducible π) (k : ℕ)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤) :
    letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
    Module.Basis
      (Fin (Module.finrank (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.ResidueField 𝒪)))
      (IsLocalRing.ResidueField 𝒪K) (mono_gradedPiece π k) :=
  letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
  (mono_lambda_basis (ξ := ξ) hξ_prim).map
    (mono_gradedPiece_equiv (𝒪K := 𝒪K) hπ k)

/-- **M3-(3)-apply** Explicit value of the graded-piece basis: the `j`-th
vector of `mono_gradedPiece_basis` is the class of `ξ^j·π^k` in
`𝒪 ⧸ (π)^{k+1}`.  This explicit monomial formula is what M4 glues over
`k = 0, …, e-1`. -/
@[simp] theorem mono_gradedPiece_basis_apply
    {π : 𝒪} (hπ : Irreducible π) (k : ℕ)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤)
    (j : Fin (Module.finrank (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.ResidueField 𝒪))) :
    letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
    (mono_gradedPiece_basis (ξ := ξ) hπ k hξ_prim j :
        mono_gradedPiece π k) =
      ⟨Ideal.Quotient.mk (Ideal.span {π} ^ (k + 1) : Ideal 𝒪)
          (ξ ^ (j : ℕ) * π ^ k),
        ⟨ξ ^ (j : ℕ), by rw [mono_gr_lmap_apply, mul_comm]⟩⟩ := by
  letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ k
  rw [mono_gradedPiece_basis, Module.Basis.map_apply, mono_lambda_basis_apply]
  rw [show (IsLocalRing.residue 𝒪 ξ) ^ (j : ℕ)
        = Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪) (ξ ^ (j : ℕ)) by
      rw [map_pow]; rfl]
  rw [mono_gradedPiece_equiv_apply (𝒪K := 𝒪K) hπ k (ξ ^ (j : ℕ))]
  apply Subtype.ext
  show Ideal.Quotient.mk (Ideal.span {π} ^ (k + 1) : Ideal 𝒪) (π ^ k * ξ ^ (j : ℕ))
      = Ideal.Quotient.mk (Ideal.span {π} ^ (k + 1) : Ideal 𝒪) (ξ ^ (j : ℕ) * π ^ k)
  rw [mul_comm (π ^ k) (ξ ^ (j : ℕ))]

end M3

/-! ## M4 — gluing the graded bases into a `κ`-basis of `Q`

We realise the standard Neukirch II.10.4 filtration glue.  Write
`I := Ideal.span {π}` and `M n := 𝒪 ⧸ I^n`.  For `n ≤ e` the ideal
`𝔪K · 𝒪 = I^e` is contained in `I^n`, so `𝔪K` annihilates `M n`, giving it a
`κ = ResidueField 𝒪K`-vector-space structure (the same `IsTorsionBySet`
construction M2 uses for `gr_k`).  The bottom step of `M (n+1)` is the
`κ`-subspace `Wκ n := range (φ n)` where
`φ n : λ →ₗ[κ] M (n+1)`, `residue 𝒪 x ↦ mk (π^n · x)`, is M2's graded-piece
map composed with the inclusion `gr_n ↪ M (n+1)`; M3's `κ`-basis `{ξ̄^j}` of
`λ` pushes to a `κ`-basis of `Wκ n` whose `j`-th vector is `mk (ξ^j π^n)`.
Noether's third isomorphism gives `M (n+1) ⧸ Wκ n ≃ₗ[κ] M n`.  `Basis.sumQuot`
then glues a `κ`-basis of `M n` (inductive) and the `κ`-basis of `Wκ n` into a
`κ`-basis of `M (n+1)`, indexed by `Fin f ⊕ (Fin f × Fin n) ≃ Fin f × Fin (n+1)`.
At `n = e` we have `I^e = 𝔪K·𝒪`, and transporting the `κ`-structure to the
canonical one on `Q = 𝒪 ⧸ 𝔪K·𝒪` finishes the structure theorem.
-/

section M4

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ξ : 𝒪}

/-- `𝔪K` annihilates `M n = 𝒪 ⧸ I^n` whenever `𝔪K·𝒪 = I^e ≤ I^n`
(equivalently `n ≤ e`): the `IsTorsionBySet` fact equipping `M n` with its
`κ`-vector-space structure (same construction as M2's `gr_k`). -/
theorem mono_quot_isTorsion
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪)) :
    Module.IsTorsionBySet 𝒪K
      (𝒪 ⧸ (Ideal.span {π} ^ n : Ideal 𝒪))
      (IsLocalRing.maximalIdeal 𝒪K : Set 𝒪K) := by
  intro y c
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hc : algebraMap 𝒪K 𝒪 (c : 𝒪K) ∈ (Ideal.span {π} ^ n : Ideal 𝒪) :=
    hn (Ideal.mem_map_of_mem _ c.2)
  show (c : 𝒪K) • (Ideal.Quotient.mk _ x) = (0 : 𝒪 ⧸ (Ideal.span {π} ^ n : Ideal 𝒪))
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap 𝒪K
        (Ideal.span {π} ^ n : Ideal 𝒪) (c : 𝒪K), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ hc

/-- The `κ`-vector-space structure on `M n = 𝒪 ⧸ I^n` (for `n ≤ e`), via
`mono_quot_isTorsion`.  Brought into scope with
`letI := mono_quot_kappaModule hπ n hn`. -/
@[reducible] noncomputable def mono_quot_kappaModule
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪)) :
    Module (IsLocalRing.ResidueField 𝒪K)
      (𝒪 ⧸ (Ideal.span {π} ^ n : Ideal 𝒪)) :=
  (mono_quot_isTorsion hπ n hn).module

/-- The `κ`-action on `M n = 𝒪 ⧸ I^n` reduces to the `𝒪K`-action:
`(residue 𝒪K c) • z = c • z` (`Module.IsTorsionBySet.mk_smul`).  This is the
single compatibility fact used to upgrade `𝒪`-linear (hence `𝒪K`-linear) maps
between these quotients to `κ`-linear ones. -/
theorem mono_quot_kappa_smul
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪)) (c : 𝒪K)
    (z : 𝒪 ⧸ (Ideal.span {π} ^ n : Ideal 𝒪)) :
    letI := mono_quot_kappaModule hπ n hn
    (IsLocalRing.residue 𝒪K c) • z = c • z :=
  Module.IsTorsionBySet.mk_smul (mono_quot_isTorsion hπ n hn) c z

/-- The `κ`-linear inclusion `gr_n ↪ M (n+1)` (the submodule `subtype`,
upgraded to `κ`-linearity by the residue-reduction trick: every `κ`-scalar is
`residue 𝒪K c`, acting as the `𝒪K`-scalar `c` on both `gr_n` (M2 torsion) and
`M (n+1)` (`mono_quot_kappaModule` torsion), where the `subtype` is
`𝒪`- hence `𝒪K`-linear). -/
noncomputable def mono_grnSubtypeKappa
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) :
    letI := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ n
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    (mono_gradedPiece π n) →ₗ[IsLocalRing.ResidueField 𝒪K]
      (𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) :=
  letI iGr := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ n
  letI iV := mono_quot_kappaModule hπ (n + 1) hn1
  { toFun := fun y => (y : 𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪))
    map_add' := by intro a b; rfl
    map_smul' := by
      intro r y
      obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective (R := 𝒪K) r
      simp only [RingHom.id_apply]
      have hGr : (IsLocalRing.residue 𝒪K c) • y = c • y :=
        Module.IsTorsionBySet.mk_smul (mono_gradedPiece_isTorsion hπ n) c y
      have hV : (IsLocalRing.residue 𝒪K c)
          • (y : 𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) = c • (y : _) :=
        mono_quot_kappa_smul hπ (n + 1) hn1 c
          (y : 𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪))
      rw [hGr, hV]
      exact (Submodule.coe_smul_of_tower (c : 𝒪K) y) }

/-- The `κ`-linear "bottom-step" map `λ →ₗ[κ] M (n+1)`,
`residue 𝒪 x ↦ mk (π^n · x)`, i.e. M2's graded isomorphism
`λ ≃ₗ[κ] gr_n` composed with the `κ`-linear inclusion `gr_n ↪ M (n+1)`.
Its range is the bottom filtration step `(π̄)^n · M (n+1)`. -/
noncomputable def mono_botMap
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) :
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    IsLocalRing.ResidueField 𝒪 →ₗ[IsLocalRing.ResidueField 𝒪K]
      (𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) :=
  letI iGr := mono_gradedPiece_kappaModule (𝒪K := 𝒪K) hπ n
  letI iV := mono_quot_kappaModule hπ (n + 1) hn1
  (mono_grnSubtypeKappa (𝒪K := 𝒪K) hπ n hn1).comp
    (mono_gradedPiece_equiv (𝒪K := 𝒪K) hπ n).toLinearMap

/-- Value of `mono_botMap` on `residue 𝒪 x`: the class of `π^n · x`. -/
theorem mono_botMap_apply
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) (x : 𝒪) :
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    mono_botMap (𝒪K := 𝒪K) hπ n hn1
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪) x)
      = Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1) : Ideal 𝒪) (π ^ n * x) := by
  letI := mono_quot_kappaModule hπ (n + 1) hn1
  show ((mono_gradedPiece_equiv (𝒪K := 𝒪K) hπ n)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪) x) :
      𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) = _
  rw [mono_gradedPiece_equiv_apply (𝒪K := 𝒪K) hπ n x]

/-- `mono_botMap` is injective (it is M2's `κ`-iso `λ ≃ₗ[κ] gr_n` followed by
the injective inclusion `gr_n ↪ M (n+1)`). -/
theorem mono_botMap_injective
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) :
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    Function.Injective (mono_botMap (𝒪K := 𝒪K) hπ n hn1) := by
  letI := mono_quot_kappaModule hπ (n + 1) hn1
  intro a b hab
  apply (mono_gradedPiece_equiv (𝒪K := 𝒪K) hπ n).injective
  apply Subtype.ext
  exact hab

/-- The range of `mono_botMap` (a `κ`-submodule of `M (n+1)`) has the same
carrier as the `𝒪`-submodule `gr_n` (= image of `I^n` in `M (n+1)`). -/
theorem mono_botMap_range_coe
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) :
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    (LinearMap.range (mono_botMap (𝒪K := 𝒪K) hπ n hn1) :
        Set (𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)))
      = (mono_gradedPiece π n : Set (𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪))) := by
  letI := mono_quot_kappaModule hπ (n + 1) hn1
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := 𝒪) a
    rw [show IsLocalRing.residue 𝒪 x
        = Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪) x from rfl,
      mono_botMap_apply (𝒪K := 𝒪K) hπ n hn1 x]
    exact ⟨x, by rw [mono_gr_lmap_apply, mul_comm]⟩
  · rintro ⟨x, rfl⟩
    refine ⟨IsLocalRing.residue 𝒪 x, ?_⟩
    rw [show IsLocalRing.residue 𝒪 x
        = Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪) x from rfl,
      mono_botMap_apply (𝒪K := 𝒪K) hπ n hn1 x, mono_gr_lmap_apply, mul_comm]

/-- The `κ`-linear filtration projection `M (n+1) →ₗ[κ] M n`
(`mk_{I^{n+1}} a ↦ mk_{I^n} a`), the `κ`-linear upgrade of `Submodule.factor`
for `I^{n+1} ≤ I^n`.  `κ`-linear by the residue-reduction trick. -/
noncomputable def mono_filtProj
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪))
    (hn : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪)) :
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    letI := mono_quot_kappaModule hπ n hn
    (𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) →ₗ[IsLocalRing.ResidueField 𝒪K]
      (𝒪 ⧸ (Ideal.span {π} ^ n : Ideal 𝒪)) :=
  letI i1 := mono_quot_kappaModule hπ (n + 1) hn1
  letI i0 := mono_quot_kappaModule hπ n hn
  have hLE : (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪) := by
    apply Ideal.pow_le_pow_right; omega
  { toFun := Submodule.factor hLE
    map_add' := (Submodule.factor hLE).map_add
    map_smul' := by
      intro r y
      obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective (R := 𝒪K) r
      simp only [RingHom.id_apply]
      rw [mono_quot_kappa_smul hπ (n + 1) hn1 c y,
        mono_quot_kappa_smul hπ n hn c (Submodule.factor hLE y)]
      exact (Submodule.factor hLE).map_smul_of_tower c y }

/-- `mono_filtProj` is surjective. -/
theorem mono_filtProj_surjective
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪))
    (hn : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪)) :
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    letI := mono_quot_kappaModule hπ n hn
    Function.Surjective (mono_filtProj (𝒪K := 𝒪K) hπ n hn1 hn) := by
  letI := mono_quot_kappaModule hπ (n + 1) hn1
  letI := mono_quot_kappaModule hπ n hn
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

/-- The kernel of `mono_filtProj` is exactly the range of `mono_botMap`
(both equal `gr_n` = image of `I^n` in `M (n+1)`). -/
theorem mono_filtProj_ker
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪))
    (hn : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪)) :
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    letI := mono_quot_kappaModule hπ n hn
    LinearMap.ker (mono_filtProj (𝒪K := 𝒪K) hπ n hn1 hn)
      = LinearMap.range (mono_botMap (𝒪K := 𝒪K) hπ n hn1) := by
  letI := mono_quot_kappaModule hπ (n + 1) hn1
  letI := mono_quot_kappaModule hπ n hn
  apply SetLike.ext'
  rw [mono_botMap_range_coe (𝒪K := 𝒪K) hπ n hn1]
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  have hspn : (Ideal.span {π} ^ n : Ideal 𝒪) = Ideal.span {π ^ n} :=
    Ideal.span_singleton_pow π n
  constructor
  · intro hz
    have hfac : (mono_filtProj (𝒪K := 𝒪K) hπ n hn1 hn)
        (Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1) : Ideal 𝒪) x)
        = Ideal.Quotient.mk (Ideal.span {π} ^ n : Ideal 𝒪) x := rfl
    rw [hfac] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem, hspn, Ideal.mem_span_singleton] at hz
    obtain ⟨d, rfl⟩ := hz
    exact ⟨d, by rw [mono_gr_lmap_apply]⟩
  · rintro ⟨w, hw⟩
    rw [mono_gr_lmap_apply] at hw
    have hxmem : x - π ^ n * w ∈ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪) := by
      rw [← Ideal.Quotient.eq]; exact hw.symm
    have hfac : (mono_filtProj (𝒪K := 𝒪K) hπ n hn1 hn)
        (Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1) : Ideal 𝒪) x)
        = Ideal.Quotient.mk (Ideal.span {π} ^ n : Ideal 𝒪) x := rfl
    rw [hfac, Ideal.Quotient.eq_zero_iff_mem]
    have hw1 : x - π ^ n * w ∈ (Ideal.span {π} ^ n : Ideal 𝒪) := by
      have hLE : (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)
          ≤ (Ideal.span {π} ^ n : Ideal 𝒪) := by
        apply Ideal.pow_le_pow_right; omega
      exact hLE hxmem
    have hpw : π ^ n * w ∈ (Ideal.span {π} ^ n : Ideal 𝒪) := by
      rw [hspn, Ideal.mem_span_singleton]; exact ⟨w, rfl⟩
    have : x = (x - π ^ n * w) + π ^ n * w := by ring
    rw [this]
    exact Ideal.add_mem _ hw1 hpw

/-- Value of `mono_filtProj` on a monomial class: `mk_{I^{n+1}}(a) ↦ mk_{I^n}(a)`. -/
theorem mono_filtProj_mk
    {π : 𝒪} (hπ : Irreducible π) (n : ℕ)
    (hn1 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪))
    (hn : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪)) (a : 𝒪) :
    letI := mono_quot_kappaModule hπ (n + 1) hn1
    letI := mono_quot_kappaModule hπ n hn
    (mono_filtProj (𝒪K := 𝒪K) hπ n hn1 hn)
        (Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1) : Ideal 𝒪) a)
      = Ideal.Quotient.mk (Ideal.span {π} ^ n : Ideal 𝒪) a := rfl

set_option maxHeartbeats 2000000 in
/-- **M4 induction.** For every `n` with `𝔪K·𝒪 ≤ I^n`, the explicit monomial
family `(j,k) ↦ mk_{I^n}(ξ^j · π^k)` is a `κ`-basis of `M n = 𝒪 ⧸ I^n`,
indexed by `Fin f × Fin n`.  Induction on `n` via the `κ`-linear short exact
sequence `0 → λ →[botMap] M (n+1) →[filtProj] M n → 0`. -/
theorem mono_basis_aux
    {π : 𝒪} (hπ : Irreducible π)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤)
    (F : ℕ)
    (hF : F = Module.finrank (IsLocalRing.ResidueField 𝒪K)
      (IsLocalRing.ResidueField 𝒪))
    (n : ℕ)
    (hn : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
      ≤ (Ideal.span {π} ^ n : Ideal 𝒪)) :
    letI := mono_quot_kappaModule hπ n hn
    ∃ B : Module.Basis
        (Fin F × Fin n)
        (IsLocalRing.ResidueField 𝒪K)
        (𝒪 ⧸ (Ideal.span {π} ^ n : Ideal 𝒪)),
      ∀ jk, B jk =
        Ideal.Quotient.mk (Ideal.span {π} ^ n : Ideal 𝒪)
          (ξ ^ (jk.1 : ℕ) * π ^ (jk.2 : ℕ)) := by
  induction n with
  | zero =>
    letI := mono_quot_kappaModule hπ 0 hn
    -- M 0 = 𝒪 ⧸ I^0 = 𝒪 ⧸ ⊤ is trivial; index `Fin f × Fin 0` is empty.
    have hsub : Subsingleton (𝒪 ⧸ (Ideal.span {π} ^ 0 : Ideal 𝒪)) := by
      rw [pow_zero]
      exact (Ideal.Quotient.subsingleton_iff).mpr (by simp)
    have hempty : IsEmpty (Fin F × Fin 0) := by
      simp only [isEmpty_prod]
      right; exact Fin.isEmpty
    refine ⟨Module.Basis.empty _, ?_⟩
    intro jk
    exact (hempty.false jk).elim
  | succ n ih =>
    letI iV1 := mono_quot_kappaModule hπ (n + 1) hn
    have hn0 : Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
        ≤ (Ideal.span {π} ^ n : Ideal 𝒪) := by
      refine le_trans hn ?_
      apply Ideal.pow_le_pow_right; omega
    letI iV0 := mono_quot_kappaModule hπ n hn0
    obtain ⟨Bn, hBn⟩ := ih hn0
    have hBnLI : LinearIndependent (IsLocalRing.ResidueField 𝒪K) ⇑Bn :=
      Bn.linearIndependent
    have hBnLI' := (Fintype.linearIndependent_iff).1 hBnLI
    -- `Fin F`-indexed `κ`-basis of `λ` (reindexed `mono_lambda_basis`)
    set lamB : Module.Basis (Fin F) (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.ResidueField 𝒪) :=
      (mono_lambda_basis (ξ := ξ) hξ_prim).reindex (finCongr hF.symm) with hlamB
    have hlamBval : ∀ j : Fin F,
        lamB j = (IsLocalRing.residue 𝒪 ξ) ^ (j : ℕ) := by
      intro j
      rw [hlamB, Module.Basis.reindex_apply, mono_lambda_basis_apply,
        finCongr_symm, finCongr_apply, Fin.val_cast]
    have hLamLI := (Fintype.linearIndependent_iff).1 lamB.linearIndependent
    -- the explicit monomial family on `M (n+1)`, indexed by `Fin F × Fin (n+1)`
    set v : (Fin F × Fin (n + 1)) →
        (𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) :=
      fun jk => Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)
        (ξ ^ (jk.1 : ℕ) * π ^ (jk.2 : ℕ)) with hv
    -- `filtProj (v (j, castSucc k')) = Bn (j, k')`
    have hvProjCast : ∀ (j : Fin F) (k' : Fin n),
        (mono_filtProj (𝒪K := 𝒪K) hπ n hn hn0) (v (j, k'.castSucc))
          = Bn (j, k') := by
      intro j k'
      rw [hv]
      simp only [Fin.val_castSucc]
      rw [mono_filtProj_mk (𝒪K := 𝒪K) hπ n hn hn0]
      exact (hBn (j, k')).symm
    -- `filtProj (v (j, last)) = 0` (since `π^n ∈ I^n`)
    have hvProjLast : ∀ (j : Fin F),
        (mono_filtProj (𝒪K := 𝒪K) hπ n hn hn0) (v (j, Fin.last n)) = 0 := by
      intro j
      rw [hv]
      simp only [Fin.val_last]
      rw [mono_filtProj_mk (𝒪K := 𝒪K) hπ n hn hn0,
        Ideal.Quotient.eq_zero_iff_mem,
        show (Ideal.span {π} ^ n : Ideal 𝒪) = Ideal.span {π ^ n} from
          Ideal.span_singleton_pow π n, Ideal.mem_span_singleton]
      exact ⟨ξ ^ (j : ℕ), by ring⟩
    -- `v (j, last) = botMap (lambda_basis j)`
    have hvLastBot : ∀ (j : Fin F),
        v (j, Fin.last n) = (mono_botMap (𝒪K := 𝒪K) hπ n hn) (lamB j) := by
      intro j
      rw [hv]
      simp only [Fin.val_last]
      rw [hlamBval j,
        show (IsLocalRing.residue 𝒪 ξ) ^ (j : ℕ)
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪) (ξ ^ (j : ℕ)) by
            rw [map_pow]; rfl,
        mono_botMap_apply (𝒪K := 𝒪K) hπ n hn (ξ ^ (j : ℕ)), mul_comm]
    -- LINEAR INDEPENDENCE of `v`
    have hLI : LinearIndependent (IsLocalRing.ResidueField 𝒪K) v := by
      rw [Fintype.linearIndependent_iff]
      intro g hg j0k0
      -- split the double sum over `Fin F × Fin (n+1)` into `castSucc` + `last`
      rw [Fintype.sum_prod_type] at hg
      have hsplit : ∀ j : Fin F,
          ∑ k : Fin (n + 1), g (j, k) • v (j, k)
            = (∑ k' : Fin n, g (j, k'.castSucc) • v (j, k'.castSucc))
              + g (j, Fin.last n) • v (j, Fin.last n) := by
        intro j; rw [Fin.sum_univ_castSucc]
      simp_rw [hsplit, Finset.sum_add_distrib] at hg
      -- apply `mono_filtProj`; the `last` block dies
      have hgproj : (∑ j : Fin F, ∑ k' : Fin n,
          g (j, k'.castSucc) • Bn (j, k')) = 0 := by
        have := congrArg (mono_filtProj (𝒪K := 𝒪K) hπ n hn hn0) hg
        rw [map_add, map_zero] at this
        rw [map_sum] at this
        simp_rw [map_sum, map_smul] at this
        have hL : (∑ j : Fin F, ∑ k' : Fin n,
            g (j, k'.castSucc) •
              (mono_filtProj (𝒪K := 𝒪K) hπ n hn hn0) (v (j, k'.castSucc)))
            = ∑ j : Fin F, ∑ k' : Fin n,
              g (j, k'.castSucc) • Bn (j, k') := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          refine Finset.sum_congr rfl (fun k' _ => ?_)
          rw [hvProjCast j k']
        have hR : (∑ j : Fin F, g (j, Fin.last n) •
            (mono_filtProj (𝒪K := 𝒪K) hπ n hn hn0) (v (j, Fin.last n)))
            = 0 := by
          refine Finset.sum_eq_zero (fun j _ => ?_)
          rw [hvProjLast j, smul_zero]
        rw [hL, hR, add_zero] at this
        exact this
      -- Bn is a basis: castSucc coefficients vanish
      have hgCast : ∀ (j : Fin F) (k' : Fin n), g (j, k'.castSucc) = 0 := by
        have := hBnLI' (fun jk => g (jk.1, jk.2.castSucc))
        rw [Fintype.sum_prod_type] at this
        intro j k'
        exact this hgproj (j, k')
      -- the original relation collapses to the `last` block
      have hlast : (∑ j : Fin F, g (j, Fin.last n) • v (j, Fin.last n)) = 0 := by
        have hzero : (∑ j : Fin F, ∑ k' : Fin n,
            g (j, k'.castSucc) • v (j, k'.castSucc)) = 0 := by
          refine Finset.sum_eq_zero (fun j _ => ?_)
          refine Finset.sum_eq_zero (fun k' _ => ?_)
          rw [hgCast j k', zero_smul]
        rw [hzero, zero_add] at hg
        exact hg
      -- push through the injective `botMap`
      have hbot : (mono_botMap (𝒪K := 𝒪K) hπ n hn)
          (∑ j : Fin F, g (j, Fin.last n) • lamB j) = 0 := by
        rw [map_sum]
        simp_rw [map_smul]
        rw [← hlast]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hvLastBot j]
      have hlamComb : (∑ j : Fin F, g (j, Fin.last n) • lamB j) = 0 :=
        (mono_botMap_injective (𝒪K := 𝒪K) hπ n hn)
          (by rw [hbot, map_zero])
      have hgLast : ∀ j : Fin F, g (j, Fin.last n) = 0 :=
        hLamLI _ hlamComb
      -- conclude `g = 0` everywhere
      obtain ⟨j0, k0⟩ := j0k0
      refine Fin.lastCases ?_ ?_ k0
      · exact hgLast j0
      · intro k'; exact hgCast j0 k'
    -- SPANNING of `v`
    have hspan : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField 𝒪K)
        (Set.range v) := by
      intro z _
      -- `filtProj z` lies in `span Bn = ⊤`; write it via the basis
      have hz1 : (mono_filtProj (𝒪K := 𝒪K) hπ n hn hn0) z
          ∈ Submodule.span (IsLocalRing.ResidueField 𝒪K) (Set.range ⇑Bn) := by
        rw [Bn.span_eq]; exact Submodule.mem_top
      rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz1
      obtain ⟨c, hc⟩ := hz1
      -- lift: `y := Σ c (j,k') • v (j, castSucc k')`
      set y : (𝒪 ⧸ (Ideal.span {π} ^ (n + 1) : Ideal 𝒪)) :=
        c.sum (fun jk a => a • v (jk.1, jk.2.castSucc)) with hy
      have hyspan : y ∈ Submodule.span (IsLocalRing.ResidueField 𝒪K)
          (Set.range v) := by
        rw [hy, Finsupp.sum]
        refine Submodule.sum_mem _ (fun jk _ => ?_)
        exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨(jk.1, jk.2.castSucc), rfl⟩)
      -- `filtProj y = filtProj z`
      have hyproj : (mono_filtProj (𝒪K := 𝒪K) hπ n hn hn0) y
          = (mono_filtProj (𝒪K := 𝒪K) hπ n hn hn0) z := by
        rw [hy, Finsupp.sum, map_sum]
        rw [← hc, Finsupp.sum]
        refine Finset.sum_congr rfl (fun jk _ => ?_)
        rw [map_smul, hvProjCast jk.1 jk.2]
      -- `z - y ∈ ker filtProj = range botMap = span (v (·, last))`
      have hker : z - y ∈ LinearMap.range
          (mono_botMap (𝒪K := 𝒪K) hπ n hn) := by
        rw [← mono_filtProj_ker (𝒪K := 𝒪K) hπ n hn hn0]
        rw [LinearMap.mem_ker, map_sub, hyproj, sub_self]
      obtain ⟨w, hw⟩ := hker
      -- express `w` over the λ-basis, push to `v (·, last)`
      have hwspan : z - y ∈ Submodule.span (IsLocalRing.ResidueField 𝒪K)
          (Set.range v) := by
        have hwrepr : w = ∑ j : Fin F, lamB.repr w j • lamB j :=
          (lamB.sum_repr w).symm
        rw [← hw, hwrepr, map_sum]
        refine Submodule.sum_mem _ (fun j _ => ?_)
        rw [map_smul, ← hvLastBot j]
        exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨(j, Fin.last n), rfl⟩)
      have hzeq : z = y + (z - y) := by ring
      rw [hzeq]
      exact Submodule.add_mem _ hyspan hwspan
    -- assemble the basis with the explicit monomial values
    refine ⟨Module.Basis.mk hLI hspan, ?_⟩
    intro jk
    have := Module.Basis.mk_apply hLI hspan jk
    rw [this, hv]

/-- **M4 finrank transport.** Over the canonical `κ = 𝒪K ⧸ 𝔪K`-structure on
`Q = 𝒪 ⧸ 𝔪K·𝒪`, the monomial family `(j,k) ↦ mk(ξ^j π^k)` is `κ`-linearly
independent and spans, hence is a `κ`-basis.  Proven by pulling the M4
induction basis of `𝒪 ⧸ I^e` (over the `IsTorsionBySet` `κ`-structure) across
the `𝒪`-linear identity-on-classes equivalence `𝒪 ⧸ I^e ≃ₗ[𝒪] Q`
(`Submodule.quotEquivOfEq`, valid since `I^e = 𝔪K·𝒪` by M1), converting every
`κ`-scalar to the underlying `𝒪K`-scalar (`residue c • _ = c • _`, identical
for both `κ`-structures and matching across the `𝒪`-linear bijection). -/
theorem mono_basis_Q
    {π : 𝒪} (hπ : Irreducible π)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤) :
    ∃ B : Module.Basis
        (Fin (Module.finrank (IsLocalRing.ResidueField 𝒪K)
          (IsLocalRing.ResidueField 𝒪)) ×
          Fin (mono_ramificationIdx 𝒪K 𝒪 hπ))
        (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K)
        (𝒪 ⧸ (Ideal.map (algebraMap 𝒪K 𝒪)
          (IsLocalRing.maximalIdeal 𝒪K))),
      ∀ jk, B jk =
        Ideal.Quotient.mk
          (Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K))
          (ξ ^ (jk.1 : ℕ) * π ^ (jk.2 : ℕ)) := by
  classical
  set e := mono_ramificationIdx 𝒪K 𝒪 hπ with he
  set F := Module.finrank (IsLocalRing.ResidueField 𝒪K)
    (IsLocalRing.ResidueField 𝒪) with hF
  set 𝔪Q := Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
    with h𝔪Q
  -- `I^e = 𝔪K·𝒪`  (M1)
  have hee : (Ideal.span {π} ^ e : Ideal 𝒪) = 𝔪Q := by
    rw [h𝔪Q, he, mono_mapMK_eq_pow hπ, mono_maximalIdeal_eq_span hπ]
  have hn : 𝔪Q ≤ (Ideal.span {π} ^ e : Ideal 𝒪) := le_of_eq hee.symm
  -- the M4 induction basis of `𝒪 ⧸ I^e` (torsion `κ`-structure),
  -- with the `κ`-scalar pinned to the literal quotient `𝒪K ⧸ 𝔪K`
  letI iE : Module (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K)
      (𝒪 ⧸ (Ideal.span {π} ^ e : Ideal 𝒪)) :=
    mono_quot_kappaModule hπ e hn
  obtain ⟨B0, hB0⟩ :
      ∃ B : Module.Basis (Fin F × Fin e)
          (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K)
          (𝒪 ⧸ (Ideal.span {π} ^ e : Ideal 𝒪)),
        ∀ jk, B jk = Ideal.Quotient.mk
          (Ideal.span {π} ^ e : Ideal 𝒪)
          (ξ ^ (jk.1 : ℕ) * π ^ (jk.2 : ℕ)) :=
    mono_basis_aux (𝒪K := 𝒪K) (ξ := ξ) hπ hξ_prim F hF e hn
  -- the `𝒪`-linear identity-on-classes bijection `𝒪 ⧸ I^e ≃ₗ[𝒪] Q`
  let e𝒪 : (𝒪 ⧸ (Ideal.span {π} ^ e : Ideal 𝒪)) ≃ₗ[𝒪] (𝒪 ⧸ 𝔪Q) :=
    Submodule.quotEquivOfEq _ _ hee
  have he𝒪mk : ∀ a : 𝒪, e𝒪 (Ideal.Quotient.mk
      (Ideal.span {π} ^ e : Ideal 𝒪) a) = Ideal.Quotient.mk 𝔪Q a :=
    fun a => rfl
  -- compatibility of both `κ`-actions with the `𝒪K`-action
  have hsmulE : ∀ (c : 𝒪K) (x : 𝒪 ⧸ (Ideal.span {π} ^ e : Ideal 𝒪)),
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪K) c) • x = c • x :=
    fun c x => mono_quot_kappa_smul hπ e hn c x
  have hsmulQ : ∀ (c : 𝒪K) (x : 𝒪 ⧸ 𝔪Q),
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪K) c) • x = c • x := by
    intro c x
    have h := IsScalarTower.algebraMap_smul
      (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K) c x
    rw [← h]
    congr 1
  -- the target monomial family on `Q`
  set vQ : (Fin F × Fin e) → (𝒪 ⧸ 𝔪Q) :=
    fun jk => Ideal.Quotient.mk 𝔪Q
      (ξ ^ (jk.1 : ℕ) * π ^ (jk.2 : ℕ)) with hvQ
  have hvQe : ∀ jk, vQ jk = e𝒪 (B0 jk) := by
    intro jk; rw [hvQ, hB0 jk, he𝒪mk]
  -- bridge: an `𝒪K`-combination matches across `e𝒪`
  have hbridge : ∀ (a : Fin F × Fin e → 𝒪K),
      (∑ jk, (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪K) (a jk)) • vQ jk)
        = e𝒪 (∑ jk, (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪K)
            (a jk)) • B0 jk) := by
    intro a
    rw [map_sum]
    refine Finset.sum_congr rfl (fun jk _ => ?_)
    rw [hsmulQ (a jk) (vQ jk), hsmulE (a jk) (B0 jk), hvQe jk]
    exact (e𝒪.map_smul_of_tower (a jk) (B0 jk)).symm
  -- LINEAR INDEPENDENCE of `vQ` over the canonical `κ`-structure on `Q`
  have hLIQ : LinearIndependent (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K) vQ := by
    rw [Fintype.linearIndependent_iff]
    intro g hg jk0
    choose c hc using fun jk =>
      Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal 𝒪K) (g jk)
    have hgc : ∀ jk, g jk
        = Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪K) (c jk) :=
      fun jk => (hc jk).symm
    have hpull : (∑ jk, (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal 𝒪K) (c jk)) • B0 jk) = 0 := by
      apply e𝒪.injective
      rw [map_zero, ← hbridge c]
      rw [← hg]
      refine Finset.sum_congr rfl (fun jk _ => ?_)
      rw [hgc jk]
    have hB0LI := (Fintype.linearIndependent_iff).1 B0.linearIndependent
    have hczero := hB0LI _ hpull
    rw [hgc jk0]
    exact hczero jk0
  -- SPANNING of `vQ`
  have hspanQ : ⊤ ≤ Submodule.span (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K)
      (Set.range vQ) := by
    intro z _
    have hz0 : e𝒪.symm z ∈ Submodule.span
        (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K) (Set.range ⇑B0) := by
      rw [B0.span_eq]; exact Submodule.mem_top
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hz0
    obtain ⟨d, hd⟩ := hz0
    -- write each `κ`-coefficient of `d` as a residue
    choose cd hcd using fun jk =>
      Ideal.Quotient.mk_surjective
        (I := IsLocalRing.maximalIdeal 𝒪K) (d jk)
    have hzcomb : z = ∑ jk, (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal 𝒪K) (cd jk)) • vQ jk := by
      have hsum : (∑ jk, (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal 𝒪K) (cd jk)) • B0 jk) = e𝒪.symm z := by
        rw [← hd, Finsupp.sum_fintype _ _ (fun _ => by rw [zero_smul])]
        refine Finset.sum_congr rfl (fun jk _ => ?_)
        rw [hcd jk]
      have := hbridge cd
      rw [hsum] at this
      rw [this, LinearEquiv.apply_symm_apply]
    rw [hzcomb]
    refine Submodule.sum_mem _ (fun jk _ => ?_)
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨jk, rfl⟩)
  exact ⟨Module.Basis.mk hLIQ hspanQ,
    fun jk => by rw [Module.Basis.mk_apply hLIQ hspanQ jk, hvQ]⟩

end M4

/-! ## The generic target theorem (M2–M5 will replace the `sorry` body)

This is the *only* `sorry` permitted in this file after M1.  Its typeclass
setup is **identical** to the keystone `thm_10_4_aux_iterate_h_lift_coeff_mem`
(so M5 can wire it in directly):

  `[CommRing 𝒪K] [IsDomain 𝒪K] [IsLocalRing 𝒪K] [IsDiscreteValuationRing 𝒪K]`
  `[CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪] [IsDiscreteValuationRing 𝒪]`
  `[Algebra 𝒪K 𝒪] [IsLocalHom (algebraMap 𝒪K 𝒪)] [Module.Finite 𝒪K 𝒪]`
  `[FaithfulSMul 𝒪K 𝒪]`, separability of the residue extension, plus the two
  genuine data inputs `hξ_prim` (ξ̄ primitive) and `hπ` (π irreducible).

Conclusion: the family `fun (jk : Fin f × Fin e) => mkQ (ξ^jk.1 * π^jk.2)`
is a `κ`-basis of `Q`, exhibited as a `Module.Basis` whose values are exactly
those monomial classes. -/

set_option linter.unusedVariables false in
/-- **Neukirch II.10.4 structure theorem (generic target).**

With `κ := ResidueField 𝒪K`, `Q := 𝒪 ⧸ 𝔪K·𝒪`, `f := [ResidueField 𝒪 :
ResidueField 𝒪K]`, `e := mono_ramificationIdx`, `ξ` a lift of a primitive
element `ξ̄ := residue 𝒪 ξ` of `λ/κ`, and `π` a uniformizer of `𝒪`: the family
`{ξ^j · π^k mod 𝔪K·𝒪 : j < f, k < e}` is a `κ`-basis of `Q`.

Body is `sorry` — filled by milestones M2–M5.  This is the single permitted
`sorry`; every M1 foundation lemma above is proved sorry-free. -/
theorem thm_10_4_monogenicity_basis
    {𝒪K : Type*} [CommRing 𝒪K] [IsDomain 𝒪K] [IsLocalRing 𝒪K]
    [IsDiscreteValuationRing 𝒪K]
    {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsLocalRing 𝒪]
    [IsDiscreteValuationRing 𝒪]
    [Algebra 𝒪K 𝒪]
    [IsLocalHom (algebraMap 𝒪K 𝒪)]
    [Module.Finite 𝒪K 𝒪]
    [FaithfulSMul 𝒪K 𝒪]
    (_hSep : Algebra.IsSeparable
       (IsLocalRing.ResidueField 𝒪K) (IsLocalRing.ResidueField 𝒪))
    (ξ π : 𝒪)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤)
    (hπ : Irreducible π) :
    ∃ B : Module.Basis
        (Fin (Module.finrank (IsLocalRing.ResidueField 𝒪K)
              (IsLocalRing.ResidueField 𝒪)) ×
          Fin (mono_ramificationIdx 𝒪K 𝒪 hπ))
        (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K)
        (𝒪 ⧸ (Ideal.map (algebraMap 𝒪K 𝒪)
          (IsLocalRing.maximalIdeal 𝒪K))),
      ∀ jk, B jk =
        Ideal.Quotient.mk
          (Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K))
          (ξ ^ (jk.1 : ℕ) * π ^ (jk.2 : ℕ)) := by
  exact mono_basis_Q (𝒪K := 𝒪K) (ξ := ξ) hπ hξ_prim

/-! ## M6 — the two-generator monogenicity corollary `𝒪 = 𝒪K[ξ, π]`

From the structure theorem `thm_10_4_monogenicity_basis` the finitely many
monomials `{ξ^j · π^k : j < f, k < e}` form a `κ`-basis of
`Q := 𝒪 ⧸ 𝔪K·𝒪`.  Since `κ = 𝒪K ⧸ 𝔪K` is a quotient of `𝒪K`
(`algebraMap 𝒪K κ` surjective), `Submodule.restrictScalars_span` shows the same
monomials span `Q` as an `𝒪K`-module.  Pulling back through the `𝒪K`-linear
quotient `𝒪 →ₗ[𝒪K] Q` (whose kernel as an `𝒪K`-submodule is
`𝔪K • (⊤ : Submodule 𝒪K 𝒪) = (Ideal.map (algebraMap 𝒪K 𝒪) 𝔪K).restrictScalars`
by `Ideal.smul_top_eq_map`), the image of the `𝒪K`-span of the monomials is the
whole of `Q ≃ₗ[𝒪K] 𝒪 ⧸ (𝔪K • ⊤)`.  As `𝒪` is module-finite over the local
ring `𝒪K`, **Nakayama** (`IsLocalRing.map_mkQ_eq_top`) lifts this to
`Submodule.span 𝒪K {ξ^j π^k} = ⊤`.  Since each monomial lies in the subalgebra
`𝒪K[ξ, π]`, that span (a fortiori the subalgebra) is everything, i.e.
`Algebra.adjoin 𝒪K {ξ, π} = ⊤`.  This holds for ALL admissible `ξ`
(genuine — no `ξ + π` shortcut). -/

set_option linter.unusedVariables false in
/-- **M6 helper.** The `𝒪K`-span of the finite monomial family
`{ξ^j · π^k : j < f, k < e}` is the whole of `𝒪`.

Proof: the structure theorem makes these monomials a `κ`-basis of
`Q := 𝒪 ⧸ 𝔪K·𝒪`; `Submodule.restrictScalars_span` (with the surjection
`𝒪K ↠ κ = 𝒪K ⧸ 𝔪K`) turns the `κ`-spanning into `𝒪K`-spanning of `Q`; the
`𝒪K`-linear quotient `𝒪 → Q` then has the `𝒪K`-span of the monomials mapping
onto all of `Q`, which (its kernel being `𝔪K • ⊤` by `Ideal.smul_top_eq_map`)
is exactly the Nakayama hypothesis `IsLocalRing.map_mkQ_eq_top`. -/
theorem mono_span_two_gen_eq_top
    (ξ π : 𝒪)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤)
    (hπ : Irreducible π) :
    Submodule.span 𝒪K
        (Set.range (fun jk : Fin (Module.finrank (IsLocalRing.ResidueField 𝒪K)
              (IsLocalRing.ResidueField 𝒪)) ×
            Fin (mono_ramificationIdx 𝒪K 𝒪 hπ) =>
          ξ ^ (jk.1 : ℕ) * π ^ (jk.2 : ℕ))) = ⊤ := by
  classical
  set I : Ideal 𝒪 := Ideal.map (algebraMap 𝒪K 𝒪) (IsLocalRing.maximalIdeal 𝒪K)
    with hI
  set mono : Fin (Module.finrank (IsLocalRing.ResidueField 𝒪K)
        (IsLocalRing.ResidueField 𝒪)) ×
      Fin (mono_ramificationIdx 𝒪K 𝒪 hπ) → 𝒪 :=
    fun jk => ξ ^ (jk.1 : ℕ) * π ^ (jk.2 : ℕ) with hmono
  -- the structure theorem: a `κ = 𝒪K ⧸ 𝔪K`-basis of `Q = 𝒪 ⧸ I`
  obtain ⟨B, hB⟩ := mono_basis_Q (𝒪K := 𝒪K) (ξ := ξ) hπ hξ_prim
  -- the `𝒪K`-linear quotient map `q : 𝒪 →ₗ[𝒪K] Q`
  let q : 𝒪 →ₗ[𝒪K] (𝒪 ⧸ I) := (Ideal.Quotient.mkₐ 𝒪K I).toLinearMap
  have hq : ∀ a : 𝒪, q a = Ideal.Quotient.mk I a := fun _ => rfl
  -- `Set.range B = q '' (Set.range mono)`
  have hrangeB : Set.range ⇑B = q '' (Set.range mono) := by
    rw [← Set.range_comp]
    apply congrArg
    funext jk
    simp only [Function.comp_apply, hq, hmono]
    rw [hB jk]
  -- the monomial classes span `Q` over `κ`
  have hspanκ : Submodule.span (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K)
      (q '' (Set.range mono)) = ⊤ := by
    rw [← hrangeB]; exact B.span_eq
  -- ... hence over `𝒪K` (algebraMap `𝒪K ↠ κ` surjective)
  have hsurj : Function.Surjective
      (algebraMap 𝒪K (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K)) :=
    Ideal.Quotient.mk_surjective
  have hspanOK : Submodule.span 𝒪K (q '' (Set.range mono)) = ⊤ := by
    have h := Submodule.restrictScalars_span 𝒪K
      (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K) hsurj (q '' (Set.range mono))
    rw [hspanκ] at h
    have : (⊤ : Submodule (𝒪K ⧸ IsLocalRing.maximalIdeal 𝒪K) (𝒪 ⧸ I)).restrictScalars 𝒪K
        = (⊤ : Submodule 𝒪K (𝒪 ⧸ I)) := rfl
    rw [this] at h
    exact h.symm
  -- so `q` maps the `𝒪K`-span of the monomials onto all of `Q`
  have hmapTop : Submodule.map q
      (Submodule.span 𝒪K (Set.range mono)) = ⊤ := by
    rw [Submodule.map_span q (Set.range mono)]
    exact hspanOK
  -- bridge: `I.restrictScalars 𝒪K = 𝔪K • (⊤ : Submodule 𝒪K 𝒪)`
  have hbridge : (I.restrictScalars 𝒪K)
      = (IsLocalRing.maximalIdeal 𝒪K) • (⊤ : Submodule 𝒪K 𝒪) := by
    rw [Ideal.smul_top_eq_map, hI]
  -- the `𝒪K`-linear iso `𝒪 ⧸ (I.restrictScalars 𝒪K) ≃ₗ[𝒪K] 𝒪 ⧸ I`
  let eRS : (𝒪 ⧸ (I.restrictScalars 𝒪K)) ≃ₗ[𝒪K] (𝒪 ⧸ I) :=
    Submodule.Quotient.restrictScalarsEquiv 𝒪K I
  -- `eRS.symm ∘ q` is the canonical projection `mkQ (I.restrictScalars 𝒪K)`
  have hcomp : (eRS.symm.toLinearMap.comp q)
      = Submodule.mkQ (I.restrictScalars 𝒪K) := by
    apply LinearMap.ext
    intro a
    show eRS.symm (Ideal.Quotient.mk I a)
      = Submodule.mkQ (I.restrictScalars 𝒪K) a
    rfl
  -- Nakayama input: image of `N` under `mkQ (𝔪K • ⊤)` is `⊤`
  set N : Submodule 𝒪K 𝒪 := Submodule.span 𝒪K (Set.range mono) with hN
  have hNakInput : N.map
      (Submodule.mkQ ((IsLocalRing.maximalIdeal 𝒪K)
        • (⊤ : Submodule 𝒪K 𝒪))) = ⊤ := by
    have hstep : N.map (Submodule.mkQ (I.restrictScalars 𝒪K)) = ⊤ := by
      rw [← hcomp, Submodule.map_comp]
      rw [hmapTop]
      rw [Submodule.map_top, LinearEquiv.range]
    rw [← hbridge]; exact hstep
  -- finish via Mathlib's local-ring Nakayama
  have := (IsLocalRing.map_mkQ_eq_top (R := 𝒪K) (M := 𝒪) (N := N)).mp hNakInput
  rw [hN] at this
  exact this

set_option linter.unusedVariables false in
/-- **M6 — Item 1 (firm milestone).  Two-generator monogenicity:**
`𝒪 = 𝒪K[ξ, π]`.

Same hypotheses as `thm_10_4_monogenicity_basis` (`_hSep`, the genuine
primitivity `hξ_prim`, `hπ : Irreducible π`, full DVR/finiteness context).
The structure theorem exhibits the monomials `{ξ^j π^k}` as a `κ`-basis of
`Q = 𝒪 ⧸ 𝔪K·𝒪`; Nakayama (`mono_span_two_gen_eq_top`) lifts them to an
`𝒪K`-module generating set of all of `𝒪`; since each monomial lies in the
subalgebra `𝒪K[ξ, π]`, that subalgebra is everything.  Genuine for all
admissible `ξ` (no `ξ + π` shortcut). -/
theorem mono_adjoin_two_gen
    [Algebra.IsSeparable
       (IsLocalRing.ResidueField 𝒪K) (IsLocalRing.ResidueField 𝒪)]
    (ξ π : 𝒪)
    (hξ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
       ({IsLocalRing.residue 𝒪 ξ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤)
    (hπ : Irreducible π) :
    Algebra.adjoin 𝒪K ({ξ, π} : Set 𝒪) = ⊤ := by
  classical
  -- it suffices to show the underlying submodule is `⊤`
  rw [← Algebra.toSubmodule_eq_top]
  rw [eq_top_iff]
  -- the `𝒪K`-span of the monomials is `⊤` (Nakayama, via `mono_span...`)
  have hspan := mono_span_two_gen_eq_top (𝒪K := 𝒪K) ξ π hξ_prim hπ
  rw [← hspan]
  -- each monomial `ξ^j · π^k` lies in the subalgebra `𝒪K[ξ, π]`
  rw [Submodule.span_le]
  rintro _ ⟨jk, rfl⟩
  refine Subalgebra.mul_mem _ ?_ ?_
  · exact Subalgebra.pow_mem _
      (Algebra.subset_adjoin (by simp)) _
  · exact Subalgebra.pow_mem _
      (Algebra.subset_adjoin (by simp)) _

/-! ## M7 — the genuine single-generator monogenicity `∃ θ, 𝒪 = 𝒪K[θ]`
(Neukirch II.10.4, single generator)

This is the honest Neukirch II.10.4: from the **separable** residue extension
`λ/κ` we choose a primitive element `ξ̄` (`Field.exists_primitive_element`,
finite by `mono_residueField_finite`) and lift it to `ξ : 𝒪`.  The naive
`θ = ξ + π` for an *arbitrary* lift is the FALSE keystone (char-2
counterexample `ξ + π = 0`).  The genuine construction performs **one Newton
step** (valid in any local ring — no Henselian/completeness hypothesis) so that
the chosen lift satisfies `g(ξ) ∈ 𝔪²` for `g` a monic lift of the (separable)
minimal polynomial of `ξ̄`.  Then for `θ := ξ + π`:

* `g(θ) = g(ξ) + g'(ξ)·π + k·π² = π·(unit)` (because `g(ξ) ∈ 𝔪²`, `g'(ξ)` is a
  unit by separability), so `ϖ := g(θ) = aeval θ g` is a **uniformizer lying in
  `A := 𝒪K[θ]`** (`Polynomial.aeval_mem_adjoin_singleton`);
* `residue 𝒪 θ = ξ̄` is primitive (`π ∈ 𝔪`).

Hence `Algebra.adjoin 𝒪K {θ, ϖ} ≤ A` and, by the proven two-generator asset
`mono_adjoin_two_gen` (applied with the primitive `θ̄ = ξ̄` and the uniformizer
`ϖ`), `Algebra.adjoin 𝒪K {θ, ϖ} = ⊤`, so `A = ⊤`, i.e. `𝒪 = 𝒪K[θ]`.  This is
uniform across all `e, f` (no case split): if `f = 1` the minimal polynomial is
linear and the Newton step collapses `θ` to a uniformizer; if `e = 1`, `π` is
still a uniformizer of `𝒪`.  Genuine — `ξ` is the Newton-corrected primitive
lift, never an unconditioned `ξ + π`.
-/

section M7

set_option linter.unusedSectionVars false

/-- **M7-(bridge).** Residue/`map`/`eval` plumbing: for any `g : 𝒪K[X]` and
`x : 𝒪`, the residue of `eval x (g.map (algebraMap 𝒪K 𝒪))` is the evaluation
at `residue 𝒪 x` of `g` mapped down the residue tower `𝒪K → κ → λ`.  Pure
`Polynomial.map`/`eval_map_apply`/`map_map` bookkeeping using
`IsLocalRing.algebraMap_residue`. -/
theorem mono_residue_eval_lift (g : Polynomial 𝒪K) (x : 𝒪) :
    IsLocalRing.residue 𝒪
        (Polynomial.eval x (g.map (algebraMap 𝒪K 𝒪)))
      = Polynomial.eval (IsLocalRing.residue 𝒪 x)
          ((g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K))).map
            (algebraMap (IsLocalRing.ResidueField 𝒪K)
              (IsLocalRing.ResidueField 𝒪))) := by
  have hcomp :
      (IsLocalRing.residue 𝒪).comp (algebraMap 𝒪K 𝒪)
        = (algebraMap (IsLocalRing.ResidueField 𝒪K)
            (IsLocalRing.ResidueField 𝒪)).comp
            (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)) := by
    apply RingHom.ext
    intro a
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsLocalRing.ResidueField.algebraMap_eq 𝒪K,
      IsLocalRing.ResidueField.algebraMap_residue]
  have hmaps : (g.map (algebraMap 𝒪K 𝒪)).map (IsLocalRing.residue 𝒪)
      = (g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K))).map
          (algebraMap (IsLocalRing.ResidueField 𝒪K)
            (IsLocalRing.ResidueField 𝒪)) := by
    rw [Polynomial.map_map, Polynomial.map_map, hcomp]
  rw [← Polynomial.eval_map_apply (IsLocalRing.residue 𝒪)
      (p := g.map (algebraMap 𝒪K 𝒪)) x, hmaps]

/-- **M7-(Newton).** One Newton step in the local ring `𝒪` (no completeness
needed): given a monic `g : 𝒪K[X]`, a uniformizer `π`, and a lift `x₀` of a
root `ξ̄` of `gbar := g.map (𝒪K→κ)` over `κ` with `gbar'(ξ̄) ≠ 0`, there is an
`x = x₀ + π·t` with `residue 𝒪 x = residue 𝒪 x₀` and
`Polynomial.eval x (g.map (algebraMap 𝒪K 𝒪)) ∈ 𝔪²`. -/
theorem mono_newton_step
    {π : 𝒪} (hπ : Irreducible π) (g : Polynomial 𝒪K) (x₀ : 𝒪)
    (hroot : Polynomial.eval (IsLocalRing.residue 𝒪 x₀)
        ((g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K))).map
          (algebraMap (IsLocalRing.ResidueField 𝒪K)
            (IsLocalRing.ResidueField 𝒪))) = 0)
    (hderiv : Polynomial.eval (IsLocalRing.residue 𝒪 x₀)
        ((Polynomial.derivative
            (g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)))).map
          (algebraMap (IsLocalRing.ResidueField 𝒪K)
            (IsLocalRing.ResidueField 𝒪))) ≠ 0) :
    ∃ x : 𝒪, IsLocalRing.residue 𝒪 x = IsLocalRing.residue 𝒪 x₀ ∧
      Polynomial.eval x (g.map (algebraMap 𝒪K 𝒪))
        ∈ (IsLocalRing.maximalIdeal 𝒪) ^ 2 := by
  classical
  set G : Polynomial 𝒪 := g.map (algebraMap 𝒪K 𝒪) with hG
  -- `g(x₀) ∈ 𝔪`
  have hGx₀_mem : Polynomial.eval x₀ G ∈ IsLocalRing.maximalIdeal 𝒪 := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [hG, mono_residue_eval_lift g x₀, hroot]
  -- `g'(x₀)` is a unit
  have hDeriv_unit : IsUnit (Polynomial.eval x₀ (Polynomial.derivative G)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    rw [hG, Polynomial.derivative_map,
      mono_residue_eval_lift (Polynomial.derivative g) x₀]
    rw [Polynomial.derivative_map] at hderiv
    exact hderiv
  -- write `g(x₀) = π * b`
  have hmem_span : Polynomial.eval x₀ G ∈ Ideal.span ({π} : Set 𝒪) := by
    rw [← mono_maximalIdeal_eq_span hπ]; exact hGx₀_mem
  rw [Ideal.mem_span_singleton] at hmem_span
  obtain ⟨b, hb⟩ := hmem_span
  -- Newton choice: `t := -(unit⁻¹) * b`, so `g'(x₀) * t = -b`
  set D := Polynomial.eval x₀ (Polynomial.derivative G) with hD
  set t : 𝒪 := -(↑(hDeriv_unit.unit⁻¹) : 𝒪) * b with ht
  have hDinv : D * (↑(hDeriv_unit.unit⁻¹) : 𝒪) = 1 :=
    hDeriv_unit.mul_val_inv
  have hDt : D * t = -b := by
    have : D * t = -(D * (↑(hDeriv_unit.unit⁻¹) : 𝒪)) * b := by
      rw [ht]; ring
    rw [this, hDinv, neg_one_mul]
  refine ⟨x₀ + π * t, ?_, ?_⟩
  · -- residue unchanged: `π * t ∈ 𝔪`
    rw [map_add, map_mul]
    have : IsLocalRing.residue 𝒪 π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, mono_maximalIdeal_eq_span hπ]
      exact Ideal.mem_span_singleton_self π
    rw [this, zero_mul, add_zero]
  · -- Taylor: `g(x₀ + π t) = g(x₀) + g'(x₀)·(π t) + k·(π t)²`
    obtain ⟨k, hk⟩ := Polynomial.binomExpansion G x₀ (π * t)
    -- `g(x₀) + D·(π t) + k·(π t)² = π²·(k t²)` (since `g(x₀)=πb`, `Dt=-b`)
    have hcollapse :
        Polynomial.eval x₀ G
          + Polynomial.eval x₀ (Polynomial.derivative G) * (π * t)
          + k * (π * t) ^ 2
        = π ^ 2 * (k * t ^ 2) := by
      have hDeq : Polynomial.eval x₀ (Polynomial.derivative G) = D := rfl
      rw [hb, hDeq]
      have hDtπ : D * (π * t) = π * (D * t) := by ring
      rw [hDtπ, hDt]
      ring
    rw [hk, hcollapse]
    -- `π² * (k t²) ∈ (π²) = 𝔪²`
    rw [mono_maximalIdeal_eq_span hπ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact ⟨k * t ^ 2, rfl⟩

end M7

set_option linter.unusedVariables false in
/-- **Neukirch II.10.4 — single-generator monogenicity.**

Under the standing finite-DVR-extension hypotheses and a **separable** residue
extension `λ/κ`, there exists `θ : 𝒪` with `Algebra.adjoin 𝒪K {θ} = ⊤`, i.e.
`𝒪 = 𝒪K[θ]`.

`θ := ξ + π`, where `π` is a uniformizer (`IsDiscreteValuationRing`) and `ξ`
is the **Newton-corrected** lift (`mono_newton_step`) of a primitive element
`ξ̄` of `λ/κ` (`Field.exists_primitive_element`, finite by
`mono_residueField_finite`).  Then `aeval θ g` (`g` a monic lift of the
separable `minpoly κ ξ̄`) is a uniformizer in `𝒪K[θ]`, and
`mono_adjoin_two_gen` (primitive `θ̄ = ξ̄`, uniformizer `aeval θ g`) collapses
to `𝒪K[θ] = ⊤`.  Genuine: `ξ` is the Newton-corrected primitive lift, not an
unconditioned `ξ + π`. -/
theorem mono_exists_primitive
    [Algebra.IsSeparable
       (IsLocalRing.ResidueField 𝒪K) (IsLocalRing.ResidueField 𝒪)] :
    ∃ θ : 𝒪, Algebra.adjoin 𝒪K ({θ} : Set 𝒪) = ⊤ := by
  classical
  -- a uniformizer of the DVR `𝒪`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  -- a primitive element `ξ̄` of the finite separable extension `λ/κ`
  haveI : Module.Finite (IsLocalRing.ResidueField 𝒪K)
      (IsLocalRing.ResidueField 𝒪) := mono_residueField_finite
  obtain ⟨ξbar, hξbar⟩ :=
    Field.exists_primitive_element (IsLocalRing.ResidueField 𝒪K)
      (IsLocalRing.ResidueField 𝒪)
  -- a lift `x₀ : 𝒪` of `ξ̄`
  obtain ⟨x₀, hx₀⟩ := IsLocalRing.residue_surjective (R := 𝒪) ξbar
  -- the separable minimal polynomial `gbar := minpoly κ ξ̄`
  set gbar : Polynomial (IsLocalRing.ResidueField 𝒪K) :=
    minpoly (IsLocalRing.ResidueField 𝒪K) ξbar with hgbar
  have hgbar_sep : gbar.Separable :=
    (Algebra.IsSeparable.isSeparable
      (IsLocalRing.ResidueField 𝒪K) ξbar)
  have hgbar_monic : gbar.Monic :=
    minpoly.monic
      (Algebra.IsIntegral.isIntegral (R := IsLocalRing.ResidueField 𝒪K)
        ξbar)
  -- lift `gbar` to a monic `g : 𝒪K[X]` along the surjection `𝒪K ↠ κ`
  have hsurj : Function.Surjective
      (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq 𝒪K]
    exact IsLocalRing.residue_surjective
  have hlifts : gbar ∈ Polynomial.lifts
      (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact hsurj (gbar.coeff n)
  obtain ⟨g, hg_map, _hg_deg, _hg_monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hgbar_monic
  -- `gbar` at `ξ̄`: root, derivative ≠ 0  (transported through `κ → λ`)
  have haeval_zero : Polynomial.eval (IsLocalRing.residue 𝒪 x₀)
      ((g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K))).map
        (algebraMap (IsLocalRing.ResidueField 𝒪K)
          (IsLocalRing.ResidueField 𝒪))) = 0 := by
    rw [hg_map, hx₀, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  have haeval_deriv : Polynomial.eval (IsLocalRing.residue 𝒪 x₀)
      ((Polynomial.derivative
          (g.map (algebraMap 𝒪K (IsLocalRing.ResidueField 𝒪K)))).map
        (algebraMap (IsLocalRing.ResidueField 𝒪K)
          (IsLocalRing.ResidueField 𝒪))) ≠ 0 := by
    rw [hg_map, hx₀, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hgbar_sep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  -- Newton step → corrected lift `ξ` with `g(ξ) ∈ 𝔪²`, `residue ξ = ξ̄`
  obtain ⟨ξ, hξ_res, hξ_sq⟩ :=
    mono_newton_step hπ g x₀ haeval_zero haeval_deriv
  -- primitivity carries to `ξ` (same residue as `x₀`, `= ξ̄`)
  have hξ_residue : IsLocalRing.residue 𝒪 ξ = ξbar := by
    rw [hξ_res, hx₀]
  -- `θ := ξ + π`
  set θ : 𝒪 := ξ + π with hθ
  -- `residue 𝒪 θ = ξ̄`  (π ∈ 𝔪)
  have hθ_res : IsLocalRing.residue 𝒪 θ = ξbar := by
    rw [hθ, map_add, hξ_residue]
    have : IsLocalRing.residue 𝒪 π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, mono_maximalIdeal_eq_span hπ]
      exact Ideal.mem_span_singleton_self π
    rw [this, add_zero]
  -- primitivity of `residue θ` (= `ξ̄`)
  have hθ_prim : IntermediateField.adjoin (IsLocalRing.ResidueField 𝒪K)
      ({IsLocalRing.residue 𝒪 θ} : Set (IsLocalRing.ResidueField 𝒪)) = ⊤ := by
    rw [hθ_res]; exact hξbar
  -- the candidate uniformizer `ϖ := aeval θ g = eval θ (g.map (𝒪K→𝒪))`
  set G : Polynomial 𝒪 := g.map (algebraMap 𝒪K 𝒪) with hGdef
  -- `g(ξ) ∈ 𝔪²`, write `g(ξ) = π² * d`
  have hξsq_span : Polynomial.eval ξ G
      ∈ Ideal.span ({π ^ 2} : Set 𝒪) := by
    have := hξ_sq
    rw [mono_maximalIdeal_eq_span hπ, Ideal.span_singleton_pow] at this
    exact this
  rw [Ideal.mem_span_singleton] at hξsq_span
  obtain ⟨d, hd⟩ := hξsq_span
  -- `g'(ξ)` is a unit (residue at `ξ` is the residue at `ξ̄`, ≠ 0)
  have hDerivξ_unit :
      IsUnit (Polynomial.eval ξ (Polynomial.derivative G)) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hGdef,
      Polynomial.derivative_map,
      mono_residue_eval_lift (Polynomial.derivative g) ξ, hξ_residue]
    rw [← Polynomial.derivative_map, hg_map, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact hgbar_sep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  -- Taylor at `ξ` with increment `π`: `g(θ) = g(ξ) + g'(ξ)·π + k·π²`
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion G ξ π
  set D' := Polynomial.eval ξ (Polynomial.derivative G) with hD'
  -- `ϖ := g(θ) = π * u` with `u` a unit
  set u : 𝒪 := D' + π * (d + k) with hu
  have hϖ_eq : Polynomial.eval θ G = π * u := by
    rw [hθ, hk, hd, hu]
    rw [hD']
    ring
  have hu_unit : IsUnit u := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hu, map_add, map_mul]
    have hπ_res : IsLocalRing.residue 𝒪 π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, mono_maximalIdeal_eq_span hπ]
      exact Ideal.mem_span_singleton_self π
    rw [hπ_res, zero_mul, add_zero, hD']
    rw [IsLocalRing.residue_ne_zero_iff_isUnit]
    exact hDerivξ_unit
  -- `ϖ := g(θ)` is irreducible (= π · unit) and lies in `A := 𝒪K[θ]`
  have hϖ_irred : Irreducible (Polynomial.eval θ G) := by
    rw [hϖ_eq, irreducible_mul_isUnit hu_unit]
    exact hπ
  have hϖ_mem : Polynomial.eval θ G ∈ Algebra.adjoin 𝒪K ({θ} : Set 𝒪) := by
    rw [hGdef,
      show Polynomial.eval θ (g.map (algebraMap 𝒪K 𝒪))
          = Polynomial.aeval θ g from by
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]]
    exact Polynomial.aeval_mem_adjoin_singleton 𝒪K θ
  -- both generators `θ, ϖ` lie in `A`; the two-generator asset finishes
  refine ⟨θ, ?_⟩
  rw [eq_top_iff]
  have htwo := mono_adjoin_two_gen (𝒪K := 𝒪K)
    θ (Polynomial.eval θ G) hθ_prim hϖ_irred
  rw [← htwo]
  rw [Algebra.adjoin_le_iff]
  intro y hy
  rcases hy with hy | hy
  · rw [hy]; exact Algebra.self_mem_adjoin_singleton 𝒪K θ
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact hϖ_mem

end Neukirch.Chapter2.Sections8to10
