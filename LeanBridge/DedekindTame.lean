import Mathlib

/-!
# Trace over a filtration and the sharp tame different formula

This file builds the linear-algebra input for the wild-ramification part of Dedekind's
different theorem: the trace of multiplication on `𝒪_L / 𝔪_L ^ e` equals `e` times the
residue-field trace. The key general lemma is additivity of the trace along an
`f`-invariant submodule.
-/

open LinearMap Submodule Module

namespace DedekindTame

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]

/-- **Trace is additive along an invariant submodule.** If `f` maps the subspace `p`
into itself, then `tr f = tr (f|_p) + tr (f on M ⧸ p)`. -/
theorem trace_eq_restrict_add_mapQ (f : Module.End k M) {p : Submodule k M}
    (hp : ∀ x ∈ p, f x ∈ p) :
    trace k M f = trace k p (f.restrict hp) + trace k (M ⧸ p) (p.mapQ p f hp) := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl p
  set Pp : M →ₗ[k] p := p.projectionOnto q hq with hPpdef
  set Pq : M →ₗ[k] q := q.projectionOnto p hq.symm with hPqdef
  have hid : p.subtype ∘ₗ Pp + q.subtype ∘ₗ Pq = LinearMap.id := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.id_coe, id_eq, hPpdef, hPqdef, Submodule.coe_projectionOnto_apply]
    exact projection_add_projection_eq_self hq x
  have hfcomp : f = f ∘ₗ (p.subtype ∘ₗ Pp) + f ∘ₗ (q.subtype ∘ₗ Pq) := by
    rw [← LinearMap.comp_add, hid, LinearMap.comp_id]
  conv_lhs => rw [hfcomp]
  rw [map_add]
  congr 1
  · -- p-block: `tr (f ∘ ι_p ∘ Pp) = tr (f|_p)`
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
    congr 1
    ext x
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_restrict_apply,
      hPpdef, Submodule.projectionOnto_apply_of_mem_left hq (hp _ x.2)]
  · -- q-block: `tr (f ∘ ι_q ∘ Pq) = tr (f on M ⧸ p)` via `q ≃ M ⧸ p`
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm',
      ← LinearMap.trace_conj' (p.mapQ p f hp) (p.quotientEquivOfIsCompl q hq)]
    congr 1

/-!
## The core trace formula `tr(μ_x on S/P^e) = e · Tr_{S/P}(x̄)`

We mirror Mathlib's `Ideal.rank_pow_quot` (which proves `[S/P^e : R/p] = e·[S/P:R/p]`)
but for the trace of multiplication by `x`, using the invariant-submodule additivity
`trace_eq_restrict_add_mapQ` in place of `rank_quotient_add_rank`, and the graded-piece
isomorphism `Ideal.quotientRangePowQuotSuccInclusionEquiv`.
-/

section CoreTrace

open Ideal

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  {p : Ideal R} {P : Ideal S} [p.IsMaximal] [P.IsPrime] [IsDedekindDomain S]
  [NeZero (Ideal.ramificationIdx p P)] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

local notation "e" => Ideal.ramificationIdx p P

example : Algebra (R ⧸ p) (S ⧸ P) := inferInstance

/-- Multiplication by `mk x` as an `R/p`-linear endomorphism of `M i = P^i / P^e`. -/
noncomputable def mulPow (x : S) (i : ℕ) :
    Module.End (R ⧸ p)
      ((Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)).restrictScalars (R ⧸ p)) :=
  LinearMap.restrict (LinearMap.mulLeft (R ⧸ p) (Ideal.Quotient.mk (P ^ e) x))
    (fun (y : S ⧸ P ^ e)
      (hy : y ∈ (Ideal.map (Ideal.Quotient.mk (P ^ e)) (P ^ i)).restrictScalars (R ⧸ p)) =>
      Ideal.mul_mem_left _ _ hy)

/-- `mulPow` commutes with the inclusion `P^(i+1)/P^e ↪ P^i/P^e`. -/
theorem mulPow_comp_inclusion (x : S) (i : ℕ) (w) :
    Ideal.powQuotSuccInclusion p P i (mulPow x (i + 1) w) =
      mulPow x i (Ideal.powQuotSuccInclusion p P i w) := by
  ext
  simp only [mulPow, Ideal.powQuotSuccInclusion, LinearMap.coe_restrict_apply,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mulLeft_apply]

/-- `mulPow` preserves the image `P^(i+1)/P^e ⊆ P^i/P^e`. -/
theorem mulPow_mapsTo_range (x : S) (i : ℕ) :
    ∀ z ∈ LinearMap.range (Ideal.powQuotSuccInclusion p P i),
      mulPow x i z ∈ LinearMap.range (Ideal.powQuotSuccInclusion p P i) := by
  rintro z ⟨w, rfl⟩
  exact ⟨mulPow x (i + 1) w, mulPow_comp_inclusion x i w⟩

/-!
### Status of the core trace formula

The intended core formula is `Algebra.trace (R/p) (S/P^e) (mk x) = e • Algebra.trace (R/p)
(S/P) (mk x)`, to be proved by mirroring `Ideal.rank_pow_quot` (which proves the rank
identity `[S/P^e:R/p] = e·[S/P:R/p]` by decreasing induction) but with the trace in place
of the rank, using `DedekindTame.trace_eq_restrict_add_mapQ` in place of
`Submodule.rank_quotient_add_rank`, and the graded-piece isomorphism
`Ideal.quotientRangePowQuotSuccInclusionEquiv`.

The building blocks `mulPow`, `mulPow_comp_inclusion`, `mulPow_mapsTo_range` above are
verified. However, assembling the per-step trace identity
`trace(mulPow x i) = Tr_{S/P}(x̄) + trace(mulPow x (i+1))` runs into a `whnf` performance
wall (heartbeat timeout even at `maxHeartbeats 1000000`): the `Submodule.restrictScalars
(R/p)` structure on `↥(Ideal.map (mk) (P^i))`, combined with `LinearEquiv.ofInjective`
conjugation, makes the required `defeq`/`simp` checks intractable. Closing it needs a
reformulation avoiding `restrictScalars` (e.g. working with the quotient rings `S/P^n`
and their natural `R/p`-algebra structure), which is a further redesign. -/

end CoreTrace

end DedekindTame
