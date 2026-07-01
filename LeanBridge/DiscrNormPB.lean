import Mathlib

/-!
# Discriminant of an integral power basis as the norm of the derivative

For an integrally-closed domain `A` with fraction field `K`, and `B` its integral
closure in a finite separable extension `L / K` that is monogenic over `A` (a power
basis `pb : PowerBasis A B`), the discriminant of the power basis is associated (as
an element of `A`) to the integral norm of `f'(θ)`, where `θ = pb.gen` and
`f = minpoly A θ`.

This descends `Algebra.discr_powerBasis_eq_norm` (stated over the field `K`) to the
ring `A`, using `Algebra.discr_localizationLocalization`, `Algebra.algebraMap_intNorm`
and injectivity of `algebraMap A K`.
-/

open Polynomial

/-- The discriminant of an integral power basis is associated to `intNorm A B (f'(θ))`,
with `θ = pb.gen`, `f = minpoly A θ`. -/
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
  -- instances for the fraction-ring tower
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization A K L B
  have hθint : IsIntegral A θ := Algebra.IsIntegral.isIntegral θ
  set θL : L := algebraMap B L θ with hθL
  set k : ℕ := Module.finrank K L * (Module.finrank K L - 1) / 2 with hk
  -- the localized basis of `L / K` and its power-basis packaging
  set bLoc : Module.Basis (Fin pb.dim) K L :=
    Module.Basis.localizationLocalization K (nonZeroDivisors A) L pb.basis with hbLoc
  have hbLoc_pow : ∀ i, bLoc i = θL ^ (i : ℕ) := by
    intro i
    rw [hbLoc, Module.Basis.localizationLocalization_apply, pb.basis_eq_pow, map_pow, ← hθ, ← hθL]
  let pbL : PowerBasis K L :=
    { gen := θL, dim := pb.dim, basis := bLoc, basis_eq_pow := hbLoc_pow }
  have hpbLgen : pbL.gen = θL := rfl
  -- discriminant of the localized basis descends from `A`
  have hdiscrK : Algebra.discr K ⇑bLoc = algebraMap A K (Algebra.discr A ⇑pb.basis) := by
    rw [hbLoc]; exact Algebra.discr_localizationLocalization A (nonZeroDivisors A) L pb.basis
  -- discriminant of a power basis over the field `K` is `± norm f'(θ)`
  have hnorm : Algebra.discr K ⇑pbL.basis
      = (-1) ^ k * (Algebra.norm K)
          (aeval pbL.gen (derivative (minpoly K pbL.gen))) :=
    Algebra.discr_powerBasis_eq_norm K pbL
  -- minimal polynomial descends to the fraction field
  have hmin : minpoly K θL = Polynomial.map (algebraMap A K) f := by
    rw [hθL, hf]; exact minpoly.isIntegrallyClosed_eq_field_fractions K L hθint
  -- pull the derivative-evaluation down to `B`
  have haeval : aeval θL (derivative (minpoly K θL))
      = algebraMap B L (aeval θ (derivative f)) := by
    rw [hmin, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap, hθL,
      Polynomial.aeval_algebraMap_apply]
  -- integral norm ↔ field norm
  have hintnorm : algebraMap A K (Algebra.intNorm A B (aeval θ (derivative f)))
      = (Algebra.norm K) (algebraMap B L (aeval θ (derivative f))) :=
    Algebra.algebraMap_intNorm (K := K) (L := L) _
  -- identity after applying `algebraMap A K`
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
