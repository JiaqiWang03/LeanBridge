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
  sorry
