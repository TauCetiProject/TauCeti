/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion

/-!
# Cohomology of schemes finite over a field

A scheme finite over a field `k` is affine and Noetherian, so the acyclicity of quasi-coherent
sheaves on affine locally Noetherian schemes
(`Scheme.Modules.subsingleton_cohomology_succ_of_isAffine`) applies: a quasi-coherent sheaf on it
has no cohomology in positive degrees.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isFinite`:
  acyclicity of quasi-coherent sheaves on schemes finite over a field.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 3.5.
-/

public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent sheaf on a scheme finite over a field has no cohomology in positive
degrees. -/
theorem subsingleton_cohomology_succ_of_isFinite (k : Type u) [Field k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsFinite (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Cohomology M (n + 1)) := by
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  exact subsingleton_cohomology_succ_of_isAffine M n

end AlgebraicGeometry.Scheme.Modules

end
