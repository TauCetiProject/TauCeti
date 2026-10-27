/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Cohomology.Affine

/-!
# Cohomology of schemes affine over an affine base

A scheme affine over an affine scheme, for example finite over it, is itself affine, so the
acyclicity of quasi-coherent sheaves on affine schemes
(`Scheme.Modules.subsingleton_cohomology_succ_of_isAffine`) applies: a quasi-coherent sheaf on it
has no cohomology in positive degrees. The main example is a scheme finite over a field `k`, taking
the structure morphism to `Spec k`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isAffineHom`:
  acyclicity of quasi-coherent sheaves on the source of an affine morphism (for example a finite
  morphism) to an affine scheme.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 3.5.
-/

public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent sheaf on the source of an affine morphism to an affine scheme (for example, on
a scheme finite over a field) has no cohomology in positive degrees. -/
theorem subsingleton_cohomology_succ_of_isAffineHom {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    [IsAffine S] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Cohomology M (n + 1)) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  exact subsingleton_cohomology_succ_of_isAffine M n

end AlgebraicGeometry.Scheme.Modules

end
