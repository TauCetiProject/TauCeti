/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Affine
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite

/-!
# Coherent cohomology of finite covers of the projective line

Let `X` be finite over `ℙ¹_R`, where `R` is Noetherian. Every quasicoherent sheaf of finite
type on `X` has finitely generated cohomology over `R` in every degree, and its cohomology
vanishes above degree one. No flatness or reducedness assumption is imposed on `X` or the
coefficient sheaf. In particular this applies to the finite normalization maps from regular
curve models to `ℙ¹`.

Finite pushforward preserves coherent sheaves and is affine, hence preserves cohomology of
quasi-coherent sheaves; finiteness of cohomology on `ℙ¹_R` therefore transfers directly to `X`.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 8.1 and Theorem 5.2.
* The Stacks Project, Tag 02O6, finiteness of cohomology of coherent sheaves on proper schemes.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} [X.Over (Spec (.of R))]
  (f : X ⟶ projectiveLine R) [IsFinite f] [f.IsOver (Spec (.of R))]

include f

/-- Every cohomology group of a quasicoherent sheaf of finite type on a scheme finite over
`ℙ¹_R` is finite over the Noetherian ring `R`. Neither the morphism nor the coefficient
sheaf needs to be flat over `R`. -/
theorem finite_cohomology_of_isFinite_to_projectiveLine (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) : Module.Finite R (Cohomology M n) := by
  let N : SheafOfModules (projectiveLine R).ringCatSheaf := (pushforward f).obj M
  have : N.IsFinitePresentation := isFinitePresentation_pushforward_of_isFinite f M
  have : N.IsFiniteType := inferInstance
  have := projectiveLine.finite_cohomology R N n
  exact (f.moduleFinite_cohomology_pushforward_iff_of_isAffineHom R M n).mp inferInstance

end AlgebraicGeometry.Scheme.Modules
