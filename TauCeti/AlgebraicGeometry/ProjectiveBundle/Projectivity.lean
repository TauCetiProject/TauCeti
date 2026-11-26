/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveBundle.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

/-!
# Projectivity of a projective bundle over affine opens

Use `ProjectiveBundles.projectiveBundle.affineOpenIso` to identify the restriction over an
affine open `U` with `Proj (Sym Γ(E, U))` over `Spec Γ(S, U)`.
`ProjectiveBundles.projectiveBundle.isProjectiveOver_affineOpen` gives projectivity when
`Γ(E, U)` is finite, by `AlgebraicGeometry.Scheme.isProjectiveOver_proj` and
`AlgebraicGeometry.Scheme.IsProjectiveOver.of_isClosedImmersion`.
`ProjectiveBundles.projectiveBundle.isProjectiveOver_affineOpen_of_isFiniteType` gives
projectivity on every affine open for a finite-type quasi-coherent module. Apply
`AlgebraicGeometry.Scheme.IsProjectiveOver.exists_isClosedImmersion_pi` to obtain a closed
immersion into projective space with finitely many coordinates over `Γ(S, U)`.

## References

* [The Stacks Project, Section 27.21, Projective bundles](https://stacks.math.columbia.edu/tag/01OA)
* [The Stacks Project, Definition 29.44.1](https://stacks.math.columbia.edu/tag/01W8)
-/

public section

noncomputable section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle

open _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (F : QuasicoherentSheaf S)
variable {U : S.Opens} (hU : IsAffineOpen U)

/-- The restriction of `P(E)` to an affine open `U` is projective over its coefficient ring when
`Γ(E, U)` is finite. This holds on every affine open if `E` is of finite type, by
`Scheme.Modules.finite_sections_of_isAffineOpen`. See Stacks, Section 27.21 and
Definition 29.44.1. -/
theorem isProjectiveOver_affineOpen
    [Module.Finite Γ(S, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj)] :
    @Scheme.IsProjectiveOver Γ(S, U) _ (pullback hU.fromSpec (projection S F.obj))
      (OverClass.ofHom (pullback.fst hU.fromSpec (projection S F.obj))) := by
  let P := pullback hU.fromSpec (projection S F.obj)
  let : P.Over (Spec (.of Γ(S, U))) := ⟨pullback.fst hU.fromSpec (projection S F.obj)⟩
  let e : P ≅ Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(S, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj)) :=
    (Over.forget _).mapIso (affineOpenIso F hU)
  have : e.hom.IsOver (Spec (.of Γ(S, U))) := ⟨Over.w (affineOpenIso F hU).hom⟩
  exact Scheme.IsProjectiveOver.of_isClosedImmersion Γ(S, U) e.hom

/-- A projective bundle of a finite-type quasi-coherent sheaf is projective over each affine
open of the base. See Stacks, Section 27.21 and Definition 29.44.1. -/
theorem isProjectiveOver_affineOpen_of_isFiniteType [F.obj.IsFiniteType] :
    @Scheme.IsProjectiveOver Γ(S, U) _ (pullback hU.fromSpec (projection S F.obj))
      (OverClass.ofHom (pullback.fst hU.fromSpec (projection S F.obj))) := by
  have : Module.Finite Γ(S, U) ((Scheme.Modules.sectionsFunctor U).obj F.obj) :=
    Scheme.Modules.finite_sections_of_isAffineOpen F.obj U hU
  exact isProjectiveOver_affineOpen F hU

end TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle
