/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.LinearScheme.BaseChange

/-!
# Coherent base change of linear spectra

The base-change comparison for `linearSpec` respects identity morphisms and composition.
Thus taking a linear spectrum before changing the base agrees with changing the base of its
degree-one sheaf, independently of whether a change of base is performed in one or two steps.
The equations retain the grading of the linear schemes.

The comparisons are induced by the unit and counit of the linear-spectrum equivalence.
Their coherence follows from naturality and the triangle identities of that equivalence.

## References

* The Stacks Project, Section 27.6, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

open CategoryTheory Opposite
open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.QuasicoherentLinearScheme

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

/-- For the identity change of base, the linear-spectrum comparison followed by the
identity comparison of sheaf pullback is the identity comparison of linear-scheme pullback. -/
@[reassoc]
theorem linearSpecPullbackIso_hom_id (F : (QuasicoherentSheaf X)ᵒᵖ) :
    (linearSpecPullbackIso (𝟙 X)).hom.app F ≫
        (linearSpec X).map (((QuasicoherentSheaf.pullbackId X).inv.app F.unop).op) =
      (pullbackId X).hom.app ((linearSpec X).obj F) := by
  rw [linearSpecPullbackIso_hom_app, pullbackId_hom_app,
    ← linearSpecEquiv_unitInv_app, ← linearSpecEquiv_counit_app]
  have ht : (linearSpecEquiv X).counit.app ((linearSpec X).obj F) =
      (linearSpec X).map ((linearSpecEquiv X).unitInv.app F) :=
    (linearSpecEquiv X).counit_app_functor F
  rw [ht]
  -- The full-subcategory module instances require reducible transport through functor mapping.
  erw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg ((linearSpec X).map)
    ((NatIso.op (QuasicoherentSheaf.pullbackId X)).inv.naturality
      ((linearSpecEquiv X).unitInv.app F))

/-- For two successive changes of base, the two linear-spectrum comparisons followed by
the sheaf composition comparison agree with the linear-scheme composition comparison followed
by the comparison for the composite morphism. -/
@[reassoc]
theorem linearSpecPullbackIso_hom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : (QuasicoherentSheaf Z)ᵒᵖ) :
    (pullback f).map ((linearSpecPullbackIso g).hom.app F) ≫
        (linearSpecPullbackIso f).hom.app ((QuasicoherentSheaf.pullback g).op.obj F) ≫
          (linearSpec X).map (((QuasicoherentSheaf.pullbackComp f g).inv.app F.unop).op) =
      (pullbackComp f g).hom.app ((linearSpec Z).obj F) ≫
        (linearSpecPullbackIso (f ≫ g)).hom.app F := by
  simp only [linearSpecPullbackIso_hom_app, pullbackComp_hom_app,
    pullbackDegreeOneIso_hom_app, ← linearSpecEquiv_unitInv_app]
  -- Rewrite at reducible transparency to align the full-subcategory module instances.
  erw [pullback_map]
  erw [← Category.assoc]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg ((linearSpec X).map)
  have hu := (linearSpecEquiv Y).unitInv.naturality
    ((QuasicoherentSheaf.pullback g).op.map ((linearSpecEquiv Z).unitInv.app F))
  have hc := (NatIso.op (QuasicoherentSheaf.pullbackComp f g)).inv.naturality
    ((linearSpecEquiv Z).unitInv.app F)
  erw [hu, Functor.map_comp, Category.assoc]
  exact congrArg (_ ≫ ·) hc

/-- The degree-one comparison respects identity base change: extracting degree one from
the identity comparison of linear schemes gives the identity comparison of sheaves. -/
@[reassoc]
theorem pullbackDegreeOneIso_hom_id (V : QuasicoherentLinearScheme X) :
    (degreeOne X).map ((pullbackId X).hom.app V) =
      (pullbackDegreeOneIso (𝟙 X)).hom.app V ≫
        ((QuasicoherentSheaf.pullbackId X).inv.app ((degreeOne X).obj V).unop).op := by
  rw [pullbackId_hom_app, pullbackDegreeOneIso_hom_app,
    ← linearSpecEquiv_unitInv_app, ← linearSpecEquiv_counit_app]
  have ht : (degreeOne X).map ((linearSpecEquiv X).counit.app V) =
      (linearSpecEquiv X).unitInv.app ((degreeOne X).obj V) :=
    ((linearSpecEquiv X).unitInv_app_inverse V).symm
  -- The slice-module and scheme-module presentations of the full subcategories agree at
  -- reducible transparency; use it when composing the mapped comparison.
  erw [Functor.map_comp, ht]
  exact (linearSpecEquiv X).unitInv.naturality
    (((QuasicoherentSheaf.pullbackId X).inv.app ((degreeOne X).obj V).unop).op)

/-- Extracting degree one commutes with the composition comparison for base change.
This is the coherence equation for the inverse of the linear-spectrum equivalence. -/
@[reassoc]
theorem pullbackDegreeOneIso_hom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : QuasicoherentLinearScheme Z) :
    (degreeOne X).map ((pullbackComp f g).hom.app V) ≫
        (pullbackDegreeOneIso (f ≫ g)).hom.app V =
      (pullbackDegreeOneIso f).hom.app ((pullback g).obj V) ≫
        (QuasicoherentSheaf.pullback f).op.map ((pullbackDegreeOneIso g).hom.app V) ≫
          ((QuasicoherentSheaf.pullbackComp f g).inv.app ((degreeOne Z).obj V).unop).op := by
  simp only [pullbackComp_hom_app, pullbackDegreeOneIso_hom_app,
    ← linearSpecEquiv_unitInv_app]
  -- Normalize the mapped composite using the same full-subcategory instance transport.
  erw [← Functor.map_comp]
  exact (linearSpecEquiv X).unitInv.naturality
    ((QuasicoherentSheaf.pullback f).op.map
        ((linearSpecEquiv Y).unitInv.app
          ((QuasicoherentSheaf.pullback g).op.obj ((degreeOne Z).obj V))) ≫
      ((QuasicoherentSheaf.pullbackComp f g).inv.app ((degreeOne Z).obj V).unop).op)

end

end TauCeti.AlgebraicGeometry.QuasicoherentLinearScheme
