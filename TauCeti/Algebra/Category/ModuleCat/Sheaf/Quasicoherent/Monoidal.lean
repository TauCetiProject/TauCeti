/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Refinement
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Presentation
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction
public import TauCeti.CategoryTheory.Sites.CoversTop

/-!
# The tensor product of quasi-coherent sheaves is quasi-coherent

Let `R` be a sheaf of commutative rings on a small site with pullbacks. If `M` and `N` are
quasi-coherent sheaves of `R`-modules, then so is `M ⊗ N`: on a common refinement of covers on
which `M` and `N` have presentations, the restriction of `M ⊗ N` is the tensor product of the
restrictions of `M` and `N` (`SheafOfModules.overTensorIso`), which is presented by the tensor
product of their presentations (`SheafOfModules.Presentation.tensor`). As the unit `R` is free on
one generator, quasi-coherence is a monoidal property of sheaves of modules, and quasi-coherent
sheaves of modules form a monoidal full subcategory.

The same construction applied to finite presentations gives finite presentations, so finite
presentation is a monoidal property as well. Applied to presentations whose generating morphisms
are isomorphisms, it gives presentations of the same kind; this is the local input for the tensor
product of locally free sheaves.

## Main declarations

* `SheafOfModules.QuasicoherentData.tensor`: quasi-coherent data for `M ⊗ N` built from
  quasi-coherent data for `M` and for `N`;
* `TauCeti.SheafOfModules.isQuasicoherent_tensorObj`: `M ⊗ N` is quasi-coherent when `M` and
  `N` are;
* `TauCeti.SheafOfModules.isMonoidal_isQuasicoherent`: quasi-coherence is an
  `ObjectProperty.IsMonoidal`;
* `SheafOfModules.QuasicoherentData.isIso_tensor_presentation_generators_π`: the tensor data
  presents `M ⊗ N` by free sheaves where the data for `M` and `N` do;
* `TauCeti.SheafOfModules.isFinitePresentation_tensorObj` and
  `TauCeti.SheafOfModules.isMonoidal_isFinitePresentation`: finite presentation is an
  `ObjectProperty.IsMonoidal`.

## References

* [The Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}} {M N : SheafOfModules.{u} (ringCatSheaf R)}

/-- Quasi-coherent data for `M ⊗ N` from quasi-coherent data for `M` and for `N`. Its cover is
the common refinement of the two covers, and over each of its members the presentation is the
tensor product of the restricted presentations of `M` and `N`. -/
@[expose, simps I X presentation]
def _root_.SheafOfModules.QuasicoherentData.tensor (qM : M.QuasicoherentData)
    (qN : N.QuasicoherentData) : (M ⊗ N).QuasicoherentData :=
  let r := GrothendieckTopology.CoversTop.commonRefinement qM.coversTop qN.coversTop
  { I := r.I
    X := r.X
    coversTop := r.coversTop
    presentation i :=
      -- The isomorphism lives over `R.over (r.X i)`, while the expected presentation is over the
      -- definitionally equal restriction of the sheaf of rings underlying `R`; instance search
      -- does not see through this, so the `IsIso` instance is supplied explicitly.
      @Presentation.ofIsIso _ _ _ _ _ _ _ _ (overTensorIso M N (r.X i)).inv (Iso.isIso_inv _)
        (Presentation.tensor (R := R.over (r.X i))
          ((qM.ofRefinement r.X r.coversTop r.leftIndex r.left).presentation i)
          ((qN.ofRefinement r.X r.coversTop r.rightIndex r.right).presentation i)) }

/-- The tensor product of two quasi-coherent sheaves of modules is quasi-coherent. -/
instance isQuasicoherent_tensorObj [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊗ N).IsQuasicoherent :=
  ((IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.tensor
    (IsQuasicoherent.nonempty_quasicoherentData (M := N)).some).isQuasicoherent

/-- Quasi-coherence of sheaves of modules is a monoidal property: the unit is quasi-coherent and
quasi-coherent sheaves are closed under tensor products. Hence quasi-coherent sheaves of modules
form a monoidal full subcategory (`ObjectProperty.fullMonoidalSubcategory`). -/
instance isMonoidal_isQuasicoherent [HasBinaryProducts C] :
    ObjectProperty.IsMonoidal (isQuasicoherent (ringCatSheaf R)) where
  prop_unit := (isQuasicoherent (ringCatSheaf R)).prop_of_iso
    (freePUnitIsoUnit (ringCatSheaf R)) inferInstance
  prop_tensor M N _ _ := inferInstanceAs (M ⊗ N).IsQuasicoherent

omit [HasPullbacks C] in
/-- The presentation of `M ⊗ N` over `X` assembled in `QuasicoherentData.tensor` from
presentations `P` of `M.over X` and `Q` of `N.over X` has an invertible generating morphism when
`P` and `Q` do. -/
private theorem isIso_ofIsIso_overTensorIso_tensor_generators_π (X : C)
    (P : (M.over X).Presentation) (Q : (N.over X).Presentation) (hP : IsIso P.generators.π)
    (hQ : IsIso Q.generators.π) :
    -- The presentation is spelled out with the same implicit arguments as in
    -- `QuasicoherentData.tensor`, so that this lemma applies to it syntactically; unifying the
    -- two definitionally equal restrictions of the sheaf of rings instead is very slow.
    IsIso (@Presentation.ofIsIso _ _ _ _ _ _ _ _ (overTensorIso M N X).inv (Iso.isIso_inv _)
      (Presentation.tensor (R := R.over X) P Q)).generators.π :=
  Presentation.isIso_ofIsIso_generators_π (hf := Iso.isIso_inv _) _ _
    (Presentation.isIso_tensor_generators_π _ _ hP hQ)

/-- If quasi-coherent data for `M` and for `N` present them locally by free sheaves, that is, all
their generating morphisms are isomorphisms, then so does their tensor product data for
`M ⊗ N`. -/
theorem _root_.SheafOfModules.QuasicoherentData.isIso_tensor_presentation_generators_π
    (qM : M.QuasicoherentData) (qN : N.QuasicoherentData)
    (hM : ∀ i, IsIso (qM.presentation i).generators.π)
    (hN : ∀ i, IsIso (qN.presentation i).generators.π) (i : (qM.tensor qN).I) :
    IsIso ((qM.tensor qN).presentation i).generators.π := by
  refine isIso_ofIsIso_overTensorIso_tensor_generators_π _ _ _ ?_ ?_
  · exact qM.isIso_ofRefinement_presentation_generators_π _ _ _ _ i (hM _)
  · exact qN.isIso_ofRefinement_presentation_generators_π _ _ _ _ i (hN _)

omit [HasPullbacks C] in
/-- The presentation of `M ⊗ N` over `X` assembled in `QuasicoherentData.tensor` from finite
presentations of `M.over X` and `N.over X` is finite. -/
private theorem isFinite_ofIsIso_overTensorIso_tensor (X : C) (P : (M.over X).Presentation)
    (Q : (N.over X).Presentation) (hP : P.IsFinite) (hQ : Q.IsFinite) :
    -- As in `isIso_ofIsIso_overTensorIso_tensor_generators_π`, the presentation is spelled out
    -- with the same implicit arguments as in `QuasicoherentData.tensor`.
    (@Presentation.ofIsIso _ _ _ _ _ _ _ _ (overTensorIso M N X).inv (Iso.isIso_inv _)
      (Presentation.tensor (R := R.over X) P Q)).IsFinite :=
  -- Instance search does not unify `Presentation.ofIsIso` and `Presentation.tensor` across the
  -- two definitionally equal presentations of the restricted sheaf of rings, so the instances are
  -- applied explicitly.
  @SheafOfModules.instIsFiniteOfIsIso _ _ _ _ _ _ _ _ _ (Iso.isIso_inv _) _
    (@Presentation.isFinite_tensor _ _ _ (R.over X) _ _ P Q hP hQ)

/-- The tensor product of finite quasi-coherent data is finite. -/
instance (qM : M.QuasicoherentData) (qN : N.QuasicoherentData) [qM.IsFinitePresentation]
    [qN.IsFinitePresentation] : (qM.tensor qN).IsFinitePresentation where
  isFinite_presentation i := by
    refine isFinite_ofIsIso_overTensorIso_tensor _ _ _ ?_ ?_
    · exact qM.isFinite_ofRefinement_presentation _ _ _ _ i
    · exact qN.isFinite_ofRefinement_presentation _ _ _ _ i

/-- The tensor product of two finitely presented sheaves of modules is finitely presented. -/
instance isFinitePresentation_tensorObj [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (M ⊗ N).IsFinitePresentation := by
  obtain ⟨qM, _⟩ := IsFinitePresentation.exists_quasicoherentData M
  obtain ⟨qN, _⟩ := IsFinitePresentation.exists_quasicoherentData N
  exact IsFinitePresentation.mk (M := M ⊗ N) ⟨qM.tensor qN, inferInstance⟩

/-- Finite presentation of sheaves of modules is a monoidal property: the unit is finitely
presented and finitely presented sheaves are closed under tensor products. -/
instance isMonoidal_isFinitePresentation [HasBinaryProducts C] :
    ObjectProperty.IsMonoidal (isFinitePresentation (ringCatSheaf R)) where
  prop_unit := (isFinitePresentation (ringCatSheaf R)).prop_of_iso
    (freePUnitIsoUnit (ringCatSheaf R)) inferInstance
  prop_tensor M N _ _ := inferInstanceAs (M ⊗ N).IsFinitePresentation

end SheafOfModules

end

end TauCeti
