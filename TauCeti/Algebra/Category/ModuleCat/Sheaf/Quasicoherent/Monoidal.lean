/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.Monoidal.Subcategory
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

## Main declarations

* `SheafOfModules.QuasicoherentData.tensor`: quasi-coherent data for `M ⊗ N` built from
  quasi-coherent data for `M` and for `N`;
* `TauCeti.SheafOfModules.isQuasicoherent_tensorObj`: `M ⊗ N` is quasi-coherent when `M` and
  `N` are;
* `TauCeti.SheafOfModules.isMonoidal_isQuasicoherent`: quasi-coherence is an
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

end SheafOfModules

end

end TauCeti
