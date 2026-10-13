/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.InternalHom.Quasicoherent
public import TauCeti.CategoryTheory.Monoidal.Closed.Kernels

/-!
# Quasicoherence of internal Hom from a finitely presented sheaf

On an arbitrary scheme, the ordinary sheaf internal Hom from a finitely presented module
sheaf to a quasicoherent module sheaf is quasicoherent. The source need not be locally free,
and no finiteness condition is imposed on the target.

A finite presentation on an open expresses internal Hom as the kernel of precomposition
between internal Homs from finite free sheaves. Those two sheaves are quasicoherent, and
quasicoherence is closed under kernels. Restriction of internal Hom to the presentation
charts then gives the result by descent.

## References

* The Stacks Project, Section 26.24 (Tag 01LA), item (10).
* The Stacks Project, Lemma 17.22.6 (Tag 01CQ), internal Hom via a local presentation.
-/

public section

open CategoryTheory Limits MonoidalClosed

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} (U : X.Opens)

local instance : HasBinaryProducts (Over U) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- The sheaf tensor product on the slice site of an open. -/
local instance monoidalCategorySheafOfModulesOver :
    MonoidalCategory (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  TauCeti.SheafOfModules.monoidalCategory (X.sheaf.over U)

/-- Symmetry of the sheaf tensor product on the slice site of an open. -/
local instance symmetricCategorySheafOfModulesOver :
    SymmetricCategory (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  TauCeti.SheafOfModules.symmetricCategory (X.sheaf.over U)

/-- The closed structure on module sheaves on the slice site of an open. -/
local instance monoidalClosedSheafOfModulesOver :
    MonoidalClosed (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  TauCeti.SheafOfModules.monoidalClosed (X.sheaf.over U)

/-- A finite presentation on the slice site of an open gives quasicoherent internal Hom
into any quasicoherent target on that site. -/
private theorem isQuasicoherent_ihom_of_presentation_over
    (M N : SheafOfModules.{u} (X.ringCatSheaf.over U))
    (P : M.Presentation) [P.IsFinite] [hN : N.IsQuasicoherent] :
    ((ihom M).obj N).IsQuasicoherent := by
  let f := P.relations.π ≫ kernel.ι P.generators.π
  have : Finite P.generators.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have : Finite P.relations.I := SheafOfModules.GeneratingSections.IsFiniteType.finite
  have hfree (I : Type u) [Finite I] :
      ((ihom (SheafOfModules.free (R := X.ringCatSheaf.over U) I)).obj N).IsQuasicoherent := by
    have hLF : (SheafOfModules.free (R := X.ringCatSheaf.over U) I).IsLocallyFree :=
      inferInstance
    have hFT : (SheafOfModules.free (R := X.ringCatSheaf.over U) I).IsFiniteType :=
      inferInstance
    -- Pass the free-sheaf instances explicitly: instance search does not identify
    -- `ringCatSheaf (X.sheaf.over U)` with `X.ringCatSheaf.over U` in these class heads.
    exact @SheafOfModules.isQuasicoherent_ihom_of_isLocallyFree _ _ _ _ _ _ _ _ _ _ _ _
      (X.sheaf.over U) (SheafOfModules.free (R := X.ringCatSheaf.over U) I) N hLF hFT
      hN
  have := hfree P.generators.I
  have := hfree P.relations.I
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
    (ihomIsoKernelOfIsColimit f P.generators.π (by simp [f]) P.isColimit N).symm
    inferInstance

variable (M N : X.Modules)

/-- Internal Hom from a finitely presented module sheaf into a quasicoherent module sheaf
is quasicoherent on every scheme. No local freeness or Noetherian hypothesis is required. -/
instance isQuasicoherent_ihom_of_isFinitePresentation
    [M.IsFinitePresentation] [N.IsQuasicoherent] :
    ((ihom (C := X.Modules) M).obj N).IsQuasicoherent := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have (i : q.I) : (((ihom (C := X.Modules) M).obj N).over (q.X i)).IsQuasicoherent := by
    have : (q.presentation i).IsFinite := hq.isFinite_presentation i
    have := SheafOfModules.isQuasicoherent_over N (q.X i)
    have h := isQuasicoherent_ihom_of_presentation_over (q.X i)
      (M.over (q.X i)) (N.over (q.X i)) (q.presentation i)
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (q.X i))).prop_of_iso
      ((M.overIhomIso X.sheaf (q.X i)).app N).symm h
  exact SheafOfModules.IsQuasicoherent.of_coversTop (R := X.ringCatSheaf)
    ((ihom (C := X.Modules) M).obj N) q.X q.coversTop

end

end TauCeti.AlgebraicGeometry
