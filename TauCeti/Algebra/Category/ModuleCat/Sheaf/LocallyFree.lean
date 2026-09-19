/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Monoidal

/-!
# Tensor products of locally free sheaves of modules

Let `R` be a sheaf of commutative rings on a small site with pullbacks. If `M` and `N` are locally
free sheaves of `R`-modules, then so is `M ⊗ N`: on a common refinement of covers on which `M`
and `N` are free, the restriction of `M ⊗ N` is the tensor product of two free sheaves, which is
free on the product of the index types. If the site also has binary products, the unit is free on
one generator, so local freeness is a monoidal property of sheaves of modules. Together with the
corresponding result for finite presentation
(`TauCeti.SheafOfModules.isMonoidal_isFinitePresentation`), this shows that finite locally free
sheaves of modules, the sheaves of sections of vector bundles, form a monoidal full subcategory
(`ObjectProperty.fullMonoidalSubcategory`).

Local freeness is also shown to be invariant under isomorphism, by transporting local bases along
an isomorphism (`SheafOfModules.LocalGeneratorsData.ofIsIso`).

## Main declarations

* `SheafOfModules.isLocallyFree`: local freeness as an `ObjectProperty`; it is closed under
  isomorphisms;
* `TauCeti.SheafOfModules.isLocallyFree_tensorObj`: `M ⊗ N` is locally free when `M` and `N`
  are;
* `TauCeti.SheafOfModules.isMonoidal_isLocallyFree`: local freeness is an
  `ObjectProperty.IsMonoidal`;
* `SheafOfModules.isFiniteLocallyFree`: the property of being locally free and finitely
  presented, and `TauCeti.SheafOfModules.isMonoidal_isFiniteLocallyFree`: it is an
  `ObjectProperty.IsMonoidal`.

## References

* [The Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

section LocalGeneratorsData

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- Local generators data transported along an isomorphism `f : M ⟶ N`: the covering family is
unchanged, and the generating sections of `M.over (q.X i)` are pushed forward along the
restriction of `f`. -/
@[expose, simps I X generators]
def _root_.SheafOfModules.LocalGeneratorsData.ofIsIso (f : M ⟶ N) [IsIso f]
    (q : M.LocalGeneratorsData) : N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (f.over (q.X i))

/-- Locally free data transported along an isomorphism is locally free data. -/
instance (f : M ⟶ N) [IsIso f] (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    (q.ofIsIso f).IsLocallyFreeData where
  -- `LocalGeneratorsData.ofIsIso_generators` cannot be rewritten here: the category in which
  -- `IsIso` is stated depends on the index `i`, whose type is `(q.ofIsIso f).I` rather than
  -- `q.I`. The generators are stated directly in their unfolded form instead.
  isIso i := (q.generators i).isIso_ofEpi_π (f.over (q.X i))
    (LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i)

variable (R) in
/-- Local freeness of sheaves of modules, as a property of objects. -/
abbrev _root_.SheafOfModules.isLocallyFree : ObjectProperty (SheafOfModules.{u} R) :=
  IsLocallyFree

/-- Local freeness is invariant under isomorphism. -/
instance : (isLocallyFree R).IsClosedUnderIsomorphisms where
  of_iso e h :=
    have := h.exists_isLocallyFreeData.choose_spec
    (h.exists_isLocallyFreeData.choose.ofIsIso e.hom).isLocallyFree

variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]

/-- The quasi-coherent data associated with locally free data presents each restriction by the
free sheaf on its local basis. -/
theorem _root_.SheafOfModules.LocalGeneratorsData.isIso_quasiCoherentData_presentation_generators_π
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (i : q.I) :
    IsIso (q.quasiCoherentData.presentation i).generators.π := by
  rw [LocalGeneratorsData.quasiCoherentData_presentation_generators]
  exact LocalGeneratorsData.IsLocallyFreeData.isIso i

variable (R) in
/-- A sheaf of modules is finite locally free if it is locally free and finitely presented. -/
abbrev _root_.SheafOfModules.isFiniteLocallyFree : ObjectProperty (SheafOfModules.{u} R) :=
  isLocallyFree R ⊓ isFinitePresentation R

end LocalGeneratorsData

section Tensor

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}} {M N : SheafOfModules.{u} (ringCatSheaf R)}

/-- The tensor product of two locally free sheaves of modules is locally free. -/
instance isLocallyFree_tensorObj [M.IsLocallyFree] [N.IsLocallyFree] :
    (M ⊗ N).IsLocallyFree := by
  obtain ⟨qM, _⟩ := ‹M.IsLocallyFree›.exists_isLocallyFreeData
  obtain ⟨qN, _⟩ := ‹N.IsLocallyFree›.exists_isLocallyFreeData
  have :
      (qM.quasiCoherentData.tensor qN.quasiCoherentData).localGeneratorsData.IsLocallyFreeData :=
    { isIso := QuasicoherentData.isIso_tensor_presentation_generators_π
        qM.quasiCoherentData qN.quasiCoherentData
        qM.isIso_quasiCoherentData_presentation_generators_π
        qN.isIso_quasiCoherentData_presentation_generators_π }
  exact (qM.quasiCoherentData.tensor qN.quasiCoherentData).localGeneratorsData.isLocallyFree

variable [HasBinaryProducts C]

/-- Local freeness of sheaves of modules is a monoidal property: the unit is locally free and
locally free sheaves are closed under tensor products. -/
instance isMonoidal_isLocallyFree :
    ObjectProperty.IsMonoidal (isLocallyFree (ringCatSheaf R)) where
  prop_unit := (isLocallyFree (ringCatSheaf R)).prop_of_iso
    (freePUnitIsoUnit (ringCatSheaf R)) inferInstance
  prop_tensor M N _ _ := inferInstanceAs (M ⊗ N).IsLocallyFree

/-- Finite local freeness of sheaves of modules is a monoidal property. Hence finite locally free
sheaves of modules form a monoidal full subcategory. -/
instance isMonoidal_isFiniteLocallyFree :
    ObjectProperty.IsMonoidal (isFiniteLocallyFree (ringCatSheaf R)) where
  prop_unit := ⟨(isLocallyFree (ringCatSheaf R)).prop_unit,
    (isFinitePresentation (ringCatSheaf R)).prop_unit⟩
  prop_tensor _ _ hM hN := ⟨(isLocallyFree (ringCatSheaf R)).prop_tensor hM.1 hN.1,
    (isFinitePresentation (ringCatSheaf R)).prop_tensor hM.2 hN.2⟩

end Tensor

end SheafOfModules

end

end TauCeti
