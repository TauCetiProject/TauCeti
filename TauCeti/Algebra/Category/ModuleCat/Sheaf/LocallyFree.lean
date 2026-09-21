/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Biprod
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
sheaves of modules form a monoidal full subcategory (`ObjectProperty.fullMonoidalSubcategory`).
In appropriate geometric settings, these are the sheaves of sections of vector bundles.

Finite locally free sheaves also contain the zero sheaf (the free sheaf on the empty type) and are
closed under direct sums, hence under finite products, so they form an additive full subcategory.

Local freeness is also shown to be invariant under isomorphism, by transporting local bases along
an isomorphism (`SheafOfModules.LocalGeneratorsData.ofIsIso`).

Finally, local freeness is local for the topology: local bases chosen after restricting to every
member of a covering family can be combined into local bases on the original site. The
construction follows the one proposed in
[Mathlib PR #39553](https://github.com/leanprover-community/mathlib4/pull/39553).

## Main declarations

* `SheafOfModules.isLocallyFree`: local freeness as an `ObjectProperty`; it is closed under
  isomorphisms;
* `TauCeti.SheafOfModules.isLocallyFree_tensorObj`: `M ⊗ N` is locally free when `M` and `N`
  are;
* `TauCeti.SheafOfModules.isMonoidal_isLocallyFree`: local freeness is an
  `ObjectProperty.IsMonoidal`;
* `SheafOfModules.isFiniteLocallyFree`: the property of being locally free and finitely
  presented, and `TauCeti.SheafOfModules.isMonoidal_isFiniteLocallyFree`: it is an
  `ObjectProperty.IsMonoidal`;
* `TauCeti.SheafOfModules.iteratedSliceEquivalence` compares sheaves of modules on an iterated
  slice with those on the slice over the composite,
  `TauCeti.SheafOfModules.LocalGeneratorsData.bind` combines local-generator atlases over a cover,
  and `TauCeti.SheafOfModules.IsLocallyFree.of_coversTop` shows that local freeness descends from a
  cover;
* `TauCeti.SheafOfModules.containsZero_isFiniteLocallyFree` and
  `TauCeti.SheafOfModules.isClosedUnderFiniteProducts_isFiniteLocallyFree`: finite locally free
  sheaves contain a zero object and are closed under finite products.

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
def _root_.SheafOfModules.LocalGeneratorsData.ofIsIso (f : M ⟶ N) [IsIso f]
    (q : M.LocalGeneratorsData) : N.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi (f.over (q.X i))

/-- Transporting local generators preserves the cover's index type. -/
@[simp]
theorem _root_.SheafOfModules.LocalGeneratorsData.ofIsIso_I (f : M ⟶ N) [IsIso f]
    (q : M.LocalGeneratorsData) : (q.ofIsIso f).I = q.I := (rfl)

/-- Transporting local generators preserves the covering objects. -/
@[simp]
theorem _root_.SheafOfModules.LocalGeneratorsData.ofIsIso_X (f : M ⟶ N) [IsIso f]
    (q : M.LocalGeneratorsData) :
    (q.ofIsIso f).X = fun i ↦ q.X ((LocalGeneratorsData.ofIsIso_I f q).mp i) := (rfl)

/-- Transporting local generators pushes each generating family along the restricted isomorphism. -/
@[simp]
theorem _root_.SheafOfModules.LocalGeneratorsData.ofIsIso_generators
    (f : M ⟶ N) [IsIso f] (q : M.LocalGeneratorsData) (i : (q.ofIsIso f).I) :
    (q.ofIsIso f).generators i =
      cast (by rw [LocalGeneratorsData.ofIsIso_X])
        ((q.generators ((LocalGeneratorsData.ofIsIso_I f q).mp i)).ofEpi
          (f.over (q.X ((LocalGeneratorsData.ofIsIso_I f q).mp i)))) := (rfl)

/-- Locally free data transported along an isomorphism is locally free data. -/
instance (f : M ⟶ N) [IsIso f] (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] :
    (q.ofIsIso f).IsLocallyFreeData where
  isIso i := by
    rw [LocalGeneratorsData.ofIsIso_generators]
    exact (q.generators _).isIso_ofEpi_π (f.over (q.X _))
      (LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) _)

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

section Locality

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

variable (R) in
/-- Restriction along `Over.iteratedSliceEquiv Y`, as an equivalence between sheaves of modules on
the slice over `Y.left` and sheaves of modules on the iterated slice over `Y`. -/
@[expose]
noncomputable def iteratedSliceEquivalence {Z : C} (Y : Over Z) :
    SheafOfModules.{u} (R.over Y.left) ≌ SheafOfModules.{u} ((R.over Z).over Y) :=
  pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Y)
    (S := (R.over Z).over Y) (R := R.over Y.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)

/-- Generating sections of the twice-restricted sheaf `(M.over Z).over Y`, read along
`iteratedSliceEquivalence` as generating sections of the restriction of `M` to `Y.left`. -/
noncomputable def overIteratedSliceGenerators {Z : C} {Y : Over Z}
    (σ : ((M.over Z).over Y).GeneratingSections) : (M.over Y.left).GeneratingSections :=
  (σ.map (iteratedSliceEquivalence R Y).inverse (.refl _)).ofEpi
    ((iteratedSliceEquivalence R Y).fullyFaithfulFunctor.preimageIso
      (by exact (iteratedSliceEquivalence R Y).counitIso.app ((M.over Z).over Y))).hom

/-- Reading a local basis through `iteratedSliceEquivalence` again gives a local basis. -/
instance isIso_overIteratedSliceGenerators_π {Z : C} {Y : Over Z}
    (σ : ((M.over Z).over Y).GeneratingSections) [IsIso σ.π] :
    IsIso (overIteratedSliceGenerators σ).π := by
  let η : _root_.SheafOfModules.unit (R.over Y.left) ≅
      (iteratedSliceEquivalence R Y).inverse.obj
        (_root_.SheafOfModules.unit ((R.over Z).over Y)) := .refl _
  have h : IsIso (σ.map (iteratedSliceEquivalence R Y).inverse η).π := by
    rw [GeneratingSections.map_π_eq]
    exact IsIso.comp_isIso' (mapFreeIso _ _ _).isIso_hom (Functor.map_isIso _ _)
  exact GeneratingSections.isIso_ofEpi_π _ _ h

/-- Combine local-generator atlases on the restrictions of `M` to a covering family.

The resulting atlas is indexed by a covering object and then by a member of the atlas chosen on
its slice, and its generators are the chosen ones, read through
`iteratedSliceEquivalence`. -/
noncomputable def LocalGeneratorsData.bind {I : Type*}
    (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, _root_.SheafOfModules.LocalGeneratorsData (M.over (X i))) :
    M.LocalGeneratorsData where
  I := (i : I) × (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop := hX.over fun i ↦ (D i).coversTop
  generators i := overIteratedSliceGenerators ((D i.1).generators i.2)

/-- Combining local-generator atlases indexes the cover by a covering object and a member of the
atlas chosen on its slice. -/
@[simp]
theorem LocalGeneratorsData.bind_I {I : Type*} (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, _root_.SheafOfModules.LocalGeneratorsData (M.over (X i))) :
    (LocalGeneratorsData.bind X hX D).I = ((i : I) × (D i).I) := (rfl)

/-- The covering objects of a combined atlas are the underlying objects of the chosen slices. -/
@[simp]
theorem LocalGeneratorsData.bind_X {I : Type*} (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, _root_.SheafOfModules.LocalGeneratorsData (M.over (X i))) :
    (LocalGeneratorsData.bind X hX D).X = fun i ↦
      ((D ((LocalGeneratorsData.bind_I X hX D).mp i).1).X
        ((LocalGeneratorsData.bind_I X hX D).mp i).2).left := (rfl)

/-- The complete description of a combined atlas: it is indexed by pairs of a covering object and
a member of the atlas chosen on its slice, and its generators are the chosen ones read through
`iteratedSliceEquivalence`. This is the elimination principle for `LocalGeneratorsData.bind`,
whose body is not exposed. -/
theorem LocalGeneratorsData.bind_eq {I : Type*} (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, _root_.SheafOfModules.LocalGeneratorsData (M.over (X i))) :
    LocalGeneratorsData.bind X hX D =
      { I := (i : I) × (D i).I
        X := fun ij ↦ ((D ij.1).X ij.2).left
        coversTop := hX.over fun i ↦ (D i).coversTop
        generators := fun ij ↦ overIteratedSliceGenerators ((D ij.1).generators ij.2) } := (rfl)

/-- Combining locally free atlases over a cover produces locally free data on the original site. -/
instance LocalGeneratorsData.isLocallyFreeData_bind {I : Type*}
    (X : I → C) (hX : J.CoversTop X)
    (D : ∀ i, _root_.SheafOfModules.LocalGeneratorsData (M.over (X i)))
    [∀ i, (D i).IsLocallyFreeData] : (LocalGeneratorsData.bind X hX D).IsLocallyFreeData where
  isIso i := isIso_overIteratedSliceGenerators_π ((D i.1).generators i.2)

/-- If a sheaf of modules is locally free after restriction to every member of a covering family,
then it is locally free. -/
theorem IsLocallyFree.of_coversTop {I : Type*} (X : I → C)
    (hX : J.CoversTop X) [∀ i, (M.over (X i)).IsLocallyFree] : M.IsLocallyFree := by
  let D (i : I) : _root_.SheafOfModules.LocalGeneratorsData (M.over (X i)) :=
    (show (M.over (X i)).IsLocallyFree from inferInstance).exists_isLocallyFreeData.choose
  have := fun i ↦
    (show (M.over (X i)).IsLocallyFree from inferInstance).exists_isLocallyFreeData.choose_spec
  have := LocalGeneratorsData.isLocallyFreeData_bind X hX D
  exact (LocalGeneratorsData.bind (M := M) X hX D).isLocallyFree

end Locality

section DirectSum

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Finite locally free sheaves of modules are closed under binary products, which are the direct
sums `M ⊞ N`. -/
instance isClosedUnderBinaryProducts_isFiniteLocallyFree :
    (isFiniteLocallyFree R).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro M ⟨p⟩
    obtain ⟨_, _⟩ := p.prop_diag_obj ⟨.left⟩
    obtain ⟨_, _⟩ := p.prop_diag_obj ⟨.right⟩
    exact (isFiniteLocallyFree R).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
        ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit))
      ⟨isLocallyFree_biprod, isFinitePresentation_biprod⟩

variable [HasBinaryProducts C]

/-- The zero sheaf of modules is finite locally free, being the free sheaf on the empty type. -/
instance containsZero_isFiniteLocallyFree : (isFiniteLocallyFree R).ContainsZero where
  exists_zero := ⟨_, isZero_free PEmpty, inferInstance, isFinitePresentation_free PEmpty⟩

/-- Finite locally free sheaves of modules are closed under finite products, which are the finite
direct sums. -/
instance isClosedUnderFiniteProducts_isFiniteLocallyFree :
    (isFiniteLocallyFree R).IsClosedUnderFiniteProducts :=
  .mk'

end DirectSum

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
