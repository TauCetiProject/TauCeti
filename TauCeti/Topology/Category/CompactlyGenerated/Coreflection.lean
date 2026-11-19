/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.CompactlyGenerated
public import Mathlib.Topology.Category.TopCat.Monoidal
public import TauCeti.Topology.Convenient.CompactlyGenerated

/-!
# The compact-generation coreflection on `TopCat`

To embed `TopCat` into a cartesian closed category for homotopy theory without altering existing
compactly generated spaces, one refines spaces to `TopologicalSpace.compactlyGenerated.{u} X`. Via
`Topology.isGeneratedBy_compHaus_iff`, we identify `CompactlyGenerated.{u, w}` strictly with
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` over `TopCat.{w}`
(`CompactlyGenerated.equivGeneratedByTopCat`) and transport `GeneratedByTopCat.adj`
(`Mathlib.Topology.Convenient.Category`):

* `TopCat.toCompactlyGenerated : TopCat.{w} ⥤ CompactlyGenerated.{u, w}` refines `X` while keeping
  points and maps fixed, unwrapped pointwise via `TopCat.toCompactlyGeneratedEquiv X`.
* `CompactlyGenerated.adj : compactlyGeneratedToTop.{u, w} ⊣ TopCat.toCompactlyGenerated.{u, w}`
  makes `CompactlyGenerated.{u, w}` coreflective in `TopCat.{w}`, creating colimits and providing
  all limits and colimits.
* `CompactlyGenerated.isIso_adjCounit_app_iff` characterizes `IsIso (adjCounit.app X)` by
  `UCompactlyGeneratedSpace.{u} X`, specializing to Hausdorff weakly locally compact spaces at
  `max w u` (`isIso_adjCounit_app_of_t2Space_of_weaklyLocallyCompactSpace`; see
  `TauCeti.Topology.CWComplex.Classical.CompactlyGenerated` for Hausdorff CW complexes at any `u`),
  together with specializations to `PEmpty`, `PUnit`, `TopCat.I`, and Sierpiński `Prop`.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core) compactly
  generated spaces*, Topology Appl. 143 (2004), 105–145.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Section "Compactly Generated Spaces".
-/

public section

universe u v w

open CategoryTheory Limits Topology TopologicalSpace

instance : UCompactlyGeneratedSpace.{u} TopCat.I.{w} :=
  inferInstanceAs (UCompactlyGeneratedSpace.{u} (ULift unitInterval))

/-! ### Comparison with `GeneratedByTopCat` and the coreflection adjunction -/

namespace CompactlyGenerated

/-- Reinterpret an object or morphism of `CompactlyGenerated.{u, w}` in
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`. -/
@[expose, simps] def toGeneratedByTopCat :
    CompactlyGenerated.{u, w} ⥤ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) where
  obj X := ⟨X.toTop, (isGeneratedBy_compHaus_iff X.toTop).2 X.is_compactly_generated⟩
  map f := ObjectProperty.homMk f.hom

/-- Reinterpret an object or morphism of `GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` in
`CompactlyGenerated.{u, w}`. -/
@[expose, simps] def fromGeneratedByTopCat :
    GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) ⥤ CompactlyGenerated.{u, w} where
  obj Y := { toTop := Y.obj, is_compactly_generated := (isGeneratedBy_compHaus_iff Y.obj).1 Y.2 }
  map g := InducedCategory.homMk g.hom

@[simp] theorem toGeneratedByTopCat_comp_fromGeneratedByTopCat :
    toGeneratedByTopCat.{u, w} ⋙ fromGeneratedByTopCat.{u, w} = 𝟭 _ := (rfl)
@[simp] theorem fromGeneratedByTopCat_comp_toGeneratedByTopCat :
    fromGeneratedByTopCat.{u, w} ⋙ toGeneratedByTopCat.{u, w} = 𝟭 _ := (rfl)
@[simp] theorem toGeneratedByTopCat_comp_toTopCat :
    toGeneratedByTopCat.{u, w} ⋙ GeneratedByTopCat.toTopCat = compactlyGeneratedToTop.{u, w} :=
  (rfl)
@[simp] theorem fromGeneratedByTopCat_comp_compactlyGeneratedToTop :
    fromGeneratedByTopCat.{u, w} ⋙ compactlyGeneratedToTop.{u, w} = GeneratedByTopCat.toTopCat :=
  (rfl)

/-- `CompactlyGenerated.{u, w}` is strictly isomorphic to
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`. -/
@[expose, simps] def equivGeneratedByTopCat :
    CompactlyGenerated.{u, w} ≌ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) where
  functor := toGeneratedByTopCat
  inverse := fromGeneratedByTopCat
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := Category.comp_id _

instance : toGeneratedByTopCat.{u, w}.IsEquivalence := equivGeneratedByTopCat.isEquivalence_functor
instance : fromGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivGeneratedByTopCat.isEquivalence_inverse

end CompactlyGenerated

/-- The compact-generation coreflector `TopCat.{w} ⥤ CompactlyGenerated.{u, w}`, refining the
topology of `X` to the `u`-compactly generated topology while leaving points and maps unchanged. -/
@[expose] def TopCat.toCompactlyGenerated : TopCat.{w} ⥤ CompactlyGenerated.{u, w} :=
  TopCat.toGeneratedByTopCat (X := fun K : CompHaus.{u} ↦ K) ⋙
    CompactlyGenerated.fromGeneratedByTopCat.{u, w}

namespace TopCat

/-- The canonical bijection between `TopCat.toCompactlyGenerated.{u, w}.obj X` and `X`. -/
@[expose] def toCompactlyGeneratedEquiv (X : TopCat.{w}) :
    ↑(TopCat.toCompactlyGenerated.{u, w}.obj X) ≃ X :=
  WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)

@[ext] theorem toCompactlyGenerated_obj_ext {X : TopCat.{w}}
    {x y : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)}
    (h : toCompactlyGeneratedEquiv.{u, w} X x = toCompactlyGeneratedEquiv.{u, w} X y) : x = y :=
  (toCompactlyGeneratedEquiv.{u, w} X).injective h
@[simp] theorem toCompactlyGenerated_map_apply {X Y : TopCat.{w}} (f : X ⟶ Y)
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    toCompactlyGeneratedEquiv.{u, w} Y (TopCat.toCompactlyGenerated.{u, w}.map f x) =
      f (toCompactlyGeneratedEquiv.{u, w} X x) := (rfl)
@[continuity, fun_prop] theorem continuous_toCompactlyGeneratedEquiv (X : TopCat.{w}) :
    Continuous (toCompactlyGeneratedEquiv.{u, w} X) :=
  WithGeneratedByTopology.continuous_equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)

/-- A subset of `TopCat.toCompactlyGenerated.{u, w}.obj X` is open iff its image in `X` is open in
`TopologicalSpace.compactlyGenerated.{u} X`. -/
theorem isOpen_toCompactlyGenerated_iff (X : TopCat.{w})
    (U : Set ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    IsOpen U ↔ IsOpen[TopologicalSpace.compactlyGenerated.{u} X]
      ((toCompactlyGeneratedEquiv.{u, w} X).symm ⁻¹' U) := by
  refine (WithGeneratedByTopology.isOpen_iff
    (X := fun K : CompHaus.{u} ↦ K) (Y := X) (U := U)).trans ?_
  rw [← TopologicalSpace.generatedBy_compHaus, TopologicalSpace.generatedBy]
  simp only [isOpen_iSup_iff, isOpen_coinduced, Set.preimage_preimage]; rfl

/-- A subset of `TopCat.toCompactlyGenerated.{u, w}.obj X` is closed iff its image in `X` is closed
in `TopologicalSpace.compactlyGenerated.{u} X`. -/
theorem isClosed_toCompactlyGenerated_iff (X : TopCat.{w})
    (C : Set ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    IsClosed C ↔ IsClosed[TopologicalSpace.compactlyGenerated.{u} X]
      ((toCompactlyGeneratedEquiv.{u, w} X).symm ⁻¹' C) := by
  rw [← isOpen_compl_iff, isOpen_toCompactlyGenerated_iff]
  exact @isOpen_compl_iff _ _ (TopologicalSpace.compactlyGenerated.{u} X)

/-- A map out of `TopCat.toCompactlyGenerated.{u, w}.obj X` is continuous iff its composites with
all probes from `u`-small compact Hausdorff spaces into `X` are continuous. -/
theorem continuous_from_toCompactlyGenerated_iff {X : TopCat.{w}} {Y : Type v}
    [TopologicalSpace Y] (g : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X) → Y) :
    Continuous g ↔ ∀ (K : CompHaus.{u}) (f : C(K, X)),
      Continuous (g ∘ (toCompactlyGeneratedEquiv.{u, w} X).symm ∘ f) :=
  WithGeneratedByTopology.continuous_from_iff (X := fun K : CompHaus.{u} ↦ K) (Y := X) g

/-- A map from a `u`-compactly generated space `Y` into `TopCat.toCompactlyGenerated.{u, w}.obj X`
is continuous iff the underlying map `Y → X` is continuous. -/
theorem toCompactlyGeneratedEquiv_symm_comp_continuous_iff {X : TopCat.{w}} {Y : Type v}
    [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} Y] (g : Y → X) :
    Continuous ((toCompactlyGeneratedEquiv.{u, w} X).symm ∘ g) ↔ Continuous g :=
  IsGeneratedBy.equiv_symm_comp_continuous_iff (fun K : CompHaus.{u} ↦ K) g

instance instIsEmptyToCompactlyGenerated (X : TopCat.{w}) [IsEmpty X] :
    IsEmpty ↑(TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  inferInstanceAs (IsEmpty (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X))
instance instNontrivialToCompactlyGenerated (X : TopCat.{w}) [Nontrivial X] :
    Nontrivial ↑(TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  inferInstanceAs (Nontrivial (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X))
/-- Refining a Hausdorff space `X` to its compactly generated topology preserves `T2Space`. -/
instance instT2SpaceToCompactlyGenerated (X : TopCat.{w}) [T2Space X] :
    T2Space ↑(TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  inferInstanceAs (T2Space (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X))

end TopCat

namespace CompactlyGenerated

/-- When `X` is `u`-compactly generated, the counit gives a homeomorphism from
`TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of X)` onto `X`. -/
def counitHomeomorph (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of X)) ≃ₜ X :=
  IsGeneratedBy.homeomorph (X := fun K : CompHaus.{u} ↦ K) (Y := X)

@[simp] theorem counitHomeomorph_apply {X : Type w} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of X))) :
    counitHomeomorph.{u, w} X x = TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of X) x := (rfl)
@[simp] theorem counitHomeomorph_symm_apply {X : Type w} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] (x : X) : (counitHomeomorph.{u, w} X).symm x =
      (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of X)).symm x := (rfl)

/-- The unit isomorphism `𝟭 _ ≅ compactlyGeneratedToTop ⋙ TopCat.toCompactlyGenerated` of the
compact-generation coreflection. -/
def adjUnitIso : 𝟭 CompactlyGenerated.{u, w} ≅
    compactlyGeneratedToTop.{u, w} ⋙ TopCat.toCompactlyGenerated.{u, w} :=
  NatIso.ofComponents (fun X ↦ isoOfHomeo (counitHomeomorph.{u, w} X.toTop).symm)
    (fun _ ↦ by ext; rfl)

/-- The counit `(TopCat.toCompactlyGenerated ⋙ compactlyGeneratedToTop) ⟶ 𝟭 TopCat` of the
compact-generation coreflection. -/
def adjCounit :
    TopCat.toCompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w} ⟶ 𝟭 TopCat.{w} :=
  GeneratedByTopCat.adjCounit (X := fun K : CompHaus.{u} ↦ K)

theorem adjCounit_eq_generatedByTopCat_adjCounit :
    adjCounit.{u, w} = GeneratedByTopCat.adjCounit (X := fun K : CompHaus.{u} ↦ K) := (rfl)
@[simp] theorem adjCounit_app_apply (X : TopCat.{w})
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    dsimp% adjCounit.{u, w}.app X x = TopCat.toCompactlyGeneratedEquiv.{u, w} X x := (rfl)
@[simp] theorem adjUnitIso_hom_app_apply (X : CompactlyGenerated.{u, w}) (x : X) :
    dsimp% TopCat.toCompactlyGeneratedEquiv.{u, w} X.toTop ((adjUnitIso.{u, w}.hom.app X) x) = x :=
  (rfl)
@[simp] theorem adjUnitIso_inv_app_apply (X : CompactlyGenerated.{u, w})
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X.toTop)) :
    dsimp% (adjUnitIso.{u, w}.inv.app X) x = TopCat.toCompactlyGeneratedEquiv.{u, w} X.toTop x :=
  (rfl)

/-- **The compact-generation coreflection**: `compactlyGeneratedToTop` is left adjoint to
`TopCat.toCompactlyGenerated`. -/
def adj : compactlyGeneratedToTop.{u, w} ⊣ TopCat.toCompactlyGenerated.{u, w} where
  unit := adjUnitIso.hom
  counit := adjCounit
  left_triangle_components _ := by ext; rfl
  right_triangle_components _ := by ext; rfl

@[simp] theorem adj_unit : adj.{u, w}.unit = adjUnitIso.{u, w}.hom := (rfl)
@[simp] theorem adj_counit : adj.{u, w}.counit = adjCounit.{u, w} := (rfl)
@[simp] theorem adj_homEquiv_apply {X : CompactlyGenerated.{u, w}} {Y : TopCat.{w}}
    (f : compactlyGeneratedToTop.{u, w}.obj X ⟶ Y) (x : X) :
    TopCat.toCompactlyGeneratedEquiv.{u, w} Y (adj.{u, w}.homEquiv X Y f x) = f x := by
  rw [Adjunction.homEquiv_unit, CategoryTheory.comp_apply, adj_unit,
    TopCat.toCompactlyGenerated_map_apply]
  exact congrArg f (adjUnitIso_hom_app_apply X x)
@[simp] theorem adj_homEquiv_symm_apply {X : CompactlyGenerated.{u, w}} {Y : TopCat.{w}}
    (g : X ⟶ TopCat.toCompactlyGenerated.{u, w}.obj Y) (x : X) :
    dsimp% (adj.{u, w}.homEquiv X Y).symm g x = TopCat.toCompactlyGeneratedEquiv.{u, w} Y (g x) :=
  congr($(Adjunction.homEquiv_counit adj.{u, w} X Y g) x).trans (adjCounit_app_apply.{u, w} Y (g x))

instance : IsIso adj.{u, w}.unit := inferInstanceAs (IsIso adjUnitIso.{u, w}.hom)
instance : compactlyGeneratedToTop.{u, w}.IsLeftAdjoint := adj.isLeftAdjoint
instance : TopCat.toCompactlyGenerated.{u, w}.IsRightAdjoint := adj.isRightAdjoint
instance : TopCat.toCompactlyGenerated.{u, w}.Faithful :=
  inferInstanceAs ((TopCat.toContinuousGeneratedByCat (fun K : CompHaus.{u} ↦ K) ⋙
    ContinuousGeneratedByCat.toGeneratedByTopCat ⋙
    CompactlyGenerated.fromGeneratedByTopCat.{u, w}).Faithful)

/-- `CompactlyGenerated.{u, w}` is a coreflective subcategory of `TopCat.{w}`. -/
instance instCoreflectiveCompactlyGeneratedToTop : Coreflective compactlyGeneratedToTop.{u, w} where
  R := TopCat.toCompactlyGenerated
  adj := adj

noncomputable instance instCreatesColimitsCompactlyGeneratedToTop :
    CreatesColimits compactlyGeneratedToTop.{u, w} := comonadicCreatesColimits _
instance : HasLimits CompactlyGenerated.{u, w} := hasLimits_of_coreflective compactlyGeneratedToTop
instance : HasColimits CompactlyGenerated.{u, w} :=
  hasColimits_of_hasColimits_createsColimits compactlyGeneratedToTop
instance (X : TopCat.{w}) :
    IsIso (TopCat.toCompactlyGenerated.{u, w}.map (adjCounit.{u, w}.app X)) :=
  inferInstanceAs (IsIso (TopCat.toCompactlyGenerated.map (adj.counit.app X)))

/-! ### Characterization and specializations of the counit isomorphism -/

/-- If `X` is `u`-compactly generated, `adjCounit.app X` is an isomorphism in `TopCat.{w}`. -/
instance isIso_adjCounit_app (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    IsIso (adjCounit.{u, w}.app X) := by
  rw [adjCounit_eq_generatedByTopCat_adjCounit]
  exact GeneratedByTopCat.isIso_adjCounit_app (G := fun K : CompHaus.{u} ↦ K) X

/-- **Characterization of the coreflection counit**: `adjCounit.app X` is an isomorphism in
`TopCat.{w}` if and only if `X` is already `u`-compactly generated. -/
theorem isIso_adjCounit_app_iff (X : TopCat.{w}) :
    IsIso (adjCounit.{u, w}.app X) ↔ UCompactlyGeneratedSpace.{u} X := by
  rw [adjCounit_eq_generatedByTopCat_adjCounit]
  exact (GeneratedByTopCat.isIso_adjCounit_app_iff (G := fun K : CompHaus.{u} ↦ K) X).trans
    (isGeneratedBy_compHaus_iff X)

/-- For a Hausdorff weakly locally compact space `X : TopCat.{w}`, the counit for test universe
`max w u` is an isomorphism. -/
theorem isIso_adjCounit_app_of_t2Space_of_weaklyLocallyCompactSpace (X : TopCat.{w})
    [T2Space X] [WeaklyLocallyCompactSpace X] : IsIso (adjCounit.{max w u, w}.app X) :=
  have := UCompactlyGeneratedSpace.of_t2Space_of_weaklyLocallyCompactSpace.{u, w} X; inferInstance

/-! ### Specializations: initial object, unit interval, and Sierpiński space -/

/-- The empty space `PEmpty` is initial in `CompactlyGenerated.{u, w}`. -/
def isInitialPEmpty : IsInitial (of.{u, w} PEmpty.{w + 1}) :=
  IsInitial.ofUniqueHom (fun _ ↦ ofHom ⟨PEmpty.elim, continuous_of_discreteTopology⟩)
    (fun _ _ ↦ by ext x; exact x.elim)

/-- `PUnit` is fixed up to canonical isomorphism by `TopCat.toCompactlyGenerated`. -/
def toCompactlyGeneratedPUnitIso :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of PUnit.{w + 1}) ≅ of.{u, w} PUnit.{w + 1} :=
  (adjUnitIso.{u, w}.app (of.{u, w} PUnit.{w + 1})).symm

@[simp] theorem toCompactlyGeneratedPUnitIso_hom_apply
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of PUnit.{w + 1}))) :
    toCompactlyGeneratedPUnitIso.{u, w}.hom x =
      TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of PUnit.{w + 1}) x := (rfl)
@[simp] theorem toCompactlyGeneratedPUnitIso_inv_apply (x : PUnit.{w + 1}) :
    toCompactlyGeneratedPUnitIso.{u, w}.inv x =
      (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of PUnit.{w + 1})).symm x := (rfl)

/-- The unit interval `TopCat.I` is fixed up to canonical isomorphism by
`TopCat.toCompactlyGenerated`. -/
def toCompactlyGeneratedUnitIntervalIso :
    TopCat.toCompactlyGenerated.{u, w}.obj TopCat.I.{w} ≅ of.{u, w} TopCat.I.{w} :=
  (adjUnitIso.{u, w}.app (of.{u, w} TopCat.I.{w})).symm

@[simp] theorem toCompactlyGeneratedUnitIntervalIso_hom_apply
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj TopCat.I.{w})) :
    toCompactlyGeneratedUnitIntervalIso.{u, w}.hom x =
      TopCat.toCompactlyGeneratedEquiv.{u, w} TopCat.I.{w} x := (rfl)
@[simp] theorem toCompactlyGeneratedUnitIntervalIso_inv_apply (x : TopCat.I.{w}) :
    toCompactlyGeneratedUnitIntervalIso.{u, w}.inv x =
      (TopCat.toCompactlyGeneratedEquiv.{u, w} TopCat.I.{w}).symm x := (rfl)

end CompactlyGenerated

namespace TauCeti

/-- The Sierpiński space `Prop` is already `u`-compactly generated for every universe `u`. -/
theorem compactlyGenerated_sierpinski :
    TopologicalSpace.compactlyGenerated.{u} Prop = sierpinskiSpace :=
  (eq_compactlyGenerated.{u} (X := Prop)).symm

/-- `CompactlyGenerated.of.{u, 0} Prop` is not Hausdorff (`¬ T2Space`), confirming that
`CompactlyGenerated` performs genuine compact generation without Hausdorffification. -/
theorem not_t2Space_sierpinski : ¬ T2Space (CompactlyGenerated.of.{u, 0} Prop) := fun h ↦ by
  obtain ⟨U, V, _, hVo, hTU, hFV, hUV⟩ := h.t2 (by simp : (True : Prop) ≠ False)
  exact hUV.notMem_of_mem_left hTU (Filter.mem_top.1 (nhds_false ▸ hVo.mem_nhds hFV) ▸ trivial)

end TauCeti

end
