/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.CompactlyGenerated
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Sequences
public import TauCeti.Topology.CWComplex.Classical.DeltaGenerated
public import TauCeti.Topology.Convenient.CompactlyGenerated

/-!
# The compact-generation coreflection on `TopCat`

Mathlib defines the category `CompactlyGenerated.{u, w}` of `w`-small topological spaces that are
`u`-compactly generated (`UCompactlyGeneratedSpace.{u}`), together with its fully faithful
forgetful embedding `CompactlyGenerated.compactlyGeneratedToTop : CompactlyGenerated.{u, w} ⥤
TopCat.{w}`, and separately defines `GeneratedByTopCat.{w} X` with its coreflection
`GeneratedByTopCat.adj` for an arbitrary family `X` of test spaces.

Using `Topology.isGeneratedBy_compHaus_iff`, we identify `CompactlyGenerated.{u, w}` with
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` over `TopCat.{w}` and transport the
coreflection to `CompactlyGenerated.{u, w}`:

* `TopCat.toCompactlyGenerated : TopCat.{w} ⥤ CompactlyGenerated.{u, w}` refines the topology of a
  space `X` to `TopologicalSpace.compactlyGenerated.{u} X` while keeping the underlying set and
  underlying functions unchanged.
* `CompactlyGenerated.adj : compactlyGeneratedToTop.{u, w} ⊣ TopCat.toCompactlyGenerated.{u, w}`
  exhibits `CompactlyGenerated.{u, w}` as a coreflective subcategory of `TopCat.{w}` with
  invertible unit, creating all colimits and admitting all limits and colimits.
* `CompactlyGenerated.isIso_adjCounit_app_iff` shows that the counit `k X ⟶ X` at `X : TopCat.{w}`
  is an isomorphism in `TopCat.{w}` if and only if `X` is already `u`-compactly generated. In
  particular, the counit is a homeomorphism for every Hausdorff CW complex and every Hausdorff
  weakly locally compact space (for test universes `max w u`).
* Concrete checks verify the coreflection on the terminal one-point space, initial empty space,
  unit interval `TopCat.I`, and Sierpiński space `Prop`, showing in particular that
  `CompactlyGenerated.{u, 0}` retains non-Hausdorff spaces without Hausdorffification.

## Main declarations

* `CompactlyGenerated.equivGeneratedByTopCat`: the isomorphism of categories
  `CompactlyGenerated.{u, w} ≌ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` over `TopCat.{w}`.
* `TopCat.toCompactlyGenerated` and `CompactlyGenerated.adj`: the right adjoint coreflector
  `TopCat.{w} ⥤ CompactlyGenerated.{u, w}` and the coreflection adjunction.
* `CompactlyGenerated.isIso_adjCounit_app_iff` and `CompactlyGenerated.counitHomeomorph`: the counit
  is an isomorphism precisely on `u`-compactly generated spaces.
* `UCompactlyGeneratedSpace.ulift` and `TauCeti.uCompactlyGeneratedSpace_of_relCWComplex`:
  universe-lifting of compact generation and stability under relative CW attachments.
* `TauCeti.isOpen_sierpinski_iff`, `TauCeti.compactlyGenerated_sierpinski`, and
  `TauCeti.not_t2Space_sierpinski`: exact open sets, compact generation, and non-Hausdorffness of
  the Sierpiński space in `CompactlyGenerated`.

## References

* N. E. Steenrod, *A convenient category of topological spaces*, Michigan Math. J. 14 (1967),
  133–152.
* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), Appendix,
  Section "Compactly Generated Spaces".
-/

public section

universe u v w

open CategoryTheory Limits Topology TopologicalSpace

/-! ### Universe lifting and CW-complex instances for `UCompactlyGeneratedSpace` -/

/-- If `X` is `v`-compactly generated, then it is `(max v u)`-compactly generated: every continuous
map from a `v`-small compact Hausdorff space `S` into `X` factors through `ULift.{u} S`. -/
theorem UCompactlyGeneratedSpace.ulift {X : Type w} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{v} X] : UCompactlyGeneratedSpace.{max v u} X := by
  refine uCompactlyGeneratedSpace_of_isClosed fun s h ↦
    UCompactlyGeneratedSpace.isClosed.{v} fun S f ↦ ?_
  exact (h (CompHaus.of (ULift.{u} S))
    (f.comp ⟨ULift.down, continuous_uliftDown⟩)).preimage continuous_uliftUp

/-- A Hausdorff weakly locally compact space `X : Type w` is `(max w u)`-compactly generated for
every universe `u`. -/
theorem UCompactlyGeneratedSpace.of_t2Space_of_weaklyLocallyCompactSpace
    (X : Type w) [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X] :
    UCompactlyGeneratedSpace.{max w u} X :=
  UCompactlyGeneratedSpace.ulift.{u, w} (X := X)

instance : UCompactlyGeneratedSpace.{u} TopCat.I.{w} :=
  inferInstanceAs (UCompactlyGeneratedSpace.{u} (ULift unitInterval))

namespace TauCeti

/-- **A Hausdorff relative CW complex over a `u`-compactly generated base is `u`-compactly
generated**, for every test universe `u`. Every closed cell `closedBall 0 1 ⊆ Fin n → ℝ` is
metrizable, hence sequential and `u`-compactly generated, and `C` is a quotient of the disjoint
union of `D` and the closed cells by `TauCeti.isQuotientMap_sumElim_base_map`. -/
theorem uCompactlyGeneratedSpace_of_relCWComplex {X : Type w} [TopologicalSpace X] [T2Space X]
    {C D : Set X} [RelCWComplex C D] [UCompactlyGeneratedSpace.{u} D] :
    UCompactlyGeneratedSpace.{u} C :=
  (isGeneratedBy_compHaus_iff C).1 isQuotientMap_sumElim_base_map.isGeneratedBy

end TauCeti

/-! ### Comparison with `GeneratedByTopCat` and the coreflection adjunction -/

namespace CompactlyGenerated

/-- Reinterpret an object or morphism of `CompactlyGenerated.{u, w}` in
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`. -/
@[expose, simps]
def toGeneratedByTopCat :
    CompactlyGenerated.{u, w} ⥤ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) where
  obj X := ⟨X.toTop, (isGeneratedBy_compHaus_iff X.toTop).2 X.is_compactly_generated⟩
  map f := ObjectProperty.homMk f.hom

/-- Reinterpret an object or morphism of `GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` in
`CompactlyGenerated.{u, w}`. -/
@[expose, simps]
def fromGeneratedByTopCat :
    GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) ⥤ CompactlyGenerated.{u, w} where
  obj Y :=
    { toTop := Y.obj
      is_compactly_generated := (isGeneratedBy_compHaus_iff Y.obj).1 Y.property }
  map g := InducedCategory.homMk g.hom

@[simp]
theorem toGeneratedByTopCat_comp_fromGeneratedByTopCat :
    toGeneratedByTopCat.{u, w} ⋙ fromGeneratedByTopCat.{u, w} = 𝟭 _ :=
  (rfl)

@[simp]
theorem fromGeneratedByTopCat_comp_toGeneratedByTopCat :
    fromGeneratedByTopCat.{u, w} ⋙ toGeneratedByTopCat.{u, w} = 𝟭 _ :=
  (rfl)

@[simp]
theorem toGeneratedByTopCat_comp_toTopCat :
    toGeneratedByTopCat.{u, w} ⋙ GeneratedByTopCat.toTopCat = compactlyGeneratedToTop.{u, w} :=
  (rfl)

@[simp]
theorem fromGeneratedByTopCat_comp_compactlyGeneratedToTop :
    fromGeneratedByTopCat.{u, w} ⋙ compactlyGeneratedToTop.{u, w} = GeneratedByTopCat.toTopCat :=
  (rfl)

/-- `CompactlyGenerated.{u, w}` is strictly isomorphic to
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`. -/
def equivGeneratedByTopCat :
    CompactlyGenerated.{u, w} ≌ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) where
  functor := toGeneratedByTopCat
  inverse := fromGeneratedByTopCat
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
theorem equivGeneratedByTopCat_functor :
    equivGeneratedByTopCat.{u, w}.functor = toGeneratedByTopCat.{u, w} :=
  (rfl)

@[simp]
theorem equivGeneratedByTopCat_inverse :
    equivGeneratedByTopCat.{u, w}.inverse = fromGeneratedByTopCat.{u, w} :=
  (rfl)

instance : toGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivGeneratedByTopCat.isEquivalence_functor

instance : fromGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivGeneratedByTopCat.isEquivalence_inverse

end CompactlyGenerated

/-- The compact-generation coreflector `TopCat.{w} ⥤ CompactlyGenerated.{u, w}`, refining the
topology of a space `X` to the `u`-compactly generated topology while leaving the underlying type
and functions unchanged. -/
@[expose]
def TopCat.toCompactlyGenerated : TopCat.{w} ⥤ CompactlyGenerated.{u, w} :=
  TopCat.toGeneratedByTopCat (X := fun K : CompHaus.{u} ↦ K) ⋙
    CompactlyGenerated.fromGeneratedByTopCat.{u, w}

namespace TopCat

/-- The canonical bijection between the underlying points of
`TopCat.toCompactlyGenerated.{u, w}.obj X` and `X`. -/
@[expose]
def toCompactlyGeneratedEquiv (X : TopCat.{w}) :
    ↑(TopCat.toCompactlyGenerated.{u, w}.obj X) ≃ X :=
  WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X)

@[simp]
theorem toCompactlyGenerated_map_apply {X Y : TopCat.{w}} (f : X ⟶ Y)
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    toCompactlyGeneratedEquiv.{u, w} Y (TopCat.toCompactlyGenerated.{u, w}.map f x) =
      f (toCompactlyGeneratedEquiv.{u, w} X x) :=
  (rfl)

/-- A subset of `TopCat.toCompactlyGenerated.{u, w}.obj X` is open if and only if its image in `X`
is open in `TopologicalSpace.compactlyGenerated.{u} X`. -/
theorem isOpen_toCompactlyGenerated_iff (X : TopCat.{w})
    (U : Set ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    IsOpen U ↔ IsOpen[TopologicalSpace.compactlyGenerated.{u} X]
      ((toCompactlyGeneratedEquiv.{u, w} X).symm ⁻¹' U) := by
  refine (WithGeneratedByTopology.isOpen_iff
    (X := fun K : CompHaus.{u} ↦ K) (Y := X) (U := U)).trans ?_
  rw [← TopologicalSpace.generatedBy_compHaus, TopologicalSpace.generatedBy]
  simp only [isOpen_iSup_iff, isOpen_coinduced, Set.preimage_preimage]
  rfl

end TopCat

namespace CompactlyGenerated

/-- When `X` is `u`-compactly generated, the counit gives a homeomorphism from
`TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of X)` onto `X`. -/
def counitHomeomorph (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of X)) ≃ₜ X :=
  IsGeneratedBy.homeomorph (X := fun K : CompHaus.{u} ↦ K) (Y := X)

@[simp]
theorem counitHomeomorph_apply {X : Type w} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of X))) :
    counitHomeomorph.{u, w} X x = TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of X) x :=
  (rfl)

@[simp]
theorem counitHomeomorph_symm_apply {X : Type w} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} X] (x : X) :
    (counitHomeomorph.{u, w} X).symm x =
      (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of X)).symm x :=
  (rfl)

/-- The unit isomorphism `𝟭 _ ≅ compactlyGeneratedToTop ⋙ TopCat.toCompactlyGenerated` of the
compact-generation coreflection. -/
def adjUnitIso :
    𝟭 CompactlyGenerated.{u, w} ≅
      compactlyGeneratedToTop.{u, w} ⋙ TopCat.toCompactlyGenerated.{u, w} :=
  NatIso.ofComponents
    (fun X ↦ isoOfHomeo (counitHomeomorph.{u, w} X.toTop).symm)
    (fun _ ↦ by ext; rfl)

/-- The counit `(TopCat.toCompactlyGenerated ⋙ compactlyGeneratedToTop) ⟶ 𝟭 TopCat` of the
compact-generation coreflection. -/
@[expose]
def adjCounit :
    TopCat.toCompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w} ⟶ 𝟭 TopCat.{w} :=
  GeneratedByTopCat.adjCounit (X := fun K : CompHaus.{u} ↦ K)

theorem adjCounit_eq_generatedByTopCat_adjCounit :
    adjCounit.{u, w} = GeneratedByTopCat.adjCounit (X := fun K : CompHaus.{u} ↦ K) :=
  (rfl)

@[simp]
theorem adjCounit_app_apply (X : TopCat.{w})
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    dsimp% adjCounit.{u, w}.app X x = TopCat.toCompactlyGeneratedEquiv.{u, w} X x :=
  (rfl)

@[simp]
theorem adjUnitIso_hom_app_apply (X : CompactlyGenerated.{u, w}) (x : X) :
    dsimp% TopCat.toCompactlyGeneratedEquiv.{u, w} X.toTop ((adjUnitIso.{u, w}.hom.app X) x) = x :=
  (rfl)

@[simp]
theorem adjUnitIso_inv_app_apply (X : CompactlyGenerated.{u, w})
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X.toTop)) :
    dsimp% (adjUnitIso.{u, w}.inv.app X) x = TopCat.toCompactlyGeneratedEquiv.{u, w} X.toTop x :=
  (rfl)

/-- **The compact-generation coreflection**: the inclusion
`compactlyGeneratedToTop : CompactlyGenerated.{u, w} ⥤ TopCat.{w}` is left adjoint to
`TopCat.toCompactlyGenerated : TopCat.{w} ⥤ CompactlyGenerated.{u, w}`. -/
def adj : compactlyGeneratedToTop.{u, w} ⊣ TopCat.toCompactlyGenerated.{u, w} where
  unit := adjUnitIso.hom
  counit := adjCounit
  left_triangle_components X := by
    ext x
    exact (rfl)
  right_triangle_components X := by
    ext x
    exact (rfl)

@[simp]
theorem adj_unit : adj.{u, w}.unit = adjUnitIso.{u, w}.hom :=
  (rfl)

@[simp]
theorem adj_counit : adj.{u, w}.counit = adjCounit.{u, w} :=
  (rfl)

instance : IsIso adj.{u, w}.unit :=
  inferInstanceAs (IsIso adjUnitIso.{u, w}.hom)

instance : compactlyGeneratedToTop.{u, w}.IsLeftAdjoint :=
  adj.isLeftAdjoint

instance : TopCat.toCompactlyGenerated.{u, w}.IsRightAdjoint :=
  adj.isRightAdjoint

instance : TopCat.toCompactlyGenerated.{u, w}.Faithful where
  map_injective {X Y} {f g} h := by
    ext x
    exact congr($(h) ((TopCat.toCompactlyGeneratedEquiv.{u, w} X).symm x))

/-- `CompactlyGenerated.{u, w}` is a coreflective subcategory of `TopCat.{w}`. -/
instance instCoreflectiveCompactlyGeneratedToTop :
    Coreflective compactlyGeneratedToTop.{u, w} where
  R := TopCat.toCompactlyGenerated
  adj := adj

noncomputable instance instCreatesColimitsCompactlyGeneratedToTop :
    CreatesColimits compactlyGeneratedToTop.{u, w} :=
  comonadicCreatesColimits _

instance : HasLimits CompactlyGenerated.{u, w} :=
  hasLimits_of_coreflective compactlyGeneratedToTop

instance : HasColimits CompactlyGenerated.{u, w} :=
  hasColimits_of_hasColimits_createsColimits compactlyGeneratedToTop

instance (X : TopCat.{w}) :
    IsIso (TopCat.toCompactlyGenerated.{u, w}.map (adjCounit.{u, w}.app X)) :=
  inferInstanceAs (IsIso (TopCat.toCompactlyGenerated.map (adj.counit.app X)))

/-! ### Characterization and specializations of the counit isomorphism -/

/-- If `X` is `u`-compactly generated, the counit `adjCounit.app X` is an isomorphism in
`TopCat.{w}`. -/
instance isIso_adjCounit_app (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    IsIso (adjCounit.{u, w}.app X) := by
  change IsIso (TopCat.isoOfHomeo (counitHomeomorph.{u, w} X)).hom
  infer_instance

/-- **Characterization of the coreflection counit**: the counit `(k X).toTop ⟶ X` is an
isomorphism in `TopCat.{w}` if and only if `X` is already `u`-compactly generated. -/
theorem isIso_adjCounit_app_iff (X : TopCat.{w}) :
    IsIso (adjCounit.{u, w}.app X) ↔ UCompactlyGeneratedSpace.{u} X := by
  refine ⟨fun h ↦ ?_, fun _ ↦ inferInstance⟩
  have hquot : IsQuotientMap (adjCounit.{u, w}.app X) :=
    (TopCat.homeoOfIso (asIso (adjCounit.{u, w}.app X))).isQuotientMap
  have : UCompactlyGeneratedSpace.{u}
      ((TopCat.toCompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w}).obj X) :=
    (TopCat.toCompactlyGenerated.{u, w}.obj X).is_compactly_generated
  exact uCompactlyGeneratedSpace_of_coinduced hquot.continuous hquot.eq_coinduced

/-- For a Hausdorff CW complex `C` in any ambient space `X : Type w`, the compact-generation
counit at `TopCat.of C` is an isomorphism for every test universe `u`. -/
theorem isIso_adjCounit_of_cwComplex {X : Type w} [TopologicalSpace X] [T2Space X]
    (C : Set X) [CWComplex C] :
    IsIso (adjCounit.{u, w}.app (TopCat.of C)) :=
  inferInstance

/-- For a Hausdorff space `X : Type w` carrying a CW structure on `Set.univ`, the
compact-generation counit at `TopCat.of X` is an isomorphism for every test universe `u`. -/
theorem isIso_adjCounit_of_cwComplex_univ (X : Type w) [TopologicalSpace X] [T2Space X]
    [CWComplex (Set.univ : Set X)] :
    IsIso (adjCounit.{u, w}.app (TopCat.of X)) :=
  inferInstance

/-- For a Hausdorff weakly locally compact space `X : Type w`, the compact-generation counit for
test universe `max w u` is an isomorphism. -/
theorem isIso_adjCounit_of_t2Space_of_weaklyLocallyCompactSpace (X : TopCat.{w})
    [T2Space X] [WeaklyLocallyCompactSpace X] :
    IsIso (adjCounit.{max w u, w}.app X) := by
  have : UCompactlyGeneratedSpace.{max w u} X :=
    UCompactlyGeneratedSpace.of_t2Space_of_weaklyLocallyCompactSpace X
  infer_instance

/-! ### Concrete checks: point, empty space, unit interval, and Sierpiński space -/

/-- The empty space `PEmpty` is initial in `CompactlyGenerated.{u, w}`. -/
def isInitialPEmpty : IsInitial (of.{u, w} PEmpty.{w + 1}) :=
  IsInitial.ofUniqueHom
    (fun _ ↦ ofHom ⟨PEmpty.elim, continuous_of_discreteTopology⟩)
    (fun _ _ ↦ by ext x; exact x.elim)

/-- Applying `TopCat.toCompactlyGenerated` to `TopCat.of PEmpty` yields an empty space, distinct
from the inhabited one-point space `of PUnit`. -/
instance isEmpty_toCompactlyGenerated_pEmpty :
    IsEmpty ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of PEmpty.{w + 1})) :=
  (TopCat.toCompactlyGeneratedEquiv.{u, w} (TopCat.of PEmpty.{w + 1})).isEmpty

/-- The one-point space `PUnit` is fixed up to canonical isomorphism by
`TopCat.toCompactlyGenerated`. -/
def toCompactlyGeneratedPUnitIso :
    TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of PUnit.{w + 1}) ≅ of.{u, w} PUnit.{w + 1} :=
  (adjUnitIso.{u, w}.app (of.{u, w} PUnit.{w + 1})).symm

/-- The unit interval `TopCat.I` is fixed up to canonical isomorphism by
`TopCat.toCompactlyGenerated`. -/
def toCompactlyGeneratedUnitIntervalIso :
    TopCat.toCompactlyGenerated.{u, w}.obj TopCat.I.{w} ≅ of.{u, w} TopCat.I.{w} :=
  (adjUnitIso.{u, w}.app (of.{u, w} TopCat.I.{w})).symm

@[simp]
theorem toCompactlyGeneratedUnitIntervalIso_hom_apply
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj TopCat.I.{w})) :
    toCompactlyGeneratedUnitIntervalIso.{u, w}.hom x =
      TopCat.toCompactlyGeneratedEquiv.{u, w} TopCat.I.{w} x :=
  (rfl)

@[simp]
theorem toCompactlyGeneratedUnitIntervalIso_inv_apply (x : TopCat.I.{w}) :
    toCompactlyGeneratedUnitIntervalIso.{u, w}.inv x =
      (TopCat.toCompactlyGeneratedEquiv.{u, w} TopCat.I.{w}).symm x :=
  (rfl)

end CompactlyGenerated

namespace TopCat

instance instNontrivialToCompactlyGenerated (X : TopCat.{w}) [Nontrivial X] :
    Nontrivial ↑(TopCat.toCompactlyGenerated.{u, w}.obj X) :=
  (TopCat.toCompactlyGeneratedEquiv.{u, w} X).nontrivial

instance : Nontrivial TopCat.I.{w} :=
  TopCat.I.homeomorph.toEquiv.nontrivial

@[simp]
theorem I.zero_ne_one : (0 : TopCat.I.{w}) ≠ 1 := by
  intro h
  have h01 : (0 : unitInterval) = 1 := by
    simpa using congrArg TopCat.I.homeomorph h
  exact _root_.zero_ne_one (congrArg Subtype.val h01)

end TopCat

namespace TauCeti

/-- **Exact open sets of the Sierpiński space `Prop`**: a subset of `Prop` is open in
`sierpinskiSpace` if and only if it is `∅`, `{True}`, or `Set.univ`. -/
theorem isOpen_sierpinski_iff {s : Set Prop} :
    IsOpen s ↔ s = ∅ ∨ s = {True} ∨ s = Set.univ := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · by_cases hF : False ∈ s
    · exact Or.inr (Or.inr (Filter.mem_top.1 (nhds_false ▸ hs.mem_nhds hF)))
    · by_cases hT : True ∈ s
      · right; left
        ext p
        simp only [Set.mem_singleton_iff]
        exact ⟨fun hp ↦ by by_cases hp' : p <;> simp_all, fun hp ↦ hp ▸ hT⟩
      · left
        ext p
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hp
        by_cases hp' : p <;> simp_all
  · rintro (rfl | rfl | rfl)
    · exact isOpen_empty
    · exact isOpen_singleton_true
    · exact isOpen_univ

/-- The Sierpiński space `Prop` is already `u`-compactly generated for every universe `u`, so its
compactly generated refinement equals `sierpinskiSpace`. -/
theorem compactlyGenerated_sierpinski :
    TopologicalSpace.compactlyGenerated.{u} Prop = sierpinskiSpace :=
  (eq_compactlyGenerated.{u} (X := Prop)).symm

/-- The Sierpiński object `CompactlyGenerated.of.{u, 0} Prop` is not Hausdorff (`¬ T2Space`),
confirming that `CompactlyGenerated` performs genuine compact generation without
Hausdorffification. -/
theorem not_t2Space_sierpinski : ¬ T2Space (CompactlyGenerated.of.{u, 0} Prop) := by
  intro h
  obtain ⟨U, V, _, hVo, hTU, hFV, hUV⟩ := h.t2 (by simp : (True : Prop) ≠ False)
  have hVuniv : V = Set.univ := Filter.mem_top.1 (nhds_false ▸ hVo.mem_nhds hFV)
  exact hUV.notMem_of_mem_left hTU (hVuniv ▸ Set.mem_univ True)

end TauCeti

end
