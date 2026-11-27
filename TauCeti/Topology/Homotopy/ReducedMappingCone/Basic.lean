/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import TauCeti.Topology.Category.BasedTopologicalSpace.ReducedSuspension
public import TauCeti.Topology.Convenient.CompactlyGenerated
public import TauCeti.Topology.Homotopy.MappingCylinder

/-!
# The reduced mapping cone of a based map

For a based map `f : X ⟶ Y`, the reduced mapping cone attaches the cylinder `I × X`
to `Y` by `(0, x) ∼ f x` and collapses its other end and the segment over the basepoint.
It is built from `TauCeti.MappingCylinder` and `TopPair.ordinaryPairQuotient`.
The cone parameter runs from the attached end to the apex, the reverse of the parameter
in the mapping cylinder. The construction takes compactly generated spaces to
compactly generated spaces.

A based map out of the cone specifies a based map on `Y` and a pointed nullhomotopy
of its composite with `f`. In particular a based map on `Y` extends over the cone
exactly when this composite is pointed-nullhomotopic. Collapsing the image of `Y`
gives the reduced suspension of `X` via the map taking each cone line to its increasing
meridian. Both the inclusion and the collapse are natural in commutative squares of based maps.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (mapping cones) and §4.3 (the cofiber sequence).
-/

public section

noncomputable section

universe u v

open CategoryTheory Topology
open scoped unitInterval

namespace TauCeti.BasedTopologicalSpace

variable {X Y Z : BasedTopologicalSpace.{u}} (f : Hom X Y)

private abbrev conePair : TopPair.{u} :=
  TopPair.ofSubset (X := _root_.TopCat.of (MappingCylinder f.toContinuousMap))
    (Set.range (MappingCylinder.incl f.toContinuousMap) ∪
      Set.range fun t : I ↦ MappingCylinder.mkCyl f.toContinuousMap (t, X.basepoint))

/-- The **reduced mapping cone** of a based map, based at the collapsed end of its cylinder. -/
def reducedMappingCone : BasedTopologicalSpace.{u} :=
  ⟨(conePair f).ordinaryPairQuotient, (conePair f).ordinaryPairQuotientBasepoint⟩

namespace reducedMappingCone

private abbrev π := (conePair f).ordinaryPairQuotientπ

private theorem isQuotientMap_π : IsQuotientMap (π f) := by
  let : Nonempty (conePair f).snd :=
    ⟨⟨MappingCylinder.incl f.toContinuousMap X.basepoint, Or.inl ⟨_, rfl⟩⟩⟩
  exact (conePair f).isQuotientMap_ordinaryPairQuotientπ

/-- The reduced mapping cone is compactly generated whenever its source and target are. -/
instance [UCompactlyGeneratedSpace.{v} X.carrier] [UCompactlyGeneratedSpace.{v} Y.carrier] :
    UCompactlyGeneratedSpace.{v} (reducedMappingCone f).carrier := by
  have h := (isQuotientMap_π f).comp
    (MappingCylinder.isQuotientMap_sumElim_mkCyl_mkBase (f := f.toContinuousMap))
  exact uCompactlyGeneratedSpace_of_coinduced h.continuous h.eq_coinduced

private lemma π_spine (t : I) :
    π f (MappingCylinder.mkCyl f.toContinuousMap (t, X.basepoint)) =
      (reducedMappingCone f).basepoint :=
  (conePair f).ordinaryPairQuotientπ_map ⟨_, Or.inr ⟨t, rfl⟩⟩

/-- The inclusion of the target into the reduced mapping cone. -/
def incl : Hom Y (reducedMappingCone f) where
  toContinuousMap := (π f).hom.comp (MappingCylinder.mkBase f.toContinuousMap)
  map_basepoint := by
    have h := π_spine f 1
    rw [MappingCylinder.mkCyl_one, f.map_basepoint] at h
    exact h

/-- The cone lines, parameterized from their attaching points at time zero to the apex at one. -/
def line : C(I × X.carrier, (reducedMappingCone f).carrier) :=
  (π f).hom.comp ((MappingCylinder.mkCyl f.toContinuousMap).comp
    ⟨fun p ↦ (σ p.1, p.2), by fun_prop⟩)

private lemma line_apply (p : I × X.carrier) :
    line f p = π f (MappingCylinder.mkCyl f.toContinuousMap (σ p.1, p.2)) := (rfl)

private lemma incl_apply (y : Y.carrier) :
    incl f y = π f (MappingCylinder.mkBase f.toContinuousMap y) := (rfl)

/-- Distinct points of the target remain distinct in the reduced mapping cone. -/
theorem incl_injective : Function.Injective (incl f) := by
  have hbase (y : Y.carrier) (hy : MappingCylinder.mkBase f.toContinuousMap y ∈
      Set.range (conePair f).map) : y = Y.basepoint := by
    rw [TopPair.range_ofSubset_map] at hy
    obtain hy | ⟨t, ht⟩ := hy
    · exact (MappingCylinder.mkBase_notMem_range_incl y hy).elim
    · exact (MappingCylinder.mkCyl_eq_mkBase_iff.1 ht).2.symm.trans f.map_basepoint
  intro y y' he
  rw [incl_apply, incl_apply] at he
  obtain h | ⟨hy, hy'⟩ := ((conePair f).ordinaryPairQuotientπ_eq_iff _ _).1 he
  · exact MappingCylinder.mkBase_injective h
  · exact (hbase y hy).trans (hbase y' hy').symm

@[simp]
theorem line_zero (x : X.carrier) : line f (0, x) = incl f (f x) := by
  rw [line_apply, incl_apply, unitInterval.symm_zero, MappingCylinder.mkCyl_one]
  rfl

@[simp]
theorem line_one (x : X.carrier) : line f (1, x) = (reducedMappingCone f).basepoint := by
  rw [line_apply, unitInterval.symm_one, ← MappingCylinder.incl_apply]
  exact (conePair f).ordinaryPairQuotientπ_map ⟨_, Or.inl ⟨x, rfl⟩⟩

@[simp]
theorem line_basepoint (t : I) : line f (t, X.basepoint) = (reducedMappingCone f).basepoint :=
  π_spine f (σ t)

/-- Every point is on the target or on a cone line. -/
@[elab_as_elim]
theorem ind {P : (reducedMappingCone f).carrier → Prop}
    (target : ∀ y, P (incl f y)) (cone : ∀ p, P (line f p)) (z) : P z := by
  obtain ⟨m, rfl⟩ := (isQuotientMap_π f).surjective z
  induction m using MappingCylinder.ind with
  | base y => exact target y
  | cyl p => simpa only [line_apply, unitInterval.symm_symm] using cone (σ p.1, p.2)

/-- Two based maps out of the cone agree if they agree on the target and the cone lines. -/
@[ext]
theorem hom_ext {g h : Hom (reducedMappingCone f) Z} (target : ∀ y, g (incl f y) = h (incl f y))
    (cone : ∀ p, g (line f p) = h (line f p)) : g = h :=
  DFunLike.ext _ _ (ind f target cone)

section Extension

variable (g : Hom Y Z)
  (H : (g.toContinuousMap.comp f.toContinuousMap).HomotopyRel
    (.const _ Z.basepoint) {X.basepoint})

private def cylinderDesc : C(MappingCylinder f.toContinuousMap, Z.carrier) :=
  MappingCylinder.lift H.symm.toHomotopy.toContinuousMap g.toContinuousMap
    fun x ↦ H.symm.apply_one x

private lemma cylinderDesc_locus (b : (conePair f).snd) :
    cylinderDesc f g H ((conePair f).map b) = Z.basepoint := by
  obtain ⟨m, hm⟩ := b
  -- The embedding of the subset pair is the subtype inclusion.
  change cylinderDesc f g H m = Z.basepoint
  rcases hm with ⟨x, rfl⟩ | ⟨t, rfl⟩
  · rw [cylinderDesc, MappingCylinder.incl_apply, MappingCylinder.lift_mkCyl]
    exact H.symm.apply_zero x
  · rw [cylinderDesc, MappingCylinder.lift_mkCyl]
    exact H.symm.eq_fst t (Set.mem_singleton _)

/-- Extend a based map across the cone using a specified pointed nullhomotopy on the source. -/
def desc : Hom (reducedMappingCone f) Z where
  toContinuousMap := ((conePair f).ordinaryPairQuotientDesc
    (_root_.TopCat.ofHom (cylinderDesc f g H)) Z.basepoint (cylinderDesc_locus f g H)).hom
  map_basepoint := (conePair f).ordinaryPairQuotientDesc_basepoint _ _ _

private lemma desc_π (m : MappingCylinder f.toContinuousMap) :
    desc f g H (π f m) = cylinderDesc f g H m :=
  ConcreteCategory.congr_hom ((conePair f).ordinaryPairQuotientπ_desc _ _ _) m

@[simp]
theorem desc_incl (y : Y.carrier) : desc f g H (incl f y) = g y := by
  rw [incl_apply, desc_π]
  exact MappingCylinder.lift_mkBase _ _

@[simp]
theorem desc_line (p : I × X.carrier) : desc f g H (line f p) = H p := by
  rw [line_apply, desc_π, cylinderDesc, MappingCylinder.lift_mkCyl]
  exact congrArg H (Prod.ext (unitInterval.symm_symm _) rfl)

/-- Restricting a based map out of the cone to its lines gives a pointed nullhomotopy of its
restriction along `X → Y → C_f`. -/
def nullhomotopy (h : Hom (reducedMappingCone f) Z) :
    ((h.comp (incl f)).toContinuousMap.comp f.toContinuousMap).HomotopyRel
      (.const _ Z.basepoint) {X.basepoint} where
  toContinuousMap := h.toContinuousMap.comp (line f)
  map_zero_left x := by simp
  map_one_left x := by simp
  prop' t := by rintro x rfl; simp

@[simp]
theorem nullhomotopy_apply (h : Hom (reducedMappingCone f) Z) (p : I × X.carrier) :
    nullhomotopy f h p = h (line f p) := (rfl)

/-- A based map extends across the reduced mapping cone exactly when it is pointed-nullhomotopic
after precomposition with the attaching map. -/
theorem exists_extension_iff :
    (∃ h : Hom (reducedMappingCone f) Z, h.comp (incl f) = g) ↔
      (g.toContinuousMap.comp f.toContinuousMap).HomotopicRel
        (.const _ Z.basepoint) {X.basepoint} := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨nullhomotopy f h⟩
  · rintro ⟨K⟩
    exact ⟨desc f g K, DFunLike.ext _ _ fun y ↦ (Hom.comp_apply _ _ y).trans (desc_incl f g K y)⟩

end Extension

/-- The collapse `C_f → ΣX` sends the whole target to the suspension basepoint and a cone
line to the increasing meridian. -/
def collapse : Hom (reducedMappingCone f) (reducedSuspension.obj X) :=
  desc f ⟨.const _ ReducedSuspension.basepoint, rfl⟩
    { toContinuousMap := ReducedSuspension.mk.comp ⟨Prod.swap, continuous_swap⟩
      map_zero_left := ReducedSuspension.mk_zero
      map_one_left := ReducedSuspension.mk_one
      prop' := fun t x hx ↦ by
        obtain rfl := Set.mem_singleton_iff.1 hx
        exact ReducedSuspension.mk_basepoint t }

@[simp]
theorem collapse_incl (y : Y.carrier) :
    collapse f (incl f y) = (reducedSuspension.obj X).basepoint :=
  desc_incl _ _ _ y

@[simp]
theorem collapse_line (p : I × X.carrier) :
    collapse f (line f p) = ReducedSuspension.mk (p.2, p.1) :=
  desc_line _ _ _ p

/-- The collapse is a quotient map, with the quotient topology even for non-Hausdorff spaces. -/
theorem isQuotientMap_collapse : IsQuotientMap (collapse f) := by
  apply IsQuotientMap.of_comp (line f).continuous (collapse f).toContinuousMap.continuous
  have h : collapse f ∘ line f = ReducedSuspension.mk ∘ Prod.swap := funext (collapse_line f)
  rw [Hom.coe_toContinuousMap, h]
  exact ReducedSuspension.isQuotientMap_mk.comp (Homeomorph.prodComm _ _).isQuotientMap

/-- The fibre over the suspension basepoint is exactly the image of the target. -/
theorem collapse_eq_basepoint_iff (z : (reducedMappingCone f).carrier) :
    collapse f z = (reducedSuspension.obj X).basepoint ↔ z ∈ Set.range (incl f) := by
  refine ⟨?_, fun ⟨y, hy⟩ ↦ hy ▸ collapse_incl f y⟩
  induction z using ind f with
  | target y => exact fun _ ↦ Set.mem_range_self y
  | cone p =>
    rintro h
    obtain ⟨t, x⟩ := p
    rw [collapse_line, reducedSuspension_obj_basepoint, ReducedSuspension.mk_eq_basepoint_iff,
      mem_reducedSuspensionLocus] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨_, (incl f).map_basepoint.trans (line_basepoint f t).symm⟩
    · exact ⟨_, (line_zero f x).symm⟩
    · exact ⟨_, (incl f).map_basepoint.trans (line_one f x).symm⟩

/-- Away from the target the collapse is injective. -/
theorem eq_of_collapse_eq {z w : (reducedMappingCone f).carrier}
    (hz : z ∉ Set.range (incl f)) (h : collapse f z = collapse f w) : z = w := by
  induction z using ind f with
  | target y => exact (hz ⟨y, rfl⟩).elim
  | cone p =>
    induction w using ind f with
    | target y => exact (hz ((collapse_eq_basepoint_iff f _).1 (h.trans (collapse_incl f y)))).elim
    | cone q =>
      rw [collapse_line, collapse_line, ReducedSuspension.mk_eq_mk_iff] at h
      obtain he | ⟨hp, _⟩ := h
      · exact congrArg (line f) (congrArg Prod.swap he)
      · exact (hz ((collapse_eq_basepoint_iff f _).1
          ((collapse_line f p).trans (ReducedSuspension.mk_eq_basepoint hp)))).elim

/-- The pair consisting of the reduced mapping cone and the image of the target. -/
abbrev targetPair : TopPair.{u} :=
  TopPair.ofSubset (X := _root_.TopCat.of (reducedMappingCone f).carrier) (Set.range (incl f))

/-- Collapsing the target of the reduced mapping cone gives the reduced suspension of the source.
The homeomorphism uses the same increasing interval parameter on both sides. -/
def quotientTargetHomeomorph :
    (targetPair f).ordinaryPairQuotient ≃ₜ ReducedSuspension X.carrier X.basepoint := by
  let c := _root_.TopCat.ofHom (collapse f).toContinuousMap
  have hbase (z) : c z = ReducedSuspension.basepoint ↔ z ∈ Set.range (targetPair f).map :=
    (collapse_eq_basepoint_iff f z).trans (by rw [TopPair.range_ofSubset_map]; rfl)
  let d := (targetPair f).ordinaryPairQuotientDesc c ReducedSuspension.basepoint
    fun b ↦ (hbase _).2 ⟨b, rfl⟩
  have hd : Function.Bijective d := (targetPair f).ordinaryPairQuotientDesc_bijective c _
    hbase (fun z w hz h ↦ eq_of_collapse_eq f (by rwa [TopPair.range_ofSubset_map] at hz) h)
    fun z _ ↦ (isQuotientMap_collapse f).surjective z
  have hq : IsQuotientMap d := by
    apply IsQuotientMap.of_comp (targetPair f).ordinaryPairQuotientπ.hom.continuous d.hom.continuous
    have he : d ∘ (targetPair f).ordinaryPairQuotientπ = collapse f :=
      funext ((targetPair f).ordinaryPairQuotientπ_desc_apply _ _ _)
    rw [he]
    exact isQuotientMap_collapse f
  exact (isHomeomorph_iff_isQuotientMap_injective.2 ⟨hq, hd.1⟩).homeomorph d

@[simp]
theorem quotientTargetHomeomorph_π (z : (reducedMappingCone f).carrier) :
    quotientTargetHomeomorph f ((targetPair f).ordinaryPairQuotientπ z) = collapse f z :=
  (targetPair f).ordinaryPairQuotientπ_desc_apply _ _ _ z

@[simp]
theorem quotientTargetHomeomorph_basepoint :
    quotientTargetHomeomorph f (targetPair f).ordinaryPairQuotientBasepoint =
      ReducedSuspension.basepoint :=
  (targetPair f).ordinaryPairQuotientDesc_basepoint _ _ _

@[simp]
theorem quotientTargetHomeomorph_symm_mk (p : X.carrier × I) :
    (quotientTargetHomeomorph f).symm (ReducedSuspension.mk p) =
      (targetPair f).ordinaryPairQuotientπ (line f (p.2, p.1)) :=
  (quotientTargetHomeomorph f).symm_apply_eq.mpr (by simp)

@[simp]
theorem quotientTargetHomeomorph_symm_basepoint :
    (quotientTargetHomeomorph f).symm ReducedSuspension.basepoint =
      (targetPair f).ordinaryPairQuotientBasepoint :=
  (quotientTargetHomeomorph f).symm_apply_eq.mpr (quotientTargetHomeomorph_basepoint f).symm

section Functor

variable {a b : Arrow BasedTopologicalSpace.{u}} (s : a ⟶ b)

/-- A commutative square of based maps induces a map of their reduced mapping cones. -/
def map : Hom (reducedMappingCone a.hom) (reducedMappingCone b.hom) :=
  desc a.hom ((incl b.hom).comp s.right)
    { toContinuousMap := (line b.hom).comp ((ContinuousMap.id I).prodMap s.left.toContinuousMap)
      map_zero_left := fun x ↦ by
        refine (line_zero b.hom _).trans ?_
        simpa only [comp_eq_hom_comp, Hom.toContinuousMap_comp, ContinuousMap.comp_apply,
          Hom.coe_toContinuousMap, Hom.comp_apply] using
          congrArg (incl b.hom) (DFunLike.congr_fun (F := Hom a.left b.right) (Arrow.w s) x)
      map_one_left := fun x ↦ line_one b.hom (DFunLike.coe (F := Hom a.left b.left) s.left x)
      prop' := fun t x hx ↦ by
        obtain rfl := Set.mem_singleton_iff.1 hx
        simp [Hom.toContinuousMap_comp] }

@[simp]
theorem map_incl (y : a.right.carrier) :
    map s (incl a.hom y) = incl b.hom (DFunLike.coe (F := Hom a.right b.right) s.right y) :=
  (desc_incl _ _ _ y).trans (Hom.comp_apply _ _ _)

@[simp]
theorem map_line (p : I × a.left.carrier) :
    map s (line a.hom p) = line b.hom (p.1, DFunLike.coe (F := Hom a.left b.left) s.left p.2) :=
  desc_line _ _ _ p

/-- The reduced mapping cone as a functor on arrows of based spaces. -/
@[expose, implicit_reducible, simps obj map]
def functor : Arrow BasedTopologicalSpace.{u} ⥤ BasedTopologicalSpace.{u} where
  obj a := reducedMappingCone a.hom
  map s := map s
  map_id a := hom_ext a.hom (fun y ↦ by simp) fun p ↦ by simp
  map_comp s t := hom_ext _ (fun y ↦ by simp) fun p ↦ by simp

/-- Inclusion of the target is natural in the attaching map. -/
def inclNatTrans : Arrow.rightFunc ⟶ functor.{u} where
  app a := incl a.hom
  naturality a b s := Hom.ext <| ContinuousMap.ext fun y ↦ by
    simp [comp_eq_hom_comp, Hom.toContinuousMap_comp]

@[simp]
theorem inclNatTrans_app (a : Arrow BasedTopologicalSpace.{u}) :
    inclNatTrans.app a = incl a.hom := (rfl)

/-- Collapse to the suspension of the source is natural in the attaching map. -/
def collapseNatTrans : functor.{u} ⟶ Arrow.leftFunc ⋙ reducedSuspension where
  app a := collapse a.hom
  naturality a b s := by
    apply hom_ext a.hom
    · intro y
      simp only [Functor.comp_obj, Arrow.leftFunc_obj, functor_obj, functor_map, comp_eq_hom_comp,
        Hom.comp_apply, map_incl, collapse_incl, Functor.comp_map, Arrow.leftFunc_map]
      exact (reducedSuspension.map s.left).map_basepoint.symm
    · intro p
      simp only [Functor.comp_obj, Arrow.leftFunc_obj, functor_obj, functor_map, comp_eq_hom_comp,
        Hom.comp_apply, map_line, collapse_line, Functor.comp_map, Arrow.leftFunc_map]
      exact (reducedSuspension_map_apply_mk s.left (p.2, p.1)).symm

@[simp]
theorem collapseNatTrans_app (a : Arrow BasedTopologicalSpace.{u}) :
    collapseNatTrans.app a = collapse a.hom := (rfl)

end Functor

end reducedMappingCone

end TauCeti.BasedTopologicalSpace
