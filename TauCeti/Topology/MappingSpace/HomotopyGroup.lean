/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Section
public import TauCeti.Topology.MappingSpace.Based
public import TauCeti.Topology.MappingSpace.Evaluation

/-!
# Homotopy groups of mapping spaces with fibrant evaluation

Let `B` be a space with a point `b`, and suppose that evaluation `Map(B, Q) → Q` at `b` is a Serre
fibration, as it is when `b` is a cofibrant point of a locally compact space
(`TauCeti.HasHomotopyExtensionProperty.isHurewiczFibration_mappingSpaceEval`). Its fibre over `x` is
the space `Map_*(B, Q)` of based maps sending `b` to `x`, and the constant maps are a section. So
the boundary maps of its exact homotopy sequence vanish
(`TauCeti.TopCat.fibrationBoundary_eq_of_section`), and at the constant map at `x`:

* the based maps inject into all maps on positive-dimensional homotopy groups
  (`TauCeti.injective_homotopyGroupMap_basedMap_val`);
* the image is the kernel of evaluation
  (`TauCeti.mem_range_homotopyGroupMap_basedMap_val_iff`);
* evaluation is split by the constant maps
  (`TauCeti.mapHom_mappingSpaceEval_comp_mapHom_const`), with no fibration hypothesis.

Composed with any identification `e` of the homotopy groups of the based maps with a group `G`, the
inclusion gives `TauCeti.basedMapHomotopyGroupHom e : G →* π_N(Map(B, Q))`, injective with image
the kernel of evaluation (`TauCeti.injective_basedMapHomotopyGroupHom`,
`TauCeti.range_basedMapHomotopyGroupHom`).

For maps out of a circle or a sphere, the based maps are an iterated loop space, and taking `e` to
be the loop-space shift gives the split short exact sequences
`1 → π_{m+1+k}(Q) → π_{m+1}(Map(Sᵏ, Q)) → π_{m+1}(Q) → 1` of
`TauCeti.AlgebraicTopology.Homotopy.LoopSpace.FreeLoop` and
`TauCeti.AlgebraicTopology.Homotopy.LoopSpace.SphereMap`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I and IV.8.
* A. Hatcher, *Algebraic Topology*, Section 4.2, the long exact sequence of a fibration.
-/

public section

noncomputable section

open CategoryTheory

universe u v

namespace TauCeti

variable {B : Type v} [TopologicalSpace B] (b : B) {Q : Type max v u} [TopologicalSpace Q]
  (x : Q) {N : Type*}

/-! ### The evaluation fibration as a morphism of `TopCat` -/

/-- Evaluation at `b`, as a morphism of topological spaces. -/
private abbrev mappingSpaceEvalHom : _root_.TopCat.of C(B, Q) ⟶ _root_.TopCat.of Q :=
  _root_.TopCat.ofHom (mappingSpaceEval b)

/-- The constant map at `x`, as a point of the fibre of evaluation over `x`. -/
private def mappingSpaceEvalFiberConst : (mappingSpaceEvalHom b (Q := Q)).fiber x :=
  ⟨ContinuousMap.const B x, by simp⟩

/-- The constant maps are a section of evaluation. -/
private theorem const_comp_mappingSpaceEvalHom :
    _root_.TopCat.ofHom ContinuousMap.const' ≫ mappingSpaceEvalHom b (Q := Q) = 𝟙 _ := by
  ext q
  simp

/-- The fibre of evaluation over `x` is the space of based maps sending `b` to `x`. -/
private def mappingSpaceEvalFiberHomeomorph :
    (mappingSpaceEvalHom b (Q := Q)).fiber x ≃ₜ BasedMap B Q b x :=
  Homeomorph.setCongr (t := {f : C(B, Q) | f b = x}) (by ext; simp [mappingSpaceEval_apply])

private theorem mappingSpaceEvalFiberHomeomorph_mappingSpaceEvalFiberConst :
    mappingSpaceEvalFiberHomeomorph b x (mappingSpaceEvalFiberConst b x) =
      ⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩ :=
  Subtype.ext rfl

/-- Pushed into all maps, the based maps give the fibre inclusion. -/
private theorem subtypeVal_comp_mappingSpaceEvalFiberHomeomorph :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(BasedMap B Q b x, C(B, Q))).comp
      ⟨mappingSpaceEvalFiberHomeomorph b x, (mappingSpaceEvalFiberHomeomorph b x).continuous⟩ =
      ((mappingSpaceEvalHom b (Q := Q)).fiberι x).hom :=
  ContinuousMap.ext fun f ↦ (TopCat.Hom.fiberι_apply _ _ f).symm

/-- On homotopy groups, the inclusion of the based maps is the fibre inclusion of evaluation, up to
the identification of the fibre with the based maps. -/
private theorem homotopyGroupMap_basedMap_val_eq :
    HomotopyGroup.map (N := N)
        (x := (⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩ : BasedMap B Q b x))
        ⟨Subtype.val, continuous_subtype_val⟩ rfl =
      HomotopyGroup.map ((mappingSpaceEvalHom b (Q := Q)).fiberι x).hom
          (TopCat.Hom.fiberι_apply _ _ (mappingSpaceEvalFiberConst b x)) ∘
        (HomotopyGroup.homeomorphEquivOfEq (mappingSpaceEvalFiberHomeomorph b x)
          (mappingSpaceEvalFiberHomeomorph_mappingSpaceEvalFiberConst b x)).symm := by
  funext a
  obtain ⟨a, rfl⟩ := (HomotopyGroup.homeomorphEquivOfEq (mappingSpaceEvalFiberHomeomorph b x)
    (mappingSpaceEvalFiberHomeomorph_mappingSpaceEvalFiberConst b x)).surjective a
  rw [Function.comp_apply, Equiv.symm_apply_apply, HomotopyGroup.homeomorphEquivOfEq_apply,
    HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr (subtypeVal_comp_mappingSpaceEvalFiberHomeomorph b x) _ _ a

/-! ### Based maps in all maps -/

variable {b}

/-- **The based maps inject into all maps on homotopy groups.** If evaluation `Map(B, Q) → Q` at
`b` is a Serre fibration then, in positive dimension, the inclusion `Map_*(B, Q) → Map(B, Q)` of
the maps sending `b` to `x` induces an injection on homotopy groups at the constant map: evaluation
has the constant maps as a section, so the boundary maps of its exact homotopy sequence vanish. -/
theorem injective_homotopyGroupMap_basedMap_val
    (hev : TopCat.serreFibrations (_root_.TopCat.ofHom (mappingSpaceEval (X := Q) b)))
    [Finite N] [Nonempty N] :
    Function.Injective (HomotopyGroup.map (N := N)
      (x := (⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩ : BasedMap B Q b x))
      ⟨Subtype.val, continuous_subtype_val⟩ rfl) := by
  rw [homotopyGroupMap_basedMap_val_eq]
  exact (TopCat.injective_homotopyGroupMap_fiberι_of_section
    (e := mappingSpaceEvalFiberConst b x) hev (const_comp_mappingSpaceEvalHom b) rfl).comp
      (Equiv.injective _)

/-- **Exactness at all maps.** If evaluation `Map(B, Q) → Q` at `b` is a Serre fibration then, in
every dimension, a class of `π_N(Map(B, Q))` at the constant map at `x` comes from the based maps
exactly when its evaluation at `b` is trivial. -/
theorem mem_range_homotopyGroupMap_basedMap_val_iff
    (hev : TopCat.serreFibrations (_root_.TopCat.ofHom (mappingSpaceEval (X := Q) b)))
    [Finite N] {a : HomotopyGroup N C(B, Q) (ContinuousMap.const B x)} :
    a ∈ Set.range (HomotopyGroup.map (N := N)
      (x := (⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩ : BasedMap B Q b x))
      ⟨Subtype.val, continuous_subtype_val⟩ rfl) ↔
      HomotopyGroup.map (mappingSpaceEval b) (leftInverse_mappingSpaceEval_const b x) a =
        (⟦GenLoop.const⟧ : HomotopyGroup N Q x) := by
  have h := congrFun (homotopyGroupMap_basedMap_val_eq (N := N) b x)
  refine Iff.trans ?_ (TopCat.mem_range_homotopyGroupMap_fiberι_iff
    (e := mappingSpaceEvalFiberConst b x) hev)
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, (h c).symm⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, (h _).trans (congrArg _ (Equiv.symm_apply_apply _ c))⟩

/-! ### Shifted based maps in all maps -/

section Shift

variable {x} [DecidableEq N] [Nonempty N] {G : Type*} [Group G]

/-- The homomorphism `G → π_N(Map(B, Q), x)` at the constant map, for a group `G` identified with
the homotopy group of the based maps by `e`: the inverse of `e`, followed by the inclusion of the
based maps. For maps out of a circle or a sphere, `e` is the shift of the based maps, an iterated
loop space, to the homotopy groups of `Q`. -/
def basedMapHomotopyGroupHom
    (e : HomotopyGroup N (BasedMap B Q b x)
      ⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩ ≃* G) :
    G →* HomotopyGroup N C(B, Q) (ContinuousMap.const B x) :=
  (HomotopyGroup.mapHom ⟨Subtype.val, continuous_subtype_val⟩ rfl).comp e.symm.toMonoidHom

/-- On the image under `e` of a class of based maps, `TauCeti.basedMapHomotopyGroupHom` is the map
induced by the inclusion of the based maps. -/
theorem basedMapHomotopyGroupHom_apply_mulEquiv
    (e : HomotopyGroup N (BasedMap B Q b x)
      ⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩ ≃* G)
    (a : HomotopyGroup N (BasedMap B Q b x)
      ⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩) :
    basedMapHomotopyGroupHom e (e a) =
      HomotopyGroup.map ⟨Subtype.val, continuous_subtype_val⟩ rfl a := by
  rw [basedMapHomotopyGroupHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, HomotopyGroup.mapHom_apply]

/-- If evaluation `Map(B, Q) → Q` at `b` is a Serre fibration then
`TauCeti.basedMapHomotopyGroupHom` is injective. -/
theorem injective_basedMapHomotopyGroupHom
    (hev : TopCat.serreFibrations (_root_.TopCat.ofHom (mappingSpaceEval (X := Q) b)))
    [Finite N]
    (e : HomotopyGroup N (BasedMap B Q b x)
      ⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩ ≃* G) :
    Function.Injective (basedMapHomotopyGroupHom e) := by
  rw [basedMapHomotopyGroupHom, MonoidHom.coe_comp]
  exact (injective_homotopyGroupMap_basedMap_val x hev).comp (MulEquiv.injective _)

/-- **Exactness at all maps.** If evaluation `Map(B, Q) → Q` at `b` is a Serre fibration then the
image of `TauCeti.basedMapHomotopyGroupHom` is the kernel of evaluation on homotopy groups. -/
theorem range_basedMapHomotopyGroupHom
    (hev : TopCat.serreFibrations (_root_.TopCat.ofHom (mappingSpaceEval (X := Q) b)))
    [Finite N]
    (e : HomotopyGroup N (BasedMap B Q b x)
      ⟨ContinuousMap.const B x, ContinuousMap.const_apply x b⟩ ≃* G) :
    (basedMapHomotopyGroupHom e).range =
      (HomotopyGroup.mapHom (N := N) (mappingSpaceEval (X := Q) b)
        (leftInverse_mappingSpaceEval_const b x)).ker := by
  ext a
  rw [MonoidHom.mem_ker, HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one,
    ← mem_range_homotopyGroupMap_basedMap_val_iff x hev]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨e c, basedMapHomotopyGroupHom_apply_mulEquiv e c⟩

end Shift

variable (b)

/-- **The constant maps split evaluation on homotopy groups.** Evaluation `Map(B, Q) → Q` at `b`
undoes the constant maps on homotopy groups. -/
theorem mapHom_mappingSpaceEval_comp_mapHom_const [DecidableEq N] [Nonempty N] :
    (HomotopyGroup.mapHom (mappingSpaceEval (X := Q) b)
        (leftInverse_mappingSpaceEval_const b x)).comp
        (HomotopyGroup.mapHom (N := N) (x := x) ContinuousMap.const' rfl) =
      MonoidHom.id (HomotopyGroup N Q x) :=
  MonoidHom.ext fun a ↦ HomotopyGroup.map_map_of_comp_eq_id _ _ rfl _
    (mappingSpaceEval_comp_const' b) a

end TauCeti
