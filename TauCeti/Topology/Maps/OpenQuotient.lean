/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Maps.OpenQuotient
public import TauCeti.Data.Setoid.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Open quotient maps

An open quotient map `π : X → Y` commutes with taking frontiers of saturated sets: if `A` is the
full preimage of its image, the frontier of `π '' A` is the image of the frontier of `A`. This is
what lets a decomposition of `X` into pieces meeting along their frontiers descend to a quotient.
Likewise, preimages under an open quotient map commute with `coborder`, so local closedness
descends along open quotient maps (`IsOpenQuotientMap.isLocallyClosed_preimage_iff`).

Every homeomorphism is an open quotient map (`IsHomeomorph.isOpenQuotientMap`), and discrete
topologies descend along coinducing, quotient, and open quotient maps
(`Topology.IsCoinducing.discreteTopology`, `Topology.IsQuotientMap.discreteTopology`,
`IsOpenQuotientMap.discreteTopology`).

For a `Setoid X`, coordinate swap gives an involutive homeomorphism `Setoid.swapHomeomorph` of its
graph `{q : X × X // r q.1 q.2}`, making openness and the generalizing property symmetric between
the two projections (`Setoid.isOpenMap_snd_iff_fst`, `Setoid.generalizingMap_snd_iff_fst`). When a
projection is generalizing, saturations of open subsets are stable under generalization
(`IsOpen.stableUnderGeneralization_preimage_image_quotientMk`). When a projection is open,
`Quotient.mk r` is an open quotient map (`Setoid.isOpenMap_quotientMk`,
`Setoid.isOpenQuotientMap_quotientMk`), restricting `r` to any open subset `W ⊆ X` preserves
openness of the first projection (`IsOpen.isOpenMap_fst_comap`), and the quotient of `W` by the
restricted equivalence relation is homeomorphic to its image `Quotient.mk r '' W`
(`IsOpen.quotientComapHomeomorphImage`), without requiring `W` to be saturated.
-/

public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}

/-- The frontier of the image of a saturated set under an open quotient map is the image of its
frontier. -/
theorem IsOpenQuotientMap.frontier_image_of_preimage_image_eq (hπ : IsOpenQuotientMap π)
    {A : Set X} (hA : π ⁻¹' (π '' A) = A) : frontier (π '' A) = π '' frontier A := by
  rw [← image_preimage_eq (frontier (π '' A)) hπ.surjective,
    hπ.isOpenMap.preimage_frontier_eq_frontier_preimage hπ.continuous, hA]

/-- Under an open quotient map, a set has locally closed preimage if and only if it is locally
closed. -/
theorem IsOpenQuotientMap.isLocallyClosed_preimage_iff (hπ : IsOpenQuotientMap π) {s : Set Y} :
    IsLocallyClosed (π ⁻¹' s) ↔ IsLocallyClosed s := by
  rw [isLocallyClosed_iff_isOpen_coborder, isLocallyClosed_iff_isOpen_coborder,
    coborder_preimage hπ.isOpenMap hπ.continuous, ← hπ.isQuotientMap.isOpen_preimage]

/-- A homeomorphism is an open quotient map. -/
theorem IsHomeomorph.isOpenQuotientMap (hπ : IsHomeomorph π) : IsOpenQuotientMap π :=
  ⟨hπ.surjective, hπ.continuous, hπ.isOpenMap⟩

/-- A coinducing map out of a discrete space has discrete codomain. -/
theorem Topology.IsCoinducing.discreteTopology [DiscreteTopology X]
    (hπ : Topology.IsCoinducing π) : DiscreteTopology Y := by
  rw [discreteTopology_iff_forall_isOpen]
  exact fun s ↦ hπ.isOpen_preimage.mp (isOpen_discrete _)

/-- A quotient map out of a discrete space has discrete codomain. -/
theorem Topology.IsQuotientMap.discreteTopology [DiscreteTopology X]
    (hπ : Topology.IsQuotientMap π) : DiscreteTopology Y :=
  hπ.isCoinducing.discreteTopology

/-- An open quotient map out of a discrete space has discrete codomain. -/
theorem IsOpenQuotientMap.discreteTopology [DiscreteTopology X]
    (hπ : IsOpenQuotientMap π) : DiscreteTopology Y :=
  hπ.isQuotientMap.discreteTopology

namespace Setoid

/-- Swapping coordinates is an involutive homeomorphism on `{q : X × X // r q.1 q.2}`. -/
def swapHomeomorph (r : Setoid X) :
    {q : X × X // r q.1 q.2} ≃ₜ {q : X × X // r q.1 q.2} :=
  (Homeomorph.prodComm X X).subtype fun _ ↦ ⟨r.symm, r.symm⟩

@[simp]
theorem coe_swapHomeomorph (r : Setoid X) (q : {q : X × X // r q.1 q.2}) :
    (r.swapHomeomorph q : X × X) = q.val.swap :=
  (rfl)

@[simp]
theorem swapHomeomorph_symm (r : Setoid X) : r.swapHomeomorph.symm = r.swapHomeomorph :=
  (rfl)

/-- The first coordinate after `Setoid.swapHomeomorph` is the second coordinate. -/
theorem fst_swapHomeomorph (r : Setoid X) (q : {q : X × X // r q.1 q.2}) :
    (r.swapHomeomorph q).val.1 = q.val.2 :=
  (rfl)

/-- The second coordinate after `Setoid.swapHomeomorph` is the first coordinate. -/
theorem snd_swapHomeomorph (r : Setoid X) (q : {q : X × X // r q.1 q.2}) :
    (r.swapHomeomorph q).val.2 = q.val.1 :=
  (rfl)

/-- On the graph of an equivalence relation, the second projection is an open map if and only if
the first projection is. -/
theorem isOpenMap_snd_iff_fst (r : Setoid X) :
    IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.val.2) ↔
      IsOpenMap (fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) := by
  have heq : (fun q : {q : X × X // r q.1 q.2} ↦ q.val.2) =
      (fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) ∘ r.swapHomeomorph :=
    funext fun q ↦ (r.fst_swapHomeomorph q).symm
  rw [heq]
  exact ⟨fun h ↦ by simpa [Function.comp_def] using h.comp r.swapHomeomorph.isOpenMap,
    fun h ↦ h.comp r.swapHomeomorph.isOpenMap⟩

/-- On the graph of an equivalence relation, the second projection is generalizing if and only if
the first projection is. -/
theorem generalizingMap_snd_iff_fst (r : Setoid X) :
    GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.val.2) ↔
      GeneralizingMap (fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) := by
  have heq : (fun q : {q : X × X // r q.1 q.2} ↦ q.val.2) =
      (fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) ∘ r.swapHomeomorph :=
    funext fun q ↦ (r.fst_swapHomeomorph q).symm
  rw [heq]
  exact ⟨fun h ↦ by simpa [Function.comp_def] using
      r.swapHomeomorph.isOpenEmbedding.generalizingMap.comp h,
    fun h ↦ r.swapHomeomorph.isOpenEmbedding.generalizingMap.comp h⟩

/-- If the first projection from `{q : X × X // r q.1 q.2}` is open, then `Quotient.mk r` is an
open map. -/
theorem isOpenMap_quotientMk (r : Setoid X)
    (hs : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) :
    IsOpenMap (Quotient.mk r) := fun U hU ↦
  isQuotientMap_quot_mk.isOpen_preimage.mp <|
    (r.preimage_image_quotientMk U).symm ▸ (r.isOpenMap_snd_iff_fst.mpr hs) _
      (hU.preimage (continuous_fst.comp continuous_subtypeVal))

/-- If the first projection from `{q : X × X // r q.1 q.2}` is open, then `Quotient.mk r` is an
open quotient map. -/
theorem isOpenQuotientMap_quotientMk (r : Setoid X)
    (hs : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) :
    IsOpenQuotientMap (Quotient.mk r) :=
  ⟨Quotient.mk_surjective, continuous_quot_mk, r.isOpenMap_quotientMk hs⟩

end Setoid

/-- When the first projection from `{q : X × X // r q.1 q.2}` is generalizing, the saturation of
every open subset `W ⊆ X` is stable under generalization. -/
theorem IsOpen.stableUnderGeneralization_preimage_image_quotientMk {r : Setoid X} {W : Set X}
    (hWo : IsOpen W) (hs_gen : GeneralizingMap fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) :
    StableUnderGeneralization (Quotient.mk r ⁻¹' (Quotient.mk r '' W)) := by
  rw [r.preimage_image_quotientMk]
  exact ((hWo.preimage (continuous_fst.comp continuous_subtypeVal)).stableUnderGeneralization
    ).image (r.generalizingMap_snd_iff_fst.mpr hs_gen)

/-- Restricting an equivalence relation with open first projection to an open subset `W ⊆ X`
yields an equivalence relation on `W` whose first projection is again an open map. -/
theorem IsOpen.isOpenMap_fst_comap {r : Setoid X} {W : Set X} (hWo : IsOpen W)
    (hs_open : IsOpenMap fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) :
    IsOpenMap (fun q : {q : W × W // (r.comap (Subtype.val : W → X)) q.1 q.2} ↦ q.val.1) := by
  intro O hO
  rw [isOpen_induced_iff] at hO
  obtain ⟨O₁, hO₁o, rfl⟩ := hO
  let O₂ : Set (X × X) := (Prod.map (Subtype.val : W → X) (Subtype.val : W → X)) '' O₁
  have hO₂o : IsOpen O₂ :=
    (hWo.isOpenMap_subtypeVal.prodMap hWo.isOpenMap_subtypeVal) O₁ hO₁o
  let O₃ : Set {q : X × X // r q.1 q.2} := Subtype.val ⁻¹' O₂
  have hO₃o : IsOpen O₃ := hO₂o.preimage continuous_subtypeVal
  have heq : (fun q : {q : W × W // (r.comap (Subtype.val : W → X)) q.1 q.2} ↦ q.val.1) ''
      (Subtype.val ⁻¹' O₁) =
      (Subtype.val : W → X) ⁻¹' ((fun q : {q : X × X // r q.1 q.2} ↦ q.val.1) '' O₃) := by
    ext w
    constructor
    · rintro ⟨⟨⟨w₁, w₂⟩, hr⟩, hwO₁, rfl⟩
      exact ⟨⟨(w₁.val, w₂.val), hr⟩, ⟨(w₁, w₂), hwO₁, rfl⟩, rfl⟩
    · rintro ⟨⟨⟨x₁, x₂⟩, hr⟩, ⟨⟨w₁, w₂⟩, hwO₁, hprod⟩, hx₁⟩
      have hx₁' : w₁.val = x₁ := congrArg Prod.fst hprod
      have hx₂ : w₂.val = x₂ := congrArg Prod.snd hprod
      have hw₁ : w₁ = w := Subtype.ext (hx₁'.trans hx₁)
      subst hw₁
      have hrW : (r.comap (Subtype.val : W → X)) w₁ w₂ := by
        rw [Setoid.comap_rel, hx₁', hx₂]
        exact hr
      exact ⟨⟨(w₁, w₂), hrW⟩, hwO₁, rfl⟩
  rw [heq]
  exact (hs_open O₃ hO₃o).preimage continuous_subtypeVal

/-- When `Quotient.mk r` is an open map and `W ⊆ X` is open, the quotient of `W` by the induced
equivalence relation `r.comap Subtype.val` is homeomorphic to its image `Quotient.mk r '' W`,
even when `W` is not saturated for `r`. -/
noncomputable def IsOpen.quotientComapHomeomorphImage {r : Setoid X} {W : Set X} (hW : IsOpen W)
    (hq : IsOpenMap (Quotient.mk r)) :
    Quotient (r.comap (Subtype.val : W → X)) ≃ₜ Quotient.mk r '' W := by
  let g : C(W, Quotient.mk r '' W) :=
    ⟨fun w ↦ ⟨Quotient.mk r w.val, w.val, w.property, rfl⟩,
      (continuous_quot_mk.comp continuous_subtypeVal).subtype_mk _⟩
  have hg : IsOpenQuotientMap g :=
    ⟨fun ⟨_, x, hxW, hx⟩ ↦ ⟨⟨x, hxW⟩, Subtype.ext hx⟩,
      g.continuous, (hq.comp hW.isOpenMap_subtypeVal).subtype_mk _⟩
  exact (Homeomorph.Quotient.congrRight fun w₁ w₂ ↦ by
    rw [Setoid.comap_rel, Setoid.ker_def, Subtype.ext_iff]
    exact (@Quotient.eq _ r w₁.val w₂.val).symm).trans hg.isQuotientMap.homeomorph

@[simp]
theorem IsOpen.coe_quotientComapHomeomorphImage_mk {r : Setoid X} {W : Set X} (hW : IsOpen W)
    (hq : IsOpenMap (Quotient.mk r)) (w : W) :
    ((hW.quotientComapHomeomorphImage hq
      (Quotient.mk (r.comap (Subtype.val : W → X)) w)) : Quotient r) = Quotient.mk r w.val := by
  simp only [IsOpen.quotientComapHomeomorphImage, Homeomorph.trans_apply,
    IsQuotientMap.homeomorph_apply]
  exact congrArg Subtype.val (Setoid.kerLift_mk _ w)
