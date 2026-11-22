/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.Analysis.Normed.Order.OrderUnit.Basic

/-!
# Norm completion of an order-unit space

This file equips the norm completion `UniformSpace.Completion E` of an order-unit space `(E, e)`
with the closed positive cone `TauCeti.IsOrderUnitNorm.completionPosCone`, defines the induced
partial order `TauCeti.IsOrderUnitNorm.completionPartialOrder`, and proves that the completion
norm is the order-unit norm of the canonical image `(e : UniformSpace.Completion E)`.

## Main definitions and results

* `TauCeti.IsOrderUnitNorm.completionPosCone`, `coe_completionPosCone`,
  `coe_mem_completionPosCone_iff`: the closed positive cone in `UniformSpace.Completion E`.
* `TauCeti.IsOrderUnitNorm.completionPartialOrder`, `completion_le_iff`,
  `completion_nonneg_iff`, `completionIsOrderedAddMonoid`, `completion_coe_le_coe_iff`:
  the partial order on `UniformSpace.Completion E` induced by the closed positive cone.
* `TauCeti.IsOrderUnitNorm.isOrderUnitNorm_completion`: `UniformSpace.Completion E` with the
  closed positive cone and unit `(e : UniformSpace.Completion E)` is an order-unit space.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, §1.
* R. V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set
open scoped Topology

namespace TauCeti

namespace IsOrderUnitNorm

section Completion

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- The closed positive cone in the norm completion `UniformSpace.Completion E`, obtained by
mapping `ProperCone.positive ℝ E` along `E →L[ℝ] UniformSpace.Completion E`. -/
noncomputable def completionPosCone : ProperCone ℝ (UniformSpace.Completion E) :=
  let : PosSMulMono ℝ E := he.posSMulMono
  have : OrderClosedTopology E := he.orderClosedTopology
  (ProperCone.positive ℝ E).map (UniformSpace.Completion.toComplL (S := ℝ) (α := E))

/-- As a set, `he.completionPosCone` is the closure of the image of the positive cone of `E`. -/
theorem coe_completionPosCone :
    (he.completionPosCone : Set (UniformSpace.Completion E)) =
      closure (((↑) : E → UniformSpace.Completion E) '' Set.Ici (0 : E)) := by
  let : PosSMulMono ℝ E := he.posSMulMono
  have : OrderClosedTopology E := he.orderClosedTopology
  ext x
  simp only [completionPosCone, SetLike.mem_coe, ProperCone.mem_map]
  change x ∈ ((PointedCone.map (UniformSpace.Completion.toComplL (S := ℝ) (α := E) :
    E →ₗ[ℝ] UniformSpace.Completion E) (ProperCone.positive ℝ E).toPointedCone).topologicalClosure :
    Set (UniformSpace.Completion E)) ↔ _
  rw [Submodule.topologicalClosure_coe, PointedCone.coe_map, ProperCone.toPointedCone_positive]
  have himg : ((UniformSpace.Completion.toComplL (S := ℝ) (α := E) :
      E →ₗ[ℝ] UniformSpace.Completion E) '' (PointedCone.positive ℝ E : Set E)) =
      (((↑) : E → UniformSpace.Completion E) '' Set.Ici (0 : E)) := by
    ext y
    simp [UniformSpace.Completion.toComplL]
  rw [himg]

/-- An element of `E` lies in `he.completionPosCone` iff it is nonnegative in `E`. -/
theorem coe_mem_completionPosCone_iff {a : E} :
    (a : UniformSpace.Completion E) ∈ he.completionPosCone ↔ 0 ≤ a := by
  have h := (UniformSpace.Completion.isUniformInducing_coe E).isInducing
    |>.closure_eq_preimage_closure_image (Set.Ici (0 : E))
  have hcl : closure (Set.Ici (0 : E)) = Set.Ici (0 : E) := he.isClosed_nonneg.closure_eq
  rw [hcl] at h
  change (a : UniformSpace.Completion E) ∈ (he.completionPosCone : Set _) ↔ 0 ≤ a
  rw [he.coe_completionPosCone]
  exact Set.ext_iff.mp h.symm a

private theorem norm_sub_le_norm_add_of_mem_completionPosCone
    {u v : UniformSpace.Completion E}
    (hu : u ∈ he.completionPosCone) (hv : v ∈ he.completionPosCone) :
    ‖u - v‖ ≤ ‖u + v‖ := by
  change u ∈ (he.completionPosCone : Set _) at hu
  change v ∈ (he.completionPosCone : Set _) at hv
  rw [he.coe_completionPosCone] at hu hv
  let S : Set (UniformSpace.Completion E) :=
    ((↑) : E → UniformSpace.Completion E) '' Set.Ici (0 : E)
  have huv : (u, v) ∈ closure (S ×ˢ S) := by
    rw [closure_prod_eq]
    exact ⟨hu, hv⟩
  refine closure_minimal ?_
    (isClosed_le (continuous_fst.sub continuous_snd).norm
      (continuous_fst.add continuous_snd).norm) huv
  rintro ⟨u', v'⟩ ⟨⟨p, hp, hup⟩, ⟨q, hq, hvq⟩⟩
  dsimp only at hup hvq
  change ‖u' - v'‖ ≤ ‖u' + v'‖
  rw [← hup, ← hvq, ← UniformSpace.Completion.coe_sub, ← UniformSpace.Completion.coe_add,
    UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  refine he.norm_le_norm_of_neg_le_of_le ?_ ?_
  · rw [neg_add, sub_eq_add_neg]
    exact add_le_add ((neg_nonpos.mpr hp).trans hp) le_rfl
  · rw [sub_eq_add_neg]
    exact add_le_add le_rfl ((neg_nonpos.mpr hq).trans hq)

/-- The completion positive cone is pointed (`x ∈ C` and `-x ∈ C` imply `x = 0`). -/
theorem eq_zero_of_mem_completionPosCone_of_neg_mem
    {x : UniformSpace.Completion E} (hx : x ∈ he.completionPosCone)
    (hneg : -x ∈ he.completionPosCone) : x = 0 := by
  have h := he.norm_sub_le_norm_add_of_mem_completionPosCone hx hneg
  rw [sub_neg_eq_add, add_neg_cancel, norm_zero, ← two_smul ℝ x, norm_smul,
    Real.norm_eq_abs, abs_of_pos two_pos] at h
  exact norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg x))

private theorem salient_completionPosCone :
    (he.completionPosCone : ConvexCone ℝ (UniformSpace.Completion E)).Salient :=
  fun _ hx hx0 hneg => hx0 (he.eq_zero_of_mem_completionPosCone_of_neg_mem hx hneg)

/-- The partial order on `UniformSpace.Completion E` defined by the closed positive cone
`he.completionPosCone`. -/
@[instance_reducible]
noncomputable def completionPartialOrder : PartialOrder (UniformSpace.Completion E) :=
  (he.completionPosCone : ConvexCone ℝ (UniformSpace.Completion E)).toPartialOrder
    he.completionPosCone.pointed_toConvexCone he.salient_completionPosCone

/-- Characterization of the completion partial order in terms of `he.completionPosCone`. -/
theorem completion_le_iff {x y : UniformSpace.Completion E} :
    @LE.le _ he.completionPartialOrder.toLE x y ↔ y - x ∈ he.completionPosCone :=
  (Iff.rfl)

/-- Nonnegativity in the completion partial order is membership in `he.completionPosCone`. -/
theorem completion_nonneg_iff {x : UniformSpace.Completion E} :
    @LE.le _ he.completionPartialOrder.toLE 0 x ↔ x ∈ he.completionPosCone := by
  rw [he.completion_le_iff, sub_zero]

/-- Addition is compatible with the completion partial order. -/
theorem completionIsOrderedAddMonoid :
    @IsOrderedAddMonoid (UniformSpace.Completion E) _ he.completionPartialOrder.toPreorder :=
  (he.completionPosCone : ConvexCone ℝ (UniformSpace.Completion E)).to_isOrderedAddMonoid
    he.completionPosCone.pointed_toConvexCone he.salient_completionPosCone

/-- The canonical embedding `E → UniformSpace.Completion E` preserves and reflects the order. -/
theorem completion_coe_le_coe_iff {a b : E} :
    @LE.le _ he.completionPartialOrder.toLE
      (a : UniformSpace.Completion E) (b : UniformSpace.Completion E) ↔ a ≤ b := by
  rw [he.completion_le_iff, ← UniformSpace.Completion.coe_sub, he.coe_mem_completionPosCone_iff,
    sub_nonneg]

private theorem add_norm_smul_mem_completionPosCone
    (x : UniformSpace.Completion E) :
    x + ‖x‖ • (e : UniformSpace.Completion E) ∈ he.completionPosCone := by
  refine UniformSpace.Completion.denseRange_coe.induction_on x ?_ fun a => ?_
  · exact he.completionPosCone.isClosed.preimage
      (continuous_id.add (continuous_norm.smul continuous_const))
  · rw [UniformSpace.Completion.norm_coe, ← UniformSpace.Completion.coe_smul,
      ← UniformSpace.Completion.coe_add]
    refine he.coe_mem_completionPosCone_iff.mpr ?_
    have hlo := he.neg_norm_smul_le a
    exact neg_le_iff_add_nonneg.mp hlo

/-- The norm completion of an order-unit space, with the closed positive cone and the image of `e`,
is an order-unit space with its completion norm. -/
theorem isOrderUnitNorm_completion :
    @IsOrderUnitNorm (UniformSpace.Completion E) _ _ _ he.completionPartialOrder
      (e : UniformSpace.Completion E) := by
  let : PartialOrder (UniformSpace.Completion E) := he.completionPartialOrder
  refine ⟨by rw [UniformSpace.Completion.norm_coe, he.norm_eq_one], fun {x r} hr => ⟨?_, ?_⟩⟩
  · intro hxr
    have hrsub : (r - ‖x‖) • (e : UniformSpace.Completion E) ∈ he.completionPosCone := by
      rw [← UniformSpace.Completion.coe_smul]
      exact he.coe_mem_completionPosCone_iff.mpr (he.smul_nonneg (sub_nonneg.mpr hxr))
    rw [he.completion_le_iff, he.completion_le_iff]
    refine ⟨?_, ?_⟩
    · have heq : x - (-(r • (e : UniformSpace.Completion E))) =
          (x + ‖x‖ • (e : UniformSpace.Completion E)) +
            (r - ‖x‖) • (e : UniformSpace.Completion E) := by
        rw [sub_neg_eq_add, sub_smul]; abel
      rw [heq]
      exact he.completionPosCone.add_mem (he.add_norm_smul_mem_completionPosCone x) hrsub
    · have heq : r • (e : UniformSpace.Completion E) - x =
          (-x + ‖-x‖ • (e : UniformSpace.Completion E)) +
            (r - ‖x‖) • (e : UniformSpace.Completion E) := by
        rw [norm_neg, sub_smul]; abel
      rw [heq]
      exact he.completionPosCone.add_mem (he.add_norm_smul_mem_completionPosCone (-x)) hrsub
  · rw [he.completion_le_iff, he.completion_le_iff]
    rintro ⟨hlo, hhi⟩
    have hlo' : x + r • (e : UniformSpace.Completion E) ∈ he.completionPosCone := by
      simpa [sub_neg_eq_add] using hlo
    have hbound := he.norm_sub_le_norm_add_of_mem_completionPosCone hlo' hhi
    have hsub : (x + r • (e : UniformSpace.Completion E)) -
        (r • (e : UniformSpace.Completion E) - x) = (2 : ℝ) • x := by rw [two_smul]; abel
    have hadd : (x + r • (e : UniformSpace.Completion E)) +
        (r • (e : UniformSpace.Completion E) - x) =
        (2 * r) • (e : UniformSpace.Completion E) := by rw [mul_smul, two_smul]; abel
    rw [hsub, hadd, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos two_pos,
      abs_of_nonneg (by positivity), UniformSpace.Completion.norm_coe, he.norm_eq_one,
      mul_one] at hbound
    linarith

end Completion

end IsOrderUnitNorm

end TauCeti
