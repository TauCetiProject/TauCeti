/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.Analysis.Normed.Order.OrderUnit

/-!
# Further properties and norm completion of order-unit spaces

This file extends `TauCeti.Analysis.Normed.Order.OrderUnit` with additional properties of
`TauCeti.IsOrderUnitNorm`, automatic `PosSMulMono ℝ E`, unital linear order isomorphisms as
linear isometry equivalences, transport of `IsOrderUnitNorm` along unital isometric order
embeddings, and the norm completion of an order-unit space.

## Main definitions and results

* `TauCeti.IsOrderUnitNorm.nontrivial`, `norm_eq_zero_iff`, `norm_smul_unit`,
  `norm_le_iff_of_nonneg`, `norm_le_norm_of_le`, `nonneg_iff_exists`,
  `le_iff_norm_smul_sub_le`, `posSMulMono`, `closedBall_subset_Ici_zero`: additional norm and
  order properties derived from `IsOrderUnitNorm`.
* `TauCeti.IsOrderUnitNorm.linearIsometryEquivOfMapNonnegIff`, `of_linearIsometry`: unital linear
  order isomorphisms as linear isometry equivalences, and pullback of `IsOrderUnitNorm` along
  unital isometric order embeddings.
* `TauCeti.IsOrderUnitNorm.completionPosCone`, `completionPartialOrder`, `completion_le_iff`,
  `completion_nonneg_iff`, `completionIsOrderedAddMonoid`, `completion_coe_le_coe_iff`,
  `isOrderUnitNorm_completion`: the norm completion `UniformSpace.Completion E` equipped with the
  closed positive cone is an order-unit space with the same unit.
* `TauCeti.isOrderUnitNorm_pi_one`: finite nonempty `ℓ∞(ι, ℝ)` with `e = 1` is an order-unit space.

## References

* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), 559–600, §1.
* R. V. Kadison, *A representation theory for commutative topological algebra*,
  Mem. Amer. Math. Soc. 7 (1951).
-/

public section

open Set Metric
open scoped Topology

namespace TauCeti

namespace IsOrderUnitNorm

section BasicMinimal

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  {e : E} (he : IsOrderUnitNorm e)

include he

/-- A space carrying an order-unit norm is nontrivial. -/
theorem nontrivial : Nontrivial E :=
  ⟨⟨e, 0, he.ne_zero⟩⟩

/-- An order-unit seminorm is automatically definite (`‖a‖ = 0 ↔ a = 0`). -/
theorem norm_eq_zero_iff {a : E} : ‖a‖ = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  obtain ⟨hlo, hhi⟩ := (he.norm_le_iff le_rfl).mp h.le
  simp only [neg_zero, zero_smul] at hlo hhi
  exact le_antisymm hhi hlo

end BasicMinimal

section NormSmulUnit

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]

/-- Scalar multiples of the order unit satisfy `‖r • e‖ = |r|`. -/
theorem norm_smul_unit {e : E} (he : IsOrderUnitNorm e) (r : ℝ) : ‖r • e‖ = |r| := by
  rw [norm_smul, Real.norm_eq_abs, he.norm_eq_one, mul_one]

end NormSmulUnit

section BasicOrdered

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- For a nonnegative element `a`, `‖a‖ ≤ r` is equivalent to `a ≤ r • e`. -/
theorem norm_le_iff_of_nonneg {a : E} (ha : 0 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    ‖a‖ ≤ r ↔ a ≤ r • e := by
  rw [he.norm_le_iff hr, and_iff_right_iff_imp]
  intro _
  exact (neg_nonpos.mpr (he.smul_nonneg hr)).trans ha

/-- Monotonicity of the order-unit norm on symmetric order intervals: `-b ≤ a ≤ b` implies
`‖a‖ ≤ ‖b‖`. -/
theorem norm_le_norm_of_le {a b : E} (hlo : -b ≤ a) (hhi : a ≤ b) : ‖a‖ ≤ ‖b‖ := by
  refine (he.norm_le_iff (norm_nonneg b)).mpr ⟨?_, hhi.trans (he.le_norm_smul b)⟩
  have h : -(‖b‖ • e) ≤ -b := neg_le_neg (he.le_norm_smul b)
  exact h.trans hlo

/-- An element `a` is nonnegative iff `‖r • e - a‖ ≤ r` for some `r ≥ 0`. -/
theorem nonneg_iff_exists {a : E} :
    0 ≤ a ↔ ∃ r : ℝ, 0 ≤ r ∧ ‖r • e - a‖ ≤ r := by
  refine ⟨fun ha => ⟨‖a‖, norm_nonneg a, he.nonneg_iff_norm_smul_sub_le.mp ha⟩,
    fun ⟨r, hr, hle⟩ => ?_⟩
  have hhi := ((he.norm_le_iff hr).mp hle).2
  exact le_add_iff_nonneg_right (r • e) |>.mp (sub_le_iff_le_add.mp hhi)

/-- Recovery of the partial order from the norm and the order unit. -/
theorem le_iff_norm_smul_sub_le {a b : E} :
    a ≤ b ↔ ‖‖b - a‖ • e - (b - a)‖ ≤ ‖b - a‖ := by
  rw [← sub_nonneg, he.nonneg_iff_norm_smul_sub_le]

/-- The closed unit ball around the order unit `e` lies inside the positive cone. -/
theorem closedBall_subset_Ici_zero : closedBall e 1 ⊆ Ici 0 := fun a ha => by
  rw [mem_closedBall_iff_norm] at ha
  have hlo := ((he.norm_le_iff zero_le_one).mp ha).1
  rw [one_smul] at hlo
  exact sub_nonneg.mp (by simpa [sub_eq_add_neg, add_comm] using add_le_add_left hlo e)

end BasicOrdered

section PosSMulMono

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] {e : E} (he : IsOrderUnitNorm e)

include he

/-- Compatibility of the partial order with nonnegative scalar multiplication follows
automatically from `IsOrderUnitNorm`. -/
theorem posSMulMono : PosSMulMono ℝ E := by
  refine ⟨fun c hc a b hab => ?_⟩
  rw [← sub_nonneg, ← smul_sub, he.nonneg_iff_norm_smul_sub_le]
  have hx : ‖‖b - a‖ • e - (b - a)‖ ≤ ‖b - a‖ :=
    he.nonneg_iff_norm_smul_sub_le.mp (sub_nonneg.mpr hab)
  calc
    ‖‖c • (b - a)‖ • e - c • (b - a)‖
        = ‖c • (‖b - a‖ • e - (b - a))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_smul, ← smul_sub]
    _ = c * ‖‖b - a‖ • e - (b - a)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ c * ‖b - a‖ := mul_le_mul_of_nonneg_left hx hc
    _ = ‖c • (b - a)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]

end PosSMulMono

section Maps

variable {E F : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [PartialOrder E]
  [SeminormedAddCommGroup F] [Module ℝ F] [PartialOrder F]

/-- A unital linear order isomorphism between order-unit spaces is automatically a linear
isometry equivalence. -/
def linearIsometryEquivOfMapNonnegIff [IsOrderedAddMonoid E] [IsOrderedAddMonoid F]
    {e : E} {f : F} (he : IsOrderUnitNorm e)
    (hf : IsOrderUnitNorm f) (T : E ≃ₗ[ℝ] F) (hTe : T e = f)
    (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) : E ≃ₗᵢ[ℝ] F where
  toLinearEquiv := T
  norm_map' := he.norm_map hf T.toLinearMap hTe fun a b => by
    rw [← sub_nonneg, ← map_sub, LinearEquiv.coe_coe, hpos, sub_nonneg]

/-- Evaluating `linearIsometryEquivOfMapNonnegIff` agrees with the underlying linear equivalence. -/
@[simp]
theorem linearIsometryEquivOfMapNonnegIff_apply [IsOrderedAddMonoid E] [IsOrderedAddMonoid F]
    {e : E} {f : F}
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : E ≃ₗ[ℝ] F) (hTe : T e = f)
    (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) (a : E) :
    he.linearIsometryEquivOfMapNonnegIff hf T hTe hpos a = T a :=
  (rfl)

/-- Evaluating the inverse of `linearIsometryEquivOfMapNonnegIff` agrees with `T.symm`. -/
@[simp]
theorem linearIsometryEquivOfMapNonnegIff_symm_apply [IsOrderedAddMonoid E] [IsOrderedAddMonoid F]
    {e : E} {f : F}
    (he : IsOrderUnitNorm e) (hf : IsOrderUnitNorm f) (T : E ≃ₗ[ℝ] F) (hTe : T e = f)
    (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) (b : F) :
    (he.linearIsometryEquivOfMapNonnegIff hf T hTe hpos).symm b = T.symm b :=
  (rfl)

end Maps

section LinearIsometryMap

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PartialOrder F]
  [IsOrderedAddMonoid F]

/-- Transport of `IsOrderUnitNorm` back along a linear isometric order embedding. -/
theorem of_linearIsometry {e : E} {f : F}
    (hf : IsOrderUnitNorm f) (T : E →ₗᵢ[ℝ] F) (hTe : T e = f)
    (hpos : ∀ a : E, 0 ≤ T a ↔ 0 ≤ a) : IsOrderUnitNorm e where
  norm_eq_one := by rw [← T.norm_map e, hTe, hf.norm_eq_one]
  norm_le_iff {a r} hr := by
    have hle_iff (x y : E) : T x ≤ T y ↔ x ≤ y := by
      rw [← sub_nonneg, ← map_sub, hpos, sub_nonneg]
    rw [← T.norm_map a, hf.norm_le_iff hr, ← hTe, ← map_smul, ← map_neg, hle_iff, hle_iff]

end LinearIsometryMap

/-! ### Norm completion of an order-unit space -/

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
  refine he.norm_le_norm_of_le ?_ ?_
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

/-- Finite-dimensional `ℓ∞(ι, ℝ)` with `e = 1` is an order-unit space. -/
theorem isOrderUnitNorm_pi_one {ι : Type*} [Fintype ι] [Nonempty ι] :
    IsOrderUnitNorm (1 : ι → ℝ) :=
  IsOrderUnitNorm.pi fun _ => isOrderUnitNorm_real_one

end TauCeti
