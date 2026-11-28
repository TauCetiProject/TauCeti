/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Principal.MilnorJoin.Basic
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractibility of the strong-coordinate Milnor join

`TauCeti.MilnorTotalSpace.contractionToVertex` contracts the strong-coordinate join to
the vertex at index zero. Move each coordinate to its successor in its own time interval,
vacating the destination before the move begins. The resulting map is continuous by
`TauCeti.MilnorTotalSpace.continuous_iff`. At the end of the shift the zeroth coordinate is
empty, so `TauCeti.MilnorTotalSpace.coneAtFreshIndexHomotopy` gives the second half of the
contraction. This applies to the universal bundle of Milnor (*Construction of universal bundles,
II*, §§2–3).
-/

public section

noncomputable section

open unitInterval

namespace TauCeti.MilnorTotalSpace

variable {G : Type*}

private def moved (i : ℕ) (t : I) : I := Set.projIcc 0 1 zero_le_one
  ((2 : ℝ) ^ (i + 1) * (t : ℝ) - 1)

private theorem continuous_moved (i : ℕ) : Continuous (fun t ↦ (moved i t : ℝ)) :=
  continuous_subtypeVal.comp (continuous_projIcc.comp (by fun_prop))

private theorem moved_succ_eq_one {i : ℕ} {t : I} (h : 0 < (moved i t : ℝ)) :
    moved (i + 1) t = 1 := by
  simp only [moved, Set.coe_projIcc, lt_max_iff, lt_irrefl, false_or, lt_min_iff, sub_pos] at h
  rw [moved, projIcc_eq_one, pow_succ, mul_right_comm]
  linarith [h.2]

private theorem moved_zero (i : ℕ) : moved i 0 = 0 := by
  simp only [moved, projIcc_eq_zero, Set.Icc.coe_zero, mul_zero, sub_nonpos, zero_le_one]

private theorem moved_one (i : ℕ) : moved i 1 = 1 := by
  rw [moved, projIcc_eq_one, Set.Icc.coe_one, mul_one, pow_succ]
  have h : 1 ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  linarith

private def kept (z : I × MilnorTotalSpace G) (i : ℕ) : ℝ :=
  (1 - (moved i z.1 : ℝ)) * weight i z.2

private def incoming (z : I × MilnorTotalSpace G) : ℕ → ℝ
  | 0 => 0
  | i + 1 => (moved i z.1 : ℝ) * weight i z.2

private theorem kept_nonneg (z : I × MilnorTotalSpace G) (i : ℕ) : 0 ≤ kept z i :=
  mul_nonneg (one_sub_nonneg (moved i z.1)) (weight_nonneg i z.2)

private theorem incoming_nonneg (z : I × MilnorTotalSpace G) (i : ℕ) : 0 ≤ incoming z i := by
  cases i with
  | zero => exact le_rfl
  | succ i => exact mul_nonneg (unitInterval.nonneg (moved i z.1)) (weight_nonneg i z.2)

private theorem kept_eq_zero_of_incoming_pos {z : I × MilnorTotalSpace G} {i : ℕ}
    (h : 0 < incoming z i) : kept z i = 0 := by
  cases i with
  | zero => exact (lt_irrefl 0 h).elim
  | succ i =>
    simp only [kept, moved_succ_eq_one (pos_of_mul_pos_left h (weight_nonneg i z.2)),
      Set.Icc.coe_one, sub_self, zero_mul]

private theorem sum_range_kept_add_incoming (z : I × MilnorTotalSpace G) {N : ℕ}
    (hN : ∀ i, N ≤ i → weight i z.2 = 0) :
    ∑ i ∈ Finset.range (N + 1), (kept z i + incoming z i) = 1 := by
  rw [Finset.sum_add_distrib, Finset.sum_range_succ, Finset.sum_range_succ' (incoming z)]
  have hz : kept z N = 0 := by simp only [kept, hN N le_rfl, mul_zero]
  simp only [hz, add_zero, incoming]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ i ∈ Finset.range N, weight i z.2 := Finset.sum_congr rfl fun i _ ↦ by
      simp only [kept, sub_mul, one_mul, sub_add_cancel]
    _ = 1 := sum_weight_of_support_subset fun i hi ↦ hN i (le_of_not_gt (hi ∘ Finset.mem_range.mpr))

private def shiftLabel (z : I × MilnorTotalSpace G) (i : ℕ) : G :=
  if 0 < incoming z i then label i.pred z.2 else label i z.2

private def shiftPoint (z : I × MilnorTotalSpace G) : MilnorTotalSpace G :=
  ofFinsetCoord (Finset.range ((exists_forall_le_weight_eq_zero z.2).choose + 1))
    (fun i ↦ kept z i + incoming z i) (shiftLabel z)
    (fun i _ ↦ add_nonneg (kept_nonneg z i) (incoming_nonneg z i))
    (sum_range_kept_add_incoming z (exists_forall_le_weight_eq_zero z.2).choose_spec)

private theorem weight_shiftPoint (z : I × MilnorTotalSpace G) (i : ℕ) :
    weight i (shiftPoint z) = kept z i + incoming z i := by
  rw [shiftPoint, weight_ofFinsetCoord]
  split_ifs with hi
  · rfl
  · let N := (exists_forall_le_weight_eq_zero z.2).choose
    have hN : ∀ j, N ≤ j → weight j z.2 = 0 :=
      (exists_forall_le_weight_eq_zero z.2).choose_spec
    have hle : N + 1 ≤ i := by simpa only [Finset.mem_range, not_lt] using hi
    have hk : kept z i = 0 := by simp only [kept, hN i (Nat.le_of_succ_le hle), mul_zero]
    have hm : incoming z i = 0 := by
      cases i with
      | zero => rfl
      | succ j => simp only [incoming, hN j (Nat.le_of_succ_le_succ hle), mul_zero]
    rw [hk, hm, add_zero]

private theorem label_shiftPoint {z : I × MilnorTotalSpace G} {i : ℕ}
    (h : 0 < weight i (shiftPoint z)) : label i (shiftPoint z) = shiftLabel z i := by
  rw [shiftPoint, weight_ofFinsetCoord] at h
  split_ifs at h with hi
  · exact label_ofFinsetCoord _ _ _ _ _ hi h
  · exact (lt_irrefl 0 h).elim

variable [TopologicalSpace G]

private theorem continuous_shiftPoint : Continuous (shiftPoint : I × MilnorTotalSpace G → _) := by
  have hc (i : ℕ) : Continuous (fun z : I × MilnorTotalSpace G ↦ kept z i) := by
    exact (continuous_const.sub ((continuous_moved i).comp continuous_fst)).mul
      ((continuous_weight i).comp continuous_snd)
  have hd (i : ℕ) : Continuous (fun z : I × MilnorTotalSpace G ↦ incoming z i) := by
    cases i with
    | zero => exact continuous_const
    | succ i =>
      exact ((continuous_moved i).comp continuous_fst).mul
        ((continuous_weight i (G := G)).comp continuous_snd)
  refine continuous_iff.mpr ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · simp only [weight_shiftPoint]
    exact (hc i).add (hd i)
  have hkept : ContinuousOn (fun z : I × MilnorTotalSpace G ↦ label i (shiftPoint z))
      {z | 0 < kept z i} := by
    refine ((continuousOn_label i).comp continuous_snd.continuousOn
      (fun z hz ↦ mem_coordSet_iff.mpr (pos_of_mul_pos_right hz
        (one_sub_nonneg (moved i z.1))))).congr fun z hz ↦ ?_
    have hz' : 0 < kept z i := hz
    have hn : ¬ 0 < incoming z i := fun h ↦ hz'.ne' (kept_eq_zero_of_incoming_pos h)
    have hp : 0 < weight i (shiftPoint z) :=
      (weight_shiftPoint z i).symm ▸ add_pos_of_pos_of_nonneg hz' (incoming_nonneg z i)
    simp only [label_shiftPoint hp, shiftLabel, ite_eq_right hn, Function.comp_apply]
  have hin : ContinuousOn (fun z : I × MilnorTotalSpace G ↦ label i (shiftPoint z))
      {z | 0 < incoming z i} := by
    cases i with
    | zero =>
      simpa only [incoming, lt_self_iff_false, Set.ofPred_false] using
        (continuousOn_empty (f := fun z : I × MilnorTotalSpace G ↦ label 0 (shiftPoint z)))
    | succ i =>
      refine ((continuousOn_label i).comp continuous_snd.continuousOn
        (fun z hz ↦ mem_coordSet_iff.mpr (pos_of_mul_pos_right hz
          (unitInterval.nonneg (moved i z.1))))).congr fun z hz ↦ ?_
      have hz' : 0 < incoming z (i + 1) := hz
      have hp : 0 < weight (i + 1) (shiftPoint z) :=
        (weight_shiftPoint z _).symm ▸ add_pos_of_nonneg_of_pos (kept_nonneg z _) hz'
      simp only [label_shiftPoint hp, shiftLabel, ite_eq_left hz', Nat.pred_succ,
        Function.comp_apply]
  refine (hkept.union_of_isOpen hin (isOpen_lt continuous_const (hc i))
    (isOpen_lt continuous_const (hd i))).mono ?_
  intro z hz
  have hp : 0 < kept z i + incoming z i := weight_shiftPoint z i ▸ hz
  by_cases h : 0 < kept z i
  · exact Set.mem_union_left _ h
  · have hm : 0 < incoming z i := by linarith [le_of_not_gt h]
    exact Set.mem_union_right _ hm

/-- The strong-coordinate Milnor join contracts to the zeroth vertex labelled by any
specified point `a`. Use `ContinuousMap.Homotopy.apply_zero` and
`ContinuousMap.Homotopy.apply_one` for its endpoint equations. -/
def contractionToVertex (a : G) :
    (ContinuousMap.id (MilnorTotalSpace G)).Homotopy
      (ContinuousMap.const _ (vertex 0 a)) :=
  let f : C(MilnorTotalSpace G, MilnorTotalSpace G) :=
    ⟨fun p ↦ shiftPoint (1, p), continuous_shiftPoint.comp
      (continuous_const.prodMk continuous_id)⟩
  have hf (p : MilnorTotalSpace G) : weight 0 (f p) = 0 := by
    have h : weight 0 (shiftPoint (1, p)) = 0 := by
      simp only [weight_shiftPoint, kept, moved_one, Set.Icc.coe_one, sub_self, zero_mul,
        incoming, add_zero]
    exact h
  have hzero (p : MilnorTotalSpace G) : shiftPoint (0, p) = p := by
    have hw (i : ℕ) : weight i (shiftPoint (0, p)) = weight i p := by
      cases i <;> simp only [weight_shiftPoint, kept, moved_zero, Set.Icc.coe_zero, sub_zero,
        one_mul, incoming, zero_mul, add_zero]
    exact ext_coord hw fun i hi ↦ by
      rw [label_shiftPoint (mem_coordSet_iff.mp hi), shiftLabel]
      cases i <;> simp only [incoming, moved_zero, Set.Icc.coe_zero, zero_mul, lt_self_iff_false,
        ite_false]
  ContinuousMap.Homotopy.trans ⟨⟨shiftPoint, continuous_shiftPoint⟩, hzero, fun _ ↦ rfl⟩
    (coneAtFreshIndexHomotopy 0 a f hf)

/-- The strong-coordinate Milnor join of any nonempty space is contractible. -/
instance instContractibleSpace [Nonempty G] : ContractibleSpace (MilnorTotalSpace G) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨vertex 0 (Classical.choice ‹Nonempty G›), ⟨contractionToVertex _⟩⟩

end TauCeti.MilnorTotalSpace
