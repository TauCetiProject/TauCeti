/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Maps from the circle into a simply connected space are null-homotopic

A continuous map `f : AddCircle p → X` (with `0 < p`) is read as the based loop
`t ↦ f (t * p)` on the unit interval. When `X` is simply connected this loop is homotopic to the
constant loop relative to its endpoints, and such a homotopy descends along the quotient map
`I × I → I × AddCircle p`, `(s, t) ↦ (s, t * p)`, because it is constant on the two ends
`t = 0` and `t = 1`, which are the only points identified. The descended map is a free
null-homotopy of `f` (`ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`).

Mathlib's `SimplyConnectedSpace` is phrased with based paths; this file supplies its consequence
for free loops parametrised by the circle, which is how circles are compared in conditions such as
simple connectivity at infinity.

## Main declarations

* `ContinuousMap.nullhomotopic_addCircle_of_simplyConnectedSpace`: every continuous map from a
  circle `AddCircle p` with `0 < p` into a simply connected space is null-homotopic.
-/

public section

noncomputable section

open Set Topology
open scoped unitInterval

namespace ContinuousMap

variable {p : ℝ} {X : Type*} [TopologicalSpace X]

/-- The map `t ↦ t * p` from the unit interval onto `AddCircle p`, winding once around. -/
private def unitIntervalToAddCircle (p : ℝ) : C(I, AddCircle p) :=
  ⟨fun t => ((t * p : ℝ) : AddCircle p), by fun_prop⟩

private theorem unitIntervalToAddCircle_apply (t : I) :
    unitIntervalToAddCircle p t = ((t * p : ℝ) : AddCircle p) :=
  rfl

private theorem unitIntervalToAddCircle_zero : unitIntervalToAddCircle p 0 = 0 := by
  simp [unitIntervalToAddCircle_apply]

private theorem unitIntervalToAddCircle_one : unitIntervalToAddCircle p 1 = 0 := by
  simp [unitIntervalToAddCircle_apply]

private theorem surjective_unitIntervalToAddCircle [hp : Fact (0 < p)] :
    Function.Surjective (unitIntervalToAddCircle p) := by
  intro θ
  obtain ⟨⟨x, hx₀, hx₁⟩, hx⟩ : ∃ x : Ico (0 : ℝ) (0 + p), (x : AddCircle p) = θ :=
    ⟨AddCircle.equivIco p 0 θ, AddCircle.coe_equivIco⟩
  rw [zero_add] at hx₁
  refine ⟨⟨x / p, div_nonneg hx₀ hp.out.le, (div_le_one hp.out).2 hx₁.le⟩, ?_⟩
  rw [unitIntervalToAddCircle_apply, ← hx, div_mul_cancel₀ x hp.out.ne']

/-- Two points of the unit interval have the same image in the circle exactly when they are equal
or are the two endpoints. -/
private theorem eq_or_of_unitIntervalToAddCircle_eq [hp : Fact (0 < p)] {s t : I}
    (h : unitIntervalToAddCircle p s = unitIntervalToAddCircle p t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  rw [unitIntervalToAddCircle_apply, unitIntervalToAddCircle_apply] at h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (QuotientAddGroup.eq.1 h)
  rw [zsmul_eq_mul, ← sub_eq_neg_add, ← sub_mul] at hk
  have hk' : (k : ℝ) = t - s := mul_right_cancel₀ hp.out.ne' hk
  obtain ⟨hs₀, hs₁⟩ := s.2
  obtain ⟨ht₀, ht₁⟩ := t.2
  have hlo : -1 < (k : ℝ) + 1 := by linarith
  have hhi : (k : ℝ) - 1 < 1 := by linarith
  have hk_lo : -1 ≤ k := by exact_mod_cast (show (-1 : ℝ) ≤ k by linarith)
  have hk_hi : k ≤ 1 := by exact_mod_cast (show (k : ℝ) ≤ 1 by linarith)
  obtain rfl | rfl | rfl : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  · refine Or.inr (Or.inr ⟨Subtype.ext ?_, Subtype.ext ?_⟩) <;>
      · push_cast at hk'
        simp only [Icc.coe_one, Icc.coe_zero]
        linarith
  · exact Or.inl (Subtype.ext (by push_cast at hk'; linarith))
  · refine Or.inr (Or.inl ⟨Subtype.ext ?_, Subtype.ext ?_⟩) <;>
      · push_cast at hk'
        simp only [Icc.coe_one, Icc.coe_zero]
        linarith

/-- A map from the circle read as a based loop at the image of `0`. -/
private def toLoop (f : C(AddCircle p, X)) : Path (f 0) (f 0) where
  toContinuousMap := f.comp (unitIntervalToAddCircle p)
  source' := by simp [unitIntervalToAddCircle_zero]
  target' := by simp [unitIntervalToAddCircle_one]

/-- **Every map from a circle into a simply connected space is null-homotopic.** -/
theorem nullhomotopic_addCircle_of_simplyConnectedSpace [Fact (0 < p)] [SimplyConnectedSpace X]
    (f : C(AddCircle p, X)) : f.Nullhomotopic := by
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic (toLoop f) (Path.refl (f 0))
  -- Descend the path homotopy `F` along `(s, t) ↦ (s, t * p)`, which only glues the two ends of
  -- the loop parameter, where `F` takes the value `f 0`.
  let q : C(I × I, I × AddCircle p) := (ContinuousMap.id I).prodMap (unitIntervalToAddCircle p)
  have hsurj : Function.Surjective q :=
    Function.surjective_id.prodMap surjective_unitIntervalToAddCircle
  have hq : IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous hsurj
  have hF : Function.FactorsThrough (F.toContinuousMap : I × I → X) q := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ h
    obtain ⟨rfl, h⟩ := Prod.ext_iff.1 h
    obtain rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := eq_or_of_unitIntervalToAddCircle_eq h
    · rfl
    · exact (F.source s).trans (F.target s).symm
    · exact (F.target s).trans (F.source s).symm
  have hG (s t : I) : hq.lift F.toContinuousMap hF (s, unitIntervalToAddCircle p t) = F (s, t) :=
    DFunLike.congr_fun (hq.lift_comp F.toContinuousMap hF) (s, t)
  refine ⟨f 0, ⟨⟨hq.lift F.toContinuousMap hF, fun θ => ?_, fun θ => ?_⟩⟩⟩ <;>
    obtain ⟨t, rfl⟩ := surjective_unitIntervalToAddCircle (p := p) θ
  · exact (hG 0 t).trans (F.apply_zero t)
  · exact (hG 1 t).trans (F.apply_one t)

end ContinuousMap
