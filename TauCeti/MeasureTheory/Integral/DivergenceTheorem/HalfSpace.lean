/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import TauCeti.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Divergence on a coordinate half-space

Compact support eliminates every face of a sufficiently large bounding box except the face at
coordinate zero. This specializes Mathlib's
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` to a bounding box containing
the support. Only regularity on the closed half-space is required.
-/

public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

/-- Compactly supported `C¹` fields on the closed coordinate half-space satisfy the divergence
theorem with the outward normal `-e₀`. Both actual integrability statements are included. -/
theorem _root_.ContDiffOn.integral_divergence_coordinate_halfSpace {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)}
    (hf : ContDiffOn ℝ 1 f {x | 0 ≤ x 0}) (hc : HasCompactSupport f) :
    IntegrableOn (fun x ↦ ∑ i : Fin (n + 1),
      fderivWithin ℝ f {y | 0 ≤ y 0} x (Pi.single i 1) i) {x | 0 ≤ x 0} ∧
      Integrable (fun y : Fin n → ℝ ↦ f (Fin.cons 0 y) 0) ∧
      (∫ x in {x | 0 ≤ x 0}, ∑ i : Fin (n + 1),
        fderivWithin ℝ f {y | 0 ≤ y 0} x (Pi.single i 1) i) =
          -(∫ y : Fin n → ℝ, f (Fin.cons 0 y) 0) := by
  let H : Set (Fin (n + 1) → ℝ) := {x | 0 ≤ x 0}
  let D (x : Fin (n + 1) → ℝ) :=
    ∑ i : Fin (n + 1), fderivWithin ℝ f H x (Pi.single i 1) i
  have hH : MeasurableSet H := isClosed_le continuous_const (continuous_apply 0) |>.measurableSet
  have huniq : UniqueDiffOn ℝ H := TauCeti.uniqueDiffOn_pi_halfSpace 0 0
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  let a : Fin (n + 1) → ℝ := Fin.cons 0 (fun _ ↦ -R)
  let b : Fin (n + 1) → ℝ := fun _ ↦ R
  have hab : a ≤ b := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [a, b, hR.le, neg_le_self hR.le]
  have hKH : Icc a b ⊆ H := fun x hx ↦ hx.1 0
  have hmem {x : Fin (n + 1) → ℝ} (hx : x ∈ H) (hn : ‖x‖ < R) : x ∈ Icc a b := by
    have hj (j : Fin (n + 1)) : |x j| < R :=
      lt_of_le_of_lt (norm_le_pi_norm x j) hn
    refine ⟨fun i ↦ ?_, fun i ↦ (abs_lt.mp (hj i)).2.le⟩
    refine Fin.cases hx (fun j ↦ ?_) i
    exact (abs_lt.mp (hj j.succ)).1.le
  have hout {x : Fin (n + 1) → ℝ} (hx : x ∈ H) (hk : x ∉ Icc a b) : R ≤ ‖x‖ :=
    le_of_not_gt fun hn ↦ hk (hmem hx hn)
  have hzero {x : Fin (n + 1) → ℝ} (hn : R ≤ ‖x‖) : f x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hx ↦ (hbound x hx).not_ge hn
  have hDzero {x : Fin (n + 1) → ℝ} (hx : x ∈ H) (hk : x ∉ Icc a b) : D x = 0 := by
    have hn : x ∉ tsupport f := fun hx' ↦ (hbound x hx').not_ge (hout hx hk)
    have hd := (HasFDerivWithinAt.of_notMem_tsupport ℝ (s := H) hn).fderivWithin (huniq x hx)
    simp [D, hd]
  have hDc : ContinuousOn D H := by
    apply continuousOn_finsetSum
    intro i _
    exact (continuous_apply i).comp_continuousOn
      ((hf.continuousOn_fderivWithin huniq (by simp)).clm_apply continuousOn_const)
  have hDi : IntegrableOn D (Icc a b) :=
    (hDc.mono hKH).integrableOn_compact isCompact_Icc
  have hDI : IntegrableOn D H := hDi.of_forall_sdiff_eq_zero hH fun x hx ↦ hDzero hx.1 hx.2
  have hDiEq : (∫ x in H, D x) = ∫ x in Icc a b, D x :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hH hKH fun x hx ↦ hDzero hx.1 hx.2
  have hbc : Continuous (fun y : Fin n → ℝ ↦ f (Fin.cons 0 y) 0) := by
    apply (continuous_apply 0).comp
    apply hf.continuousOn.comp_continuous
    · fun_prop
    · intro y
      simp
  let B : Set (Fin n → ℝ) := Icc (fun _ ↦ -R) (fun _ ↦ R)
  have hbzero {y : Fin n → ℝ} (hy : y ∉ B) : f (Fin.cons 0 y) 0 = 0 := by
    have hk : Fin.cons 0 y ∉ Icc a b := by
      intro hk
      apply hy
      exact ⟨fun i ↦ hk.1 i.succ, fun i ↦ hk.2 i.succ⟩
    exact congrFun (hzero (hout (by simp [H]) hk)) 0
  have hB : IsCompact B := isCompact_Icc
  have hbi : Integrable (fun y : Fin n → ℝ ↦ f (Fin.cons 0 y) 0) :=
    (hbc.continuousOn.integrableOn_compact hB)
      |>.integrable_of_forall_notMem_eq_zero fun _ hy ↦ hbzero hy
  have hbEq : (∫ y in B, f (Fin.cons 0 y) 0) = ∫ y : Fin n → ℝ, f (Fin.cons 0 y) 0 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun _ hy ↦ hbzero hy
  have hupper (i : Fin (n + 1)) (y : Fin n → ℝ) : f (i.insertNth (b i) y) i = 0 := by
    apply congrFun (hzero ?_) i
    have hn := norm_le_pi_norm (i.insertNth (α := fun _ ↦ ℝ) (b i) y) i
    simpa only [Fin.insertNth_apply_same, b, Real.norm_eq_abs, abs_of_pos hR] using hn
  have hlower (i : Fin n) (y : Fin n → ℝ) : f (i.succ.insertNth (a i.succ) y) i.succ = 0 := by
    apply congrFun (hzero ?_) i.succ
    have hn := norm_le_pi_norm (i.succ.insertNth (α := fun _ ↦ ℝ) (a i.succ) y) i.succ
    simpa only [Fin.insertNth_apply_same, a, Fin.cons_succ, Real.norm_eq_abs,
      abs_neg, abs_of_pos hR] using hn
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable a b hab f
    (fderivWithin ℝ f H) ∅ countable_empty (hf.continuousOn.mono hKH) (fun x hx ↦ by
      have hx0 : 0 < x 0 := (hx.1 0 (mem_univ _)).1
      have hn : H ∈ 𝓝 x := mem_of_superset
        ((isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hx0) fun y hy ↦ hy.le
      exact ((hf.differentiableOn one_ne_zero) x hx0.le).hasFDerivWithinAt.hasFDerivAt hn)
    hDi
  refine ⟨hDI, hbi, ?_⟩
  rw [hDiEq]
  -- Fold the coordinate trace into D so the bounding-box identity matches the integral.
  change (∫ x in Icc a b, D x) = _ at hdiv
  rw [hdiv]
  simp only [Fin.sum_univ_succ, hupper, hlower, integral_zero, zero_sub, neg_zero,
    Finset.sum_const_zero, add_zero]
  simpa [a, b, B, Function.comp_def, Fin.insertNth_zero] using congrArg Neg.neg hbEq

end MeasureTheory
