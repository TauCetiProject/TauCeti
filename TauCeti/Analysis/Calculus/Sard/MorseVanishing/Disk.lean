/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Calculus.MeanValue

/-!
# Parametrized disks and flatness along their chords

The mean value estimate raises the order of flatness along a parametrized disk by one.

Adapted from [KLS](https://github.com/human-ai-mathematics/kls-lean) at commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`, `formalization/FunctionalInequalities/Analysis/Sard/`.
The decomposition follows A. Norton, *A critical set with nonnull image has large Hausdorff
dimension*, Trans. Amer. Math. Soc. 296 (1986), Section 4, in its integer-regularity case.
-/

public section

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace TauCeti.MorseSard

variable {n p k : ℕ}

/-- A `C¹` parametrized disk with antilipschitz constant `κ` on the closed unit ball. -/
def IsDisk (φ : (Fin p → ℝ) → (Fin n → ℝ)) (κ : ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ 0 ≤ κ ∧
    ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
      ‖a - b‖ ≤ κ * ‖φ a - φ b‖

/-- `f` is flat of order `k` along the disk `φ` on the set `S`. -/
def FlatAlong (φ : (Fin p → ℝ) → (Fin n → ℝ)) (S : Set (Fin n → ℝ)) (k : ℕ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
      φ a ∈ S → φ b ∈ S → ‖φ a - φ b‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
        |f (φ (a + s • (b - a)))| ≤ ε * ‖φ a - φ (a + s • (b - a))‖ ^ k

/-- The defining regularity and inverse-Lipschitz bound of a parametrized disk. -/
theorem isDisk_iff {φ : (Fin p → ℝ) → (Fin n → ℝ)} {κ : ℝ} :
    IsDisk φ κ ↔ ContDiff ℝ 1 φ ∧ 0 ≤ κ ∧
      ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
        ‖a - b‖ ≤ κ * ‖φ a - φ b‖ := Iff.rfl

/-- The uniform small-oscillation condition defining flatness along a disk. -/
theorem flatAlong_iff {φ : (Fin p → ℝ) → (Fin n → ℝ)} {S : Set (Fin n → ℝ)} {k : ℕ}
    {f : (Fin n → ℝ) → ℝ} :
    FlatAlong φ S k f ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
        φ a ∈ S → φ b ∈ S → ‖φ a - φ b‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
          |f (φ (a + s • (b - a)))| ≤ ε * ‖φ a - φ (a + s • (b - a))‖ ^ k := Iff.rfl

/-- **The mean value step along a `C¹` parametrized disk.**  If every coordinate of `fderiv ℝ f`
is flat of order `k` along the disk on `S`, then the increment of `f` from `φ a` is
`o(‖φ a - φ z‖ ^ (k + 1))` along the parametric segments between points of `S`. -/
theorem abs_sub_le_of_flat_fderiv {φ : (Fin p → ℝ) → (Fin n → ℝ)} {κ : ℝ}
    (hφ : IsDisk φ κ) {S : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    (hflat : ∀ j : Fin n, FlatAlong φ S k fun x => fderiv ℝ f x (Pi.single j (1 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
        φ a ∈ S → φ b ∈ S → ‖φ a - φ b‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
          |f (φ (a + s • (b - a))) - f (φ a)| ≤ ε * ‖φ a - φ (a + s • (b - a))‖ ^ (k + 1) := by
  obtain ⟨hφ1, hκ0, hanti⟩ := hφ
  have hφd : Differentiable ℝ φ := hφ1.differentiable (by simp)
  -- a uniform bound for the differential of `φ` on the closed unit ball
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin p → ℝ) 1).exists_bound_of_continuousOn
    (hφ1.continuous_fderiv (by simp)).continuousOn
  set C' : ℝ := max C 1 with hC'def
  have hC'1 : (1 : ℝ) ≤ C' := le_max_right _ _
  have hC'0 : (0 : ℝ) < C' := lt_of_lt_of_le one_pos hC'1
  have hCC' : ∀ x ∈ closedBall (0 : Fin p → ℝ) 1, ‖fderiv ℝ φ x‖ ≤ C' :=
    fun x hx => (hC x hx).trans (le_max_left _ _)
  set κ' : ℝ := max κ 1 with hκ'def
  have hκ'1 : (1 : ℝ) ≤ κ' := le_max_right _ _
  have hκ'0 : (0 : ℝ) < κ' := lt_of_lt_of_le one_pos hκ'1
  have hanti' : ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
      ‖a - b‖ ≤ κ' * ‖φ a - φ b‖ := fun a ha b hb =>
    (hanti a ha b hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- the constant absorbed by the choice of the inner accuracy
  set M : ℝ := n * C' * κ' * (C' * κ') ^ k with hMdef
  have hM0 : 0 ≤ M := by positivity
  intro ε hε
  set ε' : ℝ := ε / (M + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  choose d hd hdspec using fun j : Fin n => hflat j ε' hε'
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ j, δ ≤ d j := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin n)) with h | h
    · exact ⟨1, one_pos, fun j ↦ absurd (Finset.mem_univ j) (by simp [h])⟩
    · exact ⟨Finset.univ.inf' h d, (Finset.lt_inf'_iff h).mpr fun j _ ↦ hd j,
        fun j ↦ Finset.inf'_le _ (Finset.mem_univ j)⟩
  refine ⟨δ, hδ, ?_⟩
  intro a ha b hb haS hbS hab s hs
  set ρ : ℝ := ‖φ a - φ (a + s • (b - a))‖ with hρdef
  have hnear : ∀ t ∈ Icc (0 : ℝ) s, ‖φ a - φ (a + t • (b - a))‖ ≤ C' * κ' * ρ :=
    fun _ ht ↦ hφd.norm_sub_le_mul_of_segment hCC' hanti' ha hb hs ht
  -- Flatness controls each coordinate derivative along the chord.
  have hcoord : ∀ t ∈ Ico (0 : ℝ) s, ∀ j : Fin n,
      |fderiv ℝ f (φ (a + t • (b - a))) (Pi.single j (1 : ℝ))|
        ≤ ε' * ((C' * κ') ^ k * ρ ^ k) := by
    intro t ht j
    have hflat' := hdspec j a ha b hb haS hbS (lt_of_lt_of_le hab (hδle j)) t
      ⟨ht.1, ht.2.le.trans hs.2⟩
    refine hflat'.trans ?_
    have hle := pow_le_pow_left₀ (norm_nonneg _) (hnear t ⟨ht.1, ht.2.le⟩) k
    calc ε' * ‖φ a - φ (a + t • (b - a))‖ ^ k ≤ ε' * (C' * κ' * ρ) ^ k :=
          mul_le_mul_of_nonneg_left hle hε'.le
      _ = ε' * ((C' * κ') ^ k * ρ ^ k) := by rw [mul_pow]
  set B : ℝ := n * (C' * ‖b - a‖) * (ε' * ((C' * κ') ^ k * ρ ^ k)) with hBdef
  have hmain : |f (φ (a + s • (b - a))) - f (φ a)| ≤ B * s :=
    hφd.abs_sub_le_of_basis_bound hf (by positivity) hCC' ha hb hs hcoord
  refine hmain.trans ?_
  have hsnorm : s * ‖b - a‖ ≤ κ' * ρ := by
    have h1 := hanti' a ha _ ((convex_closedBall (0 : Fin p → ℝ) 1).add_smul_sub_mem ha hb hs)
    have heq : a - (a + s • (b - a)) = -(s • (b - a)) := by module
    simpa only [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] using h1
  -- rearrange into the claimed `ε * ρ ^ (k + 1)` bound
  have hkey : B * s = (n * C' * (C' * κ') ^ k * ε' * ρ ^ k) * (s * ‖b - a‖) := by
    rw [hBdef]; ring
  rw [hkey]
  have hfac : (0 : ℝ) ≤ n * C' * (C' * κ') ^ k * ε' * ρ ^ k := by positivity
  calc (n * C' * (C' * κ') ^ k * ε' * ρ ^ k) * (s * ‖b - a‖)
      ≤ (n * C' * (C' * κ') ^ k * ε' * ρ ^ k) * (κ' * ρ) :=
        mul_le_mul_of_nonneg_left hsnorm hfac
    _ = (M * ε') * ρ ^ (k + 1) := by rw [hMdef]; ring
    _ ≤ ε * ρ ^ (k + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [hε'def]
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hM0, hε.le]

end TauCeti.MorseSard
