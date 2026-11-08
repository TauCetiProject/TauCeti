/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.MeanValue

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
@[expose] def IsDisk (φ : (Fin p → ℝ) → (Fin n → ℝ)) (κ : ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ 0 ≤ κ ∧
    ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
      ‖a - b‖ ≤ κ * ‖φ a - φ b‖

/-- `f` is flat of order `k` along the disk `φ` on the set `S`. -/
@[expose] def FlatAlong (φ : (Fin p → ℝ) → (Fin n → ℝ)) (S : Set (Fin n → ℝ)) (k : ℕ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
      φ a ∈ S → φ b ∈ S → ‖φ a - φ b‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
        |f (φ (a + s • (b - a)))| ≤ ε * ‖φ a - φ (a + s • (b - a))‖ ^ k

/-- A finite family of positive reals is bounded below by a positive real. -/
private lemma exists_pos_le {ι : Type*} [Finite ι] (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ d i := by
  classical
  let := Fintype.ofFinite ι
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset ι) with h | h
  · exact ⟨1, one_pos, fun i => absurd (Finset.mem_univ i) (by simp [h])⟩
  · exact ⟨Finset.univ.inf' h d, (Finset.lt_inf'_iff h).mpr fun i _ => hd i,
      fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩

/-- A functional on `Fin n → ℝ` bounded on the basis vectors is bounded. -/
private lemma abs_apply_le (L : (Fin n → ℝ) →L[ℝ] ℝ) (v : Fin n → ℝ) {M : ℝ}
    (h : ∀ j, |L (Pi.single j (1 : ℝ))| ≤ M) : |L v| ≤ n * ‖v‖ * M := by
  have hv : v = ∑ j : Fin n, v j • Pi.single j (1 : ℝ) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  calc |L v| = |∑ j : Fin n, v j * L (Pi.single j (1 : ℝ))| := by
        conv_lhs => rw [hv]
        simp [map_sum, smul_eq_mul]
    _ ≤ ∑ j : Fin n, |v j * L (Pi.single j (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ‖v‖ * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j) (h j)
          (abs_nonneg _) (norm_nonneg _)
    _ = n * ‖v‖ * M := by simp [Finset.sum_const, mul_assoc]

private theorem segment_mem_closedBall {a b : Fin p → ℝ}
    (ha : a ∈ closedBall (0 : Fin p → ℝ) 1) (hb : b ∈ closedBall (0 : Fin p → ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : a + t • (b - a) ∈ closedBall (0 : Fin p → ℝ) 1 := by
  have heq : a + t • (b - a) = (1 - t) • a + t • b := by module
  rw [heq]
  exact convex_closedBall (0 : Fin p → ℝ) 1 ha hb (by linarith [ht.2]) ht.1 (by ring)

/-- A chord in parameter space remains uniformly close in the image to its initial point,
relative to the distance from that point to a prescribed intermediate point. -/
private theorem norm_sub_le_mul_of_segment {φ : (Fin p → ℝ) → (Fin n → ℝ)}
    (hφd : Differentiable ℝ φ) {C κ : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ closedBall (0 : Fin p → ℝ) 1, ‖fderiv ℝ φ x‖ ≤ C)
    (hanti : ∀ a ∈ closedBall (0 : Fin p → ℝ) 1, ∀ b ∈ closedBall (0 : Fin p → ℝ) 1,
      ‖a - b‖ ≤ κ * ‖φ a - φ b‖)
    {a b : Fin p → ℝ} (ha : a ∈ closedBall (0 : Fin p → ℝ) 1)
    (hb : b ∈ closedBall (0 : Fin p → ℝ) 1) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) s) :
    ‖φ a - φ (a + t • (b - a))‖ ≤ C * κ * ‖φ a - φ (a + s • (b - a))‖ := by
  have hsnorm : s * ‖b - a‖ ≤ κ * ‖φ a - φ (a + s • (b - a))‖ := by
    have h1 := hanti a ha _ (segment_mem_closedBall ha hb hs)
    have heq : a - (a + s • (b - a)) = -(s • (b - a)) := by module
    simpa only [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] using h1
  have hconv := convex_closedBall (0 : Fin p → ℝ) 1
  have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x _ ↦ (hφd x).hasFDerivAt.hasFDerivWithinAt) hbound ha
      (segment_mem_closedBall ha hb ⟨ht.1, ht.2.trans hs.2⟩)
  have heq : (a + t • (b - a)) - a = t • (b - a) := by module
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hmv
  rw [norm_sub_rev]
  refine hmv.trans ?_
  have htnorm : t * ‖b - a‖ ≤ κ * ‖φ a - φ (a + s • (b - a))‖ :=
    (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans hsnorm
  calc C * (t * ‖b - a‖) ≤ C * (κ * ‖φ a - φ (a + s • (b - a))‖) :=
        mul_le_mul_of_nonneg_left htnorm hC
    _ = C * κ * ‖φ a - φ (a + s • (b - a))‖ := by ring

/-- The one-variable mean value estimate on a parametrized chord, using bounds on the
coordinate derivatives of the scalar function and on the derivative of the parametrization. -/
private theorem abs_sub_le_of_basis_bound {φ : (Fin p → ℝ) → (Fin n → ℝ)}
    (hφd : Differentiable ℝ φ) {f : (Fin n → ℝ) → ℝ} (hf : Differentiable ℝ f)
    {C D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ x ∈ closedBall (0 : Fin p → ℝ) 1, ‖fderiv ℝ φ x‖ ≤ C)
    {a b : Fin p → ℝ} (ha : a ∈ closedBall (0 : Fin p → ℝ) 1)
    (hb : b ∈ closedBall (0 : Fin p → ℝ) 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hcoord : ∀ t ∈ Ico (0 : ℝ) s, ∀ j : Fin n,
      |fderiv ℝ f (φ (a + t • (b - a))) (Pi.single j (1 : ℝ))| ≤ D) :
    |f (φ (a + s • (b - a))) - f (φ a)| ≤ n * (C * ‖b - a‖) * D * s := by
  let g : ℝ → ℝ := fun t ↦ f (φ (a + t • (b - a)))
  let g' : ℝ → ℝ := fun t ↦
    fderiv ℝ f (φ (a + t • (b - a))) (fderiv ℝ φ (a + t • (b - a)) (b - a))
  have hcurve (t : ℝ) : HasDerivAt (fun t : ℝ ↦ a + t • (b - a)) (b - a) t := by
    simpa using ((hasDerivAt_id t).smul_const (b - a)).const_add a
  have hgd (t : ℝ) : HasDerivAt g (g' t) t :=
    (hf _).hasFDerivAt.comp_hasDerivAt t
      ((hφd _).hasFDerivAt.comp_hasDerivAt t (hcurve t))
  have hderiv : ∀ t ∈ Ico (0 : ℝ) s, ‖g' t‖ ≤ n * (C * ‖b - a‖) * D := by
    intro t ht
    have hvnorm : ‖fderiv ℝ φ (a + t • (b - a)) (b - a)‖ ≤ C * ‖b - a‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right
          (hbound _ (segment_mem_closedBall ha hb ⟨ht.1, ht.2.le.trans hs.2⟩)) (norm_nonneg _))
    exact (abs_apply_le _ _ (hcoord t ht)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvnorm (Nat.cast_nonneg n)) hD)
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t _ ↦ (hgd t).hasDerivWithinAt) hderiv s (right_mem_Icc.mpr hs.1)
  simpa only [g, zero_smul, add_zero, sub_zero, Real.norm_eq_abs] using hmain

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
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le d hd
  refine ⟨δ, hδ, ?_⟩
  intro a ha b hb haS hbS hab s hs
  set ρ : ℝ := ‖φ a - φ (a + s • (b - a))‖ with hρdef
  have hnear : ∀ t ∈ Icc (0 : ℝ) s, ‖φ a - φ (a + t • (b - a))‖ ≤ C' * κ' * ρ :=
    fun _ ht ↦ norm_sub_le_mul_of_segment hφd hC'0.le hCC' hanti' ha hb hs ht
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
    abs_sub_le_of_basis_bound hφd hf (by positivity) hCC' ha hb hs hcoord
  refine hmain.trans ?_
  have hsnorm : s * ‖b - a‖ ≤ κ' * ρ := by
    have h1 := hanti' a ha _ (segment_mem_closedBall ha hb hs)
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
