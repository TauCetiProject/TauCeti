/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.MeasureTheory.Integral.DivergenceTheorem.CompactSupport
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Divergence on the coordinate quadrant

The closed coordinate quadrant `Set.Ici 0 = {x | ∀ i, 0 ≤ x i}` of `Fin (n + 1) → ℝ` is the
local model of a manifold with corners. Its boundary is the union of the faces `x i = 0`,
each parametrized by the quadrant one dimension down through `Fin.insertNth i 0`.

For a compactly supported field that is `C¹` on the closed quadrant, the divergence integral is
minus the sum of the normal components over all the faces: the outward normal of the face
`x i = 0` is `-eᵢ`. Compact support eliminates every far face of a sufficiently
large bounding box, which specializes Mathlib's
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`. Only regularity on the closed
quadrant is required.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 16.25 (Stokes' theorem on
  manifolds with corners), whose local computation in the quadrant this is.
-/

public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `i`-th component of a field along the face `x i = 0` of the quadrant, parametrized by the
quadrant one dimension down, is integrable when it vanishes outside a cube `[0, R]ⁿ`, and its
integral over the face is the integral over that cube. -/
private lemma integrableOn_and_setIntegral_face_quadrant {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → F)} (hf : ContDiffOn ℝ 1 f (Ici 0)) {R : ℝ}
    (i : Fin (n + 1)) (hzero : ∀ y ∈ Ici (0 : Fin n → ℝ), y ∉ Icc 0 (fun _ ↦ R) →
      f (i.insertNth 0 y) i = 0) :
    IntegrableOn (fun y : Fin n → ℝ ↦ f (i.insertNth 0 y) i) (Ici 0) ∧
      (∫ y in Icc 0 fun _ ↦ R, f (i.insertNth 0 y) i) = ∫ y in Ici 0, f (i.insertNth 0 y) i := by
  have hface {y : Fin n → ℝ} (hy : 0 ≤ y) : i.insertNth 0 y ∈ Ici (0 : Fin (n + 1) → ℝ) := by
    intro j
    refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j
    · simp
    · simpa using hy k
  have hi : IntegrableOn (fun y : Fin n → ℝ ↦ f (i.insertNth 0 y) i) (Icc 0 fun _ ↦ R) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine (continuous_apply i).comp_continuousOn (hf.continuousOn.comp ?_ ?_)
    · exact (continuous_const.finInsertNth (A := fun _ ↦ ℝ) i continuous_id).continuousOn
    · exact fun y hy ↦ hface hy.1
  exact ⟨hi.of_forall_sdiff_eq_zero measurableSet_Ici fun y hy ↦ hzero y hy.1 hy.2,
    (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
      (s := Icc 0 fun _ ↦ R) (fun _ hy ↦ hy.1) fun y hy ↦ hzero y hy.1 hy.2).symm⟩

/-- Compactly supported `C¹` fields on the closed coordinate quadrant satisfy the divergence
theorem: the divergence integral is minus the sum, over the faces `x i = 0`, of the integral of
the `i`-th component over the face, parametrized by the quadrant one dimension down. Both the
divergence and every face integrand are integrable. -/
theorem _root_.ContDiffOn.integral_divergence_coordinate_quadrant {n : ℕ}
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → F)}
    (hf : ContDiffOn ℝ 1 f (Ici 0)) (hc : HasCompactSupport f) :
    IntegrableOn (fun x ↦ ∑ i : Fin (n + 1),
      fderivWithin ℝ f (Ici 0) x (Pi.single i 1) i) (Ici 0) ∧
      (∀ i : Fin (n + 1), IntegrableOn (fun y : Fin n → ℝ ↦ f (i.insertNth 0 y) i) (Ici 0)) ∧
      (∫ x in Ici 0, ∑ i : Fin (n + 1),
        fderivWithin ℝ f (Ici 0) x (Pi.single i 1) i) =
          -∑ i : Fin (n + 1), ∫ y in Ici 0, f (i.insertNth 0 y) i := by
  let Q : Set (Fin (n + 1) → ℝ) := Ici 0
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_lt
  let b : Fin (n + 1) → ℝ := fun _ ↦ R
  have hab : (0 : Fin (n + 1) → ℝ) ≤ b := fun _ ↦ hR.le
  have hKQ : Icc 0 b ⊆ Q := fun _ hx ↦ hx.1
  have hQm : MeasurableSet Q := measurableSet_Ici
  have hmem {m : ℕ} {x : Fin m → ℝ} (hx : 0 ≤ x) (hn : ‖x‖ < R) : x ∈ Icc 0 fun _ ↦ R :=
    ⟨hx, fun j ↦ (le_abs_self (x j)).trans (lt_of_le_of_lt (norm_le_pi_norm x j) hn).le⟩
  -- The field vanishes at every point with a coordinate of absolute value at least `R`.
  have hzero {x : Fin (n + 1) → ℝ} (j : Fin (n + 1)) (hj : R ≤ |x j|) : f x = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun hx ↦ ?_
    have := lt_of_le_of_lt (norm_le_pi_norm x j) (hbound x hx)
    rw [Real.norm_eq_abs] at this
    exact this.not_ge hj
  have huniq : UniqueDiffOn ℝ Q := TauCeti.uniqueDiffOn_pi_Ici 0
  obtain ⟨hDi, hDI, hDiEq⟩ := hf.integrableOn_divergence_and_setIntegral_eq_Icc huniq hQm hKQ
    fun x hx hx' ↦ hmem hx (hbound x hx')
  -- Each face integrand vanishes on the face quadrant outside `[0, R]ⁿ`.
  have hfacezero (i : Fin (n + 1)) (y : Fin n → ℝ) (hy : y ∈ Ici 0)
      (hk : y ∉ Icc 0 fun _ ↦ R) : f (i.insertNth 0 y) i = 0 := by
    have hn : ¬ ‖y‖ < R := fun hn ↦ hk (hmem hy hn)
    obtain ⟨j, hj⟩ : ∃ j, R ≤ |y j| := by
      by_contra! h
      exact hn ((pi_norm_lt_iff hR).2 fun j ↦ by simpa [Real.norm_eq_abs] using h j)
    have := hzero (x := i.insertNth 0 y) (i.succAbove j)
      (by simpa only [Fin.insertNth_apply_succAbove] using hj)
    simp [this]
  have hface (i : Fin (n + 1)) :=
    integrableOn_and_setIntegral_face_quadrant hf i (hfacezero i)
  -- The far faces of the box lie outside the support.
  have hupper (i : Fin (n + 1)) (y : Fin n → ℝ) : f (i.insertNth (b i) y) i = 0 := by
    rw [hzero i (by simp [b, abs_of_pos hR]), Pi.zero_apply]
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable 0 b hab f
    (fderivWithin ℝ f Q) ∅ countable_empty (hf.continuousOn.mono hKQ) (fun x hx ↦ by
      have hopen : IsOpen (Set.pi univ fun _ : Fin (n + 1) ↦ Ioi (0 : ℝ)) :=
        isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioi
      have hn : Q ∈ 𝓝 x := mem_of_superset
        (hopen.mem_nhds fun i _ ↦ (hx.1 i (mem_univ _)).1) fun y hy i ↦ (hy i (mem_univ _)).le
      exact ((hf.differentiableOn one_ne_zero) x (mem_of_mem_nhds hn)).hasFDerivWithinAt
        |>.hasFDerivAt hn)
    hDi
  refine ⟨hDI, fun i ↦ (hface i).1, ?_⟩
  rw [hDiEq, hdiv, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [hupper, integral_zero, zero_sub, Pi.zero_apply]
  exact congrArg Neg.neg (hface i).2

end MeasureTheory
