/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Ray
public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.Convex.TriangleEquality
import TauCeti.Analysis.Contour.Residue.Germ
import TauCeti.Analysis.Meromorphic.Order

/-!
# Noncancellation of simple poles in finite sums

If finitely many meromorphic functions have at most simple poles at a point, and their residues
lie on a common ray, their sum has a pole exactly when a summand does. For a sum with nonnegative
real weights, only the summands of positive weight contribute to the pole set. This is used when
summing Mellin transforms of Riesz remainders: at a given zero the individual residues are
nonnegative multiples of the same complex factor.

The application to weighted families of Dirichlet characters is from `Deduction.poleData` in
Levent Alpöge's formalization: <https://github.com/leanprover-community/riemann-hypothesis>.
-/

public section

open scoped Function

namespace TauCeti.Contour

/-- A finite sum of functions with at most simple poles at `z` has a pole at `z` if and only
if some summand does, provided the residues there lie on a common closed ray. -/
theorem meromorphicOrderAt_sum_lt_zero_iff_of_pairwise_sameRay {ι : Type*} {s : Finset ι}
    {f : ι → ℂ → ℂ} {z : ℂ} (hf : ∀ i ∈ s, MeromorphicAt (f i) z)
    (hord : ∀ i ∈ s, -1 ≤ meromorphicOrderAt (f i) z)
    (hr : (s : Set ι).Pairwise (SameRay ℝ on fun i ↦ residue (f i) z)) :
    meromorphicOrderAt (∑ i ∈ s, f i) z < 0 ↔ ∃ i ∈ s, meromorphicOrderAt (f i) z < 0 := by
  have hpole i (hi : i ∈ s) := meromorphicOrderAt_lt_zero_iff_residue_ne_zero (hf i hi) (hord i hi)
  rw [meromorphicOrderAt_lt_zero_iff_residue_ne_zero (MeromorphicAt.sum hf)
    (le_meromorphicOrderAt_sum hf hord), residue_sum s hf]
  constructor
  · intro hsum
    obtain ⟨i, hi, hres⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    exact ⟨i, hi, (hpole i hi).2 hres⟩
  · rintro ⟨i, hi, hp⟩
    exact sum_ne_zero_of_pairwise_sameRay hr hi ((hpole i hi).1 hp)

/-- For nonnegative weights and residues on a common closed ray, the poles of a weighted sum
of functions with at most simple poles come exactly from the summands of positive weight. -/
theorem meromorphicOrderAt_sum_smul_lt_zero_iff_of_pairwise_sameRay {ι : Type*} {s : Finset ι}
    {f : ι → ℂ → ℂ} {w : ι → ℝ} {z : ℂ} (hf : ∀ i ∈ s, MeromorphicAt (f i) z)
    (hord : ∀ i ∈ s, -1 ≤ meromorphicOrderAt (f i) z) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hr : (s : Set ι).Pairwise (SameRay ℝ on fun i ↦ residue (f i) z)) :
    meromorphicOrderAt (∑ i ∈ s, (w i : ℂ) • f i) z < 0 ↔
      ∃ i ∈ s, 0 < w i ∧ meromorphicOrderAt (f i) z < 0 := by
  have horder i (hwi : w i ≠ 0) :
      meromorphicOrderAt ((w i : ℂ) • f i) z = meromorphicOrderAt (f i) z :=
    meromorphicOrderAt_const_smul_eq_meromorphicOrderAt (Complex.ofReal_ne_zero.mpr hwi)
  have hscaled i (hi : i ∈ s) : -1 ≤ meromorphicOrderAt ((w i : ℂ) • f i) z := by
    by_cases hwi : w i = 0
    · simp [hwi]
    · rw [horder i hwi]
      exact hord i hi
  rw [meromorphicOrderAt_sum_lt_zero_iff_of_pairwise_sameRay
    (fun i hi ↦ (hf i hi).const_smul _) hscaled]
  · refine exists_congr fun i ↦ and_congr_right fun hi ↦ ?_
    by_cases hwi : w i = 0
    · simp [hwi]
    · rw [horder i hwi, and_iff_right (lt_of_le_of_ne (hw i hi) (Ne.symm hwi))]
  · intro i hi j hj hij
    simp only [Function.onFun, residue_const_smul, smul_eq_mul, ← Complex.real_smul]
    exact ((hr hi hj hij).nonneg_smul_left (hw i hi)).nonneg_smul_right (hw j hj)

end TauCeti.Contour
