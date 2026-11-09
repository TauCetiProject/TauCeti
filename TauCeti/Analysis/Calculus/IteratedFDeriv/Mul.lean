/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Orders of vanishing of products

A function vanishes to order `m` at `x` when its iterated derivatives of every order `i < m`
vanish at `x`. By the Leibniz rule, orders of vanishing add under multiplication: if `g` vanishes
to order `m` and `h` to order `n` at `x`, then `g * h` vanishes to order `m + n` at `x`. This is
the analytic half of the identification of the powers of the ideal of functions vanishing at a
point with the functions whose jets vanish there.
-/

public section

namespace TauCeti

variable {𝕜 E A : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedRing A] [NormedAlgebra 𝕜 A]

/-- **Orders of vanishing add under multiplication.** If the iterated derivatives of `g` of order
`i < m` and those of `h` of order `i < n` vanish at `x`, then so do those of `g * h` of every
order `k < m + n`. -/
theorem iteratedFDeriv_mul_eq_zero_of_lt_add {g h : E → A} {N : WithTop ℕ∞} {x : E}
    (hg : ContDiffAt 𝕜 N g x) (hh : ContDiffAt 𝕜 N h x) {m n k : ℕ}
    (hgx : ∀ i < m, iteratedFDeriv 𝕜 i g x = 0) (hhx : ∀ i < n, iteratedFDeriv 𝕜 i h x = 0)
    (hk : k < m + n) (hkN : k ≤ N) :
    iteratedFDeriv 𝕜 k (fun y ↦ g y * h y) x = 0 := by
  -- Work on an open neighbourhood of `x` on which both factors are `C^k`.
  obtain ⟨u, hu, hxu, hgu⟩ := hg.contDiffOn' hkN (by simp)
  obtain ⟨v, hv, hxv, hhv⟩ := hh.contDiffOn' hkN (by simp)
  have hs : IsOpen (u ∩ v) := hu.inter hv
  have hxs : x ∈ u ∩ v := ⟨hxu, hxv⟩
  have hbound := norm_iteratedFDerivWithin_mul_le
    (hgu.mono fun y (hy : y ∈ u ∩ v) ↦ ⟨Set.mem_insert_of_mem _ trivial, hy.1⟩)
    (hhv.mono fun y (hy : y ∈ u ∩ v) ↦ ⟨Set.mem_insert_of_mem _ trivial, hy.2⟩)
    hs.uniqueDiffOn hxs le_rfl
  simp only [iteratedFDerivWithin_of_isOpen _ hs hxs] at hbound
  refine norm_le_zero_iff.mp (hbound.trans ?_)
  -- Each Leibniz term has a factor `D^i g x` with `i < m` or `D^(k-i) h x` with `k - i < n`.
  refine (Finset.sum_eq_zero fun i hi ↦ ?_).le
  rw [Finset.mem_range] at hi
  rcases lt_or_ge i m with him | him
  · simp [hgx i him]
  · simp [hhx (k - i) (by omega)]

end TauCeti
