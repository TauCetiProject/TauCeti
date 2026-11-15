/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Piecewise

/-!
# Gluing real functions with matching derivatives at zero

The piecewise function on the nonnegative and negative half-lines preserves derivatives when
the two branches match at zero. Matching jets yield finite-order continuous differentiability.
-/

public section

open Set Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Equal values and derivatives at zero allow gluing the one-sided derivatives. -/
theorem TauCeti.hasDerivAt_if_nonneg {f g f' g' : ℝ → F}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (h₀ : f 0 = g 0) (h₁ : f' 0 = g' 0) (t : ℝ) :
    HasDerivAt (fun t ↦ if 0 ≤ t then f t else g t)
      (if 0 ≤ t then f' t else g' t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · simp only [ite_eq_right ht.not_ge]
    exact (hg t).congr_of_eventuallyEq (by
      filter_upwards [eventually_lt_nhds ht] with x hx
      exact ite_eq_right hx.not_ge)
  · simp only [le_refl, ite_true]
    have hpos : HasDerivWithinAt (fun t ↦ if 0 ≤ t then f t else g t) (f' 0) (Ici 0) 0 :=
      (hf 0).hasDerivWithinAt.congr (fun _ hx ↦ ite_eq_left hx) (ite_eq_left le_rfl)
    have hneg : HasDerivWithinAt (fun t ↦ if 0 ≤ t then f t else g t) (f' 0) (Iic 0) 0 := by
      rw [h₁]
      apply (hg 0).hasDerivWithinAt.congr
      · intro x hx
        by_cases hx' : 0 ≤ x
        · have : x = 0 := le_antisymm hx hx'
          subst x
          simpa using h₀
        · exact ite_eq_right hx'
      · simpa using h₀
    simpa only [Ici_union_Iic, hasDerivWithinAt_univ] using hpos.union hneg
  · simp only [ite_eq_left ht.le]
    exact (hf t).congr_of_eventuallyEq (by
      filter_upwards [eventually_gt_nhds ht] with x hx
      exact ite_eq_left hx.le)

/-- Gluing `Cⁿ` functions with matching jets through order `n`. -/
theorem ContDiff.if_nonneg {n : ℕ} {f g : ℝ → F}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (h : ∀ i ≤ n, iteratedDeriv i f 0 = iteratedDeriv i g 0) :
    ContDiff ℝ n (fun t ↦ if 0 ≤ t then f t else g t) := by
  induction n generalizing f g with
  | zero =>
    apply contDiff_zero.mpr
    apply hf.continuous.if _ hg.continuous
    intro t ht
    -- The branch predicate is the closed half-line; expose that set for its frontier formula.
    have hset : {x : ℝ | 0 ≤ x} = Ici 0 := rfl
    have ht : t = 0 := by simpa only [hset, frontier_Ici, mem_singleton_iff] using ht
    subst t
    exact h 0 le_rfl
  | succ n ih =>
    have hderiv := TauCeti.hasDerivAt_if_nonneg
      (fun t ↦ (hf.differentiable (by simp) t).hasDerivAt)
      (fun t ↦ (hg.differentiable (by simp) t).hasDerivAt)
      (h 0 (by omega)) (by simpa only [iteratedDeriv_one] using h 1 (by omega))
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun t ↦ (hderiv t).differentiableAt, by simp, ?_⟩
    have heq : deriv (fun t ↦ if 0 ≤ t then f t else g t) =
        fun t ↦ if 0 ≤ t then deriv f t else deriv g t := funext fun t ↦ (hderiv t).deriv
    rw [heq]
    apply ih hf.deriv' hg.deriv'
    intro i hi
    simpa only [← iteratedDeriv_succ'] using h (i + 1) (by omega)
