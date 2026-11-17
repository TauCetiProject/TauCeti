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
Within a set, one-sided derivatives of two branches which match at the gluing point glue to a
derivative of the piecewise function (`TauCeti.hasDerivWithinAt_if_le`), and three solutions of an
equation `x' = v t x` on consecutive intervals glue to a solution
(`TauCeti.hasDerivWithinAt_if_le_if_le`).
-/

public section

open Set Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Gluing one-sided derivatives within a set.** Let `f` have derivative `f'` within
`s ∩ Iic c` at `t` if `t ≤ c`, and `g` have derivative `g'` within `s ∩ Ici c` at `t` if `c ≤ t`,
the values and the derivatives agreeing if `t = c`. Then the function equal to `f` on `Iic c` and
to `g` elsewhere has derivative `f'` or `g'` within `s` at `t`. -/
theorem TauCeti.hasDerivWithinAt_if_le {f g : ℝ → F} {f' g' : F} {s : Set ℝ} {c t : ℝ}
    (hf : t ≤ c → HasDerivWithinAt f f' (s ∩ Iic c) t)
    (hg : c ≤ t → HasDerivWithinAt g g' (s ∩ Ici c) t) (h₀ : t = c → f c = g c)
    (h₁ : t = c → f' = g') :
    HasDerivWithinAt (fun y ↦ if y ≤ c then f y else g y) (if t ≤ c then f' else g') s t := by
  have hhf : EqOn (fun y ↦ if y ≤ c then f y else g y) f (Iic c) := fun y hy ↦ ite_eq_left hy
  rcases lt_trichotomy t c with htc | rfl | htc
  · rw [ite_eq_left htc.le]
    exact ((hf htc.le).congr (hhf.mono inter_subset_right) (hhf htc.le)).mono_of_mem_nhdsWithin
      (inter_mem_nhdsWithin s (Iic_mem_nhds htc))
  · have hhg : EqOn (fun y ↦ if y ≤ t then f y else g y) g (Ici t) := fun y hy ↦ by
      rcases hy.eq_or_lt with rfl | hlt
      · simpa using h₀ rfl
      · exact ite_eq_right hlt.not_ge
    rw [ite_eq_left le_rfl,
      show s = s ∩ Iic t ∪ s ∩ Ici t by rw [← inter_union_distrib_left, Iic_union_Ici, inter_univ]]
    refine ((hf le_rfl).congr (hhf.mono inter_subset_right) (hhf le_rfl)).union ?_
    rw [h₁ rfl]
    exact (hg le_rfl).congr (hhg.mono inter_subset_right) (hhg le_rfl)
  · have hhg : EqOn (fun y ↦ if y ≤ c then f y else g y) g (Ioi c) := fun y hy ↦
      ite_eq_right (not_le.2 hy)
    rw [ite_eq_right htc.not_ge]
    exact (((hg htc.le).mono (inter_subset_inter_right s Ioi_subset_Ici_self)).congr
      (hhg.mono inter_subset_right) (hhg htc)).mono_of_mem_nhdsWithin
      (inter_mem_nhdsWithin s (Ioi_mem_nhds htc))

/-- **Gluing three solutions of an equation `x' = v t x`.** Let `a ≤ b`, and let `f`, `g` and `h`
solve the equation at `t` within `s ∩ Iic a`, `s ∩ Icc a b` and `s ∩ Ici b` respectively, whenever
`t` lies in the corresponding interval, with `f a = g a` and `g b = h b`. Then the function equal
to `f` on `Iic a`, to `g` on `Ioc a b` and to `h` on `Ioi b` solves the equation at `t` within
`s`. -/
theorem TauCeti.hasDerivWithinAt_if_le_if_le {v : ℝ → F → F} {f g h : ℝ → F} {s : Set ℝ}
    {a b t : ℝ} (hab : a ≤ b) (hf : t ≤ a → HasDerivWithinAt f (v t (f t)) (s ∩ Iic a) t)
    (hg : t ∈ Icc a b → HasDerivWithinAt g (v t (g t)) (s ∩ Icc a b) t)
    (hh : b ≤ t → HasDerivWithinAt h (v t (h t)) (s ∩ Ici b) t) (hfg : f a = g a)
    (hgh : g b = h b) :
    HasDerivWithinAt (fun y ↦ if y ≤ a then f y else if y ≤ b then g y else h y)
      (v t (if t ≤ a then f t else if t ≤ b then g t else h t)) s t := by
  have hga : (if a ≤ b then g a else h a) = f a := by rw [ite_eq_left hab, hfg]
  rw [apply_ite (v t)]
  refine TauCeti.hasDerivWithinAt_if_le hf (fun hat ↦ ?_) (fun _ ↦ hga.symm)
    (fun hta ↦ by rw [hta, hga])
  rw [apply_ite (v t)]
  exact TauCeti.hasDerivWithinAt_if_le
    (fun htb ↦ (hg ⟨hat, htb⟩).mono fun y hy ↦ ⟨hy.1.1, hy.1.2, hy.2⟩)
    (fun hbt ↦ (hh hbt).mono fun y hy ↦ ⟨hy.1.1, hy.2⟩) (fun _ ↦ hgh)
    (fun htb ↦ by rw [htb, hgh])

/-- Equal values and derivatives at zero allow gluing the one-sided derivatives. -/
theorem TauCeti.hasDerivAt_if_nonneg {f g f' g' : ℝ → F}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (h₀ : f 0 = g 0) (h₁ : f' 0 = g' 0) (t : ℝ) :
    HasDerivAt (fun t ↦ if 0 ≤ t then f t else g t)
      (if 0 ≤ t then f' t else g' t) t := by
  -- Swap the branches, so that the branch on `Iic 0` comes first.
  have hswap : ∀ (u w : ℝ → F), u 0 = w 0 → ∀ x : ℝ,
      (if 0 ≤ x then u x else w x) = if x ≤ 0 then w x else u x := fun u w h x ↦ by
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · simp [hx.not_ge, hx.le]
    · simp [h]
    · simp [hx.le, hx.not_ge]
  rw [funext (hswap f g h₀), hswap f' g' h₁, ← hasDerivWithinAt_univ]
  exact TauCeti.hasDerivWithinAt_if_le (fun _ ↦ (hg t).hasDerivWithinAt)
    (fun _ ↦ (hf t).hasDerivWithinAt) (fun _ ↦ h₀.symm) (fun ht ↦ by rw [ht, h₁])

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
