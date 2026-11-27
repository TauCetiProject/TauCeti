/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import TauCeti.Analysis.Normed.Monoid.MulUnit

/-!
# Locating a root of a split polynomial

Let `p` be a split polynomial over a domain with a multiplicative seminorm. If
`p.natDegree ≠ 0`, the root `b` of `p` nearest to `u` has
`‖p.leadingCoeff‖ * ‖u - b‖ ^ p.natDegree ≤ ‖p.eval u‖`. Indeed `p.eval u` is the leading
coefficient times the product of `u - b` over the roots `b`, and there are `p.natDegree` of
them. Consequently, if `p` is small at `u` compared with its leading coefficient,
`‖p.eval u‖ < ‖p.leadingCoeff‖ * r ^ p.natDegree` with `0 ≤ r`, then some root of `p` lies
within `r` of `u`.

This is the pointwise step of root approximation for polynomial families, used in
`TauCeti.Analysis.Polynomial.ContinuityOfRoots.Approximation`.
-/

public section

open Polynomial

namespace Polynomial.Splits

/-- **A root near every point.** If a split polynomial `p` has positive degree `n`, then for
every point `u` the nearest root `b` of `p` has `‖p.leadingCoeff‖ * ‖u - b‖ ^ n ≤ ‖p.eval u‖`,
since `‖p.eval u‖` is `‖p.leadingCoeff‖` times the product of the distances from `u` to the `n`
roots of `p`, counted with multiplicity. For monic `p` over a normed field, `u` lies within
`‖p.eval u‖^(1/n)` of a root. The seminorm only needs to be multiplicative. -/
theorem exists_mem_roots_norm_sub_pow_le {R : Type*} [SeminormedCommRing R] [IsDomain R]
    [NormMulClass R] {p : R[X]} (hp : p.Splits) (hn : p.natDegree ≠ 0) (u : R) :
    ∃ b ∈ p.roots, ‖p.leadingCoeff‖ * ‖u - b‖ ^ p.natDegree ≤ ‖p.eval u‖ := by
  classical
  have hne : p.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty, ← Multiset.card_pos, ← hp.natDegree_eq_card_roots]
    exact Nat.pos_of_ne_zero hn
  obtain ⟨b, hb, hmin⟩ := p.roots.toFinset.exists_min_image (fun b ↦ ‖u - b‖) hne
  refine ⟨b, Multiset.mem_toFinset.1 hb, ?_⟩
  -- A leading coefficient of norm zero makes the claim trivial; otherwise `‖1‖ = 1`.
  rcases eq_or_ne ‖p.leadingCoeff‖ 0 with hlc | hlc
  · rw [hlc, zero_mul]
    exact norm_nonneg _
  have : NormOneClass R :=
    ⟨TauCeti.NormedRing.norm_one_of_norm_mul hlc fun x ↦ norm_mul _ x⟩
  rw [hp.eval_eq_prod_roots, norm_mul, Multiset.norm_prod_map, hp.natDegree_eq_card_roots]
  gcongr
  calc ‖u - b‖ ^ Multiset.card p.roots = (p.roots.map fun _ ↦ ‖u - b‖).prod := by simp
    _ ≤ _ := Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ norm_nonneg _)
      fun c hc ↦ hmin c (Multiset.mem_toFinset.2 hc)

/-- A split polynomial that is small at `u` compared with its leading coefficient has a root
near `u`: if `‖p.eval u‖ < ‖p.leadingCoeff‖ * r ^ p.natDegree` and `0 ≤ r`, some root `b` of
`p` satisfies `‖u - b‖ < r`. The seminorm only needs to be multiplicative. -/
theorem exists_mem_roots_norm_sub_lt {R : Type*} [SeminormedCommRing R] [IsDomain R]
    [NormMulClass R] {p : R[X]} (hp : p.Splits) {u : R} {r : ℝ} (hr : 0 ≤ r)
    (h : ‖p.eval u‖ < ‖p.leadingCoeff‖ * r ^ p.natDegree) :
    ∃ b ∈ p.roots, ‖u - b‖ < r := by
  -- A constant `p` has `p.eval u = p.leadingCoeff`, which contradicts `h`.
  rcases eq_or_ne p.natDegree 0 with h0 | h0
  · have he : p.eval u = p.leadingCoeff := by
      conv_lhs => rw [eq_C_of_natDegree_eq_zero h0]
      rw [eval_C, leadingCoeff, h0]
    rw [he, h0, pow_zero, mul_one] at h
    exact absurd h (lt_irrefl _)
  obtain ⟨b, hb, hle⟩ := hp.exists_mem_roots_norm_sub_pow_le h0 u
  exact ⟨b, hb, lt_of_pow_lt_pow_left₀ _ hr
    (lt_of_mul_lt_mul_left (hle.trans_lt h) (norm_nonneg _))⟩

end Polynomial.Splits
