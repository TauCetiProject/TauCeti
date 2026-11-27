/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Calculus.LocalExtr.Rolle

/-!
# The Lagrange interpolation remainder

Cauchy's interpolation remainder expresses the error at a point as the product of the
differences from the nodes times one value of the highest derivative divided by the factorial.
Thus a bound on that derivative controls the error through the node polynomial.

The formula uses `Lagrange.interpolate` and applies also at the nodes and to the empty set
of nodes. Derivatives are taken within the closed interval containing the nodes and the point.
-/

public section

open Finset Polynomial Set

namespace Set.InjOn

/-- The interpolation correction has highest derivative `c * N!`: the interpolant has degree
less than `N`, and the nodal polynomial is monic of degree `N`. -/
private theorem eval_iterate_derivative_interpolation_correction {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {v : ι → ℝ} (hv : InjOn v s) (r : ι → ℝ) (c ξ : ℝ) :
    (derivative^[s.card] (Lagrange.interpolate s v r + C c * Lagrange.nodal s v)).eval ξ =
      c * (s.card.factorial : ℝ) := by
  let p := Lagrange.interpolate s v r
  let w := Lagrange.nodal s v
  have hp : derivative^[s.card] p = 0 :=
    iterate_derivative_eq_zero_of_degree_lt (Lagrange.degree_interpolate_lt r hv)
  have hw : (derivative^[s.card] w).eval ξ = (s.card.factorial : ℝ) := by
    rw [← congrFun (Polynomial.iteratedDeriv w s.card) ξ,
      iteratedDeriv_eq_factorial_mul_eval_hasseDeriv,
      ← Lagrange.natDegree_nodal (s := s) (v := v), hasseDeriv_natDegree_eq_C,
      eval_C, Lagrange.nodal_monic.leadingCoeff, mul_one]
  have hadd : derivative^[s.card] (p + C c * w) = derivative^[s.card] p +
      derivative^[s.card] (C c * w) := by
    simp only [← pow_apply_eq_iterate, map_add]
  rw [hadd, hp, zero_add, iterate_derivative_C_mul, eval_mul, eval_C, hw]

/-- Cauchy's interpolation remainder. For `N` distinct nodes in `[a, b]` and `f` of class `C^N`
there, the error of Lagrange interpolation at `x ∈ [a, b]` is the node product at `x` times
`f⁽ᴺ⁾(ξ) / N!` for some `ξ ∈ [a, b]`. -/
theorem exists_sub_eval_interpolate_eq {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    (hv : InjOn v s) {a b : ℝ} (hvab : ∀ i ∈ s, v i ∈ Icc a b) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ s.card f (Icc a b)) {x : ℝ} (hx : x ∈ Icc a b) :
    ∃ ξ ∈ Icc a b, f x - (Lagrange.interpolate s v (fun i ↦ f (v i))).eval x =
      iteratedDerivWithin s.card f (Icc a b) ξ / (s.card.factorial : ℝ) * ∏ i ∈ s, (x - v i) := by
  classical
  rw [← Lagrange.eval_nodal]
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨x, hx, by simp⟩
  by_cases hnode : x ∈ s.image v
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hnode
    exact ⟨v i, hx, by rw [Lagrange.eval_interpolate_at_node _ hv hi,
      Lagrange.eval_nodal_at_node hi, sub_self, mul_zero]⟩
  have hnot (i : ι) (hi : i ∈ s) : x ≠ v i :=
    fun h ↦ hnode (Finset.mem_image.mpr ⟨i, hi, h.symm⟩)
  have hab : a < b := by
    obtain ⟨i, hi⟩ := hne
    exact lt_of_not_ge fun h ↦ hnot i hi ((subsingleton_Icc_of_ge h) hx (hvab i hi))
  have huniq := uniqueDiffOn_Icc hab
  let p := Lagrange.interpolate s v (fun i ↦ f (v i))
  let w := Lagrange.nodal s v
  let c := (f x - p.eval x) / w.eval x
  have hc : c * w.eval x = f x - p.eval x :=
    div_mul_cancel₀ _ (Lagrange.eval_nodal_not_at_node hnot)
  let q := p + C c * w
  have hq : ContDiff ℝ s.card q.eval := by
    simpa only [coe_aeval_eq_eval] using q.contDiff_aeval (𝕜 := ℝ) s.card
  have hmem : (↑(insert x (s.image v)) : Set ℝ) ⊆ Icc a b := by
    simp only [Finset.coe_insert, Finset.coe_image, Set.insert_subset_iff, Set.image_subset_iff]
    exact ⟨hx, hvab⟩
  have hzero : ∀ y ∈ insert x (s.image v), f y - q.eval y = 0 := by
    simp only [Finset.mem_insert, Finset.mem_image]
    rintro y (rfl | ⟨i, hi, rfl⟩)
    · simp only [q, eval_add, eval_mul, eval_C, hc, add_sub_cancel, sub_self]
    · simp only [q, p, w, eval_add, eval_mul, eval_C, Lagrange.eval_interpolate_at_node _ hv hi,
        Lagrange.eval_nodal_at_node hi, mul_zero, add_zero, sub_self]
  obtain ⟨ξ, hξ, hξzero⟩ := (hf.sub hq.contDiffOn).exists_iteratedDerivWithin_eq_zero_of_lt_card
    ordConnected_Icc hmem hzero (by
      rw [card_insert_of_notMem hnode, card_image_of_injOn hv]
      exact Nat.lt_succ_self _)
  rw [← Pi.sub_def, iteratedDerivWithin_sub hξ huniq (hf ξ hξ) hq.contDiffAt.contDiffWithinAt,
    iteratedDerivWithin_eq_iteratedDeriv huniq hq.contDiffAt hξ] at hξzero
  simp only [Polynomial.iteratedDeriv] at hξzero
  rw [hv.eval_iterate_derivative_interpolation_correction (fun i ↦ f (v i)) c ξ,
    sub_eq_zero] at hξzero
  have hquot := (div_eq_iff (Nat.cast_ne_zero.mpr s.card.factorial_ne_zero)).mpr hξzero
  exact ⟨ξ, hξ, hc.symm.trans (congrArg (· * w.eval x) hquot.symm)⟩

end Set.InjOn
