/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Calculus.LocalExtr.Rolle
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# The Lagrange interpolation remainder

For `N` distinct nodes and a `C^N` function, Cauchy's interpolation remainder expresses the
error at a point as the product of the differences from the nodes times one value of the
`N`-th derivative divided by `N!`.
Thus a bound on that derivative controls the error through the node polynomial.

The formula uses `Lagrange.interpolate` and applies also at the nodes and to the empty set
of nodes. It holds on any order-connected set containing the nodes and the point, with
higher derivatives taken within that set.

## Main result

* `Set.InjOn.exists_sub_eval_interpolate_eq`: apply this to the injectivity proof for the nodes,
  an order-connected domain, and the `C^N` hypothesis. The witness lies in the interior when the
  nodes are nonempty and the evaluation point is not a node.
-/

public section

open Finset Polynomial Set

namespace Set.InjOn

/-- Cauchy's interpolation remainder. For `N` distinct nodes in an order-connected set `t` and
`f` of class `C^N` there, the error of Lagrange interpolation at `x ∈ t` is the node product at
`x` times `f⁽ᴺ⁾(ξ) / N!` for some `ξ ∈ t`, where `f⁽ᴺ⁾` is taken within `t`.
If the nodes are nonempty and `x` is not a node, then `ξ` lies in the interior of `t`. -/
theorem exists_sub_eval_interpolate_eq {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    (hv : InjOn v s) {t : Set ℝ} (ht : t.OrdConnected) (hvt : ∀ i ∈ s, v i ∈ t) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ s.card f t) {x : ℝ} (hx : x ∈ t) :
    ∃ ξ ∈ t, f x - (Lagrange.interpolate s v (fun i ↦ f (v i))).eval x =
      iteratedDerivWithin s.card f t ξ / (s.card.factorial : ℝ) * ∏ i ∈ s, (x - v i) ∧
      (s.Nonempty → x ∉ s.image v → ξ ∈ interior t) := by
  classical
  rw [← Lagrange.eval_nodal]
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨x, hx, by simp, by simp⟩
  by_cases hnode : x ∈ s.image v
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hnode
    exact ⟨v i, hx, by simp [-Lagrange.interpolate_apply, Lagrange.eval_interpolate_at_node _ hv hi,
      Lagrange.eval_nodal_at_node hi], fun _ h ↦ (h hnode).elim⟩
  have hnot (i : ι) (hi : i ∈ s) : x ≠ v i :=
    fun h ↦ hnode (Finset.mem_image.mpr ⟨i, hi, h.symm⟩)
  obtain ⟨i, hi⟩ := hne
  have huniq := ht.isPreconnected.uniqueDiffOn hx (hvt i hi) (hnot i hi)
  let p := Lagrange.interpolate s v (fun i ↦ f (v i))
  let w := Lagrange.nodal s v
  let c := (f x - p.eval x) / w.eval x
  have hc : c * w.eval x = f x - p.eval x :=
    div_mul_cancel₀ _ (Lagrange.eval_nodal_not_at_node hnot)
  let q := p + C c * w
  have hq : ContDiff ℝ s.card q.eval := by
    simpa only [coe_aeval_eq_eval] using q.contDiff_aeval (𝕜 := ℝ) s.card
  have hmem : (↑(insert x (s.image v)) : Set ℝ) ⊆ t := by
    simp only [Finset.coe_insert, Finset.coe_image, Set.insert_subset_iff, Set.image_subset_iff]
    exact ⟨hx, hvt⟩
  have hzero : ∀ y ∈ insert x (s.image v), f y - q.eval y = 0 := by
    simp only [Finset.mem_insert, Finset.mem_image]
    rintro y (rfl | ⟨i, hi, rfl⟩)
    · simp [q, hc]
    · simp [q, p, w, -Lagrange.interpolate_apply, Lagrange.eval_interpolate_at_node _ hv hi,
        Lagrange.eval_nodal_at_node hi]
  -- The derivative zero comes from Tau Ceti's finite-set Rolle argument.
  obtain ⟨ξ, hξ, hξzero, hξinterior⟩ :=
    (hf.sub hq.contDiffOn).exists_iteratedDerivWithin_eq_zero_of_lt_card
    ht hmem hzero (by
      rw [card_insert_of_notMem hnode, card_image_of_injOn hv]
      exact Nat.lt_succ_self _)
  rw [← Pi.sub_def, iteratedDerivWithin_sub hξ huniq (hf ξ hξ) hq.contDiffAt.contDiffWithinAt,
    iteratedDerivWithin_eq_iteratedDeriv huniq hq.contDiffAt hξ] at hξzero
  simp only [Polynomial.iteratedDeriv] at hξzero
  rw [Lagrange.iterate_derivative_interpolate_add_C_mul_nodal, eval_C, sub_eq_zero] at hξzero
  have hquot := (div_eq_iff (Nat.cast_ne_zero.mpr s.card.factorial_ne_zero)).mpr hξzero
  exact ⟨ξ, hξ, hc.symm.trans (congrArg (· * w.eval x) hquot.symm),
    fun _ _ ↦ hξinterior (Finset.card_pos.mpr ⟨i, hi⟩)⟩

end Set.InjOn
