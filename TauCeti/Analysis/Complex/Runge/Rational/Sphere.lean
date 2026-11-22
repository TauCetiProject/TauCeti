/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Analysis.Complex.Inversion.Basic
import TauCeti.Analysis.Complex.Inversion.FilledHull
import TauCeti.Analysis.Complex.Runge.Rational.Basic
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.LinearAlgebra.Complex.Finrank

/-!
# Riemann-sphere rational Runge approximation

Let `K ⊆ ℂ` be a compact set and `A ⊆ ℂ` a prescribed set of poles meeting every connected
component of `Kᶜ`, including the unbounded component. Choosing `a₀ ∈ A \ filledHull K`, the
Möbius inversion `z ↦ (z - a₀)⁻¹` sends `a₀` to `∞` and `∞` to `0`, sending `A \ {a₀}` to a set
meeting every bounded complementary component of the inverted compact set
(`IsClosed.image_inv_sub_inter_connectedComponentIn_nonempty`). Applying finite-pole rational Runge
approximation (`IsCompact.exists_rational_norm_sub_lt`) on the inverted domain and homogenizing the
resulting rational function in `(z - a₀)` yields a uniform rational approximant `p / q` with
`p.natDegree ≤ q.natDegree` and all finite poles in `A \ K`.

## Main results

* `IsCompact.exists_rational_natDegree_le_norm_sub_lt`: uniform approximation by rational functions
  bounded at `∞` (`p.natDegree ≤ q.natDegree`) with finite poles in `A \ K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.7, p. 29.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.6.
-/

public section

open Bornology Polynomial Set

namespace TauCeti

/-- **Riemann-sphere rational Runge approximation.** Let `K ⊆ ℂ` be compact and `A ⊆ ℂ` meet every
connected component of `Kᶜ`, including the unbounded component. Then every function holomorphic on
an open neighbourhood `U` of `K` can be uniformly approximated on `K` by rational functions `p / q`
with `p.natDegree ≤ q.natDegree` (hence bounded at `∞`) and all finite poles in `A \ K`. -/
theorem _root_.IsCompact.exists_rational_natDegree_le_norm_sub_lt {K U A : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hA : ∀ x ∈ Kᶜ, (A ∩ connectedComponentIn Kᶜ x).Nonempty)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p q : ℂ[X], q ≠ 0 ∧ p.natDegree ≤ q.natDegree ∧ (∀ z, q.eval z = 0 → z ∈ A \ K) ∧
      ∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε := by
  obtain ⟨x₀, hx₀⟩ := nonempty_compl_filledHull hK.isBounded
  obtain ⟨a₀, ha₀A, ha₀c⟩ := hA x₀ fun hxK ↦ hx₀ (subset_filledHull hxK)
  have ha₀ : a₀ ∉ filledHull K := by
    rwa [← mem_compl_iff,
      compl_filledHull_eq_connectedComponentIn Complex.one_lt_rank_real hK.isBounded hx₀]
  have ha₀K : a₀ ∉ K := fun h ↦ ha₀ (subset_filledHull h)
  set φ : ℂ → ℂ := fun z ↦ (z - a₀)⁻¹
  obtain ⟨P, Q, -, hQA', happrox⟩ := (hK.image_inv_sub ha₀K).exists_rational_norm_sub_lt
    (hU.compl_singleton_inter_preimage_add_inv a₀)
    (image_inv_sub_subset_compl_singleton_inter_preimage_add_inv hKU ha₀K)
    (hK.isClosed.image_inv_sub_inter_connectedComponentIn_nonempty ha₀ hA)
    (hf.comp_add_inv a₀) hε
  have hQ0 : Q.eval 0 ≠ 0 := by
    intro h0
    obtain ⟨b, ⟨-, hba⟩, hb0⟩ := (hQA' 0 h0).1
    exact inv_ne_zero (sub_ne_zero.mpr hba) hb0
  set d := max P.natDegree Q.natDegree
  refine ⟨(P.reflect d).comp (X - C a₀), (Q.reflect d).comp (X - C a₀),
    ?_, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · intro hq0
    exact hQ0 (by
      rw [← coeff_reflect_comp_X_sub_C a₀ (le_max_right _ _), hq0, coeff_zero])
  · exact (natDegree_reflect_comp_X_sub_C_le a₀ (le_max_left _ _)).trans
      (le_natDegree_of_ne_zero (by rwa [coeff_reflect_comp_X_sub_C a₀ (le_max_right _ _)]))
  · by_cases hza : z = a₀
    · exact hza ▸ ⟨ha₀A, ha₀K⟩
    · rw [eval_reflect_comp_X_sub_C (le_max_right _ _) hza, mul_eq_zero] at hz
      have hQz : Q.eval (φ z) = 0 := hz.resolve_left (pow_ne_zero d (sub_ne_zero.mpr hza))
      obtain ⟨⟨b, ⟨hbA, -⟩, hbz⟩, hzK'⟩ := hQA' (φ z) hQz
      exact ⟨sub_left_injective (inv_injective hbz) ▸ hbA, fun hzK ↦ hzK' ⟨z, hzK, rfl⟩⟩
  · have hza : z ≠ a₀ := fun h ↦ ha₀K (h ▸ hz)
    rw [eval_reflect_comp_X_sub_C (le_max_left _ _) hza,
      eval_reflect_comp_X_sub_C (le_max_right _ _) hza,
      mul_div_mul_left _ _ (pow_ne_zero d (sub_ne_zero.mpr hza))]
    simpa [φ] using happrox (φ z) ⟨z, hz, rfl⟩

end TauCeti
