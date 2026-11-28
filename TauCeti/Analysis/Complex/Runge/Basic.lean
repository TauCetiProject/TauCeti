/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.PowerSeries.Approximation
import TauCeti.Analysis.Complex.Runge.Rational.Basic

/-!
# Forward Runge approximation theorems

Building on rational-kernel Runge approximation (`IsCompact.exists_rational_norm_sub_sum_smul_lt` in
`TauCeti.Analysis.Complex.Runge.Rational.Basic`) and entire power-series truncation
(`Differentiable.exists_polynomial_norm_sub_lt` in
`TauCeti.Analysis.Complex.PowerSeries.Approximation`), this file provides the forward Runge
approximation theorems without pulling in the holomorphic-hull or exhaustion machinery:

* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: vector-valued uniform Runge
  approximation on a compact set `K` filled in an arbitrary subset `Ω ⊆ ℂ` (without requiring `Ω`
  to be open).
* `TauCeti.IsFilledIn.exists_polynomial_norm_sub_lt`: uniform polynomial approximation on a compact
  set `K` filled in `ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.1.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.5.
-/

public section

open Polynomial Set

namespace TauCeti

/-- **Runge's approximation theorem (vector-valued, arbitrary `Ω`).** Let `K` be a compact set
filled in `Ω ⊆ ℂ` (without requiring `Ω` to be open), and let `f : ℂ → F` be holomorphic on an
open neighbourhood `U` of `K` with values in a complex normed space `F`. For every `ε > 0` there is
a function `g : ℂ → F` holomorphic on `Ω` such that `‖f z - g z‖ < ε` for all `z ∈ K`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {K Ω U : Set ℂ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] (hfill : IsFilledIn K Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → F}
    (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖f z - g z‖ < ε := by
  obtain ⟨N, ζ, p, q, -, -, hqΩ, happrox⟩ := hK.exists_rational_norm_sub_sum_smul_lt hU hKU
    (fun _ hx ↦ hfill.compl_inter_connectedComponentIn_nonempty hKΩ hx) hf hε
  refine ⟨fun w ↦ ∑ i, ((p i).eval w / (q i).eval w) • f (ζ i),
    DifferentiableOn.fun_sum fun i _ ↦ ?_, happrox⟩
  exact (Polynomial.differentiableOn_eval_div_eval
    fun z hz h0 ↦ (hqΩ i z h0).1 hz).smul_const (f (ζ i))

/-- **Polynomial Runge theorem (for filled compact sets).** If `K ⊆ ℂ` is compact and filled in
`ℂ`, every function holomorphic on an open neighbourhood `U` of `K` can be uniformly approximated on
`K` by complex polynomials. -/
theorem IsFilledIn.exists_polynomial_norm_sub_lt {K U : Set ℂ} (hfill : IsFilledIn K univ)
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  obtain ⟨g, hg, hfg⟩ := hfill.exists_differentiableOn_norm_sub_lt hK (subset_univ K)
    hU hKU hf (half_pos hε)
  obtain ⟨p, hgp⟩ := (differentiableOn_univ.mp hg).exists_polynomial_norm_sub_lt hK.isBounded
    (half_pos hε)
  exact ⟨p, fun z hz ↦ (norm_sub_le_norm_sub_add_norm_sub (f z) (g z) (p.eval z)).trans_lt
    (by linarith [hfg z hz, hgp z hz])⟩

end TauCeti
