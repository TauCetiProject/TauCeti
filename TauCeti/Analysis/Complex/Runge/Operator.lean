/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.Runge.Rational.Basic

/-!
# The finite-rank Runge approximation operator

Via rational Runge approximation (`IsCompact.exists_rational_norm_sub_sum_smul_le` in
`TauCeti.Analysis.Complex.Runge.Rational.Basic`), this file establishes the vector-valued
finite-rank Runge operator (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_sum_smul_le`)
without requiring `Ω` to be open, together with a fixed compact collar `L` (`K ⊆ interior L` and
`L ⊆ V`) chosen independently of `ε`.

## Main results

* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_sum_smul_le`: vector-valued finite-rank
  Runge operator with compact-collar control for compact sets filled in an arbitrary `Ω ⊆ ℂ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.9.
-/

public section

open Set

universe u

namespace TauCeti

/-- **Finite-rank Runge approximation operator.** Let `K` be a compact set filled in `Ω ⊆ ℂ`
(without requiring `Ω` to be open), and let `V ⊆ ℂ` be an open neighbourhood of `K`. Then there is
a compact set `L` with `K ⊆ interior L` and `L ⊆ V` such that for every `ε > 0` there are
finitely many evaluation points `ζ i ∈ interior L \ K` and functions `g i : ℂ → ℂ` holomorphic on
`Ω` such that every `f : ℂ → F` into a complex normed space, holomorphic on `V` and bounded by `M`
on `L`, satisfies `‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M` for all `w ∈ K`.

The collar `L` depends only on `K` and `V`, and the points `ζ i` and holomorphic kernels `g i`
depend only on `K`, `Ω`, `L`, and `ε`, not on `f`, `M`, or `F`. The resulting operator
`f ↦ ∑ i, g i · • f (ζ i)` is linear in `f`, takes values in functions holomorphic on `Ω`, and has
finite rank for scalar `f`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_sum_smul_le {K Ω V : Set ℂ}
    (hfill : IsFilledIn K Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ V ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ (N : ℕ) (ζ : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
          (∀ i, ζ i ∈ interior L \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
          ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
            DifferentiableOn ℂ f V → (∀ z ∈ L, ‖f z‖ ≤ M) →
            ∀ w ∈ K, ‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M := by
  obtain ⟨L, hL, hKL, hLV, hop⟩ := hK.exists_rational_norm_sub_sum_smul_le.{u} hV hKV
    fun _ hx ↦ hfill.compl_inter_connectedComponentIn_nonempty hKΩ hx
  refine ⟨L, hL, hKL, hLV, fun {ε} hε ↦ ?_⟩
  obtain ⟨N, ζ, p, q, hζ, -, hqΩ, hle⟩ := hop hε
  refine ⟨N, ζ, fun i w ↦ (p i).eval w / (q i).eval w, hζ, fun i ↦
    DifferentiableOn.div (p i).differentiable.differentiableOn
      (q i).differentiable.differentiableOn fun z hz h0 ↦ (hqΩ i z h0).1 hz, hle⟩

end TauCeti
