/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Complex.Runge.Rational.Basic

/-!
# The finite-rank Runge approximation operator

Via rational Runge approximation (`IsCompact.exists_rational_norm_sub_sum_smul_le` in
`TauCeti.Analysis.Complex.Runge.Rational.Basic`), this file establishes the vector-valued
finite-rank Runge operator (`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_sum_smul_le`)
without requiring `Ω` to be open, together with a fixed compact collar `L` (`K ⊆ interior L` and
`L ⊆ V ∩ W`) chosen independently of `ε`. By the Hahn–Banach theorem, evaluation data
approximating scalar holomorphic functions also approximate functions with values in any complex
normed space within the same error (`TauCeti.norm_sub_sum_smul_le_of_scalar`); applying the
finite-rank operator to families depending on parameters is studied in
`TauCeti.Analysis.Complex.Runge.Parameter`.

## Main results

* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_sum_smul_le`: vector-valued finite-rank
  Runge operator with compact-collar control for compact sets filled in an arbitrary `Ω ⊆ ℂ`.
* `TauCeti.norm_sub_sum_smul_le_of_scalar`: evaluation data approximating scalar holomorphic
  functions approximate functions with values in any complex normed space within the same error.

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
(without requiring `Ω` to be open), and let `V` and `W` be open neighbourhoods of `K`. Then there
is a compact set `L` with `K ⊆ interior L` and `L ⊆ V ∩ W` such that for every `ε > 0` there are
finitely many evaluation points `ζ i ∈ interior L \ K` and functions `g i : ℂ → ℂ` holomorphic on
`Ω` such that every `f : ℂ → F` into a complex normed space, holomorphic on `V` and bounded by `M`
on `L`, satisfies `‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M` for all `w ∈ K`.

The collar `L` depends only on `K`, `V`, and `W`, and the points `ζ i` and holomorphic kernels
`g i` depend only on `K`, `Ω`, `L`, and `ε`, not on `f`, `M`, or `F`. The resulting operator
`f ↦ ∑ i, g i · • f (ζ i)` is linear in `f`, takes values in functions holomorphic on `Ω`, and has
finite rank for scalar `f`. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_sum_smul_le {K Ω V W : Set ℂ}
    (hfill : IsFilledIn K Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V) (hKV : K ⊆ V)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ V ∩ W ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ (N : ℕ) (ζ : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
          (∀ i, ζ i ∈ interior L \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
          ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] (f : ℂ → F) (M : ℝ),
            DifferentiableOn ℂ f V → (∀ z ∈ L, ‖f z‖ ≤ M) →
            ∀ w ∈ K, ‖f w - ∑ i, g i w • f (ζ i)‖ ≤ ε * M := by
  obtain ⟨L, hL, hKL, hLVW, hop⟩ := hK.exists_rational_norm_sub_sum_smul_le.{u} (hV.inter hW)
    (subset_inter hKV hKW) fun _ hx ↦ hfill.compl_inter_connectedComponentIn_nonempty hKΩ hx
  refine ⟨L, hL, hKL, hLVW, fun {ε} hε ↦ ?_⟩
  obtain ⟨N, ζ, p, q, hζ, -, hqΩ, hle⟩ := hop hε
  refine ⟨N, ζ, fun i w ↦ (p i).eval w / (q i).eval w, hζ, fun i ↦
    Polynomial.differentiableOn_eval_div_eval fun z hz h0 ↦ (hqΩ i z h0).1 hz,
    fun f M hf hM w hw ↦ hle f M (hf.mono inter_subset_left) hM w hw⟩

/-- **Vector-valued finite-rank Runge estimate.** If nodes `ζ j`, weights `w j` and functions
`g j` approximate every scalar function holomorphic on `U` at the points of `K` within `ε` times
any nonnegative bound for it on `L`, then they approximate every function holomorphic on `U` with
values in a complex normed space `G` just as well. -/
theorem norm_sub_sum_smul_le_of_scalar {ι : Type*} [Fintype ι] {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℂ G] {U L K : Set ℂ} {ζ w : ι → ℂ} {g : ι → ℂ → ℂ}
    {ε : ℝ} (hA : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∀ B : ℝ, 0 ≤ B → (∀ y ∈ L, ‖f y‖ ≤ B) →
      ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B)
    {f : ℂ → G} (hf : DifferentiableOn ℂ f U) {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ y ∈ L, ‖f y‖ ≤ B)
    {z : ℂ} (hz : z ∈ K) :
    ‖f z - ∑ j, (w j * g j z) • f (ζ j)‖ ≤ ε * B := by
  -- The zero function shows that the error bound is nonnegative.
  have hεB : 0 ≤ ε * B := by
    simpa using hA 0 (differentiableOn_const 0) B hB (fun _ _ ↦ by simpa using hB) z hz
  refine NormedSpace.norm_le_dual_bound ℂ _ hεB fun φ ↦ ?_
  have hφ := hA (fun y ↦ φ (f y)) (φ.differentiable.comp_differentiableOn hf) (B * ‖φ‖)
    (mul_nonneg hB (norm_nonneg φ))
    (fun y hy ↦ (φ.le_opNorm (f y)).trans (by rw [mul_comm]; gcongr; exact hfB y hy)) z hz
  have heq : φ (f z - ∑ j, (w j * g j z) • f (ζ j)) =
      φ (f z) - ∑ j, w j * φ (f (ζ j)) * g j z := by
    simp only [map_sub, map_sum, map_smul, smul_eq_mul]
    exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ by ring)
  rw [heq, mul_assoc]
  exact hφ

end TauCeti
