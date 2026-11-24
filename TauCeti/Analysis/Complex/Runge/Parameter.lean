/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.MixedDeriv
import TauCeti.Analysis.Complex.Runge.Operator

/-!
# Finite-rank Runge operators with parameters

The finite-rank Runge operator `TauCeti.exists_finite_rank_runge_operator`
(`TauCeti.Analysis.Complex.Runge.Operator`) approximates every function `f` holomorphic on an
open set `U`, at the points of a compact set `K`, by `A f = ∑ j, w j * f (ζ j) * g j` within `ε`
times any nonnegative bound for `f` on a compact set `L`. Here the nodes `ζ j ∈ U`, the weights
`w j` and the functions `g j`, holomorphic on an open set `Ω` (the Runge domain), do not depend
on `f`. This file applies such an operator, fibrewise, to families of functions depending on
parameters.

* `TauCeti.contDiffOn_sum_smul_apply`: applied to a family `h (x, ·)` depending on a parameter `x`
  in a normed space over a field `𝕜` such as `ℝ` or `ℂ`, of which `ℂ` is a normed algebra, the
  operator yields a family on `S ×ˢ Ω` as regular in `(x, z)` as `h` is in `x`. For `𝕜 = ℝ`
  this is joint smoothness, and for `𝕜 = ℂ` joint holomorphy when `h` is holomorphic in the
  parameters.
* `TauCeti.norm_iteratedFDeriv_sub_sum_smul_le`: if `h` is jointly `C^n` and holomorphic in its
  complex variable, then on `K` every parameter derivative of `h - A h` of order `k < n` is at
  most `ε` times any nonnegative bound for the same derivative of `h` on `L`. Parameter
  derivatives commute with `A`, whose data do not depend on the parameter (Mathlib's
  `iteratedFDeriv_fun_sum_apply` and `iteratedFDeriv_const_smul_apply'`), and they are again
  holomorphic in the complex variable (`ContDiffOn.differentiableOn_iteratedFDeriv_partial`), so
  the vector-valued form of the operator estimate (`TauCeti.norm_sub_sum_smul_le_of_scalar`)
  applies to them.

These estimates control all parameter derivatives of the Runge corrections when solutions of
the inhomogeneous Cauchy–Riemann equation depending smoothly or holomorphically on parameters
are built by exhaustion.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.3.1.

The parametric estimates follow the parametric Runge operators of Tau Ceti pull request 43183.
-/

public section

open Set

namespace TauCeti

variable {ι : Type*} [Fintype ι] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {U L K : Set ℂ} {ζ w : ι → ℂ} {g : ι → ℂ → ℂ} {ε : ℝ}

/-- **Regularity of the finite-rank Runge operator with parameters.** For a family `h (x, ·)`
whose values at the nodes `ζ j` are `C^n` over `𝕜` in a parameter `x ∈ S`, where `ℂ` is a normed
`𝕜`-algebra, and functions `g j` holomorphic on an open set `Ω`, the family
`(x, z) ↦ ∑ j, (w j * g j z) • h (x, ζ j)` is `C^n` on `S ×ˢ Ω`. -/
theorem contDiffOn_sum_smul_apply {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedSpace 𝕜 G] [IsScalarTower 𝕜 ℂ G]
    {S : Set X} {Ω : Set ℂ} {h : X × ℂ → G} {n : WithTop ℕ∞} (hΩ : IsOpen Ω)
    (hg : ∀ j, DifferentiableOn ℂ (g j) Ω) (hh : ∀ j, ContDiffOn 𝕜 n (fun x ↦ h (x, ζ j)) S) :
    ContDiffOn 𝕜 n (fun p : X × ℂ ↦ ∑ j, (w j * g j p.2) • h (p.1, ζ j)) (S ×ˢ Ω) := by
  refine ContDiffOn.sum fun j _ ↦ ContDiffOn.smul ?_ ?_
  · exact ((((hg j).const_mul (w j)).contDiffOn hΩ).restrict_scalars 𝕜).of_le le_top
      |>.comp contDiffOn_snd fun _ hp ↦ hp.2
  · exact (hh j).comp contDiffOn_fst fun _ hp ↦ hp.1

/-- **Parameter derivatives under the finite-rank Runge operator.** Let `h : X × ℂ → G` be `C^n`
on `S ×ˢ U` for open sets `S` and `U`, and holomorphic in its complex variable on `U`. If nodes
`ζ j ∈ U`, weights `w j` and functions `g j` approximate every scalar function holomorphic on
`U` at the points of `K ⊆ U` within `ε` times any nonnegative bound for it on `L`, then for
`k < n`, every `x ∈ S` and every `z ∈ K`, the `k`-th parameter derivative at `x` of `h - A h` at
`z`, where `A h (x, z) = ∑ j, (w j * g j z) • h (x, ζ j)`, has norm at most `ε * B` for any
nonnegative bound `B` on `L` for the `k`-th parameter derivative of `h` at `x`. -/
theorem norm_iteratedFDeriv_sub_sum_smul_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {S : Set X} {h : X × ℂ → G} {n : WithTop ℕ∞}
    (hA : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∀ B : ℝ, 0 ≤ B → (∀ y ∈ L, ‖f y‖ ≤ B) →
      ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B)
    (hS : IsOpen S) (hU : IsOpen U) (hζ : ∀ j, ζ j ∈ U) (hKU : K ⊆ U)
    (hh : ContDiffOn ℝ n h (S ×ˢ U)) (hhol : ∀ x ∈ S, DifferentiableOn ℂ (fun z ↦ h (x, z)) U)
    {k : ℕ} (hk : k + 1 ≤ n) {x : X} (hx : x ∈ S) {B : ℝ} (hB : 0 ≤ B)
    (hhB : ∀ y ∈ L, ‖iteratedFDeriv ℝ k (fun x' ↦ h (x', y)) x‖ ≤ B) {z : ℂ} (hz : z ∈ K) :
    ‖iteratedFDeriv ℝ k (fun x' ↦ h (x', z) - ∑ j, (w j * g j z) • h (x', ζ j)) x‖ ≤
      ε * B := by
  have hslice {y : ℂ} (hy : y ∈ U) : ContDiffAt ℝ k (fun x' ↦ h (x', y)) x :=
    ((hh.contDiffAt ((hS.prod hU).mem_nhds ⟨hx, hy⟩)).of_le
      (le_trans (by exact_mod_cast Nat.le_succ k) hk)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  -- Parameter derivatives commute with the operator, whose data do not depend on `x`.
  rw [fun_iteratedFDeriv_sub_apply (hslice (hKU hz))
      (ContDiffAt.sum fun j _ ↦ (hslice (hζ j)).const_smul _),
    iteratedFDeriv_fun_sum_apply fun j _ ↦ (hslice (hζ j)).const_smul _]
  simp_rw [iteratedFDeriv_const_smul_apply' (hslice (hζ _))]
  exact norm_sub_sum_smul_le_of_scalar hA
    (hh.differentiableOn_iteratedFDeriv_partial hS hU hhol hk hx) hB hhB hz

end TauCeti
