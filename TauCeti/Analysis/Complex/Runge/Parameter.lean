/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Complex.Runge.Operator
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.ParameterDeriv

/-!
# The finite-rank Runge operator on families

The finite-rank Runge operator of `TauCeti.exists_finite_rank_runge_operator` is
`A f(z) = ∑ j, w j * f (ζ j) * g j z`: finitely many point evaluations of `f` at nodes `ζ j`,
multiplied by weights `w j` and by functions `g j` holomorphic on `Ω`, none of which depend on `f`.
This file applies it to vector-valued functions and to smooth families of holomorphic functions.

* The scalar estimate `sup_K |f - A f| ≤ ε sup_L |f|` for holomorphic `f : ℂ → ℂ` implies the same
  estimate, with the same nodes, weights and output functions, for holomorphic functions with
  values in any complex normed space (`TauCeti.norm_sub_sum_smul_le_of_scalar`).
* For a family `h : E → ℂ → W`, smooth in a real parameter `y ∈ E` and holomorphic in `z`, the
  operator acts fibrewise: `(A h)(y, z) = ∑ j, (w j * g j z) • h y (ζ j)`. Parameter derivatives
  commute with it, since its nodes, weights and output functions do not depend on `y`, and every
  parameter derivative of `h` is again holomorphic in `z`
  (`ContDiffOn.differentiableOn_iteratedFDeriv_slice`). Hence the error estimate holds for every
  parameter derivative: `sup_K ‖D_yᵏ (h - A h)(x, ·)‖ ≤ ε sup_L ‖D_yᵏ h (x, ·)‖`. Evaluating the
  multilinear map `D_yᵏ` on coordinate vectors gives the estimate for every partial derivative
  of order `k` in coordinates of `E`.
* `A h` is jointly as smooth as the evaluations `y ↦ h y (ζ j)`. Being a finite linear
  combination of these evaluations, it is also holomorphic in a complex parameter when they are.

These are the properties used when Runge corrections are applied to families of solutions of the
inhomogeneous Cauchy–Riemann equation depending on smooth and holomorphic parameters.

## Main results

* `TauCeti.norm_iteratedFDeriv_sub_sum_smul_le`: the estimate for parameter derivatives of a smooth
  family of holomorphic functions.
* `TauCeti.exists_finite_rank_runge_operator_with_param`: a finite-rank Runge operator whose
  estimate holds for all parameter derivatives of all smooth families of holomorphic functions.
* `TauCeti.contDiffOn_sum_smul_apply`: the operator preserves joint smoothness in the parameter
  and the plane variable.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorems 11.1 and 12.2.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  Theorem 1.4.5.
-/

public section

namespace TauCeti

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {U L K : Set ℂ} {N : ℕ} {ζ w : Fin N → ℂ} {g : Fin N → ℂ → ℂ} {ε : ℝ}

/-- **The finite-rank Runge estimate for parameter derivatives.** Let a finite-rank evaluation
operator with nodes in `U` satisfy the Runge estimate on `K ⊆ U` for scalar functions holomorphic
on `U`, with bounds taken on `L`. Let `h : E → ℂ → W` be jointly `C^n` on `s ×ˢ U`, `s` and `U`
open, with each `h y` holomorphic on `U`. Then for `k + 1 ≤ n` the `k`-th parameter derivative of
the error `h - A h` at `x ∈ s` is bounded on `K` by `ε` times any bound of the `k`-th parameter
derivative of `h` on `L`. -/
theorem norm_iteratedFDeriv_sub_sum_smul_le
    (hA : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∀ B : ℝ, 0 ≤ B → (∀ z ∈ L, ‖f z‖ ≤ B) →
      ∀ z ∈ K, ‖f z - ∑ j, w j * f (ζ j) * g j z‖ ≤ ε * B)
    (hU : IsOpen U) (hKU : K ⊆ U) (hζ : ∀ j, ζ j ∈ U) {n : WithTop ℕ∞} {s : Set E}
    {h : E → ℂ → W} (hs : IsOpen s) (hh : ContDiffOn ℝ n (Function.uncurry h) (s ×ˢ U))
    (hhU : ∀ y ∈ s, DifferentiableOn ℂ (h y) U) {k : ℕ} (hk : (k + 1 : WithTop ℕ∞) ≤ n)
    {x : E} (hx : x ∈ s) {B : ℝ} (hB : 0 ≤ B)
    (hhB : ∀ z ∈ L, ‖iteratedFDeriv ℝ k (fun y ↦ h y z) x‖ ≤ B) {z : ℂ} (hz : z ∈ K) :
    ‖iteratedFDeriv ℝ k (fun y ↦ h y z - ∑ j, (w j * g j z) • h y (ζ j)) x‖ ≤ ε * B := by
  have hkn : (k : WithTop ℕ∞) ≤ n := le_trans (by norm_cast; omega) hk
  have hsl {z' : ℂ} (hz' : z' ∈ U) : ContDiffAt ℝ k (fun y ↦ h y z') x :=
    ((hh.comp (contDiffOn_id.prodMk contDiffOn_const) fun _ hy ↦ ⟨hy, hz'⟩).contDiffAt
      (hs.mem_nhds hx)).of_le hkn
  -- Parameter derivatives commute with the operator.
  have hsum : (fun y ↦ ∑ j, (w j * g j z) • h y (ζ j)) =
      ∑ j, fun y ↦ (w j * g j z) • h y (ζ j) := by
    ext; simp
  rw [fun_iteratedFDeriv_sub_apply (hsl (hKU hz))
      (ContDiffAt.sum fun j _ ↦ (hsl (hζ j)).const_smul (w j * g j z)), hsum,
    iteratedFDeriv_sum_apply fun j _ ↦ (hsl (hζ j)).const_smul (w j * g j z)]
  simp only [iteratedFDeriv_const_smul_apply' (hsl (hζ _))]
  exact norm_sub_sum_smul_le_of_scalar hA
    (hh.differentiableOn_iteratedFDeriv_slice hs hU hhU hk hx) hB hhB hz

/-- **The finite-rank Runge operator on smooth families of holomorphic functions.** For a Runge
compact pair `(Ω, K)` and an open neighbourhood `U ⊇ K`, there is a compact neighbourhood `L` of
`K` inside `U ∩ Ω` such that for every `ε > 0` there are nodes `ζ j ∈ interior L`, weights `w j`
and `Ω`-holomorphic functions `g j` with the following property. For every family
`h : E → ℂ → W`, jointly `C^n` on `s ×ˢ U` with `s` open and holomorphic in its second variable on
`U`, every `k` with `k + 1 ≤ n` and every `x ∈ s`, the `k`-th parameter derivative of
`h - A h`, where `(A h)(y, z) = ∑ j, (w j * g j z) • h y (ζ j)`, is bounded on `K` by `ε` times any
bound of the `k`-th parameter derivative of `h` on `L`. The data do not depend on the family. -/
theorem exists_finite_rank_runge_operator_with_param {Ω : Set ℂ} (hRunge : IsRungeCompactPair Ω K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ L : Set ℂ, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∩ Ω ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∃ ζ : Fin N → ℂ, ∃ w : Fin N → ℂ, ∃ g : Fin N → ℂ → ℂ,
          (∀ j, ζ j ∈ interior L) ∧ (∀ j, DifferentiableOn ℂ (g j) Ω) ∧
          ∀ (n : WithTop ℕ∞) (s : Set E) (h : E → ℂ → W), IsOpen s →
            ContDiffOn ℝ n (Function.uncurry h) (s ×ˢ U) →
            (∀ y ∈ s, DifferentiableOn ℂ (h y) U) →
            ∀ k : ℕ, (k + 1 : WithTop ℕ∞) ≤ n → ∀ x ∈ s, ∀ B : ℝ, 0 ≤ B →
              (∀ z ∈ L, ‖iteratedFDeriv ℝ k (fun y ↦ h y z) x‖ ≤ B) →
              ∀ z ∈ K, ‖iteratedFDeriv ℝ k
                (fun y ↦ h y z - ∑ j, (w j * g j z) • h y (ζ j)) x‖ ≤ ε * B := by
  obtain ⟨L, hL, hKL, hLUΩ, hA⟩ := exists_finite_rank_runge_operator hRunge hU hKU
  refine ⟨L, hL, hKL, hLUΩ, fun ε hε ↦ ?_⟩
  obtain ⟨N, ζ, w, g, hζ, hg, hA⟩ := hA ε hε
  refine ⟨N, ζ, w, g, hζ, hg, fun n s h hs hh hhU k hk x hx B hB hhB z hz ↦ ?_⟩
  exact norm_iteratedFDeriv_sub_sum_smul_le hA hU hKU
    (fun j ↦ (hLUΩ (interior_subset (hζ j))).1) hs hh hhU hk hx hB hhB hz

/-- **The finite-rank operator preserves joint smoothness.** If the output functions `g j` are
holomorphic on an open set `Ω` and every evaluation `y ↦ h y (ζ j)` is `C^n` on `s`, then
`(y, z) ↦ ∑ j, (w j * g j z) • h y (ζ j)` is `C^n` on `s ×ˢ Ω`. -/
theorem contDiffOn_sum_smul_apply {n : WithTop ℕ∞} {Ω : Set ℂ} {s : Set E} {h : E → ℂ → W}
    (hΩ : IsOpen Ω) (hg : ∀ j, DifferentiableOn ℂ (g j) Ω)
    (hh : ∀ j, ContDiffOn ℝ n (fun y ↦ h y (ζ j)) s) :
    ContDiffOn ℝ n (fun p : E × ℂ ↦ ∑ j, (w j * g j p.2) • h p.1 (ζ j)) (s ×ˢ Ω) :=
  ContDiffOn.sum fun j _ ↦
    ((contDiffOn_const.mul (((hg j).contDiffOn hΩ).restrict_scalars ℝ)).comp contDiffOn_snd
      fun _ (hp : _ ∈ s ×ˢ Ω) ↦ hp.2).smul
        ((hh j).comp contDiffOn_fst fun _ (hp : _ ∈ s ×ˢ Ω) ↦ hp.1)

end TauCeti
