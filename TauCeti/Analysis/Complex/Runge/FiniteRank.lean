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
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Complex.MixedDeriv

/-!
# Parametric Runge approximation operators

Let `K` be a compact subset of an open set `Ω ⊆ ℂ` which is filled in `Ω` (`TauCeti.IsFilledIn K Ω`,
meaning no connected component of `Ω \ K` is relatively compact in `Ω`), and let `V ⊇ K` be open.
Because the Runge operator from `TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`
(`TauCeti.Analysis.Complex.Runge.Operator`) chooses its nodes `ζ i ∈ V \ K`, weights `c i : ℂ`,
and `Ω`-holomorphic functions `g i : ℂ → ℂ` independently of both the input function and the
target space (yielding a finite-rank operator for scalar targets `F = ℂ` or finite-dimensional `F`,
and factoring through the finite sample space `Fin N → F` for general complex normed targets `F`),
applying it fiberwise and commuting finite constant-coefficient sums with `iteratedFDeriv`
(`TauCeti.iteratedFDeriv_sub_sum_const_smul`) yields a parametric Runge approximation operator
bounding every iterated parameter derivative uniformly by `ε * M` on `K`. Smoothness
preservation for any finite-sample operator `p ↦ ∑ i, (c i * g i p.2) • f p.1 (ζ i)` is provided
separately by `TauCeti.contDiffOn_sum_mul_smul_eval`.

## Main results

* `TauCeti.contDiffOn_sum_mul_smul_eval`: any finite-sample operator with nodes in `V` and
  `Ω`-holomorphic coefficients preserves joint `C^n` smoothness from `s ×ˢ V` to `s ×ˢ Ω`.
* `TauCeti.IsFilledIn.exists_norm_iteratedFDeriv_sub_sum_mul_smul_le`: parametric Runge
  approximation factoring through `Fin N → F` and bounding all iterated parameter derivatives
  uniformly by `ε * M`.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.1.
-/

public section

open Set

universe uX uF

namespace TauCeti

/-- Any finite-sample operator `p ↦ ∑ i, (c i * g i p.2) • f p.1 (ζ i)` with nodes `ζ i ∈ V`
and functions `g i` holomorphic on an open set `Ω ⊆ ℂ` preserves joint `C^n` smoothness from
`s ×ˢ V` to `s ×ˢ Ω`. -/
theorem contDiffOn_sum_mul_smul_eval {ι X F : Type*} [Fintype ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {s : Set X} {V Ω : Set ℂ} (hΩ : IsOpen Ω) {ζ : ι → ℂ} (hζ : ∀ i, ζ i ∈ V)
    (c : ι → ℂ) {g : ι → ℂ → ℂ} (hg : ∀ i, DifferentiableOn ℂ (g i) Ω)
    {n : WithTop ℕ∞} {f : X → ℂ → F} (hf : ContDiffOn ℝ n (Function.uncurry f) (s ×ˢ V)) :
    ContDiffOn ℝ n (fun p : X × ℂ ↦ ∑ i, (c i * g i p.2) • f p.1 (ζ i)) (s ×ˢ Ω) := by
  refine ContDiffOn.sum fun i _ ↦ ?_
  have hg_cd : ContDiffOn ℝ n (fun p : X × ℂ ↦ c i * g i p.2) (s ×ˢ Ω) :=
    (((((hg i).const_mul (c i)).contDiffOn hΩ).restrict_scalars ℝ).of_le le_top).comp
      contDiffOn_snd fun _ hp ↦ hp.2
  have hf_ζ : ContDiffOn ℝ n (fun p : X × ℂ ↦ f p.1 (ζ i)) (s ×ˢ Ω) :=
    hf.comp (contDiffOn_fst.prodMk contDiffOn_const) fun _ hp ↦ ⟨hp.1, hζ i⟩
  exact hg_cd.smul hf_ζ

/-- **Parametric Runge approximation operator.** Let `K` be a compact subset filled in an open set
`Ω ⊆ ℂ`, and let `V ⊇ K` be open. For every `ε > 0` there are finitely many evaluation points
`ζ i ∈ V \ K`, weights `c i : ℂ`, and functions `g i : ℂ → ℂ` holomorphic on `Ω` (depending only
on `K`, `V`, `Ω`, and `ε`) such that the operator `A f x w = ∑ i, (c i * g i w) • f x (ζ i)`,
which factors through the finite sample space `Fin N → F` (and has finite rank when `F = ℂ` or `F`
is finite-dimensional), approximates every `k`-th parameter derivative of a `C^(k+1)` family
`f : X → ℂ → F` holomorphic in the second variable on `V` within `ε * M` on `K`. -/
theorem IsFilledIn.exists_norm_iteratedFDeriv_sub_sum_mul_smul_le {K V Ω : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V)
    (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      ∀ {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
        {s : Set X}, IsOpen s → ∀ (f : X → ℂ → F) (k : ℕ) (M : ℝ),
        ContDiffOn ℝ (k + 1 : ℕ) (Function.uncurry f) (s ×ˢ V) →
        (∀ x ∈ s, DifferentiableOn ℂ (f x) V) →
        ∀ x ∈ s, (∀ z ∈ V, ‖iteratedFDeriv ℝ k (fun x' ↦ f x' z) x‖ ≤ M) →
        ∀ w ∈ K,
          ‖iteratedFDeriv ℝ k (fun x' ↦ f x' w - ∑ i, (c i * g i w) • f x' (ζ i)) x‖ ≤
            ε * M := by
  obtain ⟨N, ζ, c, g, hζ, hg, happrox⟩ :=
    hfill.exists_norm_sub_sum_mul_smul_le.{max uX uF} hΩ hK hKΩ hV hKV hε
  refine ⟨N, ζ, c, g, hζ, hg, ?_⟩
  intro X _ _ F _ _ s hs f k M hf_cd hf_hol x hx hM w hw
  let φ : ℂ → X [×k]→L[ℝ] F := fun z ↦ iteratedFDeriv ℝ k (fun x' ↦ f x' z) x
  have hφ_hol : DifferentiableOn ℂ φ V :=
    differentiableOn_iteratedFDeriv_prod_left k hs hV hf_cd hf_hol hx
  have hslice (z : ℂ) (hz : z ∈ V) : ContDiffAt ℝ k (fun x' ↦ f x' z) x :=
    ((hf_cd.contDiffAt ((hs.prod hV).mem_nhds ⟨hx, hz⟩)).of_le
      (by exact_mod_cast Nat.le_succ k)).comp x (contDiffAt_id.prodMk contDiffAt_const)
  rw [iteratedFDeriv_sub_sum_const_smul (u := Finset.univ) (fun i ↦ c i * g i w)
    (hslice w (hKV hw)) fun i _ ↦ hslice (ζ i) (hζ i).1]
  exact happrox φ M hφ_hol hM w hw

end TauCeti
