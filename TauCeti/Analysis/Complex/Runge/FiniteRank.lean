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
# Parametric finite-rank Runge approximation operators

Let `K` be a compact subset of an open set `Ω ⊆ ℂ` which is filled in `Ω` (`TauCeti.IsFilledIn K Ω`,
meaning no connected component of `Ω \ K` is relatively compact in `Ω`), and let `V ⊇ K` be open.
Because the finite-rank Runge operator from `TauCeti.IsFilledIn.exists_norm_sub_sum_mul_smul_le`
(`TauCeti.Analysis.Complex.Runge.Operator`) chooses its nodes `ζ i ∈ V \ K`, weights `c i : ℂ`,
and `Ω`-holomorphic functions `g i : ℂ → ℂ` independently of both the input function and the
target space, applying it fiberwise and commuting finite constant-coefficient sums with
`iteratedFDeriv` (`TauCeti.iteratedFDeriv_sub_sum_const_smul`) yields a parametric finite-rank
Runge operator (`TauCeti.IsFilledIn.exists_norm_iteratedFDeriv_sub_sum_mul_smul_le`) that preserves
joint smoothness and external complex holomorphy while bounding every iterated parameter derivative
uniformly by `ε * M` on `K`.

## Main results

* `TauCeti.IsFilledIn.exists_norm_iteratedFDeriv_sub_sum_mul_smul_le`: parametric finite-rank Runge
  approximation preserving joint smoothness and parameter holomorphy and bounding all iterated
  parameter derivatives uniformly by `ε * M`.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.1.
-/

public section

open Set

universe uX uQ uF

namespace TauCeti

/-- **Parametric finite-rank Runge operator.** Let `K` be a compact subset filled in an open set
`Ω ⊆ ℂ`, and let `V ⊇ K` be open. For every `ε > 0` there are finitely many evaluation points
`ζ i ∈ V \ K`, weights `c i : ℂ`, and functions `g i : ℂ → ℂ` holomorphic on `Ω` (depending only
on `K`, `V`, `Ω`, and `ε`) such that the finite-rank operator
`A f x w = ∑ i, (c i * g i w) • f x (ζ i)`:
1. preserves joint `C^n` smoothness on `s ×ˢ V` to `s ×ˢ Ω`;
2. preserves complex differentiability with respect to an external complex parameter;
3. approximates every `k`-th parameter derivative of a `C^(k+1)` family `f : X → ℂ → F`
   holomorphic in the second variable on `V` within `ε * M` on `K`. -/
theorem IsFilledIn.exists_norm_iteratedFDeriv_sub_sum_mul_smul_le {K V Ω : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V)
    (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      (∀ {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
        {s : Set X} {n : WithTop ℕ∞} {f : X → ℂ → F},
        ContDiffOn ℝ n (Function.uncurry f) (s ×ˢ V) →
        ContDiffOn ℝ n (fun p : X × ℂ ↦ ∑ i, (c i * g i p.2) • f p.1 (ζ i)) (s ×ˢ Ω)) ∧
      (∀ {Q : Type uQ} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
        {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
        {f : Q → ℂ → F} {q₀ : Q} {w : ℂ},
        (∀ i, DifferentiableAt ℂ (fun q ↦ f q (ζ i)) q₀) →
        DifferentiableAt ℂ (fun q ↦ ∑ i, (c i * g i w) • f q (ζ i)) q₀) ∧
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
  refine ⟨N, ζ, c, g, hζ, hg, ?_, ?_, ?_⟩
  · intro X _ _ F _ _ s n f hf
    refine ContDiffOn.sum fun i _ ↦ ?_
    have hg_cd : ContDiffOn ℝ n (fun p : X × ℂ ↦ c i * g i p.2) (s ×ˢ Ω) :=
      (((((hg i).const_mul (c i)).contDiffOn hΩ).restrict_scalars ℝ).of_le le_top).comp
        contDiffOn_snd fun _ hp ↦ hp.2
    have hf_ζ : ContDiffOn ℝ n (fun p : X × ℂ ↦ f p.1 (ζ i)) (s ×ˢ Ω) :=
      hf.comp (contDiffOn_fst.prodMk contDiffOn_const) fun _ hp ↦ ⟨hp.1, (hζ i).1⟩
    exact hg_cd.smul hf_ζ
  · exact fun hfq ↦ DifferentiableAt.fun_sum fun i _ ↦ (hfq i).const_smul _
  · intro X _ _ F _ _ s hs f k M hf_cd hf_hol x hx hM w hw
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
