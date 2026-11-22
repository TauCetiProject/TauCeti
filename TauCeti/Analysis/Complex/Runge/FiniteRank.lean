/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Complex.Runge.Operator
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Complex.MixedDeriv
import TauCeti.Geometry.Manifold.ContMDiff.Prod

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
(`TauCeti.iteratedFDeriv_fun_sum_const_smul`, `TauCeti.iteratedFDeriv_sub_sum_const_smul`) yields a
parametric Runge approximation operator that preserves joint smoothness and external complex
holomorphy, commutes with parameter differentiation, and bounds every iterated parameter derivative
uniformly by `ε * M` on `K`.

## Main results

* `TauCeti.IsFilledIn.exists_norm_iteratedFDeriv_sub_sum_mul_smul_le`: parametric Runge
  approximation factoring through `Fin N → F`, preserving joint smoothness and parameter
  holomorphy, commuting with parameter derivatives, and bounding all iterated parameter derivatives
  uniformly by `ε * M`.
* `TauCeti.IsFilledIn.exists_contMDiffOn_norm_iteratedFDeriv_sub_sum_mul_smul_le`:
  manifold-parameter version giving joint `ContMDiffOn` regularity, parameter holomorphy, chartwise
  commutation with `iteratedFDeriv`, and chartwise uniform `ε * M` bounds on `K`.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Theorems 10.3 and 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.1.
-/

public section

open Set
open scoped Manifold

universe uX uQ uF uHP uP

namespace TauCeti

/-- **Parametric Runge approximation operator.** Let `K` be a compact subset filled in an open set
`Ω ⊆ ℂ`, and let `V ⊇ K` be open. For every `ε > 0` there are finitely many evaluation points
`ζ i ∈ V \ K`, weights `c i : ℂ`, and functions `g i : ℂ → ℂ` holomorphic on `Ω` (depending only
on `K`, `V`, `Ω`, and `ε`) such that the operator `A f x w = ∑ i, (c i * g i w) • f x (ζ i)`,
which factors through the finite sample space `Fin N → F` (and has finite rank when `F = ℂ` or `F`
is finite-dimensional):
1. preserves joint `C^n` smoothness on `s ×ˢ V` to `s ×ˢ Ω`;
2. preserves complex differentiability with respect to an external complex parameter;
3. commutes with `k`-th parameter derivatives `iteratedFDeriv ℝ k`;
4. approximates every `k`-th parameter derivative of a `C^(k+1)` family `f : X → ℂ → F`
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
      (∀ {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
        {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
        {f : X → ℂ → F} {k : ℕ} {x : X} {w : ℂ},
        (∀ i, ContDiffAt ℝ k (fun x' ↦ f x' (ζ i)) x) →
        iteratedFDeriv ℝ k (fun x' ↦ ∑ i, (c i * g i w) • f x' (ζ i)) x =
          ∑ i, (c i * g i w) • iteratedFDeriv ℝ k (fun x' ↦ f x' (ζ i)) x) ∧
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
  refine ⟨N, ζ, c, g, hζ, hg, ?_, ?_, ?_, ?_⟩
  · intro X _ _ F _ _ s n f hf
    refine ContDiffOn.sum fun i _ ↦ ?_
    have hg_cd : ContDiffOn ℝ n (fun p : X × ℂ ↦ c i * g i p.2) (s ×ˢ Ω) :=
      (((((hg i).const_mul (c i)).contDiffOn hΩ).restrict_scalars ℝ).of_le le_top).comp
        contDiffOn_snd fun _ hp ↦ hp.2
    have hf_ζ : ContDiffOn ℝ n (fun p : X × ℂ ↦ f p.1 (ζ i)) (s ×ˢ Ω) :=
      hf.comp (contDiffOn_fst.prodMk contDiffOn_const) fun _ hp ↦ ⟨hp.1, (hζ i).1⟩
    exact hg_cd.smul hf_ζ
  · exact fun hfq ↦ DifferentiableAt.fun_sum fun i _ ↦ (hfq i).const_smul _
  · exact fun hζ_cd ↦ iteratedFDeriv_fun_sum_const_smul (fun i ↦ c i * g i _) fun i _ ↦ hζ_cd i
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

private theorem contDiffOn_chart_prod {EP HP P F : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {I : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {s : Set P} {V : Set ℂ} {n : ℕ}
    [IsManifold I n P] {f : P → ℂ → F}
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) n (Function.uncurry f) (s ×ˢ V)) (p₀ : P) :
    ContDiffOn ℝ n (fun q : EP × ℂ ↦ f ((extChartAt I p₀).symm q.1) q.2)
      (((extChartAt I p₀).target ∩ (extChartAt I p₀).symm ⁻¹' s) ×ˢ V) := by
  have hfst : ContMDiffOn (𝓘(ℝ, EP).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, EP) n Prod.fst
      (((extChartAt I p₀).target ∩ (extChartAt I p₀).symm ⁻¹' s) ×ˢ V) := contMDiffOn_fst
  have hmap : ContMDiffOn (𝓘(ℝ, EP).prod 𝓘(ℝ, ℂ)) (I.prod 𝓘(ℝ, ℂ)) n
      (fun q : EP × ℂ ↦ ((extChartAt I p₀).symm q.1, q.2))
      (((extChartAt I p₀).target ∩ (extChartAt I p₀).symm ⁻¹' s) ×ˢ V) :=
    ((contMDiffOn_extChartAt_symm p₀).comp hfst fun _ hq ↦ hq.1.1).prodMk contMDiffOn_snd
  exact contMDiffOn_iff_contDiffOn.1 <| contMDiffOn_prod_modelWithCornersSelf_iff.1 <|
    hf.comp hmap fun _ hq ↦ ⟨hq.1.2, hq.2⟩

/-- **Manifold-parameter Runge approximation operator.** For a compact set `K` filled in an open
set `Ω ⊆ ℂ` and an open neighbourhood `V ⊇ K`, the finite-sample operator
`A f p w = ∑ i, (c i * g i w) • f p (ζ i)` (factoring through `Fin N → F`, and finite-rank for
`F = ℂ` or finite-dimensional `F`):
1. preserves joint `ContMDiffOn` smoothness on `s ×ˢ V` to `s ×ˢ Ω` for any manifold `P`;
2. preserves complex differentiability with respect to an external complex parameter;
3. commutes with chartwise `k`-th parameter derivatives `iteratedFDeriv ℝ k`;
4. approximates every chartwise `k`-th parameter derivative of a `C^(k+1)` manifold family
   holomorphic in the second variable on `V` within `ε * M` on `K`. -/
theorem IsFilledIn.exists_contMDiffOn_norm_iteratedFDeriv_sub_sum_mul_smul_le {K V Ω : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hV : IsOpen V)
    (hKV : K ⊆ V) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (ζ : Fin N → ℂ) (c : Fin N → ℂ) (g : Fin N → ℂ → ℂ),
      (∀ i, ζ i ∈ V \ K) ∧ (∀ i, DifferentiableOn ℂ (g i) Ω) ∧
      (∀ {EP : Type uX} {HP : Type uHP} {P : Type uP} {F : Type uF}
        [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
        {I : ModelWithCorners ℝ EP HP} [TopologicalSpace P] [ChartedSpace HP P]
        [NormedAddCommGroup F] [NormedSpace ℂ F]
        {s : Set P} {n : WithTop ℕ∞} {f : P → ℂ → F},
        ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) n (Function.uncurry f) (s ×ˢ V) →
        ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) n
          (fun p : P × ℂ ↦ ∑ i, (c i * g i p.2) • f p.1 (ζ i)) (s ×ˢ Ω)) ∧
      (∀ {Q : Type uQ} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
        {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
        {f : Q → ℂ → F} {q₀ : Q} {w : ℂ},
        (∀ i, DifferentiableAt ℂ (fun q ↦ f q (ζ i)) q₀) →
        DifferentiableAt ℂ (fun q ↦ ∑ i, (c i * g i w) • f q (ζ i)) q₀) ∧
      (∀ {EP : Type uX} {HP : Type uHP} {P : Type uP} {F : Type uF}
        [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
        {I : ModelWithCorners ℝ EP HP} [I.Boundaryless]
        [TopologicalSpace P] [ChartedSpace HP P]
        [NormedAddCommGroup F] [NormedSpace ℂ F]
        {s : Set P}, IsOpen s → ∀ {f : P → ℂ → F} {k : ℕ} [IsManifold I (k : ℕ) P],
        ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) k (Function.uncurry f) (s ×ˢ V) →
        ∀ p₀ : P, ∀ x ∈ (extChartAt I p₀).target ∩ (extChartAt I p₀).symm ⁻¹' s, ∀ w : ℂ,
          iteratedFDeriv ℝ k
              (fun x' ↦ ∑ i, (c i * g i w) • f ((extChartAt I p₀).symm x') (ζ i)) x =
            ∑ i, (c i * g i w) •
              iteratedFDeriv ℝ k (fun x' ↦ f ((extChartAt I p₀).symm x') (ζ i)) x) ∧
      ∀ {EP : Type uX} {HP : Type uHP} {P : Type uP} {F : Type uF}
        [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
        {I : ModelWithCorners ℝ EP HP} [I.Boundaryless]
        [TopologicalSpace P] [ChartedSpace HP P]
        [NormedAddCommGroup F] [NormedSpace ℂ F]
        {s : Set P}, IsOpen s → ∀ (f : P → ℂ → F) (k : ℕ) [IsManifold I (k + 1 : ℕ) P] (M : ℝ),
        ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) (k + 1 : ℕ) (Function.uncurry f) (s ×ˢ V) →
        (∀ p ∈ s, DifferentiableOn ℂ (f p) V) →
        ∀ p₀ : P, ∀ x ∈ (extChartAt I p₀).target ∩ (extChartAt I p₀).symm ⁻¹' s,
          (∀ z ∈ V, ‖iteratedFDeriv ℝ k (fun x' ↦ f ((extChartAt I p₀).symm x') z) x‖ ≤ M) →
          ∀ w ∈ K,
            ‖iteratedFDeriv ℝ k (fun x' ↦ f ((extChartAt I p₀).symm x') w -
              ∑ i, (c i * g i w) • f ((extChartAt I p₀).symm x') (ζ i)) x‖ ≤ ε * M := by
  obtain ⟨N, ζ, c, g, hζ, hg, -, ha_q, hcomm, happrox⟩ :=
    hfill.exists_norm_iteratedFDeriv_sub_sum_mul_smul_le.{uX, uQ, uF} hΩ hK hKΩ hV hKV hε
  refine ⟨N, ζ, c, g, hζ, hg, ?_, ha_q, ?_, ?_⟩
  · intro EP HP P F _ _ _ I _ _ _ _ s n f hf
    have hsmul : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) 𝓘(ℝ, F) n (fun q : ℂ × F ↦ q.1 • q.2) := by
      rw [contMDiff_prod_modelWithCornersSelf_iff]
      exact ((contDiff_fst.smul contDiff_snd).of_le le_top).contMDiff
    refine contMDiffOn_finsetSum fun i _ ↦ ?_
    have hg_cd :
        ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) n (fun p : P × ℂ ↦ c i * g i p.2) (s ×ˢ Ω) :=
      (((((hg i).const_mul (c i)).contDiffOn hΩ).restrict_scalars ℝ).of_le le_top).contMDiffOn.comp
        contMDiffOn_snd fun _ hp ↦ hp.2
    have hf_ζ :
        ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) n (fun p : P × ℂ ↦ f p.1 (ζ i)) (s ×ˢ Ω) :=
      hf.comp (contMDiffOn_fst.prodMk contMDiffOn_const) fun _ hp ↦ ⟨hp.1, (hζ i).1⟩
    exact hsmul.comp_contMDiffOn (hg_cd.prodMk hf_ζ)
  · intro EP HP P F _ _ _ I _ _ _ _ _ s hs f k _ hf p₀ x hx w
    have hs' : IsOpen ((extChartAt I p₀).target ∩ (extChartAt I p₀).symm ⁻¹' s) :=
      (continuousOn_extChartAt_symm p₀).isOpen_inter_preimage (isOpen_extChartAt_target p₀) hs
    have hcd := contDiffOn_chart_prod hf p₀
    refine hcomm fun i ↦ (hcd.contDiffAt ((hs'.prod hV).mem_nhds ⟨hx, (hζ i).1⟩)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  · intro EP HP P F _ _ _ I _ _ _ _ _ s hs f k _ M hf hhol p₀ x hx hM w hw
    have hs' : IsOpen ((extChartAt I p₀).target ∩ (extChartAt I p₀).symm ⁻¹' s) :=
      (continuousOn_extChartAt_symm p₀).isOpen_inter_preimage (isOpen_extChartAt_target p₀) hs
    exact happrox hs' (fun x' z ↦ f ((extChartAt I p₀).symm x') z) k M (contDiffOn_chart_prod hf p₀)
      (fun x' hx' ↦ hhol _ hx'.2) x hx hM w hw

end TauCeti
