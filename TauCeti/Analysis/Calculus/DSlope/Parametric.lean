/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Analysis.Analytic.ConstantOrder.Basic

/-!
# Joint analyticity of parametric divided differences

For a jointly analytic family `f : E × 𝕜 → F` over `𝕜 = ℝ` or `ℂ` (`[RCLike 𝕜]`) from a normed
`𝕜`-space `E` into a complete normed `𝕜`-space `F`, taking divided differences `dslope · z₀` in
the second variable preserves joint analyticity: if `f` is analytic at both `(x₀, z₀)` and
`(x₀, w₀)`, then `(x, w) ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (x, y)) w` is jointly
analytic at `(x₀, w₀)` (`AnalyticAt.dslope_snd`, `AnalyticAt.iterate_dslope_snd`, and
`AnalyticOnNhd.iterate_dslope_snd`).

Near the diagonal `w₀ = z₀`, this follows from Hadamard's lemma in the distinguished scalar
variable (`AnalyticAt.exists_eventuallyEq_sub_smul`), which constructs the analytic quotient; off
the diagonal, it is `(w - z₀)⁻¹ • (f (x, w) - f (x, z₀))`.

## Main results

* `AnalyticAt.dslope_snd`: joint analyticity of the second-variable divided difference.
* `AnalyticAt.iterate_dslope_snd`: joint analyticity of the `n`-th iterated second-variable
  divided difference at a point.
* `AnalyticOnNhd.iterate_dslope_snd`: joint analyticity of the `n`-th iterated second-variable
  divided difference on a set closed under `(x, w) ↦ (x, z₀)`.
-/

public section

open Filter Metric Topology

section ParametricDSlope

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- If `f : E × 𝕜 → F` is jointly analytic at `(x₀, z₀)` and at `(x₀, w₀)` with `F` complete,
then the second-variable divided difference `(x, w) ↦ dslope (fun y ↦ f (x, y)) z₀ w` is jointly
analytic at `(x₀, w₀)`. -/
theorem AnalyticAt.dslope_snd {f : E × 𝕜 → F} {x₀ : E} {z₀ w₀ : 𝕜}
    (hf₀ : AnalyticAt 𝕜 f (x₀, z₀)) (hf : AnalyticAt 𝕜 f (x₀, w₀)) :
    AnalyticAt 𝕜 (fun p : E × 𝕜 ↦ dslope (fun y ↦ f (p.1, y)) z₀ p.2) (x₀, w₀) := by
  rcases eq_or_ne w₀ z₀ with rfl | hne
  · let G : E × 𝕜 → F := fun p ↦ f p - f (p.1, w₀)
    have hG : AnalyticAt 𝕜 G (x₀, w₀) :=
      hf₀.sub (hf₀.comp_of_eq (analyticAt_fst.prod analyticAt_const) rfl)
    obtain ⟨H, hH, hGH⟩ := hG.exists_eventuallyEq_sub_smul (.of_forall fun _ ↦ sub_self _)
    have hH_nhds : ∀ᶠ p : E × 𝕜 in 𝓝 (x₀, w₀), AnalyticAt 𝕜 H p :=
      (isOpen_analyticAt 𝕜 H).mem_nhds hH
    obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp (hGH.and hH_nhds)
    refine hH.congr (eventually_of_mem (prod_mem_nhds hU hV) ?_)
    rintro ⟨x, w⟩ ⟨hx, hw⟩
    have hrel : ∀ y ∈ V, f (x, y) - f (x, w₀) = (y - w₀) • H (x, y) := fun y hy ↦
      (hUV (Set.mk_mem_prod hx hy)).1
    dsimp only
    symm
    rcases eq_or_ne w w₀ with rfl | hwz
    · have hHz : AnalyticAt 𝕜 H (x, w) := (hUV (Set.mk_mem_prod hx hw)).2
      have hHy : HasDerivAt (fun y : 𝕜 ↦ H (x, y)) (deriv (fun y : 𝕜 ↦ H (x, y)) w) w :=
        (hHz.comp (analyticAt_const.prod analyticAt_id)).differentiableAt.hasDerivAt
      have hprod : HasDerivAt (fun y : 𝕜 ↦ (y - w) • H (x, y) + f (x, w))
          ((w - w) • deriv (fun y : 𝕜 ↦ H (x, y)) w + (1 : 𝕜) • H (x, w)) w :=
        (((hasDerivAt_id w).sub_const w).smul hHy).add_const (f (x, w))
      have hderiv : HasDerivAt (fun y : 𝕜 ↦ f (x, y)) (H (x, w)) w := by
        have h' : HasDerivAt (fun y : 𝕜 ↦ f (x, y))
            ((w - w) • deriv (fun y : 𝕜 ↦ H (x, y)) w + (1 : 𝕜) • H (x, w)) w :=
          hprod.congr_of_eventuallyEq
            (eventually_of_mem hV fun y hy ↦ eq_add_of_sub_eq (hrel y hy))
        simpa only [sub_self, zero_smul, zero_add, one_smul] using h'
      rw [dslope_same, hderiv.deriv]
    · rw [dslope_of_ne _ hwz, slope_def_module, hrel w hw,
        inv_smul_smul₀ (sub_ne_zero.mpr hwz)]
  · have hfx₀ : AnalyticAt 𝕜 (fun p : E × 𝕜 ↦ f (p.1, z₀)) (x₀, w₀) :=
      hf₀.comp_of_eq (analyticAt_fst.prod analyticAt_const) rfl
    have hq : AnalyticAt 𝕜 (fun p : E × 𝕜 ↦ (p.2 - z₀)⁻¹ • (f p - f (p.1, z₀))) (x₀, w₀) :=
      ((analyticAt_snd.sub analyticAt_const).inv (sub_ne_zero.mpr hne)).smul (hf.sub hfx₀)
    refine hq.congr ?_
    filter_upwards [continuousAt_snd.eventually_ne hne] with p hp
    symm
    rw [dslope_of_ne _ hp, slope_def_module]

/-- If `f : E × 𝕜 → F` is jointly analytic at `(x₀, z₀)` and at `(x₀, w₀)` with `F` complete,
then for every `n : ℕ` the `n`-th iterated divided difference
`(x, w) ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (x, y)) w` is jointly analytic at `(x₀, w₀)`. -/
theorem AnalyticAt.iterate_dslope_snd {f : E × 𝕜 → F} {x₀ : E} {z₀ w₀ : 𝕜}
    (hf₀ : AnalyticAt 𝕜 f (x₀, z₀)) (hf : AnalyticAt 𝕜 f (x₀, w₀)) :
    ∀ n : ℕ, AnalyticAt 𝕜
      (fun p : E × 𝕜 ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (p.1, y)) p.2) (x₀, w₀)
  | 0 => by simpa only [Function.iterate_zero_apply] using hf
  | n + 1 => by
    have ih₀ : AnalyticAt 𝕜
        (fun p : E × 𝕜 ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (p.1, y)) p.2) (x₀, z₀) :=
      hf₀.iterate_dslope_snd hf₀ n
    have ih : AnalyticAt 𝕜
        (fun p : E × 𝕜 ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (p.1, y)) p.2) (x₀, w₀) :=
      hf₀.iterate_dslope_snd hf n
    simpa only [Function.iterate_succ_apply'] using ih₀.dslope_snd ih

/-- If `f : E × 𝕜 → F` into a complete space `F` is analytic on `S` and `∀ p ∈ S, (p.1, z₀) ∈ S`,
then for every `n : ℕ` the `n`-th iterated second-variable divided difference at `z₀` is analytic
on `S`. -/
theorem AnalyticOnNhd.iterate_dslope_snd {f : E × 𝕜 → F} {S : Set (E × 𝕜)} {z₀ : 𝕜}
    (hf : AnalyticOnNhd 𝕜 f S) (hz₀ : ∀ p ∈ S, (p.1, z₀) ∈ S) (n : ℕ) :
    AnalyticOnNhd 𝕜
      (fun p : E × 𝕜 ↦ (Function.swap dslope z₀)^[n] (fun y ↦ f (p.1, y)) p.2) S :=
  fun p hp ↦ (hf (p.1, z₀) (hz₀ p hp)).iterate_dslope_snd (hf p hp) n

end ParametricDSlope
