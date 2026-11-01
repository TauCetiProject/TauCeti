/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The maximum principle for `J`-holomorphic curves in a cylindrical end

Let `V` be a real normed space carrying a family `J : V → (V →L[ℝ] V)` of linear maps with
`J(x)² = -1`, an almost complex structure written in local coordinates, a one-form
`α : V → (V →L[ℝ] ℝ)` and a function `ρ : V → ℝ`. On the cylindrical end of a Liouville
completion, where `ρ` is the radial coordinate and `α` the Liouville primitive, an almost complex
structure of contact type satisfies

`dρ ∘ J = -α`.

A map `u : ℂ → V`, with `s + i t` the coordinate on `ℂ`, is `J`-holomorphic when it solves the
Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu`. For such a curve the function `ρ ∘ u` has derivatives
`∂ₛ(ρ ∘ u) = α(∂ₜu)` and `∂ₜ(ρ ∘ u) = -α(∂ₛu)`, and therefore

`Δ(ρ ∘ u) = dα(∂ₛu, ∂ₜu) = dα(∂ₛu, J ∂ₛu)`,

where `dα(v, w) = Dα(v)(w) - Dα(w)(v)` is the exterior derivative of `α`
(`TauCeti.laplacian_comp_eq_of_fderiv_comp_eq_neg`). When `dα` tames `J`, that is
`dα(v, J v) ≥ 0`, the function `ρ ∘ u` is subharmonic
(`TauCeti.laplacian_comp_nonneg_of_fderiv_comp_eq_neg`).

The weak maximum principle then confines `J`-holomorphic curves: if the conditions above hold on
the region `{ρ > R}`, a curve on a compact domain whose boundary is mapped into `{ρ ≤ R}` lies
entirely in `{ρ ≤ R}` (`TauCeti.comp_le_of_comp_le_frontier`). Applied to large rectangles, the
same holds for a strip `ℝ × [0, 1]` which maps its two boundary lines and its two ends
`|ℜ z| ≥ T` into `{ρ ≤ R}` (`TauCeti.comp_le_of_comp_le_strip_frontier`). This is the no-escape
argument for Floer strips in an exact symplectic manifold with a cylindrical end: a strip with
Lagrangian boundary conditions in `{ρ ≤ R}` whose ends converge uniformly to chords in `{ρ < R}`
satisfies these hypotheses, and so stays in `{ρ ≤ R}`.

The statements are in local coordinates, with `ρ`, `α` and `J` on the model space `V`.

## Main results

* `TauCeti.laplacian_comp_eq_of_fderiv_comp_eq_neg`: `Δ(ρ ∘ u) = dα(∂ₛu, ∂ₜu)` for a
  `J`-holomorphic curve when `dρ ∘ J = -α`.
* `TauCeti.laplacian_comp_nonneg_of_fderiv_comp_eq_neg`: if moreover `dα` tames `J`, then
  `ρ ∘ u` is subharmonic.
* `TauCeti.comp_le_of_comp_le_frontier`: a `J`-holomorphic curve on a compact domain with
  boundary in `{ρ ≤ R}` lies in `{ρ ≤ R}`.
* `TauCeti.comp_le_of_comp_le_strip_frontier`: the same for a strip whose boundary lines and ends
  lie in `{ρ ≤ R}`.

## References

* M. Abouzaid and P. Seidel, *An open string analogue of Viterbo functoriality*, Geom. Topol.
  **14** (2010), 627--718; arXiv:0712.3177v2, Lemma 7.2 (the maximum principle for the radial
  coordinate on the cylindrical end).
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian Filter Topology Complex Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {u : ℂ → V} {J : V → V →L[ℝ] V} {α : V → V →L[ℝ] ℝ} {ρ : V → ℝ} {z : ℂ}

/-- **The Laplacian of the radial coordinate along a `J`-holomorphic curve.** Let `u : ℂ → V` be
`C²` at `z` and solve the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` near `z`. Suppose that near
`u z` the maps `J` square to `-1` and `dρ ∘ J = -α`, where `ρ` is `C²` and `α` is differentiable
at `u z`. Then

`Δ(ρ ∘ u)(z) = Dα(∂ₛu)(∂ₜu) - Dα(∂ₜu)(∂ₛu)`,

the exterior derivative `dα` evaluated on `(∂ₛu, ∂ₜu)`. -/
theorem laplacian_comp_eq_of_fderiv_comp_eq_neg (hu : ContDiffAt ℝ 2 u z)
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hρ : ContDiffAt ℝ 2 ρ (u z)) (hα : DifferentiableAt ℝ α (u z))
    (hJsq : ∀ᶠ x in 𝓝 (u z), ∀ v, J x (J x v) = -v)
    (hρJ : ∀ᶠ x in 𝓝 (u z), (fderiv ℝ ρ x).comp (J x) = -α x) :
    Δ (ρ ∘ u) z = fderiv ℝ α (u z) (fderiv ℝ u z 1) (fderiv ℝ u z I) -
      fderiv ℝ α (u z) (fderiv ℝ u z I) (fderiv ℝ u z 1) := by
  have hcont : ContinuousAt u z := hu.continuousAt
  have hf : ContDiffAt ℝ 2 (ρ ∘ u) z := hρ.comp z hu
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDf : DifferentiableAt ℝ (fderiv ℝ (ρ ∘ u)) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- Near `z`, the first derivatives of `ρ ∘ u` are `α(∂ₜu)` and `-α(∂ₛu)`.
  have hnear : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ u y ∧ DifferentiableAt ℝ ρ (u y) ∧
      fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1) ∧ (∀ v, J (u y) (J (u y) v) = -v) ∧
      (fderiv ℝ ρ (u y)).comp (J (u y)) = -α (u y) := by
    filter_upwards [(hu.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num),
      hcont.eventually ((hρ.eventually (by simp)).mono fun x hx ↦ hx.differentiableAt
        (by norm_num)), hCR, hcont.eventually hJsq, hcont.eventually hρJ] with y h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hs : (fun y ↦ fderiv ℝ (ρ ∘ u) y 1) =ᶠ[𝓝 z] fun y ↦ α (u y) (fderiv ℝ u y I) := by
    filter_upwards [hnear] with y h
    obtain ⟨hu', hρ', hCR', hJsq', hρJ'⟩ := h
    have hs' : fderiv ℝ u y 1 = -J (u y) (fderiv ℝ u y I) := by rw [hCR', hJsq', neg_neg]
    have := congr($hρJ' (fderiv ℝ u y I))
    simp only [ContinuousLinearMap.comp_apply, neg_apply] at this
    rw [fderiv_comp y hρ' hu', ContinuousLinearMap.comp_apply, hs', map_neg, this, neg_neg]
  have ht : (fun y ↦ fderiv ℝ (ρ ∘ u) y I) =ᶠ[𝓝 z] fun y ↦ -α (u y) (fderiv ℝ u y 1) := by
    filter_upwards [hnear] with y h
    obtain ⟨hu', hρ', hCR', -, hρJ'⟩ := h
    have := congr($hρJ' (fderiv ℝ u y 1))
    simp only [ContinuousLinearMap.comp_apply, neg_apply] at this
    rw [fderiv_comp y hρ' hu', ContinuousLinearMap.comp_apply, hCR', this]
  -- Differentiate `y ↦ α (u y) (∂_w u y)` in the direction `a`.
  have hg (w a : ℂ) : fderiv ℝ (fun y ↦ α (u y) (fderiv ℝ u y w)) z a =
      fderiv ℝ α (u z) (fderiv ℝ u z a) (fderiv ℝ u z w) +
        α (u z) (fderiv ℝ (fderiv ℝ u) z a w) := by
    have hu' : DifferentiableAt ℝ u z := hu.differentiableAt (by norm_num)
    rw [fderiv_clm_apply (c := fun y ↦ α (u y)) (hα.comp z hu')
      (hDu.clm_apply (differentiableAt_const w))]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      fderiv_fun_comp z hα hu', fderiv_clm_apply_const_apply hDu]
    rw [add_comm]
  have hsymm : fderiv ℝ (fderiv ℝ u) z I 1 = fderiv ℝ (fderiv ℝ u) z 1 I :=
    hu.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) I 1
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [← fderiv_clm_apply_const_apply hDf, ← fderiv_clm_apply_const_apply hDf, hs.fderiv_eq,
    ht.fderiv_eq, fderiv_fun_neg, neg_apply, hg, hg, hsymm]
  abel

/-- **The radial coordinate is subharmonic along a `J`-holomorphic curve.** Under the hypotheses
of `TauCeti.laplacian_comp_eq_of_fderiv_comp_eq_neg`, if the exterior derivative `dα` tames `J`
at `u z`, that is `dα(v, J v) ≥ 0` for every `v`, then `Δ(ρ ∘ u)(z) ≥ 0`. -/
theorem laplacian_comp_nonneg_of_fderiv_comp_eq_neg (hu : ContDiffAt ℝ 2 u z)
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J (u y) (fderiv ℝ u y 1))
    (hρ : ContDiffAt ℝ 2 ρ (u z)) (hα : DifferentiableAt ℝ α (u z))
    (hJsq : ∀ᶠ x in 𝓝 (u z), ∀ v, J x (J x v) = -v)
    (hρJ : ∀ᶠ x in 𝓝 (u z), (fderiv ℝ ρ x).comp (J x) = -α x)
    (htame : ∀ v, 0 ≤ fderiv ℝ α (u z) v (J (u z) v) - fderiv ℝ α (u z) (J (u z) v) v) :
    0 ≤ Δ (ρ ∘ u) z := by
  rw [laplacian_comp_eq_of_fderiv_comp_eq_neg hu hCR hρ hα hJsq hρJ, hCR.self_of_nhds]
  exact htame _

/-- **The maximum principle for `J`-holomorphic curves in a cylindrical end.** Suppose that on
the region `{ρ > R}` the function `ρ` is `C²`, the one-form `α` is differentiable, the maps `J`
square to `-1`, `dρ ∘ J = -α`, and `dα` tames `J`. Let `K ⊆ ℂ` be compact and `u` be `C²` and
`J`-holomorphic on the interior of `K`, with `ρ ∘ u` continuous on `K`. If `u` maps the frontier
of `K` into `{ρ ≤ R}`, then it maps all of `K` into `{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_frontier {R : ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hf : ContinuousOn (ρ ∘ u) K) (hu : ∀ z ∈ interior K, ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ interior K, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hρ : ∀ x, R < ρ x → ContDiffAt ℝ 2 ρ x)
    (hα : ∀ x, R < ρ x → DifferentiableAt ℝ α x)
    (hJsq : ∀ x, R < ρ x → ∀ v, J x (J x v) = -v)
    (hρJ : ∀ x, R < ρ x → (fderiv ℝ ρ x).comp (J x) = -α x)
    (htame : ∀ x, R < ρ x → ∀ v, 0 ≤ fderiv ℝ α x v (J x v) - fderiv ℝ α x (J x v) v)
    (hbdry : ∀ z ∈ frontier K, ρ (u z) ≤ R) (hz : z ∈ K) : ρ (u z) ≤ R := by
  -- Apply the weak maximum principle to the compact superlevel set `K' = {ρ ∘ u ≥ R + ε}`, on
  -- whose interior `ρ ∘ u` is subharmonic and on whose frontier `ρ ∘ u ≤ R + ε`.
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set K' := K ∩ (ρ ∘ u) ⁻¹' Ici (R + ε) with hK'
  have hK'c : IsClosed K' := hf.preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici
  by_cases hzK' : z ∈ K'
  swap
  · simp only [hK', mem_inter_iff, hz, mem_preimage, Function.comp_apply, mem_Ici,
      true_and, not_le] at hzK'
    exact hzK'.le
  -- Interior points of `K'` are interior points of `K` mapped into `{ρ > R}`.
  have hint : ∀ w ∈ interior K', w ∈ interior K ∧ R < ρ (u w) := fun w hw ↦ by
    have h : R + ε ≤ ρ (u w) := (interior_subset hw).2
    exact ⟨interior_mono inter_subset_left hw, by linarith⟩
  refine le_of_laplacian_nonneg_le_frontier (hK.of_isClosed_subset hK'c inter_subset_left)
    (hf.mono inter_subset_left) (fun w hw ↦ ?_) (fun w hw ↦ ?_) (fun w hw ↦ ?_) hzK'
  · obtain ⟨hwK, hRw⟩ := hint w hw
    exact (hρ _ hRw).comp w (hu w hwK)
  · obtain ⟨hwK, hRw⟩ := hint w hw
    have hnhds : ∀ᶠ x in 𝓝 (u w), R < ρ x := (hρ _ hRw).continuousAt.eventually (lt_mem_nhds hRw)
    exact laplacian_comp_nonneg_of_fderiv_comp_eq_neg (hu w hwK)
      (eventually_of_mem (isOpen_interior.mem_nhds hwK) hCR) (hρ _ hRw) (hα _ hRw)
      (hnhds.mono hJsq) (hnhds.mono hρJ) (htame _ hRw)
  · have hwK' : w ∈ K' := hK'c.frontier_subset hw
    by_contra hlt
    rw [not_le, Function.comp_apply] at hlt
    by_cases hwK : w ∈ frontier K
    · linarith [hbdry w hwK]
    -- Otherwise `w` is an interior point of `K` with `ρ (u w) > R + ε`, hence interior to `K'`.
    have hwint : w ∈ interior K := by
      by_contra hw'
      exact hwK (hK.isClosed.frontier_eq ▸ ⟨hwK'.1, hw'⟩)
    have hKw : K ∈ 𝓝 w := mem_interior_iff_mem_nhds.mp hwint
    exact hw.2 (mem_interior_iff_mem_nhds.mpr (inter_mem hKw
      ((hf.continuousAt hKw).preimage_mem_nhds (Ici_mem_nhds hlt))))

/-- **No escape for strips.** Suppose that on the region `{ρ > R}` the function `ρ` is `C²`, the
one-form `α` is differentiable, the maps `J` square to `-1`, `dρ ∘ J = -α`, and `dα` tames `J`.
Let `u` be `C²` and `J`-holomorphic on the open strip `ℝ × (0, 1)`, with `ρ ∘ u` continuous on
the closed strip `ℝ × [0, 1]`. If `u` maps both boundary lines `ℑ z = 0` and `ℑ z = 1` into
`{ρ ≤ R}`, and also the two ends `|ℜ z| ≥ T` of the strip for some `T`, then `u` maps the whole
strip into `{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_strip_frontier {R T : ℝ}
    (hf : ContinuousOn (ρ ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → ContDiffAt ℝ 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hρ : ∀ x, R < ρ x → ContDiffAt ℝ 2 ρ x)
    (hα : ∀ x, R < ρ x → DifferentiableAt ℝ α x)
    (hJsq : ∀ x, R < ρ x → ∀ v, J x (J x v) = -v)
    (hρJ : ∀ x, R < ρ x → (fderiv ℝ ρ x).comp (J x) = -α x)
    (htame : ∀ x, R < ρ x → ∀ v, 0 ≤ fderiv ℝ α x v (J x v) - fderiv ℝ α x (J x v) v)
    (h₀ : ∀ z : ℂ, z.im = 0 → ρ (u z) ≤ R) (h₁ : ∀ z : ℂ, z.im = 1 → ρ (u z) ≤ R)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → ρ (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : ρ (u z) ≤ R := by
  -- Apply the maximum principle on a rectangle `[-S, S] × [0, 1]` containing `z`, with `S ≥ T`.
  set S := max T |z.re|
  have hS : 0 ≤ S := (abs_nonneg _).trans (le_max_right _ _)
  have hsub : Icc (-S) S ×ℂ Icc 0 1 ⊆ univ ×ℂ Icc 0 1 := fun w hw ↦ ⟨mem_univ _, hw.2⟩
  refine comp_le_of_comp_le_frontier (isCompact_Icc.reProdIm isCompact_Icc) (hf.mono hsub)
    (fun w hw ↦ ?_) (fun w hw ↦ ?_) hρ hα hJsq hρJ htame (fun w hw ↦ ?_)
    ⟨abs_le.mp (le_max_right _ _), hz₀, hz₁⟩
  · rw [interior_reProdIm, interior_Icc, interior_Icc] at hw
    exact hu w hw.2.1 hw.2.2
  · rw [interior_reProdIm, interior_Icc, interior_Icc] at hw
    exact hCR w hw.2.1 hw.2.2
  · rw [frontier_reProdIm, closure_Icc, closure_Icc, frontier_Icc zero_le_one,
      frontier_Icc (by linarith)] at hw
    rcases hw with ⟨-, hw | hw⟩ | ⟨hw, hw₀, hw₁⟩
    · exact h₀ w hw
    · exact h₁ w hw
    · refine hends w ?_ hw₀ hw₁
      rcases hw with hw | hw <;> rw [hw] <;> simp [S, abs_of_nonneg hS]

end TauCeti
