/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Defs
public import Mathlib.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.TangentCone.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.NeumannMaximumPrinciple

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
(`TauCeti.JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg`). When `dα` tames `J`, that is
`dα(v, J v) ≥ 0`, the function `ρ ∘ u` is subharmonic
(`TauCeti.JHolomorphic.laplacian_comp_nonneg_of_fderiv_comp_eq_neg`).

The weak maximum principle then confines `J`-holomorphic curves: if the conditions above hold on
the region `{ρ > R}`, a curve on a compact domain whose boundary is mapped into `{ρ ≤ R}` lies
entirely in `{ρ ≤ R}` (`TauCeti.JHolomorphic.comp_le_of_comp_le_frontier`). Applied to large
rectangles, the same holds for a strip `ℝ × [0, 1]` which maps its two boundary lines and its two
ends `|ℜ z| ≥ T` into `{ρ ≤ R}`
(`TauCeti.JHolomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends`).

The boundary lines of a strip need not lie in `{ρ ≤ R}`. On the cylindrical end, an exact
Lagrangian that is conical at infinity, of the form `[R, ∞) × Λ` for a Legendrian `Λ`, has
`α|TL = 0`. If the two boundary lines of a `J`-holomorphic strip lie on such Lagrangians `L₀`
and `L₁`, the Cauchy--Riemann equation turns this into the Neumann condition
`∂ₜ(ρ ∘ u) = -α(∂ₛu) = 0` on the boundary
(`TauCeti.JHolomorphic.fderiv_comp_apply_I_eq_neg_of_fderiv_comp_eq_neg`), because `∂ₛu` is
tangent to the Lagrangian. The weak maximum principle with a Neumann condition
(`TauCeti.le_of_laplacian_nonneg_of_lt_of_neumann`) then confines the strip to `{ρ ≤ R}` as soon
as its two ends are (`TauCeti.JHolomorphic.comp_le_of_comp_le_strip_ends`). The condition on the
Lagrangians is stated through the tangent cone, `α x v = 0` for `v ∈ tangentConeAt ℝ L x`, which
for a submanifold is the condition `α|TL = 0`.

The statements are in local coordinates, with `ρ`, `α` and `J` on the model space `V`, and cover
only unperturbed `J`-holomorphic curves: `J` depends on the point of `V` but not on the point of
the domain, and the equation carries no Hamiltonian term. Floer strips with a domain-dependent
`J` or a Hamiltonian perturbation, and the passage from a manifold to local coordinates, are not
treated here.

The results live in the organisational namespace `TauCeti.JHolomorphic`: their names describe
conclusions about `ρ ∘ u`, which only hold for curves solving the Cauchy--Riemann equation.

## Main results

* `TauCeti.JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg`: `Δ(ρ ∘ u) = dα(∂ₛu, ∂ₜu)` for a
  `J`-holomorphic curve when `dρ ∘ J = -α`.
* `TauCeti.JHolomorphic.laplacian_comp_nonneg_of_fderiv_comp_eq_neg`: if moreover `dα` tames `J`,
  then `ρ ∘ u` is subharmonic.
* `TauCeti.JHolomorphic.comp_le_of_comp_le_frontier`: a `J`-holomorphic curve on a compact domain
  with boundary in `{ρ ≤ R}` lies in `{ρ ≤ R}`.
* `TauCeti.JHolomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends`: the same for a strip
  whose boundary lines and ends lie in `{ρ ≤ R}`.
* `TauCeti.JHolomorphic.fderiv_comp_apply_I_eq_neg_of_fderiv_comp_eq_neg`: `∂ₜ(ρ ∘ u) = -α(∂ₛu)`
  for a `J`-holomorphic curve when `dρ ∘ J = -α`.
* `TauCeti.JHolomorphic.comp_le_of_comp_le_strip_ends`: a strip with boundary on Lagrangians
  satisfying `α|TL = 0` on `{ρ > R}` lies in `{ρ ≤ R}` once its ends do.

## References

* M. Abouzaid and P. Seidel, *An open string analogue of Viterbo functoriality*, Geom. Topol.
  **14** (2010), 627--718; arXiv:0712.3177v2, Lemma 7.2 (the maximum principle for the radial
  coordinate on the cylindrical end).
-/

public section

namespace TauCeti.JHolomorphic

open InnerProductSpace Laplacian Filter Topology Complex Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {u : ℂ → V} {J : V → V →L[ℝ] V} {α : V → V →L[ℝ] ℝ} {ρ : V → ℝ} {z : ℂ}

/-- **The normal derivative of the radial coordinate along a `J`-holomorphic curve.** If `u`
solves the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` at `z` and `dρ ∘ J = -α` at `u z`, then
`∂ₜ(ρ ∘ u)(z) = -α(∂ₛu)`. -/
theorem fderiv_comp_apply_I_eq_neg_of_fderiv_comp_eq_neg (hu : DifferentiableAt ℝ u z)
    (hρ : DifferentiableAt ℝ ρ (u z)) (hCR : fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hρJ : (fderiv ℝ ρ (u z)).comp (J (u z)) = -α (u z)) :
    fderiv ℝ (ρ ∘ u) z I = -α (u z) (fderiv ℝ u z 1) := by
  have := congr($hρJ (fderiv ℝ u z 1))
  simp only [ContinuousLinearMap.comp_apply, neg_apply] at this
  rw [fderiv_comp z hρ hu, ContinuousLinearMap.comp_apply, hCR, this]

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
    filter_upwards [hnear] with y ⟨hu', hρ', hCR', _, hρJ'⟩
    exact fderiv_comp_apply_I_eq_neg_of_fderiv_comp_eq_neg hu' hρ' hCR' hρJ'
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
of `TauCeti.JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg`, if the exterior derivative
`dα` tames `J` at `u z`, that is `dα(v, J v) ≥ 0` for every `v`, then `Δ(ρ ∘ u)(z) ≥ 0`. -/
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
  -- `ρ ∘ u` is subharmonic wherever it exceeds `R`, so the weak maximum principle above the level
  -- `R` applies.
  refine le_of_laplacian_nonneg_of_lt_le_frontier hK hf (fun w hw hRw ↦ ?_) (fun w hw hRw ↦ ?_)
    (fun w hw ↦ hbdry w hw) hz
  · exact (hρ _ hRw).comp w (hu w hw)
  · have hnhds : ∀ᶠ x in 𝓝 (u w), R < ρ x := (hρ _ hRw).continuousAt.eventually (lt_mem_nhds hRw)
    exact laplacian_comp_nonneg_of_fderiv_comp_eq_neg (hu w hw)
      (eventually_of_mem (isOpen_interior.mem_nhds hw) hCR) (hρ _ hRw) (hα _ hRw)
      (hnhds.mono hJsq) (hnhds.mono hρJ) (htame _ hRw)

/-- **No escape for strips.** Suppose that on the region `{ρ > R}` the function `ρ` is `C²`, the
one-form `α` is differentiable, the maps `J` square to `-1`, `dρ ∘ J = -α`, and `dα` tames `J`.
Let `u` be `C²` and `J`-holomorphic on the open strip `ℝ × (0, 1)`, with `ρ ∘ u` continuous on
the closed strip `ℝ × [0, 1]`. If `u` maps both boundary lines `ℑ z = 0` and `ℑ z = 1` into
`{ρ ≤ R}`, and also the two ends `|ℜ z| ≥ T` of the strip for some `T`, then `u` maps the whole
strip into `{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_strip_boundary_of_comp_le_ends {R T : ℝ}
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
  refine comp_le_of_comp_le_frontier (isCompact_Icc.reProdIm isCompact_Icc)
    (hf.mono hsub) (fun w hw ↦ ?_) (fun w hw ↦ ?_) hρ hα hJsq hρJ htame (fun w hw ↦ ?_)
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

/-- **No escape for strips with Lagrangian boundary.** Suppose that on the region `{ρ > R}` the
function `ρ` is `C²`, the one-form `α` is differentiable, the maps `J` square to `-1`,
`dρ ∘ J = -α`, and `dα` tames `J`. Let `L₀` and `L₁` be subsets of `V` on which `α` vanishes in
the tangent directions over `{ρ > R}`: `α x v = 0` whenever `x ∈ Lᵢ`, `R < ρ x` and `v` lies in
the tangent cone of `Lᵢ` at `x`. Let `u` be `C²` on the open strip `ℝ × (0, 1)`, differentiable
on its boundary lines, and `J`-holomorphic on the closed strip `ℝ × [0, 1]`, with `ρ ∘ u`
continuous there, mapping the line `ℑ z = 0` into `L₀` and the line `ℑ z = 1` into `L₁`. If `u`
maps the two ends `|ℜ z| ≥ T` of the strip into `{ρ ≤ R}`, then it maps the whole strip into
`{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_strip_ends {R T : ℝ} {L₀ L₁ : Set V}
    (hf : ContinuousOn (ρ ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → ContDiffAt ℝ 2 u z)
    (hub : ∀ z : ℂ, z.im = 0 ∨ z.im = 1 → DifferentiableAt ℝ u z)
    (hCR : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hρ : ∀ x, R < ρ x → ContDiffAt ℝ 2 ρ x)
    (hα : ∀ x, R < ρ x → DifferentiableAt ℝ α x)
    (hJsq : ∀ x, R < ρ x → ∀ v, J x (J x v) = -v)
    (hρJ : ∀ x, R < ρ x → (fderiv ℝ ρ x).comp (J x) = -α x)
    (htame : ∀ x, R < ρ x → ∀ v, 0 ≤ fderiv ℝ α x v (J x v) - fderiv ℝ α x (J x v) v)
    (h₀ : ∀ z : ℂ, z.im = 0 → u z ∈ L₀) (h₁ : ∀ z : ℂ, z.im = 1 → u z ∈ L₁)
    (hL₀ : ∀ x ∈ L₀, R < ρ x → ∀ v ∈ tangentConeAt ℝ L₀ x, α x v = 0)
    (hL₁ : ∀ x ∈ L₁, R < ρ x → ∀ v ∈ tangentConeAt ℝ L₁ x, α x v = 0)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → ρ (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : ρ (u z) ≤ R := by
  -- On a boundary line `ℑ w = c` mapped into `L`, the derivative `∂ₛu` is tangent to `L`, so
  -- `∂ₜ(ρ ∘ u) = -α(∂ₛu)` vanishes wherever `ρ ∘ u > R`.
  have hneu : ∀ (L : Set V) (c : ℝ), (∀ w : ℂ, w.im = c → u w ∈ L) →
      (∀ x ∈ L, R < ρ x → ∀ v ∈ tangentConeAt ℝ L x, α x v = 0) → ∀ w : ℂ, w.im = c →
      DifferentiableAt ℝ u w → 0 ≤ w.im → w.im ≤ 1 → R < ρ (u w) →
        fderiv ℝ (ρ ∘ u) w I = 0 := by
    intro L c hL hαL w hw hdu hw₀ hw₁ hRw
    -- `∂ₛu` is the velocity of the curve `s ↦ u (s + i c)` in `L`.
    have hγ : HasDerivAt (fun s : ℝ ↦ u (s + w.im * I)) (fderiv ℝ u w 1) w.re := by
      have hl : HasDerivAt (fun s : ℝ ↦ (s : ℂ) + w.im * I) 1 w.re :=
        ofRealCLM.hasDerivAt.add_const _
      rw [← re_add_im w] at hdu
      simpa [re_add_im, Function.comp_def] using hdu.hasFDerivAt.comp_hasDerivAt w.re hl
    have htan : fderiv ℝ u w 1 ∈ tangentConeAt ℝ L (u w) := by
      simpa [re_add_im] using
        hγ.mem_tangentConeAt (Filter.Eventually.of_forall fun s ↦ hL _ (by simp [hw]))
    rw [fderiv_comp_apply_I_eq_neg_of_fderiv_comp_eq_neg hdu
      ((hρ _ hRw).differentiableAt (by norm_num)) (hCR w hw₀ hw₁) (hρJ _ hRw),
      hαL _ (hL w hw) hRw _ htan, neg_zero]
  -- Apply the maximum principle with a Neumann condition on a rectangle `[-S, S] × [0, 1]`
  -- containing `z`, with `S ≥ T`.
  set S := max T |z.re|
  have hsub : Icc (-S) S ×ℂ Icc 0 1 ⊆ univ ×ℂ Icc 0 1 := fun w hw ↦ ⟨mem_univ _, hw.2⟩
  refine le_of_laplacian_nonneg_of_lt_of_neumann zero_lt_one (hf.mono hsub)
    (fun w hw hRw ↦ (hρ _ hRw).comp w (hu w hw.2.1 hw.2.2)) (fun w hw hRw ↦ ?_)
    (fun w hw hRw ↦ ?_) (fun w hw hRw ↦ ?_) (fun w hw hRw ↦ ?_) (fun w hw ↦ ?_)
    ⟨abs_le.mp (le_max_right _ _), hz₀, hz₁⟩
  · have hnhds : ∀ᶠ x in 𝓝 (u w), R < ρ x := (hρ _ hRw).continuousAt.eventually (lt_mem_nhds hRw)
    have hopen : {w' : ℂ | 0 < w'.im ∧ w'.im < 1} ∈ 𝓝 w :=
      (isOpen_lt continuous_const continuous_im |>.inter
        (isOpen_lt continuous_im continuous_const)).mem_nhds hw.2
    exact laplacian_comp_nonneg_of_fderiv_comp_eq_neg (hu w hw.2.1 hw.2.2)
      (Filter.mem_of_superset hopen fun w' hw' ↦ hCR w' hw'.1.le hw'.2.le) (hρ _ hRw) (hα _ hRw)
      (hnhds.mono hJsq) (hnhds.mono hρJ) (htame _ hRw)
  · exact ((hρ _ hRw).differentiableAt (by norm_num)).comp w (hub w hw.2)
  · have hw0 : w.im = 0 := hw.2
    rw [hneu L₀ 0 h₀ hL₀ w hw0 (hub w (Or.inl hw0)) hw0.ge (by rw [hw0]; norm_num) hRw]
  · have hw1 : w.im = 1 := hw.2
    rw [hneu L₁ 1 h₁ hL₁ w hw1 (hub w (Or.inr hw1)) (by rw [hw1]; norm_num) hw1.le hRw]
  · refine hends w ?_ hw.2.1 hw.2.2
    rcases hw.1 with hw' | hw' <;> rw [hw'] <;>
      simp [S, abs_of_nonneg ((abs_nonneg _).trans (le_max_right T |z.re|))]

end TauCeti.JHolomorphic
