/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.InnerProductSpace.Laplacian.NeumannMaximumPrinciple
public import TauCeti.Analysis.InnerProductSpace.Laplacian.WeakMaximumPrinciple
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.TangentCone.Real
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
Cauchy--Riemann equation `∂ₜu = J_z(u) ∂ₛu`. Here `J_z` may depend on the point `z` of the domain,
as the almost complex structures of continuation strips and of parametrized families of Floer
strips do. For such a curve the function `ρ ∘ u` has derivatives
`∂ₛ(ρ ∘ u) = α(∂ₜu)` and `∂ₜ(ρ ∘ u) = -α(∂ₛu)`, and therefore

`Δ(ρ ∘ u) = dα(∂ₛu, ∂ₜu) = dα(∂ₛu, J ∂ₛu)`,

where `dα(v, w) = Dα(v)(w) - Dα(w)(v)` is the exterior derivative of `α`
(`TauCeti.JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg`). When `dα` tames `J`, that is
`dα(v, J v) ≥ 0`, the function `ρ ∘ u` is subharmonic
(`TauCeti.JHolomorphic.laplacian_comp_nonneg_of_fderiv_comp_eq_neg`). The derivative of `J_z` in
`z` does not enter: the Cauchy--Riemann equation is used only to rewrite the first derivatives of
`ρ ∘ u`, so no regularity of `J_z` in `z` is needed.

The weak maximum principle then confines `J`-holomorphic curves: if the conditions above hold on
the region `{ρ > R}` for every `J_z`, a curve on a compact domain whose boundary is mapped into
`{ρ ≤ R}` lies entirely in `{ρ ≤ R}` (`TauCeti.JHolomorphic.comp_le_of_comp_le_frontier`). The
curve need only be `C²` and solve the Cauchy--Riemann equation at the points which it maps into
`{ρ > R}`. So the statements apply to Floer strips `∂ₜu = J_z(u) ∂ₛu + X_z(u)` whose Hamiltonian
vector fields `X_z` vanish on `{ρ > R}`, as for continuation strips between Hamiltonians which
are constant outside a compact set contained in `{ρ ≤ R}`. Applied to large
rectangles, the same holds for a strip `ℝ × [0, 1]` which maps its two boundary lines and its two
ends `|ℜ z| ≥ T` into `{ρ ≤ R}`
(`TauCeti.JHolomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends`).

The boundary lines of the strip need not stay in `{ρ ≤ R}`. On the cylindrical end, a Lagrangian
which is cylindrical at infinity is tangent to the Liouville field `Z`, so the Liouville primitive
`α = ι_Z ω` vanishes on it: `α|TL = 0`. If the boundary line `ℑ z = 0` is mapped into such a
Lagrangian, then `∂ₛu` is tangent to it, and the Cauchy--Riemann equation gives the Neumann
condition `∂ₜ(ρ ∘ u) = dρ(J ∂ₛu) = -α(∂ₛu) = 0` along that line. A maximum of `ρ ∘ u` above `R`
on the boundary is then excluded by the weak maximum principle with Neumann boundary conditions
(`TauCeti.le_of_laplacian_nonneg_of_neumann_of_le_ends`). So a strip whose ends lie in
`{ρ ≤ R}` lies in `{ρ ≤ R}` when each boundary line either stays in `{ρ ≤ R}` or moves, outside
`{ρ ≤ R}`, only in directions on which `α` vanishes
(`TauCeti.JHolomorphic.comp_le_of_neumann_of_comp_le_strip_ends`), in particular when each
boundary line is mapped into a set on whose tangent cones `α` vanishes outside `{ρ ≤ R}`
(`TauCeti.JHolomorphic.comp_le_of_mapsTo_of_comp_le_strip_ends`). Along the boundary lines `u` is
only asked to be differentiable within the closed strip, as a solution smooth up to the boundary
is.

The statements are in local coordinates, with `ρ`, `α` and `J` on the model space `V`. A
Hamiltonian term which does not vanish on `{ρ > R}` is not treated here. The statements for a
compact set and for a strip with boundary lines in `{ρ ≤ R}`, for curves in an almost complex
manifold, are in `TauCeti/Geometry/Symplectic/Manifold/MaximumPrinciple.lean`.

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
* `TauCeti.JHolomorphic.comp_le_of_neumann_of_comp_le_strip_ends`: the same for a strip whose ends
  lie in `{ρ ≤ R}` and whose boundary lines satisfy `α(∂ₛu) = 0` outside `{ρ ≤ R}`.
* `TauCeti.JHolomorphic.comp_le_of_mapsTo_of_comp_le_strip_ends`: the same for a strip whose ends
  lie in `{ρ ≤ R}` and whose boundary lines are mapped into sets on whose tangent cones `α`
  vanishes outside `{ρ ≤ R}`, such as exact Lagrangians cylindrical at infinity.

## References

* M. Abouzaid and P. Seidel, *An open string analogue of Viterbo functoriality*, Geom. Topol.
  **14** (2010), 627--718; arXiv:0712.3177v2, Lemma 7.2 (the maximum principle for the radial
  coordinate on the cylindrical end).
-/

public section

namespace TauCeti.JHolomorphic

open InnerProductSpace Laplacian Filter Topology Complex Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {u : ℂ → V} {J : ℂ → V → V →L[ℝ] V} {α : V → V →L[ℝ] ℝ} {ρ : V → ℝ} {z : ℂ}

/-- **The Laplacian of the radial coordinate along a `J`-holomorphic curve.** Let `u : ℂ → V` be
`C²` at `z` and solve the Cauchy--Riemann equation `∂ₜu = J_y(u) ∂ₛu` near `z`, for a family of
almost complex structures `J_y` depending on the point `y` of the domain. Suppose that near `z`
the maps `J_y (u y)` square to `-1` and `dρ ∘ J_y = -α` at `u y`, where `ρ` is `C²` and `α` is
differentiable at `u z`. Then

`Δ(ρ ∘ u)(z) = Dα(∂ₛu)(∂ₜu) - Dα(∂ₜu)(∂ₛu)`,

the exterior derivative `dα` evaluated on `(∂ₛu, ∂ₜu)`. No regularity of `J` in `y` is needed. -/
theorem laplacian_comp_eq_of_fderiv_comp_eq_neg (hu : ContDiffAt ℝ 2 u z)
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J y (u y) (fderiv ℝ u y 1))
    (hρ : ContDiffAt ℝ 2 ρ (u z)) (hα : DifferentiableAt ℝ α (u z))
    (hJsq : ∀ᶠ y in 𝓝 z, ∀ v, J y (u y) (J y (u y) v) = -v)
    (hρJ : ∀ᶠ y in 𝓝 z, (fderiv ℝ ρ (u y)).comp (J y (u y)) = -α (u y)) :
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
      fderiv ℝ u y I = J y (u y) (fderiv ℝ u y 1) ∧ (∀ v, J y (u y) (J y (u y) v) = -v) ∧
      (fderiv ℝ ρ (u y)).comp (J y (u y)) = -α (u y) := by
    filter_upwards [(hu.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num),
      hcont.eventually ((hρ.eventually (by simp)).mono fun x hx ↦ hx.differentiableAt
        (by norm_num)), hCR, hJsq, hρJ] with y h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  have hs : (fun y ↦ fderiv ℝ (ρ ∘ u) y 1) =ᶠ[𝓝 z] fun y ↦ α (u y) (fderiv ℝ u y I) := by
    filter_upwards [hnear] with y h
    obtain ⟨hu', hρ', hCR', hJsq', hρJ'⟩ := h
    have hs' : fderiv ℝ u y 1 = -J y (u y) (fderiv ℝ u y I) := by rw [hCR', hJsq', neg_neg]
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
of `TauCeti.JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg`, if the exterior derivative
`dα` tames `J_z` at `u z`, that is `dα(v, J_z v) ≥ 0` for every `v`, then `Δ(ρ ∘ u)(z) ≥ 0`. -/
theorem laplacian_comp_nonneg_of_fderiv_comp_eq_neg (hu : ContDiffAt ℝ 2 u z)
    (hCR : ∀ᶠ y in 𝓝 z, fderiv ℝ u y I = J y (u y) (fderiv ℝ u y 1))
    (hρ : ContDiffAt ℝ 2 ρ (u z)) (hα : DifferentiableAt ℝ α (u z))
    (hJsq : ∀ᶠ y in 𝓝 z, ∀ v, J y (u y) (J y (u y) v) = -v)
    (hρJ : ∀ᶠ y in 𝓝 z, (fderiv ℝ ρ (u y)).comp (J y (u y)) = -α (u y))
    (htame : ∀ v, 0 ≤ fderiv ℝ α (u z) v (J z (u z) v) - fderiv ℝ α (u z) (J z (u z) v) v) :
    0 ≤ Δ (ρ ∘ u) z := by
  rw [laplacian_comp_eq_of_fderiv_comp_eq_neg hu hCR hρ hα hJsq hρJ, hCR.self_of_nhds]
  exact htame _

/-- `ρ ∘ u` is `C²` and subharmonic at a point of an open set `U` at which it exceeds `R`, provided
`u` is `C²` and `J`-holomorphic at the points of `U` which it maps into `{ρ > R}`, and the
contact-type hypotheses of the maximum principle hold on `{ρ > R}` for every `J_w`. -/
private theorem contDiffAt_and_laplacian_nonneg {R : ℝ} {U : Set ℂ} (hU : IsOpen U) (hz : z ∈ U)
    (hu : ∀ z ∈ U, R < ρ (u z) → ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ U, R < ρ (u z) → fderiv ℝ u z I = J z (u z) (fderiv ℝ u z 1))
    (hρ : ∀ x, R < ρ x → ContDiffAt ℝ 2 ρ x)
    (hα : ∀ x, R < ρ x → DifferentiableAt ℝ α x)
    (hJsq : ∀ w x, R < ρ x → ∀ v, J w x (J w x v) = -v)
    (hρJ : ∀ w x, R < ρ x → (fderiv ℝ ρ x).comp (J w x) = -α x)
    (htame : ∀ w x, R < ρ x → ∀ v, 0 ≤ fderiv ℝ α x v (J w x v) - fderiv ℝ α x (J w x v) v)
    (hRz : R < ρ (u z)) : ContDiffAt ℝ 2 (ρ ∘ u) z ∧ 0 ≤ Δ (ρ ∘ u) z := by
  have hf : ContDiffAt ℝ 2 (ρ ∘ u) z := (hρ _ hRz).comp z (hu z hz hRz)
  -- Near `z` the curve stays in `U` and in `{ρ > R}`, where it solves the equation.
  have hnear : ∀ᶠ y in 𝓝 z, y ∈ U ∧ R < ρ (u y) :=
    Filter.Eventually.and (hU.mem_nhds hz) (hf.continuousAt.eventually (lt_mem_nhds hRz))
  exact ⟨hf, laplacian_comp_nonneg_of_fderiv_comp_eq_neg (hu z hz hRz)
    (hnear.mono fun y hy ↦ hCR y hy.1 hy.2) (hρ _ hRz) (hα _ hRz)
    (hnear.mono fun y hy ↦ hJsq y (u y) hy.2) (hnear.mono fun y hy ↦ hρJ y (u y) hy.2)
    (htame z (u z) hRz)⟩

/-- **The maximum principle for `J`-holomorphic curves in a cylindrical end.** Let `J_w` be a
family of almost complex structures depending on the point `w` of the domain. Suppose that on the
region `{ρ > R}` the function `ρ` is `C²`, the one-form `α` is differentiable, and for every `w`
the maps `J_w` square to `-1`, `dρ ∘ J_w = -α`, and `dα` tames `J_w`. Let `K ⊆ ℂ` be compact,
with `ρ ∘ u` continuous on `K`, and let `u` be `C²` and solve `∂ₜu = J_w(u) ∂ₛu` at the points `w`
of the interior of `K` which it maps into `{ρ > R}`. If `u` maps the frontier of `K` into
`{ρ ≤ R}`, then it maps all of `K` into `{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_frontier {R : ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hf : ContinuousOn (ρ ∘ u) K) (hu : ∀ z ∈ interior K, R < ρ (u z) → ContDiffAt ℝ 2 u z)
    (hCR : ∀ z ∈ interior K, R < ρ (u z) → fderiv ℝ u z I = J z (u z) (fderiv ℝ u z 1))
    (hρ : ∀ x, R < ρ x → ContDiffAt ℝ 2 ρ x)
    (hα : ∀ x, R < ρ x → DifferentiableAt ℝ α x)
    (hJsq : ∀ w x, R < ρ x → ∀ v, J w x (J w x v) = -v)
    (hρJ : ∀ w x, R < ρ x → (fderiv ℝ ρ x).comp (J w x) = -α x)
    (htame : ∀ w x, R < ρ x → ∀ v, 0 ≤ fderiv ℝ α x v (J w x v) - fderiv ℝ α x (J w x v) v)
    (hbdry : ∀ z ∈ frontier K, ρ (u z) ≤ R) (hz : z ∈ K) : ρ (u z) ≤ R :=
  -- `ρ ∘ u` is subharmonic wherever it exceeds `R`, so the weak maximum principle above the level
  -- `R` applies.
  le_of_laplacian_nonneg_of_lt_le_frontier hK hf
    (fun _ hw hRw ↦ (contDiffAt_and_laplacian_nonneg isOpen_interior hw hu hCR hρ hα hJsq hρJ
      htame hRw).1)
    (fun _ hw hRw ↦ (contDiffAt_and_laplacian_nonneg isOpen_interior hw hu hCR hρ hα hJsq hρJ
      htame hRw).2)
    (fun w hw ↦ hbdry w hw) hz

/-- **No escape for strips with Neumann boundary conditions.** Let `J_w` be a family of almost
complex structures depending on the point `w` of the strip. Suppose that on the region `{ρ > R}`
the function `ρ` is `C²`, the one-form `α` is differentiable, and for every `w` the maps `J_w`
square to `-1`, `dρ ∘ J_w = -α`, and `dα` tames `J_w`. Let `ρ ∘ u` be continuous on the closed
strip `ℝ × [0, 1]`, let `u` be `C²` and solve `∂ₜu = J_w(u) ∂ₛu` at the points `w` of the open
strip `ℝ × (0, 1)` which it maps into `{ρ > R}`, and suppose that `u` maps the two ends
`|ℜ z| ≥ T` of the strip into `{ρ ≤ R}`. Suppose that at every point `z` of a boundary line
`ℑ z = 0` or `ℑ z = 1` which `u` maps into `{ρ > R}`, the map `u` has a derivative `Du z` within
the closed strip satisfying the Cauchy--Riemann equation `Du z I = J z (u z) (Du z 1)`, and `α`
vanishes on its boundary direction `Du z 1`. Then `u` maps the whole strip into `{ρ ≤ R}`. -/
theorem comp_le_of_neumann_of_comp_le_strip_ends {R T : ℝ} {Du : ℂ → ℂ →L[ℝ] V}
    (hf : ContinuousOn (ρ ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < ρ (u z) → ContDiffAt ℝ 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < ρ (u z) →
      fderiv ℝ u z I = J z (u z) (fderiv ℝ u z 1))
    (hρ : ∀ x, R < ρ x → ContDiffAt ℝ 2 ρ x)
    (hα : ∀ x, R < ρ x → DifferentiableAt ℝ α x)
    (hJsq : ∀ w x, R < ρ x → ∀ v, J w x (J w x v) = -v)
    (hρJ : ∀ w x, R < ρ x → (fderiv ℝ ρ x).comp (J w x) = -α x)
    (htame : ∀ w x, R < ρ x → ∀ v, 0 ≤ fderiv ℝ α x v (J w x v) - fderiv ℝ α x (J w x v) v)
    (hDu : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → R < ρ (u z) →
      HasFDerivWithinAt u (Du z) (univ ×ℂ Icc 0 1) z)
    (hCRbdry : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → R < ρ (u z) → Du z I = J z (u z) (Du z 1))
    (hαbdry : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → R < ρ (u z) → α (u z) (Du z 1) = 0)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → ρ (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : ρ (u z) ≤ R := by
  have hU : IsOpen {w : ℂ | 0 < w.im ∧ w.im < 1} :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hint (w : ℂ) (h₀ : 0 < w.im) (h₁ : w.im < 1) (hRw : R < ρ (u w)) :=
    contDiffAt_and_laplacian_nonneg hU (z := w) ⟨h₀, h₁⟩ (fun y hy ↦ hu y hy.1 hy.2)
      (fun y hy ↦ hCR y hy.1 hy.2) hρ hα hJsq hρJ htame hRw
  -- Along a boundary line outside `{ρ ≤ R}`, `∂ₜ(ρ ∘ u) = dρ(J ∂ₛu) = -α(∂ₛu) = 0`.
  refine le_of_laplacian_nonneg_of_neumann_of_le_ends
    (f' := fun w ↦ (fderiv ℝ ρ (u w)).comp (Du w)) hf
    (fun w h₀ h₁ hRw ↦ (hint w h₀ h₁ hRw).1) (fun w h₀ h₁ hRw ↦ (hint w h₀ h₁ hRw).2)
    (fun w hw hRw ↦ ?_) (fun w hw hRw ↦ ?_) hends hz₀ hz₁
  · exact ((hρ _ hRw).differentiableAt (by norm_num)).hasFDerivAt.comp_hasFDerivWithinAt w
      (hDu w hw hRw)
  · have := congr($(hρJ w _ hRw) (Du w 1))
    simp only [ContinuousLinearMap.comp_apply, neg_apply] at this
    simp only [ContinuousLinearMap.comp_apply, hCRbdry w hw hRw, this, hαbdry w hw hRw, neg_zero]

/-- **No escape for strips.** Let `J_w` be a family of almost complex structures depending on the
point `w` of the strip. Suppose that on the region `{ρ > R}` the function `ρ` is `C²`, the
one-form `α` is differentiable, and for every `w` the maps `J_w` square to `-1`,
`dρ ∘ J_w = -α`, and `dα` tames `J_w`. Let `ρ ∘ u` be continuous on the closed strip
`ℝ × [0, 1]`, and let `u` be `C²` and solve `∂ₜu = J_w(u) ∂ₛu` at the points `w` of the open strip
`ℝ × (0, 1)` which it maps into `{ρ > R}`. If `u` maps both boundary lines `ℑ z = 0` and
`ℑ z = 1` into `{ρ ≤ R}`, and also the two ends `|ℜ z| ≥ T` of the strip for some `T`, then `u`
maps the whole strip into `{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_strip_boundary_of_comp_le_ends {R T : ℝ}
    (hf : ContinuousOn (ρ ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < ρ (u z) → ContDiffAt ℝ 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < ρ (u z) →
      fderiv ℝ u z I = J z (u z) (fderiv ℝ u z 1))
    (hρ : ∀ x, R < ρ x → ContDiffAt ℝ 2 ρ x)
    (hα : ∀ x, R < ρ x → DifferentiableAt ℝ α x)
    (hJsq : ∀ w x, R < ρ x → ∀ v, J w x (J w x v) = -v)
    (hρJ : ∀ w x, R < ρ x → (fderiv ℝ ρ x).comp (J w x) = -α x)
    (htame : ∀ w x, R < ρ x → ∀ v, 0 ≤ fderiv ℝ α x v (J w x v) - fderiv ℝ α x (J w x v) v)
    (h₀ : ∀ z : ℂ, z.im = 0 → ρ (u z) ≤ R) (h₁ : ∀ z : ℂ, z.im = 1 → ρ (u z) ≤ R)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → ρ (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : ρ (u z) ≤ R := by
  -- The boundary lines stay in `{ρ ≤ R}`, so the Neumann hypotheses hold vacuously.
  have hbdry (w : ℂ) (hw : w.im = 0 ∨ w.im = 1) (hRw : R < ρ (u w)) : False :=
    hw.elim (fun h ↦ (h₀ w h).not_gt hRw) fun h ↦ (h₁ w h).not_gt hRw
  exact comp_le_of_neumann_of_comp_le_strip_ends (Du := 0) hf hu hCR hρ hα hJsq hρJ htame
    (fun w hw hRw ↦ (hbdry w hw hRw).elim) (fun w hw hRw ↦ (hbdry w hw hRw).elim)
    (fun w hw hRw ↦ (hbdry w hw hRw).elim) hends hz₀ hz₁

/-- **No escape for strips with boundary on exact cylindrical Lagrangians.** Let `J_w` be a family
of almost complex structures depending on the point `w` of the strip. Suppose that on the region
`{ρ > R}` the function `ρ` is `C²`, the one-form `α` is differentiable, and for every `w` the maps
`J_w` square to `-1`, `dρ ∘ J_w = -α`, and `dα` tames `J_w`. Let `ρ ∘ u` be continuous on the
closed strip `ℝ × [0, 1]`, let `u` be `C²` and solve `∂ₜu = J_w(u) ∂ₛu` at the points `w` of the
open strip `ℝ × (0, 1)` which it maps into `{ρ > R}`, and suppose that `u` maps the two ends
`|ℜ z| ≥ T` of the strip into `{ρ ≤ R}`. Let `u` map the boundary line `ℑ z = 0` into `L₀` and the
line `ℑ z = 1` into `L₁`, where at every point `x` of `Lᵢ` with `R < ρ x` the form `α x` vanishes
on the tangent cone of `Lᵢ` at `x`, as the Liouville primitive does on an exact Lagrangian which
is cylindrical at infinity. Suppose that at every point `z` of a boundary line which `u` maps into
`{ρ > R}`, the map `u` has a derivative `Du z` within the closed strip satisfying the
Cauchy--Riemann equation `Du z I = J z (u z) (Du z 1)`. Then `u` maps the whole strip into
`{ρ ≤ R}`. -/
theorem comp_le_of_mapsTo_of_comp_le_strip_ends {R T : ℝ} {L₀ L₁ : Set V}
    {Du : ℂ → ℂ →L[ℝ] V} (hf : ContinuousOn (ρ ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < ρ (u z) → ContDiffAt ℝ 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < ρ (u z) →
      fderiv ℝ u z I = J z (u z) (fderiv ℝ u z 1))
    (hρ : ∀ x, R < ρ x → ContDiffAt ℝ 2 ρ x)
    (hα : ∀ x, R < ρ x → DifferentiableAt ℝ α x)
    (hJsq : ∀ w x, R < ρ x → ∀ v, J w x (J w x v) = -v)
    (hρJ : ∀ w x, R < ρ x → (fderiv ℝ ρ x).comp (J w x) = -α x)
    (htame : ∀ w x, R < ρ x → ∀ v, 0 ≤ fderiv ℝ α x v (J w x v) - fderiv ℝ α x (J w x v) v)
    (hDu : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → R < ρ (u z) →
      HasFDerivWithinAt u (Du z) (univ ×ℂ Icc 0 1) z)
    (hCRbdry : ∀ z : ℂ, (z.im = 0 ∨ z.im = 1) → R < ρ (u z) → Du z I = J z (u z) (Du z 1))
    (hL₀ : MapsTo u {z : ℂ | z.im = 0} L₀) (hL₁ : MapsTo u {z : ℂ | z.im = 1} L₁)
    (hαL₀ : ∀ x ∈ L₀, R < ρ x → ∀ v ∈ tangentConeAt ℝ L₀ x, α x v = 0)
    (hαL₁ : ∀ x ∈ L₁, R < ρ x → ∀ v ∈ tangentConeAt ℝ L₁ x, α x v = 0)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → ρ (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : ρ (u z) ≤ R := by
  -- Along the line `ℑ w = c`, the boundary direction `Du w 1` is tangent to the image of the
  -- line, hence to the Lagrangian containing it.
  have htangent (c : ℝ) (hc : c ∈ Icc (0 : ℝ) 1) (L : Set V) (hL : MapsTo u {w : ℂ | w.im = c} L)
      (w : ℂ) (hw : w.im = c) (hD : HasFDerivWithinAt u (Du w) (univ ×ℂ Icc 0 1) w) :
      Du w 1 ∈ tangentConeAt ℝ L (u w) := by
    have hline : {y : ℂ | y.im = c} ⊆ univ ×ℂ Icc 0 1 := fun y (hy : y.im = c) ↦
      ⟨mem_univ _, by rw [mem_preimage, hy]; exact hc⟩
    have hone : (1 : ℂ) ∈ tangentConeAt ℝ {y : ℂ | y.im = c} w := by
      have hseg : segment ℝ w (w + 1) ⊆ {y : ℂ | y.im = c} := by
        rw [segment_eq_image']
        rintro _ ⟨θ, -, rfl⟩
        simp [hw]
      simpa using mem_tangentConeAt_of_segment_subset hseg
    exact tangentConeAt_mono hL.image_subset ((hD.mono hline).mapsTo_tangent_cone hone)
  refine comp_le_of_neumann_of_comp_le_strip_ends hf hu hCR hρ hα hJsq hρJ htame hDu hCRbdry
    (fun w hw hRw ↦ ?_) hends hz₀ hz₁
  rcases hw with hw | hw
  · exact hαL₀ _ (hL₀ hw) hRw _
      (htangent 0 ⟨le_rfl, zero_le_one⟩ L₀ hL₀ w hw (hDu w (.inl hw) hRw))
  · exact hαL₁ _ (hL₁ hw) hRw _
      (htangent 1 ⟨zero_le_one, le_rfl⟩ L₁ hL₁ w hw (hDu w (.inr hw) hRw))

end TauCeti.JHolomorphic
