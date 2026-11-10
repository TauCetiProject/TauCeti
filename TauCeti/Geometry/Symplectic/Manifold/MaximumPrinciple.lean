/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.MaximumPrinciple
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Defs
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The maximum principle for `J`-holomorphic curves in an almost complex manifold

Let `M` be a manifold without boundary carrying a smooth almost complex structure `J`, a one-form
`α` and a function `ρ : M → ℝ` with

`dρ ∘ J = -α`.

On the cylindrical end of a Liouville completion, `ρ` is the radial coordinate and `α` the Liouville
primitive, and this is the condition that `J` is of contact type. A map `u : ℂ → M`, with
`s + i t` the coordinate on `ℂ`, is `J`-holomorphic when it solves the Cauchy--Riemann equation
`∂ₜu = J_z(u) ∂ₛu`, written here with the manifold derivative of `u`. The almost complex structure
`J_z` may depend on the point `z` of the domain, with no regularity in `z`, as for continuation
strips and parametrized families of Floer strips. For such a curve

`Δ(ρ ∘ u) = dα(∂ₛu, ∂ₜu) = dα(∂ₛu, J ∂ₛu)`

(`TauCeti.Pseudoholomorphic.laplacian_comp_eq_of_mvfderiv_comp_eq_neg`), so `ρ ∘ u` is
subharmonic where `dα` tames `J`
(`TauCeti.Pseudoholomorphic.laplacian_comp_nonneg_of_mvfderiv_comp_eq_neg`).
The proof reads `u`, `ρ`, `α` and `J` in the extended chart at `u z` and applies the computation
in local coordinates, `TauCeti.JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg`; the
exterior derivative of `α` at `u z` is computed in that same chart.

The weak maximum principle then confines `J`-holomorphic curves to `{ρ ≤ R}` when the conditions
above hold on `{ρ > R}`: a curve on a compact domain whose boundary is mapped into `{ρ ≤ R}`
(`TauCeti.Pseudoholomorphic.comp_le_of_comp_le_frontier`), and a strip `ℝ × [0, 1]` whose two
boundary lines and two ends `|ℜ z| ≥ T` are mapped into `{ρ ≤ R}`
(`TauCeti.Pseudoholomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends`). These are the
manifold forms of the statements in local coordinates in
`TauCeti/Geometry/Symplectic/JHolomorphic/MaximumPrinciple.lean`. The curve need only be `C²` and
solve the Cauchy--Riemann equation at the points which it maps into `{ρ > R}`, so the statements
apply to Floer strips whose Hamiltonian vector fields vanish on `{ρ > R}`.

The results live in the organisational namespace `TauCeti.Pseudoholomorphic`, the manifold
counterpart of `TauCeti.JHolomorphic` (see `TauCeti/Geometry/Symplectic/Manifold/JHolomorphic.lean`
for the naming).

## Main results

* `TauCeti.Pseudoholomorphic.laplacian_comp_eq_of_mvfderiv_comp_eq_neg`:
  `Δ(ρ ∘ u) = dα(∂ₛu, ∂ₜu)` for a `J`-holomorphic curve when `dρ ∘ J = -α`.
* `TauCeti.Pseudoholomorphic.laplacian_comp_nonneg_of_mvfderiv_comp_eq_neg`: if moreover `dα`
  tames `J`, then `ρ ∘ u` is subharmonic.
* `TauCeti.Pseudoholomorphic.comp_le_of_comp_le_frontier`: a `J`-holomorphic curve on a compact
  domain with boundary in `{ρ ≤ R}` lies in `{ρ ≤ R}`.
* `TauCeti.Pseudoholomorphic.comp_le_of_comp_le_strip_boundary_of_comp_le_ends`: the same for a
  strip whose boundary lines and ends lie in `{ρ ≤ R}`.

## References

* M. Abouzaid and P. Seidel, *An open string analogue of Viterbo functoriality*, Geom. Topol.
  **14** (2010), 627--718; arXiv:0712.3177v2, Lemma 7.2 (the maximum principle for the radial
  coordinate on the cylindrical end).
-/

public section

namespace TauCeti.Pseudoholomorphic

open InnerProductSpace Laplacian Filter Topology Complex Set Bundle
open scoped _root_.Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {J : ℂ → SmoothAlmostComplexStructure I M} {α : RoughForm I M ℝ 1}
  {ρ : M → ℝ} {u : ℂ → M} {z : ℂ}

/-- **The Laplacian of `ρ` along a `J`-holomorphic curve in a manifold.** Let `u : ℂ → M` be
`C²` at `z` and solve the Cauchy--Riemann equation `∂ₜu = J_w(u) ∂ₛu` near `z`, for a family of
almost complex structures `J_w` depending on the point `w` of the domain. Let `α` be a one-form
differentiable at `u z` and `ρ` a function `C²` at `u z` with `dρ ∘ J_w = -α` at `u w` for `w`
near `z`. Then

`Δ(ρ ∘ u)(z) = dα(∂ₛu, ∂ₜu)`.

No regularity of `J_w` in `w` is needed. -/
theorem laplacian_comp_eq_of_mvfderiv_comp_eq_neg
    (hu : ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ᶠ w in 𝓝 z,
      mfderiv 𝓘(ℝ, ℂ) I u w (Complex.I : ℂ) = J w (u w) (mfderiv 𝓘(ℝ, ℂ) I u w (1 : ℂ)))
    (hρ : ContMDiffAt I 𝓘(ℝ) 2 ρ (u z))
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) (u z))
    (hρJ : ∀ᶠ w in 𝓝 z, ∀ v, mvfderiv I ρ (u w) (J w (u w) v) = -α (u w) ![v]) :
    Δ (ρ ∘ u) z = mextDeriv α (u z)
      ![mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ), mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ)] := by
  -- Read `u`, `ρ`, `J` and `α` in the extended chart `φ` at `u z`, check the hypotheses of the
  -- computation in local coordinates `JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg`, and
  -- identify its right-hand side with `mextDeriv α`, which is computed in that same chart.
  -- `L` turns a one-form `E [⋀^Fin 1]→L[ℝ] ℝ` into a linear form `E →L[ℝ] ℝ`.
  let L : (E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm.toContinuousLinearEquiv
      |>.toContinuousLinearMap
  have hL (a : E [⋀^Fin 1]→L[ℝ] ℝ) (v : E) : L a v = a (fun _ ↦ v) := by
    simp [L, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]
  have hrange : range I = univ := I.range_eq_univ
  have hsrc : ∀ᶠ w in 𝓝 z, u w ∈ (extChartAt I (u z)).source :=
    hu.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (u z))
  have htgt : (extChartAt I (u z)).target ∈ 𝓝 (extChartAt I (u z) (u z)) :=
    extChartAt_target_mem_nhds (u z)
  -- Regularity of the coordinate expressions.
  have huc : ContDiffAt ℝ 2 (extChartAt I (u z) ∘ u) z :=
    contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_extChartAt (x := u z)).comp z hu)
  have hρc : ContDiffAt ℝ 2 (ρ ∘ (extChartAt I (u z)).symm) (extChartAt I (u z) (u z)) := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := 2) (u z)
    rw [hrange, contMDiffWithinAt_univ] at h
    exact contMDiffAt_iff_contDiffAt.1 (hρ.comp_of_eq h (extChartAt_to_inv (u z)))
  have hω : DifferentiableAt ℝ (α.inChartAt (u z)) ((extChartAt I (u z) ∘ u) z) :=
    α.differentiableAt_inChartAt hα
  -- The three identities of the computation in local coordinates, for the structures `J_w` read
  -- in the chart at `u z`.
  have hJsq : ∀ᶠ w in 𝓝 z, ∀ v, (J w).inChart (u z) ((extChartAt I (u z) ∘ u) w)
      ((J w).inChart (u z) ((extChartAt I (u z) ∘ u) w) v) = -v := by
    filter_upwards [hsrc] with w hw v
    exact (J w).inChart_inChart (u z) ((extChartAt I (u z)).map_source hw) v
  have hCRc : ∀ᶠ w in 𝓝 z, fderiv ℝ (extChartAt I (u z) ∘ u) w Complex.I =
      (J w).inChart (u z) ((extChartAt I (u z) ∘ u) w)
        (fderiv ℝ (extChartAt I (u z) ∘ u) w 1) := by
    filter_upwards [hCR, hsrc, ContMDiffAt.eventually_mdifferentiableAt hu two_ne_zero]
      with w hw hws hwd
    exact (J w).fderiv_extChartAt_comp_apply_eq_inChart (u z) hwd hws hw
  have hρJc : ∀ᶠ w in 𝓝 z,
      (fderiv ℝ (ρ ∘ (extChartAt I (u z)).symm) ((extChartAt I (u z) ∘ u) w)).comp
        ((J w).inChart (u z) ((extChartAt I (u z) ∘ u) w)) =
        -L (α.inChartAt (u z) ((extChartAt I (u z) ∘ u) w)) := by
    filter_upwards [hsrc, huc.continuousAt.eventually ((hρc.eventually (by simp)).mono
      fun e he ↦ he.differentiableAt (by norm_num)), hρJ] with w hws hed hJ
    have he := (extChartAt I (u z)).map_source hws
    ext v
    rw [ContinuousLinearMap.comp_apply, neg_apply, hL, Function.comp_apply,
      (J w).fderiv_comp_extChartAt_symm_inChart_apply (u z) he hed,
      (extChartAt I (u z)).left_inv hws, hJ, RoughForm.inChartAt_apply,
      (extChartAt I (u z)).left_inv hws]
    congr 2
    funext i
    fin_cases i
    rfl
  -- The computation in the chart, transported back.
  have hloc := JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg
    (J := fun w ↦ (J w).inChart (u z)) huc hCRc hρc (L.differentiableAt.comp _ hω) hJsq hρJc
  have heq : ρ ∘ u =ᶠ[𝓝 z] (ρ ∘ (extChartAt I (u z)).symm) ∘ (extChartAt I (u z) ∘ u) := by
    filter_upwards [hsrc] with w hw
    simp only [Function.comp_apply, (extChartAt I (u z)).left_inv hw]
  have hDα (a b : E) :
      fderiv ℝ (L ∘ α.inChartAt (u z)) ((extChartAt I (u z) ∘ u) z) a b =
        fderiv ℝ (α.inChartAt (u z)) (extChartAt I (u z) (u z)) a (fun _ ↦ b) := by
    rw [(L.hasFDerivAt.comp _ hω.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply, hL]
    -- The base points `(φ ∘ u) z` and `φ (u z)` agree by `Function.comp_apply`.
    rfl
  -- The chart at `u z` has the identity as derivative there.
  have hD₀ (v : ℂ) : fderiv ℝ (extChartAt I (u z) ∘ u) z v = mfderiv 𝓘(ℝ, ℂ) I u z v := by
    rw [(hu.mdifferentiableAt (by norm_num)).fderiv_extChartAt_comp_apply
      (mem_extChartAt_source (u z)), mfderiv_extChartAt_self]
    -- The identity of the tangent space at `u z` applied to `mfderiv u z v`.
    rfl
  have hR (a b : E) : mextDeriv α (u z) ![a, b] =
      fderiv ℝ (α.inChartAt (u z)) (extChartAt I (u z) (u z)) a (fun _ ↦ b) -
        fderiv ℝ (α.inChartAt (u z)) (extChartAt I (u z) (u z)) b (fun _ ↦ a) := by
    rw [mextDeriv_def, hrange, extDerivWithin_univ]
    exact extDeriv_apply_pair _ _ _
  rw [(laplacian_congr_nhds heq).self_of_nhds, hloc, hDα, hDα, hD₀, hD₀]
  exact (hR _ _).symm

/-- **The radial coordinate is subharmonic along a `J`-holomorphic curve in a manifold.** Under
the hypotheses of `TauCeti.Pseudoholomorphic.laplacian_comp_eq_of_mvfderiv_comp_eq_neg`, if the
exterior derivative `dα` tames `J_z` at `u z`, that is `dα(v, J_z v) ≥ 0` for every `v`, then
`Δ(ρ ∘ u)(z) ≥ 0`. -/
theorem laplacian_comp_nonneg_of_mvfderiv_comp_eq_neg (hu : ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ᶠ w in 𝓝 z,
      mfderiv 𝓘(ℝ, ℂ) I u w (Complex.I : ℂ) = J w (u w) (mfderiv 𝓘(ℝ, ℂ) I u w (1 : ℂ)))
    (hρ : ContMDiffAt I 𝓘(ℝ) 2 ρ (u z))
    (hα : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) (u z))
    (hρJ : ∀ᶠ w in 𝓝 z, ∀ v, mvfderiv I ρ (u w) (J w (u w) v) = -α (u w) ![v])
    (htame : ∀ v, 0 ≤ mextDeriv α (u z) ![v, J z (u z) v]) :
    0 ≤ Δ (ρ ∘ u) z := by
  rw [laplacian_comp_eq_of_mvfderiv_comp_eq_neg hu hCR hρ hα hρJ, hCR.self_of_nhds]
  exact htame _

/-- `ρ ∘ u` is `C²` and subharmonic at a point of an open set `U` at which it exceeds `R`, provided
`u` is `C²` and `J`-holomorphic at the points of `U` which it maps into `{ρ > R}`, and the
hypotheses of the maximum principle hold on `{ρ > R}` for every `J_w`. -/
private theorem contDiffAt_and_laplacian_nonneg {R : ℝ} {U : Set ℂ} (hU : IsOpen U) (hz : z ∈ U)
    (hu : ∀ z ∈ U, R < ρ (u z) → ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z ∈ U, R < ρ (u z) →
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J z (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hρ : ∀ x, R < ρ x → ContMDiffAt I 𝓘(ℝ) 2 ρ x)
    (hα : ∀ x, R < ρ x → MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hρJ : ∀ w x, R < ρ x → ∀ v, mvfderiv I ρ x (J w x v) = -α x ![v])
    (htame : ∀ w x, R < ρ x → ∀ v, 0 ≤ mextDeriv α x ![v, J w x v]) (hRz : R < ρ (u z)) :
    ContDiffAt ℝ 2 (ρ ∘ u) z ∧ 0 ≤ Δ (ρ ∘ u) z := by
  have hf : ContDiffAt ℝ 2 (ρ ∘ u) z :=
    contMDiffAt_iff_contDiffAt.1 ((hρ _ hRz).comp z (hu z hz hRz))
  -- Near `z` the curve stays in `U` and in `{ρ > R}`, where it solves the equation.
  have hnear : ∀ᶠ y in 𝓝 z, y ∈ U ∧ R < ρ (u y) :=
    Filter.Eventually.and (hU.mem_nhds hz) (hf.continuousAt.eventually (lt_mem_nhds hRz))
  exact ⟨hf, laplacian_comp_nonneg_of_mvfderiv_comp_eq_neg (hu z hz hRz)
    (hnear.mono fun y hy ↦ hCR y hy.1 hy.2) (hρ _ hRz) (hα _ hRz)
    (hnear.mono fun y hy ↦ hρJ y (u y) hy.2) (htame z (u z) hRz)⟩

/-- **The maximum principle for `J`-holomorphic curves in a manifold.** Let `J_w` be a family of
almost complex structures depending on the point `w` of the domain. Suppose that on the region
`{ρ > R}` the function `ρ` is `C²`, and for every `w`, `dρ ∘ J_w = -α` for a one-form `α`
differentiable there, and `dα` tames `J_w`. Let `K ⊆ ℂ` be compact, with `ρ ∘ u` continuous on
`K`, and let `u` be `C²` and solve `∂ₜu = J_w(u) ∂ₛu` at the points `w` of the interior of `K`
which it maps into `{ρ > R}`. If `u` maps the frontier of `K` into `{ρ ≤ R}`, then it maps all of
`K` into `{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_frontier {R : ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hf : ContinuousOn (ρ ∘ u) K)
    (hu : ∀ z ∈ interior K, R < ρ (u z) → ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z ∈ interior K, R < ρ (u z) →
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J z (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hρ : ∀ x, R < ρ x → ContMDiffAt I 𝓘(ℝ) 2 ρ x)
    (hα : ∀ x, R < ρ x → MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hρJ : ∀ w x, R < ρ x → ∀ v, mvfderiv I ρ x (J w x v) = -α x ![v])
    (htame : ∀ w x, R < ρ x → ∀ v, 0 ≤ mextDeriv α x ![v, J w x v])
    (hbdry : ∀ z ∈ frontier K, ρ (u z) ≤ R) (hz : z ∈ K) : ρ (u z) ≤ R :=
  le_of_laplacian_nonneg_of_lt_le_frontier hK hf
    (fun _ hw hRw ↦ (contDiffAt_and_laplacian_nonneg isOpen_interior hw hu hCR hρ hα hρJ htame
      hRw).1)
    (fun _ hw hRw ↦ (contDiffAt_and_laplacian_nonneg isOpen_interior hw hu hCR hρ hα hρJ htame
      hRw).2)
    (fun w hw ↦ hbdry w hw) hz

/-- **No escape for strips in a manifold.** Let `J_w` be a family of almost complex structures
depending on the point `w` of the strip. Suppose that on the region `{ρ > R}` the function `ρ` is
`C²`, and for every `w`, `dρ ∘ J_w = -α` for a one-form `α` differentiable there, and `dα` tames
`J_w`. Let `ρ ∘ u` be continuous on the closed strip `ℝ × [0, 1]`, and let `u` be `C²` and solve
`∂ₜu = J_w(u) ∂ₛu` at the points `w` of the open strip `ℝ × (0, 1)` which it maps into
`{ρ > R}`. If `u` maps both boundary lines `ℑ z = 0` and `ℑ z = 1` into `{ρ ≤ R}`, and also the
two ends `|ℜ z| ≥ T` of the strip for some `T`, then `u` maps the whole strip into `{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_strip_boundary_of_comp_le_ends {R T : ℝ}
    (hf : ContinuousOn (ρ ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < ρ (u z) → ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 → R < ρ (u z) →
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J z (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hρ : ∀ x, R < ρ x → ContMDiffAt I 𝓘(ℝ) 2 ρ x)
    (hα : ∀ x, R < ρ x → MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) x)
    (hρJ : ∀ w x, R < ρ x → ∀ v, mvfderiv I ρ x (J w x v) = -α x ![v])
    (htame : ∀ w x, R < ρ x → ∀ v, 0 ≤ mextDeriv α x ![v, J w x v])
    (h₀ : ∀ z : ℂ, z.im = 0 → ρ (u z) ≤ R) (h₁ : ∀ z : ℂ, z.im = 1 → ρ (u z) ≤ R)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → ρ (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : ρ (u z) ≤ R := by
  have hU : IsOpen {w : ℂ | 0 < w.im ∧ w.im < 1} :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hint (w : ℂ) (h₀ : 0 < w.im) (h₁ : w.im < 1) (hRw : R < ρ (u w)) :=
    contDiffAt_and_laplacian_nonneg hU (z := w) ⟨h₀, h₁⟩ (fun y hy ↦ hu y hy.1 hy.2)
      (fun y hy ↦ hCR y hy.1 hy.2) hρ hα hρJ htame hRw
  exact le_of_laplacian_nonneg_of_lt_le_strip hf (fun w h₀ h₁ hRw ↦ (hint w h₀ h₁ hRw).1)
    (fun w h₀ h₁ hRw ↦ (hint w h₀ h₁ hRw).2) h₀ h₁ hends hz₀ hz₁

end TauCeti.Pseudoholomorphic
