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

/-!
# The maximum principle for `J`-holomorphic curves in an almost complex manifold

Let `M` be a manifold without boundary carrying a smooth almost complex structure `J`, a `C¹`
one-form `α` and a function `ρ : M → ℝ` with

`dρ ∘ J = -α`.

On the cylindrical end of a Liouville completion, `ρ` is the radial coordinate and `α` the Liouville
primitive, and this is the condition that `J` is of contact type. A map `u : ℂ → M`, with
`s + i t` the coordinate on `ℂ`, is `J`-holomorphic when it solves the Cauchy--Riemann equation
`∂ₜu = J(u) ∂ₛu`, written here with the manifold derivative of `u`. For such a curve

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
`TauCeti/Geometry/Symplectic/JHolomorphic/MaximumPrinciple.lean`. The almost complex structure does
not depend on the point of the domain, and the equation carries no Hamiltonian term.

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

open InnerProductSpace Laplacian Filter Topology Complex Set
open scoped _root_.Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {J : SmoothAlmostComplexStructure I M} {α : RoughForm I M ℝ 1}
  {ρ : M → ℝ} {u : ℂ → M} {z : ℂ}

omit [I.Boundaryless] in
/-- The derivative of `u : ℂ → M` read in the extended chart at `x` is the derivative of the chart
composed with that of `u`. -/
private theorem fderiv_extChartAt_comp_apply {x : M} {w : ℂ}
    (hws : u w ∈ (extChartAt I x).source) (hwd : MDifferentiableAt 𝓘(ℝ, ℂ) I u w) (v : ℂ) :
    fderiv ℝ (extChartAt I x ∘ u) w v =
      mfderiv I 𝓘(ℝ, E) (extChartAt I x) (u w) (mfderiv 𝓘(ℝ, ℂ) I u w v) := by
  have hws' : u w ∈ (chartAt H x).source := by rwa [← extChartAt_source I]
  have h := congr($(mfderiv_comp w (mdifferentiableAt_extChartAt hws') hwd) v)
  rw [mfderiv_eq_fderiv] at h
  -- `mfderiv_eq_fderiv` only inserts the identifications of tangent spaces of `ℂ` and `E`.
  exact h

omit [I.Boundaryless] in
/-- Read in the extended chart at `x`, a solution of the Cauchy--Riemann equation
`∂ₜu = J(u) ∂ₛu` at `w` solves the Cauchy--Riemann equation for `J.inChart x`. -/
private theorem fderiv_extChartAt_comp_apply_I {x : M} {w : ℂ}
    (hws : u w ∈ (extChartAt I x).source) (hwd : MDifferentiableAt 𝓘(ℝ, ℂ) I u w)
    (hw : mfderiv 𝓘(ℝ, ℂ) I u w (Complex.I : ℂ) = J (u w) (mfderiv 𝓘(ℝ, ℂ) I u w (1 : ℂ))) :
    fderiv ℝ (extChartAt I x ∘ u) w Complex.I =
      J.inChart x ((extChartAt I x ∘ u) w) (fderiv ℝ (extChartAt I x ∘ u) w 1) := by
  have hinv := congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hws)
    (mfderiv 𝓘(ℝ, ℂ) I u w (1 : ℂ)))
  rw [fderiv_extChartAt_comp_apply hws hwd, fderiv_extChartAt_comp_apply hws hwd,
    Function.comp_apply, hw]
  exact (congrArg _ (congrArg _ hinv)).symm.trans
    (J.inChart_extChartAt_apply_eq_mfderiv x hws _).symm

omit [I.Boundaryless] in
/-- Read in the extended chart at `x`, the identity `dρ ∘ J = -α` at the point with coordinate
`e` becomes `d(ρ ∘ φ⁻¹) ∘ J_φ = -α_φ` at `e`, for the coordinate expressions `J_φ = J.inChart x`
and `α_φ = α.inChartAt x` of `J` and `α`. -/
private theorem fderiv_comp_extChartAt_symm_inChart_apply {x : M} {e : E}
    (he : e ∈ (extChartAt I x).target)
    (hed : DifferentiableAt ℝ (ρ ∘ (extChartAt I x).symm) e)
    (hJ : ∀ v, mvfderiv I ρ ((extChartAt I x).symm e) (J ((extChartAt I x).symm e) v) =
      -α ((extChartAt I x).symm e) ![v]) (v : E) :
    fderiv ℝ (ρ ∘ (extChartAt I x).symm) e (J.inChart x e v) =
      -α.inChartAt x e (fun _ ↦ v) := by
  set y := (extChartAt I x).symm e
  have hy : y ∈ (chartAt H x).source := by
    rw [← extChartAt_source I]
    exact (extChartAt I x).map_target he
  -- Near `y`, `ρ` is `ρ ∘ φ⁻¹` read through the chart `φ`, so `dρ_y = d(ρ ∘ φ⁻¹)_e ∘ dφ_y`.
  have hρeq : mfderiv I 𝓘(ℝ) ρ y =
      mfderiv I 𝓘(ℝ) ((ρ ∘ (extChartAt I x).symm) ∘ extChartAt I x) y := by
    refine Filter.EventuallyEq.mfderiv_eq ?_
    filter_upwards [extChartAt_source_mem_nhds' (I := I) ((extChartAt_source I x).symm ▸ hy)]
      with y' hy'
    simp only [Function.comp_apply, (extChartAt I x).left_inv hy']
  have hed' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (ρ ∘ (extChartAt I x).symm)
      (extChartAt I x y) := by
    rw [(extChartAt I x).right_inv he]
    exact hed.mdifferentiableAt
  set a := mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) e v
  have h := congr($(mfderiv_comp y hed' (mdifferentiableAt_extChartAt hy)) (J y a))
  rw [← hρeq, mfderiv_eq_fderiv, (extChartAt I x).right_inv he] at h
  have ha : (fun _ : Fin 1 ↦ a) = ![a] := by
    funext i
    fin_cases i
    rfl
  rw [J.inChart_apply_eq_mfderiv x he, RoughForm.inChartAt_apply, ha, ← hJ a]
  -- `h` is the chain rule, up to the identifications of tangent spaces of `E` and `ℝ`.
  exact h.symm

/-- **The Laplacian of `ρ` along a `J`-holomorphic curve in a manifold.** Let `u : ℂ → M` be
`C²` at `z` and solve the Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` near `z`. Let `α` be a `C¹`
one-form and `ρ` a function `C²` at `u z` with `dρ ∘ J = -α` near `u z`. Then

`Δ(ρ ∘ u)(z) = dα(∂ₛu, ∂ₜu)`. -/
theorem laplacian_comp_eq_of_mvfderiv_comp_eq_neg
    (hu : ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ᶠ w in 𝓝 z,
      mfderiv 𝓘(ℝ, ℂ) I u w (Complex.I : ℂ) = J (u w) (mfderiv 𝓘(ℝ, ℂ) I u w (1 : ℂ)))
    (hρ : ContMDiffAt I 𝓘(ℝ) 2 ρ (u z)) (hα : IsSmoothForm I 1 α)
    (hρJ : ∀ᶠ y in 𝓝 (u z), ∀ v, mvfderiv I ρ y (J y v) = -α y ![v]) :
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
  have hω : DifferentiableAt ℝ (α.inChartAt (u z)) ((extChartAt I (u z) ∘ u) z) := by
    have h := hα.contDiffWithinAt_inChartAt_self (u z)
    rw [hrange, contDiffWithinAt_univ] at h
    exact h.differentiableAt one_ne_zero
  -- The three identities of the computation in local coordinates.
  have hJsq : ∀ᶠ e in 𝓝 ((extChartAt I (u z) ∘ u) z),
      ∀ v, J.inChart (u z) e (J.inChart (u z) e v) = -v := by
    filter_upwards [htgt] with e he v
    exact J.inChart_inChart (u z) he v
  have hCRc : ∀ᶠ w in 𝓝 z, fderiv ℝ (extChartAt I (u z) ∘ u) w Complex.I =
      J.inChart (u z) ((extChartAt I (u z) ∘ u) w) (fderiv ℝ (extChartAt I (u z) ∘ u) w 1) := by
    filter_upwards [hCR, hsrc, ContMDiffAt.eventually_mdifferentiableAt hu one_le_two]
      with w hw hws hwd
    exact fderiv_extChartAt_comp_apply_I hws hwd hw
  have hρJc : ∀ᶠ e in 𝓝 ((extChartAt I (u z) ∘ u) z),
      (fderiv ℝ (ρ ∘ (extChartAt I (u z)).symm) e).comp (J.inChart (u z) e) =
        -L (α.inChartAt (u z) e) := by
    have hsymm := continuousAt_extChartAt_symm (I := I) (u z)
    rw [ContinuousAt, extChartAt_to_inv] at hsymm
    filter_upwards [htgt, (hρc.eventually (by simp)).mono fun e he ↦
      he.differentiableAt (by norm_num), hsymm.eventually hρJ] with e he hed hJ
    ext v
    rw [ContinuousLinearMap.comp_apply, neg_apply, hL]
    exact fderiv_comp_extChartAt_symm_inChart_apply he hed hJ v
  -- The computation in the chart, transported back.
  have hloc := JHolomorphic.laplacian_comp_eq_of_fderiv_comp_eq_neg huc hCRc hρc
    (L.differentiableAt.comp _ hω) hJsq hρJc
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
    rw [fderiv_extChartAt_comp_apply (mem_extChartAt_source (u z))
      (hu.mdifferentiableAt (by norm_num)), mfderiv_extChartAt_self]
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
exterior derivative `dα` tames `J` at `u z`, that is `dα(v, J v) ≥ 0` for every `v`, then
`Δ(ρ ∘ u)(z) ≥ 0`. -/
theorem laplacian_comp_nonneg_of_mvfderiv_comp_eq_neg (hu : ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ᶠ w in 𝓝 z,
      mfderiv 𝓘(ℝ, ℂ) I u w (Complex.I : ℂ) = J (u w) (mfderiv 𝓘(ℝ, ℂ) I u w (1 : ℂ)))
    (hρ : ContMDiffAt I 𝓘(ℝ) 2 ρ (u z)) (hα : IsSmoothForm I 1 α)
    (hρJ : ∀ᶠ y in 𝓝 (u z), ∀ v, mvfderiv I ρ y (J y v) = -α y ![v])
    (htame : ∀ v, 0 ≤ mextDeriv α (u z) ![v, J (u z) v]) :
    0 ≤ Δ (ρ ∘ u) z := by
  rw [laplacian_comp_eq_of_mvfderiv_comp_eq_neg hu hCR hρ hα hρJ, hCR.self_of_nhds]
  exact htame _

/-- `ρ ∘ u` is `C²` and subharmonic at a point of an open set on which `u` is `C²` and
`J`-holomorphic, provided `ρ ∘ u` exceeds `R` there and the hypotheses of the maximum principle
hold on `{ρ > R}`. -/
private theorem contDiffAt_and_laplacian_nonneg {R : ℝ} {U : Set ℂ} (hU : IsOpen U) (hz : z ∈ U)
    (hu : ∀ z ∈ U, ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z ∈ U,
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hρ : ∀ x, R < ρ x → ContMDiffAt I 𝓘(ℝ) 2 ρ x) (hα : IsSmoothForm I 1 α)
    (hρJ : ∀ x, R < ρ x → ∀ v, mvfderiv I ρ x (J x v) = -α x ![v])
    (htame : ∀ x, R < ρ x → ∀ v, 0 ≤ mextDeriv α x ![v, J x v]) (hRz : R < ρ (u z)) :
    ContDiffAt ℝ 2 (ρ ∘ u) z ∧ 0 ≤ Δ (ρ ∘ u) z := by
  refine ⟨contMDiffAt_iff_contDiffAt.1 ((hρ _ hRz).comp z (hu z hz)), ?_⟩
  have hnhds : ∀ᶠ x in 𝓝 (u z), R < ρ x := (hρ _ hRz).continuousAt.eventually (lt_mem_nhds hRz)
  exact laplacian_comp_nonneg_of_mvfderiv_comp_eq_neg (hu z hz)
    (eventually_of_mem (hU.mem_nhds hz) hCR) (hρ _ hRz) hα (hnhds.mono hρJ) (htame _ hRz)

/-- **The maximum principle for `J`-holomorphic curves in a manifold.** Suppose that on the region
`{ρ > R}` the function `ρ` is `C²`, `dρ ∘ J = -α` for a `C¹` one-form `α`, and `dα` tames `J`. Let
`K ⊆ ℂ` be compact and `u` be `C²` and `J`-holomorphic on the interior of `K`, with `ρ ∘ u`
continuous on `K`. If `u` maps the frontier of `K` into `{ρ ≤ R}`, then it maps all of `K` into
`{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_frontier {R : ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hf : ContinuousOn (ρ ∘ u) K) (hu : ∀ z ∈ interior K, ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z ∈ interior K,
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hρ : ∀ x, R < ρ x → ContMDiffAt I 𝓘(ℝ) 2 ρ x) (hα : IsSmoothForm I 1 α)
    (hρJ : ∀ x, R < ρ x → ∀ v, mvfderiv I ρ x (J x v) = -α x ![v])
    (htame : ∀ x, R < ρ x → ∀ v, 0 ≤ mextDeriv α x ![v, J x v])
    (hbdry : ∀ z ∈ frontier K, ρ (u z) ≤ R) (hz : z ∈ K) : ρ (u z) ≤ R :=
  le_of_laplacian_nonneg_of_lt_le_frontier hK hf
    (fun _ hw hRw ↦ (contDiffAt_and_laplacian_nonneg isOpen_interior hw hu hCR hρ hα hρJ htame
      hRw).1)
    (fun _ hw hRw ↦ (contDiffAt_and_laplacian_nonneg isOpen_interior hw hu hCR hρ hα hρJ htame
      hRw).2)
    (fun w hw ↦ hbdry w hw) hz

/-- **No escape for strips in a manifold.** Suppose that on the region `{ρ > R}` the function `ρ`
is `C²`, `dρ ∘ J = -α` for a `C¹` one-form `α`, and `dα` tames `J`. Let `u` be `C²` and
`J`-holomorphic on the open strip `ℝ × (0, 1)`, with `ρ ∘ u` continuous on the closed strip
`ℝ × [0, 1]`. If `u` maps both boundary lines `ℑ z = 0` and `ℑ z = 1` into `{ρ ≤ R}`, and also the
two ends `|ℜ z| ≥ T` of the strip for some `T`, then `u` maps the whole strip into `{ρ ≤ R}`. -/
theorem comp_le_of_comp_le_strip_boundary_of_comp_le_ends {R T : ℝ}
    (hf : ContinuousOn (ρ ∘ u) (univ ×ℂ Icc 0 1))
    (hu : ∀ z : ℂ, 0 < z.im → z.im < 1 → ContMDiffAt 𝓘(ℝ, ℂ) I 2 u z)
    (hCR : ∀ z : ℂ, 0 < z.im → z.im < 1 →
      mfderiv 𝓘(ℝ, ℂ) I u z (Complex.I : ℂ) = J (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ)))
    (hρ : ∀ x, R < ρ x → ContMDiffAt I 𝓘(ℝ) 2 ρ x) (hα : IsSmoothForm I 1 α)
    (hρJ : ∀ x, R < ρ x → ∀ v, mvfderiv I ρ x (J x v) = -α x ![v])
    (htame : ∀ x, R < ρ x → ∀ v, 0 ≤ mextDeriv α x ![v, J x v])
    (h₀ : ∀ z : ℂ, z.im = 0 → ρ (u z) ≤ R) (h₁ : ∀ z : ℂ, z.im = 1 → ρ (u z) ≤ R)
    (hends : ∀ z : ℂ, T ≤ |z.re| → 0 ≤ z.im → z.im ≤ 1 → ρ (u z) ≤ R)
    (hz₀ : 0 ≤ z.im) (hz₁ : z.im ≤ 1) : ρ (u z) ≤ R := by
  have hU : IsOpen {w : ℂ | 0 < w.im ∧ w.im < 1} :=
    (isOpen_lt continuous_const continuous_im).inter (isOpen_lt continuous_im continuous_const)
  have hu' : ∀ w ∈ {w : ℂ | 0 < w.im ∧ w.im < 1}, ContMDiffAt 𝓘(ℝ, ℂ) I 2 u w :=
    fun w hw ↦ hu w hw.1 hw.2
  have hCR' : ∀ w ∈ {w : ℂ | 0 < w.im ∧ w.im < 1}, mfderiv 𝓘(ℝ, ℂ) I u w (Complex.I : ℂ) =
      J (u w) (mfderiv 𝓘(ℝ, ℂ) I u w (1 : ℂ)) := fun w hw ↦ hCR w hw.1 hw.2
  exact le_of_laplacian_nonneg_of_lt_le_strip hf
    (fun w hw₀ hw₁ hRw ↦ (contDiffAt_and_laplacian_nonneg hU ⟨hw₀, hw₁⟩ hu' hCR' hρ hα hρJ htame
      hRw).1)
    (fun w hw₀ hw₁ hRw ↦ (contDiffAt_and_laplacian_nonneg hU ⟨hw₀, hw₁⟩ hu' hCR' hρ hα hρJ htame
      hRw).2) h₀ h₁ hends hz₀ hz₁

end TauCeti.Pseudoholomorphic
