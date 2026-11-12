/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Standard
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Contact.Darboux.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Contact Darboux charts on manifolds

Let `M` be a smooth manifold with finite-dimensional real model space `E`. **The contact Darboux
theorem** states that a contact structure is locally standard: around every point of `M` there is
a chart onto an open subset of `ℝⁿ × ℝⁿ × ℝ` carrying the contact structure to the kernel of the
standard contact form `α_std = dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`).

For forms, let `α` be a one-form, smooth on an open set `U`, which is a contact form at an interior
point `x₀ ∈ U` (`TauCeti.IsContactFormAt`). Then
`TauCeti.IsContactFormAt.exists_darbouxChart_of_isInteriorPoint` gives a smooth partial
diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ`, with `x₀ ∈ chart.source ⊆ U` and `chart x₀ = 0`,
and a function `g`, positive on `chart.source`, such that for every `x ∈ chart.source` and
`v : T_x M`,

`α_std (chart x) (d chart_x v) = g x * α x v`.

So `chart` pulls `α_std` back to the positive multiple `g α` of `α`. In particular it carries
`ker α` onto `ker α_std` and preserves the coorientations defined by `α` and `α_std`. Applied to the
contact form `-α`, the same theorem gives a chart reversing the coorientation. Only the contact
condition at `x₀` and the smoothness of `α` near `x₀` are assumed. The global versions for smooth
contact forms are `TauCeti.SmoothForm.IsContactForm.exists_darbouxChart_of_isInteriorPoint` and,
on boundaryless manifolds, `TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`.

A contact structure need not be the kernel of any global one-form, and need not be cooriented. For a
smooth contact distribution `ξ` (`TauCeti.IsContactDistribution`), the local defining forms of `ξ`
(`TauCeti.IsContactDistribution.exists_isContactFormAt`) give contact charts
(`TauCeti.IsContactDistribution.exists_darbouxChart_of_isInteriorPoint` and
`TauCeti.IsContactDistribution.exists_darbouxChart`): around every interior point there is a
smooth partial diffeomorphism to `ℝⁿ × ℝⁿ × ℝ` whose differential carries `ξ_x` onto the standard
contact hyperplane `ker α_std` at `chart x`, for every `x` in its source.

The proof reads `α` in the preferred extended chart at `x₀`. There it is a smooth one-form on the
interior of the chart target which is a contact form at the chart image of `x₀`
(`TauCeti.isContactFormAt_inChartAt_iff`), so the contact Darboux theorem on normed spaces
(`TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`) gives a
diffeomorphism `Φ` onto `ℝⁿ × ℝⁿ × ℝ` pulling `α_std` back to a positive multiple of the coordinate
expression of `α` near that point. The chart is `Φ` composed with the extended chart, restricted
to the inverse image of a neighbourhood on which this identity holds.

## Main results

* `TauCeti.IsContactFormAt.exists_darbouxChart_of_isInteriorPoint`: Darboux charts for a locally
  defined one-form which is a contact form at an interior point.
* `TauCeti.SmoothForm.IsContactForm.exists_darbouxChart_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`: Darboux charts for smooth contact forms.
* `TauCeti.IsContactDistribution.exists_darbouxChart_of_isInteriorPoint`,
  `TauCeti.IsContactDistribution.exists_darbouxChart`: contact charts for smooth contact
  distributions, with no contact form or coorientation chosen.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Theorem 3.5.14.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The contact Darboux theorem** for a locally defined one-form. Let `α` be a one-form on `M`
which is smooth on an open set `U` and is a contact form at an interior point `x₀ ∈ U`. Then there
are `n`, a smooth partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with
`x₀ ∈ chart.source ⊆ U` and `chart x₀ = 0`, and a function `g`, positive on `chart.source`, such
that `chart` pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `g α` on `chart.source`. -/
theorem IsContactFormAt.exists_darbouxChart_of_isInteriorPoint {α : RoughForm I M ℝ 1}
    {U : Set M} {x₀ : M} (hc : IsContactFormAt α x₀) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = g x * α x ![v] := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  set e := extChartAt I x₀ with he
  -- The chart coordinates of the interior points of the chart target lying over `U`.
  set W : Set E := interior e.target ∩ e.symm ⁻¹' U
  have hW : IsOpen W :=
    ((continuousOn_extChartAt_symm x₀).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hU
  have hy₀W : e x₀ ∈ W :=
    ⟨I.isInteriorPoint_iff.1 hx₀, by rw [mem_preimage, extChartAt_to_inv]; exact hx₀U⟩
  -- On `W`, the coordinate expression of `α` is smooth.
  have hη : ContDiffOn ℝ ∞ (α.inChartAt x₀) W := by
    intro z hz
    have hzt : z ∈ e.target := interior_subset hz.1
    have hloc := α.contDiffWithinAt_range_inChartAt_of_contMDiffAt
      ((hα _ hz.2).contMDiffAt (hU.mem_nhds hz.2))
    have hrange : range I ∈ 𝓝 z :=
      mem_of_superset (isOpen_interior.mem_nhds hz.1)
        (interior_subset.trans (extChartAt_target_subset_range x₀))
    exact ((α.contDiffWithinAt_inChartAt_of_contDiffWithinAt_inChartAt hzt
      (mem_extChartAt_source _) hloc).contDiffAt hrange).contDiffWithinAt
  -- The contact Darboux theorem on the model space, around the chart image of `x₀`.
  obtain ⟨n, Φ, g, hΦ₀, hev⟩ :=
    exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul (r := ⊤) le_top hW
      hy₀W (hη.of_le (by simp)) ((isContactFormAt_inChartAt_iff hx₀).2 hc)
  obtain ⟨V₁, hV₁, hV₁o, hy₀V₁⟩ := eventually_nhds_iff.1 hev
  -- The chart: `Φ` after the extended chart, restricted to the inverse image of `V₁ ∩ W`.
  set S : Set M := e.source ∩ e ⁻¹' (V₁ ∩ W)
  have hS : IsOpen S := isOpen_extChartAt_preimage' x₀ (hV₁o.inter hW)
  have hS_sub : S ⊆ (extChartPartialDiffeomorph I ∞ x₀).source := by
    rw [extChartPartialDiffeomorph_source]
    exact inter_subset_inter_right _ (preimage_mono fun _ hy ↦ hy.2.1)
  set chart := ((extChartPartialDiffeomorph I ∞ x₀).restrOpen S hS).trans Φ.toPartialDiffeomorph
  have hsrc : chart.source = S := by
    simp [chart, inter_eq_right.2 hS_sub]
  have hcoe : ⇑chart = ⇑Φ ∘ ⇑e := by
    funext y
    simp [chart, e]
  have hmvf (x : M) (hx : x ∈ S) (v : TangentSpace I x) :
      mvfderiv I chart x v = fderiv ℝ Φ (e x) (mvfderiv I e x v) := by
    have hx_chart : x ∈ (chartAt H x₀).source := by
      simpa only [he, extChartAt_source] using hx.1
    rw [hcoe, mvfderiv_comp_apply_of_differentiableAt (Φ.differentiable (by simp) _)
      (mdifferentiableAt_extChartAt hx_chart)]
  refine ⟨n, chart, fun x ↦ g (e x), hsrc ▸ ⟨mem_extChartAt_source x₀, hy₀V₁, hy₀W⟩,
    fun x hx ↦ ?_, by rw [hcoe, Function.comp_apply, hΦ₀], fun x hx ↦ ?_⟩
  · rw [hsrc] at hx
    have hU' := hx.2.2.2
    rwa [mem_preimage, e.left_inv hx.1] at hU'
  · rw [hsrc] at hx
    obtain ⟨hg, hΦ⟩ := hV₁ _ hx.2.1
    refine ⟨hg, fun v ↦ ?_⟩
    have hvec : (fun i ↦ mvfderiv I e x (![v] i)) = ![mvfderiv I e x v] := by
      ext i
      fin_cases i
      rfl
    rw [hmvf x hx v, show chart x = Φ (e x) from congrFun hcoe x, hΦ,
      RoughForm.apply_eq_inChartAt_mvfderiv α hx.1, hvec]

/-- **The contact Darboux theorem at an interior point.** Around any interior point `x₀` of a
manifold with a smooth contact form `α`, there are `n`, a smooth partial diffeomorphism `chart`
from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and `chart x₀ = 0`, and a function `g`, positive
on `chart.source`, such that `chart` pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `g α`
on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_darbouxChart_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = g x * α.1 x ![v] := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨n, chart, g, hx₀', -, h0, hchart⟩ :=
    (isContactForm_iff_forall_isContactFormAt.1 hα x₀).exists_darbouxChart_of_isInteriorPoint
      isOpen_univ (mem_univ x₀) α.contMDiff.contMDiffOn hx₀
  exact ⟨n, chart, g, hx₀', h0, hchart⟩

/-- **The contact Darboux theorem for contact structures at an interior point.** Around any
interior point `x₀` of a manifold with a smooth contact distribution `D`, there are `n` and a
smooth partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and
`chart x₀ = 0` whose differential at each `x ∈ chart.source` carries `D x` onto the kernel of the
standard contact form `dz - Σᵢ pᵢ dqᵢ` at `chart x`: `D x` is the inverse image of that kernel. No
contact form or coorientation of `D` is chosen. -/
theorem IsContactDistribution.exists_darbouxChart_of_isInteriorPoint
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} (hD : IsContactDistribution I ∞ D) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, D x =
        ((innerProductContactForm (EuclideanSpace ℝ (Fin n))).kerDistribution (chart x)).comap
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) chart
            x).toLinearMap := by
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨U, hU, hx₀U, α, hα, hαD⟩ := hD.exists_isContactFormAt (by simp) x₀
  obtain ⟨n, chart, g, hx₀', hsU, h0, hchart⟩ :=
    (hαD x₀ hx₀U).2.exists_darbouxChart_of_isInteriorPoint hU hx₀U hα hx₀
  refine ⟨n, chart, hx₀', h0, fun x hx ↦ ?_⟩
  ext v
  rw [← (hαD x (hsU hx)).1, Submodule.mem_comap, SmoothForm.mem_kerDistribution,
    ContinuousLinearMap.coe_coe, ← mvfderiv_apply_eq_mfderiv_apply, RoughForm.mem_ker,
    (hchart x hx).2 v, mul_eq_zero, or_iff_right (hchart x hx).1.ne']

section Boundaryless

variable [BoundarylessManifold I M]

/-- **The contact Darboux theorem.** Around every point `x₀` of a boundaryless manifold with a
smooth contact form `α`, there are `n`, a smooth partial diffeomorphism `chart` from `M` to
`ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and `chart x₀ = 0`, and a function `g`, positive on
`chart.source`, such that `chart` pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `g α`
on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_darbouxChart {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = g x * α.1 x ![v] :=
  hα.exists_darbouxChart_of_isInteriorPoint BoundarylessManifold.isInteriorPoint

/-- **The contact Darboux theorem for contact structures.** Around every point `x₀` of a
boundaryless manifold with a smooth contact distribution `D`, there are `n` and a smooth partial
diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and `chart x₀ = 0` whose
differential at each `x ∈ chart.source` carries `D x` onto the kernel of the standard contact form
`dz - Σᵢ pᵢ dqᵢ` at `chart x`. -/
theorem IsContactDistribution.exists_darbouxChart
    {D : Π x : M, Submodule ℝ (TangentSpace I x)} (hD : IsContactDistribution I ∞ D) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, D x =
        ((innerProductContactForm (EuclideanSpace ℝ (Fin n))).kerDistribution (chart x)).comap
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) chart
            x).toLinearMap :=
  hD.exists_darbouxChart_of_isInteriorPoint BoundarylessManifold.isInteriorPoint

end Boundaryless

end TauCeti
