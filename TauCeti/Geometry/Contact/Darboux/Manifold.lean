/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Darboux
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Darboux charts on contact manifolds

Let `α` be a smooth one-form on a smooth manifold `M` modelled on a finite-dimensional real normed
space `E`, and let `α` be a contact form at an interior point `x₀` (`TauCeti.IsContactFormAt`):
`α(x₀) ≠ 0` and `dα(x₀)` is nondegenerate on `ker α(x₀)`. **Darboux's theorem for contact
structures** gives a chart near `x₀` in which `ker α` is the standard contact structure: there are
`n` with `dim E = 2n + 1`, a smooth partial diffeomorphism

`chart : M → ℝⁿ × ℝⁿ × ℝ`, `chart x₀ = 0`,

and a positive function `g` on its source such that `chart` pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to `g α`
(`TauCeti.IsContactFormAt.exists_darbouxChart_of_isInteriorPoint`).
So `chart` carries the contact hyperplanes `ker α` to the standard ones and the coorientation given
by `α` to the coorientation given by `dz - Σᵢ pᵢ dqᵢ`. Applied to `-α`, the same theorem gives a
chart reversing the coorientation. On a boundaryless manifold every point is interior, so every
point of a contact manifold has such a chart
(`TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`).

The chart is the composition of the preferred extended chart at `x₀` with the Darboux
diffeomorphism of the model space
(`TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`), applied to
the coordinate expression of `α`. That expression is a contact form at the chart image of `x₀`
exactly when `α` is a contact form at `x₀` (`TauCeti.isContactFormAt_inChartAt_iff`), since the
chart expression of a form at the centre of its own chart is the form itself and the exterior
derivative commutes with reading forms in charts.

## Main results

* `TauCeti.isContactFormAt_inChartAt_iff`: a smooth one-form is a contact form at an interior
  point exactly when its coordinate expression in the preferred chart at that point is.
* `TauCeti.IsContactFormAt.exists_darbouxChart_of_isInteriorPoint`: a Darboux chart at an
  interior point at which a smooth one-form is contact.
* `TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`: a Darboux chart at every point of a
  boundaryless contact manifold.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1 (Darboux's theorem).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5.
-/

public section

noncomputable section

open Set Filter Topology Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A smooth one-form is a contact form at an interior point `x₀` exactly when its coordinate
expression in the preferred chart at `x₀` is a contact form at the chart image of `x₀`. -/
theorem isContactFormAt_inChartAt_iff [IsManifold I 2 M] {α : RoughForm I M ℝ 1}
    (hα : IsSmoothForm I 1 α) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    IsContactFormAt (I := 𝓘(ℝ, E)) (α.inChartAt x₀) (extChartAt I x₀ x₀) ↔
      IsContactFormAt α x₀ := by
  have : IsManifold I 1 M := IsManifold.of_le (n := 2) (by norm_num)
  set y₀ : E := extChartAt I x₀ x₀
  set η : RoughForm 𝓘(ℝ, E) E ℝ 1 := α.inChartAt x₀
  have hval : η y₀ = α x₀ := RoughForm.inChartAt_extChartAt_self α x₀
  have hker (v : E) : η y₀ ![v] = 0 ↔ α x₀ ![v] = 0 := by
    rw [hval]
    -- Both sides evaluate `α x₀` on `![v]`, read in `E` and in its synonym `TangentSpace I x₀`.
    exact Iff.rfl
  -- The flat exterior derivative of the coordinate expression at the centre is `dα(x₀)`.
  have hd (v w : E) : mextDeriv η y₀ ![v, w] = mextDeriv α x₀ ![v, w] := by
    rw [mextDeriv_eq_extDeriv, ← hα.inChartAt_mextDeriv_eq_extDeriv x₀
      ((ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx₀),
      RoughForm.inChartAt_extChartAt_self]
    -- The tangent vectors `![v, w]` are read in `E` and in its synonym `TangentSpace I x₀`.
    rfl
  constructor
  · rintro ⟨hne, hnd⟩
    refine ⟨hval ▸ hne, fun v hv hvw ↦ hnd v (RoughForm.mem_ker.2 ((hker v).2
      (RoughForm.mem_ker.1 hv))) fun w hw ↦ ?_⟩
    exact (hd v w).trans (hvw w (RoughForm.mem_ker.2 ((hker w).1 (RoughForm.mem_ker.1 hw))))
  · rintro ⟨hne, hnd⟩
    refine ⟨hval ▸ hne, fun v hv hvw ↦ hnd v (RoughForm.mem_ker.2 ((hker v).1
      (RoughForm.mem_ker.1 hv))) fun w hw ↦ ?_⟩
    exact (hd v w).symm.trans (hvw w (RoughForm.mem_ker.2 ((hker w).2 (RoughForm.mem_ker.1 hw))))

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]

/-- **The contact Darboux theorem at an interior point.** Let `α` be a smooth one-form which is a
contact form at an interior point `x₀`. Then there are `n` with `dim E = 2n + 1`, a smooth partial
diffeomorphism `chart` from `M` onto an open subset of `ℝⁿ × ℝⁿ × ℝ` with `x₀` in its source and
`chart x₀ = 0`, and a function `g`, positive on the source of `chart`, such that `chart` pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `g α` on its source. So `chart` carries `ker α` to
the standard contact structure, preserving coorientations. -/
theorem IsContactFormAt.exists_darbouxChart_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} {x₀ : M} (hα : IsContactFormAt α.1 x₀)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
        ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
          (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
            ![mvfderiv I chart x v] = g x * α.1 x ![v] := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  set y₀ : E := extChartAt I x₀ x₀
  set W : Set E := interior (extChartAt I x₀).target
  have hy₀W : y₀ ∈ W := (ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx₀
  -- The coordinate expression of `α` is a smooth contact form at `y₀`; apply the flat theorem.
  have hc : IsContactFormAt (I := 𝓘(ℝ, E)) (RoughForm.inChartAt α.1 x₀) y₀ :=
    (isContactFormAt_inChartAt_iff (α.isSmoothForm.of_le (by simp)) hx₀).2 hα
  have hsm : ContDiffOn ℝ (((⊤ : ℕ∞) : WithTop ℕ∞) + 1) (RoughForm.inChartAt α.1 x₀) W :=
    (α.isSmoothForm.contDiffOn_inChartAt_interior_target x₀).of_le (by simp)
  obtain ⟨n, Φ, g, hΦ₀, hev⟩ :=
    exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul (r := ⊤) le_top
      isOpen_interior hy₀W hsm hc
  set P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ
  -- The open set of model points where the flat Darboux identity holds.
  obtain ⟨t, ht, htΦ⟩ := hev.exists_mem
  set V₀ : Set E := interior t ∩ W
  have hV₀ : IsOpen V₀ := isOpen_interior.inter isOpen_interior
  have hy₀V₀ : y₀ ∈ V₀ := ⟨mem_interior_iff_mem_nhds.2 ht, hy₀W⟩
  obtain ⟨chart₀, hsrc₀, hcoe₀, hmvf₀⟩ :=
    exists_partialDiffeomorph_comp_extChartAt I ∞ x₀ hV₀ inter_subset_right (by simp)
      (Diffeomorph.refl 𝓘(ℝ, E) E ∞)
  let chart : PartialDiffeomorph I 𝓘(ℝ, P) M P ∞ := chart₀.trans Φ.toPartialDiffeomorph
  have hsrc : chart.source = chart₀.source := by simp [chart]
  have hcoe (y : M) : chart y = Φ (extChartAt I x₀ y) := by simp [chart, hcoe₀]
  -- The differential of `chart` is that of `Φ` after the differential of the extended chart.
  have hmvf (x : M) (hx : x ∈ chart.source) (v : TangentSpace I x) :
      mvfderiv I chart x v =
        fderiv ℝ Φ (extChartAt I x₀ x) (mvfderiv I (extChartAt I x₀) x v) := by
    have hx₀' : x ∈ chart₀.source := hsrc ▸ hx
    have hmd : MDifferentiableAt I 𝓘(ℝ, E) chart₀ x :=
      (chart₀.contMDiffOn_toFun.contMDiffAt (chart₀.open_source.mem_nhds hx₀')).mdifferentiableAt
        (by simp)
    have hcomp : ⇑chart = ⇑Φ ∘ ⇑chart₀ := by
      funext y
      simp [hcoe, hcoe₀]
    rw [hcomp, mvfderiv_comp_apply_of_differentiableAt
      ((Φ.differentiable (by simp)) _) hmd, hmvf₀ x hx₀' v, hcoe₀]
    -- `simp` reduces the derivative of the identity diffeomorphism to the identity of `E`, which
    -- is then applied to a vector of its synonym `TangentSpace 𝓘(ℝ, E) _`.
    simp
    rfl
  -- The dimension count, from the derivative of `Φ`.
  have hdim : finrank ℝ E = 2 * n + 1 := by
    have e : E ≃ₗ[ℝ] P := (Φ.mfderivToContinuousLinearEquiv (by simp) y₀).toLinearEquiv
    rw [e.finrank_eq, finrank_prod, finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
    ring
  refine ⟨n, chart, fun x ↦ g (extChartAt I x₀ x), hdim, ?_, ?_, fun x hx ↦ ?_⟩
  · rw [hsrc, hsrc₀]
    exact ⟨mem_extChartAt_source x₀, hy₀V₀⟩
  · rw [hcoe, hΦ₀]
  · have hxS : x ∈ (extChartAt I x₀).source ∩ extChartAt I x₀ ⁻¹' V₀ := hsrc₀ ▸ hsrc ▸ hx
    obtain ⟨hg, hΦx⟩ := htΦ _ (interior_subset hxS.2.1)
    refine ⟨hg, fun v ↦ ?_⟩
    have hvec : (fun i ↦ mvfderiv I (extChartAt I x₀) x (![v] i)) =
        ![mvfderiv I (extChartAt I x₀) x v] := by
      funext i
      fin_cases i
      rfl
    rw [hcoe, hmvf x hx, hΦx, RoughForm.apply_eq_inChartAt_mvfderiv α.1 hxS.1, hvec]

section Boundaryless

variable [BoundarylessManifold I M]

namespace SmoothForm

/-- **The contact Darboux theorem.** Every point `x₀` of a finite-dimensional boundaryless smooth
manifold with a contact form `α` lies in the source of a smooth partial diffeomorphism `chart` onto
an open subset of `ℝⁿ × ℝⁿ × ℝ`, where `dim E = 2n + 1`, with `chart x₀ = 0`, which pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `g α` for a function `g` positive on its source. -/
theorem IsContactForm.exists_darbouxChart
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
        ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
          (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
            ![mvfderiv I chart x v] = g x * α.1 x ![v] :=
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  (isContactForm_iff_forall_isContactFormAt.1 hα x₀
    ).exists_darbouxChart_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint

end SmoothForm

end Boundaryless

end TauCeti
