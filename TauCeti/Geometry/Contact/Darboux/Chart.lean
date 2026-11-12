/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Darboux
public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

import TauCeti.Geometry.Manifold.DifferentialForm.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Contact Darboux charts on manifolds

Let `M` be a smooth manifold of dimension `2 n + 1`, and let `α` be a one-form which is smooth on
an open set `U` and a contact form at an interior point `x₀ ∈ U`. The **contact Darboux theorem**
(`TauCeti.IsContactFormAt.exists_darbouxChart_of_finrank_eq_of_isInteriorPoint`) gives a smooth
partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ`, with `x₀ ∈ chart.source ⊆ U` and
`chart x₀ = 0`, and a function `g` positive on `chart.source`, such that the standard contact form
`α_std = dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) pulls back along `chart` to `g α`:

`α_std (chart x) (d chart_x v) = g x * α x v` for `x ∈ chart.source`.

So `chart` carries the contact structure `ker α` to the standard contact structure `ker α_std`, and
the coorientation of `ker α` given by `α` to the coorientation given by `α_std`. The opposite
coorientation is handled by applying the theorem to `-α`, which is again contact
(`TauCeti.isContactFormAt_neg_iff`). On a boundaryless manifold every point is interior
(`TauCeti.IsContactFormAt.exists_darbouxChart`), and a global contact form gives such a chart
around every point (`TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`).

A contact structure need not be the kernel of a global form, nor be coorientable. Since it is
locally the kernel of a contact form (`TauCeti.IsContactDistribution.exists_isContactFormAt`), the
form-level theorem also gives **contact charts** for the hyperplane field itself
(`TauCeti.IsContactDistribution.exists_darbouxChart`): around every point of a smooth contact
manifold `(M, ξ)` there is a smooth chart `chart` to `ℝⁿ × ℝⁿ × ℝ` with
`ξ_x = (d chart_x)⁻¹ (ker α_std)` on its source.

The proof reads `α` in the preferred extended chart at `x₀`, where it is a smooth one-form on an
open subset of the model space which is contact at the image of `x₀`, and applies the flat contact
Darboux theorem `TauCeti.exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul`.
Its diffeomorphism, composed with the extended chart restricted to an open set on which the flat
conclusion holds (`TauCeti.exists_partialDiffeomorph_comp_extChartAt`), is the chart.

## Main results

* `TauCeti.IsContactFormAt.exists_darbouxChart_of_isInteriorPoint`,
  `TauCeti.IsContactFormAt.exists_darbouxChart_of_finrank_eq_of_isInteriorPoint`: contact Darboux
  charts for a local contact form at an interior point, the second one with the dimension `n` of
  the model `ℝⁿ × ℝⁿ × ℝ` prescribed by `dim M = 2 n + 1`.
* `TauCeti.IsContactFormAt.exists_darbouxChart`,
  `TauCeti.IsContactFormAt.exists_darbouxChart_of_finrank_eq`: the same on a boundaryless manifold.
* `TauCeti.SmoothForm.IsContactForm.exists_darbouxChart`: contact Darboux charts for a global
  contact form.
* `TauCeti.IsContactDistribution.exists_darbouxChart`: contact charts for a smooth contact
  structure, possibly not coorientable.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5.
-/

public section

noncomputable section

open Set Filter Bundle Module
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- The contact Darboux chart at an interior point, with the dimension identity
`dim M = 2 n + 1` for the model `ℝⁿ × ℝⁿ × ℝ` it lands in. -/
private theorem IsContactFormAt.exists_darbouxChart_aux {α : RoughForm I M ℝ 1} {x₀ : M}
    (hc : IsContactFormAt α x₀) {U : Set M} (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = g x * α x ![v] := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  set e := extChartAt I x₀ with he
  set η : E → E [⋀^Fin 1]→L[ℝ] ℝ := α.inChartAt x₀
  set y₀ : E := e x₀ with hy₀
  -- The open set of chart coordinates, away from the boundary, over which `α` is smooth.
  set W : Set E := interior e.target ∩ e.symm ⁻¹' U
  have hW : IsOpen W :=
    ((continuousOn_extChartAt_symm x₀).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hU
  have hy₀W : y₀ ∈ W :=
    ⟨(ModelWithCorners.isInteriorPoint_iff (I := I)).mp hx₀, by
      simpa only [mem_preimage, hy₀, he, extChartAt_to_inv] using hx₀U⟩
  have hrange {z : E} (hz : z ∈ interior e.target) : range I ∈ 𝓝 z :=
    mem_of_superset (isOpen_interior.mem_nhds hz)
      (interior_subset.trans (extChartAt_target_subset_range x₀))
  -- The coordinate expression of `α` is smooth on `W`.
  have hηW : ContDiffOn ℝ ∞ η W := by
    intro z hz
    have hx : e.symm z ∈ U := hz.2
    have h₁ : ContDiffWithinAt ℝ ∞ (α.inChartAt (e.symm z)) (range I)
        (extChartAt I (e.symm z) (e.symm z)) :=
      α.contDiffWithinAt_range_inChartAt_of_contMDiffAt ((hα _ hx).contMDiffAt (hU.mem_nhds hx))
    have h₂ := α.contDiffWithinAt_inChartAt_of_contDiffWithinAt_inChartAt (n := ∞)
      (interior_subset hz.1) (mem_extChartAt_source _) h₁
    exact (h₂.contDiffAt (hrange hz.1)).contDiffWithinAt
  -- The coordinate expression is a contact form at the image of `x₀`.
  have hηy₀ : η y₀ = α x₀ := α.inChartAt_extChartAt_self x₀
  have hdη : extDeriv η y₀ = mextDeriv α x₀ := by
    have hd : DifferentiableWithinAt ℝ η (range I) y₀ :=
      ((hηW.contDiffAt (hW.mem_nhds hy₀W)).differentiableAt (by simp)).differentiableWithinAt
    have h := α.inChartAt_mextDeriv (x₀ := x₀) (z := y₀) (mem_extChartAt_target x₀)
      (by rw [hy₀, he, extChartAt_to_inv]; exact hd)
    rw [hy₀, he, RoughForm.inChartAt_extChartAt_self] at h
    rw [h, ← extDerivWithin_univ, extDerivWithin_congr_set
      (eventuallyEqSet_univ.2 (hrange hy₀W.1))]
  have hcη : IsContactFormAt (I := 𝓘(ℝ, E)) η y₀ := by
    refine ⟨by rw [hηy₀]; exact hc.ne_zero, fun v hv hvw ↦ hc.nondegenerate v ?_ fun w hw ↦ ?_⟩
    · have h := RoughForm.mem_ker.1 hv
      rw [hηy₀] at h
      exact RoughForm.mem_ker.2 h
    · have hw' := RoughForm.mem_ker.1 hw
      rw [← hηy₀] at hw'
      calc mextDeriv α x₀ ![v, w] = extDeriv η y₀ ![v, w] := congrArg (fun A ↦ A ![v, w]) hdη.symm
        _ = mextDeriv η y₀ ![v, w] := congrArg (fun A ↦ A ![v, w])
          (mextDeriv_eq_extDeriv (E := E) (F := ℝ) (k := 1) η y₀).symm
        _ = 0 := hvw w (RoughForm.mem_ker.2 hw')
  -- The flat contact Darboux theorem, on an open set of coordinates where it holds.
  obtain ⟨n, Φ, g, hΦy₀, hev⟩ :=
    exists_diffeomorph_eventually_innerProductContactForm_apply_fderiv_eq_mul (r := ⊤) le_top hW
      hy₀W (hηW.of_le (by simp)) hcη
  obtain ⟨t, ht, ht_open, hy₀t⟩ := eventually_nhds_iff.1 hev
  obtain ⟨chart, hsrc, hcoe, hmvf⟩ :=
    exists_partialDiffeomorph_comp_extChartAt I ∞ x₀ (ht_open.inter hW)
      (inter_subset_right.trans inter_subset_left) (by simp) Φ
  -- The model space has dimension `2 n + 1`, the dimension of `E`.
  have hdim : finrank ℝ E = 2 * n + 1 := by
    obtain ⟨L, -⟩ := Φ.isInvertible_mfderiv (x := y₀) (by simp)
    have hL := L.toLinearEquiv.finrank_eq
    -- The tangent spaces of a normed space are the space itself.
    change finrank ℝ E = finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) at hL
    rw [hL, finrank_prod, finrank_prod, finrank_euclideanSpace_fin, finrank_self]
    ring
  refine ⟨n, chart, g ∘ e, hdim, ?_, fun x hx ↦ ?_, by rw [hcoe, hΦy₀], fun x hx ↦ ?_⟩
  · rw [hsrc]
    exact ⟨mem_extChartAt_source x₀, hy₀t, hy₀W⟩
  · rw [hsrc] at hx
    have h := hx.2.2.2
    rwa [mem_preimage, he, (extChartAt I x₀).left_inv hx.1] at h
  · have hx' := hx
    rw [hsrc] at hx'
    obtain ⟨hg, hΦ⟩ := ht (e x) hx'.2.1
    refine ⟨hg, fun v ↦ ?_⟩
    rw [hcoe, hmvf x hx v, hΦ, Function.comp_apply,
      RoughForm.apply_eq_inChartAt_mvfderiv α hx'.1]
    congr 2
    ext i
    fin_cases i
    rfl

/-- **The contact Darboux theorem at an interior point.** Let `α` be a one-form, smooth on an open
set `U`, which is a contact form at an interior point `x₀ ∈ U`. Then there are `n` and a smooth
partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source ⊆ U` and
`chart x₀ = 0`, together with a function `g` positive on `chart.source`, such that `chart` pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `g α` on `chart.source`. -/
theorem IsContactFormAt.exists_darbouxChart_of_isInteriorPoint {α : RoughForm I M ℝ 1} {x₀ : M}
    (hc : IsContactFormAt α x₀) {U : Set M} (hU : IsOpen U) (hx₀U : x₀ ∈ U)
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
  obtain ⟨n, chart, g, -, h⟩ := hc.exists_darbouxChart_aux hU hx₀U hα hx₀
  exact ⟨n, chart, g, h⟩

/-- **The contact Darboux theorem at an interior point, in dimension `2 n + 1`.** On a manifold of
dimension `2 n + 1`, the contact Darboux chart of a local contact form at an interior point lands
in `ℝⁿ × ℝⁿ × ℝ` for this `n`. -/
theorem IsContactFormAt.exists_darbouxChart_of_finrank_eq_of_isInteriorPoint
    {α : RoughForm I M ℝ 1} {x₀ : M} (hc : IsContactFormAt α x₀) {n : ℕ}
    (hn : finrank ℝ E = 2 * n + 1) {U : Set M} (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = g x * α x ![v] := by
  obtain ⟨m, chart, g, hm, h⟩ := hc.exists_darbouxChart_aux hU hx₀U hα hx₀
  obtain rfl : m = n := by omega
  exact ⟨chart, g, h⟩

section Boundaryless

variable [BoundarylessManifold I M]

/-- **The contact Darboux theorem.** On a boundaryless manifold, let `α` be a one-form, smooth on
an open set `U`, which is a contact form at `x₀ ∈ U`. Then there are `n` and a smooth partial
diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source ⊆ U` and `chart x₀ = 0`,
together with a function `g` positive on `chart.source`, such that `chart` pulls the standard
contact form `dz - Σᵢ pᵢ dqᵢ` back to `g α` on `chart.source`. -/
theorem IsContactFormAt.exists_darbouxChart {α : RoughForm I M ℝ 1} {x₀ : M}
    (hc : IsContactFormAt α x₀) {U : Set M} (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = g x * α x ![v] :=
  hc.exists_darbouxChart_of_isInteriorPoint hU hx₀U hα BoundarylessManifold.isInteriorPoint

/-- **The contact Darboux theorem in dimension `2 n + 1`.** On a boundaryless manifold of dimension
`2 n + 1`, the contact Darboux chart of a local contact form lands in `ℝⁿ × ℝⁿ × ℝ` for this
`n`. -/
theorem IsContactFormAt.exists_darbouxChart_of_finrank_eq {α : RoughForm I M ℝ 1} {x₀ : M}
    (hc : IsContactFormAt α x₀) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1) {U : Set M}
    (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U) :
    ∃ (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = g x * α x ![v] :=
  hc.exists_darbouxChart_of_finrank_eq_of_isInteriorPoint hn hU hx₀U hα
    BoundarylessManifold.isInteriorPoint

/-- **The contact Darboux theorem for a global contact form.** Around every point `x₀` of a
boundaryless manifold with a contact form `α`, there are `n` and a smooth partial diffeomorphism
`chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and `chart x₀ = 0`, together with a
function `g` positive on `chart.source`, such that `chart` pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` back to `g α` on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_darbouxChart {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞) (g : M → ℝ),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, 0 < g x ∧ ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = g x * α.1 x ![v] := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨n, chart, g, hx₀, -, h0, h⟩ :=
    (isContactForm_iff_forall_isContactFormAt.1 hα x₀).exists_darbouxChart isOpen_univ
      (mem_univ x₀) α.contMDiff.contMDiffOn
  exact ⟨n, chart, g, hx₀, h0, h⟩

/-- **Contact charts for a contact structure.** Around every point `x₀` of a boundaryless
manifold with a smooth contact structure `ξ`, not necessarily coorientable, there are `n` and a
smooth partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and
`chart x₀ = 0`, whose differential carries `ξ` to the standard contact structure: on
`chart.source`, `ξ_x` is the inverse image of `ker (dz - Σᵢ pᵢ dqᵢ)` under the differential of
`chart`. -/
theorem IsContactDistribution.exists_darbouxChart {ξ : (x : M) → Submodule ℝ (TangentSpace I x)}
    (hξ : IsContactDistribution I ∞ ξ) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ξ x =
        ((innerProductContactForm (EuclideanSpace ℝ (Fin n))).kerDistribution (chart x)).comap
          (mvfderiv I chart x).toLinearMap := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨U, hU, hx₀U, α, hα, hαξ⟩ := hξ.exists_isContactFormAt (by simp) x₀
  obtain ⟨n, chart, g, hx₀, hsub, h0, h⟩ := (hαξ x₀ hx₀U).2.exists_darbouxChart hU hx₀U hα
  refine ⟨n, chart, hx₀, h0, fun x hx ↦ ?_⟩
  obtain ⟨hg, hpull⟩ := h x hx
  rw [← (hαξ x (hsub hx)).1]
  ext v
  refine RoughForm.mem_ker.trans (Iff.trans ?_ Submodule.mem_comap.symm)
  refine Iff.trans ?_ SmoothForm.mem_kerDistribution.symm
  simp only [ContinuousLinearMap.coe_coe]
  rw [hpull, mul_eq_zero, or_iff_right hg.ne']

end Boundaryless

end TauCeti
