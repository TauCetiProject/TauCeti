/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Nontangential.Fatou.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Bounded
import TauCeti.Topology.LimUnder

/-!
# The boundary function of a bounded holomorphic function on the upper half-plane

For `F : ℂ → ℂ`, the **boundary function** `F* = TauCeti.upperHalfPlaneBoundaryFun F` is the
nontangential limit of `F` at the points of `ℝ`: `F*(x)` is the limit of `F(z)` as `z → x`
through the cone `Γ¹(x) = {z : |Re z - x| < Im z}` (`TauCeti.nontangentialFilter 1 x`), where
that limit exists. It is the limit through cones of every aperture `α ≥ 1` wherever that exists
(`TauCeti.upperHalfPlaneBoundaryFun_eq_of_tendsto`).

For `F` holomorphic and bounded on `ℂ₊`, by `‖F‖ ≤ S` say:

* `F = P[w]` for a bounded measurable `w`
  (`TauCeti.exists_eq_upperHalfPlanePoissonIntegralFun_of_norm_le`), and Fatou's theorem for
  `w ∈ L¹(Π)` (`TauCeti.ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun`) gives,
  for almost every `x`, `F → F*(x)` nontangentially through cones of every aperture
  (`TauCeti.ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun`), and `F* = w` almost
  everywhere.
* Hence `F = P[F*]` on `ℂ₊`
  (`TauCeti.eq_upperHalfPlanePoissonIntegralFun_upperHalfPlaneBoundaryFun`) and `‖F*‖ ≤ S`
  almost everywhere (`TauCeti.ae_norm_upperHalfPlaneBoundaryFun_le`), so
  `‖F*‖_∞ ≤ sup_{ℂ₊} ‖F‖`. In particular `F* ∈ L^∞(ℝ)`
  (`TauCeti.memLp_top_upperHalfPlaneBoundaryFun`) and `F* ∈ L¹(Π)`
  (`TauCeti.integrable_upperHalfPlanePoissonMeasure_upperHalfPlaneBoundaryFun`).
* `F ↦ F*` is linear and multiplicative almost everywhere on bounded holomorphic functions
  (`TauCeti.upperHalfPlaneBoundaryFun_add_ae_eq`, `TauCeti.upperHalfPlaneBoundaryFun_smul_ae_eq`,
  `TauCeti.upperHalfPlaneBoundaryFun_mul_ae_eq`).

If `F` is continuous at `x` within the closed half-plane, then `F*(x) = F(x)`
(`TauCeti.upperHalfPlaneBoundaryFun_eq_of_continuousWithinAt`); in particular the boundary
function of a constant is that constant.

## References

* J. B. Garnett, *Bounded Analytic Functions*, revised 1st ed., Springer (2007), Chapter I, §§3-5.
-/

public section

noncomputable section

namespace TauCeti

open Complex MeasureTheory Filter Set Topology
open UpperHalfPlane (upperHalfPlaneSet)

/-- The **boundary function** `F*` of `F : ℂ → ℂ` on the upper half-plane: `F*(x)` is the
nontangential limit of `F` at `x ∈ ℝ` through the cone `|Re z - x| < Im z`, where it exists (and
an arbitrary value otherwise). -/
def upperHalfPlaneBoundaryFun (F : ℂ → ℂ) (x : ℝ) : ℂ :=
  limUnder (nontangentialFilter 1 x) F

/-- The defining formula of `TauCeti.upperHalfPlaneBoundaryFun`. -/
theorem upperHalfPlaneBoundaryFun_def (F : ℂ → ℂ) (x : ℝ) :
    upperHalfPlaneBoundaryFun F x = limUnder (nontangentialFilter 1 x) F :=
  (rfl)

/-- The boundary function is the nontangential limit through cones of any aperture `α ≥ 1`,
where that limit exists. -/
theorem upperHalfPlaneBoundaryFun_eq_of_tendsto {F : ℂ → ℂ} {α x : ℝ} {L : ℂ} (hα : 1 ≤ α)
    (hF : Tendsto F (nontangentialFilter α x) (𝓝 L)) : upperHalfPlaneBoundaryFun F x = L :=
  haveI := nontangentialFilter_neBot one_pos x
  (hF.mono_left (nontangentialFilter_mono hα x)).limUnder_eq

/-- At a point where `F` is continuous within the closed half-plane, its boundary function is its
value. -/
theorem upperHalfPlaneBoundaryFun_eq_of_continuousWithinAt {F : ℂ → ℂ} {x : ℝ}
    (hF : ContinuousWithinAt F {z | 0 ≤ z.im} x) : upperHalfPlaneBoundaryFun F x = F x := by
  refine upperHalfPlaneBoundaryFun_eq_of_tendsto le_rfl (hF.tendsto.mono_left ?_)
  rw [nontangentialFilter_def]
  refine nhdsWithin_mono _ fun z hz ↦ ?_
  exact (mem_nontangentialCone.1 hz).1.le

/-- The boundary function of a function continuous on the closed half-plane is its restriction
to `ℝ`. -/
theorem upperHalfPlaneBoundaryFun_eq_of_continuousOn {F : ℂ → ℂ}
    (hF : ContinuousOn F {z | 0 ≤ z.im}) (x : ℝ) : upperHalfPlaneBoundaryFun F x = F x :=
  upperHalfPlaneBoundaryFun_eq_of_continuousWithinAt (hF x (by simp))

/-- The boundary function of a constant is that constant. -/
@[simp]
theorem upperHalfPlaneBoundaryFun_const (c : ℂ) (x : ℝ) :
    upperHalfPlaneBoundaryFun (fun _ ↦ c) x = c :=
  upperHalfPlaneBoundaryFun_eq_of_continuousOn continuousOn_const x

/-- If `F = G` on the upper half-plane, then `F* = G*`. -/
theorem upperHalfPlaneBoundaryFun_congr {F G : ℂ → ℂ} (h : EqOn F G upperHalfPlaneSet) :
    upperHalfPlaneBoundaryFun F = upperHalfPlaneBoundaryFun G := by
  funext x
  refine limUnder_congr ?_
  filter_upwards [eventually_nontangentialFilter_abs_re_sub_le 1 x one_pos] with z hz
  exact h hz.1

section Bounded

variable {F G : ℂ → ℂ} {S T : ℝ}

/-- For `F` bounded and holomorphic on `ℂ₊`, the density of a Poisson representation `F = P[w]` is
the boundary function, almost everywhere, and `F → F*(x)` nontangentially through cones of every
aperture for almost every `x`. -/
private theorem exists_ae_eq_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    ∃ w : ℝ → ℂ, Measurable w ∧ Integrable w upperHalfPlanePoissonMeasure ∧
      (∀ z ∈ upperHalfPlaneSet, F z = upperHalfPlanePoissonIntegralFun w z) ∧
      ∀ᵐ x, upperHalfPlaneBoundaryFun F x = w x ∧
        ∀ α : ℝ, Tendsto F (nontangentialFilter α x) (𝓝 (w x)) := by
  obtain ⟨w, hwm, -, hwi, hFw⟩ := exists_eq_upperHalfPlanePoissonIntegralFun_of_norm_le hF hS
  refine ⟨w, hwm, hwi, hFw, ?_⟩
  filter_upwards [ae_tendsto_nontangentialFilter_upperHalfPlanePoissonIntegralFun hwi] with x hx
  have hlim (α : ℝ) : Tendsto F (nontangentialFilter α x) (𝓝 (w x)) := by
    refine (hx α).congr' ?_
    filter_upwards [eventually_nontangentialFilter_abs_re_sub_le α x one_pos] with z hz
    exact (hFw z hz.1).symm
  exact ⟨upperHalfPlaneBoundaryFun_eq_of_tendsto le_rfl (hlim 1), hlim⟩

/-- **Nontangential limits of bounded holomorphic functions.** If `F` is holomorphic and bounded
on `ℂ₊`, then for almost every `x ∈ ℝ`, `F(z) → F*(x)` as `z → x` nontangentially, through cones
of every aperture. -/
theorem ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    ∀ᵐ x, ∀ α : ℝ, Tendsto F (nontangentialFilter α x) (𝓝 (upperHalfPlaneBoundaryFun F x)) := by
  obtain ⟨w, -, -, -, hw⟩ := exists_ae_eq_upperHalfPlaneBoundaryFun hF hS
  filter_upwards [hw] with x hx
  rw [hx.1]
  exact hx.2

/-- The boundary function of a bounded holomorphic function on `ℂ₊` is almost everywhere strongly
measurable. -/
theorem aestronglyMeasurable_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    AEStronglyMeasurable (upperHalfPlaneBoundaryFun F) := by
  obtain ⟨w, hwm, -, -, hw⟩ := exists_ae_eq_upperHalfPlaneBoundaryFun hF hS
  exact hwm.aestronglyMeasurable.congr (hw.mono fun x hx ↦ hx.1.symm)

/-- **The boundary function is bounded by the supremum**: if `‖F‖ ≤ S` on `ℂ₊` for a holomorphic
`F`, then `‖F*‖ ≤ S` almost everywhere. -/
theorem ae_norm_upperHalfPlaneBoundaryFun_le (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    ∀ᵐ x, ‖upperHalfPlaneBoundaryFun F x‖ ≤ S := by
  filter_upwards [ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hF hS] with x hx
  have := nontangentialFilter_neBot one_pos x
  refine le_of_tendsto (hx 1).norm ?_
  filter_upwards [eventually_nontangentialFilter_abs_re_sub_le 1 x one_pos] with z hz
  exact hS z hz.1

/-- **The boundary function is essentially bounded**: for `F` bounded and holomorphic on `ℂ₊`,
`F* ∈ L^∞(ℝ)`. -/
theorem memLp_top_upperHalfPlaneBoundaryFun (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) : MemLp (upperHalfPlaneBoundaryFun F) ⊤ :=
  memLp_top_of_bound (aestronglyMeasurable_upperHalfPlaneBoundaryFun hF hS) S
    (ae_norm_upperHalfPlaneBoundaryFun_le hF hS)

/-- The boundary function of a bounded holomorphic function on `ℂ₊` is integrable for the Poisson
measure `dx / (1 + x ^ 2)`. -/
theorem integrable_upperHalfPlanePoissonMeasure_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) :
    Integrable (upperHalfPlaneBoundaryFun F) upperHalfPlanePoissonMeasure := by
  obtain ⟨w, -, hwi, -, hw⟩ := exists_ae_eq_upperHalfPlaneBoundaryFun hF hS
  exact hwi.congr (upperHalfPlanePoissonMeasure_absolutelyContinuous.ae_le
    (hw.mono fun x hx ↦ hx.1.symm))

/-- **A bounded holomorphic function is the Poisson integral of its boundary function**:
`F = P[F*]` on `ℂ₊`. -/
theorem eq_upperHalfPlanePoissonIntegralFun_upperHalfPlaneBoundaryFun
    (hF : DifferentiableOn ℂ F upperHalfPlaneSet) (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    F z = upperHalfPlanePoissonIntegralFun (upperHalfPlaneBoundaryFun F) z := by
  obtain ⟨w, -, -, hFw, hw⟩ := exists_ae_eq_upperHalfPlaneBoundaryFun hF hS
  rw [hFw z hz, upperHalfPlanePoissonIntegralFun_def, upperHalfPlanePoissonIntegralFun_def]
  refine integral_congr_ae ?_
  filter_upwards [hw] with x hx
  rw [hx.1]

/-- On bounded holomorphic functions, `F ↦ F*` is additive almost everywhere. -/
theorem upperHalfPlaneBoundaryFun_add_ae_eq (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) (hG : DifferentiableOn ℂ G upperHalfPlaneSet)
    (hT : ∀ z ∈ upperHalfPlaneSet, ‖G z‖ ≤ T) :
    upperHalfPlaneBoundaryFun (F + G) =ᵐ[volume]
      upperHalfPlaneBoundaryFun F + upperHalfPlaneBoundaryFun G := by
  filter_upwards [ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hF hS,
    ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hG hT] with x hFx hGx
  exact upperHalfPlaneBoundaryFun_eq_of_tendsto le_rfl ((hFx 1).add (hGx 1))

/-- On bounded holomorphic functions, `F ↦ F*` is multiplicative almost everywhere. -/
theorem upperHalfPlaneBoundaryFun_mul_ae_eq (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) (hG : DifferentiableOn ℂ G upperHalfPlaneSet)
    (hT : ∀ z ∈ upperHalfPlaneSet, ‖G z‖ ≤ T) :
    upperHalfPlaneBoundaryFun (F * G) =ᵐ[volume]
      upperHalfPlaneBoundaryFun F * upperHalfPlaneBoundaryFun G := by
  filter_upwards [ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hF hS,
    ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hG hT] with x hFx hGx
  exact upperHalfPlaneBoundaryFun_eq_of_tendsto le_rfl ((hFx 1).mul (hGx 1))

/-- On bounded holomorphic functions, `F ↦ F*` commutes with scalar multiplication almost
everywhere. -/
theorem upperHalfPlaneBoundaryFun_smul_ae_eq (hF : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hS : ∀ z ∈ upperHalfPlaneSet, ‖F z‖ ≤ S) (c : ℂ) :
    upperHalfPlaneBoundaryFun (c • F) =ᵐ[volume] c • upperHalfPlaneBoundaryFun F := by
  filter_upwards [ae_tendsto_nontangentialFilter_upperHalfPlaneBoundaryFun hF hS] with x hFx
  exact upperHalfPlaneBoundaryFun_eq_of_tendsto le_rfl ((hFx 1).const_smul c)

end Bounded

end TauCeti
