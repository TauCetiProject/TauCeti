/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.BoundaryPart
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.Sobolev.W1p.BoundaryPart.ChangeOfVariables
import TauCeti.Analysis.Sobolev.W1p.Interval.OneEndpoint

/-!
# The interval domain

This file realizes the open interval `(a, b)` as the open subset `TauCeti.PDE.intervalDomain a b`
of the Euclidean line `EuclideanSpace ℝ (Fin 1)`, the setting of the Sobolev spaces and the energy
forms of the PDE library. Composition with the isometry `TauCeti.PDE.lineEquiv : t ↦ t e₀`
identifies its Sobolev spaces with those of the real interval `(a, b)`
(`TauCeti.PDE.intervalDomainEquivL`), where functions have continuous representatives and
endpoint values.

## Main declarations

* `TauCeti.PDE.intervalDomain`: the interval `(a, b)` as an open subset of the Euclidean line.
* `TauCeti.PDE.lineEquiv`: the isometry `t ↦ t e₀` of `ℝ` onto the Euclidean line.
* `TauCeti.PDE.isBounded_intervalDomain`: the interval domain is bounded, so it has finite volume.
* `TauCeti.PDE.setIntegral_intervalDomain`: integrals over the interval domain are integrals over
  the real interval.
* `TauCeti.PDE.intervalDomainEquivL`: `W^{1,p}` of the interval domain is `W^{1,p}` of the real
  interval, with the value, derivative, integral, boundary part and Dirichlet form transferred by
  `TauCeti.PDE.value_intervalDomainEquivL_ae`, `TauCeti.PDE.gradient_intervalDomainEquivL_ae`,
  `TauCeti.PDE.setIntegral_value_intervalDomainEquivL`,
  `TauCeti.PDE.intervalDomainEquivL_mem_w1pVanishingOnSubmodule_iff` and
  `TauCeti.PDE.energyFormH1_one_zero_zero_eq_setIntegral_intervalDomainEquivL`.
* `TauCeti.PDE.norm_value_le_mul_norm_gradient_intervalDomain`: the Poincaré–Friedrichs inequality
  `‖u‖ ≤ (b - a) ‖u'‖` on `W^{1,p}_{{a}}(a, b)`.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology _root_.MeasureTheory Set TopologicalSpace

/-- The open interval `(a, b)`, as an open subset of the Euclidean line `EuclideanSpace ℝ (Fin 1)`.
-/
def intervalDomain (a b : ℝ) : Opens (EuclideanSpace ℝ (Fin 1)) :=
  ⟨{x | x 0 ∈ Ioo a b}, isOpen_Ioo.preimage (by fun_prop)⟩

@[simp]
theorem mem_intervalDomain {a b : ℝ} {x : EuclideanSpace ℝ (Fin 1)} :
    x ∈ intervalDomain a b ↔ x 0 ∈ Ioo a b :=
  Iff.rfl

/-- As a set, the interval domain consists of the points of the line whose coordinate lies in
`(a, b)`. -/
theorem coe_intervalDomain (a b : ℝ) :
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) = {x | x 0 ∈ Ioo a b} := by
  ext x
  exact mem_intervalDomain

/-- The interval domain `(a, b)` is preconnected. -/
theorem isPreconnected_intervalDomain (a b : ℝ) :
    IsPreconnected (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) :=
  ((convex_Ioo a b).linear_preimage (EuclideanSpace.projₗ (0 : Fin 1))).isPreconnected

variable {a b : ℝ}

/-- The Euclidean line is isometric to `ℝ`, through `t ↦ t e₀`, with inverse `x ↦ x 0`. -/
def lineEquiv : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

/-- The inverse of `TauCeti.PDE.lineEquiv` is the coordinate `x ↦ x 0`. -/
theorem lineEquiv_symm_apply (x : EuclideanSpace ℝ (Fin 1)) :
    lineEquiv.symm x = x 0 := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext i
  fin_cases i
  exact (OrthonormalBasis.singleton_repr (ι := Fin 1) (𝕜 := ℝ) (x 0) 0).symm

/-- `TauCeti.PDE.lineEquiv` preserves Lebesgue measure. -/
theorem measurePreserving_lineEquiv : MeasurePreserving lineEquiv volume volume :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).measurePreserving_repr

/-- The inverse of `TauCeti.PDE.lineEquiv` preserves Lebesgue measure. -/
theorem measurePreserving_lineEquiv_symm :
    MeasurePreserving lineEquiv.symm volume volume :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).measurePreserving_repr_symm

/-- The coordinate of `TauCeti.PDE.lineEquiv t` is `t`. -/
@[simp] theorem lineEquiv_apply_zero (t : ℝ) : lineEquiv t 0 = t := by
  rw [← lineEquiv_symm_apply, LinearIsometryEquiv.symm_apply_apply]

/-- The interval domain is the preimage of the real interval under the coordinate. -/
theorem coe_intervalDomain_eq_preimage :
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) = lineEquiv.symm ⁻¹' Ioo a b := by
  ext x
  simp [lineEquiv_symm_apply]

/-- The real interval is the preimage of the interval domain under `TauCeti.PDE.lineEquiv`. -/
@[simp] theorem preimage_lineEquiv_intervalDomain :
    lineEquiv ⁻¹' (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) = Ioo a b := by
  rw [coe_intervalDomain_eq_preimage, ← preimage_comp]
  simp


/-- The interval domain `(a, b)` is bounded. -/
theorem isBounded_intervalDomain :
    IsBounded (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) := by
  rw [coe_intervalDomain_eq_preimage]
  exact lineEquiv.symm.antilipschitzWith.isBounded_preimage (Metric.isBounded_Ioo a b)

/-- The interval domain `(a, b)` has finite volume. -/
instance instIsFiniteMeasureRestrictIntervalDomain :
    IsFiniteMeasure (volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))) :=
  isFiniteMeasure_restrict.2 isBounded_intervalDomain.measure_lt_top.ne

/-- Integrals over the interval domain are integrals over the real interval: for `f : ℝ → E`,
the integral of `x ↦ f (x 0)` over `TauCeti.PDE.intervalDomain a b` is `∫ t in Ioo a b, f t`. -/
theorem setIntegral_intervalDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ x in (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))), f (x 0) =
      ∫ t in Ioo a b, f t := by
  have h := measurePreserving_lineEquiv.setIntegral_preimage_emb
    lineEquiv.toHomeomorph.measurableEmbedding (fun x => f (x 0))
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))
  rw [preimage_lineEquiv_intervalDomain] at h
  simp only [lineEquiv_apply_zero] at h
  exact h.symm

/-! ### Sobolev functions on the interval domain and on the real interval -/

section Sobolev

open scoped ENNReal

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inverse of `TauCeti.PDE.lineEquiv` as an affine isometry is its inverse as a linear
isometry. -/
private theorem coe_lineEquiv_toAffineIsometryEquiv_symm :
    ⇑lineEquiv.toAffineIsometryEquiv.symm = lineEquiv.symm := by
  funext x
  rw [AffineIsometryEquiv.symm_apply_eq, LinearIsometryEquiv.coe_toAffineIsometryEquiv,
    LinearIsometryEquiv.apply_symm_apply]

private theorem coe_Ioo_eq_preimage_intervalDomain :
    ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) =
      lineEquiv.toAffineIsometryEquiv ⁻¹'
        (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) := by
  rw [LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  exact preimage_lineEquiv_intervalDomain.symm

private theorem coe_intervalDomain_eq_preimage_Ioo :
    (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))) =
      lineEquiv.toAffineIsometryEquiv.symm ⁻¹' ((⟨Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ) := by
  rw [coe_lineEquiv_toAffineIsometryEquiv_symm]
  exact coe_intervalDomain_eq_preimage

/-- **Sobolev functions on the interval domain are Sobolev functions on the real interval.**
Composition with `TauCeti.PDE.lineEquiv` identifies `W^{1,p}` of the interval domain `(a, b)` of
the Euclidean line with `W^{1,p}` of the real interval `(a, b)`. -/
def intervalDomainEquivL (a b : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    W1p volume (intervalDomain a b) p ≃L[ℝ] W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p :=
  .ofContinuousLinearMap
    (W1p.compAffineIsometryEquivL lineEquiv.toAffineIsometryEquiv
      coe_Ioo_eq_preimage_intervalDomain)
    (W1p.compAffineIsometryEquivL lineEquiv.toAffineIsometryEquiv.symm
      coe_intervalDomain_eq_preimage_Ioo)
    (ContinuousLinearMap.ext fun w => W1p.compAffineIsometryEquivL_symm_compAffineIsometryEquivL
      lineEquiv.toAffineIsometryEquiv.symm coe_intervalDomain_eq_preimage_Ioo
      coe_Ioo_eq_preimage_intervalDomain w)
    (ContinuousLinearMap.ext fun u => W1p.compAffineIsometryEquivL_symm_compAffineIsometryEquivL
      lineEquiv.toAffineIsometryEquiv coe_Ioo_eq_preimage_intervalDomain
      coe_intervalDomain_eq_preimage_Ioo u)

private theorem intervalDomainEquivL_apply (u : W1p volume (intervalDomain a b) p) :
    intervalDomainEquivL a b p u = W1p.compAffineIsometryEquivL lineEquiv.toAffineIsometryEquiv
      coe_Ioo_eq_preimage_intervalDomain u :=
  rfl

private theorem intervalDomainEquivL_symm_apply (w : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    (intervalDomainEquivL a b p).symm w = W1p.compAffineIsometryEquivL
      lineEquiv.toAffineIsometryEquiv.symm coe_intervalDomain_eq_preimage_Ioo w :=
  rfl

/-- The value of the transfer of `u` to the real interval is the value of `u` along
`TauCeti.PDE.lineEquiv`. -/
theorem value_intervalDomainEquivL_ae (u : W1p volume (intervalDomain a b) p) :
    W1p.value (intervalDomainEquivL a b p u) =ᵐ[volume.restrict (Ioo a b)]
      fun t => W1p.value u (lineEquiv t) := by
  filter_upwards [W1p.value_compAffineIsometryEquivL_ae _
    coe_Ioo_eq_preimage_intervalDomain u] with t ht
  rw [intervalDomainEquivL_apply, ht, LinearIsometryEquiv.coe_toAffineIsometryEquiv]

/-- The weak derivative of the transfer of `u` to the real interval is the coordinate of the weak
gradient of `u` along `TauCeti.PDE.lineEquiv`. -/
theorem gradient_intervalDomainEquivL_ae (u : W1p volume (intervalDomain a b) p) :
    W1p.gradient (intervalDomainEquivL a b p u) =ᵐ[volume.restrict (Ioo a b)]
      fun t => W1p.gradient u (lineEquiv t) 0 := by
  filter_upwards [W1p.gradient_compAffineIsometryEquivL_ae _
    coe_Ioo_eq_preimage_intervalDomain u] with t ht
  rw [intervalDomainEquivL_apply, ht,
    LinearIsometryEquiv.toAffineIsometryEquiv_linearIsometryEquiv,
    LinearIsometryEquiv.coe_toAffineIsometryEquiv, lineEquiv_symm_apply]

/-- The value of the transfer of `w` back to the interval domain is the value of `w` at the
coordinate `x 0`. -/
theorem value_intervalDomainEquivL_symm_ae (w : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ p) :
    W1p.value ((intervalDomainEquivL a b p).symm w)
      =ᵐ[volume.restrict (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1)))]
        fun x => W1p.value w (x 0) := by
  filter_upwards [W1p.value_compAffineIsometryEquivL_ae _
    coe_intervalDomain_eq_preimage_Ioo w] with x hx
  rw [intervalDomainEquivL_symm_apply, hx, coe_lineEquiv_toAffineIsometryEquiv_symm,
    lineEquiv_symm_apply]

/-- The transfer to the real interval preserves the `Lᵖ` norm of the value. -/
theorem norm_value_intervalDomainEquivL (u : W1p volume (intervalDomain a b) p) :
    ‖W1p.value (intervalDomainEquivL a b p u)‖ = ‖W1p.value u‖ :=
  W1p.norm_value_compAffineIsometryEquivL _ _ u

/-- The transfer to the real interval preserves the `Lᵖ` norm of the weak gradient. -/
theorem norm_gradient_intervalDomainEquivL (u : W1p volume (intervalDomain a b) p) :
    ‖W1p.gradient (intervalDomainEquivL a b p u)‖ = ‖W1p.gradient u‖ :=
  W1p.norm_gradient_compAffineIsometryEquivL _ _ u

/-- **Boundary parts under the transfer to the real interval.** The transfer of `u` vanishes on
`lineEquiv⁻¹(Γ)` exactly when `u` vanishes on `Γ`. -/
theorem intervalDomainEquivL_mem_w1pVanishingOnSubmodule_iff
    {Γ : Set (EuclideanSpace ℝ (Fin 1))} {u : W1p volume (intervalDomain a b) p} :
    intervalDomainEquivL a b p u ∈
        w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p (lineEquiv ⁻¹' Γ) ↔
      u ∈ w1pVanishingOnSubmodule volume (intervalDomain a b) p Γ := by
  have h : lineEquiv ⁻¹' Γ = lineEquiv.toAffineIsometryEquiv ⁻¹' Γ := by
    rw [LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  rw [h, intervalDomainEquivL_apply]
  exact W1p.compAffineIsometryEquivL_mem_w1pVanishingOnSubmodule_iff
    lineEquiv.toAffineIsometryEquiv coe_Ioo_eq_preimage_intervalDomain

/-- The transfer of `u` to the real interval vanishes at `c` exactly when `u` vanishes at the
point `TauCeti.PDE.lineEquiv c` of the Euclidean line. -/
theorem intervalDomainEquivL_mem_w1pVanishingOnSubmodule_singleton_iff {c : ℝ}
    {u : W1p volume (intervalDomain a b) p} :
    intervalDomainEquivL a b p u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ p {c} ↔
      u ∈ w1pVanishingOnSubmodule volume (intervalDomain a b) p {lineEquiv c} := by
  have h : lineEquiv ⁻¹' {lineEquiv c} = {c} := by
    ext t
    simp
  rw [← intervalDomainEquivL_mem_w1pVanishingOnSubmodule_iff, h]

/-- **The Poincaré–Friedrichs inequality on the interval domain with `Γ = {a}`**: every
`u ∈ W^{1,p}_{{a}}(a, b)` satisfies `‖u‖_{Lᵖ} ≤ (b - a) ‖u'‖_{Lᵖ}`. -/
theorem norm_value_le_mul_norm_gradient_intervalDomain (hab : a < b)
    {u : W1p volume (intervalDomain a b) p}
    (hu : u ∈ w1pVanishingOnSubmodule volume (intervalDomain a b) p {lineEquiv a}) :
    ‖W1p.value u‖ ≤ (b - a) * ‖W1p.gradient u‖ := by
  rw [← norm_value_intervalDomainEquivL, ← norm_gradient_intervalDomainEquivL]
  exact W1p.norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero hab
    (W1p.intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab
      (intervalDomainEquivL_mem_w1pVanishingOnSubmodule_singleton_iff.2 hu))

/-- Integrals over the interval domain are integrals over the real interval along
`TauCeti.PDE.lineEquiv`. -/
theorem setIntegral_intervalDomain_eq_setIntegral_Ioo {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : EuclideanSpace ℝ (Fin 1) → E) :
    ∫ x in (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))), F x =
      ∫ t in Ioo a b, F (lineEquiv t) := by
  rw [← setIntegral_intervalDomain]
  simp_rw [← lineEquiv_symm_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The integral of `u` over the interval domain is the integral of its transfer over the real
interval. -/
theorem setIntegral_value_intervalDomainEquivL (u : W1p volume (intervalDomain a b) p) :
    ∫ x in (intervalDomain a b : Set (EuclideanSpace ℝ (Fin 1))), W1p.value u x =
      ∫ t in Ioo a b, W1p.value (intervalDomainEquivL a b p u) t := by
  rw [setIntegral_intervalDomain_eq_setIntegral_Ioo]
  exact integral_congr_ae (value_intervalDomainEquivL_ae u).symm

/-- The Dirichlet form of `-Δ` on the interval domain is `∫_a^b v' u'`, computed on the real
interval. -/
theorem energyFormH1_one_zero_zero_eq_setIntegral_intervalDomainEquivL
    (u v : W1p volume (intervalDomain a b) 2) :
    energyFormH1 (fun _ => 1) 0 0 u v =
      ∫ t in Ioo a b, W1p.gradient (intervalDomainEquivL a b 2 v) t *
        W1p.gradient (intervalDomainEquivL a b 2 u) t := by
  rw [energyFormH1_one_zero_zero_apply, setIntegral_intervalDomain_eq_setIntegral_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [gradient_intervalDomainEquivL_ae u, gradient_intervalDomainEquivL_ae v]
    with t hu hv
  simp [hu, hv, dotProduct]

end Sobolev

end PDE

end TauCeti
