/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Extension by zero away from an artificial boundary

Weak derivatives extend by zero from an open set `Ω` to another open set `V` when their
values vanish off a closed set `K` with `V ∩ K ⊆ Ω`. Unlike whole-space zero extension,
this permits the support to meet the boundary of `V`. It is the extension principle used
when localizing a Sobolev function in a boundary chart: only the artificial chart boundary
must be avoided.

This generalizes the compact-support argument of
`TauCeti.HasWeakLineDerivOn.indicator_of_isCompact`. Each test function is localized near
its compact intersection with `K`, using `IsCompact.exists_contDiff_cutoff`. The argument
follows H. Brezis,
*Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Lemma 9.5,
with the support condition imposed relative to the target domain.
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} {Ω V : Opens E} {u u' : E → F} {v : E} {K : Set E}

/-- Weak directional derivatives extend by zero to `V` if the value and derivative vanish
almost everywhere off a closed `K` whose intersection with `V` lies in `Ω`. No boundary
condition on the part of `∂Ω` outside `V` is required. -/
theorem HasWeakLineDerivOn.indicator_of_isClosed (h : HasWeakLineDerivOn μ Ω u u' v)
    (hK : IsClosed K) (hKV : (V : Set E) ∩ K ⊆ Ω)
    (hu : ∀ᵐ x ∂μ.restrict Ω, x ∉ K → u x = 0)
    (hu' : ∀ᵐ x ∂μ.restrict Ω, x ∉ K → u' x = 0) :
    HasWeakLineDerivOn μ V ((Ω : Set E).indicator u) ((Ω : Set E).indicator u') v := by
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨h.completeSpace,
    h.locallyIntegrableOn.indicator_of_isClosed Ω.isOpen.measurableSet
      V.isOpen.isLocallyClosed hK hKV hu,
    h.locallyIntegrableOn_deriv.indicator_of_isClosed Ω.isOpen.measurableSet
      V.isOpen.isLocallyClosed hK hKV hu', ?_⟩
  intro φ
  -- Only the compact part of the test support that meets `K` needs a cutoff.
  have hC : IsCompact (tsupport (φ : E → ℝ) ∩ K) := φ.hasCompactSupport.inter_right hK
  obtain ⟨χ, hχ, -, hχone, -, hχΩ⟩ := hC.exists_contDiff_cutoff Ω.isOpen
    (fun x hx => hKV ⟨φ.tsupport_subset hx.1, hx.2⟩)
  let ψ : 𝓓(Ω, ℝ) := ⟨χ * (φ : E → ℝ), hχ.mul φ.contDiff,
    φ.hasCompactSupport.mul_left, tsupport_mul_subset_left.trans hχΩ⟩
  have hψ : (ψ : E → ℝ) = χ * (φ : E → ℝ) := TestFunction.coe_mk
  have hone (x : E) (hx : x ∈ tsupport (φ : E → ℝ) ∩ K) :
      χ =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_interior.mem_nhds (hχone hx)] with y hy
    have hy' : y ∈ χ ⁻¹' ({1} : Set ℝ) := interior_subset hy
    exact hy'
  -- The cutoff leaves both test pairings unchanged where the jet can be nonzero.
  have hleft : (fun x => lineDeriv ℝ (φ : E → ℝ) x v • (Ω : Set E).indicator u x) =ᵐ[μ]
      fun x => lineDeriv ℝ (ψ : E → ℝ) x v • u x := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hu] with x hx
    by_cases hxφ : x ∈ tsupport (φ : E → ℝ)
    · by_cases hxK : x ∈ K
      · have hxΩ := hKV ⟨φ.tsupport_subset hxφ, hxK⟩
        have heq : (ψ : E → ℝ) =ᶠ[nhds x] (φ : E → ℝ) := by
          filter_upwards [hone x ⟨hxφ, hxK⟩] with y hy
          simp [hψ, hy]
        rw [indicator_of_mem hxΩ, heq.lineDeriv_eq]
      · by_cases hxΩ : x ∈ (Ω : Set E)
        · simp [indicator_of_mem hxΩ, hx hxΩ hxK]
        · rw [indicator_of_notMem hxΩ]
          have hxψ : x ∉ tsupport (ψ : E → ℝ) := fun hxψ =>
            hxΩ (ψ.tsupport_subset hxψ)
          simp [lineDeriv_eq_zero_of_notMem_tsupport ψ hxψ v]
    · have hxψ : x ∉ tsupport (ψ : E → ℝ) := fun hxψ =>
        hxφ (tsupport_mul_subset_right (by rw [hψ, Pi.mul_def] at hxψ; exact hxψ))
      simp [lineDeriv_eq_zero_of_notMem_tsupport φ hxφ v,
        lineDeriv_eq_zero_of_notMem_tsupport ψ hxψ v]
  have hright : (fun x => (φ : E → ℝ) x • (Ω : Set E).indicator u' x) =ᵐ[μ]
      fun x => (ψ : E → ℝ) x • u' x := by
    filter_upwards [(ae_restrict_iff' Ω.isOpen.measurableSet).1 hu'] with x hx
    by_cases hxφ : x ∈ tsupport (φ : E → ℝ)
    · by_cases hxK : x ∈ K
      · simp [hψ, (hone x ⟨hxφ, hxK⟩).eq_of_nhds,
          indicator_of_mem (hKV ⟨φ.tsupport_subset hxφ, hxK⟩)]
      · by_cases hxΩ : x ∈ (Ω : Set E)
        · simp [hψ, indicator_of_mem hxΩ, hx hxΩ hxK]
        · have hχzero : χ x = 0 := image_eq_zero_of_notMem_tsupport
            (fun hxχ => hxΩ (hχΩ hxχ))
          simp [hψ, indicator_of_notMem hxΩ, hχzero]
    · simp [hψ, image_eq_zero_of_notMem_tsupport hxφ]
  rw [integral_congr_ae hleft, integral_congr_ae hright]
  exact h.integral_lineDeriv_smul_eq_neg_integral_smul ψ

/-- The Fréchet form of relative zero extension: a weak derivative extends by zero when
both it and the value vanish off a closed set contained in the source inside the target. -/
theorem HasWeakFDerivOn.indicator_of_isClosed {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn μ Ω u U) (hK : IsClosed K) (hKV : (V : Set E) ∩ K ⊆ Ω)
    (hu : ∀ᵐ x ∂μ.restrict Ω, x ∉ K → u x = 0)
    (hU : ∀ᵐ x ∂μ.restrict Ω, x ∉ K → U x = 0) :
    HasWeakFDerivOn μ V ((Ω : Set E).indicator u) ((Ω : Set E).indicator U) := by
  refine hasWeakFDerivOn_iff.2 fun v => ?_
  have hUv : ∀ᵐ x ∂μ.restrict Ω, x ∉ K → U x v = 0 := by
    filter_upwards [hU] with x hx hxK
    simp [hx hxK]
  refine ((h.hasWeakLineDerivOn v).indicator_of_isClosed hK hKV hu hUv).congr_ae_deriv
    (.of_forall fun x => ?_)
  by_cases hx : x ∈ (Ω : Set E) <;> simp [hx]

end TauCeti
