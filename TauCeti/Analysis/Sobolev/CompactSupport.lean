/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.Analysis.Sobolev.WeakDeriv

/-!
# Extending a compactly supported weak derivative across the boundary

Extending a weakly differentiable function by zero across `∂Ω` destroys weak differentiability in
general: the jump along the boundary contributes a singular term that no locally integrable
function represents.  This file proves that the obstruction is entirely a boundary phenomenon.
If `u` and its weak derivative vanish almost everywhere outside a **compact** `K ⊆ Ω`, then the
extension of `u` by zero is weakly differentiable on the whole space, with the zero-extension of
the weak derivative as its derivative.

## The argument

Test the extension against a test function `φ` on the whole space.  A smooth cutoff `χ` equal to
`1` on a neighbourhood of `K` and compactly supported inside `Ω`
(`IsCompact.exists_contDiff_cutoff`) turns `χ φ` into a test function *on `Ω`*, to which the
hypothesis applies.  The product rule replaces `∂_v (χ φ)` by `χ ∂_v φ + (∂_v χ) φ`, and both
correction terms vanish where they are paired with `u`: off `K` because `u` does, and on `K`
because `χ` is constant there.  What is left is the defining identity for the extension.

Nothing is assumed about `∂Ω`; the compact support is what replaces boundary regularity.  The
same statement for a general `u ∈ W^{1,p}(Ω)` is false, and the extension theorem that repairs it
needs a Lipschitz boundary.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.indicator_of_isCompact`: the directional statement.
* `TauCeti.HasWeakFDerivOn.indicator_of_isCompact`: its Fréchet form.

## References

Lane A.2 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial Differential Equations*,
§5.3.3, and H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Lemma 9.5.
-/

public section

open MeasureTheory Set TopologicalSpace

open scoped ContDiff Distributions

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} {Omega : Opens E} {u u' : E → F} {v : E} {K : Set E}

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A function locally integrable on `Ω` and vanishing almost everywhere on `Ω` off a compact
`K ⊆ Ω` is, after extension by zero, integrable on the whole space. -/
private theorem integrable_indicator_of_isCompact (hK : IsCompact K) (hKO : K ⊆ Omega)
    (hloc : LocallyIntegrableOn u Omega mu)
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → u x = 0) :
    Integrable ((Omega : Set E).indicator u) mu := by
  have hae : (Omega : Set E).indicator u =ᵐ[mu] K.indicator u := by
    filter_upwards [(ae_restrict_iff' Omega.isOpen.measurableSet).1 hu] with x hx
    by_cases hxO : x ∈ (Omega : Set E)
    · by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxO, indicator_of_mem hxK]
      · rw [indicator_of_mem hxO, indicator_of_notMem hxK, hx hxO hxK]
    · rw [indicator_of_notMem hxO, indicator_of_notMem fun hxK => hxO (hKO hxK)]
  exact ((hloc.integrableOn_compact_subset hKO hK).integrable_indicator
    hK.isClosed.measurableSet).congr hae.symm

/-- **Extension by zero of a compactly supported weak directional derivative.**  If `u'` is a
weak derivative of `u` in the direction `v` on `Ω`, and both vanish almost everywhere on `Ω`
outside a compact `K ⊆ Ω`, then the zero-extension of `u'` is a weak derivative of the
zero-extension of `u` on the whole space.

No regularity of `∂Ω` is used: the cutoff isolating `K` from `∂Ω` is what makes the extension
weakly differentiable, and it exists for every open `Ω`. -/
theorem HasWeakLineDerivOn.indicator_of_isCompact (h : HasWeakLineDerivOn mu Omega u u' v)
    (hK : IsCompact K) (hKO : K ⊆ Omega)
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → u x = 0)
    (hu' : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → u' x = 0) :
    HasWeakLineDerivOn mu ⊤ ((Omega : Set E).indicator u) ((Omega : Set E).indicator u') v := by
  have _ := h.completeSpace
  obtain ⟨chi, hchi, -, hchi_one_nhds, hchi_cpt, hchi_tsupport⟩ :=
    hK.exists_contDiff_cutoff Omega.isOpen hKO
  -- the cutoff is constant near `K`, so it is one there and its derivative vanishes there
  have hchi_nhds : ∀ x ∈ K, chi =ᶠ[nhds x] (fun _ => 1 : E → ℝ) := by
    intro x hx
    filter_upwards [isOpen_interior.mem_nhds (hchi_one_nhds hx)] with y hy
    have hy' : y ∈ chi ⁻¹' ({1} : Set ℝ) := interior_subset hy
    exact hy'
  have hchi_one : ∀ x ∈ K, chi x = 1 := fun x hx => (hchi_nhds x hx).self_of_nhds
  have hchi_fderiv_K : ∀ x ∈ K, fderiv ℝ chi x = 0 := fun x hx => by
    rw [(hchi_nhds x hx).fderiv_eq]
    simp
  have hchi_zero : ∀ x ∉ (Omega : Set E), chi x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hchi_tsupport hx')
  have hchi_fderiv_zero : ∀ x ∉ (Omega : Set E), fderiv ℝ chi x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport ℝ fun hx' => hx (hchi_tsupport hx')
  have huO := (ae_restrict_iff' Omega.isOpen.measurableSet).1 hu
  have hu'O := (ae_restrict_iff' Omega.isOpen.measurableSet).1 hu'
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨‹CompleteSpace F›,
    (integrable_indicator_of_isCompact hK hKO h.locallyIntegrableOn hu).locallyIntegrable
      |>.locallyIntegrableOn _,
    (integrable_indicator_of_isCompact hK hKO h.locallyIntegrableOn_deriv hu').locallyIntegrable
      |>.locallyIntegrableOn _, fun phi => ?_⟩
  -- `χ φ` is a test function on `Ω`
  obtain ⟨Phi, hPhi⟩ : ∃ Phi : 𝓓(Omega, ℝ), (Phi : E → ℝ) = chi * (phi : E → ℝ) :=
    ⟨⟨chi * (phi : E → ℝ), hchi.mul phi.contDiff, hchi_cpt.mul_right,
      tsupport_mul_subset_left.trans hchi_tsupport⟩, rfl⟩
  -- the classical product rule for the two smooth factors
  have hline : ∀ x, lineDeriv ℝ (Phi : E → ℝ) x v
      = chi x * lineDeriv ℝ (phi : E → ℝ) x v + fderiv ℝ chi x v * (phi : E → ℝ) x := by
    intro x
    have hdchi : DifferentiableAt ℝ chi x := (hchi.differentiable (by simp)) x
    have hdphi : DifferentiableAt ℝ (phi : E → ℝ) x := (phi.contDiff.differentiable (by simp)) x
    rw [hPhi, (hdchi.mul hdphi).lineDeriv_eq_fderiv, hdphi.lineDeriv_eq_fderiv,
      fderiv_mul hdchi hdphi]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hleft : ∫ x, lineDeriv ℝ (phi : E → ℝ) x v • (Omega : Set E).indicator u x ∂mu
      = ∫ x, lineDeriv ℝ (Phi : E → ℝ) x v • u x ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [huO] with x hx
    rw [hline x]
    by_cases hxO : x ∈ (Omega : Set E)
    · by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxO, hchi_one x hxK, hchi_fderiv_K x hxK]
        simp
      · rw [indicator_of_mem hxO, hx hxO hxK]
        simp
    · rw [indicator_of_notMem hxO, hchi_zero x hxO, hchi_fderiv_zero x hxO]
      simp
  have hright : ∫ x, (phi : E → ℝ) x • (Omega : Set E).indicator u' x ∂mu
      = ∫ x, (Phi : E → ℝ) x • u' x ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [hu'O] with x hx
    rw [hPhi]
    simp only [Pi.mul_apply]
    by_cases hxO : x ∈ (Omega : Set E)
    · by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxO, hchi_one x hxK]
        simp
      · rw [indicator_of_mem hxO, hx hxO hxK]
        simp
    · rw [indicator_of_notMem hxO, hchi_zero x hxO]
      simp
  rw [hleft, hright]
  exact h.integral_lineDeriv_smul_eq_neg_integral_smul Phi

/-- **Extension by zero of a compactly supported weak Fréchet derivative.**  The Fréchet form of
`TauCeti.HasWeakLineDerivOn.indicator_of_isCompact`: a weakly differentiable function whose jet
vanishes almost everywhere outside a compact subset of `Ω` extends by zero to a weakly
differentiable function on the whole space. -/
theorem HasWeakFDerivOn.indicator_of_isCompact {U : E → E →L[ℝ] F}
    (h : HasWeakFDerivOn mu Omega u U) (hK : IsCompact K) (hKO : K ⊆ Omega)
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → u x = 0)
    (hU : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → U x = 0) :
    HasWeakFDerivOn mu ⊤ ((Omega : Set E).indicator u) ((Omega : Set E).indicator U) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  have hUv : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → U x v = 0 := by
    filter_upwards [hU] with x hx hxK
    rw [hx hxK]
    rfl
  refine ((h.hasWeakLineDerivOn v).indicator_of_isCompact hK hKO hu hUv).congr_ae_deriv
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hxO : x ∈ (Omega : Set E)
  · simp [indicator_of_mem hxO]
  · simp [indicator_of_notMem hxO]

end TauCeti
