/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Reflection
public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Complex.CauchyRiemann.NormalDerivative
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Regularity up to a real boundary for `\bar∂`

Let `Ω ⊆ ℂ` be an open set and `F` a finite-dimensional complex space whose real structure is its
`star` operation, for instance `ℂⁿ` with coordinatewise conjugation. This file proves that a weak
solution of `\bar∂ξ = η` on the closed upper part `Ω ∩ {0 ≤ im}`, real on the real axis in the weak
sense of `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn`, is as regular up to the real axis as
the interior theory predicts: for `1 < p < ∞` and every `k`, if `ξ` is locally `Lᵖ` and `η` lies
in `W^{k,p}_loc` up to the axis, then `ξ` lies in `W^{k+1,p}_loc` up to the axis
(`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.memWkpLoc_succ`).

This is the totally real boundary regularity of McDuff–Salamon (Lemma B.4.6 and Proposition B.4.9)
for the standard structure `J = i` with no zeroth-order term, and the induction follows their
route.

* **Order one.** Away from the axis this is interior regularity. Near a point of the axis, on the
  conjugation-invariant open set `Ω ∩ conj Ω`, the Schwarz reflection
  `TauCeti.starSchwarzReflection ξ`, equal to `ξ` above the axis and to `star (ξ (conj z))` below
  it, solves `\bar∂ (Rξ) = Rη`
  (`HasWeakConjWirtingerDerivRealBoundaryOn.hasWeakConjWirtingerDerivOn_starSchwarzReflection`).
  Since `Rη` is locally `Lᵖ`, interior regularity puts `Rξ` in `W^{1,p}_loc`, and `Rξ` agrees with
  `ξ` above the axis.
* **Tangential derivatives.** Differentiating along the real axis preserves the boundary
  condition: the derivative `∂ₛξ` of a solution solves `\bar∂ (∂ₛξ) = ∂ₛη` with real boundary
  values (`TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.weakLineDeriv_one`). Indeed `∂ₛ` maps
  test functions real on the axis to test functions real on the axis, and integration by parts in
  the tangential direction produces no boundary term
  (`TauCeti.HasWeakLineDerivOn.setIntegral_fderiv_smul_eq_neg`). Reflection cannot replace this
  step above order one, since the reflection of `η` is in general not in `W^{1,p}` across the
  axis.
* **Normal derivatives.** The equation `∂ₛξ + i ∂ₜξ = 2η` gives the normal derivative
  `∂ₜξ = i (∂ₛξ - 2η)`, which is as regular as `∂ₛξ` and `η`
  (`TauCeti.memWkpLoc_succ_of_ae_cauchyRiemann`).

## Main results

* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.weakLineDeriv_one`: a weak tangential
  derivative of a solution solves the differentiated equation, with real boundary values.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.memWkpLoc_one`: `W^{1,p}` regularity up to the
  real axis.
* `TauCeti.HasWeakConjWirtingerDerivRealBoundaryOn.memWkpLoc_succ`: `W^{k+1,p}` regularity up to
  the real axis, for every `k`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Appendix B.4, Lemma B.4.6 and Proposition B.4.9.
-/

public section

open Complex MeasureTheory TopologicalSpace Set Filter ContinuousLinearMap
open scoped ContDiff Distributions ComplexStarModule LineDeriv ComplexConjugate

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {Ω : Opens ℂ}

/-! ### Complex test functions on the closed upper half-plane -/

/-- Tangential integration by parts up to the real axis, against complex test functions, in the
form used by the weak real-boundary equation. -/
private theorem setIntegral_lineDerivOp_one_smul_eq_neg {g g' : ℂ → F}
    (hgW : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g g' 1)
    (hg : LocallyIntegrableOn g ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hg' : LocallyIntegrableOn g' ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (χ : 𝓓(Ω, ℂ)) :
    ∫ z in {z : ℂ | 0 ≤ z.im}, (∂_{(1 : ℂ)} χ : 𝓓(Ω, ℂ)) z • g z =
      -∫ z in {z : ℂ | 0 ≤ z.im}, χ z • g' z := by
  have hU := Ω.isOpen.isLocallyClosed_inter_setOfPred_le_im 0
  have e := hgW.setIntegral_fderiv_smul_eq_neg_of_complex
    ((memLpLoc_one_iff_locallyIntegrableOn hU).2 hg)
    ((memLpLoc_one_iff_locallyIntegrableOn hU).2 hg') χ.contDiff χ.hasCompactSupport
    (fun z hz ↦ χ.tsupport_subset hz.1) (Or.inl (by simp))
  simp only [TestFunction.lineDerivOp_apply_eq_fderiv]
  rwa [← setIntegral_congr_set (Complex.setOf_le_im_ae_eq 0),
    ← setIntegral_congr_set (Complex.setOf_le_im_ae_eq 0)] at e

variable [StarAddMonoid F] [StarModule ℂ F] {ξ η : ℂ → F}

/-! ### Tangential derivatives -/

/-- **Tangential derivatives of solutions with real boundary values.** If `ξ` solves
`\bar∂ξ = η` on `Ω ∩ {0 ≤ im}` with real boundary values, and `ξ'` and `η'` are weak derivatives
of `ξ` and `η` along the real axis on `Ω ∩ {0 < im}`, locally integrable up to the axis, then
`ξ'` solves `\bar∂ξ' = η'` with real boundary values. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.weakLineDeriv_one {ξ' η' : ℂ → F}
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η)
    (hξ : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) ξ ξ' 1)
    (hη : HasWeakLineDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) η η' 1)
    (hξ' : LocallyIntegrableOn ξ' ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hη' : LocallyIntegrableOn η' ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) :
    HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ' η' := by
  obtain ⟨hF, hξl, hηl, hw⟩ := hasWeakConjWirtingerDerivRealBoundaryOn_iff.1 h
  refine hasWeakConjWirtingerDerivRealBoundaryOn_iff.2 ⟨hF, hξ', hη', fun χ hχ ↦ ?_⟩
  -- The equation for `ξ`, tested against `∂ₛχ`, which is real on the axis.
  have hh := hw (∂_{(1 : ℂ)} χ) (by simpa using χ.im_lineDerivOp_ofReal_apply_ofReal hχ 1)
  have e₁ := setIntegral_lineDerivOp_one_smul_eq_neg hξ hξl hξ' (∂_{(1 : ℂ)} χ)
  have eI := setIntegral_lineDerivOp_one_smul_eq_neg hξ hξl hξ' (∂_{(I : ℂ)} χ)
  have eη := setIntegral_lineDerivOp_one_smul_eq_neg hη hηl hη' χ
  have hsplit {f : ℂ → F} (hf : LocallyIntegrableOn f ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
      (a b : 𝓓(Ω, ℂ)) :
      ∫ z in {z : ℂ | 0 ≤ z.im}, (a z + I * b z) • f z =
        (∫ z in {z : ℂ | 0 ≤ z.im}, a z • f z) + I • ∫ z in {z : ℂ | 0 ≤ z.im}, b z • f z := by
    have hf' := hf.restrict_of_inter Ω.isOpen (isClosed_setOfPred_le_im 0)
    have hc (c : 𝓓(Ω, ℂ)) :
        Integrable (fun z ↦ c z • f z) (volume.restrict {z : ℂ | 0 ≤ z.im}) := by
      simpa using c.integrable_bilin (lsmul ℂ ℂ) hf'
    have hb : Integrable (fun z ↦ I • (b z • f z)) (volume.restrict {z : ℂ | 0 ≤ z.im}) :=
      (hc b).smul I
    simp_rw [add_smul, mul_smul]
    rw [integral_add (hc a) hb, integral_smul]
  -- Write both pairings through the test functions `∂ₛχ` and `∂ₜχ`, using `∂ₜ∂ₛχ = ∂ₛ∂ₜχ`.
  have hl : (fun z ↦ (lineDeriv ℝ (χ : ℂ → ℂ) z 1 + I * lineDeriv ℝ (χ : ℂ → ℂ) z I) • ξ' z) =
      fun z ↦ ((∂_{(1 : ℂ)} χ : 𝓓(Ω, ℂ)) z + I * (∂_{(I : ℂ)} χ : 𝓓(Ω, ℂ)) z) • ξ' z := by
    simp only [TestFunction.lineDerivOp_apply]
  have hr : (fun z ↦ (lineDeriv ℝ ⇑(∂_{(1 : ℂ)} χ : 𝓓(Ω, ℂ)) z 1 +
      I * lineDeriv ℝ ⇑(∂_{(1 : ℂ)} χ : 𝓓(Ω, ℂ)) z I) • ξ z) =
      fun z ↦ ((∂_{(1 : ℂ)} (∂_{(1 : ℂ)} χ) : 𝓓(Ω, ℂ)) z +
        I * (∂_{(1 : ℂ)} (∂_{(I : ℂ)} χ) : 𝓓(Ω, ℂ)) z) • ξ z := by
    funext z
    rw [TestFunction.lineDeriv_lineDerivOp_comm χ (1 : ℂ) I z, ← TestFunction.lineDerivOp_apply,
      ← TestFunction.lineDerivOp_apply]
  rw [hr, hsplit hξl, eη, e₁, eI] at hh
  rw [hl, hsplit hξ']
  simpa only [smul_neg, ← neg_add, map_neg, neg_neg] using congrArg Neg.neg hh

/-! ### Regularity -/

variable [FiniteDimensional ℂ F] {p : ENNReal}

/-- `W^{1,p}` regularity up to the real axis on a conjugation-invariant open set, by reflection. -/
private theorem memWkpLoc_one_of_mapsTo (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) (hξ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ)
    (hη : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 ξ := by
  have : ContinuousStar F :=
    ⟨(starLinearEquiv ℝ (A := F)).toLinearMap.continuous_of_finiteDimensional⟩
  exact ((h.hasWeakConjWirtingerDerivOn_starSchwarzReflection hΩ).memWkpLoc_one hp hp_top
    (hξ.starSchwarzReflection hΩ) (hη.starSchwarzReflection hΩ)).congr_mono
    (fun _ hz ↦ (starSchwarzReflection_of_im_nonneg hz.2).symm) inter_subset_left

/-- **`W^{1,p}` regularity up to a real boundary.** For `1 < p < ∞`, a locally `Lᵖ` solution of
`\bar∂ξ = η` on `Ω ∩ {0 ≤ im}` with real boundary values and locally `Lᵖ` right-hand side lies in
`W^{1,p}_loc` up to the real axis. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.memWkpLoc_one (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hξ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ)
    (hη : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) η)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 ξ := by
  have := FiniteDimensional.completeSpace ℂ F
  refine memWkpLoc_iff_locally.2 fun x hx ↦ ?_
  have hx0 : 0 ≤ x.im := by simpa only [mem_ofPred_eq] using hx.2
  rcases hx0.lt_or_eq with hpos | hzero
  · -- Above the axis, interior regularity applies on `Ω ∩ {0 < im}`.
    have hxO : x ∈ Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
      rw [← SetLike.mem_coe, Opens.coe_interior, interior_inter_setOf_im_nonneg Ω.isOpen]
      exact ⟨hx.1, hpos⟩
    refine ⟨_, mem_nhdsWithin_of_mem_nhds ((Opens.interior _).isOpen.mem_nhds hxO), ?_⟩
    exact h.hasWeakConjWirtingerDerivOn_interior.memWkpLoc_one hp hp_top
      (hξ.mono_set interior_subset) (hη.mono_set interior_subset)
  · -- On the axis, reflect on the conjugation-invariant open set `Ω ∩ conj Ω`.
    let W : Opens ℂ := Ω ⊓ ⟨starRingEnd ℂ ⁻¹' Ω, Ω.isOpen.preimage Complex.continuous_conj⟩
    have hWc : (W : Set ℂ) = (Ω : Set ℂ) ∩ starRingEnd ℂ ⁻¹' Ω := by
      simp only [W, Opens.coe_inf, Opens.coe_mk]
    have hW : MapsTo (starRingEnd ℂ) W W := fun z hz ↦ by
      rw [hWc, mem_inter_iff, mem_preimage] at hz ⊢
      exact ⟨hz.2, by simpa using hz.1⟩
    have hxW : x ∈ (W : Set ℂ) := by
      rw [hWc, mem_inter_iff, mem_preimage, Complex.conj_eq_iff_im.2 hzero.symm]
      exact ⟨hx.1, hx.1⟩
    have hsub : (W : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
      inter_subset_inter_left _ (hWc.subset.trans inter_subset_left)
    exact ⟨(W : Set ℂ) ∩ {z | 0 ≤ z.im},
      mem_nhdsWithin.2 ⟨W, W.isOpen, hxW, inter_subset_inter_right _ inter_subset_right⟩,
      memWkpLoc_one_of_mapsTo hp hp_top hW (hξ.mono_set hsub) (hη.mono_set hsub)
        (h.mono inf_le_left)⟩

/-- **`W^{k+1,p}` regularity up to a real boundary.** For `1 < p < ∞` and every `k`, a locally
`Lᵖ` solution of `\bar∂ξ = η` on `Ω ∩ {0 ≤ im}` with real boundary values and right-hand side in
`W^{k,p}_loc` up to the real axis lies in `W^{k+1,p}_loc` up to the real axis. -/
theorem HasWeakConjWirtingerDerivRealBoundaryOn.memWkpLoc_succ (hp : 1 < p) (hp_top : p ≠ ⊤)
    {k : ℕ} (hξ : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ)
    (hη : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k η)
    (h : HasWeakConjWirtingerDerivRealBoundaryOn Ω ξ η) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) ξ := by
  have := FiniteDimensional.completeSpace ℂ F
  have hp1 : 1 ≤ p := hp.le
  have hU := Ω.isOpen.isLocallyClosed_inter_setOfPred_le_im 0
  induction k generalizing ξ η with
  | zero => exact h.memWkpLoc_one hp hp_top hξ (memWkpLoc_zero_iff.1 hη)
  | succ k ih =>
    -- By induction `ξ ∈ W^{k+1,p}`; let `D` be its weak derivative.
    have hξk := ih hξ hη.of_succ h
    obtain ⟨D, hD, hDk⟩ := hξk.exists_weakFDeriv
    obtain ⟨Dη, hDη, hDηk⟩ := hη.exists_weakFDeriv
    -- The tangential derivative `∂ₛξ = D · 1` solves the differentiated problem, so by induction
    -- it lies in `W^{k+1,p}`.
    have hD1 : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) fun z ↦ D z 1 := by
      simpa using hDk.memLpLoc.clm_comp (apply ℝ F (1 : ℂ))
    have hDη1 : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k fun z ↦ Dη z 1 := by
      simpa using hDηk.clm_comp (apply ℝ F (1 : ℂ))
    have ht := h.weakLineDeriv_one (hD.hasWeakLineDerivOn 1) (hDη.hasWeakLineDerivOn 1)
      (hD1.locallyIntegrableOn hp1 hU) (hDη1.memLpLoc.locallyIntegrableOn hp1 hU)
    have hD1k := ih hD1 hDη1 ht
    -- The equation `∂ₛξ + i ∂ₜξ = 2η` recovers the normal derivative.
    have hae := h.hasWeakConjWirtingerDerivOn_interior.ae_eq hD.hasWeakConjWirtingerDerivOn
    let J : F →L[ℝ] F := (I • ContinuousLinearMap.id ℂ F).restrictScalars ℝ
    have hJ (v : F) : J v = I • v := by simp [J]
    refine memWkpLoc_succ_of_ae_cauchyRiemann (Ω := Ω) (n := ⊤) (J := fun _ ↦ J) (S := 0)
      (η := (2 : ℝ) • η) contDiffOn_const contDiffOn_const le_top inter_subset_left
      (fun _ _ ↦ ?_) hξk (hη.const_smul 2) hD hD1k ?_
    · ext v
      simp [hJ, smul_smul]
    · rw [Opens.coe_interior] at hae
      filter_upwards [hae] with z hz
      simp only [hJ, Pi.zero_apply, zero_apply, add_zero, Pi.smul_apply]
      rw [hz, ← Complex.coe_smul, smul_smul]
      norm_num

end TauCeti
