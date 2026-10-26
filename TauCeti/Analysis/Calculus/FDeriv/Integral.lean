/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Integrating derivatives with countably many exceptional points

A continuous, compactly supported map whose derivative exists outside a countable set has
zero integral of each directional derivative, provided that derivative is integrable. The
candidate derivative may take arbitrary values at the exceptional points. This permits
integration by parts across isolated singularities without assuming differentiability there.

The proof uses Mathlib's
`MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'` on a box containing the
support, followed by the uniqueness of Haar measure and a linear change of coordinates.
-/

public section

open MeasureTheory Set
open MeasureTheory.Measure (isAddLeftInvariant_eq_smul)

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The integral of a directional derivative of a continuous compactly supported map is zero,
even if the derivative fails to exist on a countable set. Only the derivative in the chosen
direction must be integrable. -/
theorem integral_apply_eq_zero_of_hasFDerivAt_off_countable
    {f : E → F} {D : E → E →L[ℝ] F} {s : Set E} (hs : s.Countable)
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hd : ∀ x ∉ s, HasFDerivAt f (D x) x) (v : E)
    (hD : Integrable (fun x ↦ D x v) μ) : (∫ x, D x v ∂μ) = 0 := by
  by_cases hv : v = 0
  · simp [hv]
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := Module.finrank ℝ E - 1
  let X := Fin (n + 1) → ℝ
  have hdim : Module.finrank ℝ X = Module.finrank ℝ E := by
    simpa [X, n] using Nat.sub_add_cancel (Module.finrank_pos (R := ℝ) (M := E))
  let e : E ≃L[ℝ] X := (ContinuousLinearEquiv.ofFinrankEq hdim).symm
  let g : X → F := f ∘ e.symm
  let G : X → X →L[ℝ] F := fun x ↦ (D (e.symm x)).comp e.symm.toContinuousLinearMap
  let w : X := e v
  have hg : Continuous g := hf.comp e.symm.continuous
  have hgc : HasCompactSupport g := hfc.comp_homeomorph e.symm.toHomeomorph
  have hgd : ∀ x ∉ e.symm ⁻¹' s, HasFDerivAt g (G x) x := fun x hx ↦
    (hd _ hx).comp x e.symm.hasFDerivAt
  let ν := Measure.map e μ
  have he : MeasurableEmbedding (e : E → X) := e.toHomeomorph.measurableEmbedding
  have hGν : Integrable (fun x ↦ G x w) ν := by
    dsimp only [ν]
    rw [he.integrable_map_iff]
    simpa [G, w, Function.comp_def] using hD
  have hGvol : Integrable (fun x ↦ G x w) volume := by
    rw [isAddLeftInvariant_eq_smul (volume : Measure X) ν]
    exact hGν.smul_measure_nnreal
  -- In coordinates the derivative in direction `w` is the divergence of `w • g`.
  -- A box strictly containing the support has zero flux on every face.
  have hzero : (∫ x, G x w) = 0 := by
    obtain ⟨R, hR, hbound⟩ := hgc.isBounded.exists_pos_norm_lt
    let a : X := fun _ ↦ -R
    let b : X := fun _ ↦ R
    have hab : a ≤ b := fun _ ↦ neg_le_self hR.le
    have hout {x : X} (hx : x ∉ Icc a b) : x ∉ tsupport g := by
      intro hxs
      apply hx
      have hn := hbound x hxs
      exact ⟨fun i ↦ (abs_lt.mp ((norm_le_pi_norm x i).trans_lt hn)).1.le,
        fun i ↦ (abs_lt.mp ((norm_le_pi_norm x i).trans_lt hn)).2.le⟩
    have hface (i : Fin (n + 1)) (t : ℝ) (ht : |t| = R) (y : Fin n → ℝ) :
        g (i.insertNth t y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hx
      have hn := (norm_le_pi_norm (i.insertNth (α := fun _ ↦ ℝ) t y) i).trans_lt
        (hbound _ hx)
      simp [ht] at hn
    have hsum (x : X) : (∑ i : Fin (n + 1), w i • G x (Pi.single i 1)) = G x w := by
      simp_rw [← map_smul]
      rw [← map_sum, ← pi_eq_sum_univ' w]
    have hdiv := integral_divergence_of_hasFDerivAt_off_countable' a b hab
      (fun i x ↦ w i • g x) (fun i x ↦ w i • G x) (e.symm ⁻¹' s)
      (hs.preimage e.symm.injective) (fun i ↦ (hg.const_smul (w i)).continuousOn)
      (fun x hx i ↦ (hgd x hx.2).const_smul (w i))
      (by simpa only [smul_apply, hsum] using hGvol.integrableOn)
    have hGoutside : ∀ᵐ x, x ∉ Icc a b → G x w = 0 := by
      have hae : ∀ᵐ x ∂(volume : Measure X), x ∉ e.symm ⁻¹' s := by
        simpa using (measure_eq_zero_iff_ae_notMem.mp
          ((hs.preimage e.symm.injective).measure_zero volume))
      filter_upwards [hae] with x hx hxbox
      have hder := (hgd x hx).fderiv
      rw [← hder, fderiv_of_notMem_tsupport ℝ (hout hxbox), zero_apply]
    rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hGoutside]
    simpa only [smul_apply, hsum, a, b, hface _ R (abs_of_pos hR),
      hface _ (-R) (by rw [abs_neg, abs_of_pos hR]), smul_zero, integral_zero,
      sub_self, Finset.sum_const_zero] using hdiv
  -- Haar uniqueness transfers the zero integral back to the caller's measure.
  have hzeroν : (∫ x, G x w ∂ν) = 0 := by
    rw [isAddLeftInvariant_eq_smul ν (volume : Measure X), integral_smul_nnreal_measure]
    simp [hzero]
  dsimp only [ν] at hzeroν
  rw [he.integral_map] at hzeroν
  simpa [G, w] using hzeroν

end TauCeti
