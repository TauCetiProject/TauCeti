/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoxIntegral.IntervalIntegral
public import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The Henstock–Kurzweil fundamental theorem of calculus

In dimension one every box has distortion one, so Mathlib's `GP` integral agrees with the
Henstock–Kurzweil integral. Specializing the gauge divergence theorem gives the fundamental
theorem for continuous primitives differentiable off a countable exceptional set. The derivative
need not be Bochner integrable, and its values at the exceptions are arbitrary.

The finite-exception case applies in particular to piecewise differentiable parametrizations.
-/

public section

open scoped NNReal Topology
open MeasureTheory Set

namespace BoxIntegral

/-- Every nondegenerate one-dimensional box has distortion one. -/
@[simp]
theorem Box.distortion_fin_one (I : Box (Fin 1)) : I.distortion = 1 := by
  simp only [Box.distortion, Finset.univ_unique, Finset.sup_singleton]
  have hx : nndist (I.lower 0) (I.upper 0) ≠ 0 :=
    fun h ↦ I.lower_ne_upper 0 (eq_of_nndist_eq_zero h)
  simp only [nndist_pi_def, Finset.univ_unique, Finset.sup_singleton]
  exact div_self hx

/-- In dimension one the distortion restriction in the `GP` integral imposes no extra condition. -/
theorem hasIntegral_GP_iff_Henstock {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {I : Box (Fin 1)} {f : (Fin 1 → ℝ) → E}
    {vol : Fin 1 →ᵇᵃ E →L[ℝ] F} {y : F} :
    HasIntegral I IntegrationParams.GP f vol y ↔
      HasIntegral I IntegrationParams.Henstock f vol y := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono IntegrationParams.gp_le⟩
  refine hasIntegral_iff.2 fun ε hε ↦ ?_
  obtain ⟨r, _, hr⟩ := hasIntegral_iff.1 h ε hε
  refine ⟨fun _ ↦ r 1, fun _ ↦ IntegrationParams.rCond_of_bRiemann_eq_false _ rfl, ?_⟩
  intro c π hπ hπp
  apply hr 1 π _ hπp
  refine ⟨hπ.isSubordinate, hπ.isHenstock, ?_, ?_⟩
  · intro _
    exact (Prepartition.distortion_le_iff π.toPrepartition).2
      fun J _ ↦ (Box.distortion_fin_one J).le
  · intro _
    refine ⟨⊥, ?_, ?_⟩
    · rw [(TaggedPrepartition.isPartition_iff_iUnion_eq π).mp hπp]
      simp
    · simp

/-- Henstock–Kurzweil FTC for continuous Banach-valued primitives, with a countable exceptional
set. There is no integrability or boundedness requirement on the derivative; its values on the
exceptional set do not affect the integral. -/
theorem hasIntegral_Henstock_derivWithin_of_countable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b) {f f' : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b \ s, HasDerivWithinAt f (f' x) (Icc a b) x) :
    HasIntegral (intervalBox a b hab) IntegrationParams.Henstock
      (fun x ↦ f' (x 0)) BoxAdditiveMap.volume (f b - f a) := by
  apply hasIntegral_GP_iff_Henstock.mp
  let e : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hmap : MapsTo e (Box.Icc (intervalBox a b hab)) (Icc a b) := by
    intro x hx
    exact mem_Icc_intervalBox.mp hx
  have h := hasIntegral_GP_pderiv (intervalBox a b hab) (fun x ↦ f (x 0))
    (fun x ↦ (ContinuousLinearMap.toSpanSingleton ℝ (f' (x 0))).comp e)
    (e ⁻¹' (s ∩ Icc a b))
    ((hs.mono inter_subset_left).preimage
      (MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℝ)).injective)
    (fun x hx ↦ by
      -- Express coordinate evaluation as the linear map used in the chain rule below.
      change ContinuousWithinAt (f ∘ e) (Box.Icc (intervalBox a b hab)) x
      exact (hc (e x) hx.2).comp e.continuous.continuousWithinAt hmap)
    (fun x hx ↦
      (hd (x 0) ⟨hmap hx.1, fun hxs ↦ hx.2 ⟨hxs, hmap hx.1⟩⟩).hasFDerivWithinAt.comp x
        e.hasFDerivAt.hasFDerivWithinAt hmap) 0
  simpa [e, Fin.insertNth_apply_same, BoxIntegral.integral_const,
    BoxAdditiveMap.volume_apply] using h

/-- Henstock–Kurzweil FTC assuming differentiability only in the interior, outside a countable
exceptional set. No derivative is required at either endpoint. -/
theorem hasIntegral_Henstock_deriv_of_countable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b) {f f' : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b \ s, HasDerivAt f (f' x) x) :
    HasIntegral (intervalBox a b hab) IntegrationParams.Henstock
      (fun x ↦ f' (x 0)) BoxAdditiveMap.volume (f b - f a) := by
  apply hasIntegral_Henstock_derivWithin_of_countable hab
    (hs.union (Set.toFinite ({a, b} : Set ℝ)).countable) hc
  intro x hx
  have hxa : x ≠ a := fun h ↦ hx.2 (Or.inr (by simp [h]))
  have hxb : x ≠ b := fun h ↦ hx.2 (Or.inr (by simp [h]))
  exact (hd x ⟨⟨lt_of_le_of_ne hx.1.1 hxa.symm, lt_of_le_of_ne hx.1.2 hxb⟩,
    fun hxs ↦ hx.2 (Or.inl hxs)⟩).hasDerivWithinAt

end BoxIntegral
