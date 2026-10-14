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

The `GP` integral agrees with the Henstock–Kurzweil integral on one-dimensional boxes.
For a continuous Banach-valued function `f` with derivative `f'` outside a countable exceptional
set, the Henstock–Kurzweil integral of `f'` equals `f b - f a`. The derivative need not be
Bochner integrable, and its values at the exceptions are arbitrary.

The FTC is derived from Mathlib's `BoxIntegral.hasIntegral_GP_pderiv` using the GP–Henstock
equivalence in dimension one. Finite exceptional sets, such as break points of piecewise
differentiable parametrizations, are a special case of the countable hypothesis.
-/

public section

open scoped NNReal Topology
open MeasureTheory Set

open BoxIntegral

namespace TauCeti.BoxIntegral

/-- Every nondegenerate one-dimensional box has distortion one. -/
@[simp]
theorem _root_.BoxIntegral.Box.distortion_of_unique {ι : Type*} [Fintype ι] [Unique ι] (I : Box ι) :
    I.distortion = 1 := by
  simp only [Box.distortion, Finset.univ_unique, Finset.sup_singleton]
  have hx : nndist (I.lower default) (I.upper default) ≠ 0 :=
    fun h ↦ I.lower_ne_upper default (eq_of_nndist_eq_zero h)
  simp only [nndist_pi_def, Finset.univ_unique, Finset.sup_singleton]
  exact div_self hx

/-- On a finite unique-coordinate box the `GP` distortion restriction imposes no extra condition. -/
theorem hasIntegral_GP_iff_Henstock_of_unique {ι E F : Type*} [Fintype ι] [Unique ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {I : Box ι} {f : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F} {y : F} :
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
      fun J _ ↦ (Box.distortion_of_unique J).le
  · intro _
    refine ⟨⊥, ?_, ?_⟩
    · rw [(TaggedPrepartition.isPartition_iff_iUnion_eq π).mp hπp]
      simp
    · simp

/-- In dimension one the `GP` and Henstock integrals coincide. This is the interval-coordinate
specialization used by the Henstock FTC. -/
theorem hasIntegral_GP_iff_Henstock_fin_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {I : Box (Fin 1)} {f : (Fin 1 → ℝ) → E}
    {vol : Fin 1 →ᵇᵃ E →L[ℝ] F} {y : F} :
    HasIntegral I IntegrationParams.GP f vol y ↔
      HasIntegral I IntegrationParams.Henstock f vol y := hasIntegral_GP_iff_Henstock_of_unique

/-- Henstock–Kurzweil FTC for continuous Banach-valued primitives, with a countable exceptional
set. There is no integrability or boundedness requirement on the derivative; its values on the
exceptional set do not affect the integral. -/
theorem hasIntegral_Henstock_of_hasDerivWithinAt_off_countable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b) {f f' : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Icc a b \ s, HasDerivWithinAt f (f' x) (Icc a b) x) :
    HasIntegral (intervalBox a b hab) IntegrationParams.Henstock
      (fun x ↦ f' (x 0)) BoxAdditiveMap.volume (f b - f a) := by
  apply hasIntegral_GP_iff_Henstock_fin_one.mp
  have hmap : MapsTo (fun x : Fin 1 → ℝ ↦ x 0) (Box.Icc (intervalBox a b hab)) (Icc a b) := by
    intro x hx
    exact mem_Icc_intervalBox.mp hx
  have h := hasIntegral_GP_pderiv (intervalBox a b hab) (fun x ↦ f (x 0))
    (fun x ↦ (ContinuousLinearMap.toSpanSingleton ℝ (f' (x 0))).comp (ContinuousLinearMap.proj 0))
    ((fun x : Fin 1 → ℝ ↦ x 0) ⁻¹' (s ∩ Icc a b))
    ((hs.mono inter_subset_left).preimage
      (fun x y hxy ↦ funext (Fin.forall_fin_one.mpr hxy)))
    (fun x hx ↦ (hc (x 0) hx.2).comp (f := fun y : Fin 1 → ℝ ↦ y 0)
      (continuous_apply 0).continuousWithinAt hmap)
    (fun x hx ↦
      (hd (x 0) ⟨hmap hx.1, fun hxs ↦ hx.2 ⟨hxs, hmap hx.1⟩⟩).hasFDerivWithinAt.comp x
        (hasFDerivWithinAt_apply 0 x _) hmap) 0
  simpa [Fin.insertNth_apply_same, BoxIntegral.integral_const,
    BoxAdditiveMap.volume_apply] using h

/-- Henstock–Kurzweil FTC assuming differentiability only in the interior, outside a countable
exceptional set. No derivative is required at either endpoint. -/
theorem hasIntegral_Henstock_of_hasDerivAt_off_countable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b) {f f' : ℝ → E} {s : Set ℝ}
    (hs : s.Countable) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b \ s, HasDerivAt f (f' x) x) :
    HasIntegral (intervalBox a b hab) IntegrationParams.Henstock
      (fun x ↦ f' (x 0)) BoxAdditiveMap.volume (f b - f a) := by
  apply hasIntegral_Henstock_of_hasDerivWithinAt_off_countable hab
    (hs.union (Set.toFinite ({a, b} : Set ℝ)).countable) hc
  intro x hx
  have hxa : x ≠ a := fun h ↦ hx.2 (Or.inr (by simp [h]))
  have hxb : x ≠ b := fun h ↦ hx.2 (Or.inr (by simp [h]))
  exact (hd x ⟨⟨lt_of_le_of_ne hx.1.1 hxa.symm, lt_of_le_of_ne hx.1.2 hxb⟩,
    fun hxs ↦ hx.2 (Or.inl hxs)⟩).hasDerivWithinAt

end TauCeti.BoxIntegral
