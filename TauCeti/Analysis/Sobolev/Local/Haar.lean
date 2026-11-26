/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.MeasureTheory.Function.MemLpLoc.Haar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Sobolev.WeakDeriv.Haar
import TauCeti.Analysis.Sobolev.WeakDeriv.Translation

/-!
# Haar-measure independence and linear/affine invariance of local Sobolev classes

On a locally compact second-countable real normed space `E`, any two additive Haar measures differ
by a positive finite constant (`MeasureTheory.Measure.isAddLeftInvariant_eq_smul`). Because scaling
the ambient measure by a positive finite scalar preserves and reflects local `Lᵖ` membership
(`TauCeti.memLpLoc_smul_measure_iff`, re-exported from
`TauCeti.MeasureTheory.Function.MemLpLoc.Haar`) as well as weak differentiability
(`TauCeti.hasWeakFDerivOn_smul_measure_iff`), `TauCeti.MemWkpLoc` is independent of the choice of
additive Haar measure (`TauCeti.memWkpLoc_iff_of_isAddHaarMeasure`,
`TauCeti.memWkpLoc_congr_measureSpace`).

Consequently, any continuous linear equivalence `e : E ≃L[ℝ] E₁` between finite-dimensional real
normed spaces carrying arbitrary Borel additive Haar measures preserves and reflects `MemWkpLoc` at
every order (`TauCeti.MemWkpLoc.comp_continuousLinearEquiv`,
`ContinuousLinearEquiv.memWkpLoc_comp_right_iff`). Combined with translation invariance
(`TauCeti.MemWkpLoc.comp_add_right`, `TauCeti.memWkpLoc_comp_add_right_iff`), this yields affine
invariance (`TauCeti.MemWkpLoc.comp_continuousLinearEquiv_add`) across arbitrary
finite-dimensional real normed spaces, independent of inner products or canonical volume
normalizations.

## Main declarations

* `TauCeti.memWkpLoc_smul_measure_iff`: invariance under positive finite scaling of the ambient
  measure.
* `TauCeti.memWkpLoc_iff_of_isAddHaarMeasure`, `TauCeti.memWkpLoc_congr_measureSpace`:
  independence of the choice of additive Haar measure and `MeasureSpace` instance.
* `TauCeti.MemWkpLoc.comp_add_right`, `TauCeti.memWkpLoc_comp_add_right_iff`: translation
  invariance.
* `TauCeti.MemWkpLoc.comp_continuousLinearEquiv`,
  `ContinuousLinearEquiv.memWkpLoc_comp_right_iff`: linear invariance of local Sobolev classes of
  every order.
* `TauCeti.MemWkpLoc.comp_continuousLinearEquiv_add`: affine invariance of local Sobolev classes of
  every order.

## References

* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised
  edition, §4.2.
* W. Arendt and M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), §2.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

universe u u₁ v

section SmulMeasure

private theorem memWkpLoc_smul_measure_imp {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ ν : Measure E} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞) (hν : ν = c • μ)
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F}
    (hf : @MemWkpLoc E _ _ ⟨μ⟩ p U k F _ _ f) :
    @MemWkpLoc E _ _ ⟨ν⟩ p U k F _ _ f := by
  subst hν
  refine @memWkpLoc_ulift_induction E F _ _ ⟨c • μ⟩ _ _ p U k f
    (fun k F _ _ g => @MemWkpLoc E _ _ ⟨μ⟩ p U k F _ _ g)
    (fun _ _ _ _ hg => (memLpLoc_smul_measure_iff hc0 hc).2
      (@MemWkpLoc.memLpLoc _ _ _ _ ⟨μ⟩ _ _ _ _ _ _ hg))
    (fun _ _ _ _ _ hg => by
      obtain ⟨hp, D, hD, hk⟩ := (@memWkpLoc_succ_iff E _ _ _ ⟨μ⟩ _ _ _ _ _ _).1 hg
      exact ⟨(memLpLoc_smul_measure_iff hc0 hc).2 hp, D,
        (hasWeakFDerivOn_smul_measure_iff hc0 hc).2 hD, hk⟩)
    ((@ContinuousLinearEquiv.comp_memWkpLoc_iff E F (ULift.{u} F) _ _ ⟨μ⟩ _ _ _ _ p U k f
      ContinuousLinearEquiv.ulift.symm).2 hf)

/-- Scaling the ambient measure by a positive finite constant preserves and reflects local Sobolev
membership at every order. -/
theorem memWkpLoc_smul_measure_iff {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure E} {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ ⟨c • μ⟩ p U k F _ _ f ↔ @MemWkpLoc E _ _ ⟨μ⟩ p U k F _ _ f :=
  ⟨fun h => memWkpLoc_smul_measure_imp (ENNReal.inv_ne_zero.2 hc) (ENNReal.inv_ne_top.2 hc0)
      (by rw [smul_smul, ENNReal.inv_mul_cancel hc0 hc, one_smul]) h,
    fun h => memWkpLoc_smul_measure_imp hc0 hc rfl h⟩

end SmulMeasure

section HaarIndependence

/-- Local Sobolev membership at every order is independent of the choice of additive Haar
measure. -/
theorem memWkpLoc_iff_of_isAddHaarMeasure {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ ν : Measure E} [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ ⟨μ⟩ p U k F _ _ f ↔ @MemWkpLoc E _ _ ⟨ν⟩ p U k F _ _ f := by
  rw [Measure.isAddLeftInvariant_eq_smul μ ν, ← Measure.coe_nnreal_smul]
  exact memWkpLoc_smul_measure_iff
    (ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν).ne')
    ENNReal.coe_ne_top

/-- Local Sobolev membership at every order is independent of the `MeasureSpace` instance among
Borel additive Haar measures. -/
theorem memWkpLoc_congr_measureSpace {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m₁ m₂ : MeasureSpace E)
    [hB₁ : @BorelSpace E _ m₁.toMeasurableSpace]
    [hB₂ : @BorelSpace E _ m₂.toMeasurableSpace]
    [@Measure.IsAddHaarMeasure E _ _ m₁.toMeasurableSpace m₁.volume]
    [@Measure.IsAddHaarMeasure E _ _ m₂.toMeasurableSpace m₂.volume]
    {p : ENNReal} {U : Set E} {k : ℕ} {f : E → F} :
    @MemWkpLoc E _ _ m₁ p U k F _ _ f ↔ @MemWkpLoc E _ _ m₂ p U k F _ _ f := by
  rcases m₁ with @⟨m₁, μ⟩
  rcases m₂ with @⟨m₂, ν⟩
  have hm : m₁ = m₂ := hB₁.measurable_eq.trans hB₂.measurable_eq.symm
  subst hm
  exact memWkpLoc_iff_of_isAddHaarMeasure

end HaarIndependence

section Translation

/-- Right translation preserves local Sobolev membership at every order. -/
theorem MemWkpLoc.comp_add_right {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ENNReal} {U V : Set E} {k : ℕ} {u : E → F}
    (hu : MemWkpLoc p V k u) (b : E) (hmaps : MapsTo (· + b) U V) :
    MemWkpLoc p U k (fun x => u (x + b)) := by
  have hint : MapsTo (· + b) (interior U) (interior V) :=
    (Homeomorph.addRight b).isOpenMap.mapsTo_interior hmaps
  refine memWkpLoc_ulift_induction
    (fun k F _ _ g => ∃ w : E → F, g = (fun x => w (x + b)) ∧ MemWkpLoc p V k w)
    (fun _ _ _ _ ⟨_, hw, hmw⟩ => hw ▸ hmw.memLpLoc.comp_add_right b hmaps)
    (fun _ _ _ _ _ ⟨_, hw, hmw⟩ => by
      obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hmw
      exact ⟨hw ▸ hLp.comp_add_right b hmaps, fun x => D (x + b),
        hw ▸ hD.comp_add_right (V := Opens.interior U) (by simpa using hint), D, rfl, hk⟩)
    ⟨fun x => ContinuousLinearEquiv.ulift.symm (u x), rfl,
      ContinuousLinearEquiv.ulift.symm.comp_memWkpLoc_iff.2 hu⟩

/-- Right translation preserves and reflects local Sobolev membership at every order. -/
@[simp]
theorem memWkpLoc_comp_add_right_iff {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : ENNReal} {V : Set E} {k : ℕ} {u : E → F} (b : E) :
    MemWkpLoc p ((· + b) ⁻¹' V) k (fun x => u (x + b)) ↔ MemWkpLoc p V k u := by
  refine ⟨fun h => ?_, fun h => h.comp_add_right b (mapsTo_preimage (· + b) V)⟩
  simpa only [add_assoc, neg_add_cancel, add_zero] using
    h.comp_add_right (-b) fun x hx => by
      simpa [mem_preimage, add_assoc, neg_add_cancel, add_zero] using hx

end Translation

section LinearAndAffineWkp

variable {E : Type u} {E₁ : Type u₁} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [MeasureSpace E₁] [BorelSpace E₁] [(volume : Measure E₁).IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Linear invariance of local Sobolev classes.** Precomposition with any continuous linear
equivalence `e : E ≃L[ℝ] E₁` between finite-dimensional real normed spaces (carrying arbitrary
Borel additive Haar measures) preserves local Sobolev membership at every order. -/
theorem MemWkpLoc.comp_continuousLinearEquiv {p : ENNReal} {U : Set E}
    {V : Set E₁} {k : ℕ} {u : E₁ → F}
    (hu : MemWkpLoc p V k u) (e : E ≃L[ℝ] E₁) (hmaps : MapsTo e U V) :
    MemWkpLoc p U k (u ∘ e) := by
  have hint : MapsTo e (interior U) (interior V) :=
    e.toHomeomorph.isOpenMap.mapsTo_interior hmaps
  have hlift := nat_induction_clm_ulift ℝ E₁
    (fun k F _ _ => ∀ (u : E₁ → F), MemWkpLoc p V k u → MemWkpLoc p U k (u ∘ e))
    (fun F _ _ u hu =>
      memWkpLoc_zero_iff.2 ((memWkpLoc_zero_iff.1 hu).comp_continuousLinearEquiv e hmaps))
    (fun k F _ _ ih u hu => by
      obtain ⟨hLp, D, hD, hk⟩ := memWkpLoc_succ_iff.1 hu
      have := hD.completeSpace
      refine memWkpLoc_succ_iff.2
        ⟨hLp.comp_continuousLinearEquiv e hmaps,
          fun x => ((ContinuousLinearMap.compL ℝ E E₁ F).flip (e : E →L[ℝ] E₁)) (D (e x)),
          ?_, (ih D hk).clm_comp _⟩
      simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] using
        hD.comp_continuousLinearEquiv_of_isAddHaarMeasure (U := Opens.interior U) e
          (by simpa using hint))
    k F
  let eF : F ≃L[ℝ] ULift.{u₁} F := ContinuousLinearEquiv.ulift.symm
  exact eF.comp_memWkpLoc_iff.1 (hlift (fun x => eF (u x)) (eF.comp_memWkpLoc_iff.2 hu))

/-- Precomposition with a continuous linear equivalence preserves and reflects local Sobolev
membership at every order. -/
@[simp]
theorem _root_.ContinuousLinearEquiv.memWkpLoc_comp_right_iff {p : ENNReal}
    {V : Set E₁} {k : ℕ} {u : E₁ → F} (e : E ≃L[ℝ] E₁) :
    MemWkpLoc p (e ⁻¹' V) k (u ∘ e) ↔ MemWkpLoc p V k u := by
  refine ⟨fun h => ?_, fun h => h.comp_continuousLinearEquiv e (mapsTo_preimage e V)⟩
  simpa [Function.comp_def] using
    h.comp_continuousLinearEquiv e.symm fun y hy => by simpa [mem_preimage] using hy

/-- **Real-affine changes of variables preserve every order.** For `A : E ≃L[ℝ] E₁`,
`b : E₁`, and `x ↦ A x + b` mapping `U` into `V`, precomposition maps `MemWkpLoc p V k` into
`MemWkpLoc p U k` for arbitrary finite-dimensional real normed spaces carrying Borel additive
Haar measures. -/
theorem MemWkpLoc.comp_continuousLinearEquiv_add {p : ENNReal} {U : Set E}
    {V : Set E₁} {k : ℕ} {u : E₁ → F}
    (hu : MemWkpLoc p V k u) (A : E ≃L[ℝ] E₁) (b : E₁)
    (hmaps : MapsTo (fun x => A x + b) U V) :
    MemWkpLoc p U k (fun x => u (A x + b)) :=
  (hu.comp_add_right b (mapsTo_preimage (· + b) V)).comp_continuousLinearEquiv A hmaps

end LinearAndAffineWkp

end TauCeti
