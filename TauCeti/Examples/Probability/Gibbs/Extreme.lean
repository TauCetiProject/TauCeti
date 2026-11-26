/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.Probability.Gibbs.Specification
public import TauCeti.Probability.Gibbs.Extreme
public import TauCeti.MeasureTheory.Group.ErgodicExtreme
public import TauCeti.Algebra.Group.TypeTags.Countable
import TauCeti.Dynamics.Ergodic.Action.TimeMap
import TauCeti.Probability.Process.Tail.ProperAction

/-!
# Checks for the face property of invariant Gibbs measures

On the subshift `X₀` of the two constant configurations `zeroBar` and `oneBar` of `ℤ → Bool`,
with the identity specification `γ_Λ(· | ω) = δ_ω`
(`TauCeti.Examples.GibbsSpecification.idSpec`), the shift fixes both points of `X₀`, so every
probability measure on `X₀` is invariant and Gibbs: `𝒢_inv(γ) = 𝔓_inv(X₀)`
(`gibbsInvariant_idSpec`), and the face property of
`TauCeti.Specification.isExtreme_gibbsInvariant` holds trivially. The Dirac masses at `zeroBar`
and `oneBar` are ergodic, hence extreme in `𝒢_inv(γ)`; their midpoint gives the invariant event
`{oneBar}` measure `1/2`, so it is not ergodic and not extreme.

The hypothesis of the face property, that the translations of `ℤ` move every finite set off every
finite set, is `TauCeti.Probability.exists_forall_smul_notMem_self`.
-/

open MeasureTheory Set TauCeti.MeasureTheory
open scoped ENNReal

public noncomputable section

namespace TauCeti.Examples.GibbsExtreme

open TauCeti TauCeti.Examples.GibbsSpecification

/-- The shift fixes every point of `X₀`. -/
theorem smul_X₀ (g : Multiplicative ℤ) (ω : X₀) : g • ω = ω :=
  Subtype.ext (by rw [Subshift.coe_smul]; exact funext fun i => X₀_val_apply_eq ω _ i)

/-- Every measure on `X₀` is invariant under the shift. -/
instance smulInvariantMeasure_X₀ (μ : Measure X₀) :
    SMulInvariantMeasure (Multiplicative ℤ) X₀ μ :=
  ⟨fun g s _ => by simp only [smul_X₀, preimage_id']⟩

/-- **`𝒢_inv = 𝔓_inv` for the identity specification.** Every invariant probability measure on
`X₀` is Gibbs for the identity specification. -/
theorem gibbsInvariant_idSpec :
    idSpec.gibbsInvariant = invariantMeasuresOfMeasureUnivEq (Multiplicative ℤ) X₀ 1 := by
  ext μ
  exact ⟨fun h => (Specification.mem_gibbsInvariant_iff.1 h).1, fun h =>
    Specification.mem_gibbsInvariant_iff.2 ⟨h, isGibbs_idSpec μ⟩⟩

/-- The constant configuration `zeroBar`. -/
def zeroBar : X₀ := ⟨fun _ => false, (mem_X₀_iff _).2 fun _ _ => rfl⟩

/-- The constant configuration `oneBar`. -/
def oneBar : X₀ := ⟨fun _ => true, (mem_X₀_iff _).2 fun _ _ => rfl⟩

/-- The two constant configurations differ. -/
theorem zeroBar_ne_oneBar : zeroBar ≠ oneBar := fun h => by
  simpa [zeroBar, oneBar] using congrFun (congrArg Subtype.val h) 1

/-- The Dirac masses on `X₀` are ergodic. -/
theorem ergodicSMul_dirac (ω : X₀) : ErgodicSMul (Multiplicative ℤ) X₀ (Measure.dirac ω) where
  aeconst_of_forall_preimage_smul_ae_eq _ _ := by
    rw [ae_dirac_eq, Filter.eventuallyEmptyOrUniv_iff]
    simp only [Filter.eventually_pure]
    exact em _

/-- The Dirac masses at `zeroBar` and `oneBar` are extreme invariant Gibbs measures for the
identity specification. -/
theorem dirac_mem_extremePoints_gibbsInvariant (ω : X₀) :
    Measure.dirac ω ∈ extremePoints ℝ≥0∞ idSpec.gibbsInvariant := by
  have hmem : Measure.dirac ω ∈ idSpec.gibbsInvariant := by
    rw [gibbsInvariant_idSpec]
    exact mem_invariantMeasuresOfMeasureUnivEq_iff.2 ⟨inferInstance, by simp⟩
  exact (idSpec.mem_extremePoints_gibbsInvariant_iff_ergodicSMul
    Probability.exists_forall_smul_notMem_self hmem).2 (ergodicSMul_dirac ω)

/-- The midpoint of the Dirac masses at `zeroBar` and `oneBar`. -/
def diracMidpoint : Measure X₀ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac zeroBar + (2 : ℝ≥0∞)⁻¹ • Measure.dirac oneBar

/-- The invariant event `{oneBar}` has measure `1/2` under the midpoint. -/
theorem diracMidpoint_singleton_oneBar : diracMidpoint {oneBar} = 2⁻¹ := by
  simp [diracMidpoint, zeroBar_ne_oneBar]

/-- The midpoint is a probability measure. -/
theorem diracMidpoint_univ : diracMidpoint univ = 1 := by
  simp [diracMidpoint, ENNReal.inv_two_add_inv_two]

/-- The midpoint is an invariant Gibbs measure. -/
theorem diracMidpoint_mem_gibbsInvariant : diracMidpoint ∈ idSpec.gibbsInvariant := by
  rw [gibbsInvariant_idSpec]
  exact mem_invariantMeasuresOfMeasureUnivEq_iff.2 ⟨inferInstance, diracMidpoint_univ⟩

/-- **The midpoint is not ergodic**: the invariant event `{oneBar}` has measure `1/2`. -/
theorem not_ergodicSMul_diracMidpoint : ¬ ErgodicSMul (Multiplicative ℤ) X₀ diracMidpoint :=
  not_ergodicSMul_of_forall_smul_eq smul_X₀ (measurableSet_singleton oneBar).nullMeasurableSet
    (by simp [diracMidpoint_singleton_oneBar])
    (by rw [measure_compl (measurableSet_singleton _) (by simp [diracMidpoint_singleton_oneBar]),
      diracMidpoint_univ, diracMidpoint_singleton_oneBar]; norm_num)

/-- The midpoint is not extreme among the invariant Gibbs measures. -/
theorem diracMidpoint_notMem_extremePoints_gibbsInvariant :
    diracMidpoint ∉ extremePoints ℝ≥0∞ idSpec.gibbsInvariant := fun h =>
  not_ergodicSMul_diracMidpoint ((idSpec.mem_extremePoints_gibbsInvariant_iff_ergodicSMul
    Probability.exists_forall_smul_notMem_self diracMidpoint_mem_gibbsInvariant).1 h)

end TauCeti.Examples.GibbsExtreme
