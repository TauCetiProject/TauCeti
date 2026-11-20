/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.WittVector.IntervalRing.Subinterval
public import TauCeti.RingTheory.WittVector.PadicInt

/-!
# Integral scalars on the Fargues–Fontaine interval rings

The Witt-vector map from `ℤ_p` induces continuous scalar maps to the completed interval
rings `B^I`. These maps are bounded into the chart plus rings `(B^I)°` and compatible with
restriction to a subinterval. The boundedness uses the two endpoint Gauss norms, not a
claim that the scalar map is isometric in the interval norm.

## References

* L. Fargues and P. Scholze, *Geometrization of the local Langlands correspondence*, §II.1.
-/

public section

open scoped NNReal

namespace TauCeti.WittVector

open _root_.WittVector Huber

variable {p : ℕ} [Fact p.Prime] {O K : Type*} [CommRing O] [CharP O p] [PerfectRing O p]
  [Field K] [Algebra O K] {v : Valuation K ℝ≥0} {ϖ : O}
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1)
  {ρ₁ ρ₂ : ℝ≥0} (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

/-- The integral p-adic scalar map to `B^I`, obtained by composing through the unlocalized
Witt ring. -/
noncomputable def padicIntToIntervalRing : ℤ_[p] →+* IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ :=
  (algebraMap (WittVector p O) _).comp (padicIntToWitt p O)

/-- On an integral scalar, the chart map is the image of its Witt-vector representative. -/
theorem padicIntToIntervalRing_apply (a : ℤ_[p]) :
    padicIntToIntervalRing hv hϖ hϖ' hρ₁ hρ₂ a =
      algebraMap (WittVector p O) _ (padicIntToWitt p O a) :=
  (rfl)

/-- The scalar map into the complete interval ring is continuous. -/
theorem continuous_padicIntToIntervalRing :
    Continuous (padicIntToIntervalRing (p := p) hv hϖ hϖ' hρ₁ hρ₂) := by
  let J : Ideal (WittVector p O) := Ideal.span {(p : WittVector p O), teichmuller p ϖ}
  let _ : TopologicalSpace (WittVector p O) := J.adicTopology
  have hJ : IsAdic J := rfl
  exact (continuous_algebraMap_intervalRing p hv hϖ hϖ' hρ₁ hρ₂ hJ).comp
    (continuous_padicIntToWitt hJ)

/-- Integral p-adic scalars land in the interval chart's plus ring. -/
theorem padicIntToIntervalRing_mem_powerBoundedSubring (a : ℤ_[p]) :
    padicIntToIntervalRing hv hϖ hϖ' hρ₁ hρ₂ a ∈ powerBoundedSubring _ := by
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one_intervalRing,
    padicIntToIntervalRing_apply, norm_algebraMap_intervalRing, max_le_iff]
  exact ⟨gaussValuation_le_one hv hρ₁.2 _, gaussValuation_le_one hv hρ₂.2 _⟩

variable {hv hϖ hϖ' hρ₁ hρ₂}

/-- The integral scalar maps commute with restriction to a subinterval. -/
@[simp]
theorem intervalRingRestrict_padicIntToIntervalRing {ρ₁' ρ₂' : ℝ≥0}
    {hρ₁' : ρ₁' ∈ Set.Ioo 0 1} {hρ₂' : ρ₂' ∈ Set.Ioo 0 1}
    (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂') (h₂ : ρ₂' ≤ ρ₂) (a : ℤ_[p]) :
    intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂' h₁ h₁₂ h₂
        (padicIntToIntervalRing hv hϖ hϖ' hρ₁ hρ₂ a) =
      padicIntToIntervalRing hv hϖ hϖ' hρ₁' hρ₂' a := by
  simp only [padicIntToIntervalRing_apply, AlgHom.commutes]

end TauCeti.WittVector
