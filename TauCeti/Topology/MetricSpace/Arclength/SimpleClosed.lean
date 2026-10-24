/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Arclength.Basic
public import TauCeti.Analysis.ConstantSpeed

/-!
# Arclength parametrization of simple closed curves

A continuous rectifiable curve with equal endpoint values and no repetitions on the half-open
parameter interval has an arclength parametrization with exactly the same simplicity property.
The parametrization is 1-Lipschitz, has unit variation speed, and traces the original image.
The repetition characterization includes the zero-length case: its length interval is a
singleton. Values outside the length interval are unspecified.

Together with the increasing arclength homeomorphism, this permits transporting geometric
constructions on simple closed curves to a Lipschitz parameter without losing their orientation
or introducing repeated points.

The construction uses Mathlib's `naturalParameterization` and its unit-speed theorem,
together with `HasConstantSpeedOnWith.lipschitzOnWith`; there is no additional curve or
length carrier.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows*, second edition, §1.1
  (arclength parametrization of metric curves).
-/

public section

open Set
open scoped ENNReal

namespace BoundedVariationOn

variable {X : Type*} [MetricSpace X] {γ : ℝ → X} {a b : ℝ}

/-- A rectifiable simple closed curve admits a unit-speed Lipschitz arclength parametrization.
The endpoints are preserved, the trace is unchanged, and equality of two values occurs exactly
at equal parameters or at the two endpoints. The statement also holds on a singleton interval.
-/
theorem exists_simple_closed_arclength_parametrization
    (hγ : BoundedVariationOn γ (Icc a b)) (hcont : ContinuousOn γ (Icc a b))
    (hinj : InjOn γ (Ico a b)) (hclosed : γ a = γ b) (hab : a ≤ b) :
    ∃ g : ℝ → X,
      LipschitzOnWith 1 g (Icc 0 (eVariationOn γ (Icc a b)).toReal) ∧
      HasUnitSpeedOn g (Icc 0 (eVariationOn γ (Icc a b)).toReal) ∧
      EqOn (g ∘ variationOnFromTo γ (Icc a b) a) γ (Icc a b) ∧
      g 0 = γ a ∧ g (eVariationOn γ (Icc a b)).toReal = γ b ∧
      g '' Icc 0 (eVariationOn γ (Icc a b)).toReal = γ '' Icc a b ∧
      ∀ u ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal,
        ∀ v ∈ Icc 0 (eVariationOn γ (Icc a b)).toReal,
          g u = g v ↔ u = v ∨
            (u = 0 ∧ v = (eVariationOn γ (Icc a b)).toReal) ∨
            (u = (eVariationOn γ (Icc a b)).toReal ∧ v = 0) := by
  let s := variationOnFromTo γ (Icc a b) a
  let L := (eVariationOn γ (Icc a b)).toReal
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  -- Cumulative variation carries both the closed and half-open parameter intervals onto
  -- their corresponding length intervals, even though the curve itself is closed.
  have hs : ContinuousOn s (Icc a b) := fun t ht ↦
    (hγ.continuousWithinAt_variationOnFromTo_iff ha ht).mpr (hcont t ht)
  have hm : StrictMonoOn s (Icc a b) :=
    hγ.locallyBoundedVariationOn.strictMonoOn_variationOnFromTo_of_injOn_Ioo ha
      (hinj.mono Ioo_subset_Ico_self)
  have hsa : s a = 0 := variationOnFromTo.self _ _ _
  have hsb : s b = L := by
    simp only [s, variationOnFromTo.eq_of_le _ _ hab, inter_self, L]
  have himage : s '' Icc a b = Icc 0 L := hγ.image_variationOnFromTo_Icc hcont hab
  have himageco : s '' Ico a b = Ico 0 L := by
    rw [hs.image_Ico_of_strictMonoOn hab hm, hsa, hsb]
  let g := naturalParameterization γ (Icc a b) a
  have hunit : HasUnitSpeedOn g (Icc 0 L) := by
    rw [← himage]
    exact has_unit_speed_naturalParameterization γ hγ.locallyBoundedVariationOn ha
  have hg : LipschitzOnWith 1 g (Icc 0 L) := hunit.lipschitzOnWith
  have hfactor : EqOn (g ∘ s) γ (Icc a b) := fun t ht ↦
    hγ.locallyBoundedVariationOn.naturalParameterization_variationOnFromTo ha ht
  have hg0 : g 0 = γ a := by
    rw [← hsa]
    exact hfactor ha
  have hgL : g L = γ b := by
    rw [← hsb]
    exact hfactor hb
  have hgclosed : g 0 = g L := hg0.trans (hclosed.trans hgL.symm)
  -- Transfer injectivity through the factorization on the half-open interval.
  have hginj : InjOn g (Ico 0 L) := by
    rw [← himageco]
    exact (hinj.congr (hfactor.mono Ico_subset_Icc_self).symm).image_of_comp
  have htrace : g '' Icc 0 L = γ '' Icc a b := by
    rw [← himage]
    exact hγ.locallyBoundedVariationOn.image_naturalParameterization ha
  refine ⟨g, hg, hunit, hfactor, hg0, hgL, htrace, ?_⟩
  -- The right endpoint is the only parameter omitted by half-open injectivity.
  -- Separating it out also handles a length interval consisting of one point.
  intro u hu v hv
  constructor
  · intro huv
    by_cases huL : u = L
    · by_cases hvL : v = L
      · exact Or.inl (huL.trans hvL.symm)
      · have hvco : v ∈ Ico 0 L := ⟨hv.1, lt_of_le_of_ne hv.2 hvL⟩
        have h0co : 0 ∈ Ico 0 L := ⟨le_rfl, hv.1.trans_lt hvco.2⟩
        have hv0 : v = 0 := hginj hvco h0co (by simpa [huL, hgclosed] using huv.symm)
        exact Or.inr (Or.inr ⟨huL, hv0⟩)
    · have huco : u ∈ Ico 0 L := ⟨hu.1, lt_of_le_of_ne hu.2 huL⟩
      by_cases hvL : v = L
      · have h0co : 0 ∈ Ico 0 L := ⟨le_rfl, hu.1.trans_lt huco.2⟩
        have hu0 : u = 0 := hginj huco h0co (by simpa [hvL, hgclosed] using huv)
        exact Or.inr (Or.inl ⟨hu0, hvL⟩)
      · exact Or.inl (hginj huco ⟨hv.1, lt_of_le_of_ne hv.2 hvL⟩ huv)
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact hgclosed
    · exact hgclosed.symm

end BoundedVariationOn
