/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Topology.Algebra.Module.Complement
public import TauCeti.Analysis.Sobolev.Cylinder.Density
public import TauCeti.Analysis.Sobolev.Cylinder.Gluing
import TauCeti.Analysis.Fredholm.Stabilization

/-!
# Stabilizing Fredholm operators on the cylinder by test sections

A Fredholm operator `D` with values in `L²(ℝ × S¹, W)` need not be onto. Its cokernel is
finite-dimensional, and adjoining a finite-dimensional space `S` of sections that complements the
range of `D` makes the stabilized operator `(ξ, σ) ↦ D ξ + σ` onto, without changing its kernel:
since `S` meets the range of `D` only in `0`, that kernel is `ker D × {0}`
(`ContinuousLinearMap.ker_coprod_of_disjoint_range`). This is how the linear gluing of
Cauchy–Riemann and Floer operators handles pieces with cokernel: the stabilized gluing theorem
`TauCeti.CylinderSobolev.exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff`
needs stabilizers whose sections vanish near the ends that are glued, and bounded linear right
inverses of the stabilized pieces.

This file constructs such stabilizers out of test sections, the `C²` sections of the cylinder that
vanish for `|s|` large (`TauCeti.CylinderSobolev.testSection`), whose `L²` classes are dense
(`TauCeti.CylinderSobolev.dense_testSectionLp`).

* **Bounded support.** A finite-dimensional space of classes of test sections has a common bound
  `T` with all its sections vanishing for `|s| > T`
  (`TauCeti.CylinderSobolev.exists_forall_ae_eq_zero_of_le_testSectionLp`), so beyond any
  `T' ≥ T` they vanish on either side (`TauCeti.CylinderSobolev.ae_subtypeL_eq_zero_of_lt`,
  `TauCeti.CylinderSobolev.ae_subtypeL_eq_zero_of_lt_neg`).
* **Stabilizers.** A Fredholm operator `D` from a Banach space into `L²` has a stabilizer `S` made
  of test sections, a topological complement of its range, hence finite-dimensional and isomorphic
  to the cokernel of `D`. The sections of `S` vanish for `|s|` large, and the stabilized operator
  has a bounded linear right inverse
  (`ContinuousLinearMap.IsFredholm.exists_le_testSectionLp_isTopCompl`, from the general
  `ContinuousLinearMap.IsFredholm.exists_le_isTopCompl_rightInverse_coprod_of_dense`).
* **Gluing Fredholm pieces.** For two first-order operators `D₁`, `D₂` on the cylinder with
  matching ends, Fredholm on `W^{1,2}`, such stabilizers `S₁` and `S₂` stabilize every glued
  operator `D_R` with a long neck, with right inverses of `D_R ⊕ j_R` bounded independently of `R`
  (`exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff_of_isFredholm`).
  No surjectivity of the pieces is assumed.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 3.1
  (stabilizing a Fredholm operator by a finite-dimensional space complementing its range) and
  Chapter 10 (linear gluing).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3.
-/

public section

noncomputable section

open Filter MeasureTheory Set Function
open scoped ENNReal Topology

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### Stabilizers made of test sections -/

/-- The `L²` sections vanishing almost everywhere on `|s| > T`. -/
private def vanishingLp (T : ℝ) : Submodule ℝ (Lp W 2 stripMeasure) where
  carrier := {η | ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0}
  zero_mem' := by
    rw [mem_ofPred_eq]
    filter_upwards [Lp.coeFn_zero W 2 stripMeasure] with z hz _ using hz
  add_mem' := by
    rintro η η' hη hη'
    rw [mem_ofPred_eq] at hη hη' ⊢
    filter_upwards [Lp.coeFn_add η η', hη, hη'] with z hz h h' hT
    exact hz.trans (by simp [h hT, h' hT])
  smul_mem' := by
    rintro c η hη
    rw [mem_ofPred_eq] at hη ⊢
    filter_upwards [Lp.coeFn_smul c η, hη] with z hz h hT
    exact hz.trans (by simp [h hT])

private theorem mem_vanishingLp_iff {T : ℝ} {η : Lp W 2 stripMeasure} :
    η ∈ vanishingLp T ↔ ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0 :=
  Iff.rfl

private theorem vanishingLp_mono {T T' : ℝ} (h : T ≤ T') :
    vanishingLp (W := W) T ≤ vanishingLp T' := fun _ hη ↦ by
  rw [mem_vanishingLp_iff] at hη ⊢
  filter_upwards [hη] with z hz hT using hz (h.trans_lt hT)

/-- **Bounded support of finitely many test sections.** The sections of a finite-dimensional
space of `L²` classes of test sections all vanish for `|s|` beyond a common bound `T`. -/
theorem exists_forall_ae_eq_zero_of_le_testSectionLp {S : Submodule ℝ (Lp W 2 stripMeasure)}
    (hS : S ≤ testSectionLp W) [FiniteDimensional ℝ S] :
    ∃ T : ℝ, ∀ η ∈ S, ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0 := by
  have key (η) (hη : η ∈ S) : ∃ T, η ∈ vanishingLp (W := W) T := by
    obtain ⟨ξ, hξ, hηξ⟩ := mem_testSectionLp_iff.1 (hS hη)
    obtain ⟨-, -, R, hR⟩ := mem_testSection_iff.1 hξ
    refine ⟨R, mem_vanishingLp_iff.2 ?_⟩
    filter_upwards [hηξ] with z hz hT using hz.trans (hR z.1 z.2 hT.le)
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S).2 inferInstance
  choose! T hT using fun η (hη : η ∈ t) ↦ key η (ht ▸ Submodule.subset_span hη)
  obtain ⟨M, hM⟩ := (t.image T).exists_le
  refine ⟨M, fun η hη ↦ mem_vanishingLp_iff.1 ?_⟩
  rw [← ht] at hη
  exact Submodule.span_le.2 (fun ν hν ↦
    vanishingLp_mono (hM _ (Finset.mem_image_of_mem T hν)) (hT ν hν)) hη

/-- Sections of `S` vanishing for `|s| > T` vanish for `s > T'` whenever `T ≤ T'`: as a stabilizer
`S.subtypeL` of the left piece of a gluing, they vanish beyond its glued end. -/
theorem ae_subtypeL_eq_zero_of_lt {S : Submodule ℝ (Lp W 2 stripMeasure)} {T T' : ℝ}
    (hT : ∀ η ∈ S, ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0) (hTT' : T ≤ T') (σ : S) :
    ∀ᵐ z ∂stripMeasure, T' < z.1 → S.subtypeL σ z = 0 := by
  filter_upwards [hT σ σ.property] with z hz h using
    hz (hTT'.trans_lt (h.trans_le (le_abs_self _)))

/-- Sections of `S` vanishing for `|s| > T` vanish for `s < -T'` whenever `T ≤ T'`: as a
stabilizer `S.subtypeL` of the right piece of a gluing, they vanish beyond its glued end. -/
theorem ae_subtypeL_eq_zero_of_lt_neg {S : Submodule ℝ (Lp W 2 stripMeasure)} {T T' : ℝ}
    (hT : ∀ η ∈ S, ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0) (hTT' : T ≤ T') (σ : S) :
    ∀ᵐ z ∂stripMeasure, z.1 < -T' → S.subtypeL σ z = 0 := by
  filter_upwards [hT σ σ.property] with z hz h using
    hz (hTT'.trans_lt (lt_neg_of_lt_neg h |>.trans_le (neg_le_abs _)))

end TauCeti.CylinderSobolev

namespace ContinuousLinearMap

open TauCeti.CylinderSobolev TauCeti.StripSobolev

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- **Stabilizing a Fredholm operator by test sections.** A Fredholm operator `D` from a Banach
space into `L²(ℝ × [0, 1], W)` has a stabilizer `S` made of `L²` classes of test sections that is
a topological complement of the range of `D`, hence finite-dimensional and isomorphic to the
cokernel of `D`. Its sections all vanish for `|s|` beyond some `T`, and the stabilized operator
`(ξ, σ) ↦ D ξ + σ` has a bounded linear right inverse `Q`. -/
theorem IsFredholm.exists_le_testSectionLp_isTopCompl {D : E →L[ℝ] Lp W 2 stripMeasure}
    (hD : D.IsFredholm) :
    ∃ S ≤ testSectionLp W, S.IsTopCompl D.range ∧ FiniteDimensional ℝ S ∧
      (∃ T : ℝ, ∀ η ∈ S, ∀ᵐ z ∂stripMeasure, T < |z.1| → η z = 0) ∧
      ∃ Q : Lp W 2 stripMeasure →L[ℝ] E × S,
        (D.coprod S.subtypeL).comp Q = ContinuousLinearMap.id ℝ _ := by
  obtain ⟨S, hSD, hS, _, Q, hQ⟩ :=
    hD.exists_le_isTopCompl_rightInverse_coprod_of_dense dense_testSectionLp
  exact ⟨S, hSD, hS, inferInstance, exists_forall_ae_eq_zero_of_le_testSectionLp hSD, Q, hQ⟩

end ContinuousLinearMap

namespace TauCeti.CylinderSobolev

open StripSobolev

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- **Linear gluing of Fredholm pieces.** Let `D₁` and `D₂` be first-order operators on the
cylinder with essentially bounded coefficient fields `M₁` and `M₂` whose ends match, Fredholm from
`W^{1,2}` to `L²`. There are stabilizers `S₁` and `S₂` made of `L²` classes of test sections,
topological complements of the ranges of `D₁` and `D₂`, such that for every sufficiently long neck
the glued operator `D_R`, stabilized by the translates `j_R` of `S₁` and `S₂` to the two ends of
the neck (`TauCeti.CylinderSobolev.gluedStabilizer`), has a bounded linear right inverse of norm at
most a constant `C` independent of `R`. -/
theorem exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff_of_isFredholm
    {M₁ M₂ : ℝ × ℝ → V × V × V →L[ℝ] W} {M : ℝ → V × V × V →L[ℝ] W}
    (hM₁ : MemLp M₁ ∞ stripMeasure) (hM₂ : MemLp M₂ ∞ stripMeasure)
    (h₁ : TendstoUniformlyOn (Function.curry M₁) M atTop (Icc 0 1))
    (h₂ : TendstoUniformlyOn (Function.curry M₂) M atBot (Icc 0 1))
    (hD₁ : ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).IsFredholm)
    (hD₂ : ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).IsFredholm) :
    ∃ S₁ S₂ : Submodule ℝ (Lp W 2 stripMeasure), S₁ ≤ testSectionLp W ∧ S₂ ≤ testSectionLp W ∧
      S₁.IsTopCompl ((jetOperator stripMeasure M₁).comp (H1 V).subtypeL).range ∧
      S₂.IsTopCompl ((jetOperator stripMeasure M₂).comp (H1 V).subtypeL).range ∧
      ∃ C R₀ : ℝ, ∀ R ≥ R₀, ∃ Q : Lp W 2 stripMeasure →L[ℝ] H1 V × (S₁ × S₂),
        (((jetOperator stripMeasure
            (Function.uncurry (gluedCoeff (Function.curry M₁) (Function.curry M₂) R))).comp
            (H1 V).subtypeL).coprod (gluedStabilizer S₁.subtypeL S₂.subtypeL R)).comp Q =
            ContinuousLinearMap.id ℝ _ ∧
          ‖Q‖ ≤ C := by
  obtain ⟨S₁, hS₁, hc₁, -, ⟨T₁, hT₁⟩, Q₁, hQ₁⟩ := hD₁.exists_le_testSectionLp_isTopCompl
  obtain ⟨S₂, hS₂, hc₂, -, ⟨T₂, hT₂⟩, Q₂, hQ₂⟩ := hD₂.exists_le_testSectionLp_isTopCompl
  obtain ⟨R₀, hR₀⟩ := exists_forall_ge_exists_rightInverse_coprod_jetOperator_gluedCoeff
    hM₁ hM₂ h₁ h₂ (ae_subtypeL_eq_zero_of_lt hT₁ (le_max_left T₁ T₂))
    (ae_subtypeL_eq_zero_of_lt_neg hT₂ (le_max_right T₁ T₂)) hQ₁ hQ₂
  exact ⟨S₁, S₂, hS₁, hS₂, hc₁, hc₂, 4 * (‖Q₁‖ + ‖Q₂‖), R₀, hR₀⟩

end TauCeti.CylinderSobolev
