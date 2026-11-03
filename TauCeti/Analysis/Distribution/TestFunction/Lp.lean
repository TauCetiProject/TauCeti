/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.Analysis.Distribution.TestFunction.Integral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import TauCeti.Analysis.Distribution.TestFunction.Approximation

/-!
# Test functions in `Lᵖ` spaces of measures on the domain

Let `Ω` be an open set of a real normed space `E` and let `μ` be a measure on the subspace `Ω`
that is finite on compact sets. A test function on `Ω` is continuous with compact support in
`Ω`, so its restriction to `Ω` lies in `Lᵖ(μ; F)` for every `p`. This gives a linear map
`TestFunction.toLp p μ : 𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F p μ`.

When `E` is finite-dimensional, `F` is complete, `μ` is regular and `1 ≤ p < ∞`, the image is
dense. Compactly supported continuous functions on `Ω` are dense in `Lᵖ(μ)`
(`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`), and each of them is a uniform
limit of test functions supported in a fixed compact subset of `Ω`
(`Continuous.exists_testFunction_dist_le`), which is a limit in `Lᵖ(μ)` since `μ` is finite on
that compact set. No assumption is made on `μ` near the frontier of `Ω`, where it may be
infinite. This density is what extends a functional on tests that is bounded by the `L¹(μ)` norm
to all of `L¹(μ)`; for the mass measure of a current this gives its Borel restrictions.

## Main declarations

* `TestFunction.memLp_subtype`: a test function lies in `Lᵖ(μ)` for every measure `μ` on `Ω`
  finite on compact sets.
* `TestFunction.toLp`: the linear map from test functions to `Lp F p μ`.
* `TestFunction.denseRange_toLp`: test functions are dense in `Lp F p μ` for `1 ≤ p < ∞`, a
  complete space `F` and a regular measure `μ` on `Ω`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 1.3.2
  (density of test functions in `Lᵖ`).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Metric Set
open scoped Distributions ENNReal

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E} {n : ℕ∞}
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- A test function on `Ω` lies in `Lᵖ(μ)` for every measure `μ` on the subspace `Ω` that is
finite on compact sets. -/
theorem memLp_subtype (φ : 𝓓^{n}(Ω, F)) (p : ℝ≥0∞) (μ : Measure Ω)
    [IsFiniteMeasureOnCompacts μ] : MemLp (fun x : Ω => φ x) p μ := by
  have h := φ.toCompactlySupportedContinuousMap.continuous.memLp_of_hasCompactSupport
    φ.toCompactlySupportedContinuousMap.hasCompactSupport (p := p) (μ := μ)
  convert h using 1
  ext x
  simp

/-- The inclusion of test functions on `Ω` into `Lp F p μ`, for a measure `μ` on the subspace `Ω`
that is finite on compact sets. -/
def toLp (p : ℝ≥0∞) (μ : Measure Ω) [IsFiniteMeasureOnCompacts μ] :
    𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F p μ where
  toFun φ := (φ.memLp_subtype p μ).toLp _
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by simp)
  map_smul' c φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => by simp)

variable {p : ℝ≥0∞} {μ : Measure Ω}

section FiniteOnCompacts

variable [IsFiniteMeasureOnCompacts μ]

/-- The image of a test function in `Lp F p μ` is the class of its restriction to `Ω`. -/
theorem toLp_apply (φ : 𝓓^{n}(Ω, F)) :
    toLp p μ φ = (φ.memLp_subtype p μ).toLp (fun x : Ω => φ x) :=
  (rfl)

/-- The image of a test function in `Lp F p μ` is almost everywhere its restriction to `Ω`. -/
theorem coeFn_toLp (φ : 𝓓^{n}(Ω, F)) : toLp p μ φ =ᵐ[μ] fun x : Ω => φ x :=
  (φ.memLp_subtype p μ).coeFn_toLp

/-- The `Lᵖ` norm of a test function is the `Lᵖ` seminorm of its restriction to `Ω`. -/
theorem enorm_toLp (φ : 𝓓^{n}(Ω, F)) :
    ‖toLp p μ φ‖ₑ = eLpNorm (fun x : Ω => φ x) p μ := by
  rw [toLp_apply, Lp.enorm_toLp]

end FiniteOnCompacts

variable [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace F] [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] [BorelSpace E] in
/-- A compactly supported continuous function on `Ω` is approximated in `Lᵖ(μ)` by test
functions, for a measure `μ` on `Ω` finite on compact sets. -/
private theorem exists_eLpNorm_sub_le [IsFiniteMeasureOnCompacts μ] {g : Ω → F} (hg : Continuous g)
    (hgc : HasCompactSupport g) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ φ : 𝓓^{n}(Ω, F), eLpNorm (g - fun x : Ω => φ x) p μ ≤ ε := by
  -- Extend `g` by zero to `E`, and fix a compact neighbourhood `L` in `Ω` of its support.
  set G : E → F := Function.extend Subtype.val g 0
  have hG : Continuous G := hgc.continuous_extend_zero Ω.isOpen hg
  set K : Set E := (↑) '' tsupport g
  have hK : IsCompact K := hgc.isCompact.image continuous_subtype_val
  have hGK : tsupport G ⊆ K := hgc.tsupport_extend_zero_subset continuous_subtype_val
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen (Subtype.coe_image_subset _ _)
  set L : Set Ω := (↑) ⁻¹' cthickening δ K
  have hL : IsCompact L := Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage'
    hK.cthickening (by simpa using hδΩ)
  -- A uniform error `η` on `L` costs at most `η * μ L ^ (1 / p)` in `Lᵖ(μ)`.
  have hμL : μ L ^ p.toReal⁻¹ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hL.measure_lt_top.ne
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt hμL hε
  obtain ⟨φ, hφK, hφG⟩ := hG.exists_testFunction_dist_le hK hGK hδ hδΩ (NNReal.coe_pos.2 hη)
  -- The smooth test `φ` is also a test of class `C^n`.
  refine ⟨monoCLM ℝ φ, ?_⟩
  have hφn : ⇑(monoCLM ℝ φ : 𝓓^{n}(Ω, F)) = φ := by simp
  simp only [hφn]
  -- The difference vanishes off `L` and is bounded by `η` on `L`.
  have hind : (g - fun x : Ω => φ x) = L.indicator (g - fun x : Ω => φ x) := by
    refine (indicator_eq_self.2 fun x hx => ?_).symm
    by_contra hxL
    have hgx : x ∉ tsupport g := fun h => hxL (self_subset_cthickening K ⟨x, h, rfl⟩)
    have hφx : (x : E) ∉ tsupport φ := fun h => hxL (hφK h)
    exact hx (by simp [image_eq_zero_of_notMem_tsupport hgx, image_eq_zero_of_notMem_tsupport hφx])
  have hbound : ∀ x : Ω, ‖(g - fun x : Ω => φ x) x‖ ≤ η := by
    intro x
    have hGx : G x = g x := Subtype.val_injective.extend_apply _ _ x
    simpa [dist_eq_norm', hGx] using hφG x
  have hmeas : AEStronglyMeasurable (g - fun x : Ω => φ x) (μ.restrict L) :=
    (hg.sub (φ.continuous.comp continuous_subtype_val)).aestronglyMeasurable
  rw [hind, eLpNorm_indicator_eq_eLpNorm_restrict hL.measurableSet.nullMeasurableSet]
  refine (eLpNorm_le_of_ae_bound hmeas (Filter.Eventually.of_forall hbound)).trans ?_
  rw [Measure.restrict_apply_univ, ENNReal.ofReal_coe_nnreal, mul_comm]
  exact hηε.le

/-- **Test functions are dense in `Lᵖ`.** For a regular measure `μ` on an open set `Ω` of a
finite-dimensional real normed space, a complete space `F` and `1 ≤ p < ∞`, the image of the test
functions on `Ω` is dense in `Lp F p μ`. -/
theorem denseRange_toLp [μ.Regular] (hp : p ≠ ∞) :
    DenseRange (toLp p μ : 𝓓^{n}(Ω, F) →ₗ[ℝ] Lp F p μ) := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  refine fun f => EMetric.mem_closure_iff.2 fun ε hε => ?_
  rcases eq_or_ne ε ∞ with rfl | hε'
  · exact ⟨_, mem_range_self (0 : 𝓓^{n}(Ω, F)), edist_lt_top _ _⟩
  -- Approximate `f` by a compactly supported continuous `g`, and `g` by a test function, each
  -- within `ε / 4`.
  have hε4 : ε / 2 / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne').ne'
  obtain ⟨g, hgc, hfg, hg, hgp⟩ := (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le hp hε4
  obtain ⟨φ, hφ⟩ := exists_eLpNorm_sub_le (n := n) (p := p) (μ := μ) hg hgc hε4
  refine ⟨toLp p μ φ, mem_range_self φ, ?_⟩
  rw [Lp.edist_def, eLpNorm_congr_ae ((Filter.EventuallyEq.refl _ ⇑f).sub (coeFn_toLp φ))]
  calc eLpNorm (⇑f - fun x : Ω => φ x) p μ
      = eLpNorm ((⇑f - g) + (g - fun x : Ω => φ x)) p μ := by rw [sub_add_sub_cancel]
    _ ≤ eLpNorm (⇑f - g) p μ + eLpNorm (g - fun x : Ω => φ x) p μ :=
        eLpNorm_add_le Fact.out
    _ ≤ ε / 2 / 2 + ε / 2 / 2 := add_le_add hfg hφ
    _ = ε / 2 := ENNReal.add_halves _
    _ < ε := ENNReal.half_lt_self hε.ne' hε'

end TestFunction
