/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.Analysis.Distribution.TestFunction.Hyperplane
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Cutting by half-spaces and the perimeter of convex sets

Let `μ` be a measure on a finite-dimensional real inner product space `E`, finite on compact sets
(an additive Haar measure for the results on convex sets). This file proves that cutting a set of
finite measure by a closed half-space does not increase its perimeter, and deduces that
intersecting such a set with a convex set does not increase its perimeter either. In particular
the perimeter is monotone under inclusion of convex sets: a convex set has perimeter at most that
of any null-measurable set of finite measure containing it, and bounded convex sets have finite
perimeter. Cutting by the half-spaces bounding large cubes also shows that a set of finite
measure is the limit of bounded subsets whose perimeters converge to its own.

Monotonicity under convex inclusion is how perimeters of convex bodies are compared. For a
convex body `K` containing the ball `closedBall c r`, the outer parallel body
`K + t • closedBall 0 1` lies in the dilate of `K` about `c` by `1 + t / r`, so its perimeter is at
most `(1 + t / r) ^ (n - 1) P(K)`. This is the upper bound needed to identify the right derivative
of the volume of outer parallel bodies with the perimeter.

The half-space estimate is proved by duality, without any boundary regularity. Given an admissible
test vector field `φ`, the field `ψ` that extends the normal component of `φ` on the hyperplane
`{f = c}` constantly in the normal direction is divergence-free above the hyperplane, so pairing
`s` with `φ` below the hyperplane and with `ψ` above it gives `∫_{s ∩ {f ≤ c}} div φ` up to a
term controlled by `μ (s ∩ {f ≥ c + n})`. The glued field is not smooth, but it can be smoothed
across a slab of width `1 / (n + 1)` because the normal components agree on the hyperplane
(`TauCeti.ofReal_setIntegral_add_setIntegral_le_perimeter`).

## Main results

* `TauCeti.ofReal_setIntegral_add_setIntegral_le_perimeter`: two admissible test vector fields
  whose normal components agree on a hyperplane can be glued along it.
* `TauCeti.perimeter_inter_halfSpace_le`: `P(s ∩ {f ≤ c}) ≤ P(s)` for `s` of finite measure.
* `TauCeti.perimeter_inter_biInter_halfSpace_le`: the same for finitely many half-spaces.
* `MeasureTheory.NullMeasurableSet.exists_isBounded_perimeter_approximation`: bounded truncations
  of a set of finite measure, with perimeters at most and converging to its perimeter.
* `Convex.perimeter_inter_le`: `P(s ∩ C) ≤ P(s)` for `C` convex and `μ s < ∞`.
* `Convex.perimeter_le_of_subset`: `P(K) ≤ P(L)` for `K` convex and `K ⊆ L`, `μ L < ∞`.
* `Convex.perimeter_lt_top`: a bounded convex set has finite perimeter.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapters 12 and 13.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Filter TopologicalSpace TestFunction
open scoped ENNReal Distributions Topology InnerProductSpace symmDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Extending the normal component of a test vector field off a hyperplane.** For an admissible
`φ ∈ 𝓓(E, E)` and `n : ℕ`, there is an admissible `ψ` with the same normal component `f ∘ ψ` as `φ`
on the hyperplane `{f = c}`, whose divergence above the hyperplane is bounded by `M ‖f‖` and
vanishes on the slab `c < f < c + n`. Here `M` bounds the derivative of the smooth transition. -/
private theorem exists_normal_extension (f : StrongDual ℝ E) (hf : f ≠ 0) (c : ℝ)
    {φ : 𝓓(⊤, E)} (hφ : ∀ x, ‖φ x‖ ≤ 1) {M : ℝ}
    (hM : ∀ t, ‖deriv Real.smoothTransition t‖ ≤ M) (n : ℕ) :
    ∃ ψ : 𝓓(⊤, E), (∀ x, ‖ψ x‖ ≤ 1) ∧ (∀ x, f x = c → f (φ x) = f (ψ x)) ∧
      (∀ x, c < f x → ‖divergenceCLM ψ x‖ ≤ M * ‖f‖) ∧
      ∀ x, c < f x → f x < c + n → divergenceCLM ψ x = 0 := by
  -- The normal direction: `w` is normal to `{f = c}`, with `f w = 1` and `‖f‖ ‖w‖ = 1`.
  set u := (InnerProductSpace.toDual ℝ E).symm f
  have hnu : ‖u‖ = ‖f‖ := LinearIsometryEquiv.norm_map _ _
  have hf0 : ‖f‖ ≠ 0 := norm_ne_zero_iff.2 hf
  set w := (‖f‖ ^ 2)⁻¹ • u
  have hw : f w = 1 := by
    rw [map_smul, smul_eq_mul, ← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq,
      hnu, inv_mul_cancel₀ (pow_ne_zero 2 hf0)]
  have hnw : ‖f‖ * ‖w‖ = 1 := by
    rw [norm_smul, hnu, norm_inv, norm_pow, Real.norm_of_nonneg (norm_nonneg f)]
    field_simp
  obtain ⟨ψ, hψ⟩ := StrongDual.exists_coe_eq_cutoff_normal_field f c w φ n
  have hfφ (x : E) : ‖f (φ (x - (f x - c) • w))‖ ≤ ‖f‖ :=
    (f.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg f) (hφ _))
  have hdivψ (x : E) (hx : c < f x) := StrongDual.divergenceCLM_cutoff_normal_field f c hw φ n hψ hx
  refine ⟨ψ, fun x => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx hxn => ?_⟩
  · have h₀ := Real.smoothTransition.nonneg (f x - c + 1)
    have h₁ := Real.smoothTransition.le_one (f x - c + 1)
    have h₂ := Real.smoothTransition.nonneg (f x - (c + n))
    have h₃ := Real.smoothTransition.le_one (f x - (c + n))
    have hη : ‖Real.smoothTransition (f x - c + 1) * (1 - Real.smoothTransition (f x - (c + n)))‖
        ≤ 1 := by
      rw [Real.norm_of_nonneg (mul_nonneg h₀ (by linarith))]
      nlinarith
    rw [hψ, norm_smul, norm_mul]
    calc _ ≤ (1 * ‖f‖) * ‖w‖ := by gcongr; exact hfφ x
      _ = 1 := by rw [one_mul, hnw]
  · have h₀ : (-(n : ℝ)) ≤ 0 := by simp
    simp [hψ, hx, hw, Real.smoothTransition.zero_of_nonpos h₀]
  · rw [hdivψ x hx, norm_neg, norm_mul]
    exact mul_le_mul (hM _) (hfφ x) (norm_nonneg _) ((norm_nonneg _).trans (hM 0))
  · rw [hdivψ x hx, Real.smoothTransition.deriv_of_neg (by linarith), zero_mul, neg_zero]


variable [MeasurableSpace E] {μ : Measure E} {Ω : Opens E} {s : Set E}

/-- **Gluing admissible vector fields along a hyperplane.** Let `φ` and `ψ` be test vector fields
on `Ω` with `‖φ‖, ‖ψ‖ ≤ 1` whose normal components `f ∘ φ` and `f ∘ ψ` agree on the hyperplane
`{f = a}`. Then the field equal to `φ` on the half-space `{f ≤ a}` and to `ψ` on `{f > a}` still
pairs with a null-measurable set `s` to at most its perimeter:
`∫_{s ∩ {f ≤ a}} div φ + ∫_{s ∩ {f > a}} div ψ ≤ P(s; Ω)`. -/
theorem ofReal_setIntegral_add_setIntegral_le_perimeter [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] (f : StrongDual ℝ E) (a : ℝ) {φ ψ : 𝓓(Ω, E)}
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hψ : ∀ x, ‖ψ x‖ ≤ 1) (hφψ : ∀ x, f x = a → f (φ x) = f (ψ x))
    (hs : NullMeasurableSet s μ) :
    ENNReal.ofReal ((∫ x in s ∩ {x | f x ≤ a}, divergenceCLM φ x ∂μ) +
      ∫ x in s ∩ {x | a < f x}, divergenceCLM ψ x ∂μ) ≤ perimeter μ Ω s := by
  obtain ⟨Φ, hΦ, hdiv⟩ := StrongDual.exists_interpolation_divergence f a hφ hψ
  set χ : 𝓓(Ω, E) := ψ - φ
  obtain ⟨K, hK⟩ := StrongDual.exists_abs_deriv_smoothTransition_mul_le_indicator f a
    (χ := χ) fun x hx => by simp [χ, hφψ x hx]
  have hint (φ' : 𝓓(Ω, ℝ)) : Integrable φ' μ :=
    φ'.continuous.integrable_of_hasCompactSupport φ'.hasCompactSupport
  set g : E → ℝ := fun x => {x | f x ≤ a}.indicator (divergenceCLM φ) x +
    {x | a < f x}.indicator (divergenceCLM ψ) x
  have hlim : Tendsto (fun n => ∫ x in s, divergenceCLM (Φ n) x ∂μ) atTop
      (𝓝 (∫ x in s, g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |divergenceCLM φ x| + |divergenceCLM χ x| +
        (tsupport χ).indicator (fun _ => K) x)
      (fun n => (divergenceCLM (Φ n)).continuous.aestronglyMeasurable) ?_ ?_ ?_
    · refine (((hint _).abs.add (hint _).abs).add ?_).integrableOn
      exact (integrable_indicator_iff (isClosed_tsupport _).measurableSet).2
        (integrableOn_const χ.hasCompactSupport.isCompact.measure_lt_top.ne)
    · refine fun n => Eventually.of_forall fun x => ?_
      rw [hdiv, Real.norm_eq_abs]
      have hσ0 : 0 ≤ Real.smoothTransition ((n + 1) * (f x - a)) := Real.smoothTransition.nonneg _
      have hσ1 : Real.smoothTransition ((n + 1) * (f x - a)) ≤ 1 := Real.smoothTransition.le_one _
      refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_))
        (hK n x))
      rw [abs_mul, abs_of_nonneg hσ0]
      exact mul_le_of_le_one_left (abs_nonneg _) hσ1
    · refine Eventually.of_forall fun x => ?_
      simp only [hdiv]
      convert Real.smoothTransition.tendsto_add_mul_add_deriv_mul (d := divergenceCLM φ x)
        (e := divergenceCLM χ x) (k := f (χ x)) (t := f x - a) using 2
      by_cases hx : f x ≤ a
      · simp [g, hx, sub_nonpos.2 hx]
      · simp [g, hx, not_le.1 hx, χ]
  have hmeas_le : MeasurableSet {x | f x ≤ a} := measurableSet_le f.continuous.measurable
    measurable_const
  have hmeas_lt : MeasurableSet {x | a < f x} := measurableSet_lt measurable_const
    f.continuous.measurable
  have hsplit : ∫ x in s, g x ∂μ = (∫ x in s ∩ {x | f x ≤ a}, divergenceCLM φ x ∂μ) +
      ∫ x in s ∩ {x | a < f x}, divergenceCLM ψ x ∂μ := by
    simp only [g]
    rw [integral_add ((hint _).indicator hmeas_le).integrableOn
      ((hint _).indicator hmeas_lt).integrableOn, setIntegral_indicator hmeas_le,
      setIntegral_indicator hmeas_lt]
  rw [← hsplit]
  refine le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun n => ?_
  rw [perimeter_eq_iSup hs]
  exact le_iSup₂_of_le (f := fun (φ : 𝓓(Ω, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
    ENNReal.ofReal (∫ x in s, divergenceCLM φ x ∂μ)) (Φ n) (hΦ n) le_rfl

/-- **Cutting by a half-space does not increase the perimeter.** For a null-measurable set `s` of
finite measure and a closed half-space `{f ≤ c}`, `P(s ∩ {f ≤ c}) ≤ P(s)`.

The finiteness of `μ s` cannot be dropped: for an additive Haar measure the whole space has
perimeter zero, while a half-space `{f ≤ c}` with `f ≠ 0` has positive perimeter (infinite in
dimension at least two). -/
theorem perimeter_inter_halfSpace_le [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ]
    (f : StrongDual ℝ E) (c : ℝ) (hs : NullMeasurableSet s μ) (hμs : μ s ≠ ∞) :
    perimeter μ ⊤ (s ∩ {x | f x ≤ c}) ≤ perimeter μ ⊤ s := by
  by_cases hf : f = 0
  · by_cases hc : 0 ≤ c <;> simp [hf, hc]
  have hmeas_le : MeasurableSet {x | f x ≤ c} := measurableSet_le f.continuous.measurable
    measurable_const
  have hmeas_lt : MeasurableSet {x | c < f x} := measurableSet_lt measurable_const
    f.continuous.measurable
  have hmeas_ge (n : ℕ) : MeasurableSet {x | c + n ≤ f x} :=
    measurableSet_le measurable_const f.continuous.measurable
  rw [perimeter_eq_iSup (hs.inter hmeas_le.nullMeasurableSet)]
  refine iSup₂_le fun φ hφ => ?_
  -- Glue `φ` below the hyperplane to the normal extensions `ψₙ` above it; the pairings of `s`
  -- with `div ψₙ` above the hyperplane are bounded by `M ‖f‖ μ (s ∩ {f ≥ c + n}) → 0`.
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl)
    Real.smoothTransition.hasCompactSupport_deriv
  choose ψ hψn hφψ hψM hψ0 using exists_normal_extension f hf c hφ hM
  have hbound (n : ℕ) : ‖∫ x in s ∩ {x | c < f x}, divergenceCLM (ψ n) x ∂μ‖ ≤
      M * ‖f‖ * μ.real (s ∩ {x | c + n ≤ f x}) := by
    rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      (hs.inter hmeas_lt.nullMeasurableSet) (inter_subset_left (t := {x | c + n ≤ f x}))
      (Eventually.of_forall fun x hx => hψ0 n x hx.1.2 (not_le.1 fun h => hx.2 ⟨hx.1, h⟩))]
    refine (norm_setIntegral_le_of_norm_le_const ((measure_mono
      (inter_subset_left.trans inter_subset_left)).trans_lt hμs.lt_top)
      fun x hx => hψM n x hx.1.2).trans
      (mul_le_mul_of_nonneg_left (measureReal_mono (inter_subset_inter_left _
        inter_subset_left) (measure_ne_top_of_subset inter_subset_left hμs))
        (mul_nonneg ((norm_nonneg _).trans (hM 0)) (norm_nonneg f)))
  have hμ : Tendsto (fun n : ℕ => μ (s ∩ {x | c + n ≤ f x})) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n : ℕ => s ∩ {x | c + n ≤ f x})
      (fun n => hs.inter (hmeas_ge n).nullMeasurableSet)
      (fun m n hmn x hx => ⟨hx.1, le_trans (by simpa using hmn : c + (m : ℝ) ≤ c + n) hx.2⟩)
      ⟨0, measure_ne_top_of_subset inter_subset_left hμs⟩
    have hempty : ⋂ n : ℕ, s ∩ {x | c + n ≤ f x} = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (f x - c)
      have := (mem_iInter.1 hx N).2
      simp only [mem_ofPred_eq] at this
      linarith
    rwa [hempty, measure_empty] at h
  have hlim : Tendsto (fun n : ℕ => (∫ x in s ∩ {x | f x ≤ c}, divergenceCLM φ x ∂μ) +
      ∫ x in s ∩ {x | c < f x}, divergenceCLM (ψ n) x ∂μ) atTop
      (𝓝 (∫ x in s ∩ {x | f x ≤ c}, divergenceCLM φ x ∂μ)) := by
    have h0 := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hμ).const_mul (M * ‖f‖)
    simp only [ENNReal.toReal_zero, mul_zero] at h0
    simpa only [add_zero] using tendsto_const_nhds.add (squeeze_zero_norm hbound h0)
  refine le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun n => ?_
  exact ofReal_setIntegral_add_setIntegral_le_perimeter f c hφ (hψn n) (hφψ n) hs

/-- **Cutting by finitely many half-spaces does not increase the perimeter.** For a
null-measurable set `s` of finite measure and finitely many closed half-spaces `{g k ≤ c k}`,
`k ∈ S`, the perimeter of `s ∩ ⋂ k ∈ S, {g k ≤ c k}` is at most `P(s)`. -/
theorem perimeter_inter_biInter_halfSpace_le [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts μ] {κ : Type*} (g : κ → StrongDual ℝ E)
    (c : κ → ℝ) (S : Finset κ) (hs : NullMeasurableSet s μ) (hμs : μ s ≠ ∞) :
    perimeter μ ⊤ (s ∩ ⋂ k ∈ S, {x | g k x ≤ c k}) ≤ perimeter μ ⊤ s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S _ ih =>
    have h : s ∩ ⋂ j ∈ insert k S, {x | g j x ≤ c j} =
        (s ∩ ⋂ j ∈ S, {x | g j x ≤ c j}) ∩ {x | g k x ≤ c k} := by
      rw [Finset.set_biInter_insert]
      ext x
      simp only [mem_inter_iff]
      tauto
    rw [h]
    refine (perimeter_inter_halfSpace_le _ _ ?_ ?_).trans ih
    · exact hs.inter (S.measurableSet_biInter fun j _ =>
        measurableSet_le (g j).continuous.measurable measurable_const).nullMeasurableSet
    · exact measure_ne_top_of_subset inter_subset_left hμs

/-- **Bounded truncation in perimeter.** A null-measurable set `s` of finite measure is the limit
of an increasing sequence of bounded null-measurable subsets `t n ⊆ s`, converging to `s` in
measure, whose perimeters are at most `P(s)` and converge to `P(s)`. The perimeters are
extended-valued, so `s` may have infinite perimeter. The finiteness of `μ s` cannot be dropped,
since bounded subsets of a set of infinite measure do not converge to it in measure. -/
theorem _root_.MeasureTheory.NullMeasurableSet.exists_isBounded_perimeter_approximation
    [OpensMeasurableSpace E] [IsFiniteMeasureOnCompacts μ] (hs : NullMeasurableSet s μ)
    (hμs : μ s ≠ ⊤) :
    ∃ t : ℕ → Set E, Monotone t ∧
      (∀ n, t n ⊆ s ∧ NullMeasurableSet (t n) μ ∧ Bornology.IsBounded (t n) ∧
        perimeter μ ⊤ (t n) ≤ perimeter μ ⊤ s) ∧
      Tendsto (fun n => μ (s \ t n)) atTop (𝓝 0) ∧
      Tendsto (fun n => perimeter μ ⊤ (t n)) atTop (𝓝 (perimeter μ ⊤ s)) := by
  -- Cut `s` by the cubes `Q n = {x | |⟪b i, x⟫| ≤ n for all i}` of an orthonormal basis `b`.
  let b := stdOrthonormalBasis ℝ E
  let g : Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ E) → StrongDual ℝ E :=
    Sum.elim (fun i => innerSL ℝ (b i)) (fun i => -innerSL ℝ (b i))
  let Q : ℕ → Set E := fun n => ⋂ k ∈ (Finset.univ : Finset _), {x | g k x ≤ n}
  have hQ (n : ℕ) (x : E) : x ∈ Q n ↔ ∀ i, |⟪b i, x⟫_ℝ| ≤ n := by
    simp [Q, g, abs_le, forall_and, neg_le, and_comm]
  have hQm (n : ℕ) : MeasurableSet (Q n) :=
    Finset.univ.measurableSet_biInter fun k _ =>
      measurableSet_le (g k).continuous.measurable measurable_const
  have hQmono : Monotone Q := fun m n hmn x hx => (hQ n x).2 fun i =>
    ((hQ m x).1 hx i).trans (by exact_mod_cast hmn)
  let t : ℕ → Set E := fun n => s ∩ Q n
  have ht (n : ℕ) : NullMeasurableSet (t n) μ := hs.inter (hQm n).nullMeasurableSet
  have htP (n : ℕ) : perimeter μ ⊤ (t n) ≤ perimeter μ ⊤ s :=
    perimeter_inter_biInter_halfSpace_le g (fun _ => n) Finset.univ hs hμs
  have htb (n : ℕ) : Bornology.IsBounded (t n) := by
    refine isBounded_iff_forall_norm_le.2 ⟨√(Module.finrank ℝ E) * n, fun x hx => ?_⟩
    refine (b.norm_le_card_mul_iSup_norm_inner x).trans ?_
    rw [Fintype.card_fin]
    gcongr
    exact Real.iSup_le (fun i => (Real.norm_eq_abs _).trans_le ((hQ n x).1 hx.2 i)) n.cast_nonneg
  -- The remainders `s \ Q n` decrease to the empty set.
  have hlim : Tendsto (fun n => μ (s \ t n)) atTop (𝓝 0) := by
    have hdiff (n : ℕ) : s \ t n = s \ Q n := by simp [t]
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => s \ Q n)
      (fun n => hs.diff (hQm n).nullMeasurableSet)
      (fun m n hmn => sdiff_subset_sdiff_right (hQmono hmn))
      ⟨0, measure_ne_top_of_subset sdiff_subset hμs⟩
    have hempty : ⋂ n, s \ Q n = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
      refine (mem_iInter.1 hx n).2 ((hQ n x).2 fun i => ?_)
      calc |⟪b i, x⟫_ℝ| ≤ ‖b i‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ = ‖x‖ := by rw [b.orthonormal.1 i, one_mul]
        _ ≤ n := hn
    simpa only [hdiff, hempty, measure_empty, Function.comp_def] using h
  refine ⟨t, fun m n hmn => inter_subset_inter_right s (hQmono hmn),
    fun n => ⟨inter_subset_left, ht n, htb n, htP n⟩, hlim, ?_⟩
  refine tendsto_of_le_liminf_of_limsup_le ?_ (limsup_le_of_le (h := .of_forall htP))
  refine perimeter_le_liminf (.of_forall ht) hs fun K _ _ => ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun n => measure_mono ?_
  rw [symmDiff_of_le (inter_subset_left : t n ⊆ s)]
  exact inter_subset_left

/-- **Intersecting with a convex set does not increase the perimeter.** For a convex set `C` and
a null-measurable set `s` of finite measure, `P(s ∩ C) ≤ P(s)`.

The finiteness of `μ s` cannot be dropped: the complement of a small ball has small perimeter, but
its intersection with a large concentric ball has larger perimeter. -/
theorem _root_.Convex.perimeter_inter_le [BorelSpace E] [μ.IsAddHaarMeasure] {C : Set E}
    (hC : Convex ℝ C) (hs : NullMeasurableSet s μ) (hμs : μ s ≠ ∞) :
    perimeter μ ⊤ (s ∩ C) ≤ perimeter μ ⊤ s := by
  -- The closure `D` of `C` is the intersection of countably many closed half-spaces, and `s ∩ C`
  -- agrees with `s ∩ D` up to a null set. Each cut of `s` by one of these half-spaces decreases
  -- the perimeter, and the perimeter is lower semicontinuous along the decreasing cuts.
  set D := closure C
  obtain ⟨g, u, hgu⟩ := RCLike.iInter_countable_halfSpaces_eq (𝕜 := ℝ) hC.closure isClosed_closure
  simp only [RCLike.re_to_real] at hgu
  set H : ℕ → Set E := fun i => {y | g i y ≤ u i}
  have hHD : ⋂ i, H i = D := hgu
  have hmemD (y : E) (hy : ∀ i, y ∈ H i) : y ∈ D := hHD ▸ mem_iInter.2 hy
  have hH (i : ℕ) : MeasurableSet (H i) :=
    measurableSet_le (g i).continuous.measurable measurable_const
  have hDH (i : ℕ) : D ⊆ H i := hHD ▸ iInter_subset _ i
  set F : Finset ℕ → Set E := fun S => s ∩ ⋂ i ∈ S, H i
  have hF (S : Finset ℕ) : NullMeasurableSet (F S) μ :=
    hs.inter (S.measurableSet_biInter fun i _ => hH i).nullMeasurableSet
  have hFP (S : Finset ℕ) : perimeter μ ⊤ (F S) ≤ perimeter μ ⊤ s :=
    perimeter_inter_biInter_halfSpace_le g u S hs hμs
  -- These cuts decrease to `s ∩ D`, which agrees with `s ∩ C` up to the null frontier of `C`.
  have hsD : NullMeasurableSet (s ∩ D) μ :=
    hs.inter isClosed_closure.measurableSet.nullMeasurableSet
  have hsDF (S : Finset ℕ) : s ∩ D ⊆ F S := fun y hy =>
    ⟨hy.1, mem_iInter₂.2 fun i _ => hDH i hy.2⟩
  have hlim : Tendsto (fun S => μ (F S \ (s ∩ D))) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun S => F S \ (s ∩ D))
      (fun S => (hF S).diff hsD)
      (fun S S' hSS' y hy => ⟨⟨hy.1.1, mem_iInter₂.2 fun i hi => mem_iInter₂.1 hy.1.2 i
        (hSS' hi)⟩, hy.2⟩)
      ⟨∅, measure_ne_top_of_subset (sdiff_subset.trans inter_subset_left) hμs⟩
    have hempty : ⋂ S, F S \ (s ∩ D) = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => ?_
      have hy' (S : Finset ℕ) := mem_iInter.1 hy S
      exact (hy' ∅).2 ⟨(hy' ∅).1.1, hmemD y fun i =>
        mem_iInter₂.1 (hy' {i}).1.2 i (Finset.mem_singleton_self i)⟩
    rwa [hempty, measure_empty] at h
  have hae : s ∩ C =ᵐ[μ] s ∩ D := by
    refine ae_eq_set.2 ⟨by
      rw [sdiff_eq_empty.2 (inter_subset_inter_right _ subset_closure), measure_empty],
      measure_mono_null (fun y hy => ?_) (hC.addHaar_frontier μ)⟩
    exact ⟨hy.1.2, fun hyi => hy.2 ⟨hy.1.1, interior_subset hyi⟩⟩
  calc perimeter μ ⊤ (s ∩ C) = perimeter μ ⊤ (s ∩ D) := perimeter_congr_ae (ae_restrict_of_ae hae)
    _ ≤ liminf (fun S => perimeter μ ⊤ (F S)) atTop := by
      refine perimeter_le_liminf (Eventually.of_forall hF) hsD fun K' _ _ => ?_
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
        fun S => measure_mono fun y hy => ?_
      rcases hy.1 with hy' | hy'
      · exact hy'
      · exact absurd (hsDF S hy'.1) hy'.2
    _ ≤ perimeter μ ⊤ s := liminf_le_of_frequently_le' (Frequently.of_forall hFP)

/-- **The perimeter is monotone under inclusion of a convex set.** If a convex set `K` is
contained in a null-measurable set `L` of finite measure, then `P(K) ≤ P(L)`. In particular the
perimeter is monotone on bounded convex sets.

The finiteness of `μ L` cannot be dropped: a half-space `{f ≤ c}` with `f ≠ 0` is convex and has
positive perimeter (infinite in dimension at least two), while the whole space has perimeter
zero. -/
theorem _root_.Convex.perimeter_le_of_subset [BorelSpace E] [μ.IsAddHaarMeasure] {K L : Set E}
    (hK : Convex ℝ K) (hKL : K ⊆ L) (hL : NullMeasurableSet L μ) (hμL : μ L ≠ ∞) :
    perimeter μ ⊤ K ≤ perimeter μ ⊤ L := by
  simpa [inter_eq_right.2 hKL] using hK.perimeter_inter_le hL hμL

/-- **A bounded convex set has finite perimeter.** -/
theorem _root_.Convex.perimeter_lt_top [BorelSpace E] [μ.IsAddHaarMeasure] {K : Set E}
    (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) : perimeter μ ⊤ K < ∞ := by
  obtain ⟨r, hr, hKr⟩ := hKb.subset_ball_lt 0 0
  refine (hK.perimeter_le_of_subset hKr measurableSet_ball.nullMeasurableSet
    measure_ball_lt_top.ne).trans_lt ?_
  rw [perimeter_ball hr]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)
    measure_ball_lt_top

end TauCeti
