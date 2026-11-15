/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
public import TauCeti.RepresentationTheory.Continuous.LinHom
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.RepresentationTheory.Continuous.Bounded

/-!
# Averaging symbols over a compact group

Let `G` be a compact group with a probability measure `μ`, such as the normalized Haar measure,
acting on the fibres `V` and `W` by representations `σV : ContRepresentation ℂ G V` and
`σW : ContRepresentation ℂ G W` whose operator-valued maps `g ↦ σV g` and `g ↦ σW g` are
continuous for the operator norm (in finite dimension, exactly the continuous representations).
The average `TauCeti.Symbol.average μ σV hσV σW hσW a` of a symbol `a` of order `m` has
coefficient

`(x, ξ) ↦ ∫ σW(g) ∘ a(x, ξ) ∘ σV(g)⁻¹ dμ(g)`.

It is the image `TauCeti.Symbol.map` of `a` under the averaged operator
`T ↦ ∫ σW(g) ∘ T ∘ σV(g)⁻¹ dμ(g)`, a continuous linear map on `V →L[ℂ] W` whose norm is at most
the product of the bounds of the representations. So it is again a symbol of order `m`, and by
the `Symbol.map` API it commutes with all derivatives and preserves compact spatial support and
uniform estimates; it also preserves smoothing. Its seminorms are controlled by those of `a` and
the bounds of the representations (`TauCeti.Symbol.seminorm_average_le`), so averaging is a
continuous linear map on symbols (`TauCeti.Symbol.averageCLM`). For the normalized Haar measure
the averaged operator is `ContRepresentation.averageOperator` after the inversion `g ↦ g⁻¹`; here
`μ` is any probability measure.

For a left-invariant measure (with measurable left multiplication, as for the Borel σ-algebra)
its coefficients are invariant under conjugation by the action
(`TauCeti.Symbol.comp_coefficient_average_comp`), that is, they intertwine `σV` and `σW`. If
`V →L[ℂ] W` is complete, the average fixes the invariant symbols
(`TauCeti.Symbol.average_eq_self`); this uses completeness because Mathlib's Bochner integral in
an incomplete target is defined to be zero. Averaging with a left-invariant measure is therefore
idempotent (`TauCeti.Symbol.average_average`), with or without completeness. Here the group acts
only on the fibres; it acts trivially on the positions and frequencies.

## Main declarations

* `TauCeti.Symbol.average`, with `TauCeti.Symbol.coefficient_average`,
  `TauCeti.Symbol.coefficient_average_apply`, `TauCeti.Symbol.mixedDeriv_average` and
  `TauCeti.Symbol.mixedDeriv_average_apply`;
* `TauCeti.Symbol.average_add`, `TauCeti.Symbol.average_smul`: linearity, and
  `TauCeti.Symbol.averageCLM`: the average as a continuous linear map;
* `TauCeti.Symbol.seminorm_average_le`: the seminorm bound;
* `TauCeti.Symbol.comp_coefficient_average_comp`, `TauCeti.Symbol.coefficient_average_comp`:
  invariance of the average;
* `TauCeti.Symbol.average_eq_self`, `TauCeti.Symbol.average_eq_self_of_comp`,
  `TauCeti.Symbol.average_average`: the average of an invariant symbol, and idempotence.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §5, (5.5)–(5.6): averaging pseudodifferential operators over a compact group.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Definition 7.8.1, for
  the symbol seminorms.
-/

public section

noncomputable section

open MeasureTheory Set
open TopologicalSpace (Compacts)

namespace TauCeti.Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

section Conj

variable {G : Type*} [Group G] (σV : ContRepresentation ℂ G V) (σW : ContRepresentation ℂ G W)

private theorem norm_conj_le (T : V →L[ℂ] W) (g : G) :
    ‖σW g ∘L T ∘L σV g⁻¹‖ ≤ ‖σW g‖ * ‖σV g⁻¹‖ * ‖T‖ :=
  calc ‖σW g ∘L T ∘L σV g⁻¹‖
      ≤ ‖σW g‖ * (‖T‖ * ‖σV g⁻¹‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := by ring

variable [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]

/-- If the representations are bounded by `A` and `B`, averaging the conjugates of `T` multiplies
its norm by at most `A B`. -/
private theorem norm_integral_conj_le {A B : ℝ} (hA : ∀ g, ‖σW g‖ ≤ A) (hB : ∀ g, ‖σV g‖ ≤ B)
    (T : V →L[ℂ] W) : ‖∫ g, σW g ∘L T ∘L σV g⁻¹ ∂μ‖ ≤ A * B * ‖T‖ := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (.of_forall fun g =>
    (norm_conj_le σV σW T g).trans (by gcongr; exacts [hA g, hB g⁻¹]))

end Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
  (σV : ContRepresentation ℂ G V) (hσV : Continuous σV)
  (σW : ContRepresentation ℂ G W) (hσW : Continuous σW)

include hσV hσW in
private theorem integrable_conj (T : V →L[ℂ] W) :
    Integrable (fun g => σW g ∘L T ∘L σV g⁻¹) μ := by
  have hc : Continuous fun g => σV.linHom σW g T :=
    (σV.continuous_linHom σW hσV hσW).clm_apply continuous_const
  simp only [ContRepresentation.linHom_apply] at hc
  exact hc.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- The average `T ↦ ∫ σW(g) ∘ T ∘ σV(g)⁻¹ dμ(g)` of the coefficient operators, as a continuous
linear map. -/
private def coefficientAverage : (V →L[ℂ] W) →L[ℂ] V →L[ℂ] W :=
  LinearMap.mkContinuousOfExistsBound
    { toFun T := ∫ g, σW g ∘L T ∘L σV g⁻¹ ∂μ
      map_add' S T := by
        simpa [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add] using
          integral_add (integrable_conj μ σV hσV σW hσW S) (integrable_conj μ σV hσV σW hσW T)
      map_smul' c T := by
        simpa [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using
          integral_smul c fun g => σW g ∘L T ∘L σV g⁻¹ }
    (by
      obtain ⟨A, -, hA⟩ := σW.exists_norm_le_of_compactSpace hσW
      obtain ⟨B, -, hB⟩ := σV.exists_norm_le_of_compactSpace hσV
      exact ⟨A * B, norm_integral_conj_le σV σW μ hA hB⟩)

private theorem coefficientAverage_apply (T : V →L[ℂ] W) :
    coefficientAverage μ σV hσV σW hσW T = ∫ g, σW g ∘L T ∘L σV g⁻¹ ∂μ :=
  (rfl)

/-- The average `∫ σW(g) ∘ a ∘ σV(g)⁻¹ dμ(g)` of a symbol over a compact group `G` with a
probability measure `μ`, for representations `σV` and `σW` of `G` on the fibres `V` and `W` that
are continuous for the operator norm; a symbol of the same order. -/
def average (a : Symbol n V W m) : Symbol n V W m :=
  a.map ((coefficientAverage μ σV hσV σW hσW).restrictScalars ℝ)

@[simp]
theorem coefficient_average (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (average μ σV hσV σW hσW a).coefficient p = ∫ g, σW g ∘L a.coefficient p ∘L σV g⁻¹ ∂μ := by
  rw [average, coefficient_map, ContinuousLinearMap.coe_restrictScalars', coefficientAverage_apply]

/-- The coefficients of the average, evaluated at a vector. -/
theorem coefficient_average_apply (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) (v : V) :
    (average μ σV hσV σW hσW a).coefficient p v = ∫ g, σW g (a.coefficient p (σV g⁻¹ v)) ∂μ := by
  rw [coefficient_average, ContinuousLinearMap.integral_apply (integrable_conj μ σV hσV σW hσW _)]
  simp only [ContinuousLinearMap.comp_apply]

/-- Mixed derivatives commute with averaging. -/
@[simp]
theorem mixedDeriv_average (a : Symbol n V W m) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (average μ σV hσV σW hσW a).coefficient x ξ =
      ∫ g, σW g ∘L mixedDeriv α β a.coefficient x ξ ∘L σV g⁻¹ ∂μ := by
  rw [average, mixedDeriv_map, ContinuousLinearMap.coe_restrictScalars', coefficientAverage_apply]

/-- The mixed derivatives of the average, evaluated at a vector. -/
theorem mixedDeriv_average_apply (a : Symbol n V W m) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) (v : V) :
    mixedDeriv α β (average μ σV hσV σW hσW a).coefficient x ξ v =
      ∫ g, σW g (mixedDeriv α β a.coefficient x ξ (σV g⁻¹ v)) ∂μ := by
  rw [mixedDeriv_average, ContinuousLinearMap.integral_apply (integrable_conj μ σV hσV σW hσW _)]
  simp only [ContinuousLinearMap.comp_apply]

/-- Spatial derivatives commute with averaging. -/
@[simp]
theorem spatialDeriv_average (j : Fin n) (a : Symbol n V W m) :
    spatialDeriv j (average μ σV hσV σW hσW a) = average μ σV hσV σW hσW (spatialDeriv j a) := by
  rw [average, average, spatialDeriv_map]

/-- Frequency derivatives commute with averaging. -/
@[simp]
theorem frequencyDeriv_average (j : Fin n) (a : Symbol n V W m) :
    frequencyDeriv j (average μ σV hσV σW hσW a) =
      average μ σV hσV σW hσW (frequencyDeriv j a) := by
  rw [average, average, frequencyDeriv_map]

@[simp]
theorem average_zero : average μ σV hσV σW hσW (0 : Symbol n V W m) = 0 :=
  Symbol.ext (funext fun p => by simp)

@[simp]
theorem average_add (a b : Symbol n V W m) :
    average μ σV hσV σW hσW (a + b) = average μ σV hσV σW hσW a + average μ σV hσV σW hσW b := by
  refine Symbol.ext (funext fun p => ?_)
  simp only [average, coefficient_map, coefficient_add, Pi.add_apply, map_add]

@[simp]
theorem average_smul (c : ℂ) (a : Symbol n V W m) :
    average μ σV hσV σW hσW (c • a) = c • average μ σV hσV σW hσW a := by
  refine Symbol.ext (funext fun p => ?_)
  simp only [average, coefficient_map, coefficient_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul]

/-- Averaging commutes with the order inclusions. -/
@[simp]
theorem average_inclusion {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m) :
    average μ σV hσV σW hσW (inclusion h a) = inclusion h (average μ σV hσV σW hσW a) :=
  Symbol.ext (funext fun p => by simp only [coefficient_average, coefficient_inclusion])

/-- If the representations are bounded by `A` and `B`, then
`p_{K,α,β}(average a) ≤ A B p_{K,α,β}(a)`. -/
theorem seminorm_average_le (a : Symbol n V W m) {K : Compacts (CoordinateSpace n)}
    {α β : List (Fin n)} {A B : ℝ} (hA : ∀ g, ‖σW g‖ ≤ A) (hB : ∀ g, ‖σV g‖ ≤ B) :
    Symbol.seminorm K α β (average μ σV hσV σW hσW a) ≤ A * B * Symbol.seminorm K α β a := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  refine seminorm_le_bound K α β _ (by positivity) fun x hx ξ => ?_
  rw [mixedDeriv_average, mul_assoc (A * B)]
  exact (norm_integral_conj_le σV σW μ hA hB _).trans
    (mul_le_mul_of_nonneg_left (le_seminorm K α β a hx ξ) (by positivity))

/-- Averaging is continuous in the symbol topology. -/
@[continuity, fun_prop]
theorem continuous_average : Continuous (average (n := n) (m := m) μ σV hσV σW hσW) := by
  obtain ⟨A, -, hA⟩ := σW.exists_norm_le_of_compactSpace hσW
  obtain ⟨B, -, hB⟩ := σV.exists_norm_le_of_compactSpace hσV
  let L : Symbol n V W m →ₗ[ℂ] Symbol n V W m :=
    { toFun := average μ σV hσV σW hσW
      map_add' := average_add μ σV hσV σW hσW
      map_smul' := average_smul μ σV hσV σW hσW }
  exact WithSeminorms.continuous_of_isBounded withSeminorms withSeminorms L
    (Seminorm.IsBounded.of_real fun ⟨K, α, β⟩ => ⟨{(K, α, β)}, A * B, fun a => by
      simpa [L] using seminorm_average_le μ σV hσV σW hσW a hA hB⟩)

/-- The average as a continuous linear map on the symbols of order `m`. -/
def averageCLM : Symbol n V W m →L[ℂ] Symbol n V W m where
  toFun := average μ σV hσV σW hσW
  map_add' := average_add μ σV hσV σW hσW
  map_smul' := average_smul μ σV hσV σW hσW
  cont := continuous_average μ σV hσV σW hσW

@[simp]
theorem averageCLM_apply (a : Symbol n V W m) :
    averageCLM μ σV hσV σW hσW a = average μ σV hσV σW hσW a := (rfl)

@[simp]
theorem average_neg (a : Symbol n V W m) :
    average μ σV hσV σW hσW (-a) = -average μ σV hσV σW hσW a :=
  map_neg (averageCLM μ σV hσV σW hσW) a

@[simp]
theorem average_sub (a b : Symbol n V W m) :
    average μ σV hσV σW hσW (a - b) = average μ σV hσV σW hσW a - average μ σV hσV σW hσW b :=
  map_sub (averageCLM μ σV hσV σW hσW) a b

theorem average_sum {ι : Type*} (s : Finset ι) (a : ι → Symbol n V W m) :
    average μ σV hσV σW hσW (∑ i ∈ s, a i) = ∑ i ∈ s, average μ σV hσV σW hσW (a i) :=
  map_sum (averageCLM μ σV hσV σW hσW) a s

/-- Averaging preserves compact spatial support. -/
theorem HasCompactSpatialSupport.average {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) :
    (Symbol.average μ σV hσV σW hσW a).HasCompactSpatialSupport := by
  rw [Symbol.average]
  exact ha.map _

/-- Averaging preserves symbol estimates that are uniform in the position. -/
theorem IsUniform.average {a : Symbol n V W m} (ha : a.IsUniform) :
    (Symbol.average μ σV hσV σW hσW a).IsUniform := by
  rw [Symbol.average]
  exact ha.map _

/-- Averaging preserves smoothing symbols. -/
theorem IsSmoothing.average {a : Symbol n V W m} (ha : a.IsSmoothing) :
    (Symbol.average μ σV hσV σW hσW a).IsSmoothing := isSmoothing_iff.2 fun m' => by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨Symbol.average μ σV hσV σW hσW b, funext fun p => by simp only [coefficient_average, hb]⟩

/-- **The average is invariant.** For a left-invariant measure, conjugating the coefficients of the
average by the action of any `h ∈ G` returns them. -/
theorem comp_coefficient_average_comp [MeasurableMul G] [μ.IsMulLeftInvariant] (a : Symbol n V W m)
    (h : G) (p : CoordinateSpace n × CoordinateSpace n) :
    σW h ∘L (average μ σV hσV σW hσW a).coefficient p ∘L σV h⁻¹ =
      (average μ σV hσV σW hσW a).coefficient p := by
  by_cases hC : CompleteSpace (V →L[ℂ] W)
  · rw [coefficient_average, ← ContRepresentation.linHom_apply,
      ← (σV.linHom σW h).integral_comp_comm (integrable_conj μ σV hσV σW hσW (a.coefficient p))]
    have hg (g : G) : σV.linHom σW h (σW g ∘L a.coefficient p ∘L σV g⁻¹) =
        σW (h * g) ∘L a.coefficient p ∘L σV (h * g)⁻¹ := by
      simp only [ContRepresentation.linHom_apply, map_mul, mul_inv_rev,
        ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    simp_rw [hg]
    exact integral_mul_left_eq_self (fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹) h
  · simp [integral_of_not_completeSpace hC]

/-- For a left-invariant measure, the coefficients of the average intertwine the
representations. -/
theorem coefficient_average_comp [MeasurableMul G] [μ.IsMulLeftInvariant] (a : Symbol n V W m)
    (h : G) (p : CoordinateSpace n × CoordinateSpace n) :
    (average μ σV hσV σW hσW a).coefficient p ∘L σV h =
      σW h ∘L (average μ σV hσV σW hσW a).coefficient p :=
  (σV.linHom_apply_eq_self_iff_isIntertwining σW _).1
    (comp_coefficient_average_comp μ σV hσV σW hσW a · p) h

/-- If `V →L[ℂ] W` is complete, the average fixes the invariant symbols. -/
theorem average_eq_self [CompleteSpace (V →L[ℂ] W)] (a : Symbol n V W m)
    (ha : ∀ g p, σW g ∘L a.coefficient p ∘L σV g⁻¹ = a.coefficient p) :
    average μ σV hσV σW hσW a = a :=
  Symbol.ext (funext fun p => by simp [ha])

/-- If `V →L[ℂ] W` is complete, the average fixes the symbols whose coefficients intertwine the
representations. -/
theorem average_eq_self_of_comp [CompleteSpace (V →L[ℂ] W)] (a : Symbol n V W m)
    (ha : ∀ g p, a.coefficient p ∘L σV g = σW g ∘L a.coefficient p) :
    average μ σV hσV σW hσW a = a :=
  average_eq_self μ σV hσV σW hσW a fun g p =>
    (σV.linHom_apply_eq_self_iff_isIntertwining σW _).2 (ha · p) g

/-- For a left-invariant probability measure, such as the normalized Haar measure, averaging is
idempotent. -/
@[simp]
theorem average_average [MeasurableMul G] [μ.IsMulLeftInvariant] (a : Symbol n V W m) :
    average μ σV hσV σW hσW (average μ σV hσV σW hσW a) = average μ σV hσV σW hσW a := by
  by_cases hC : CompleteSpace (V →L[ℂ] W)
  · exact average_eq_self μ σV hσV σW hσW _ (comp_coefficient_average_comp μ σV hσV σW hσW a)
  · exact Symbol.ext (funext fun p => by simp [integral_of_not_completeSpace hC])

end TauCeti.Symbol
