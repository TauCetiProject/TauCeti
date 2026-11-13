/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Analysis.Pseudodifferential.Symbol.Integral
public import TauCeti.RepresentationTheory.Continuous.LinHom

/-!
# Averaging symbols over a compact group

Let `G` be a compact group with a probability measure `μ`, such as the normalized Haar measure,
acting on the fibres `V` and `W` by representations `σV : ContRepresentation ℂ G V` and
`σW : ContRepresentation ℂ G W` whose operator-valued maps `g ↦ σV g` and `g ↦ σW g` are
continuous for the operator norm (in finite dimension, exactly the continuous representations).
The average `TauCeti.Symbol.average μ σV hσV σW hσW a` of a symbol `a` of order `m` has
coefficient

`(x, ξ) ↦ ∫ σW(g) ∘ a(x, ξ) ∘ σV(g)⁻¹ dμ(g)`.

It is the integral `TauCeti.Symbol.integral` of the compact family of conjugates
`g ↦ σW(g) ∘ a ∘ σV(g)⁻¹` under the Hom representation `ContRepresentation.linHom`, so it is
again a symbol of order `m`. Its seminorms are controlled by those of `a` and the bounds of the
representations (`TauCeti.Symbol.seminorm_average_le`), so it is a continuous linear map
(`TauCeti.Symbol.averageCLM`). It commutes with all derivatives and preserves compact spatial
support, uniform estimates and smoothing.

For a left-invariant measure its coefficients are invariant under conjugation by the action
(`TauCeti.Symbol.comp_coefficient_average_comp`), that is, they intertwine `σV` and `σW`. If
`V →L[ℂ] W` is complete, the average fixes the invariant symbols
(`TauCeti.Symbol.average_eq_self`); this uses completeness because Mathlib's Bochner integral in
an incomplete target is defined to be zero. Averaging with a left-invariant measure is therefore
idempotent (`TauCeti.Symbol.average_average`), with or without completeness. Here the group acts
only on the fibres; it acts trivially on the positions and frequencies.

## Main declarations

* `TauCeti.Symbol.average`, with `TauCeti.Symbol.coefficient_average`,
  `TauCeti.Symbol.coefficient_average_apply` and `TauCeti.Symbol.mixedDeriv_average`;
* `TauCeti.Symbol.average_add`, `TauCeti.Symbol.average_smul`: linearity, and
  `TauCeti.Symbol.averageCLM`: the average as a continuous linear map;
* `TauCeti.Symbol.seminorm_average_le`: the seminorm bound;
* `TauCeti.Symbol.comp_coefficient_average_comp`, `TauCeti.Symbol.coefficient_average_comp`:
  invariance of the average;
* `TauCeti.Symbol.average_eq_self`, `TauCeti.Symbol.average_average`: the average of an
  invariant symbol, and idempotence.

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

/-- The conjugate `σW(g) ∘ a ∘ σV(g)⁻¹` of a symbol. -/
private def conj (a : Symbol n V W m) (g : G) : Symbol n V W m :=
  a.map ((σV.linHom σW g).restrictScalars ℝ)

private theorem coefficient_conj (a : Symbol n V W m) (g : G)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (conj σV σW a g).coefficient p = σW g ∘L a.coefficient p ∘L σV g⁻¹ := by
  rw [conj, coefficient_map, ContinuousLinearMap.coe_restrictScalars',
    ContRepresentation.linHom_apply]

private theorem mixedDeriv_conj (a : Symbol n V W m) (g : G) (α β : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α β (conj σV σW a g).coefficient x ξ =
      σW g ∘L mixedDeriv α β a.coefficient x ξ ∘L σV g⁻¹ := by
  rw [conj, mixedDeriv_map, ContinuousLinearMap.coe_restrictScalars',
    ContRepresentation.linHom_apply]

private theorem norm_conj_le (T : V →L[ℂ] W) (g : G) :
    ‖σW g ∘L T ∘L σV g⁻¹‖ ≤ ‖σW g‖ * ‖σV g⁻¹‖ * ‖T‖ :=
  calc ‖σW g ∘L T ∘L σV g⁻¹‖
      ≤ ‖σW g‖ * (‖T‖ * ‖σV g⁻¹‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := by ring

variable [TopologicalSpace G] [IsTopologicalGroup G] (hσV : Continuous σV)
  (hσW : Continuous σW)

include hσV hσW in
/-- The spatial jets of the conjugates are jointly continuous in the group element and the
position-frequency variables. -/
private theorem continuous_iteratedFDeriv_conj (a : Symbol n V W m) (k : ℕ) :
    Continuous fun q : G × (CoordinateSpace n × CoordinateSpace n) =>
      iteratedFDeriv ℝ k (conj σV σW a q.1).coefficient q.2 := by
  have h (q : G × (CoordinateSpace n × CoordinateSpace n)) :
      iteratedFDeriv ℝ k (conj σV σW a q.1).coefficient q.2 =
        ((σV.linHom σW q.1).restrictScalars ℝ).compContinuousMultilinearMap
          (iteratedFDeriv ℝ k a.coefficient q.2) := by
    rw [conj, iteratedFDeriv_map]
  refine Continuous.congr ?_ fun q => (h q).symm
  exact (isBoundedBilinearMap_compMultilinear (𝕜 := ℝ)
    (E := fun _ : Fin k => CoordinateSpace n × CoordinateSpace n)).continuous.comp
    ((((ContinuousLinearMap.restrictScalarsIsometry ℂ (V →L[ℂ] W) (V →L[ℂ] W) ℝ ℝ).continuous.comp
      (σV.continuous_linHom σW hσV hσW)).comp continuous_fst).prodMk
      ((a.contDiff_coefficient.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
        continuous_snd))

omit [IsTopologicalGroup G] in
include hσV hσW in
/-- The symbol estimates of the conjugates hold uniformly in the group element. -/
private theorem exists_bound_conj [CompactSpace G] (a : Symbol n V W m)
    (K : Set (CoordinateSpace n)) (hK : IsCompact K) (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (conj σV σW a g).coefficient x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  obtain ⟨A, hA⟩ := (HasCompactSupport.of_compactSpace ⇑σW).exists_bound_of_continuous hσW
  obtain ⟨B, hB⟩ := (HasCompactSupport.of_compactSpace ⇑σV).exists_bound_of_continuous hσV
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 1)
  obtain ⟨C, hC0, hC⟩ := a.exists_bound K hK α β
  refine ⟨A * B * C, by positivity, fun g x hx ξ => ?_⟩
  rw [mixedDeriv_conj, mul_assoc]
  exact (norm_conj_le σV σW _ g).trans (by gcongr; exacts [hA g, hB g⁻¹, hC x hx ξ])

end Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
  (σV : ContRepresentation ℂ G V) (hσV : Continuous σV)
  (σW : ContRepresentation ℂ G W) (hσW : Continuous σW)

include hσV hσW in
private theorem integrable_conj (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    Integrable (fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹) μ := by
  have hc : Continuous fun g => σV.linHom σW g (a.coefficient p) :=
    (σV.continuous_linHom σW hσV hσW).clm_apply continuous_const
  simp only [ContRepresentation.linHom_apply] at hc
  exact hc.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- The average `∫ σW(g) ∘ a ∘ σV(g)⁻¹ dμ(g)` of a symbol over a compact group `G` with a
probability measure `μ`, for representations `σV` and `σW` of `G` on the fibres `V` and `W` that
are continuous for the operator norm; a symbol of the same order. -/
def average (a : Symbol n V W m) : Symbol n V W m :=
  integral μ (conj σV σW a) (continuous_iteratedFDeriv_conj σV σW hσV hσW a)
    (exists_bound_conj σV σW hσV hσW a)

@[simp]
theorem coefficient_average (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (average μ σV hσV σW hσW a).coefficient p = ∫ g, σW g ∘L a.coefficient p ∘L σV g⁻¹ ∂μ := by
  simp only [average, coefficient_integral, coefficient_conj]

/-- The coefficients of the average, evaluated at a vector. -/
theorem coefficient_average_apply (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) (v : V) :
    (average μ σV hσV σW hσW a).coefficient p v = ∫ g, σW g (a.coefficient p (σV g⁻¹ v)) ∂μ := by
  rw [coefficient_average, ContinuousLinearMap.integral_apply (integrable_conj μ σV hσV σW hσW a p)]
  simp only [ContinuousLinearMap.comp_apply]

/-- Mixed derivatives commute with averaging. -/
@[simp]
theorem mixedDeriv_average (a : Symbol n V W m) (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (average μ σV hσV σW hσW a).coefficient x ξ =
      ∫ g, σW g ∘L mixedDeriv α β a.coefficient x ξ ∘L σV g⁻¹ ∂μ := by
  have h : (average μ σV hσV σW hσW a).coefficient =
      fun p => ∫ g, (conj σV σW a g).coefficient p ∂μ :=
    funext fun p => by rw [average, coefficient_integral]
  rw [h, mixedDeriv_integral_of_continuous_jets μ _
    (continuous_iteratedFDeriv_conj σV σW hσV hσW a)]
  simp only [mixedDeriv_conj]

/-- Spatial derivatives commute with averaging. -/
@[simp]
theorem spatialDeriv_average (j : Fin n) (a : Symbol n V W m) :
    spatialDeriv j (average μ σV hσV σW hσW a) = average μ σV hσV σW hσW (spatialDeriv j a) :=
  Symbol.ext (funext fun ⟨x, ξ⟩ => by
    rw [← mixedDeriv_nil_nil (spatialDeriv j _).coefficient, mixedDeriv_spatialDeriv,
      mixedDeriv_average, ← mixedDeriv_nil_nil (average μ σV hσV σW hσW _).coefficient,
      mixedDeriv_average]
    simp only [mixedDeriv_spatialDeriv, List.nil_append])

/-- Frequency derivatives commute with averaging. -/
@[simp]
theorem frequencyDeriv_average (j : Fin n) (a : Symbol n V W m) :
    frequencyDeriv j (average μ σV hσV σW hσW a) =
      average μ σV hσV σW hσW (frequencyDeriv j a) :=
  Symbol.ext (funext fun ⟨x, ξ⟩ => by
    rw [← mixedDeriv_nil_nil (frequencyDeriv j _).coefficient, mixedDeriv_frequencyDeriv,
      mixedDeriv_average, ← mixedDeriv_nil_nil (average μ σV hσV σW hσW _).coefficient,
      mixedDeriv_average]
    simp only [mixedDeriv_frequencyDeriv, List.nil_append])

@[simp]
theorem average_zero : average μ σV hσV σW hσW (0 : Symbol n V W m) = 0 :=
  Symbol.ext (funext fun p => by simp)

@[simp]
theorem average_add (a b : Symbol n V W m) :
    average μ σV hσV σW hσW (a + b) = average μ σV hσV σW hσW a + average μ σV hσV σW hσW b := by
  refine Symbol.ext (funext fun p => ?_)
  simpa [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add] using
    MeasureTheory.integral_add (integrable_conj μ σV hσV σW hσW a p)
      (integrable_conj μ σV hσV σW hσW b p)

@[simp]
theorem average_smul (c : ℂ) (a : Symbol n V W m) :
    average μ σV hσV σW hσW (c • a) = c • average μ σV hσV σW hσW a := by
  refine Symbol.ext (funext fun p => ?_)
  simpa [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul] using
    MeasureTheory.integral_smul c fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹

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
  refine seminorm_integral_le_of_probability μ (conj σV σW a)
    (continuous_iteratedFDeriv_conj σV σW hσV hσW a) (exists_bound_conj σV σW hσV hσW a) K α β
    (by positivity) fun g => seminorm_le_bound K α β _ (by positivity) fun x hx ξ => ?_
  rw [mixedDeriv_conj]
  calc ‖σW g ∘L mixedDeriv α β a.coefficient x ξ ∘L σV g⁻¹‖
      ≤ ‖σW g‖ * ‖σV g⁻¹‖ * ‖mixedDeriv α β a.coefficient x ξ‖ := norm_conj_le σV σW _ g
    _ ≤ A * B * (Symbol.seminorm K α β a * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) := by
        gcongr
        exacts [hA g, hB g⁻¹, le_seminorm K α β a hx ξ]
    _ = _ := by ring

/-- Averaging is continuous in the symbol topology. -/
theorem continuous_average : Continuous (average (n := n) (m := m) μ σV hσV σW hσW) := by
  obtain ⟨A, hA⟩ := (HasCompactSupport.of_compactSpace ⇑σW).exists_bound_of_continuous hσW
  obtain ⟨B, hB⟩ := (HasCompactSupport.of_compactSpace ⇑σV).exists_bound_of_continuous hσV
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

/-- Averaging preserves compact spatial support. -/
theorem HasCompactSpatialSupport.average {a : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) :
    (Symbol.average μ σV hσV σW hσW a).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.1 ha
  exact hasCompactSpatialSupport_iff.2 ⟨K, hK, fun x hx ξ => by simp [hKa x hx ξ]⟩

/-- Averaging preserves symbol estimates that are uniform in the position. -/
theorem IsUniform.average {a : Symbol n V W m} (ha : a.IsUniform) :
    (Symbol.average μ σV hσV σW hσW a).IsUniform := by
  obtain ⟨A, hA⟩ := (HasCompactSupport.of_compactSpace ⇑σW).exists_bound_of_continuous hσW
  obtain ⟨B, hB⟩ := (HasCompactSupport.of_compactSpace ⇑σV).exists_bound_of_continuous hσV
  have hAB : 0 ≤ A * B := mul_nonneg ((norm_nonneg _).trans (hA 1)) ((norm_nonneg _).trans (hB 1))
  refine isUniform_iff_bddAbove_seminorm.2 fun α β => ?_
  obtain ⟨C, hC⟩ := isUniform_iff_bddAbove_seminorm.1 ha α β
  exact ⟨A * B * C, Set.forall_mem_range.2 fun K =>
    (seminorm_average_le μ σV hσV σW hσW a hA hB).trans
      (mul_le_mul_of_nonneg_left (hC ⟨K, rfl⟩) hAB)⟩

/-- Averaging preserves smoothing symbols. -/
theorem IsSmoothing.average {a : Symbol n V W m} (ha : a.IsSmoothing) :
    (Symbol.average μ σV hσV σW hσW a).IsSmoothing := isSmoothing_iff.2 fun m' => by
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 ha m'
  exact ⟨Symbol.average μ σV hσV σW hσW b, funext fun p => by simp only [coefficient_average, hb]⟩

/-- **The average is invariant.** For a left-invariant measure, conjugating the coefficients of the
average by the action of any `h ∈ G` returns them. -/
theorem comp_coefficient_average_comp [μ.IsMulLeftInvariant] (a : Symbol n V W m) (h : G)
    (p : CoordinateSpace n × CoordinateSpace n) :
    σW h ∘L (average μ σV hσV σW hσW a).coefficient p ∘L σV h⁻¹ =
      (average μ σV hσV σW hσW a).coefficient p := by
  by_cases hC : CompleteSpace (V →L[ℂ] W)
  · rw [coefficient_average, ← ContRepresentation.linHom_apply,
      ← (σV.linHom σW h).integral_comp_comm (integrable_conj μ σV hσV σW hσW a p)]
    have hg (g : G) : σV.linHom σW h (σW g ∘L a.coefficient p ∘L σV g⁻¹) =
        σW (h * g) ∘L a.coefficient p ∘L σV (h * g)⁻¹ := by
      simp only [ContRepresentation.linHom_apply, map_mul, mul_inv_rev,
        ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    simp_rw [hg]
    exact integral_mul_left_eq_self (fun g => σW g ∘L a.coefficient p ∘L σV g⁻¹) h
  · simp [integral_of_not_completeSpace hC]

/-- For a left-invariant measure, the coefficients of the average intertwine the
representations. -/
theorem coefficient_average_comp [μ.IsMulLeftInvariant] (a : Symbol n V W m) (h : G)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (average μ σV hσV σW hσW a).coefficient p ∘L σV h =
      σW h ∘L (average μ σV hσV σW hσW a).coefficient p :=
  (σV.linHom_apply_eq_self_iff_isIntertwining σW _).1
    (comp_coefficient_average_comp μ σV hσV σW hσW a · p) h

/-- If `V →L[ℂ] W` is complete, the average fixes the invariant symbols. -/
theorem average_eq_self [CompleteSpace (V →L[ℂ] W)] (a : Symbol n V W m)
    (ha : ∀ g p, σW g ∘L a.coefficient p ∘L σV g⁻¹ = a.coefficient p) :
    average μ σV hσV σW hσW a = a :=
  Symbol.ext (funext fun p => by simp [ha])

/-- For a left-invariant probability measure, such as the normalized Haar measure, averaging is
idempotent. -/
@[simp]
theorem average_average [μ.IsMulLeftInvariant] (a : Symbol n V W m) :
    average μ σV hσV σW hσW (average μ σV hσV σW hσW a) = average μ σV hσV σW hσW a := by
  by_cases hC : CompleteSpace (V →L[ℂ] W)
  · exact average_eq_self μ σV hσV σW hσW _ (comp_coefficient_average_comp μ σV hσV σW hσW a)
  · exact Symbol.ext (funext fun p => by simp [integral_of_not_completeSpace hC])

end TauCeti.Symbol
