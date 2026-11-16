/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Hersch.Balancing
public import TauCeti.Geometry.Euclidean.Hersch.Stereographic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Checks for Hersch's maps and the balancing lemma

Model computations for `TauCeti.herschMap` and `TauCeti.exists_integral_herschMap_eq_zero`, in
`ℝ³ = EuclideanSpace ℝ (Fin 3)` with basis `e₀, e₁, e₂` and `a = (3/5) e₂`.

* Orthogonal points: for `x ⊥ a`, `T_a(x) = √(1 - ‖a‖²) x + a`, a unit vector for unit `x`;
  `T_a(e₀) = (4/5) e₀ + (3/5) e₂`.
* Fixed points: `T_a` fixes `±e₂`. Negative control: without the factor `(1 + ⟪a, x⟫)⁻¹` the
  image of `-u` for `a = ρ u` has norm `1 - ρ`, which is `2/5` here, off the sphere.
* Dilation factor: in stereographic coordinates from `-e₂`, `T_a` is the dilation by
  `√((1 - 3/5) / (1 + 3/5)) = 1/2`.
* Inverse: for `x ⊥ a`, `⟪-a, T_a(x)⟫ = -‖a‖²` and `T_(-a)(T_a(x)) = x`.
* The lemma: the area measure `σ` of the unit sphere is invariant under `x ↦ -x`, so
  `∫ x dσ = 0`, and its points are null in dimension at least two. For `Φ = T_b` the
  hypotheses of the lemma hold, and `a = -b` balances. Negative control: for a Dirac mass
  `δ_p`, `∫ T_a ∘ Φ dδ_p = T_a(Φ(p))` is a unit vector for every `a`, and the fibre of `Φ` over
  `Φ(p)` has mass one.
-/

public section

open Metric MeasureTheory Module Set RealInnerProductSpace
open scoped Pointwise

namespace TauCeti

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For `x ⊥ a`, `T_a(x) = √(1 - ‖a‖²) x + a`. -/
theorem herschMap_of_inner_eq_zero {a x : E} (h : ⟪a, x⟫ = 0) :
    herschMap a x = √(1 - ‖a‖ ^ 2) • x + a := by
  rw [herschMap_def, h]
  simp

/-- For a unit `x ⊥ a` with `‖a‖ ≤ 1`, `√(1 - ‖a‖²) x + a` is a unit vector. -/
theorem norm_sqrt_smul_add_of_inner_eq_zero {a x : E} (ha : ‖a‖ ≤ 1) (hx : ‖x‖ = 1)
    (h : ⟪a, x⟫ = 0) : ‖√(1 - ‖a‖ ^ 2) • x + a‖ = 1 := by
  rw [← herschMap_of_inner_eq_zero h]
  exact norm_herschMap ha hx (by rw [h]; norm_num)

/-- For `x ⊥ a`, `⟪-a, T_a(x)⟫ = -‖a‖²`. -/
theorem inner_neg_herschMap_of_inner_eq_zero {a x : E} (h : ⟪a, x⟫ = 0) :
    ⟪-a, herschMap a x⟫ = -‖a‖ ^ 2 := by
  rw [herschMap_of_inner_eq_zero h, inner_neg_left, inner_add_right, real_inner_smul_right, h,
    real_inner_self_eq_norm_sq]
  ring

/-- Negative control for the denominator of `T_a`: for `a = ρ u`, the numerator alone sends `-u`
to a vector of norm `1 - ρ`, which is not on the sphere for `ρ > 0`. -/
theorem norm_herschNumerator_neg {u : E} (hu : ‖u‖ = 1) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ‖√(1 - ‖ρ • u‖ ^ 2) • (-u) + (⟪ρ • u, -u⟫ / (1 + √(1 - ‖ρ • u‖ ^ 2)) + 1) • (ρ • u)‖ =
      1 - ρ := by
  have hρu : ‖ρ • u‖ = ρ := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hρ0]
  rw [hρu, inner_neg_right, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
  set s := √(1 - ρ ^ 2)
  have hs : s ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs1 : 1 + s ≠ 0 := by positivity
  have : s • (-u) + (-(ρ * 1 ^ 2) / (1 + s) + 1) • (ρ • u) = (ρ - 1) • u := by
    rw [smul_neg, smul_smul, ← neg_smul, ← add_smul]
    congr 1
    field_simp
    linear_combination -hs
  rw [this, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  ring

end General

section Model

/-- The unit vector `eᵢ` of `ℝ³`. -/
local notation "e" i:max => (EuclideanSpace.single (i : Fin 3) (1 : ℝ))

private theorem norm_e (i : Fin 3) : ‖e i‖ = 1 := by
  simp

private theorem inner_e (i j : Fin 3) (hij : i ≠ j) : ⟪e i, e j⟫ = 0 := by
  simp [EuclideanSpace.inner_single_left, hij.symm]

private theorem norm_threeFifths : ‖(3 / 5 : ℝ) • e 2‖ = 3 / 5 := by
  rw [norm_smul, norm_e, mul_one]
  norm_num

private theorem sqrt_threeFifths : √(1 - ‖(3 / 5 : ℝ) • e 2‖ ^ 2) = 4 / 5 := by
  rw [norm_threeFifths, show (1 : ℝ) - (3 / 5) ^ 2 = (4 / 5) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `T_a(e₀) = (4/5) e₀ + (3/5) e₂` for `a = (3/5) e₂`, the point `(4/5, 0, 3/5)`. -/
theorem herschMap_threeFifths_e0 :
    herschMap ((3 / 5 : ℝ) • e 2) (e 0) = (4 / 5 : ℝ) • e 0 + (3 / 5 : ℝ) • e 2 := by
  rw [herschMap_of_inner_eq_zero (by rw [real_inner_smul_left, inner_e 2 0 (by decide),
    mul_zero]), sqrt_threeFifths]

/-- `T_a` fixes `e₂` for `a = (3/5) e₂`. -/
theorem herschMap_threeFifths_e2 : herschMap ((3 / 5 : ℝ) • e 2) (e 2) = e 2 :=
  herschMap_smul_self (norm_e 2) (by norm_num) (by norm_num)

/-- `T_a` fixes `-e₂` for `a = (3/5) e₂`. -/
theorem herschMap_threeFifths_neg_e2 : herschMap ((3 / 5 : ℝ) • e 2) (-e 2) = -e 2 :=
  herschMap_smul_neg_self (norm_e 2) (by norm_num) (by norm_num)

/-- Negative control: without the denominator, the image of `-e₂` has norm `2/5`. -/
theorem norm_herschNumerator_threeFifths :
    ‖√(1 - ‖(3 / 5 : ℝ) • e 2‖ ^ 2) • (-e 2) +
        (⟪(3 / 5 : ℝ) • e 2, -e 2⟫ / (1 + √(1 - ‖(3 / 5 : ℝ) • e 2‖ ^ 2)) + 1) •
          ((3 / 5 : ℝ) • e 2)‖ = 2 / 5 := by
  rw [norm_herschNumerator_neg (norm_e 2) (by norm_num) (by norm_num)]
  norm_num

/-- In stereographic coordinates from `-e₂`, `T_a` for `a = (3/5) e₂` is the dilation by `1/2`. -/
theorem stereographic_herschHomeomorph_threeFifths (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    stereographic (v := -e 2) (by rw [norm_neg, norm_e])
        (herschHomeomorph (a := (3 / 5 : ℝ) • e 2) (by rw [norm_threeFifths]; norm_num) x) =
      (1 / 2 : ℝ) • stereographic (v := -e 2) (by rw [norm_neg, norm_e]) x := by
  have hhalf : √((1 - 3 / 5) / (1 + 3 / 5 : ℝ)) = 1 / 2 := by
    rw [show (1 - 3 / 5) / (1 + 3 / 5 : ℝ) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [← hhalf]
  exact stereographic_herschHomeomorph (norm_e 2) (by norm_num) (by norm_num) x

/-- The inverse: `⟪-a, T_a(e₀)⟫ = -9/25 = -‖a‖²` and `T_(-a)(T_a(e₀)) = e₀`. -/
theorem herschMap_threeFifths_inverse :
    ⟪-((3 / 5 : ℝ) • e 2), herschMap ((3 / 5 : ℝ) • e 2) (e 0)⟫ = -(9 / 25) ∧
      herschMap (-((3 / 5 : ℝ) • e 2)) (herschMap ((3 / 5 : ℝ) • e 2) (e 0)) = e 0 := by
  have h : ⟪(3 / 5 : ℝ) • e 2, e 0⟫ = 0 := by
    rw [real_inner_smul_left, inner_e 2 0 (by decide), mul_zero]
  refine ⟨?_, herschMap_neg_herschMap (by rw [norm_threeFifths]; norm_num) (by rw [h]; norm_num)⟩
  rw [inner_neg_herschMap_of_inner_eq_zero h, norm_threeFifths]
  norm_num

end Model

section AreaMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The sphere measure of a Haar measure is invariant under `x ↦ -x`. -/
theorem map_neg_toSphere : μ.toSphere.map Neg.neg = μ.toSphere := by
  ext s hs
  have hneg : Measurable (Neg.neg : sphere (0 : E) 1 → sphere (0 : E) 1) :=
    continuous_neg.measurable
  rw [Measure.map_apply hneg hs, μ.toSphere_apply' (hneg hs), μ.toSphere_apply' hs]
  congr 1
  have himage : ((↑) '' (Neg.neg ⁻¹' s) : Set E) = -((↑) '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨-y, hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨-y, by simpa using hy, ?_⟩
      rw [coe_neg_sphere, hyx, neg_neg]
  rw [himage, Set.smul_neg, ← one_smul ℝ (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)),
    ← Set.neg_smul_set, Measure.addHaar_smul]
  simp

/-- The barycentre of the sphere measure is zero. -/
theorem integral_coe_toSphere : ∫ x : sphere (0 : E) 1, (x : E) ∂μ.toSphere = 0 := by
  have h := integral_map (μ := μ.toSphere) (φ := Neg.neg) continuous_neg.aemeasurable
    (f := fun x : sphere (0 : E) 1 ↦ (x : E)) continuous_subtype_val.aestronglyMeasurable
  rw [map_neg_toSphere] at h
  simp only [coe_neg_sphere, integral_neg] at h
  have h2 : (2 : ℝ) • ∫ x : sphere (0 : E) 1, (x : E) ∂μ.toSphere = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/-- In dimension at least two, the points of the sphere are null for the sphere measure. -/
theorem toSphere_singleton (hE : 1 < finrank ℝ E) (p : sphere (0 : E) 1) :
    μ.toSphere {p} = 0 := by
  rw [μ.toSphere_apply' (measurableSet_singleton p), image_singleton]
  have hp : (p : E) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hspan : (ℝ ∙ (p : E)) ≠ ⊤ := by
    intro htop
    have h1 := finrank_span_singleton (K := ℝ) hp
    rw [htop, finrank_top] at h1
    omega
  refine mul_eq_zero_of_right _ (measure_mono_null ?_ (Measure.addHaar_submodule μ _ hspan))
  rw [Set.smul_singleton]
  rintro _ ⟨r, -, rfl⟩
  exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)

/-- For `Φ = T_b` on the unit sphere with its area measure, the hypotheses of the balancing lemma
hold: `Φ` is measurable with values on the sphere, and its fibres are points, hence null. -/
theorem herschMap_balancing_hypotheses (hE : 1 < finrank ℝ E) {b : E} (hb : ‖b‖ < 1) :
    AEMeasurable (fun x : sphere (0 : E) 1 ↦ herschMap b x) μ.toSphere ∧
      (∀ x : sphere (0 : E) 1, herschMap b x ∈ sphere (0 : E) 1) ∧
      ∀ v ∈ sphere (0 : E) 1,
        μ.toSphere ((fun x : sphere (0 : E) 1 ↦ herschMap b x) ⁻¹' {v}) = 0 := by
  have hb' : ‖-b‖ < 1 := by rwa [norm_neg]
  refine ⟨((measurable_herschMap b).comp measurable_subtype_coe).aemeasurable,
    fun x ↦ herschMap_mem_sphere hb x.2, fun v hv ↦ ?_⟩
  refine measure_mono_null (fun x hx ↦ ?_)
    (toSphere_singleton μ hE ⟨herschMap (-b) v, herschMap_mem_sphere hb' hv⟩)
  apply Subtype.ext
  obtain rfl : herschMap b x = v := hx
  exact (herschMap_neg_herschMap hb (inner_ne_neg_one hb (mem_sphere_zero_iff_norm.1 x.2))).symm

/-- **The balancing lemma for `Φ = T_b`.** On the unit sphere with its area measure, `a = -b`
balances `T_b`: `∫ T_(-b) ∘ T_b dσ = ∫ x dσ = 0`. -/
theorem integral_herschMap_neg_herschMap {b : E} (hb : ‖b‖ < 1) :
    ∫ x : sphere (0 : E) 1, herschMap (-b) (herschMap b x) ∂μ.toSphere = 0 := by
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)).trans
    (integral_coe_toSphere μ)
  exact herschMap_neg_herschMap hb (inner_ne_neg_one hb (mem_sphere_zero_iff_norm.1 x.2))

end AreaMeasure

section Dirac

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace X] [MeasurableSingletonClass X] {Φ : X → E}

/-- Negative control: for a Dirac mass, `∫ T_a ∘ Φ dδ_p = T_a(Φ(p))` is a unit vector for every
`a` of the open unit ball, so no `a` balances `Φ`. -/
theorem norm_integral_herschMap_dirac (hΦ : ∀ q, Φ q ∈ sphere (0 : E) 1) (p : X) {a : E}
    (ha : ‖a‖ < 1) : ‖∫ q, herschMap a (Φ q) ∂Measure.dirac p‖ = 1 := by
  rw [integral_dirac]
  exact mem_sphere_zero_iff_norm.1 (herschMap_mem_sphere ha (hΦ p))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSingletonClass X] in
/-- The hypothesis on the fibres fails for a Dirac mass: the fibre over `Φ(p)` has mass one. -/
theorem dirac_preimage_singleton (p : X) : Measure.dirac p (Φ ⁻¹' {Φ p}) = 1 :=
  Measure.dirac_apply_of_mem rfl

end Dirac

end TauCeti
