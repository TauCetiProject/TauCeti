/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The conformal maps of Hersch's balancing lemma

Adapted from Giada Franz's local formalization of Hersch's balancing lemma.

For a point `a` of the open unit ball of a real inner product space `E`, Hersch's map is

`T_a(x) = (√(1 - ‖a‖²) x + (⟪a, x⟫ / (1 + √(1 - ‖a‖²)) + 1) a) / (1 + ⟪a, x⟫)`.

It maps the unit sphere to itself, `T₀` is the identity and `T_a` has inverse `T_(-a)`; it is the
conformal transformation of the sphere fixing `±a / ‖a‖` that is conjugate, under stereographic
projection from `-a / ‖a‖`, to the dilation by `√((1 - ‖a‖) / (1 + ‖a‖))`. As `a` tends to a
point `v` of the unit sphere, `T_a(x)` tends to `v` for every `x ≠ -v` of the sphere: the formula
at `‖v‖ = 1` gives `T_v(x) = v` whenever `⟪v, x⟫ ≠ -1`, and the map is jointly continuous where
`⟪a, x⟫ ≠ -1`.

## Main definitions and results

* `TauCeti.herschMap`: the map `T_a`, as a map of the ambient space.
* `TauCeti.norm_herschMap`: `T_a` maps the unit sphere to itself.
* `TauCeti.herschMap_neg_herschMap`: `T_(-a) ∘ T_a = id` where `⟪a, x⟫ ≠ -1`.
* `TauCeti.herschMap_of_norm_eq_one`: `T_v(x) = v` for `‖v‖ = 1` and `⟪v, x⟫ ≠ -1`.
* `TauCeti.continuousAt_herschMap`, `TauCeti.contDiffAt_herschMap`: joint continuity where
  `⟪a, x⟫ ≠ -1`, and smoothness when moreover `‖a‖ < 1`.
* `TauCeti.tendsto_herschMap`: `T_a(x) → v` as `a → v`, for unit vectors `v` and `x ≠ -v`.

## References

* J. Hersch, *Quatre propriétés isopérimétriques de membranes sphériques homogènes*,
  C. R. Acad. Sci. Paris Sér. A-B 270 (1970), A1645–A1648.
* P. C. Yang and S.-T. Yau, *Eigenvalues of the Laplacian of compact Riemann surfaces and
  minimal submanifolds*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 7 (1980), 55–63, p. 59.
-/

public section

open Filter Metric Topology RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Hersch's conformal map** `T_a` of the unit sphere, as a map of the ambient space:
`T_a(x) = (√(1 - ‖a‖²) x + (⟪a, x⟫ / (1 + √(1 - ‖a‖²)) + 1) a) / (1 + ⟪a, x⟫)`. -/
noncomputable def herschMap (a x : E) : E :=
  (1 + ⟪a, x⟫)⁻¹ • (√(1 - ‖a‖ ^ 2) • x + (⟪a, x⟫ / (1 + √(1 - ‖a‖ ^ 2)) + 1) • a)

theorem herschMap_def (a x : E) :
    herschMap a x =
      (1 + ⟪a, x⟫)⁻¹ • (√(1 - ‖a‖ ^ 2) • x + (⟪a, x⟫ / (1 + √(1 - ‖a‖ ^ 2)) + 1) • a) := by
  rw [herschMap]

@[simp]
theorem herschMap_zero (x : E) : herschMap 0 x = x := by
  simp [herschMap]

/-- `T_a` maps the unit sphere to itself. -/
theorem norm_herschMap {a x : E} (ha : ‖a‖ ≤ 1) (hx : ‖x‖ = 1) (h : ⟪a, x⟫ ≠ -1) :
    ‖herschMap a x‖ = 1 := by
  set s := √(1 - ‖a‖ ^ 2) with hs_def
  have hs : s ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg a])
  have hD : 1 + ⟪a, x⟫ ≠ 0 := fun h' ↦ h (by linarith)
  have hs1 : 1 + s ≠ 0 := by positivity
  rw [herschMap, ← hs_def, norm_smul, norm_inv, Real.norm_eq_abs,
    inv_mul_eq_one₀ (by simpa using hD), eq_comm, ← sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _),
    sq_abs, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, hx, real_inner_comm x a,
    show ‖a‖ ^ 2 = 1 - s ^ 2 by linarith]
  field_simp
  ring

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

/-- `T_(-a)` inverts `T_a` at every `x` with `⟪a, x⟫ ≠ -1`, for `‖a‖ < 1`. -/
theorem herschMap_neg_herschMap {a x : E} (ha : ‖a‖ < 1) (h : ⟪a, x⟫ ≠ -1) :
    herschMap (-a) (herschMap a x) = x := by
  set s := √(1 - ‖a‖ ^ 2) with hs_def
  have hs : s ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg a])
  have hspos : 0 < s := Real.sqrt_pos.2 (by nlinarith [norm_nonneg a])
  have hD : 1 + ⟪a, x⟫ ≠ 0 := fun h' ↦ h (by linarith)
  have hs1 : 1 + s ≠ 0 := by positivity
  have ha2 : ‖a‖ ^ 2 = 1 - s ^ 2 := by linarith
  have hinner : ⟪-a, herschMap a x⟫ = -(⟪a, x⟫ + 1 - s ^ 2) / (1 + ⟪a, x⟫) := by
    rw [herschMap, ← hs_def]
    simp only [inner_neg_left, inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, ha2]
    field_simp
    ring
  have hD' : 1 + ⟪-a, herschMap a x⟫ = s ^ 2 / (1 + ⟪a, x⟫) := by
    rw [hinner]
    field_simp
    ring
  rw [herschMap_def (-a), hD', norm_neg, ← hs_def, hinner, herschMap_def a, ← hs_def]
  have hs2 : s ^ 2 ≠ 0 := by positivity
  rw [inv_div]
  match_scalars <;> field_simp [hs2]
  ring

/-- At a point `v` of the unit sphere, `T_v(x) = v` whenever `⟪v, x⟫ ≠ -1`. -/
theorem herschMap_of_norm_eq_one {v x : E} (hv : ‖v‖ = 1) (h : ⟪v, x⟫ ≠ -1) :
    herschMap v x = v := by
  have hD : 1 + ⟪v, x⟫ ≠ 0 := fun h' ↦ h (by linarith)
  rw [herschMap, hv]
  simp only [one_pow, sub_self, Real.sqrt_zero, zero_smul, zero_add, add_zero, div_one]
  rw [smul_smul, add_comm ⟪v, x⟫ 1, inv_mul_cancel₀ hD, one_smul]

/-- `T_a(x)` is jointly continuous in `(a, x)` where `⟪a, x⟫ ≠ -1`. -/
theorem continuousAt_herschMap {a x : E} (h : ⟪a, x⟫ ≠ -1) :
    ContinuousAt (fun p : E × E ↦ herschMap p.1 p.2) (a, x) := by
  have hD : 1 + ⟪a, x⟫ ≠ 0 := fun h' ↦ h (by linarith)
  have hsqrt : Continuous fun p : E × E ↦ √(1 - ‖p.1‖ ^ 2) := by fun_prop
  have hs1 : ∀ p : E × E, 1 + √(1 - ‖p.1‖ ^ 2) ≠ 0 := fun p ↦ by positivity
  unfold herschMap
  refine ContinuousAt.smul ?_ ((hsqrt.continuousAt.smul continuousAt_snd).add
    (((ContinuousAt.inner continuousAt_fst continuousAt_snd).div
      (continuous_const.add hsqrt).continuousAt
      (hs1 _)).add continuousAt_const |>.smul continuousAt_fst))
  exact (continuousAt_const.add (ContinuousAt.inner continuousAt_fst continuousAt_snd)).inv₀ hD

/-- `T_a(x)` is smooth in `(a, x)` where `‖a‖ < 1` and `⟪a, x⟫ ≠ -1`; in particular it is smooth
across `a = 0`. -/
theorem contDiffAt_herschMap {n : WithTop ℕ∞} {a x : E} (ha : ‖a‖ < 1) (h : ⟪a, x⟫ ≠ -1) :
    ContDiffAt ℝ n (fun p : E × E ↦ herschMap p.1 p.2) (a, x) := by
  have hD : 1 + ⟪a, x⟫ ≠ 0 := fun h' ↦ h (by linarith)
  have hpos : 1 - ‖a‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg a]
  have hsqrt : ContDiffAt ℝ n (fun p : E × E ↦ √(1 - ‖p.1‖ ^ 2)) (a, x) :=
    (contDiffAt_const.sub (ContDiffAt.norm_sq ℝ contDiffAt_fst)).sqrt hpos
  have hs1 : 1 + √(1 - ‖a‖ ^ 2) ≠ 0 := by positivity
  unfold herschMap
  refine ContDiffAt.smul ?_ ((hsqrt.smul contDiffAt_snd).add
    ((((ContDiffAt.inner ℝ contDiffAt_fst contDiffAt_snd).div (contDiffAt_const.add hsqrt) hs1).add
      contDiffAt_const).smul contDiffAt_fst))
  exact (contDiffAt_const.add (ContDiffAt.inner ℝ contDiffAt_fst contDiffAt_snd)).inv hD

/-- `T_a(x)` is continuous in `a` where `⟪a, x⟫ ≠ -1`. -/
theorem continuousAt_herschMap_left {a x : E} (h : ⟪a, x⟫ ≠ -1) :
    ContinuousAt (fun b ↦ herschMap b x) a :=
  (continuousAt_herschMap h).comp (x := a) (f := fun b : E ↦ (b, x)) (by fun_prop)

/-- As `a → v`, a point of the unit sphere, `T_a(x) → v` for every `x` with `⟪v, x⟫ ≠ -1`, in
particular for every unit vector `x ≠ -v`. -/
theorem tendsto_herschMap {v x : E} (hv : ‖v‖ = 1) (h : ⟪v, x⟫ ≠ -1) :
    Tendsto (fun a ↦ herschMap a x) (𝓝 v) (𝓝 v) := by
  have := (continuousAt_herschMap_left h).tendsto
  rwa [herschMap_of_norm_eq_one hv h] at this

/-- Where `⟪a, x⟫ = -1` the formula divides by zero, and `T_a(x) = 0`. -/
theorem herschMap_of_inner_eq_neg_one {a x : E} (h : ⟪a, x⟫ = -1) : herschMap a x = 0 := by
  rw [herschMap, h]
  simp

/-- `‖T_a(x)‖ ≤ 1` for `‖a‖ ≤ 1` and every unit vector `x`. -/
theorem norm_herschMap_le_one {a x : E} (ha : ‖a‖ ≤ 1) (hx : ‖x‖ = 1) :
    ‖herschMap a x‖ ≤ 1 := by
  by_cases h : ⟪a, x⟫ = -1
  · simp [herschMap_of_inner_eq_neg_one h]
  · exact (norm_herschMap ha hx h).le

/-- For `‖a‖ < 1`, `T_a` maps the unit sphere to itself. -/
theorem herschMap_mem_sphere {a x : E} (ha : ‖a‖ < 1) (hx : x ∈ sphere (0 : E) 1) :
    herschMap a x ∈ sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm] at hx ⊢
  exact norm_herschMap ha.le hx (inner_ne_neg_one ha hx)

/-- For `‖a‖ < 1`, Hersch's map is continuous on the unit sphere. -/
@[fun_prop]
theorem continuous_herschMap_sphere {a : E} (ha : ‖a‖ < 1) :
    Continuous fun x : sphere (0 : E) 1 ↦ herschMap a x := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  exact (continuousAt_herschMap
    (inner_ne_neg_one ha (mem_sphere_zero_iff_norm.1 x.2))).comp
    (f := fun y : sphere (0 : E) 1 ↦ (a, (y : E))) (by fun_prop)

/-- For `‖a‖ < 1`, `T_a` is a homeomorphism of the unit sphere, with inverse `T_(-a)`. -/
noncomputable def herschHomeomorph {a : E} (ha : ‖a‖ < 1) :
    sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1 :=
  have ha' : ‖-a‖ < 1 := by rwa [norm_neg]
  { toFun := fun x ↦ ⟨herschMap a x, herschMap_mem_sphere ha x.2⟩
    invFun := fun x ↦ ⟨herschMap (-a) x, herschMap_mem_sphere ha' x.2⟩
    left_inv := fun x ↦ Subtype.ext <| herschMap_neg_herschMap ha <|
      inner_ne_neg_one ha (mem_sphere_zero_iff_norm.1 x.2)
    right_inv := fun x ↦ Subtype.ext <| by
      simpa using herschMap_neg_herschMap ha'
        (inner_ne_neg_one ha' (mem_sphere_zero_iff_norm.1 x.2))
    continuous_toFun := (continuous_herschMap_sphere ha).subtype_mk _
    continuous_invFun := (continuous_herschMap_sphere ha').subtype_mk _ }

@[simp]
theorem coe_herschHomeomorph {a : E} (ha : ‖a‖ < 1) (x : sphere (0 : E) 1) :
    (herschHomeomorph ha x : E) = herschMap a x :=
  (rfl)

/-- The inverse of Hersch's sphere homeomorphism is induced by `T_(-a)`. -/
@[simp]
theorem coe_herschHomeomorph_symm {a : E} (ha : ‖a‖ < 1) (x : sphere (0 : E) 1) :
    ((herschHomeomorph ha).symm x : E) = herschMap (-a) x :=
  (rfl)

@[fun_prop]
theorem measurable_herschMap [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (a : E) : Measurable (herschMap a) := by
  unfold herschMap
  fun_prop

end TauCeti
