/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.ProjIcc

/-!
# The double of the closed annulus is the torus

For `0 < r₁ < r₂`, the closed annulus `r₁ ≤ ‖z‖ ≤ r₂` doubled along its two boundary circles is
homeomorphic to the torus `Circle × Circle`. The first coordinate is the direction `z / ‖z‖`. The
radial parameter `x = 1 - 2 (‖z‖ - r₁) / (r₂ - r₁)`, which runs from `1` on the inner circle to
`-1` on the outer one, is sent to the point `x + √(1 - x²) I` of the upper unit semicircle on the
first sheet and to its conjugate on the second sheet, so the two radial intervals close up to a
circle.

Under this homeomorphism the sheet exchange becomes `(u, v) ↦ (u, v⁻¹)`, whose fixed set is the
two circles `v = 1` and `v = -1`, the images of the inner and outer boundary circles.

This is the topological part of the Schottky double check of the pseudoholomorphic curve analysis
roadmap; the analytic atlas on the double is not constructed here.

## Main declarations

* `TauCeti.DoubleAlong.annulus` and `TauCeti.DoubleAlong.annulusBoundary`: the closed annulus
  and its two boundary circles.
* `TauCeti.DoubleAlong.annulusDoubleHomeomorph`: the doubled annulus is `Circle × Circle`.
* `TauCeti.DoubleAlong.annulusDoubleHomeomorph_swap`: the sheet exchange is `(u, v) ↦ (u, v⁻¹)`.
* `TauCeti.DoubleAlong.annulusDoubleHomeomorph_image_fixed`: the fixed set is two circles.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, the double of a
  bordered Riemann surface.
-/

public section

open Complex ComplexConjugate Function Metric Set Topology

namespace TauCeti.DoubleAlong

/-- The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` in `ℂ`. -/
def annulus (r₁ r₂ : ℝ) : Set ℂ :=
  {z | r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂}

/-- The two boundary circles of the closed annulus, as a subset of the annulus. -/
def annulusBoundary (r₁ r₂ : ℝ) : Set (annulus r₁ r₂) :=
  {z | ‖(z : ℂ)‖ = r₁ ∨ ‖(z : ℂ)‖ = r₂}

theorem isCompact_annulus (r₁ r₂ : ℝ) : IsCompact (annulus r₁ r₂) :=
  (isCompact_closedBall (0 : ℂ) r₂).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    fun _ hz ↦ mem_closedBall_zero_iff.2 hz.2

instance instCompactSpaceAnnulus (r₁ r₂ : ℝ) : CompactSpace (annulus r₁ r₂) :=
  isCompact_iff_compactSpace.1 (isCompact_annulus r₁ r₂)

variable {r₁ r₂ : ℝ}

/-! ### The coordinates of the torus model -/

/-- The point `x + √(1 - x²) I` of the upper unit semicircle. -/
private noncomputable def upperSemicircle (x : Icc (-1 : ℝ) 1) : Circle :=
  ⟨(x : ℝ) + √(1 - (x : ℝ) ^ 2) * I, mem_sphere_zero_iff_norm.2 (by
    rw [norm_add_mul_I, Real.sq_sqrt (by nlinarith [x.2.1, x.2.2]), add_sub_cancel,
      Real.sqrt_one])⟩

private theorem coe_upperSemicircle (x : Icc (-1 : ℝ) 1) :
    (upperSemicircle x : ℂ) = (x : ℝ) + √(1 - (x : ℝ) ^ 2) * I :=
  rfl

private theorem continuous_upperSemicircle : Continuous upperSemicircle :=
  Continuous.subtype_mk (by fun_prop) _

private theorem re_upperSemicircle (x : Icc (-1 : ℝ) 1) : (upperSemicircle x : ℂ).re = x := by
  simp [coe_upperSemicircle]

private theorem im_upperSemicircle (x : Icc (-1 : ℝ) 1) :
    (upperSemicircle x : ℂ).im = √(1 - (x : ℝ) ^ 2) := by
  simp [coe_upperSemicircle]

private theorem upperSemicircle_injective : Injective upperSemicircle := fun x y h ↦
  Subtype.ext (by rw [← re_upperSemicircle x, ← re_upperSemicircle y, h])

/-- The upper semicircle meets the lower one only at `±1`. -/
private theorem upperSemicircle_eq_inv {x y : Icc (-1 : ℝ) 1}
    (h : upperSemicircle x = (upperSemicircle y)⁻¹) : x = y ∧ (x : ℝ) ^ 2 = 1 := by
  have hre := congrArg (fun v : Circle ↦ (v : ℂ).re) h
  have him := congrArg (fun v : Circle ↦ (v : ℂ).im) h
  simp only [Circle.coe_inv_eq_conj, conj_re, conj_im, re_upperSemicircle,
    im_upperSemicircle] at hre him
  have hxy : x = y := Subtype.ext hre
  subst hxy
  refine ⟨rfl, ?_⟩
  have h0 : √(1 - (x : ℝ) ^ 2) = 0 := by linarith [Real.sqrt_nonneg (1 - (x : ℝ) ^ 2)]
  have := Real.sqrt_eq_zero'.1 h0
  nlinarith [x.2.1, x.2.2]

private theorem upperSemicircle_inv_of_sq_eq_one {x : Icc (-1 : ℝ) 1} (hx : (x : ℝ) ^ 2 = 1) :
    (upperSemicircle x)⁻¹ = upperSemicircle x := by
  apply Circle.ext
  rw [Circle.coe_inv_eq_conj, coe_upperSemicircle, hx, sub_self, Real.sqrt_zero, ofReal_zero,
    zero_mul, add_zero, conj_ofReal]

/-- The direction `z / ‖z‖` of a point of the annulus. -/
private noncomputable def direction (h₀ : 0 < r₁) (z : annulus r₁ r₂) : Circle :=
  ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_norm,
      div_self (h₀.trans_le z.2.1).ne'])⟩

private theorem coe_direction (h₀ : 0 < r₁) (z : annulus r₁ r₂) :
    (direction h₀ z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) :=
  rfl

private theorem continuous_direction (h₀ : 0 < r₁) :
    Continuous (direction (r₂ := r₂) h₀) :=
  Continuous.subtype_mk ((continuous_subtype_val).div
    (continuous_ofReal.comp (continuous_norm.comp continuous_subtype_val))
    fun z ↦ ofReal_ne_zero.2 (h₀.trans_le z.2.1).ne') _

/-- A point of the annulus is its norm times its direction. -/
private theorem norm_mul_direction (h₀ : 0 < r₁) (z : annulus r₁ r₂) :
    (‖(z : ℂ)‖ : ℂ) * direction h₀ z = z := by
  rw [coe_direction, mul_div_cancel₀]
  exact ofReal_ne_zero.2 (h₀.trans_le z.2.1).ne'

/-- The radial parameter `1 - 2 (‖z‖ - r₁) / (r₂ - r₁)`, running from `1` to `-1`. -/
private noncomputable def height (z : annulus r₁ r₂) : Icc (-1 : ℝ) 1 :=
  projIcc (-1) 1 (by norm_num) (1 - 2 * (‖(z : ℂ)‖ - r₁) / (r₂ - r₁))

private theorem continuous_height : Continuous (height (r₁ := r₁) (r₂ := r₂)) :=
  continuous_projIcc.comp (by fun_prop)

private theorem coe_height (h : r₁ < r₂) (z : annulus r₁ r₂) :
    (height z : ℝ) = 1 - 2 * (‖(z : ℂ)‖ - r₁) / (r₂ - r₁) := by
  have hr : 0 < r₂ - r₁ := sub_pos.2 h
  rw [height, projIcc_of_mem]
  constructor
  · rw [le_sub_comm, sub_neg_eq_add, div_le_iff₀ hr]
    linarith [z.2.2]
  · rw [sub_le_self_iff]
    exact div_nonneg (by linarith [z.2.1]) hr.le

private theorem norm_eq_of_height_eq (h : r₁ < r₂) {z w : annulus r₁ r₂}
    (hzw : height z = height w) : ‖(z : ℂ)‖ = ‖(w : ℂ)‖ := by
  have := congrArg Subtype.val hzw
  rw [coe_height h, coe_height h] at this
  have hr : 0 < r₂ - r₁ := sub_pos.2 h
  field_simp at this
  linarith

private theorem mem_annulusBoundary_of_height_sq (h : r₁ < r₂) {z : annulus r₁ r₂}
    (hz : (height z : ℝ) ^ 2 = 1) : z ∈ annulusBoundary r₁ r₂ := by
  have hr : (r₂ - r₁) ≠ 0 := (sub_pos.2 h).ne'
  rw [sq, mul_self_eq_one_iff, coe_height h] at hz
  rcases hz with hz | hz
  · left
    field_simp at hz
    linarith
  · right
    field_simp at hz
    linarith

private theorem height_sq_of_mem_annulusBoundary (h : r₁ < r₂) {z : annulus r₁ r₂}
    (hz : z ∈ annulusBoundary r₁ r₂) : (height z : ℝ) ^ 2 = 1 := by
  have hr : (r₂ - r₁) ≠ 0 := (sub_pos.2 h).ne'
  rw [coe_height h]
  rcases hz with hz | hz <;> rw [hz]
  · simp
  · rw [mul_div_assoc, div_self hr]
    norm_num

/-! ### The homeomorphism -/

/-- The continuous map from the doubled annulus to the torus. -/
private noncomputable def annulusDoubleMap (h₀ : 0 < r₁) (h : r₁ < r₂) :
    C(DoubleAlong (annulusBoundary r₁ r₂), Circle × Circle) :=
  desc (annulusBoundary r₁ r₂)
    ⟨fun z ↦ (direction h₀ z, upperSemicircle (height z)),
      (continuous_direction h₀).prodMk (continuous_upperSemicircle.comp continuous_height)⟩
    ⟨fun z ↦ (direction h₀ z, (upperSemicircle (height z))⁻¹),
      (continuous_direction h₀).prodMk
        (continuous_upperSemicircle.comp continuous_height).inv⟩
    fun z ↦ by
      simp only [ContinuousMap.coe_mk,
        upperSemicircle_inv_of_sq_eq_one (height_sq_of_mem_annulusBoundary h z.2)]

private theorem annulusDoubleMap_inl (h₀ : 0 < r₁) (h : r₁ < r₂) (z : annulus r₁ r₂) :
    annulusDoubleMap h₀ h (inl _ z) = (direction h₀ z, upperSemicircle (height z)) :=
  desc_inl _ _ _ _ z

private theorem annulusDoubleMap_inr (h₀ : 0 < r₁) (h : r₁ < r₂) (z : annulus r₁ r₂) :
    annulusDoubleMap h₀ h (inr _ z) = (direction h₀ z, (upperSemicircle (height z))⁻¹) :=
  desc_inr _ _ _ _ z

/-- Points with the same direction and the same radial parameter coincide. -/
private theorem eq_of_direction_eq_of_height_eq (h₀ : 0 < r₁) (h : r₁ < r₂)
    {z w : annulus r₁ r₂} (hd : direction h₀ z = direction h₀ w) (hh : height z = height w) :
    z = w := by
  apply Subtype.ext
  rw [← norm_mul_direction h₀ z, ← norm_mul_direction h₀ w, hd, norm_eq_of_height_eq h hh]

private theorem annulusDoubleMap_injective (h₀ : 0 < r₁) (h : r₁ < r₂) :
    Injective (annulusDoubleMap h₀ h) := by
  intro p q hpq
  induction p using induction_on with
  | hl z =>
    induction q using induction_on with
    | hl w =>
      rw [annulusDoubleMap_inl, annulusDoubleMap_inl, Prod.mk.injEq] at hpq
      rw [eq_of_direction_eq_of_height_eq h₀ h hpq.1 (upperSemicircle_injective hpq.2)]
    | hr w =>
      rw [annulusDoubleMap_inl, annulusDoubleMap_inr, Prod.mk.injEq] at hpq
      obtain ⟨hh, hsq⟩ := upperSemicircle_eq_inv hpq.2
      obtain rfl := eq_of_direction_eq_of_height_eq h₀ h hpq.1 hh
      exact (inl_eq_inr_iff _).2 ⟨rfl, mem_annulusBoundary_of_height_sq h hsq⟩
  | hr z =>
    induction q using induction_on with
    | hl w =>
      rw [annulusDoubleMap_inr, annulusDoubleMap_inl, Prod.mk.injEq] at hpq
      obtain ⟨hh, hsq⟩ := upperSemicircle_eq_inv hpq.2.symm
      obtain rfl := eq_of_direction_eq_of_height_eq h₀ h hpq.1 hh.symm
      exact (inr_eq_inl_iff _).2 ⟨rfl, mem_annulusBoundary_of_height_sq h hsq⟩
    | hr w =>
      rw [annulusDoubleMap_inr, annulusDoubleMap_inr, Prod.mk.injEq, inv_inj] at hpq
      rw [eq_of_direction_eq_of_height_eq h₀ h hpq.1 (upperSemicircle_injective hpq.2)]

private theorem annulusDoubleMap_surjective (h₀ : 0 < r₁) (h : r₁ < r₂) :
    Surjective (annulusDoubleMap h₀ h) := by
  rintro ⟨u, v⟩
  have hv : (v : ℂ).re ^ 2 + (v : ℂ).im ^ 2 = 1 := by
    have := Circle.normSq_coe v
    rw [normSq_apply] at this
    nlinarith
  have hre : (v : ℂ).re ∈ Icc (-1 : ℝ) 1 := abs_le.1 (by
    simpa using abs_re_le_norm (v : ℂ))
  set x : Icc (-1 : ℝ) 1 := ⟨(v : ℂ).re, hre⟩ with hx
  set r : ℝ := r₁ + (1 - (x : ℝ)) / 2 * (r₂ - r₁) with hr
  have hr₁ : r₁ ≤ r := by
    have : 0 ≤ (1 - (x : ℝ)) / 2 * (r₂ - r₁) :=
      mul_nonneg (by linarith [x.2.2]) (by linarith)
    linarith
  have hr₂ : r ≤ r₂ := by
    have : (1 - (x : ℝ)) / 2 * (r₂ - r₁) ≤ r₂ - r₁ :=
      mul_le_of_le_one_left (by linarith) (by linarith [x.2.1])
    linarith
  have hnorm : ‖(r : ℂ) * u‖ = r := by
    rw [norm_mul, Circle.norm_coe, mul_one, norm_real, Real.norm_eq_abs,
      abs_of_pos (h₀.trans_le hr₁)]
  let z : annulus r₁ r₂ := ⟨(r : ℂ) * u, by
    change r₁ ≤ ‖(r : ℂ) * u‖ ∧ ‖(r : ℂ) * u‖ ≤ r₂
    rw [hnorm]
    exact ⟨hr₁, hr₂⟩⟩
  have hd : direction h₀ z = u := by
    apply Circle.ext
    rw [coe_direction]
    change (r : ℂ) * u / ((‖(r : ℂ) * u‖ : ℝ) : ℂ) = u
    rw [hnorm, mul_div_cancel_left₀ _ (ofReal_ne_zero.2 (h₀.trans_le hr₁).ne')]
  have hh : height z = x := by
    apply Subtype.ext
    rw [coe_height h]
    change 1 - 2 * (‖(r : ℂ) * u‖ - r₁) / (r₂ - r₁) = (x : ℝ)
    rw [hnorm, hr]
    field_simp [(sub_pos.2 h).ne']
    ring
  have hsqrt : √(1 - (x : ℝ) ^ 2) = |(v : ℂ).im| := by
    rw [← Real.sqrt_sq_eq_abs]
    congr 1
    simp only [hx]
    linarith
  rcases le_or_gt 0 (v : ℂ).im with him | him
  · refine ⟨inl _ z, ?_⟩
    rw [annulusDoubleMap_inl, hd, hh]
    congr 1
    apply Circle.ext
    apply Complex.ext
    · rw [re_upperSemicircle]
    · rw [im_upperSemicircle, hsqrt, abs_of_nonneg him]
  · refine ⟨inr _ z, ?_⟩
    rw [annulusDoubleMap_inr, hd, hh]
    congr 1
    apply Circle.ext
    apply Complex.ext
    · rw [Circle.coe_inv_eq_conj, conj_re, re_upperSemicircle]
    · rw [Circle.coe_inv_eq_conj, conj_im, im_upperSemicircle, hsqrt, abs_of_neg him, neg_neg]

/-- For `0 < r₁ < r₂`, the closed annulus `r₁ ≤ ‖z‖ ≤ r₂` doubled along its two boundary circles
is the torus `Circle × Circle`. The first coordinate is the direction `z / ‖z‖`; the radial
parameter is sent to the upper unit semicircle on the first sheet and to the lower one on the
second. -/
noncomputable def annulusDoubleHomeomorph (h₀ : 0 < r₁) (h : r₁ < r₂) :
    DoubleAlong (annulusBoundary r₁ r₂) ≃ₜ Circle × Circle :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (annulusDoubleMap h₀ h)
      ⟨annulusDoubleMap_injective h₀ h, annulusDoubleMap_surjective h₀ h⟩)
    (annulusDoubleMap h₀ h).continuous

/-- The first coordinate of the doubled annulus is the direction `z / ‖z‖`. -/
theorem coe_annulusDoubleHomeomorph_inl_fst (h₀ : 0 < r₁) (h : r₁ < r₂) (z : annulus r₁ r₂) :
    ((annulusDoubleHomeomorph h₀ h (inl _ z)).1 : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
  change ((annulusDoubleMap h₀ h (inl _ z)).1 : ℂ) = _
  rw [annulusDoubleMap_inl, coe_direction]

/-- Both sheets have the same direction coordinate. -/
theorem annulusDoubleHomeomorph_inr_fst (h₀ : 0 < r₁) (h : r₁ < r₂) (z : annulus r₁ r₂) :
    (annulusDoubleHomeomorph h₀ h (inr _ z)).1 = (annulusDoubleHomeomorph h₀ h (inl _ z)).1 := by
  change (annulusDoubleMap h₀ h (inr _ z)).1 = (annulusDoubleMap h₀ h (inl _ z)).1
  rw [annulusDoubleMap_inl, annulusDoubleMap_inr]

/-- The radial coordinate of the first sheet is `x + √(1 - x²) I`, where
`x = 1 - 2 (‖z‖ - r₁) / (r₂ - r₁)`. -/
theorem coe_annulusDoubleHomeomorph_inl_snd (h₀ : 0 < r₁) (h : r₁ < r₂) (z : annulus r₁ r₂) :
    ((annulusDoubleHomeomorph h₀ h (inl _ z)).2 : ℂ) =
      ((1 - 2 * (‖(z : ℂ)‖ - r₁) / (r₂ - r₁) : ℝ) : ℂ) +
        √(1 - (1 - 2 * (‖(z : ℂ)‖ - r₁) / (r₂ - r₁)) ^ 2) * I := by
  change ((annulusDoubleMap h₀ h (inl _ z)).2 : ℂ) = _
  rw [annulusDoubleMap_inl, coe_upperSemicircle, coe_height h]

/-- The radial coordinate of the second sheet is the conjugate of that of the first sheet. -/
theorem annulusDoubleHomeomorph_inr_snd (h₀ : 0 < r₁) (h : r₁ < r₂) (z : annulus r₁ r₂) :
    (annulusDoubleHomeomorph h₀ h (inr _ z)).2 = (annulusDoubleHomeomorph h₀ h (inl _ z)).2⁻¹ := by
  change (annulusDoubleMap h₀ h (inr _ z)).2 = (annulusDoubleMap h₀ h (inl _ z)).2⁻¹
  rw [annulusDoubleMap_inl, annulusDoubleMap_inr]

/-- The sheet exchange of the doubled annulus is the reflection `(u, v) ↦ (u, v⁻¹)` of the
torus. -/
theorem annulusDoubleHomeomorph_swap (h₀ : 0 < r₁) (h : r₁ < r₂)
    (p : DoubleAlong (annulusBoundary r₁ r₂)) :
    annulusDoubleHomeomorph h₀ h (swap _ p) =
      ((annulusDoubleHomeomorph h₀ h p).1, (annulusDoubleHomeomorph h₀ h p).2⁻¹) := by
  induction p using induction_on with
  | hl z =>
    rw [swap_inl]
    exact Prod.ext (annulusDoubleHomeomorph_inr_fst h₀ h z)
      (annulusDoubleHomeomorph_inr_snd h₀ h z)
  | hr z =>
    rw [swap_inr]
    exact Prod.ext (annulusDoubleHomeomorph_inr_fst h₀ h z).symm
      (by rw [annulusDoubleHomeomorph_inr_snd, inv_inv])

/-- The fixed set of the sheet exchange is carried onto the two circles `v = 1` and `v = -1` of
the torus, the images of the inner and outer boundary circles. -/
theorem annulusDoubleHomeomorph_image_fixed (h₀ : 0 < r₁) (h : r₁ < r₂) :
    annulusDoubleHomeomorph h₀ h '' {p | swap (annulusBoundary r₁ r₂) p = p} =
      {q | q.2 = 1 ∨ q.2 = -1} := by
  ext q
  obtain ⟨p, rfl⟩ := (annulusDoubleHomeomorph h₀ h).surjective q
  rw [(annulusDoubleHomeomorph h₀ h).injective.mem_set_image, mem_ofPred_eq, mem_ofPred_eq,
    ← (annulusDoubleHomeomorph h₀ h).injective.eq_iff, annulusDoubleHomeomorph_swap,
    Prod.ext_iff]
  simp only [true_and]
  rw [eq_comm, eq_inv_iff_mul_eq_one, ← Circle.coe_inj, Circle.coe_mul, Circle.coe_one,
    mul_self_eq_one_iff, ← Circle.coe_one, ← Circle.coe_neg, Circle.coe_inj, Circle.coe_inj]

/-- The image of the inner boundary circle on the first sheet is the circle `v = 1`. -/
theorem annulusDoubleHomeomorph_inl_snd_of_norm_eq_inner (h₀ : 0 < r₁) (h : r₁ < r₂)
    {z : annulus r₁ r₂} (hz : ‖(z : ℂ)‖ = r₁) : (annulusDoubleHomeomorph h₀ h (inl _ z)).2 = 1 := by
  apply Circle.ext
  rw [coe_annulusDoubleHomeomorph_inl_snd, hz]
  simp

/-- The image of the outer boundary circle on the first sheet is the circle `v = -1`. -/
theorem annulusDoubleHomeomorph_inl_snd_of_norm_eq_outer (h₀ : 0 < r₁) (h : r₁ < r₂)
    {z : annulus r₁ r₂} (hz : ‖(z : ℂ)‖ = r₂) :
    (annulusDoubleHomeomorph h₀ h (inl _ z)).2 = -1 := by
  apply Circle.ext
  rw [coe_annulusDoubleHomeomorph_inl_snd, hz, mul_div_assoc, div_self (sub_pos.2 h).ne']
  norm_num

end TauCeti.DoubleAlong
