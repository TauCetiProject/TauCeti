/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.Basic
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.Complex.ClosedAnnulus
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

This identifies the topological Schottky double of the closed annulus; the analytic atlas on the
double is not constructed here.

## Main declarations

* `TauCeti.DoubleAlong.annulusBoundary`: the two boundary circles of the closed annulus
  `Complex.closedAnnulus`.
* `TauCeti.DoubleAlong.annulusDoubleHomeomorph`: the doubled annulus is `Circle × Circle`.
* `TauCeti.DoubleAlong.annulusDoubleHomeomorph_swap`: the sheet exchange is `(u, v) ↦ (u, v⁻¹)`.
* `TauCeti.DoubleAlong.annulusDoubleHomeomorph_image_fixed`: the fixed set is two circles.
* `TauCeti.DoubleAlong.annulusDoubleHomeomorph_inl_snd_eq_one` and
  `TauCeti.DoubleAlong.annulusDoubleHomeomorph_inl_snd_eq_neg_one`: the inner and outer boundary
  circles go to the circles `v = 1` and `v = -1`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, the double of a
  bordered Riemann surface.
-/

public section

open Circle Complex ComplexConjugate Function Metric Set Topology

namespace TauCeti.DoubleAlong

/-- The two boundary circles of the closed annulus, as a subset of the annulus. -/
def annulusBoundary (r₁ r₂ : ℝ) : Set (closedAnnulus r₁ r₂) :=
  {z | ‖(z : ℂ)‖ = r₁ ∨ ‖(z : ℂ)‖ = r₂}

@[simp]
theorem mem_annulusBoundary {r₁ r₂ : ℝ} {z : closedAnnulus r₁ r₂} :
    z ∈ annulusBoundary r₁ r₂ ↔ ‖(z : ℂ)‖ = r₁ ∨ ‖(z : ℂ)‖ = r₂ :=
  Iff.rfl

variable {r₁ r₂ : ℝ}

/-! ### The coordinates of the torus model -/

/-- The direction `z / ‖z‖` of a point of the annulus, its first polar coordinate. -/
private noncomputable def direction (h₀ : 0 < r₁) (z : closedAnnulus r₁ r₂) : Circle :=
  (closedAnnulusHomeomorph h₀ z).1

private theorem coe_direction (h₀ : 0 < r₁) (z : closedAnnulus r₁ r₂) :
    (direction h₀ z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
  simp [direction, div_eq_inv_mul, ← ofReal_inv, ← real_smul]

private theorem continuous_direction (h₀ : 0 < r₁) :
    Continuous (direction (r₂ := r₂) h₀) :=
  continuous_fst.comp (closedAnnulusHomeomorph h₀).continuous

/-- The radial parameter `1 - 2 (‖z‖ - r₁) / (r₂ - r₁)`, running from `1` to `-1`. -/
private noncomputable def height (z : closedAnnulus r₁ r₂) : Icc (-1 : ℝ) 1 :=
  projIcc (-1) 1 (by norm_num) (1 - 2 * (‖(z : ℂ)‖ - r₁) / (r₂ - r₁))

private theorem continuous_height : Continuous (height (r₁ := r₁) (r₂ := r₂)) :=
  continuous_projIcc.comp (by fun_prop)

private theorem coe_height (h : r₁ < r₂) (z : closedAnnulus r₁ r₂) :
    (height z : ℝ) = 1 - 2 * (‖(z : ℂ)‖ - r₁) / (r₂ - r₁) := by
  have hr : 0 < r₂ - r₁ := sub_pos.2 h
  rw [height, projIcc_of_mem]
  constructor
  · rw [le_sub_comm, sub_neg_eq_add, div_le_iff₀ hr]
    linarith [closedAnnulus.norm_coe_le z]
  · rw [sub_le_self_iff]
    exact div_nonneg (by linarith [closedAnnulus.le_norm_coe z]) hr.le

private theorem norm_eq_of_height_eq (h : r₁ < r₂) {z w : closedAnnulus r₁ r₂}
    (hzw : height z = height w) : ‖(z : ℂ)‖ = ‖(w : ℂ)‖ := by
  have := congrArg Subtype.val hzw
  rw [coe_height h, coe_height h] at this
  field_simp at this
  linarith

private theorem mem_annulusBoundary_of_height_sq (h : r₁ < r₂) {z : closedAnnulus r₁ r₂}
    (hz : (height z : ℝ) ^ 2 = 1) : z ∈ annulusBoundary r₁ r₂ := by
  have hr : (r₂ - r₁) ≠ 0 := (sub_pos.2 h).ne'
  rw [sq, mul_self_eq_one_iff, coe_height h] at hz
  rw [mem_annulusBoundary]
  rcases hz with hz | hz
  · left
    field_simp at hz
    linarith
  · right
    field_simp at hz
    linarith

private theorem height_sq_of_mem_annulusBoundary (h : r₁ < r₂) {z : closedAnnulus r₁ r₂}
    (hz : z ∈ annulusBoundary r₁ r₂) : (height z : ℝ) ^ 2 = 1 := by
  have hr : (r₂ - r₁) ≠ 0 := (sub_pos.2 h).ne'
  rw [coe_height h]
  rcases mem_annulusBoundary.1 hz with hz | hz <;> rw [hz]
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
        inv_upperSemicircle_of_sq_eq_one (height_sq_of_mem_annulusBoundary h z.2)]

private theorem annulusDoubleMap_inl (h₀ : 0 < r₁) (h : r₁ < r₂) (z : closedAnnulus r₁ r₂) :
    annulusDoubleMap h₀ h (inl _ z) = (direction h₀ z, upperSemicircle (height z)) :=
  desc_inl _ _ _ _ z

private theorem annulusDoubleMap_inr (h₀ : 0 < r₁) (h : r₁ < r₂) (z : closedAnnulus r₁ r₂) :
    annulusDoubleMap h₀ h (inr _ z) = (direction h₀ z, (upperSemicircle (height z))⁻¹) :=
  desc_inr _ _ _ _ z

/-- Points with the same direction and the same radial parameter coincide. -/
private theorem eq_of_direction_eq_of_height_eq (h₀ : 0 < r₁) (h : r₁ < r₂)
    {z w : closedAnnulus r₁ r₂} (hd : direction h₀ z = direction h₀ w) (hh : height z = height w) :
    z = w :=
  (closedAnnulusHomeomorph h₀).injective
    (Prod.ext hd (Subtype.ext (by simpa using norm_eq_of_height_eq h hh)))

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
      obtain ⟨hh, hsq⟩ := upperSemicircle_eq_inv_iff.1 hpq.2
      obtain rfl := eq_of_direction_eq_of_height_eq h₀ h hpq.1 hh
      exact (inl_eq_inr_iff _).2 ⟨rfl, mem_annulusBoundary_of_height_sq h hsq⟩
  | hr z =>
    induction q using induction_on with
    | hl w =>
      rw [annulusDoubleMap_inr, annulusDoubleMap_inl, Prod.mk.injEq] at hpq
      obtain ⟨hh, hsq⟩ := upperSemicircle_eq_inv_iff.1 hpq.2.symm
      obtain rfl := eq_of_direction_eq_of_height_eq h₀ h hpq.1 hh.symm
      exact (inr_eq_inl_iff _).2 ⟨rfl, mem_annulusBoundary_of_height_sq h hsq⟩
    | hr w =>
      rw [annulusDoubleMap_inr, annulusDoubleMap_inr, Prod.mk.injEq, inv_inj] at hpq
      rw [eq_of_direction_eq_of_height_eq h₀ h hpq.1 (upperSemicircle_injective hpq.2)]

/-- Every direction and every radial parameter is attained by a point of the annulus. -/
private theorem exists_direction_eq_and_height_eq (h₀ : 0 < r₁) (h : r₁ < r₂) (u : Circle)
    (x : Icc (-1 : ℝ) 1) : ∃ z : closedAnnulus r₁ r₂, direction h₀ z = u ∧ height z = x := by
  set r : ℝ := r₁ + (1 - (x : ℝ)) / 2 * (r₂ - r₁) with hr
  have hr₁ : r₁ ≤ r := by
    have : 0 ≤ (1 - (x : ℝ)) / 2 * (r₂ - r₁) :=
      mul_nonneg (by linarith [x.2.2]) (by linarith)
    linarith
  have hr₂ : r ≤ r₂ := by
    have : (1 - (x : ℝ)) / 2 * (r₂ - r₁) ≤ r₂ - r₁ :=
      mul_le_of_le_one_left (by linarith) (by linarith [x.2.1])
    linarith
  have hpolar := (closedAnnulusHomeomorph h₀).apply_symm_apply (u, ⟨r, hr₁, hr₂⟩)
  refine ⟨(closedAnnulusHomeomorph h₀).symm (u, ⟨r, hr₁, hr₂⟩), congrArg Prod.fst hpolar, ?_⟩
  have hnorm : ‖((closedAnnulusHomeomorph h₀).symm (u, ⟨r, hr₁, hr₂⟩) : ℂ)‖ = r := by
    rw [← coe_closedAnnulusHomeomorph_apply_snd h₀, hpolar]
  apply Subtype.ext
  rw [coe_height h, hnorm, hr]
  field_simp [(sub_pos.2 h).ne']
  ring

private theorem annulusDoubleMap_surjective (h₀ : 0 < r₁) (h : r₁ < r₂) :
    Surjective (annulusDoubleMap h₀ h) := by
  rintro ⟨u, v⟩
  obtain ⟨x, hv⟩ := exists_upperSemicircle_eq_or_inv_eq v
  obtain ⟨z, hd, hh⟩ := exists_direction_eq_and_height_eq h₀ h u x
  rcases hv with hv | hv
  · exact ⟨inl _ z, by rw [annulusDoubleMap_inl, hd, hh, hv]⟩
  · exact ⟨inr _ z, by rw [annulusDoubleMap_inr, hd, hh, hv]⟩

private theorem annulusDoubleMap_bijective (h₀ : 0 < r₁) (h : r₁ < r₂) :
    Bijective (annulusDoubleMap h₀ h) :=
  ⟨annulusDoubleMap_injective h₀ h, annulusDoubleMap_surjective h₀ h⟩

/-- For `0 < r₁ < r₂`, the closed annulus `r₁ ≤ ‖z‖ ≤ r₂` doubled along its two boundary circles
is the torus `Circle × Circle`. The first coordinate is the direction `z / ‖z‖`; the radial
parameter is sent to the upper unit semicircle on the first sheet and to the lower one on the
second. -/
noncomputable def annulusDoubleHomeomorph (h₀ : 0 < r₁) (h : r₁ < r₂) :
    DoubleAlong (annulusBoundary r₁ r₂) ≃ₜ Circle × Circle :=
  IsHomeomorph.homeomorph (annulusDoubleMap h₀ h) (isHomeomorph_iff_continuous_bijective.2
    ⟨(annulusDoubleMap h₀ h).continuous, annulusDoubleMap_bijective h₀ h⟩)

private theorem annulusDoubleHomeomorph_apply (h₀ : 0 < r₁) (h : r₁ < r₂)
    (p : DoubleAlong (annulusBoundary r₁ r₂)) :
    annulusDoubleHomeomorph h₀ h p = annulusDoubleMap h₀ h p := by
  rw [annulusDoubleHomeomorph, IsHomeomorph.homeomorph_apply]

/-- The first coordinate of the doubled annulus is the direction `z / ‖z‖`. -/
@[simp]
theorem coe_annulusDoubleHomeomorph_inl_fst (h₀ : 0 < r₁) (h : r₁ < r₂) (z : closedAnnulus r₁ r₂) :
    ((annulusDoubleHomeomorph h₀ h (inl _ z)).1 : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
  rw [annulusDoubleHomeomorph_apply, annulusDoubleMap_inl, coe_direction]

/-- Both sheets have the same direction coordinate. -/
@[simp]
theorem annulusDoubleHomeomorph_inr_fst (h₀ : 0 < r₁) (h : r₁ < r₂) (z : closedAnnulus r₁ r₂) :
    (annulusDoubleHomeomorph h₀ h (inr _ z)).1 = (annulusDoubleHomeomorph h₀ h (inl _ z)).1 := by
  rw [annulusDoubleHomeomorph_apply, annulusDoubleHomeomorph_apply, annulusDoubleMap_inl,
    annulusDoubleMap_inr]

/-- The radial coordinate of the first sheet is `x + √(1 - x²) I`, where
`x = 1 - 2 (‖z‖ - r₁) / (r₂ - r₁)`. -/
theorem coe_annulusDoubleHomeomorph_inl_snd (h₀ : 0 < r₁) (h : r₁ < r₂) (z : closedAnnulus r₁ r₂) :
    ((annulusDoubleHomeomorph h₀ h (inl _ z)).2 : ℂ) =
      ((1 - 2 * (‖(z : ℂ)‖ - r₁) / (r₂ - r₁) : ℝ) : ℂ) +
        √(1 - (1 - 2 * (‖(z : ℂ)‖ - r₁) / (r₂ - r₁)) ^ 2) * I := by
  rw [annulusDoubleHomeomorph_apply, annulusDoubleMap_inl, coe_upperSemicircle, coe_height h]

/-- The radial coordinate of the second sheet is the conjugate of that of the first sheet. -/
@[simp]
theorem annulusDoubleHomeomorph_inr_snd (h₀ : 0 < r₁) (h : r₁ < r₂) (z : closedAnnulus r₁ r₂) :
    (annulusDoubleHomeomorph h₀ h (inr _ z)).2 = (annulusDoubleHomeomorph h₀ h (inl _ z)).2⁻¹ := by
  rw [annulusDoubleHomeomorph_apply, annulusDoubleHomeomorph_apply, annulusDoubleMap_inl,
    annulusDoubleMap_inr]

/-- The sheet exchange of the doubled annulus is the reflection `(u, v) ↦ (u, v⁻¹)` of the
torus. -/
@[simp]
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
  exact Circle.inv_eq_self_iff _

/-- A point of the inner boundary circle on the first sheet is sent to the circle `v = 1`. -/
theorem annulusDoubleHomeomorph_inl_snd_eq_one (h₀ : 0 < r₁) (h : r₁ < r₂)
    {z : closedAnnulus r₁ r₂} (hz : ‖(z : ℂ)‖ = r₁) :
    (annulusDoubleHomeomorph h₀ h (inl _ z)).2 = 1 := by
  apply Circle.ext
  rw [coe_annulusDoubleHomeomorph_inl_snd, hz]
  simp

/-- A point of the outer boundary circle on the first sheet is sent to the circle `v = -1`. -/
theorem annulusDoubleHomeomorph_inl_snd_eq_neg_one (h₀ : 0 < r₁) (h : r₁ < r₂)
    {z : closedAnnulus r₁ r₂} (hz : ‖(z : ℂ)‖ = r₂) :
    (annulusDoubleHomeomorph h₀ h (inl _ z)).2 = -1 := by
  apply Circle.ext
  rw [coe_annulusDoubleHomeomorph_inl_snd, hz, mul_div_assoc, div_self (sub_pos.2 h).ne']
  norm_num

end TauCeti.DoubleAlong
