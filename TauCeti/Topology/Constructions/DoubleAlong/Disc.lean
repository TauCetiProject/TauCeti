/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.Basic
public import TauCeti.Topology.Compactification.OnePoint.UnitCircleInversion

/-!
# The double of the closed disc is the Riemann sphere

The closed unit disc doubled along its boundary circle is homeomorphic to the Riemann sphere
`OnePoint ℂ`. The first sheet is sent identically to the closed unit disc, and the second sheet is
sent to the closed exterior by the inversion in the unit circle `w ↦ (conj w)⁻¹`, with `0 ↦ ∞`.
Under this homeomorphism the sheet exchange of the double becomes the inversion in the unit
circle, an orientation-reversing involution of the sphere whose fixed set is the unit circle, the
image of the boundary.

Gluing the two sheets along the boundary by `z ↦ -conj z` instead of the identity is the same as
reparametrizing the second sheet of `DoubleAlong` by that map; the resulting sheet exchange is a
homeomorphism fixing only the two boundary points `I` and `-I`, not the whole boundary circle.

This identifies the topological Schottky double of the closed disc. The analytic atlas on the
double is not constructed here, so neither is the antiholomorphy of the sheet exchange, nor the
statement that gluing the boundary charts by `z ↦ -conj z` fails to match the complex structures
of the two sheets.

## Main declarations

* `TauCeti.DoubleAlong.discDoubleHomeomorph`: the doubled closed disc is `OnePoint ℂ`.
* `TauCeti.DoubleAlong.discDoubleHomeomorph_swap`: the sheet exchange is the inversion
  `OnePoint.unitCircleInversion`.
* `TauCeti.DoubleAlong.discDoubleHomeomorph_image_fixed_eq_sphere`: the fixed set is the unit
  circle.
* `TauCeti.DoubleAlong.discNegConjSwap`: the sheet exchange for the gluing by `z ↦ -conj z`,
  whose fixed set is `{I, -I}` (`TauCeti.DoubleAlong.discNegConjSwap_fixed`).

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, the double of a
  bordered Riemann surface.
-/

public section

open Complex ComplexConjugate Function Metric Set Topology

namespace TauCeti.DoubleAlong

open OnePoint

/-- The boundary circle of the closed unit disc, as a subset of the disc. -/
def discBoundary : Set (closedBall (0 : ℂ) 1) :=
  {z | ‖(z : ℂ)‖ = 1}

@[simp]
theorem mem_discBoundary {z : closedBall (0 : ℂ) 1} : z ∈ discBoundary ↔ ‖(z : ℂ)‖ = 1 :=
  Iff.rfl

private theorem norm_le_one (z : closedBall (0 : ℂ) 1) : ‖(z : ℂ)‖ ≤ 1 :=
  mem_closedBall_zero_iff.1 z.2

/-- The continuous map from the doubled disc to the sphere: the identity on the first sheet and the
inversion in the unit circle on the second. -/
private noncomputable def discDoubleMap : C(DoubleAlong discBoundary, OnePoint ℂ) :=
  desc discBoundary
    ⟨fun z ↦ ((z : ℂ) : OnePoint ℂ), continuous_coe.comp continuous_subtype_val⟩
    ⟨fun z ↦ unitCircleInversion ((z : ℂ) : OnePoint ℂ),
      unitCircleInversion.continuous.comp (continuous_coe.comp continuous_subtype_val)⟩
    fun z ↦ (unitCircleInversion_coe_of_norm_eq_one z.2).symm

private theorem discDoubleMap_inl (z : closedBall (0 : ℂ) 1) :
    discDoubleMap (inl _ z) = ((z : ℂ) : OnePoint ℂ) :=
  desc_inl _ _ _ _ z

private theorem discDoubleMap_inr (z : closedBall (0 : ℂ) 1) :
    discDoubleMap (inr _ z) = unitCircleInversion ((z : ℂ) : OnePoint ℂ) :=
  desc_inr _ _ _ _ z

private theorem discDoubleMap_injective : Injective discDoubleMap := by
  intro p q hpq
  induction p using induction_on with
  | hl z =>
    induction q using induction_on with
    | hl w =>
      rw [discDoubleMap_inl, discDoubleMap_inl, coe_eq_coe] at hpq
      rw [Subtype.ext hpq]
    | hr w =>
      rw [discDoubleMap_inl, discDoubleMap_inr] at hpq
      obtain ⟨hw, h⟩ :=
        (unitCircleInversion_coe_eq_coe_iff (norm_le_one z) (norm_le_one w)).1 hpq.symm
      exact (inl_eq_inr_iff _).2 ⟨Subtype.ext h, mem_discBoundary.2 (h ▸ hw)⟩
  | hr z =>
    induction q using induction_on with
    | hl w =>
      rw [discDoubleMap_inl, discDoubleMap_inr] at hpq
      obtain ⟨hz, h⟩ := (unitCircleInversion_coe_eq_coe_iff (norm_le_one w) (norm_le_one z)).1 hpq
      exact (inr_eq_inl_iff _).2 ⟨Subtype.ext h.symm, hz⟩
    | hr w =>
      rw [discDoubleMap_inr, discDoubleMap_inr, unitCircleInversion.injective.eq_iff,
        coe_eq_coe] at hpq
      rw [Subtype.ext hpq]

private theorem discDoubleMap_surjective : Surjective discDoubleMap := by
  intro x
  induction x using OnePoint.rec with
  | infty => exact ⟨inr _ ⟨0, by simp⟩, by simp [discDoubleMap_inr]⟩
  | coe w =>
    by_cases hw : ‖w‖ ≤ 1
    · exact ⟨inl _ ⟨w, mem_closedBall_zero_iff.2 hw⟩, discDoubleMap_inl _⟩
    · push Not at hw
      have hw0 : w ≠ 0 := norm_pos_iff.1 (one_pos.trans hw)
      have hu : ‖(conj w)⁻¹‖ ≤ 1 := by
        rw [norm_inv, norm_conj]
        exact inv_le_one_of_one_le₀ hw.le
      refine ⟨inr _ ⟨(conj w)⁻¹, mem_closedBall_zero_iff.2 hu⟩, ?_⟩
      rw [discDoubleMap_inr, ← unitCircleInversion_coe hw0, unitCircleInversion_unitCircleInversion]

private theorem discDoubleMap_bijective : Bijective discDoubleMap :=
  ⟨discDoubleMap_injective, discDoubleMap_surjective⟩

/-- The doubled closed unit disc is the Riemann sphere: the first sheet is the closed unit disc
and the second sheet is its image `w ↦ (conj w)⁻¹` under the inversion in the unit circle. -/
noncomputable def discDoubleHomeomorph : DoubleAlong discBoundary ≃ₜ OnePoint ℂ :=
  IsHomeomorph.homeomorph discDoubleMap
    (isHomeomorph_iff_continuous_bijective.2 ⟨discDoubleMap.continuous, discDoubleMap_bijective⟩)

private theorem discDoubleHomeomorph_apply (p : DoubleAlong discBoundary) :
    discDoubleHomeomorph p = discDoubleMap p := by
  rw [discDoubleHomeomorph, IsHomeomorph.homeomorph_apply]

@[simp]
theorem discDoubleHomeomorph_inl (z : closedBall (0 : ℂ) 1) :
    discDoubleHomeomorph (inl _ z) = ((z : ℂ) : OnePoint ℂ) := by
  rw [discDoubleHomeomorph_apply, discDoubleMap_inl]

@[simp]
theorem discDoubleHomeomorph_inr (z : closedBall (0 : ℂ) 1) :
    discDoubleHomeomorph (inr _ z) = unitCircleInversion ((z : ℂ) : OnePoint ℂ) := by
  rw [discDoubleHomeomorph_apply, discDoubleMap_inr]

/-- The sheet exchange of the doubled disc is the inversion of the sphere in the unit circle. -/
@[simp]
theorem discDoubleHomeomorph_swap (p : DoubleAlong discBoundary) :
    discDoubleHomeomorph (swap _ p) = unitCircleInversion (discDoubleHomeomorph p) := by
  induction p using induction_on with
  | hl z => simp
  | hr z => simp

/-- The fixed set of the sheet exchange is carried onto the unit circle of the sphere. -/
theorem discDoubleHomeomorph_image_fixed_eq_sphere :
    discDoubleHomeomorph '' {p | swap discBoundary p = p} =
      (↑) '' sphere (0 : ℂ) 1 := by
  rw [fixed_locus, image_image]
  ext x
  simp only [discDoubleHomeomorph_inl, mem_image, mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, mem_closedBall_zero_iff.2 hz.le⟩, hz, rfl⟩

/-- The fixed set of the sheet exchange is carried onto the fixed set of the inversion. -/
theorem discDoubleHomeomorph_image_fixed_eq_unitCircleInversion_fixed :
    discDoubleHomeomorph '' {p | swap discBoundary p = p} =
      {x | unitCircleInversion x = x} := by
  rw [discDoubleHomeomorph_image_fixed_eq_sphere]
  ext x
  simp only [mem_image, mem_sphere_zero_iff_norm, mem_ofPred_eq,
    unitCircleInversion_eq_self_iff]

/-! ### Gluing the sheets by `z ↦ -conj z` -/

/-- The reflection `z ↦ -conj z` of the closed unit disc in the imaginary axis. -/
def discNegConj (z : closedBall (0 : ℂ) 1) : closedBall (0 : ℂ) 1 :=
  ⟨-conj (z : ℂ), mem_closedBall_zero_iff.2 (by rw [norm_neg, norm_conj]; exact norm_le_one z)⟩

@[simp]
theorem coe_discNegConj (z : closedBall (0 : ℂ) 1) : (discNegConj z : ℂ) = -conj (z : ℂ) :=
  (rfl)

@[simp]
theorem discNegConj_discNegConj (z : closedBall (0 : ℂ) 1) : discNegConj (discNegConj z) = z :=
  Subtype.ext (by simp)

theorem continuous_discNegConj : Continuous discNegConj :=
  (continuous_conj.comp continuous_subtype_val).neg.subtype_mk _

theorem discNegConj_mem_discBoundary {z : closedBall (0 : ℂ) 1} (hz : z ∈ discBoundary) :
    discNegConj z ∈ discBoundary := by
  rw [mem_discBoundary, coe_discNegConj, norm_neg, norm_conj]
  exact hz

/-- The continuous map underlying `discNegConjSwap`. -/
private noncomputable def discNegConjSwapMap :
    C(DoubleAlong discBoundary, DoubleAlong discBoundary) :=
  desc discBoundary ((inr _).comp ⟨discNegConj, continuous_discNegConj⟩)
    ((inl _).comp ⟨discNegConj, continuous_discNegConj⟩)
    fun z ↦ (inl_coe_eq_inr _ ⟨discNegConj z, discNegConj_mem_discBoundary z.2⟩).symm

private theorem discNegConjSwapMap_inl (z : closedBall (0 : ℂ) 1) :
    discNegConjSwapMap (inl _ z) = inr _ (discNegConj z) :=
  desc_inl _ _ _ _ z

private theorem discNegConjSwapMap_inr (z : closedBall (0 : ℂ) 1) :
    discNegConjSwapMap (inr _ z) = inl _ (discNegConj z) :=
  desc_inr _ _ _ _ z

private theorem discNegConjSwapMap_involutive : Involutive discNegConjSwapMap := fun p ↦ by
  induction p using induction_on with
  | hl z => simp [discNegConjSwapMap_inl, discNegConjSwapMap_inr]
  | hr z => simp [discNegConjSwapMap_inl, discNegConjSwapMap_inr]

/-- The sheet exchange for the double glued along the boundary by `z ↦ -conj z` instead of the
identity. Reparametrizing the second sheet of that double by `z ↦ -conj z` identifies it with
`DoubleAlong discBoundary`, and its sheet exchange becomes `inl z ↦ inr (-conj z)` and
`inr z ↦ inl (-conj z)`. This is only the topological sheet exchange: no complex structure on the
double is involved. -/
noncomputable def discNegConjSwap : DoubleAlong discBoundary ≃ₜ DoubleAlong discBoundary where
  toFun := discNegConjSwapMap
  invFun := discNegConjSwapMap
  left_inv := discNegConjSwapMap_involutive
  right_inv := discNegConjSwapMap_involutive
  continuous_toFun := discNegConjSwapMap.continuous
  continuous_invFun := discNegConjSwapMap.continuous

@[simp]
theorem discNegConjSwap_inl (z : closedBall (0 : ℂ) 1) :
    discNegConjSwap (inl _ z) = inr _ (discNegConj z) :=
  discNegConjSwapMap_inl z

@[simp]
theorem discNegConjSwap_inr (z : closedBall (0 : ℂ) 1) :
    discNegConjSwap (inr _ z) = inl _ (discNegConj z) :=
  discNegConjSwapMap_inr z

/-- The sheet exchange for the gluing by `z ↦ -conj z` is an involution. -/
@[simp]
theorem discNegConjSwap_discNegConjSwap (p : DoubleAlong discBoundary) :
    discNegConjSwap (discNegConjSwap p) = p :=
  discNegConjSwapMap_involutive p

@[simp]
theorem discNegConjSwap_symm : discNegConjSwap.symm = discNegConjSwap := by
  ext p
  rw [Homeomorph.symm_apply_eq, discNegConjSwap_discNegConjSwap]

/-- The boundary points fixed by `z ↦ -conj z` are `I` and `-I`. -/
private theorem discNegConj_eq_self_and_mem_iff (z : closedBall (0 : ℂ) 1) :
    (discNegConj z = z ∧ discNegConj z ∈ discBoundary) ↔ (z : ℂ) = I ∨ (z : ℂ) = -I := by
  rw [Subtype.ext_iff, mem_discBoundary, coe_discNegConj, norm_neg, norm_conj]
  generalize (z : ℂ) = w
  constructor
  · rintro ⟨h1, h2⟩
    have hre : w.re = 0 := by
      have := congrArg re h1
      simp only [neg_re, conj_re] at this
      linarith
    have hw : w = (w.im : ℂ) * I := by
      apply Complex.ext <;> simp [hre]
    rw [hw, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] at h2
    rcases (abs_eq zero_le_one).1 h2 with h | h
    · left
      rw [hw, h, ofReal_one, one_mul]
    · right
      rw [hw, h, ofReal_neg, ofReal_one, neg_one_mul]
  · rintro (rfl | rfl) <;> simp

/-- The gluing by `z ↦ -conj z` gives a sheet exchange fixing only the two boundary points `I`
and `-I`, unlike the identity gluing, whose sheet exchange fixes the whole boundary circle. This
is a topological statement about fixed sets; it does not concern complex structures. -/
theorem discNegConjSwap_fixed :
    {p | discNegConjSwap p = p} =
      inl discBoundary '' {z | (z : ℂ) = I ∨ (z : ℂ) = -I} := by
  ext p
  simp only [mem_ofPred_eq, mem_image]
  induction p using induction_on with
  | hl z =>
    simp only [discNegConjSwap_inl, inr_eq_inl_iff, inl_eq_inl_iff, exists_eq_right]
    exact discNegConj_eq_self_and_mem_iff z
  | hr z =>
    simp only [discNegConjSwap_inr, inl_eq_inr_iff]
    constructor
    · rintro ⟨h, hz⟩
      exact ⟨z, (discNegConj_eq_self_and_mem_iff z).1 ⟨h, hz⟩, rfl, h ▸ hz⟩
    · rintro ⟨w, hw, rfl, -⟩
      exact (discNegConj_eq_self_and_mem_iff w).2 hw

end TauCeti.DoubleAlong
