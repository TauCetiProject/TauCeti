/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Topology.FilledHull
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.Complex.Conformal.Jordan.Quadrilateral
import TauCeti.Analysis.Complex.Conformal.Jordan.Schoenflies
import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Crosscut.Decomposition
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.Frontier
import TauCeti.Topology.MetricSpace.ProperSpace
import TauCeti.Topology.Path.Arc

/-!
# The planar annulus theorem

**Two nested Jordan curves in the plane cobound a closed annulus**: if `C₁` and `C₂` are Jordan
curves in `ℂ` with `C₂` contained in the inside `filledHull C₁ \ C₁` of `C₁`, then the closed
annular region `filledHull C₁ \ (filledHull C₂ \ C₂)` between them is homeomorphic to
`sphere (0 : ℂ) 1 × I`, carrying the end `sphere (0 : ℂ) 1 × {0}` onto `C₁` and the end
`sphere (0 : ℂ) 1 × {1}` onto `C₂`
(`TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval`). Moreover, the parametrization
on the outer boundary `C₁` may be prescribed arbitrarily
(`TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval_of_homeomorph`).

## The argument

1. **Normalization.** Since `C₂ ⊆ filledHull C₁ \ C₁`, its entire filled hull also lies inside
   `filledHull C₁ \ C₁` (`TauCeti.IsJordanCurve.filledHull_subset_filledHull_sdiff`). Choosing a
   point `p₀ ∈ filledHull C₂ \ C₂` and applying the prescribed-boundary Schoenflies theorem
   (`TauCeti.IsJordanCurve.exists_homeomorph_sphere_eq_of_mem`) to `C₁` at `p₀` reduces to the
   case `C₁ = sphere 0 1`, `C₂ ⊆ ball 0 1`, and `0 ∈ filledHull C₂ \ C₂`.

2. **Two radial crosscuts and two disc decompositions.** Along the positive and negative real rays
   from `0` to `±1`, compactness of `C₂` yields last-hit points `p₁ = t₁` and `p₂ = -t₂` with
   `t₁, t₂ ∈ (0, 1)`. The radial segments `J₁` from `1` to `p₁` and `J₂` from `p₂` to `-1` are
   disjoint and meet `C₂` only at `p₁` and `p₂`. Splitting `C₂` at `p₁, p₂` into arcs `γ₁, γ₂`
   produces a crosscut `κ₁ = (J₁.trans γ₁).trans J₂` of `ball 0 1`, which splits `closedBall 0 1`
   into two closed Jordan domains `D⁺, D⁻`
   (`Path.IsCrosscut.filledHull_union_filledHull_eq_closedBall`). The open arc of `γ₂` is connected
   and avoids `κ₁`, so it lies in the inside of one half, say `D⁻`, where it forms a second
   crosscut splitting `D⁻` into `filledHull C₂` and a remaining four-sided closed Jordan domain
   `D⁻'`. Together `D⁺` and `D⁻'` cover `closedBall 0 1 \ (filledHull C₂ \ C₂)` and meet precisely
   along `range J₁ ∪ range J₂`.

3. **Gluing.** The four-sided Jordan domain theorem
   (`TauCeti.exists_homeomorph_unitInterval_prod_filledHull`) identifies `D⁺` and `D⁻'` with
   `I × I` via maps agreeing identically along the common vertical edges `J₁` and `J₂.symm`.
   Parametrizing the upper and lower semicircles by `u ↦ Real.arccos u.re / Real.pi` glues the two
   squares into the desired homeomorphism
   `sphere (0 : ℂ) 1 × I ≃ₜ ↥(closedBall 0 1 \ (filledHull C₂ \ C₂))`.

## Main results

* `TauCeti.IsJordanCurve.filledHull_subset_filledHull_sdiff`: any subset contained in the inside
  of a Jordan curve has its whole filled hull contained in that inside.
* `TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval_of_homeomorph`: **the planar
  annulus theorem** with prescribed outer boundary parametrization.
* `TauCeti.IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval`: **the planar annulus
  theorem**.

## References

* A. Schoenflies, *Beiträge zur Theorie der Punktmengen. III*, Math. Ann. 62 (1906), 286–328.
* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977), Chapter 10.
-/

public section

noncomputable section

open Function Metric Set Topology unitInterval

namespace TauCeti

/-! ### Standard semicircles on the unit circle -/

section Semicircles

/-- The upper semicircle path from `1` to `-1` in `ℂ`. -/
private def upperSemicircle : Path (1 : ℂ) (-1 : ℂ) :=
  ((Circle.path (1 : Circle) (-1)).map Circle.coordinate.continuous).cast
    (by simp) (by simp)

/-- The lower semicircle path from `1` to `-1` in `ℂ`. -/
private def lowerSemicircle : Path (1 : ℂ) (-1 : ℂ) :=
  ((Circle.path (-1 : Circle) 1).symm.map Circle.coordinate.continuous).cast
    (by simp) (by simp)

private theorem coe_upperSemicircle_eq :
    (upperSemicircle : I → ℂ) = Circle.coordinate ∘ Circle.path (1 : Circle) (-1) := by
  ext t
  simp only [upperSemicircle, Path.cast_coe, Path.map_coe, Function.comp_apply]

private theorem coe_lowerSemicircle_eq :
    (lowerSemicircle : I → ℂ) = Circle.coordinate ∘ (Circle.path (-1 : Circle) 1).symm := by
  ext t
  simp only [lowerSemicircle, Path.cast_coe, Path.map_coe, Function.comp_apply]

private theorem coordinate_injective : Injective Circle.coordinate := fun _ _ h =>
  Circle.coe_injective (by simpa only [Circle.coordinate_apply] using h)

private theorem upperSemicircle_mem_sphere (t : I) : upperSemicircle t ∈ sphere (0 : ℂ) 1 := by
  simp [upperSemicircle]

private theorem lowerSemicircle_mem_sphere (t : I) : lowerSemicircle t ∈ sphere (0 : ℂ) 1 := by
  simp [lowerSemicircle]

private theorem upperSemicircle_apply (t : I) :
    upperSemicircle t = Complex.exp (↑(Real.pi * (t : ℝ)) * Complex.I) := by
  have hval1 : (1 : Circle).val = 1 := rfl
  have hvaln1 : (-1 : Circle).val = -1 := rfl
  have hdiff : Circle.angleDiff 1 (-1) = Real.pi := by
    simp [Circle.angleDiff, hvaln1, Real.pi_pos.le]
  have harg : (t : ℝ) * Real.pi = Real.pi * (t : ℝ) := mul_comm _ _
  rw [coe_upperSemicircle_eq, Function.comp_apply, Circle.path_apply, Circle.coordinate_apply,
    Circle.coe_exp, hdiff, hval1, Complex.arg_one, add_zero, Path.segment_apply,
    AffineMap.lineMap_apply_module, smul_zero, zero_add, smul_eq_mul, harg]

private theorem lowerSemicircle_apply (t : I) :
    lowerSemicircle t = Complex.exp (↑(-(Real.pi * (t : ℝ))) * Complex.I) := by
  have hvaln1 : (-1 : Circle).val = -1 := rfl
  have hdiff : Circle.angleDiff (-1) 1 = Real.pi := by
    simp [Circle.angleDiff, hvaln1, not_le.mpr Real.pi_pos]
    ring
  have harg : (1 - (1 - (t : ℝ))) * Real.pi + (1 - (t : ℝ)) * (Real.pi + Real.pi) =
      2 * Real.pi + -(Real.pi * (t : ℝ)) := by ring
  rw [coe_lowerSemicircle_eq, Function.comp_apply, Path.symm_apply, Function.comp_apply,
    Circle.path_apply, Circle.coordinate_apply, Circle.coe_exp, hdiff, hvaln1, Complex.arg_neg_one,
    Path.segment_apply, AffineMap.lineMap_apply_module, unitInterval.coe_symm_eq, smul_eq_mul,
    smul_eq_mul, harg]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]

private theorem upperSemicircle_im_nonneg (t : I) : 0 ≤ (upperSemicircle t).im := by
  rw [upperSemicircle_apply, Complex.exp_ofReal_mul_I_im]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le t.property.1)
    (mul_le_of_le_one_right Real.pi_pos.le t.property.2)

private theorem lowerSemicircle_im_nonpos (t : I) : (lowerSemicircle t).im ≤ 0 := by
  rw [lowerSemicircle_apply, Complex.exp_ofReal_mul_I_im, Real.sin_neg, Left.neg_nonpos_iff]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le t.property.1)
    (mul_le_of_le_one_right Real.pi_pos.le t.property.2)

private theorem circle_one_ne_neg_one : (1 : Circle) ≠ -1 := by
  intro h
  have : ((1 : Circle) : ℂ) = ((-1 : Circle) : ℂ) := congrArg ((↑) : Circle → ℂ) h
  norm_num at this

private theorem upperSemicircle_injective : Injective upperSemicircle := by
  rw [coe_upperSemicircle_eq]
  exact coordinate_injective.comp (Circle.path_injective_of_ne circle_one_ne_neg_one)

private theorem lowerSemicircle_injective : Injective lowerSemicircle := by
  rw [coe_lowerSemicircle_eq]
  exact coordinate_injective.comp
    (Path.injective_symm_iff.mpr (Circle.path_injective_of_ne circle_one_ne_neg_one.symm))

private theorem range_upperSemicircle_union_lowerSemicircle :
    range upperSemicircle ∪ range lowerSemicircle = sphere (0 : ℂ) 1 := by
  rw [coe_upperSemicircle_eq, coe_lowerSemicircle_eq, range_comp, range_comp, Path.symm_range,
    ← image_union, Circle.range_path_union_range_path circle_one_ne_neg_one, image_univ]
  ext z
  simp only [mem_range, Circle.coordinate_apply]
  exact ⟨fun ⟨w, hw⟩ => hw ▸ mem_sphere_zero_iff_norm.2 w.norm_coe,
    fun hz => ⟨Circle.homeomorphSphere.symm ⟨z, hz⟩, Circle.coe_homeomorphSphere_symm_apply _⟩⟩

private theorem range_upperSemicircle_inter_lowerSemicircle :
    range upperSemicircle ∩ range lowerSemicircle = {1, -1} := by
  rw [coe_upperSemicircle_eq, coe_lowerSemicircle_eq, range_comp, range_comp, Path.symm_range,
    ← image_inter coordinate_injective, Circle.range_path_inter_range_path circle_one_ne_neg_one]
  simp

/-- The semicircle parameter `Real.arccos u.re / Real.pi ∈ I` on the unit circle. -/
private def circleAngleParam (u : sphere (0 : ℂ) 1) : I :=
  ⟨Real.arccos (u : ℂ).re / Real.pi,
    div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le,
    (div_le_one Real.pi_pos).mpr (Real.arccos_le_pi _)⟩

private theorem coe_circleAngleParam (u : sphere (0 : ℂ) 1) :
    (circleAngleParam u : ℝ) = Real.arccos (u : ℂ).re / Real.pi :=
  rfl

private theorem continuous_circleAngleParam : Continuous circleAngleParam := by
  refine Continuous.subtype_mk ?_ _
  exact (Real.continuous_arccos.comp
    (Complex.continuous_re.comp continuous_subtypeVal)).div_const Real.pi

private theorem circleAngleParam_upperSemicircle (t : I) :
    circleAngleParam ⟨upperSemicircle t, upperSemicircle_mem_sphere t⟩ = t := by
  apply Subtype.ext
  rw [coe_circleAngleParam]
  dsimp only
  rw [upperSemicircle_apply, Complex.exp_ofReal_mul_I_re,
    Real.arccos_cos (mul_nonneg Real.pi_pos.le t.property.1)
      (mul_le_of_le_one_right Real.pi_pos.le t.property.2),
    mul_div_cancel_left₀ _ Real.pi_ne_zero]

private theorem circleAngleParam_lowerSemicircle (t : I) :
    circleAngleParam ⟨lowerSemicircle t, lowerSemicircle_mem_sphere t⟩ = t := by
  apply Subtype.ext
  rw [coe_circleAngleParam]
  dsimp only
  rw [lowerSemicircle_apply, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
    Real.arccos_cos (mul_nonneg Real.pi_pos.le t.property.1)
      (mul_le_of_le_one_right Real.pi_pos.le t.property.2),
    mul_div_cancel_left₀ _ Real.pi_ne_zero]

private theorem upperSemicircle_circleAngleParam {u : sphere (0 : ℂ) 1} (hu : 0 ≤ (u : ℂ).im) :
    upperSemicircle (circleAngleParam u) = u := by
  have hsq := Complex.re_sq_add_im_sq_of_mem_sphere u.property
  have himsq : 1 - (u : ℂ).re ^ 2 = (u : ℂ).im ^ 2 := by linarith
  have hre : |(u : ℂ).re| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (u : ℂ).im]
  have hmul : Real.pi * (circleAngleParam u : ℝ) = Real.arccos (u : ℂ).re := by
    rw [coe_circleAngleParam, mul_div_cancel₀ _ Real.pi_ne_zero]
  apply Complex.ext
  · rw [upperSemicircle_apply, hmul, Complex.exp_ofReal_mul_I_re,
      Real.cos_arccos (abs_le.mp hre).1 (abs_le.mp hre).2]
  · rw [upperSemicircle_apply, hmul, Complex.exp_ofReal_mul_I_im, Real.sin_arccos, himsq,
      Real.sqrt_sq hu]

private theorem lowerSemicircle_circleAngleParam {u : sphere (0 : ℂ) 1} (hu : (u : ℂ).im ≤ 0) :
    lowerSemicircle (circleAngleParam u) = u := by
  have hsq := Complex.re_sq_add_im_sq_of_mem_sphere u.property
  have himsq : 1 - (u : ℂ).re ^ 2 = (-(u : ℂ).im) ^ 2 := by linarith
  have hre : |(u : ℂ).re| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (u : ℂ).im]
  have hmul : Real.pi * (circleAngleParam u : ℝ) = Real.arccos (u : ℂ).re := by
    rw [coe_circleAngleParam, mul_div_cancel₀ _ Real.pi_ne_zero]
  apply Complex.ext
  · rw [lowerSemicircle_apply, hmul, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
      Real.cos_arccos (abs_le.mp hre).1 (abs_le.mp hre).2]
  · rw [lowerSemicircle_apply, hmul, Complex.exp_ofReal_mul_I_im, Real.sin_neg, Real.sin_arccos,
      himsq, Real.sqrt_sq (neg_nonneg.mpr hu), neg_neg]

private theorem circleAngleParam_eq_zero_of_coe_eq_one {u : sphere (0 : ℂ) 1} (hu : (u : ℂ) = 1) :
    circleAngleParam u = 0 := by
  apply Subtype.ext
  simp [coe_circleAngleParam, hu]

private theorem circleAngleParam_eq_one_of_coe_eq_neg_one {u : sphere (0 : ℂ) 1}
    (hu : (u : ℂ) = -1) : circleAngleParam u = 1 := by
  apply Subtype.ext
  simp [coe_circleAngleParam, hu]

end Semicircles

/-! ### Normalized planar annulus theorem -/

section Normalized

/-- On either real ray `{s * r | r ≥ 0}` (`s = ±1`), a Jordan curve `C ⊆ ball 0 1` enclosing `0`
has a last intersection point at some radius `t ∈ (0, 1)`. -/
private theorem exists_maximal_real_hit {C : Set ℂ} (hC : IsJordanCurve C)
    (hCb : C ⊆ ball 0 1) (h0 : (0 : ℂ) ∈ filledHull C \ C) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ((s * t : ℝ) : ℂ) ∈ C ∧
      ∀ r : ℝ, t < r → ((s * r : ℝ) : ℂ) ∉ C := by
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  let f : ℝ → ℂ := fun r => ((s * r : ℝ) : ℂ)
  have hfc : Continuous f := by fun_prop
  set S : Set ℝ := {r : ℝ | 0 ≤ r ∧ f r ∈ C}
  have hSsub : S ⊆ Icc 0 1 := by
    intro r hr
    refine ⟨hr.1, ?_⟩
    have hlt : ‖f r‖ < 1 := mem_ball_zero_iff.mp (hCb hr.2)
    have hnorm : ‖f r‖ = r := by
      simp only [f, Complex.norm_real, Real.norm_eq_abs, abs_mul, hsabs, one_mul,
        abs_of_nonneg hr.1]
    linarith
  have hSclosed : IsClosed S := isClosed_Ici.inter (hC.isClosed.preimage hfc)
  have hScomp : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed hSsub
  have hSne : S.Nonempty := by
    have h1not : f 1 ∉ filledHull C := by
      intro hmem
      have hlt : ‖f 1‖ < 1 := mem_ball_zero_iff.mp (hC.isCompact.filledHull_subset_ball hCb hmem)
      simp [f, hsabs] at hlt
    have hconn : IsPreconnected (f '' Icc 0 1) :=
      isPreconnected_Icc.image f hfc.continuousOn
    obtain ⟨z, ⟨r, hr, rfl⟩, hfr⟩ := hconn.inter_frontier_nonempty
      ⟨f 0, mem_image_of_mem f ⟨le_rfl, zero_le_one⟩, by simpa [f] using h0.1⟩
      ⟨f 1, mem_image_of_mem f ⟨zero_le_one, le_rfl⟩, h1not⟩
    rw [hC.frontier_filledHull] at hfr
    exact ⟨r, hr.1, hfr⟩
  obtain ⟨t, htS, htmax⟩ := hScomp.exists_isMaxOn hSne continuous_id.continuousOn
  have htpos : 0 < t := lt_of_le_of_ne htS.1 fun h0t => by
    subst h0t
    exact h0.2 (by simpa [f] using htS.2)
  have htlt : t < 1 := by
    have hlt : ‖f t‖ < 1 := mem_ball_zero_iff.mp (hCb htS.2)
    have hnorm : ‖f t‖ = t := by
      simp only [f, Complex.norm_real, Real.norm_eq_abs, abs_mul, hsabs, one_mul,
        abs_of_nonneg htS.1]
    linarith
  refine ⟨t, htpos, htlt, htS.2, fun r hr hmem => ?_⟩
  have hle : r ≤ t := htmax ⟨htpos.le.trans hr.le, hmem⟩
  linarith

/-- Second crosscut decomposition: given the first crosscut `κ₁ = (J₁.trans γ₁).trans J₂` splitting
`closedBall 0 1` into `Dₐ` (bounded by `κ₁` and `σₐ`) and `D_b` (bounded by `κ₁` and `σ_b`), if the
open arc `γ₂ '' Ioo 0 1` lies inside the open domain `W_b = D_b \ (range κ₁ ∪ range σ_b)`, then
cutting `W_b` along `γ₂` isolates `filledHull C` from the complementary four-sided domain `D_b'`, so
that `Dₐ` and `D_b'` cover `closedBall 0 1 \ (filledHull C \ C)` and meet precisely along
`range J₁ ∪ range J₂`. -/
private theorem split_second_half {C : Set ℂ} {p₁ p₂ : ℂ}
    {J₁ : Path (1 : ℂ) p₁} {J₂ : Path p₂ (-1 : ℂ)}
    {γ₁ γ₂ : Path p₁ p₂} {σₐ σ_b : Path (1 : ℂ) (-1 : ℂ)}
    (hJ₁ : Injective J₁) (hJ₂ : Injective J₂)
    (hγ₁ : Injective γ₁) (hγ₂ : Injective γ₂)
    (hσₐ : Injective σₐ) (hσ_b : Injective σ_b)
    (hJ₁J₂ : Disjoint (range J₁) (range J₂))
    (hJ₁C : range J₁ ∩ C = {p₁}) (hJ₂C : range J₂ ∩ C = {p₂})
    (hJ₁S : range J₁ ∩ sphere 0 1 = {1}) (hJ₂S : range J₂ ∩ sphere 0 1 = {-1})
    (hCb : C ⊆ ball 0 1)
    (hγu : range γ₁ ∪ range γ₂ = C) (hγi : range γ₁ ∩ range γ₂ = {p₁, p₂})
    (hσu : range σₐ ∪ range σ_b = sphere 0 1) (hσi : range σₐ ∩ range σ_b = {1, -1})
    (hκcut : ((J₁.trans γ₁).trans J₂).IsCrosscut (ball 0 1))
    (hγ₂in : γ₂ '' Ioo 0 1 ⊆
      filledHull (range ((J₁.trans γ₁).trans J₂) ∪ range σ_b) \
        (range ((J₁.trans γ₁).trans J₂) ∪ range σ_b)) :
    let Aₐ := filledHull (range σₐ ∪ range γ₁ ∪ range J₁ ∪ range J₂.symm)
    let A_b := filledHull (range σ_b ∪ range γ₂ ∪ range J₁ ∪ range J₂.symm)
    Aₐ ∪ A_b = closedBall 0 1 \ (filledHull C \ C) ∧
      Aₐ ∩ A_b = range J₁ ∪ range J₂ := by
  set κ₁ : Path (1 : ℂ) (-1 : ℂ) := (J₁.trans γ₁).trans J₂
  have hκ₁_range : range κ₁ = range J₁ ∪ range γ₁ ∪ range J₂ := by
    simp [κ₁, Path.trans_range]
  have hσₐS : range σₐ ⊆ sphere 0 1 := hσu ▸ subset_union_left
  have hσ_bS : range σ_b ⊆ sphere 0 1 := hσu ▸ subset_union_right
  have hγ₁C : range γ₁ ⊆ C := hγu ▸ subset_union_left
  have hγ₂C : range γ₂ ⊆ C := hγu ▸ subset_union_right
  -- First decomposition: `closedBall 0 1 = Dₐ ∪ D_b` with `Dₐ ∩ D_b = range κ₁`.
  set Jₐ : Set ℂ := range κ₁ ∪ range σₐ
  set J_b : Set ℂ := range κ₁ ∪ range σ_b
  have hJ_b_curve : IsJordanCurve J_b :=
    hκcut.isJordanCurve_range_union_range_of_subset_sphere hσ_b hσ_bS
  have hD_union : filledHull Jₐ ∪ filledHull J_b = closedBall 0 1 :=
    hκcut.filledHull_union_filledHull_eq_closedBall hσₐ hσ_b hσₐS hσ_bS hσi
  have hD_inter : filledHull Jₐ ∩ filledHull J_b = range κ₁ :=
    hκcut.filledHull_inter_filledHull_eq_range_of_subset_sphere hσₐ hσ_b hσₐS hσ_bS hσi
  -- `γ₂` is a crosscut of the open Jordan domain `W_b = filledHull J_b \ J_b`.
  set W_b : Set ℂ := filledHull J_b \ J_b
  have hW_open : IsOpen W_b := hJ_b_curve.isClosed.isOpen_filledHull_sdiff
  have hW_bdd : Bornology.IsBounded W_b :=
    (isBounded_filledHull.mpr hJ_b_curve.isCompact.isBounded).subset sdiff_subset
  have hW_fr : frontier W_b = J_b := hJ_b_curve.frontier_filledHull_sdiff
  have hW_cl : closure W_b = filledHull J_b := hJ_b_curve.closure_filledHull_sdiff
  have hW_frJ : IsJordanCurve (frontier W_b) := hW_fr.symm ▸ hJ_b_curve
  have hp₁Jb : p₁ ∈ J_b := Or.inl (hκ₁_range ▸ Or.inl (Or.inr γ₁.source_mem_range))
  have hp₂Jb : p₂ ∈ J_b := Or.inl (hκ₁_range ▸ Or.inl (Or.inr γ₁.target_mem_range))
  have hγ₂_cut : γ₂.IsCrosscut W_b := Path.isCrosscut_def.mpr
    ⟨hγ₂, hW_fr.symm ▸ hp₁Jb, hW_fr.symm ▸ hp₂Jb, fun t ht => hγ₂in (mem_image_of_mem γ₂ ht)⟩
  -- Build the complementary boundary path `β₂ = (J₁.symm.trans σ_b).trans J₂.symm` of `W_b`.
  have hJ₁_σb : range J₁.symm ∩ range σ_b = {1} := by
    rw [Path.symm_range]
    refine Subset.antisymm ((inter_subset_inter_right _ hσ_bS).trans hJ₁S.subset) ?_
    rintro z rfl
    exact ⟨J₁.source_mem_range, σ_b.source_mem_range⟩
  have hJ₁σb_inj : Injective (J₁.symm.trans σ_b) :=
    Path.injective_trans (Path.injective_symm_iff.mpr hJ₁) hσ_b hJ₁_σb
  have hJ₁σb_J₂ : range (J₁.symm.trans σ_b) ∩ range J₂.symm = {-1} := by
    rw [Path.trans_range, Path.symm_range, Path.symm_range, union_inter_distrib_right,
      hJ₁J₂.inter_eq, empty_union]
    refine Subset.antisymm ?_ ?_
    · rw [inter_comm]
      exact (inter_subset_inter_right _ hσ_bS).trans hJ₂S.subset
    · rintro z rfl
      exact ⟨σ_b.target_mem_range, J₂.target_mem_range⟩
  set β₂ : Path p₁ p₂ := (J₁.symm.trans σ_b).trans J₂.symm
  have hβ₂_inj : Injective β₂ :=
    Path.injective_trans hJ₁σb_inj (Path.injective_symm_iff.mpr hJ₂) hJ₁σb_J₂
  have hβ₂_range : range β₂ = range J₁ ∪ range σ_b ∪ range J₂ := by
    simp [β₂, Path.trans_range]
  have hγ₁_fr : range γ₁ ⊆ frontier W_b := by
    rintro z hz
    rw [hW_fr]
    exact Or.inl (hκ₁_range ▸ Or.inl (Or.inr hz))
  have hβ₂_fr : range β₂ ⊆ frontier W_b := by
    rw [hW_fr, hβ₂_range]
    rintro z ((hz | hz) | hz)
    · exact Or.inl (hκ₁_range ▸ Or.inl (Or.inl hz))
    · exact Or.inr hz
    · exact Or.inl (hκ₁_range ▸ Or.inr hz)
  have hγ₁_β₂ : range γ₁ ∩ range β₂ = {p₁, p₂} := by
    rw [hβ₂_range]
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨hz₁, ((hz | hz) | hz)⟩
      · exact Or.inl (mem_singleton_iff.mp (hJ₁C ▸ ⟨hz, hγ₁C hz₁⟩))
      · exact (sphere_disjoint_ball.notMem_of_mem_left (hσ_bS hz)
          (hCb (hγ₁C hz₁))).elim
      · exact Or.inr (mem_singleton_iff.mp (hJ₂C ▸ ⟨hz, hγ₁C hz₁⟩))
    · rintro z (rfl | rfl)
      · exact ⟨γ₁.source_mem_range, Or.inl (Or.inl J₁.target_mem_range)⟩
      · exact ⟨γ₁.target_mem_range, Or.inr J₂.source_mem_range⟩
  -- Apply the second crosscut decomposition to `W_b` along `γ₂`.
  have hC_eq : range γ₂ ∪ range γ₁ = C := by rw [union_comm, hγu]
  have hD_b_union : filledHull C ∪ filledHull (range γ₂ ∪ range β₂) = filledHull J_b := by
    rw [← hC_eq, ← hW_cl]
    exact hγ₂_cut.filledHull_union_filledHull_eq_closure hW_open hW_bdd hW_frJ hγ₁ hβ₂_inj
      hγ₁_fr hβ₂_fr hγ₁_β₂
  have hD_b_inter : filledHull C ∩ filledHull (range γ₂ ∪ range β₂) = range γ₂ := by
    rw [← hC_eq]
    exact hγ₂_cut.filledHull_inter_filledHull_eq_range hW_open hW_bdd hW_frJ hγ₁ hβ₂_inj
      hγ₁_fr hβ₂_fr hγ₁_β₂
  have hC_inside : filledHull C \ C ⊆ W_b := by
    rw [← hC_eq]
    exact (hγ₂_cut.filledHull_sdiff_subset hW_open hW_bdd hW_frJ hγ₁_fr).trans sdiff_subset
  -- Rewrite the boundary unions to match `Aₐ` and `A_b`.
  have hJₐ_eq : Jₐ = range σₐ ∪ range γ₁ ∪ range J₁ ∪ range J₂.symm := by
    simp only [Jₐ, hκ₁_range, Path.symm_range]
    ext z; simp only [mem_union]; tauto
  have hJ_b'_eq : range γ₂ ∪ range β₂ = range σ_b ∪ range γ₂ ∪ range J₁ ∪ range J₂.symm := by
    simp only [hβ₂_range, Path.symm_range]
    ext z; simp only [mem_union]; tauto
  dsimp only
  rw [← hJₐ_eq, ← hJ_b'_eq]
  have hDb'_sub : filledHull (range γ₂ ∪ range β₂) ⊆ filledHull J_b :=
    hD_b_union ▸ subset_union_right
  constructor
  · refine Subset.antisymm ?_ ?_
    · refine union_subset ?_ ?_
      · intro z hz
        refine ⟨hD_union ▸ Or.inl hz, fun hzC => ?_⟩
        have hzW : z ∈ W_b := hC_inside hzC
        have hzκ : z ∈ range κ₁ := hD_inter ▸ ⟨hz, hzW.1⟩
        exact hzW.2 (Or.inl hzκ)
      · intro z hz
        refine ⟨hD_union ▸ Or.inr (hDb'_sub hz), fun hzC => ?_⟩
        have hzγ₂ : z ∈ range γ₂ := hD_b_inter ▸ ⟨hzC.1, hz⟩
        exact hzC.2 (hγ₂C hzγ₂)
    · intro z ⟨hzCB, hznot⟩
      rcases hD_union.symm.subset hzCB with hzA | hzB
      · exact Or.inl hzA
      · rcases hD_b_union.symm.subset hzB with hzC | hzB'
        · have hzCmem : z ∈ C := by
            by_contra h
            exact hznot ⟨hzC, h⟩
          rcases hγu.symm.subset hzCmem with hz1 | hz2
          · exact Or.inl (subset_filledHull (Or.inl (hκ₁_range ▸ Or.inl (Or.inr hz1))))
          · exact Or.inr (subset_filledHull (Or.inl hz2))
        · exact Or.inr hzB'
  · refine Subset.antisymm ?_ ?_
    · intro z ⟨hzA, hzB'⟩
      have hzκ : z ∈ range κ₁ := hD_inter ▸ ⟨hzA, hDb'_sub hzB'⟩
      rw [hκ₁_range] at hzκ
      rcases hzκ with (hzJ₁ | hzγ₁) | hzJ₂
      · exact Or.inl hzJ₁
      · have hzγ₂ : z ∈ range γ₂ := hD_b_inter ▸ ⟨subset_filledHull (hγ₁C hzγ₁), hzB'⟩
        rcases (hγi ▸ ⟨hzγ₁, hzγ₂⟩ : z ∈ ({p₁, p₂} : Set ℂ)) with rfl | rfl
        · exact Or.inl J₁.target_mem_range
        · exact Or.inr J₂.source_mem_range
      · exact Or.inr hzJ₂
    · rintro z (hz | hz)
      · exact ⟨subset_filledHull (Or.inl (hκ₁_range ▸ Or.inl (Or.inl hz))),
          subset_filledHull (Or.inr (hβ₂_range ▸ Or.inl (Or.inl hz)))⟩
      · exact ⟨subset_filledHull (Or.inl (hκ₁_range ▸ Or.inr hz)),
          subset_filledHull (Or.inr (hβ₂_range ▸ Or.inr hz))⟩

/-- Gluing two four-sided parametrizations `Φp, Φm : I × I ≃ₜ Ap, Am` that agree on the common
vertical edges `J₁` and `J₂.symm` and map the top edges to the upper and lower semicircles yields a
homeomorphism `sphere (0 : ℂ) 1 × I ≃ₜ ↥(Ap ∪ Am)`. -/
private theorem glue_upper_lower_squares {C : Set ℂ} {p₁ p₂ : ℂ}
    {J₁ : Path (1 : ℂ) p₁} {J₂ : Path p₂ (-1 : ℂ)} {αp αm : Path p₁ p₂}
    {Ap Am : Set ℂ}
    (hαu : range αp ∪ range αm = C)
    (hA_union : Ap ∪ Am = closedBall 0 1 \ (filledHull C \ C))
    (hA_inter : Ap ∩ Am = range J₁ ∪ range J₂)
    (Φp : I × I ≃ₜ Ap) (Φm : I × I ≃ₜ Am)
    (hΦp_top : ∀ s : I, (Φp (s, 0) : ℂ) = upperSemicircle s)
    (hΦp_bot : ∀ s : I, (Φp (s, 1) : ℂ) = αp s)
    (hΦp_left : ∀ t : I, (Φp (0, t) : ℂ) = J₁ t)
    (hΦp_right : ∀ t : I, (Φp (1, t) : ℂ) = J₂.symm t)
    (hΦm_top : ∀ s : I, (Φm (s, 0) : ℂ) = lowerSemicircle s)
    (hΦm_bot : ∀ s : I, (Φm (s, 1) : ℂ) = αm s)
    (hΦm_left : ∀ t : I, (Φm (0, t) : ℂ) = J₁ t)
    (hΦm_right : ∀ t : I, (Φm (1, t) : ℂ) = J₂.symm t) :
    ∃ Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(closedBall (0 : ℂ) 1 \ (filledHull C \ C)),
      (∀ u : sphere (0 : ℂ) 1, (Φ (u, 0) : ℂ) = u) ∧
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {1}) = C := by
  have hαpC : range αp ⊆ C := hαu ▸ subset_union_left
  have hαmC : range αm ⊆ C := hαu ▸ subset_union_right
  let H : sphere (0 : ℂ) 1 × I → ℂ := fun p =>
    if 0 ≤ (p.1 : ℂ).im then (Φp (circleAngleParam p.1, p.2) : ℂ)
    else (Φm (circleAngleParam p.1, p.2) : ℂ)
  have hH_agree {u : sphere (0 : ℂ) 1} (hu : (u : ℂ).im = 0) (t : I) :
      (Φp (circleAngleParam u, t) : ℂ) = (Φm (circleAngleParam u, t) : ℂ) := by
    rcases (Circle.im_coe_eq_zero_iff (Circle.homeomorphSphere.symm u)).mp (by simpa using hu) with
      h1 | h1
    · have hu1 : (u : ℂ) = 1 := by simpa using congrArg ((↑) : Circle → ℂ) h1
      rw [circleAngleParam_eq_zero_of_coe_eq_one hu1, hΦp_left, hΦm_left]
    · have hu1 : (u : ℂ) = -1 := by simpa using congrArg ((↑) : Circle → ℂ) h1
      rw [circleAngleParam_eq_one_of_coe_eq_neg_one hu1, hΦp_right, hΦm_right]
  have hH_upper {u : sphere (0 : ℂ) 1} (hu : 0 ≤ (u : ℂ).im) (t : I) :
      H (u, t) = (Φp (circleAngleParam u, t) : ℂ) := by
    simp [H, hu]
  have hH_lower {u : sphere (0 : ℂ) 1} (hu : (u : ℂ).im ≤ 0) (t : I) :
      H (u, t) = (Φm (circleAngleParam u, t) : ℂ) := by
    rcases hu.eq_or_lt with h0 | hlt
    · simp [H, h0, hH_agree h0]
    · simp [H, not_le.mpr hlt]
  have hH_cont : Continuous H := by
    have h1 : Continuous fun p : sphere (0 : ℂ) 1 × I =>
        (Φp (circleAngleParam p.1, p.2) : ℂ) :=
      continuous_subtypeVal.comp (Φp.continuous.comp
        ((continuous_circleAngleParam.comp continuous_fst).prodMk continuous_snd))
    have h2 : Continuous fun p : sphere (0 : ℂ) 1 × I =>
        (Φm (circleAngleParam p.1, p.2) : ℂ) :=
      continuous_subtypeVal.comp (Φm.continuous.comp
        ((continuous_circleAngleParam.comp continuous_fst).prodMk continuous_snd))
    exact continuous_if_le continuous_const
      (Complex.continuous_im.comp (continuous_subtypeVal.comp continuous_fst))
      h1.continuousOn h2.continuousOn fun p hp => hH_agree hp.symm p.2
  have hH_inj : Injective H := by
    rintro ⟨u₁, t₁⟩ ⟨u₂, t₂⟩ heq
    have hcross {u v : sphere (0 : ℂ) 1} {tu tv : I} (hv : (v : ℂ).im < 0)
        (h : (Φp (circleAngleParam u, tu) : ℂ) = (Φm (circleAngleParam v, tv) : ℂ)) : False := by
      have hmem : (Φm (circleAngleParam v, tv) : ℂ) ∈ Ap ∩ Am :=
        ⟨h ▸ (Φp (circleAngleParam u, tu)).property, (Φm (circleAngleParam v, tv)).property⟩
      rw [hA_inter] at hmem
      rcases hmem with ⟨t, ht⟩ | ⟨t, ht⟩
      · have hΦ : Φm (circleAngleParam v, tv) = Φm (0, t) := Subtype.ext (by rw [hΦm_left, ht])
        have hs0 : circleAngleParam v = 0 := congrArg Prod.fst (Φm.injective hΦ)
        have hv1 : (v : ℂ) = 1 := by
          rw [← lowerSemicircle_circleAngleParam hv.le, hs0, lowerSemicircle.source]
        have : (v : ℂ).im = 0 := by simp [hv1]
        linarith
      · have hΦ : Φm (circleAngleParam v, tv) = Φm (1, unitInterval.symm t) :=
          Subtype.ext (by rw [hΦm_right, Path.symm_apply, Function.comp_apply,
            unitInterval.symm_symm, ht])
        have hs1 : circleAngleParam v = 1 := congrArg Prod.fst (Φm.injective hΦ)
        have hv1 : (v : ℂ) = -1 := by
          rw [← lowerSemicircle_circleAngleParam hv.le, hs1, lowerSemicircle.target]
        have : (v : ℂ).im = 0 := by simp [hv1]
        linarith
    by_cases h1 : 0 ≤ (u₁ : ℂ).im <;> by_cases h2 : 0 ≤ (u₂ : ℂ).im
    · rw [hH_upper h1, hH_upper h2] at heq
      obtain ⟨hu_ang, ht⟩ := Prod.mk.inj (Φp.injective (Subtype.ext heq))
      have hu : u₁ = u₂ := Subtype.ext <| by
        rw [← upperSemicircle_circleAngleParam h1, ← upperSemicircle_circleAngleParam h2, hu_ang]
      exact Prod.ext hu ht
    · rw [hH_upper h1, hH_lower (not_le.mp h2).le] at heq
      exact (hcross (not_le.mp h2) heq).elim
    · rw [hH_lower (not_le.mp h1).le, hH_upper h2] at heq
      exact (hcross (not_le.mp h1) heq.symm).elim
    · rw [hH_lower (not_le.mp h1).le, hH_lower (not_le.mp h2).le] at heq
      obtain ⟨hu_ang, ht⟩ := Prod.mk.inj (Φm.injective (Subtype.ext heq))
      have hu : u₁ = u₂ := Subtype.ext <| by
        rw [← lowerSemicircle_circleAngleParam (not_le.mp h1).le,
          ← lowerSemicircle_circleAngleParam (not_le.mp h2).le, hu_ang]
      exact Prod.ext hu ht
  have hH_range : range H = closedBall (0 : ℂ) 1 \ (filledHull C \ C) := by
    rw [← hA_union]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨u, t⟩, rfl⟩
      by_cases hu : 0 ≤ (u : ℂ).im
      · rw [hH_upper hu]; exact Or.inl (Φp _).property
      · rw [hH_lower (not_le.mp hu).le]; exact Or.inr (Φm _).property
    · rintro z (hz | hz)
      · obtain ⟨⟨s, t⟩, hst⟩ := Φp.surjective ⟨z, hz⟩
        refine ⟨(⟨upperSemicircle s, upperSemicircle_mem_sphere s⟩, t), ?_⟩
        rw [hH_upper (u := ⟨upperSemicircle s, _⟩) (upperSemicircle_im_nonneg s),
          circleAngleParam_upperSemicircle]
        exact congrArg Subtype.val hst
      · obtain ⟨⟨s, t⟩, hst⟩ := Φm.surjective ⟨z, hz⟩
        refine ⟨(⟨lowerSemicircle s, lowerSemicircle_mem_sphere s⟩, t), ?_⟩
        rw [hH_lower (u := ⟨lowerSemicircle s, _⟩) (lowerSemicircle_im_nonpos s),
          circleAngleParam_lowerSemicircle]
        exact congrArg Subtype.val hst
  have hH_emb : IsEmbedding H := (hH_cont.isClosedEmbedding hH_inj).isEmbedding
  let Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(closedBall (0 : ℂ) 1 \ (filledHull C \ C)) :=
    hH_emb.toHomeomorph.trans (Homeomorph.setCongr hH_range)
  have hΦ_coe (p : sphere (0 : ℂ) 1 × I) : (Φ p : ℂ) = H p := rfl
  refine ⟨Φ, ?_, ?_⟩
  · intro u
    rw [hΦ_coe]
    rcases le_total 0 (u : ℂ).im with hu | hu
    · rw [hH_upper hu, hΦp_top, upperSemicircle_circleAngleParam hu]
    · rw [hH_lower hu, hΦm_top, lowerSemicircle_circleAngleParam hu]
  · refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨u, t⟩, ⟨-, ht⟩, rfl⟩
      rw [mem_singleton_iff] at ht; subst ht
      dsimp only
      rw [hΦ_coe]
      rcases le_total 0 (u : ℂ).im with hu | hu
      · rw [hH_upper hu, hΦp_bot]; exact hαpC (mem_range_self _)
      · rw [hH_lower hu, hΦm_bot]; exact hαmC (mem_range_self _)
    · intro z hz
      rcases hαu.symm.subset hz with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · refine ⟨(⟨upperSemicircle s, upperSemicircle_mem_sphere s⟩, 1), ⟨trivial, rfl⟩, ?_⟩
        dsimp only
        rw [hΦ_coe, hH_upper (u := ⟨upperSemicircle s, _⟩) (upperSemicircle_im_nonneg s),
          circleAngleParam_upperSemicircle, hΦp_bot]
      · refine ⟨(⟨lowerSemicircle s, lowerSemicircle_mem_sphere s⟩, 1), ⟨trivial, rfl⟩, ?_⟩
        dsimp only
        rw [hΦ_coe, hH_lower (u := ⟨lowerSemicircle s, _⟩) (lowerSemicircle_im_nonpos s),
          circleAngleParam_lowerSemicircle, hΦm_bot]

/-- **Normalized planar annulus theorem.** If `C ⊆ ball (0 : ℂ) 1` is a Jordan curve with
`0 ∈ filledHull C \ C`, then `closedBall (0 : ℂ) 1 \ (filledHull C \ C)` is homeomorphic to
`sphere (0 : ℂ) 1 × I` by a homeomorphism fixing the outer boundary `sphere (0 : ℂ) 1` pointwise at
`t = 0` and carrying `sphere (0 : ℂ) 1 × {1}` onto `C`. -/
private theorem exists_homeomorph_sphere_prod_unitInterval_normalized {C : Set ℂ}
    (hC : IsJordanCurve C) (hCb : C ⊆ ball 0 1) (h0 : (0 : ℂ) ∈ filledHull C \ C) :
    ∃ Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(closedBall (0 : ℂ) 1 \ (filledHull C \ C)),
      (∀ u : sphere (0 : ℂ) 1, (Φ (u, 0) : ℂ) = u) ∧
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {1}) = C := by
  -- Step 1: Two disjoint radial segments `J₁` and `J₂` joining `±1` to `C`.
  obtain ⟨t₁, ht₁pos, ht₁lt, hp₁C, ht₁max⟩ := exists_maximal_real_hit hC hCb h0 (Or.inl rfl)
  obtain ⟨t₂, ht₂pos, ht₂lt, hp₂C, ht₂max⟩ := exists_maximal_real_hit hC hCb h0 (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at hp₁C ht₁max hp₂C ht₂max
  set p₁ : ℂ := (t₁ : ℂ)
  set p₂ : ℂ := ((-t₂ : ℝ) : ℂ)
  have hp₁ne : (1 : ℂ) ≠ p₁ := fun h => ht₁lt.ne (by simpa [p₁] using congrArg Complex.re h.symm)
  have hp₂ne : p₂ ≠ (-1 : ℂ) := fun h => ht₂lt.ne (by
    have := congrArg Complex.re h; simp [p₂] at this; linarith)
  have hp₁₂ : p₁ ≠ p₂ := fun h => by
    have := congrArg Complex.re h; simp [p₁, p₂] at this; linarith
  set J₁ : Path (1 : ℂ) p₁ := Path.segment 1 p₁
  set J₂ : Path p₂ (-1 : ℂ) := Path.segment p₂ (-1)
  have hJ₁_inj : Injective J₁ := Path.segment_injective_of_ne hp₁ne
  have hJ₂_inj : Injective J₂ := Path.segment_injective_of_ne hp₂ne
  have hJ₁_eval (t : I) : J₁ t = (((1 - (t : ℝ)) + (t : ℝ) * t₁ : ℝ) : ℂ) := by
    simp [J₁, Path.segment, AffineMap.lineMap_apply, p₁]; ring
  have hJ₂_eval (t : I) : J₂ t = ((-((1 - (t : ℝ)) * t₂ + (t : ℝ)) : ℝ) : ℂ) := by
    simp [J₂, Path.segment, AffineMap.lineMap_apply, p₂]; ring
  have hJ₁_re {z : ℂ} (hz : z ∈ range J₁) : t₁ ≤ z.re := by
    rcases hz with ⟨t, rfl⟩
    rw [hJ₁_eval, Complex.ofReal_re]; nlinarith [t.property.1, t.property.2]
  have hJ₂_re {z : ℂ} (hz : z ∈ range J₂) : z.re ≤ -t₂ := by
    rcases hz with ⟨t, rfl⟩
    rw [hJ₂_eval, Complex.ofReal_re]; nlinarith [t.property.1, t.property.2]
  have hJ₁J₂ : Disjoint (range J₁) (range J₂) :=
    Set.disjoint_left.mpr fun _ hz₁ hz₂ => by linarith [hJ₁_re hz₁, hJ₂_re hz₂]
  have hJ₁C : range J₁ ∩ C = {p₁} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨J₁.target_mem_range, hp₁C⟩)
    rintro z ⟨⟨t, rfl⟩, hzC⟩
    rw [mem_singleton_iff]
    by_cases ht1 : (t : ℝ) = 1
    · have : t = 1 := Subtype.ext ht1
      subst this; exact J₁.target
    · have hgt : t₁ < (1 - (t : ℝ)) + (t : ℝ) * t₁ := by
        have : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht1
        nlinarith
      exact (ht₁max _ hgt (hJ₁_eval t ▸ hzC)).elim
  have hJ₂C : range J₂ ∩ C = {p₂} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨J₂.source_mem_range, hp₂C⟩)
    rintro z ⟨⟨t, rfl⟩, hzC⟩
    rw [mem_singleton_iff]
    by_cases ht0 : (t : ℝ) = 0
    · have : t = 0 := Subtype.ext ht0
      subst this; exact J₂.source
    · have hgt : t₂ < (1 - (t : ℝ)) * t₂ + (t : ℝ) := by
        have : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht0)
        nlinarith
      exact (ht₂max _ hgt (hJ₂_eval t ▸ hzC)).elim
  have hJ₁_cb : range J₁ ⊆ closedBall 0 1 := by
    rintro z ⟨t, rfl⟩
    rw [mem_closedBall_zero_iff, hJ₁_eval, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [t.property.1, t.property.2]
  have hJ₂_cb : range J₂ ⊆ closedBall 0 1 := by
    rintro z ⟨t, rfl⟩
    rw [mem_closedBall_zero_iff, hJ₂_eval, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [t.property.1, t.property.2]
  have hJ₁S : range J₁ ∩ sphere 0 1 = {1} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨J₁.source_mem_range, by simp⟩)
    rintro z ⟨⟨t, rfl⟩, hzS⟩
    rw [mem_sphere_zero_iff_norm, hJ₁_eval, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [t.property.1, t.property.2])] at hzS
    have ht0 : t = 0 := Subtype.ext (by nlinarith : (t : ℝ) = 0)
    subst ht0
    exact mem_singleton_iff.mpr J₁.source
  have hJ₂S : range J₂ ∩ sphere 0 1 = {-1} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨J₂.target_mem_range, by simp⟩)
    rintro z ⟨⟨t, rfl⟩, hzS⟩
    rw [mem_sphere_zero_iff_norm, hJ₂_eval, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by nlinarith [t.property.1, t.property.2])] at hzS
    have ht1 : t = 1 := Subtype.ext (by nlinarith : (t : ℝ) = 1)
    subst ht1
    exact mem_singleton_iff.mpr J₂.target
  -- Step 2: Split `C` at `p₁, p₂` into `γ₁, γ₂` and form the crosscut `κ₁ = J₁ · γ₁ · J₂`.
  obtain ⟨γ₁, γ₂, hγ₁_inj, hγ₂_inj, hγu, hγi⟩ :=
    hC.exists_injective_path_range_union_eq_and_inter_eq_pair hp₁C hp₂C hp₁₂
  have hγ₁C : range γ₁ ⊆ C := hγu ▸ subset_union_left
  have hγ₂C : range γ₂ ⊆ C := hγu ▸ subset_union_right
  have hJ₁γ₁ : range J₁ ∩ range γ₁ = {p₁} := by
    refine Subset.antisymm ((inter_subset_inter_right _ hγ₁C).trans hJ₁C.subset) ?_
    exact singleton_subset_iff.mpr ⟨J₁.target_mem_range, γ₁.source_mem_range⟩
  have hJ₁γ₁_inj : Injective (J₁.trans γ₁) := Path.injective_trans hJ₁_inj hγ₁_inj hJ₁γ₁
  have hJ₁γ₁_J₂ : range (J₁.trans γ₁) ∩ range J₂ = {p₂} := by
    rw [Path.trans_range, union_inter_distrib_right, hJ₁J₂.inter_eq, empty_union]
    refine Subset.antisymm ?_
      (singleton_subset_iff.mpr ⟨γ₁.target_mem_range, J₂.source_mem_range⟩)
    rw [inter_comm]
    exact (inter_subset_inter_right _ hγ₁C).trans hJ₂C.subset
  set κ₁ : Path (1 : ℂ) (-1 : ℂ) := (J₁.trans γ₁).trans J₂
  have hκ₁_inj : Injective κ₁ := Path.injective_trans hJ₁γ₁_inj hJ₂_inj hJ₁γ₁_J₂
  have hκ₁_range : range κ₁ = range J₁ ∪ range γ₁ ∪ range J₂ := by simp [κ₁, Path.trans_range]
  have hfr_ball : frontier (ball (0 : ℂ) 1) = sphere (0 : ℂ) 1 := frontier_ball 0 one_ne_zero
  have hκ₁_cut : κ₁.IsCrosscut (ball 0 1) := Path.isCrosscut_def.mpr
    ⟨hκ₁_inj, by rw [hfr_ball]; simp, by rw [hfr_ball]; simp, fun t ht => by
      have hcb : κ₁ t ∈ closedBall (0 : ℂ) 1 := by
        rcases (hκ₁_range ▸ mem_range_self t :
          κ₁ t ∈ range J₁ ∪ range γ₁ ∪ range J₂) with (h | h) | h
        · exact hJ₁_cb h
        · exact ball_subset_closedBall (hCb (hγ₁C h))
        · exact hJ₂_cb h
      have hnotS : κ₁ t ∉ sphere (0 : ℂ) 1 := by
        intro hS
        rcases (hκ₁_range ▸ mem_range_self t :
          κ₁ t ∈ range J₁ ∪ range γ₁ ∪ range J₂) with (h | h) | h
        · have h1 : κ₁ t = κ₁ 0 := (mem_singleton_iff.mp (hJ₁S ▸ ⟨h, hS⟩)).trans κ₁.source.symm
          exact ht.1.ne' (hκ₁_inj h1)
        · exact sphere_disjoint_ball.notMem_of_mem_left hS (hCb (hγ₁C h))
        · have h1 : κ₁ t = κ₁ 1 := (mem_singleton_iff.mp (hJ₂S ▸ ⟨h, hS⟩)).trans κ₁.target.symm
          exact ht.2.ne (hκ₁_inj h1)
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp hcb)
        (by simpa [mem_sphere_zero_iff_norm] using hnotS)⟩
  -- Step 3: Locate `γ₂ '' Ioo 0 1` on one side of `κ₁`, and split that side along `γ₂`.
  have hσpS : range upperSemicircle ⊆ sphere 0 1 := range_subset_iff.mpr upperSemicircle_mem_sphere
  have hσmS : range lowerSemicircle ⊆ sphere 0 1 := range_subset_iff.mpr lowerSemicircle_mem_sphere
  obtain ⟨hWdisj, hWunion⟩ := hκ₁_cut.disjoint_and_union_filledHull_sdiff isOpen_ball isBounded_ball
    (hfr_ball.symm ▸ isJordanCurve_sphere 0 one_pos) upperSemicircle_injective
    lowerSemicircle_injective (hfr_ball.symm ▸ hσpS) (hfr_ball.symm ▸ hσmS)
    range_upperSemicircle_inter_lowerSemicircle
  have hJp_curve : IsJordanCurve (range κ₁ ∪ range upperSemicircle) :=
    hκ₁_cut.isJordanCurve_range_union_range_of_subset_sphere upperSemicircle_injective hσpS
  have hJm_curve : IsJordanCurve (range κ₁ ∪ range lowerSemicircle) :=
    hκ₁_cut.isJordanCurve_range_union_range_of_subset_sphere lowerSemicircle_injective hσmS
  have hγ₂_open_sub : γ₂ '' Ioo 0 1 ⊆ ball 0 1 \ range κ₁ := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨hCb (hγ₂C (mem_range_self t)), fun hmem => ?_⟩
    rw [hκ₁_range] at hmem
    rcases hmem with (h | h) | h
    · have h1 : γ₂ t = γ₂ 0 :=
        (mem_singleton_iff.mp (hJ₁C ▸ ⟨h, hγ₂C (mem_range_self t)⟩)).trans γ₂.source.symm
      exact ht.1.ne' (hγ₂_inj h1)
    · rcases (hγi ▸ ⟨h, mem_range_self t⟩ : γ₂ t ∈ ({p₁, p₂} : Set ℂ)) with h1 | h2
      · exact ht.1.ne' (hγ₂_inj (h1.trans γ₂.source.symm))
      · exact ht.2.ne (hγ₂_inj (h2.trans γ₂.target.symm))
    · have h2 : γ₂ t = γ₂ 1 :=
        (mem_singleton_iff.mp (hJ₂C ▸ ⟨h, hγ₂C (mem_range_self t)⟩)).trans γ₂.target.symm
      exact ht.2.ne (hγ₂_inj h2)
  have hγ₂_conn : IsPreconnected (γ₂ '' Ioo (0 : I) 1) :=
    (isPreconnected_Ioo (a := (0 : I)) (b := 1)).image γ₂ γ₂.continuous.continuousOn
  have hγ₂_side :
      γ₂ '' Ioo 0 1 ⊆
          filledHull (range κ₁ ∪ range lowerSemicircle) \ (range κ₁ ∪ range lowerSemicircle) ∨
        γ₂ '' Ioo 0 1 ⊆
          filledHull (range κ₁ ∪ range upperSemicircle) \ (range κ₁ ∪ range upperSemicircle) := by
    have hcov : γ₂ '' Ioo 0 1 ⊆
        (filledHull (range κ₁ ∪ range upperSemicircle) \ (range κ₁ ∪ range upperSemicircle)) ∪
          (filledHull (range κ₁ ∪ range lowerSemicircle) \ (range κ₁ ∪ range lowerSemicircle)) :=
      hWunion ▸ hγ₂_open_sub
    exact (hγ₂_conn.subset_or_subset
      hJp_curve.isClosed.isOpen_filledHull_sdiff hJm_curve.isClosed.isOpen_filledHull_sdiff
      hWdisj hcov).symm
  have hsplit : ∃ αp αm : Path p₁ p₂, Injective αp ∧ Injective αm ∧
      range αp ∪ range αm = C ∧
      filledHull (range upperSemicircle ∪ range αp ∪ range J₁ ∪ range J₂.symm) ∪
        filledHull (range lowerSemicircle ∪ range αm ∪ range J₁ ∪ range J₂.symm) =
        closedBall 0 1 \ (filledHull C \ C) ∧
      filledHull (range upperSemicircle ∪ range αp ∪ range J₁ ∪ range J₂.symm) ∩
        filledHull (range lowerSemicircle ∪ range αm ∪ range J₁ ∪ range J₂.symm) =
        range J₁ ∪ range J₂ := by
    rcases hγ₂_side with hside | hside
    · obtain ⟨hu, hi⟩ := split_second_half hJ₁_inj hJ₂_inj hγ₁_inj hγ₂_inj
        upperSemicircle_injective lowerSemicircle_injective hJ₁J₂ hJ₁C hJ₂C hJ₁S hJ₂S hCb
        hγu hγi range_upperSemicircle_union_lowerSemicircle
        range_upperSemicircle_inter_lowerSemicircle hκ₁_cut hside
      exact ⟨γ₁, γ₂, hγ₁_inj, hγ₂_inj, hγu, hu, hi⟩
    · obtain ⟨hu, hi⟩ := split_second_half hJ₁_inj hJ₂_inj hγ₁_inj hγ₂_inj
        lowerSemicircle_injective upperSemicircle_injective hJ₁J₂ hJ₁C hJ₂C hJ₁S hJ₂S hCb
        hγu hγi (by rw [union_comm, range_upperSemicircle_union_lowerSemicircle])
        (by rw [inter_comm, range_upperSemicircle_inter_lowerSemicircle]) hκ₁_cut hside
      exact ⟨γ₂, γ₁, hγ₂_inj, hγ₁_inj, by rw [union_comm, hγu],
        by rw [union_comm, hu], by rw [inter_comm, hi]⟩
  obtain ⟨αp, αm, hαp_inj, hαm_inj, hαu, hA_union, hA_inter⟩ := hsplit
  have hαpC : range αp ⊆ C := hαu ▸ subset_union_left
  have hαmC : range αm ⊆ C := hαu ▸ subset_union_right
  -- Step 4: Parametrize both four-sided domains by `I × I` and glue them along `J₁` and `J₂.symm`.
  have hmkSquare {arc : Path (1 : ℂ) (-1 : ℂ)} {α : Path p₁ p₂}
      (harc : Injective arc) (hα : Injective α)
      (harcS : range arc ⊆ sphere 0 1) (hαC : range α ⊆ C) :
      ∃ Φ : I × I ≃ₜ filledHull (range arc ∪ range α ∪ range J₁ ∪ range J₂.symm),
        (∀ s : I, (Φ (s, 0) : ℂ) = arc s) ∧
        (∀ s : I, (Φ (s, 1) : ℂ) = α s) ∧
        (∀ t : I, (Φ (0, t) : ℂ) = J₁ t) ∧
        (∀ t : I, (Φ (1, t) : ℂ) = J₂.symm t) := by
    refine (exists_homeomorph_unitInterval_prod_filledHull harc hα hJ₁_inj
      (Path.injective_symm_iff.mpr hJ₂_inj)
      (sphere_disjoint_ball.mono harcS (hαC.trans hCb))
      (by rwa [Path.symm_range]) ?_ ?_ ?_ ?_).2
    · refine Subset.antisymm ?_
        (singleton_subset_iff.mpr ⟨arc.source_mem_range, J₁.source_mem_range⟩)
      rw [inter_comm]
      exact (inter_subset_inter_right _ harcS).trans hJ₁S.subset
    · rw [Path.symm_range]
      refine Subset.antisymm ?_
        (singleton_subset_iff.mpr ⟨arc.target_mem_range, J₂.target_mem_range⟩)
      rw [inter_comm]
      exact (inter_subset_inter_right _ harcS).trans hJ₂S.subset
    · refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨α.source_mem_range, J₁.target_mem_range⟩)
      rw [inter_comm]
      exact (inter_subset_inter_right _ hαC).trans hJ₁C.subset
    · rw [Path.symm_range]
      refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨α.target_mem_range, J₂.source_mem_range⟩)
      rw [inter_comm]
      exact (inter_subset_inter_right _ hαC).trans hJ₂C.subset
  obtain ⟨Φp, hΦp_top, hΦp_bot, hΦp_left, hΦp_right⟩ :=
    hmkSquare upperSemicircle_injective hαp_inj hσpS hαpC
  obtain ⟨Φm, hΦm_top, hΦm_bot, hΦm_left, hΦm_right⟩ :=
    hmkSquare lowerSemicircle_injective hαm_inj hσmS hαmC
  exact glue_upper_lower_squares hαu hA_union hA_inter Φp Φm hΦp_top hΦp_bot hΦp_left hΦp_right
    hΦm_top hΦm_bot hΦm_left hΦm_right

end Normalized

/-! ### The planar annulus theorem -/

/-- If a subset `K ⊆ ℂ` lies inside the open region `filledHull C \ C` bounded by a Jordan
curve `C ⊆ ℂ`, then its whole filled hull `filledHull K` lies inside `filledHull C \ C`. -/
theorem IsJordanCurve.filledHull_subset_filledHull_sdiff {C K : Set ℂ}
    (hC : IsJordanCurve C) (hsub : K ⊆ filledHull C \ C) :
    filledHull K ⊆ filledHull C \ C := by
  rw [← hC.interior_filledHull] at hsub ⊢
  exact filledHull_subset_interior_filledHull
    (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) hC.isCompact.isBounded hsub

/-- **The planar annulus theorem with prescribed outer boundary parametrization.** Let `C₁` and `C₂`
be Jordan curves in `ℂ` with `C₂ ⊆ filledHull C₁ \ C₁`, and let `φ : sphere (0 : ℂ) 1 ≃ₜ C₁` be any
homeomorphism onto the outer curve. Then the closed region `filledHull C₁ \ (filledHull C₂ \ C₂)`
between `C₁` and `C₂` is homeomorphic to `sphere (0 : ℂ) 1 × I` by a homeomorphism restricting to
`φ` on `sphere (0 : ℂ) 1 × {0}` and carrying `sphere (0 : ℂ) 1 × {1}` onto `C₂`. -/
theorem IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval_of_homeomorph {C₁ C₂ : Set ℂ}
    (hC₁ : IsJordanCurve C₁) (hC₂ : IsJordanCurve C₂) (hsub : C₂ ⊆ filledHull C₁ \ C₁)
    (φ : sphere (0 : ℂ) 1 ≃ₜ C₁) :
    ∃ Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(filledHull C₁ \ (filledHull C₂ \ C₂)),
      (∀ u : sphere (0 : ℂ) 1, (Φ (u, 0) : ℂ) = φ u) ∧
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {1}) = C₂ := by
  obtain ⟨p₀, hp₀⟩ := hC₂.nonempty_filledHull_sdiff
  have hp₀₁ : p₀ ∈ filledHull C₁ \ C₁ :=
    hC₁.filledHull_subset_filledHull_sdiff hsub hp₀.1
  obtain ⟨e, he0, heφ, -, heB, heCB⟩ := hC₁.exists_homeomorph_sphere_eq_of_mem hp₀₁ φ
  set C : Set ℂ := e.symm '' C₂
  have hC : IsJordanCurve C := hC₂.image_homeomorph e.symm
  have hCb : C ⊆ ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwe⟩ := heB.symm.subset (hsub hz)
    rwa [← hwe, e.symm_apply_apply]
  have hfhC : filledHull C = e.symm '' filledHull C₂ :=
    (e.symm.image_filledHull (fun _ => e.symm.isBounded_image_iff) C₂).symm
  have h0C : (0 : ℂ) ∈ filledHull C \ C := by
    have he0' : e.symm p₀ = 0 := by rw [← he0, e.symm_apply_apply]
    refine ⟨?_, ?_⟩
    · rw [hfhC, ← he0']; exact mem_image_of_mem e.symm hp₀.1
    · rw [← he0', e.symm.injective.mem_set_image]; exact hp₀.2
  obtain ⟨Φ₀, hΦ₀0, hΦ₀1⟩ := exists_homeomorph_sphere_prod_unitInterval_normalized hC hCb h0C
  have himg : e '' (closedBall 0 1 \ (filledHull C \ C)) =
      filledHull C₁ \ (filledHull C₂ \ C₂) := by
    rw [Set.image_sdiff e.injective, Set.image_sdiff e.injective, heCB, hfhC]
    simp [C, image_image]
  let Ψ : ↥(closedBall (0 : ℂ) 1 \ (filledHull C \ C)) ≃ₜ
      ↥(filledHull C₁ \ (filledHull C₂ \ C₂)) :=
    (e.image _).trans (Homeomorph.setCongr himg)
  refine ⟨Φ₀.trans Ψ, ?_, ?_⟩
  · intro u
    have hcoe : ((Φ₀.trans Ψ) (u, 0) : ℂ) = e (Φ₀ (u, 0)) := rfl
    rw [hcoe, hΦ₀0 u, heφ u]
  · have hcoe : (fun p : sphere (0 : ℂ) 1 × I => ((Φ₀.trans Ψ) p : ℂ)) =
        e ∘ (fun p => (Φ₀ p : ℂ)) := rfl
    rw [hcoe, image_comp, hΦ₀1]
    simp [C, image_image]

/-- **The planar annulus theorem.** If `C₁` and `C₂` are Jordan curves in `ℂ` with
`C₂ ⊆ filledHull C₁ \ C₁`, then the closed region `filledHull C₁ \ (filledHull C₂ \ C₂)` between
them is homeomorphic to `sphere (0 : ℂ) 1 × I`, carrying `sphere (0 : ℂ) 1 × {0}` onto `C₁` and
`sphere (0 : ℂ) 1 × {1}` onto `C₂`. -/
theorem IsJordanCurve.exists_homeomorph_sphere_prod_unitInterval {C₁ C₂ : Set ℂ}
    (hC₁ : IsJordanCurve C₁) (hC₂ : IsJordanCurve C₂) (hsub : C₂ ⊆ filledHull C₁ \ C₁) :
    ∃ Φ : sphere (0 : ℂ) 1 × I ≃ₜ ↥(filledHull C₁ \ (filledHull C₂ \ C₂)),
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {0}) = C₁ ∧
      (fun p => (Φ p : ℂ)) '' (univ ×ˢ {1}) = C₂ := by
  obtain ⟨e₁⟩ := isJordanCurve_iff.mp hC₁
  let φ : sphere (0 : ℂ) 1 ≃ₜ C₁ := (sphereCircleHomeomorph 0 one_pos).trans e₁.symm
  obtain ⟨Φ, hΦ0, hΦ1⟩ :=
    hC₁.exists_homeomorph_sphere_prod_unitInterval_of_homeomorph hC₂ hsub φ
  refine ⟨Φ, ?_, hΦ1⟩
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨⟨u, t⟩, ⟨-, ht⟩, rfl⟩
    rw [mem_singleton_iff] at ht; subst ht
    dsimp only
    rw [hΦ0 u]
    exact (φ u).property
  · intro z hz
    refine ⟨(φ.symm ⟨z, hz⟩, 0), ⟨trivial, rfl⟩, ?_⟩
    dsimp only
    rw [hΦ0, φ.apply_symm_apply]

end TauCeti
