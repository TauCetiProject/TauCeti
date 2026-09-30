/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Semicircle
public import TauCeti.Analysis.Complex.UpperHalfPlane.IdealRegion

/-!
# Hyperbolic triangles and the Gauss–Bonnet formula

A hyperbolic triangle with vertices `A`, `B`, `C` in `ℍ` is the intersection of the three closed
half-planes bounded by the geodesic through two of the vertices and containing the third
(`triangle`). Its interior angle at `A` is the angle between the geodesics from `A` to `B` and
from `A` to `C` (`interiorAngle`). The **Gauss–Bonnet formula** (`volume_triangle`) computes its
invariant area as the angular defect `π - α - β - γ`.

Following Katok, the formula is first proved for triangles with a vertex at infinity
(`volume_idealRegion`), and a general triangle is the difference of two such, cut along the
geodesic through one vertex and the point at infinity of the opposite side. We normalise so that
this point at infinity is `∞` itself: the side `AB` lies on the imaginary axis, and `C` lies to
its right (`exists_smul_eq_normal_form`). In this normal form the triangle is described by
three explicit inequalities (`mem_triangle_normal_form_iff`), it differs from `Δ₁ \ Δ₂` by a null
arc (`triangle_subset_diff_union_of_normal_form`), and its three interior angles are read off the
radius vectors of the two semicircles (`interiorAngle_I_geodesicLine_one`,
`interiorAngle_geodesicLine_one_I`, `interiorAngle_of_normal_form`).

Source: Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 8 (2008), §5 p. 19–20:
the definition of a hyperbolic triangle and Theorem 5.4 (Gauss–Bonnet) with its proof.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation dilation)

/-! ### The closed half-plane bounded by the geodesic through two points -/

open scoped Classical in
/-- The closed half-plane bounded by the geodesic from `z` to `w` that contains `u`. -/
def closedSide (z w u : ℍ) : Set ℍ :=
  if u ∈ rightHalfPlane (geodesicBetween z w) then closure (rightHalfPlane (geodesicBetween z w))
  else closure (leftHalfPlane (geodesicBetween z w))

open scoped Classical in
/-- Restatement of the body of `closedSide`, unfolded from the `def`. -/
theorem closedSide_def (z w u : ℍ) :
    closedSide z w u =
      if u ∈ rightHalfPlane (geodesicBetween z w) then
        closure (rightHalfPlane (geodesicBetween z w))
      else closure (leftHalfPlane (geodesicBetween z w)) := by
  rfl

/-- The reference point lies in its closed side. -/
theorem mem_closedSide_self (z w u : ℍ) : u ∈ closedSide z w u := by
  unfold closedSide
  split_ifs with h
  · exact subset_closure h
  · have hu : u ∈ rightHalfPlane (geodesicBetween z w) ∪
        Set.range (geodesicLine (geodesicBetween z w)) ∪ leftHalfPlane (geodesicBetween z w) :=
      (rightHalfPlane_union_range_geodesicLine_union_leftHalfPlane _).symm ▸ Set.mem_univ u
    rw [closure_leftHalfPlane]
    rcases hu with (hu | hu) | hu
    · exact absurd hu h
    · exact Or.inr hu
    · exact Or.inl hu

/-- Closed sides are closed. -/
theorem isClosed_closedSide (z w u : ℍ) : IsClosed (closedSide z w u) := by
  unfold closedSide
  split_ifs <;> exact isClosed_closure

/-- Closed sides are measurable. -/
theorem measurableSet_closedSide (z w u : ℍ) : MeasurableSet (closedSide z w u) :=
  (isClosed_closedSide z w u).measurableSet

/-- Closed sides transform naturally under the action. -/
theorem smul_closedSide (h : PSL(2, ℝ)) {z w : ℍ} (hzw : z ≠ w) (u : ℍ) :
    h • closedSide z w u = closedSide (h • z) (h • w) (h • u) := by
  unfold closedSide
  rw [geodesicBetween_smul h hzw, ← smul_rightHalfPlane, ← smul_leftHalfPlane,
    Set.smul_mem_smul_set_iff]
  split_ifs <;> rw [closure_smul]

/-- The closed side does not depend on the direction of the bounding geodesic, as long as the
reference point is off the line. -/
theorem closedSide_swap {z w u : ℍ} (hzw : z ≠ w)
    (hu : u ∉ Set.range (geodesicLine (geodesicBetween z w))) :
    closedSide w z u = closedSide z w u := by
  unfold closedSide
  rw [geodesicBetween_swap hzw, rightHalfPlane_mul_pslS, leftHalfPlane_mul_pslS,
    rightHalfPlane_mul_dilation, leftHalfPlane_mul_dilation]
  by_cases hr : u ∈ rightHalfPlane (geodesicBetween z w)
  · have hl : u ∉ leftHalfPlane (geodesicBetween z w) := fun hl ↦
      Set.disjoint_left.1 (disjoint_rightHalfPlane_leftHalfPlane _) hr hl
    simp only [hr, hl, ↓reduceIte]
  · have hl : u ∈ leftHalfPlane (geodesicBetween z w) := by
      have hu' : u ∈ rightHalfPlane (geodesicBetween z w) ∪
          Set.range (geodesicLine (geodesicBetween z w)) ∪ leftHalfPlane (geodesicBetween z w) :=
        (rightHalfPlane_union_range_geodesicLine_union_leftHalfPlane _).symm ▸ Set.mem_univ u
      rcases hu' with (h | h) | h
      · exact absurd h hr
      · exact absurd h hu
      · exact h
    simp only [hr, hl, ↓reduceIte]

/-! ### Triangles -/

/-- The hyperbolic triangle with vertices `A`, `B`, `C`: the intersection of the three closed
half-planes bounded by the geodesic through two vertices and containing the third. -/
def triangle (A B C : ℍ) : Set ℍ :=
  closedSide A B C ∩ closedSide B C A ∩ closedSide C A B

/-- Restatement of the body of `triangle`, unfolded from the `def`. -/
theorem triangle_def (A B C : ℍ) :
    triangle A B C = closedSide A B C ∩ closedSide B C A ∩ closedSide C A B := by
  rfl

/-- Triangles are closed. -/
theorem isClosed_triangle (A B C : ℍ) : IsClosed (triangle A B C) :=
  ((isClosed_closedSide _ _ _).inter (isClosed_closedSide _ _ _)).inter (isClosed_closedSide _ _ _)

/-- Triangles are measurable. -/
theorem measurableSet_triangle (A B C : ℍ) : MeasurableSet (triangle A B C) :=
  (isClosed_triangle A B C).measurableSet

/-- Triangles transform naturally under the action. -/
theorem smul_triangle (h : PSL(2, ℝ)) {A B C : ℍ} (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    h • triangle A B C = triangle (h • A) (h • B) (h • C) := by
  rw [triangle, triangle, Set.smul_set_inter, Set.smul_set_inter, smul_closedSide h hAB,
    smul_closedSide h hBC, smul_closedSide h hCA]

/-- The triangle does not depend on the order of its vertices. -/
theorem triangle_swap_left {A B C : ℍ} (hAB : A ≠ B)
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) :
    triangle B A C = triangle A B C := by
  have hAC : A ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_left A B)
  have hBC : B ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_right A B)
  -- `B` is off the line `A C`, and `A` is off the line `C B`: otherwise that line would be `A B`
  have hB : B ∉ Set.range (geodesicLine (geodesicBetween A C)) := fun hB ↦ hC
    ((range_geodesicLine_geodesicBetween_of_mem (mem_range_geodesicLine_geodesicBetween_left A C)
      hB hAB).symm ▸ mem_range_geodesicLine_geodesicBetween_right A C)
  have hA : A ∉ Set.range (geodesicLine (geodesicBetween C B)) := fun hA ↦ hC
    ((range_geodesicLine_geodesicBetween_of_mem hA
      (mem_range_geodesicLine_geodesicBetween_right C B) hAB).symm ▸
      mem_range_geodesicLine_geodesicBetween_left C B)
  rw [triangle, triangle, closedSide_swap hAB hC, closedSide_swap hAC hB,
    closedSide_swap hBC.symm hA, Set.inter_right_comm]

/-- The interior angle of the triangle `A B C` at the vertex `A`: the angle between the geodesics
from `A` to `B` and from `A` to `C`. -/
def interiorAngle (A B C : ℍ) : ℝ :=
  geodesicAngle (geodesicBetween A B) (geodesicBetween A C)

-- The body of `interiorAngle` is not `@[expose]`d, so downstream modules rewrite with this.
/-- `interiorAngle` is the angle between the geodesics from `A` to `B` and from `A` to `C`. -/
theorem interiorAngle_def (A B C : ℍ) :
    interiorAngle A B C = geodesicAngle (geodesicBetween A B) (geodesicBetween A C) := by rfl

/-- The interior angle at `A` does not depend on the order of the other two vertices. -/
theorem interiorAngle_comm (A B C : ℍ) : interiorAngle A C B = interiorAngle A B C :=
  geodesicAngle_comm _ _

/-- Interior angles are nonnegative. -/
theorem interiorAngle_nonneg (A B C : ℍ) : 0 ≤ interiorAngle A B C :=
  geodesicAngle_nonneg _ _

/-- Interior angles are at most `π`. -/
theorem interiorAngle_le_pi (A B C : ℍ) : interiorAngle A B C ≤ π :=
  geodesicAngle_le_pi _ _

/-- Interior angles are invariant under the action. -/
theorem interiorAngle_smul (h : PSL(2, ℝ)) {A B C : ℍ} (hAB : A ≠ B) (hAC : A ≠ C) :
    interiorAngle (h • A) (h • B) (h • C) = interiorAngle A B C := by
  rw [interiorAngle, interiorAngle, geodesicBetween_smul h hAB, geodesicBetween_smul h hAC,
    geodesicAngle_mul _ _ _ (by rw [geodesicLine_geodesicBetween_zero,
      geodesicLine_geodesicBetween_zero])]

/-! ### The Gauss–Bonnet formula -/

/-- The triangle in normal form, with `A = I`, `B = i exp d` above it and `C` to the right, as
a system of inequalities: to the right of the imaginary axis, inside the disc bounded by the
semicircle through `B` and `C`, and outside the disc bounded by the semicircle through `I` and
`C`. -/
theorem mem_triangle_normal_form_iff {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) (z : ℍ) :
    z ∈ triangle UpperHalfPlane.I (geodesicLine 1 d) C ↔
      0 ≤ z.re ∧
        Complex.normSq ((z : ℂ) - circleCenter (geodesicLine 1 d) C) ≤
          Complex.normSq ((C : ℂ) - circleCenter (geodesicLine 1 d) C) ∧
        Complex.normSq ((C : ℂ) - circleCenter UpperHalfPlane.I C) ≤
          Complex.normSq ((z : ℂ) - circleCenter UpperHalfPlane.I C) := by
  set B := geodesicLine 1 d with hB
  have hBre : B.re = 0 := by rw [hB, geodesicLine_one_apply]; rfl
  have hBim : B.im = Real.exp d := by rw [hB, geodesicLine_one_apply]; rfl
  have hIre : UpperHalfPlane.I.re = 0 := rfl
  have hIim : UpperHalfPlane.I.im = 1 := rfl
  have hexp : 1 < Real.exp d := Real.one_lt_exp_iff.2 hd
  have hBC : B.re < C.re := by rw [hBre]; exact hC
  have hIC : UpperHalfPlane.I.re < C.re := by rw [hIre]; exact hC
  -- the side `I B` is the imaginary axis, with `C` on its right
  have h1 : closedSide UpperHalfPlane.I B C = {z : ℍ | 0 ≤ z.re} := by
    unfold closedSide
    rw [hB, geodesicBetween_I_geodesicLine_one hd]
    have hCmem : C ∈ rightHalfPlane (1 : PSL(2, ℝ)) := by
      rw [mem_rightHalfPlane_iff, inv_one, one_smul]
      exact hC
    simp only [hCmem, ↓reduceIte]
    ext z
    rw [mem_closure_rightHalfPlane_iff, inv_one, one_smul, Set.mem_ofPred_eq]
  -- the side `B C` is a semicircle, with `I` inside its disc
  have h2 : closedSide B C UpperHalfPlane.I = {z : ℍ |
      Complex.normSq ((z : ℂ) - circleCenter B C) ≤
        Complex.normSq ((C : ℂ) - circleCenter B C)} := by
    unfold closedSide
    have hImem : UpperHalfPlane.I ∈ rightHalfPlane (geodesicBetween B C) := by
      rw [mem_rightHalfPlane_geodesicBetween_iff_of_re_lt hBC]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hBre, hBim,
        hIre, hIim]
      nlinarith
    simp only [hImem, ↓reduceIte]
    ext z
    rw [mem_closure_rightHalfPlane_iff, Set.mem_ofPred_eq]
    obtain ⟨κ, hκ, h⟩ := exists_re_inv_geodesicBetween_smul_eq hBC.ne z
    rw [h, hBre, ← normSq_sub_circleCenter hBC.ne, mul_nonneg_iff_of_pos_left hκ]
    set X := Complex.normSq ((z : ℂ) - circleCenter B C)
    set Y := Complex.normSq ((C : ℂ) - circleCenter B C)
    have e : (0 - C.re) * (X - Y) = C.re * (Y - X) := by ring
    rw [e, mul_nonneg_iff_of_pos_left hC, sub_nonneg]
  -- the side `C I` is a semicircle, with `B` outside its disc
  have h3 : closedSide C UpperHalfPlane.I B = {z : ℍ |
      Complex.normSq ((C : ℂ) - circleCenter UpperHalfPlane.I C) ≤
        Complex.normSq ((z : ℂ) - circleCenter UpperHalfPlane.I C)} := by
    unfold closedSide
    have hBmem : B ∈ rightHalfPlane (geodesicBetween C UpperHalfPlane.I) := by
      rw [mem_rightHalfPlane_geodesicBetween_iff_of_lt_re hIC, circleCenter_comm,
        normSq_sub_circleCenter hIC.ne]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
        Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hBre, hBim,
        hIre, hIim]
      nlinarith
    simp only [hBmem, ↓reduceIte]
    ext z
    rw [mem_closure_rightHalfPlane_iff, Set.mem_ofPred_eq]
    obtain ⟨κ, hκ, h⟩ := exists_re_inv_geodesicBetween_smul_eq hIC.ne' z
    rw [h, hIre, sub_zero, circleCenter_comm, mul_nonneg_iff_of_pos_left hκ,
      mul_nonneg_iff_of_pos_left hC, sub_nonneg]
  rw [triangle, h1, h2, h3]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-- In normal form, the centre of the semicircle through `i exp d` and `C` lies to the left of
the centre of the semicircle through `I` and `C`. -/
theorem circleCenter_lt_of_normal_form {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    circleCenter (geodesicLine 1 d) C < circleCenter UpperHalfPlane.I C := by
  have hBre : (geodesicLine 1 d).re = 0 := by rw [geodesicLine_one_apply]; rfl
  have hBn : Complex.normSq ((geodesicLine 1 d : ℍ) : ℂ) = Real.exp d * Real.exp d := by
    rw [geodesicLine_one_apply, UpperHalfPlane.coe_mk, Complex.normSq_apply]
    simp
  have hIn : Complex.normSq ((UpperHalfPlane.I : ℍ) : ℂ) = 1 := by
    rw [UpperHalfPlane.coe_I, Complex.normSq_I]
  have hexp : 1 < Real.exp d := Real.one_lt_exp_iff.2 hd
  rw [circleCenter_def, circleCenter_def, hBre, hBn, hIn, show UpperHalfPlane.I.re = 0 from rfl,
    sub_zero, div_lt_div_iff_of_pos_right (by positivity)]
  nlinarith

/-- The "radical line" identity: the difference of the two power functions of `z` with respect
to the semicircles through `C` is affine in `z.re` and vanishes at `C.re`. -/
theorem normSq_sub_circleCenter_sub_eq {c₁ c₂ : ℝ} (C z : ℍ) :
    (Complex.normSq ((z : ℂ) - c₁) - Complex.normSq ((C : ℂ) - c₁)) -
        (Complex.normSq ((z : ℂ) - c₂) - Complex.normSq ((C : ℂ) - c₂)) =
      2 * (c₂ - c₁) * (z.re - C.re) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

/-- In normal form, the ideal-vertex region over the semicircle through `i exp d` and `C` is
contained in the one over the semicircle through `I` and `C`. -/
theorem idealRegionAbove_subset_of_normal_form {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    idealRegionAbove (circleCenter (geodesicLine 1 d) C)
        (Real.sqrt (Complex.normSq ((C : ℂ) - circleCenter (geodesicLine 1 d) C))) 0 C.re ⊆
      idealRegionAbove (circleCenter UpperHalfPlane.I C)
        (Real.sqrt (Complex.normSq ((C : ℂ) - circleCenter UpperHalfPlane.I C))) 0 C.re := by
  intro z hz'
  rw [mem_idealRegionAbove_iff] at hz' ⊢
  obtain ⟨h0, hz, h2⟩ := hz'
  refine ⟨h0, hz, ?_⟩
  rw [Real.sq_sqrt (Complex.normSq_nonneg _)] at h2 ⊢
  have hrad := normSq_sub_circleCenter_sub_eq (c₁ := circleCenter UpperHalfPlane.I C)
    (c₂ := circleCenter (geodesicLine 1 d) C) C z
  have hlt := circleCenter_lt_of_normal_form hd hC
  nlinarith [mul_nonneg (sub_nonneg.2 hlt.le) (sub_nonneg.2 hz)]

/-- In normal form, the difference of the two ideal-vertex regions lies in the triangle. -/
theorem diff_subset_triangle_of_normal_form {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    idealRegionAbove (circleCenter UpperHalfPlane.I C)
          (Real.sqrt (Complex.normSq ((C : ℂ) - circleCenter UpperHalfPlane.I C))) 0 C.re \
        idealRegionAbove (circleCenter (geodesicLine 1 d) C)
          (Real.sqrt (Complex.normSq ((C : ℂ) - circleCenter (geodesicLine 1 d) C))) 0 C.re ⊆
      triangle UpperHalfPlane.I (geodesicLine 1 d) C := by
  intro z ⟨hz1, h2⟩
  rw [mem_idealRegionAbove_iff] at hz1 h2
  obtain ⟨h0, hz, h1⟩ := hz1
  rw [mem_triangle_normal_form_iff hd hC]
  rw [Real.sq_sqrt (Complex.normSq_nonneg _)] at h1
  refine ⟨h0, ?_, h1⟩
  by_contra hlt
  exact h2 ⟨h0, hz, by rw [Real.sq_sqrt (Complex.normSq_nonneg _)]; exact le_of_not_ge hlt⟩

/-- In normal form, the triangle lies in the difference of the two ideal-vertex regions, up to
the arc `B C`. -/
theorem triangle_subset_diff_union_of_normal_form {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    triangle UpperHalfPlane.I (geodesicLine 1 d) C ⊆
      (idealRegionAbove (circleCenter UpperHalfPlane.I C)
          (Real.sqrt (Complex.normSq ((C : ℂ) - circleCenter UpperHalfPlane.I C))) 0 C.re \
        idealRegionAbove (circleCenter (geodesicLine 1 d) C)
          (Real.sqrt (Complex.normSq ((C : ℂ) - circleCenter (geodesicLine 1 d) C))) 0 C.re) ∪
        Set.range (geodesicLine (geodesicBetween (geodesicLine 1 d) C)) := by
  intro z hz
  rw [mem_triangle_normal_form_iff hd hC] at hz
  obtain ⟨h0, h2, h1⟩ := hz
  have hBre : (geodesicLine 1 d).re = 0 := by rw [geodesicLine_one_apply]; rfl
  have hBC : (geodesicLine 1 d).re < C.re := by rw [hBre]; exact hC
  have hrad := normSq_sub_circleCenter_sub_eq (c₁ := circleCenter UpperHalfPlane.I C)
    (c₂ := circleCenter (geodesicLine 1 d) C) C z
  have hlt := circleCenter_lt_of_normal_form hd hC
  -- the triangle lies over `[0, C.re]`
  have hzC : z.re ≤ C.re := by
    by_contra hgt
    have := mul_neg_of_neg_of_pos (sub_neg.2 hlt) (sub_pos.2 (lt_of_not_ge hgt))
    linarith
  rcases lt_or_eq_of_le h2 with h2 | h2
  · left
    refine ⟨(mem_idealRegionAbove_iff _ _ _ _ _).2
      ⟨h0, hzC, by rw [Real.sq_sqrt (Complex.normSq_nonneg _)]; exact h1⟩, ?_⟩
    intro hmem
    rw [mem_idealRegionAbove_iff] at hmem
    obtain ⟨-, -, h⟩ := hmem
    rw [Real.sq_sqrt (Complex.normSq_nonneg _)] at h
    exact absurd h (not_le.2 h2)
  · right
    rw [mem_range_geodesicLine_geodesicBetween_iff_of_re_ne hBC.ne, h2,
      normSq_sub_circleCenter hBC.ne]

/-- `√(normSq z)` is the norm. -/
private theorem sqrt_normSq_eq_norm (z : ℂ) : Real.sqrt (Complex.normSq z) = ‖z‖ := by
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The argument of a quotient of two points of the upper half-plane whose quotient also has
nonnegative imaginary part is the difference of the arguments. -/
private theorem arg_div_eq_sub_of_im_pos {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) :
    Complex.arg (x / y) = Complex.arg x - Complex.arg y := by
  have hx0 : x ≠ 0 := fun h ↦ hx.ne' (by rw [h, Complex.zero_im])
  have hy0 : y ≠ 0 := fun h ↦ hy.ne' (by rw [h, Complex.zero_im])
  have h := Complex.arg_div_coe_angle hx0 hy0
  rw [← Real.Angle.coe_sub] at h
  have h' := (Real.Angle.toReal_coe_eq_self_iff (θ := Complex.arg x - Complex.arg y)).2
    ⟨by linarith [Complex.arg_nonneg_iff.2 hx.le, Complex.arg_lt_pi_iff.2 (Or.inr hy.ne')],
      by linarith [Complex.arg_nonneg_iff.2 hy.le, Complex.arg_le_pi x]⟩
  rw [← h, Complex.arg_coe_angle_toReal_eq_arg] at h'
  exact h'

/-- The interior angle at `I` of the triangle in normal form. -/
theorem interiorAngle_I_geodesicLine_one {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    interiorAngle UpperHalfPlane.I (geodesicLine 1 d) C =
      Real.arccos (circleCenter UpperHalfPlane.I C /
        Real.sqrt (Complex.normSq ((UpperHalfPlane.I : ℂ) - circleCenter UpperHalfPlane.I C))) := by
  have hIC : UpperHalfPlane.I.re ≠ C.re := by
    rw [show UpperHalfPlane.I.re = 0 from rfl]
    exact hC.ne
  obtain ⟨μ, hμ, hv⟩ := exists_velocity_geodesicBetween_zero_eq hIC
  rw [show UpperHalfPlane.I.re = 0 from rfl, sub_zero] at hμ
  have hμ' : μ < 0 := (neg_of_mul_neg_left hμ hC.le)
  set c := circleCenter UpperHalfPlane.I C with hc
  have hne : (c : ℂ) - UpperHalfPlane.I ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h
    simp at this
  rw [interiorAngle, geodesicBetween_I_geodesicLine_one hd, geodesicAngle_def, velocity_one,
    Real.exp_zero, Complex.ofReal_one, mul_one, hv, ← Complex.real_smul,
    InnerProductGeometry.angle_smul_right_of_neg _ _ hμ', ← mul_neg, ← mul_one Complex.I,
    mul_assoc, one_mul, Complex.angle_mul_left Complex.I_ne_zero, neg_sub,
    Complex.angle_one_left hne, Complex.arg_of_im_neg (by simp), abs_neg,
    abs_of_nonneg (Real.arccos_nonneg _), sqrt_normSq_eq_norm, norm_sub_rev]
  congr 2
  simp

/-- The interior angle at `i exp d` of the triangle in normal form. -/
theorem interiorAngle_geodesicLine_one_I {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    interiorAngle (geodesicLine 1 d) C UpperHalfPlane.I =
      π - Real.arccos (circleCenter (geodesicLine 1 d) C /
        Real.sqrt (Complex.normSq ((geodesicLine 1 d : ℂ) -
          circleCenter (geodesicLine 1 d) C))) := by
  set B := geodesicLine 1 d with hB
  have hBre : B.re = 0 := by rw [hB, geodesicLine_one_apply]; rfl
  have hBim : B.im = Real.exp d := by rw [hB, geodesicLine_one_apply]; rfl
  have hBC : B.re ≠ C.re := by rw [hBre]; exact hC.ne
  have hBI : B ≠ UpperHalfPlane.I := fun h ↦ by
    have := congrArg UpperHalfPlane.im h
    rw [hBim] at this
    exact (Real.one_lt_exp_iff.2 hd).ne' this
  obtain ⟨μ, hμ, hv⟩ := exists_velocity_geodesicBetween_zero_eq hBC
  rw [hBre, sub_zero] at hμ
  have hμ' : μ < 0 := neg_of_mul_neg_left hμ hC.le
  obtain ⟨ν, hν, hv'⟩ := exists_velocity_geodesicBetween_zero_eq_of_re_eq (P := B)
    (Q := UpperHalfPlane.I) hBre hBI
  rw [show UpperHalfPlane.I.im = 1 from rfl, hBim] at hv'
  have hρ : ν * (1 - Real.exp d) < 0 :=
    mul_neg_of_pos_of_neg hν (by linarith [Real.one_lt_exp_iff.2 hd])
  set c := circleCenter B C with hc
  have hne : (B : ℂ) - c ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h
    simp [hBim] at this
  have hv'' : velocity (geodesicBetween B UpperHalfPlane.I) 0 =
      (ν * (1 - Real.exp d)) • Complex.I := by
    rw [hv', Complex.real_smul]
    push_cast
    ring
  rw [interiorAngle, geodesicAngle_def, hv, hv'', ← Complex.real_smul,
    InnerProductGeometry.angle_smul_left_of_neg _ _ hμ',
    InnerProductGeometry.angle_smul_right_of_neg _ _ hρ, InnerProductGeometry.angle_neg_neg,
    Complex.angle_eq_abs_arg (mul_ne_zero Complex.I_ne_zero hne) Complex.I_ne_zero,
    mul_div_cancel_left₀ _ Complex.I_ne_zero,
    Complex.arg_of_im_pos (by simp [hBim, Real.exp_pos]),
    abs_of_nonneg (Real.arccos_nonneg _), sqrt_normSq_eq_norm, ← Real.arccos_neg]
  congr 2
  simp [hBre, neg_div]

/-- The interior angle at `C` of the triangle in normal form: the difference of the angles
between the vertical through `C` and the two semicircles. -/
theorem interiorAngle_of_normal_form {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    interiorAngle C UpperHalfPlane.I (geodesicLine 1 d) =
      Real.arccos ((C.re - circleCenter UpperHalfPlane.I C) /
          Real.sqrt (Complex.normSq ((UpperHalfPlane.I : ℂ) - circleCenter UpperHalfPlane.I C))) -
        Real.arccos ((C.re - circleCenter (geodesicLine 1 d) C) /
          Real.sqrt (Complex.normSq ((geodesicLine 1 d : ℂ) -
            circleCenter (geodesicLine 1 d) C))) := by
  have hBre : (geodesicLine 1 d).re = 0 := by rw [geodesicLine_one_apply]; rfl
  have hCI : C.re ≠ UpperHalfPlane.I.re := by
    rw [show UpperHalfPlane.I.re = 0 from rfl]
    exact hC.ne'
  have hCB : C.re ≠ (geodesicLine 1 d).re := by rw [hBre]; exact hC.ne'
  obtain ⟨μ₁, hμ₁, hv₁⟩ := exists_velocity_geodesicBetween_zero_eq hCI
  obtain ⟨μ₂, hμ₂, hv₂⟩ := exists_velocity_geodesicBetween_zero_eq hCB
  rw [show UpperHalfPlane.I.re = 0 from rfl, zero_sub] at hμ₁
  rw [hBre, zero_sub] at hμ₂
  have hμ₁' : 0 < μ₁ := by nlinarith
  have hμ₂' : 0 < μ₂ := by nlinarith
  rw [circleCenter_comm] at hv₁ hv₂
  have hlt := circleCenter_lt_of_normal_form hd hC
  have hx : 0 < ((C : ℂ) - circleCenter UpperHalfPlane.I C).im := by simp [C.im_pos]
  have hy : 0 < ((C : ℂ) - circleCenter (geodesicLine 1 d) C).im := by simp [C.im_pos]
  have hx0 : (C : ℂ) - circleCenter UpperHalfPlane.I C ≠ 0 := fun h ↦
    hx.ne' (by rw [h, Complex.zero_im])
  have hy0 : (C : ℂ) - circleCenter (geodesicLine 1 d) C ≠ 0 := fun h ↦
    hy.ne' (by rw [h, Complex.zero_im])
  -- the quotient of the two radius vectors has nonnegative imaginary part, as `c₂ < c₁`
  have him : 0 ≤ (((C : ℂ) - circleCenter UpperHalfPlane.I C) /
      ((C : ℂ) - circleCenter (geodesicLine 1 d) C)).im := by
    rw [Complex.div_im, ← sub_div]
    refine div_nonneg ?_ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith [C.im_pos]
  rw [interiorAngle, geodesicAngle_def, hv₁, hv₂, ← Complex.real_smul, ← Complex.real_smul,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hμ₁',
    InnerProductGeometry.angle_smul_right_of_pos _ _ hμ₂',
    Complex.angle_mul_left Complex.I_ne_zero, Complex.angle_eq_abs_arg hx0 hy0,
    abs_of_nonneg (Complex.arg_nonneg_iff.2 him), arg_div_eq_sub_of_im_pos hx hy,
    Complex.arg_of_im_pos hx, Complex.arg_of_im_pos hy, ← sqrt_normSq_eq_norm,
    ← sqrt_normSq_eq_norm, normSq_sub_circleCenter (Ne.symm hCI),
    normSq_sub_circleCenter (Ne.symm hCB)]
  simp only [Complex.sub_re, Complex.ofReal_re, UpperHalfPlane.coe_re]

private theorem lt_sqrt_of_sq_lt {a b : ℝ} (h : a ^ 2 < b) : a < Real.sqrt b := by
  rcases lt_or_ge a 0 with ha | ha
  · exact ha.trans_le (Real.sqrt_nonneg _)
  · exact (Real.lt_sqrt ha).2 h

/-- The Gauss–Bonnet formula for the triangle in normal form. -/
theorem volume_triangle_I_geodesicLine_one {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    volume (triangle UpperHalfPlane.I (geodesicLine 1 d) C) =
      ENNReal.ofReal (π - interiorAngle UpperHalfPlane.I (geodesicLine 1 d) C -
        interiorAngle (geodesicLine 1 d) C UpperHalfPlane.I -
        interiorAngle C UpperHalfPlane.I (geodesicLine 1 d)) := by
  set B := geodesicLine 1 d with hB
  have hBre : B.re = 0 := by rw [hB, geodesicLine_one_apply]; rfl
  have hBim : B.im = Real.exp d := by rw [hB, geodesicLine_one_apply]; rfl
  have hIC : UpperHalfPlane.I.re ≠ C.re := by
    rw [show UpperHalfPlane.I.re = 0 from rfl]
    exact hC.ne
  have hBC : B.re ≠ C.re := by rw [hBre]; exact hC.ne
  set c₁ := circleCenter UpperHalfPlane.I C with hc₁
  set c₂ := circleCenter B C with hc₂
  set r₁ := Real.sqrt (Complex.normSq ((C : ℂ) - c₁)) with hr₁
  set r₂ := Real.sqrt (Complex.normSq ((C : ℂ) - c₂)) with hr₂
  -- the semicircles through `I`, `C` and through `B`, `C`: `I`, `B` and `C` are interior points
  have hn₁ : Complex.normSq ((C : ℂ) - c₁) = c₁ ^ 2 + 1 := by
    rw [normSq_sub_circleCenter hIC, Complex.normSq_apply]
    simp
    ring
  have hn₂ : Complex.normSq ((C : ℂ) - c₂) = c₂ ^ 2 + Real.exp d ^ 2 := by
    rw [normSq_sub_circleCenter hBC, Complex.normSq_apply]
    simp [hBre, hBim]
    ring
  have hnC : ∀ c : ℝ, Complex.normSq ((C : ℂ) - c) = (C.re - c) ^ 2 + C.im ^ 2 := fun c ↦ by
    rw [Complex.normSq_apply]
    simp
    ring
  have hr₁0 : 0 < r₁ := Real.sqrt_pos.2 (by rw [hn₁]; positivity)
  have hr₂0 : 0 < r₂ := Real.sqrt_pos.2 (by rw [hn₂]; positivity)
  have hr₁sq : r₁ ^ 2 = Complex.normSq ((C : ℂ) - c₁) := Real.sq_sqrt (Complex.normSq_nonneg _)
  have hr₂sq : r₂ ^ 2 = Complex.normSq ((C : ℂ) - c₂) := Real.sq_sqrt (Complex.normSq_nonneg _)
  have h1a : c₁ - r₁ < 0 := by
    rw [sub_neg]
    exact lt_sqrt_of_sq_lt (by rw [hn₁]; linarith)
  have h1b : C.re < c₁ + r₁ := by
    rw [← sub_lt_iff_lt_add']
    exact lt_sqrt_of_sq_lt (by rw [hnC]; nlinarith [C.im_pos])
  have h2a : c₂ - r₂ < 0 := by
    rw [sub_neg]
    exact lt_sqrt_of_sq_lt (by rw [hn₂]; nlinarith [Real.exp_pos d])
  have h2b : C.re < c₂ + r₂ := by
    rw [← sub_lt_iff_lt_add']
    exact lt_sqrt_of_sq_lt (by rw [hnC]; nlinarith [C.im_pos])
  -- the areas of the two ideal-vertex regions
  have hV₁ := volume_idealRegionAbove hr₁0 h1a hC.le h1b
  have hV₂ := volume_idealRegionAbove hr₂0 h2a hC.le h2b
  have hsub := idealRegionAbove_subset_of_normal_form hd hC
  rw [← hB, ← hc₂, ← hr₂, ← hc₁, ← hr₁] at hsub
  -- the triangle and the difference of the two regions have the same area
  have hT : volume (triangle UpperHalfPlane.I B C) =
      volume (idealRegionAbove c₁ r₁ 0 C.re \ idealRegionAbove c₂ r₂ 0 C.re) := by
    refine le_antisymm ?_ (measure_mono (diff_subset_triangle_of_normal_form hd hC))
    calc volume (triangle UpperHalfPlane.I B C)
        ≤ volume ((idealRegionAbove c₁ r₁ 0 C.re \ idealRegionAbove c₂ r₂ 0 C.re) ∪
            Set.range (geodesicLine (geodesicBetween B C))) :=
          measure_mono (triangle_subset_diff_union_of_normal_form hd hC)
      _ ≤ volume (idealRegionAbove c₁ r₁ 0 C.re \ idealRegionAbove c₂ r₂ 0 C.re) +
            volume (Set.range (geodesicLine (geodesicBetween B C))) := measure_union_le _ _
      _ = volume (idealRegionAbove c₁ r₁ 0 C.re \ idealRegionAbove c₂ r₂ 0 C.re) := by
          rw [volume_range_geodesicLine, add_zero]
  rw [hT, measure_sdiff hsub (measurableSet_idealRegionAbove _ _ _ _).nullMeasurableSet
    (by rw [hV₂]; exact ENNReal.ofReal_ne_top), hV₁, hV₂,
    ← ENNReal.ofReal_sub _ (sub_nonneg.2 (Real.arccos_le_arccos
      ((div_le_div_iff_of_pos_right hr₂0).2 (by linarith)))),
    interiorAngle_I_geodesicLine_one hd hC, interiorAngle_geodesicLine_one_I hd hC,
    interiorAngle_of_normal_form hd hC, ← hB, ← normSq_sub_circleCenter hIC,
    ← normSq_sub_circleCenter hBC, ← hc₁, ← hc₂, ← hr₁, ← hr₂]
  congr 1
  rw [zero_sub, zero_sub, neg_div, neg_div, Real.arccos_neg, Real.arccos_neg]
  ring

/-- Every nondegenerate triangle can be moved to normal form, possibly after swapping `A` and
`B`. -/
theorem exists_smul_eq_normal_form {A B C : ℍ} (hAB : A ≠ B)
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) :
    ∃ h : PSL(2, ℝ), ∃ d : ℝ, 0 < d ∧ 0 < (h • C).re ∧
      ((h • A = UpperHalfPlane.I ∧ h • B = geodesicLine 1 d) ∨
        (h • B = UpperHalfPlane.I ∧ h • A = geodesicLine 1 d)) := by
  have hA : (geodesicBetween A B)⁻¹ • A = UpperHalfPlane.I := by
    have h := smul_geodesicLine (geodesicBetween A B)⁻¹ (geodesicBetween A B) 0
    rwa [geodesicLine_geodesicBetween_zero, inv_mul_cancel, geodesicLine_zero, one_smul] at h
  have hB : (geodesicBetween A B)⁻¹ • B = geodesicLine 1 (dist A B) := by
    have h := smul_geodesicLine (geodesicBetween A B)⁻¹ (geodesicBetween A B) (dist A B)
    rwa [geodesicLine_geodesicBetween_dist, inv_mul_cancel] at h
  have hCre : ((geodesicBetween A B)⁻¹ • C : ℍ).re ≠ 0 := fun h ↦
    hC ((mem_range_geodesicLine_iff (geodesicBetween A B) C).2 h)
  have hSI : pslS • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [pslS_smul]
    apply UpperHalfPlane.coe_injective
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I, ← neg_inv,
      Complex.inv_I, neg_neg]
  rcases lt_or_gt_of_ne hCre with hneg | hpos
  · -- reflect through `z ↦ -exp d / z`, which swaps `I` and `i exp d`
    refine ⟨↑(dilation (dist A B)) * pslS * (geodesicBetween A B)⁻¹, dist A B, dist_pos.2 hAB,
      ?_, Or.inr ⟨?_, ?_⟩⟩
    · rw [mul_smul, mul_smul, UpperHalfPlane.pslMk_smul, ← UpperHalfPlane.coe_re,
        coe_dilation_smul, Complex.re_ofReal_mul, UpperHalfPlane.coe_re, re_pslS_smul]
      exact mul_pos (Real.exp_pos _)
        (div_pos (neg_pos.2 hneg) (Complex.normSq_pos.2 (ne_zero _)))
    · rw [mul_smul, mul_smul, hB, smul_geodesicLine, mul_one, ← one_mul pslS,
        geodesicLine_mul_pslS, smul_geodesicLine, mul_one,
        ← one_mul (↑(dilation (dist A B)) : PSL(2, ℝ)), geodesicLine_mul_dilation, add_neg_cancel,
        geodesicLine_zero, one_smul]
    · rw [mul_smul, mul_smul, hA, hSI, UpperHalfPlane.pslMk_smul,
        ← geodesicLine_one_eq_dilation_smul_I]
  · exact ⟨(geodesicBetween A B)⁻¹, dist A B, dist_pos.2 hAB, hpos, Or.inl ⟨hA, hB⟩⟩

/-- **The Gauss–Bonnet formula**: the invariant area of a hyperbolic triangle is its angular
defect `π - α - β - γ`. -/
theorem volume_triangle {A B C : ℍ} (hAB : A ≠ B)
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) :
    volume (triangle A B C) =
      ENNReal.ofReal (π - interiorAngle A B C - interiorAngle B C A - interiorAngle C A B) := by
  have hAC : A ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_left A B)
  have hBC : B ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_right A B)
  obtain ⟨h, d, hd, hCre, hcase⟩ := exists_smul_eq_normal_form hAB hC
  have hvol : volume (h • triangle A B C) = volume (triangle A B C) := by
    rw [MeasureTheory.measure_smul]
  rw [← hvol, smul_triangle h hAB hBC hAC.symm]
  rcases hcase with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · rw [hA, hB, volume_triangle_I_geodesicLine_one hd hCre, ← hA, ← hB,
      interiorAngle_smul h hAB hAC, interiorAngle_smul h hBC hAB.symm,
      interiorAngle_smul h hAC.symm hBC.symm]
  · have hAB' : h • A ≠ h • B := (MulAction.injective h).ne hAB
    have hC' : h • C ∉ Set.range (geodesicLine (geodesicBetween (h • A) (h • B))) := by
      rw [geodesicBetween_smul h hAB, ← smul_range_geodesicLine, Set.smul_mem_smul_set_iff]
      exact hC
    rw [← triangle_swap_left hAB' hC', hB, hA, volume_triangle_I_geodesicLine_one hd hCre, ← hB,
      ← hA, interiorAngle_smul h hAB.symm hBC, interiorAngle_smul h hAC hAB,
      interiorAngle_smul h hBC.symm hAC.symm, interiorAngle_comm B C A, interiorAngle_comm A B C,
      interiorAngle_comm C A B]
    congr 1
    ring

end TauCeti.UpperHalfPlane
