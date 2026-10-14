/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.InteriorAngle
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Semicircle
public import TauCeti.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# The oriented angle between two geodesics and the side of a line

`UpperHalfPlane.orientedAngle A B C` is the oriented angle at `A` from the geodesic towards `B`
to the geodesic towards `C`, the oriented angle (`Orientation.oangle` for the standard
orientation of `ℂ`) between the two velocities at `A`. Its absolute value is the unoriented
`UpperHalfPlane.interiorAngle A B C` (`UpperHalfPlane.interiorAngle_eq_abs_toReal_orientedAngle`),
it is invariant under `PSL(2, ℝ)` when `A ≠ B` and `A ≠ C` (`orientedAngle_smul`), and it is
additive (`UpperHalfPlane.orientedAngle_add`). For a transformation fixing `A`, its angle of
rotation is the argument of its derivative (`orientedAngle_smul_right_of_smul_eq_self`), and
every angle is attained by points arbitrarily close to `A` (`frequently_orientedAngle_eq`). For
`A ≠ C`, its sign is the side of the line through `A` and `B` on which `C` lies: `+1` on the left,
`-1` on the right, `0` on the line
(`orientedAngle_sign_eq_one_iff` and companions); in particular the angles of a nondegenerate
triangle lie strictly between `0` and `π` (`interiorAngle_pos`, `interiorAngle_lt_pi`). The same
sign reads off the closed half-planes via `mem_closure_leftHalfPlane_geodesicBetween_iff` and
`mem_closure_rightHalfPlane_geodesicBetween_iff`.
Three consequences used for polygons: orientation is cyclically invariant
(`mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane`: if `C` is left of `A → B` then `A` is
left of `B → C`), unoriented angles add when the middle geodesic lies between the outer two
(`interiorAngle_add`), and the angular order of two points on the left of `A → B` is read off
the side of the geodesic through the first (`toReal_orientedAngle_lt_iff`).

Source: Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 10 (2010), Corollary 5.2
p. 18 (Möbius transformations preserve angles and orientation). The sign–side correspondence and
the cyclic invariance are not stated in the sources.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup Set UpperHalfPlane
open scoped MatrixGroups Real Topology

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

attribute [local instance] Complex.finrank_real_complex_fact

/-! ### The oriented angle -/

/-- The oriented angle at `A` from the geodesic towards `B` to the geodesic towards `C`. -/
def orientedAngle (A B C : ℍ) : Real.Angle :=
  Complex.orientation.oangle (velocity (geodesicBetween A B) 0) (velocity (geodesicBetween A C) 0)

-- The body of `orientedAngle` is not `@[expose]`d, so downstream modules rewrite with this.
/-- `orientedAngle` is the oriented angle between the velocities at parameter `0`. -/
theorem orientedAngle_def (A B C : ℍ) :
    orientedAngle A B C = Complex.orientation.oangle (velocity (geodesicBetween A B) 0)
      (velocity (geodesicBetween A C) 0) := by
  rfl

/-- The unoriented angle is the absolute value of the oriented one. -/
theorem interiorAngle_eq_abs_toReal_orientedAngle (A B C : ℍ) :
    interiorAngle A B C = |(orientedAngle A B C).toReal| := by
  rw [interiorAngle_def, geodesicAngle_def, orientedAngle_def,
    Complex.orientation.angle_eq_abs_oangle_toReal (velocity_ne_zero _ _) (velocity_ne_zero _ _)]

/-- Reversing the two geodesics negates the oriented angle. -/
theorem orientedAngle_rev (A B C : ℍ) : orientedAngle A C B = -orientedAngle A B C :=
  Complex.orientation.oangle_rev _ _

/-- The oriented angle of a geodesic with itself is `0`. -/
@[simp]
theorem orientedAngle_self (A B : ℍ) : orientedAngle A B B = 0 :=
  Complex.orientation.oangle_self _

/-- Oriented angles at a common vertex add. -/
theorem orientedAngle_add (A B C D : ℍ) :
    orientedAngle A B C + orientedAngle A C D = orientedAngle A B D :=
  Complex.orientation.oangle_add (velocity_ne_zero _ _) (velocity_ne_zero _ _)
    (velocity_ne_zero _ _)

/-! ### The normal form: the geodesic from `A` to `B` as the imaginary axis -/

/-- The inverse of the geodesic line from `A` to `B` moves `A` to `I`. -/
theorem inv_geodesicBetween_smul_left (A B : ℍ) :
    (geodesicBetween A B)⁻¹ • A = UpperHalfPlane.I := by
  rw [inv_smul_eq_iff, ← geodesicLine_zero, geodesicLine_geodesicBetween_zero]

/-- The inverse of the geodesic line from `A` to `B` moves `B` up the imaginary axis, to the
point at distance `dist A B` from `I`. -/
theorem inv_geodesicBetween_smul_right (A B : ℍ) :
    (geodesicBetween A B)⁻¹ • B = geodesicLine 1 (dist A B) := by
  rw [inv_smul_eq_iff, smul_geodesicLine, mul_one, geodesicLine_geodesicBetween_dist]

/-- The geodesic line from `A` to `B` is also the line from `A` to some point `B' ≠ A` on it;
this lets results assuming `A ≠ B` apply to `geodesicBetween A A` as well. -/
theorem exists_ne_and_geodesicBetween_eq (A B : ℍ) :
    ∃ B' : ℍ, A ≠ B' ∧ geodesicBetween A B' = geodesicBetween A B := by
  have hne : A ≠ geodesicLine (geodesicBetween A B) 1 := fun h ↦
    zero_ne_one (geodesicLine_injective _ ((geodesicLine_geodesicBetween_zero A B).trans h))
  have hd : dist A (geodesicLine (geodesicBetween A B) 1) = 1 := by
    simpa using dist_geodesicLine (geodesicBetween A B) 0 1
  exact ⟨_, hne, (eq_geodesicBetween_of_geodesicLine_eq hne
    (geodesicLine_geodesicBetween_zero A B) (by rw [hd])).symm⟩

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation dilation)

attribute [local instance] Complex.finrank_real_complex_fact

/-! ### Invariance of the oriented angle -/

/-- **Möbius transformations preserve oriented angles** at `A`, for `A ≠ B` and `A ≠ C`.
Source: Katok, *Fuchsian groups, geodesic flows…* (Clay Math. Proc. 10), Corollary 5.2 p. 18. -/
theorem orientedAngle_smul (h : PSL(2, ℝ)) {A B C : ℍ} (hAB : A ≠ B) (hAC : A ≠ C) :
    orientedAngle (h • A) (h • B) (h • C) = orientedAngle A B C := by
  rw [orientedAngle_def, orientedAngle_def, geodesicBetween_smul h hAB,
    geodesicBetween_smul h hAC, velocity_mul, velocity_mul, geodesicLine_geodesicBetween_zero,
    geodesicLine_geodesicBetween_zero, Complex.oangle, Complex.oangle, map_mul, mul_mul_mul_comm,
    Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.arg_real_mul _ (by positivity [smulDeriv_ne_zero h A])]

/-! ### The normal form: rotations of the imaginary axis -/

/-- A transformation fixing `A` turns every geodesic from `A` through the argument of its
derivative at `A`. The angle is read counterclockwise, in `Real.Angle`. -/
theorem orientedAngle_smul_right_of_smul_eq_self {q : PSL(2, ℝ)} {A B : ℍ}
    (hA : q • A = A) (hAB : A ≠ B) :
    orientedAngle A B (q • B) = (smulDeriv q A).arg := by
  have hg : geodesicBetween A (q • B) = q * geodesicBetween A B := by
    simpa only [hA] using geodesicBetween_smul q hAB
  rw [orientedAngle_def, hg, velocity_mul, geodesicLine_geodesicBetween_zero]
  -- Compare both velocities to the unit vector, so multiplication adds arguments.
  rw [← Complex.orientation.oangle_sub_left (one_ne_zero : (1 : ℂ) ≠ 0)
    (velocity_ne_zero _ _) (mul_ne_zero (smulDeriv_ne_zero q A) (velocity_ne_zero _ _))]
  simp [Complex.arg_mul_coe_angle (smulDeriv_ne_zero q A) (velocity_ne_zero _ _)]

/-- The geodesic line from `I` to a point at positive parameter on the imaginary axis rotated by
`θ` is that rotated axis (compare `geodesicBetween_I_geodesicLine_one`). -/
theorem geodesicBetween_I_geodesicLine_rotation {t : ℝ} (ht : 0 < t) (θ : ℝ) :
    geodesicBetween UpperHalfPlane.I (geodesicLine (↑(rotation θ)) t) = ↑(rotation θ) := by
  have h0 : geodesicLine (↑(rotation θ)) 0 = UpperHalfPlane.I := by
    rw [geodesicLine_zero, pslMk_smul, rotation_smul_I]
  symm
  refine eq_geodesicBetween_of_geodesicLine_eq (fun h ↦ ht.ne ?_) h0 ?_
  · exact geodesicLine_injective _ (h0.trans h)
  · rw [← h0, dist_geodesicLine, zero_sub, abs_neg, abs_of_pos ht]

/-- The oriented angle at `I` from the geodesic towards the point `geodesicLine 1 d` of the
imaginary axis to the geodesic towards the point `geodesicLine (rotation θ) t` of its rotation by
`θ` is `2θ`, for `0 < d` and `0 < t`. -/
theorem orientedAngle_I_geodesicLine_one_rotation {d t : ℝ} (hd : 0 < d) (ht : 0 < t) (θ : ℝ) :
    orientedAngle UpperHalfPlane.I (geodesicLine 1 d) (geodesicLine (↑(rotation θ)) t) =
      ((2 * θ : ℝ) : Real.Angle) := by
  have h : 2 * (θ : ℂ) * Complex.I = ((2 * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [orientedAngle_def, geodesicBetween_I_geodesicLine_one hd,
    geodesicBetween_I_geodesicLine_rotation ht θ, velocity_one, velocity_rotation_zero,
    Complex.oangle, Real.exp_zero, Complex.ofReal_one, mul_one, Complex.conj_I, neg_mul,
    ← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_neg, h, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Real.Angle.cos_coe, ← Real.Angle.sin_coe,
    Complex.arg_cos_add_sin_mul_I_coe_angle]

/-- **Every direction at `A` is realized arbitrarily close to `A`.** For every oriented angle `φ`,
there are points `C ≠ A` arbitrarily close to `A` whose oriented angle at `A`, measured from the
geodesic towards `B`, is `φ`. -/
theorem frequently_orientedAngle_eq (A B : ℍ) (φ : Real.Angle) :
    ∃ᶠ C in 𝓝[≠] A, orientedAngle A B C = φ := by
  refine Filter.frequently_iff.2 fun {U} hU ↦ ?_
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
  -- replace `B` by a point `B' ≠ A` on the same ray, and move `A` to `I` along that ray
  obtain ⟨B', hAB', hB'⟩ := exists_ne_and_geodesicBetween_eq A B
  set R := geodesicBetween A B'
  have hRI : R • UpperHalfPlane.I = A := by
    rw [← geodesicLine_zero, geodesicLine_geodesicBetween_zero]
  -- the point at distance `ε / 2` from `A` on the ray at angle `φ`
  set G : PSL(2, ℝ) := R * ↑(rotation (φ.toReal / 2))
  have hG : geodesicLine G 0 = A := by
    rw [geodesicLine_zero, mul_smul, pslMk_smul, rotation_smul_I, hRI]
  have hdist : dist (geodesicLine G (ε / 2)) A = ε / 2 := by
    rw [← hG, dist_geodesicLine, sub_zero, abs_of_pos (half_pos hε)]
  have hAC : A ≠ geodesicLine G (ε / 2) := fun h ↦ (half_pos hε).ne' (by rw [← hdist, ← h,
    dist_self])
  refine ⟨geodesicLine G (ε / 2), hεU
    ⟨Metric.mem_ball.2 (by rw [hdist]; exact half_lt_self hε), hAC.symm⟩, ?_⟩
  obtain ⟨d, hd, hB⟩ : ∃ d, 0 < d ∧ R • geodesicLine 1 d = B' :=
    ⟨_, dist_pos.2 hAB', by rw [smul_geodesicLine, mul_one, geodesicLine_geodesicBetween_dist]⟩
  have hC : R • geodesicLine (↑(rotation (φ.toReal / 2))) (ε / 2) = geodesicLine G (ε / 2) :=
    smul_geodesicLine _ _ _
  have hIB : UpperHalfPlane.I ≠ geodesicLine 1 d := fun h ↦ hAB' (by
    rw [← hRI, h, hB])
  have hIC : UpperHalfPlane.I ≠ geodesicLine (↑(rotation (φ.toReal / 2))) (ε / 2) := fun h ↦
    hAC (by rw [← hRI, h, hC])
  rw [orientedAngle_def, ← hB', ← orientedAngle_def, ← hB, ← hC, ← hRI,
    orientedAngle_smul R hIB hIC,
    orientedAngle_I_geodesicLine_one_rotation hd (half_pos hε),
    mul_div_cancel₀ _ two_ne_zero, Real.Angle.coe_toReal]

/-! ### The sign of the oriented angle is the side of the line -/

/-- In the normal form `A = I`, `B` up the imaginary axis and `C` on the axis rotated by `θ`,
the sign of the oriented angle is the sign of `-C.re`. -/
private theorem sign_orientedAngle_I_geodesicLine_one_rotation {d t : ℝ} (hd : 0 < d)
    (ht : 0 < t) (θ : ℝ) :
    (orientedAngle UpperHalfPlane.I (geodesicLine 1 d) (geodesicLine (↑(rotation θ)) t)).sign =
      SignType.sign (-(geodesicLine (↑(rotation θ)) t).re) := by
  rw [orientedAngle_I_geodesicLine_one_rotation hd ht θ, Real.Angle.sign, Real.Angle.sin_coe,
    Real.sin_two_mul, mul_assoc, geodesicLine_def, pslMk_smul, re_rotation_smul_mk]
  have hy : 1 < Real.exp t ^ 2 := one_lt_pow₀ (Real.one_lt_exp_iff.2 ht) two_ne_zero
  have hN : 0 < Complex.normSq ((Real.cos θ : ℂ) - Complex.I * Real.exp t * Real.sin θ) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.sin_sq_add_cos_sq θ, mul_nonneg (sub_nonneg.2 hy.le) (sq_nonneg (Real.sin θ))]
  have h : -(Real.sin θ * Real.cos θ * (1 - Real.exp t ^ 2) /
      Complex.normSq ((Real.cos θ : ℂ) - Complex.I * Real.exp t * Real.sin θ)) =
      Real.sin θ * Real.cos θ * ((Real.exp t ^ 2 - 1) /
        Complex.normSq ((Real.cos θ : ℂ) - Complex.I * Real.exp t * Real.sin θ)) := by
    ring
  rw [h, sign_mul 2, sign_mul (Real.sin θ * Real.cos θ), sign_pos two_pos,
    sign_pos (div_pos (by linarith) hN), one_mul, mul_one]

/-- The sign of the oriented angle is the sign of `-C.re` once the geodesic from `A` to `B` is
moved onto the upward imaginary axis. -/
private theorem sign_orientedAngle_eq {A B C : ℍ} (hAC : A ≠ C) :
    (orientedAngle A B C).sign = SignType.sign (-((geodesicBetween A B)⁻¹ • C : ℍ).re) := by
  -- replace `B` by a point `B' ≠ A` of the same line
  obtain ⟨B, hAB, hB⟩ := exists_ne_and_geodesicBetween_eq A B
  rw [← hB, orientedAngle_def, ← hB, ← orientedAngle_def]
  have hIC : UpperHalfPlane.I ≠ (geodesicBetween A B)⁻¹ • C := by
    rw [← inv_geodesicBetween_smul_left A B]
    exact (MulAction.injective _).ne hAC
  obtain ⟨θ, hθ⟩ := exists_geodesicBetween_I_eq_rotation ((geodesicBetween A B)⁻¹ • C)
  rw [← orientedAngle_smul (geodesicBetween A B)⁻¹ hAB hAC, inv_geodesicBetween_smul_left,
    inv_geodesicBetween_smul_right,
    ← geodesicLine_geodesicBetween_dist UpperHalfPlane.I ((geodesicBetween A B)⁻¹ • C), hθ,
    sign_orientedAngle_I_geodesicLine_one_rotation (dist_pos.2 hAB) (dist_pos.2 hIC) θ]

/-- For `A ≠ C`, the sign of the oriented angle is `+1` exactly when `C` lies to the left of the
geodesic from `A` to `B`. -/
theorem orientedAngle_sign_eq_one_iff {A B C : ℍ} (hAC : A ≠ C) :
    (orientedAngle A B C).sign = 1 ↔ C ∈ leftHalfPlane (geodesicBetween A B) := by
  rw [sign_orientedAngle_eq hAC, sign_eq_one_iff, mem_leftHalfPlane_iff, neg_pos]

/-- For `A ≠ C`, the sign of the oriented angle is `-1` exactly when `C` lies to the right of the
geodesic from `A` to `B`. -/
theorem orientedAngle_sign_eq_neg_one_iff {A B C : ℍ} (hAC : A ≠ C) :
    (orientedAngle A B C).sign = -1 ↔ C ∈ rightHalfPlane (geodesicBetween A B) := by
  rw [sign_orientedAngle_eq hAC, sign_eq_neg_one_iff, mem_rightHalfPlane_iff, neg_lt_zero]

/-- For `A ≠ C`, the sign of the oriented angle is `0` exactly when `C` lies on the geodesic
through `A` and `B`. -/
theorem orientedAngle_sign_eq_zero_iff {A B C : ℍ} (hAC : A ≠ C) :
    (orientedAngle A B C).sign = 0 ↔ C ∈ Set.range (geodesicLine (geodesicBetween A B)) := by
  rw [sign_orientedAngle_eq hAC, sign_eq_zero_iff, mem_range_geodesicLine_iff, neg_eq_zero]

/-- For `A ≠ C`, `C` lies in the closed left half-plane of the geodesic from `A` to `B` exactly
when the oriented angle is not negative. -/
theorem mem_closure_leftHalfPlane_geodesicBetween_iff {A B C : ℍ} (hAC : A ≠ C) :
    C ∈ closure (leftHalfPlane (geodesicBetween A B)) ↔ (orientedAngle A B C).sign ≠ -1 := by
  rw [mem_closure_leftHalfPlane_iff, Ne, orientedAngle_sign_eq_neg_one_iff hAC,
    mem_rightHalfPlane_iff, not_lt]

/-- For `A ≠ C`, `C` lies in the closed right half-plane of the geodesic from `A` to `B` exactly
when the oriented angle is not positive. -/
theorem mem_closure_rightHalfPlane_geodesicBetween_iff {A B C : ℍ} (hAC : A ≠ C) :
    C ∈ closure (rightHalfPlane (geodesicBetween A B)) ↔ (orientedAngle A B C).sign ≠ 1 := by
  rw [mem_closure_rightHalfPlane_iff, Ne, orientedAngle_sign_eq_one_iff hAC,
    mem_leftHalfPlane_iff, not_lt]

/-- The oriented angle of a nondegenerate triangle is neither `0` nor `π`. -/
private theorem orientedAngle_ne_zero_and_ne_pi {A B C : ℍ}
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) :
    orientedAngle A B C ≠ 0 ∧ orientedAngle A B C ≠ π := by
  have hAC : A ≠ C := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_left A B) hC
  rwa [← orientedAngle_sign_eq_zero_iff hAC, Real.Angle.sign_eq_zero_iff, not_or] at hC

/-- The angle at `A` of a nondegenerate triangle is strictly positive. -/
theorem interiorAngle_pos {A B C : ℍ}
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) : 0 < interiorAngle A B C := by
  rw [interiorAngle_eq_abs_toReal_orientedAngle, abs_pos, Ne, Real.Angle.toReal_eq_zero_iff]
  exact (orientedAngle_ne_zero_and_ne_pi hC).1

/-- The angle at `A` of a nondegenerate triangle is strictly less than `π`. -/
theorem interiorAngle_lt_pi {A B C : ℍ}
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) : interiorAngle A B C < π := by
  rw [interiorAngle_eq_abs_toReal_orientedAngle, abs_lt]
  exact ⟨Real.Angle.neg_pi_lt_toReal _, (Real.Angle.toReal_le_pi _).lt_of_ne
    (mt Real.Angle.toReal_eq_pi_iff.1 (orientedAngle_ne_zero_and_ne_pi hC).2)⟩

/-! ### Reversal and cyclic invariance of the sides -/

/-- Reversing the direction of the geodesic through two distinct points swaps its two
half-planes. -/
theorem leftHalfPlane_geodesicBetween_swap {z w : ℍ} (hzw : z ≠ w) :
    leftHalfPlane (geodesicBetween w z) = rightHalfPlane (geodesicBetween z w) := by
  rw [geodesicBetween_swap hzw, leftHalfPlane_mul_pslS, rightHalfPlane_mul_dilation]

/-- Reversing the direction of the geodesic through two distinct points swaps its two
half-planes. -/
theorem rightHalfPlane_geodesicBetween_swap {z w : ℍ} (hzw : z ≠ w) :
    rightHalfPlane (geodesicBetween w z) = leftHalfPlane (geodesicBetween z w) := by
  rw [geodesicBetween_swap hzw, rightHalfPlane_mul_pslS, leftHalfPlane_mul_dilation]

/-- A point of an open left half-plane is not on the bounding line. -/
theorem notMem_range_geodesicLine_of_mem_leftHalfPlane {g : PSL(2, ℝ)} {z : ℍ}
    (hz : z ∈ leftHalfPlane g) : z ∉ Set.range (geodesicLine g) :=
  Set.disjoint_left.1 (disjoint_leftHalfPlane_range_geodesicLine g) hz

/-- **Orientation is cyclically invariant**: for `A ≠ B`, if `C` lies to the left of the geodesic
from `A` to `B`, then `A` lies to the left of the geodesic from `B` to `C`. -/
theorem mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane {A B C : ℍ} (hAB : A ≠ B)
    (h : C ∈ leftHalfPlane (geodesicBetween A B)) :
    A ∈ leftHalfPlane (geodesicBetween B C) := by
  have hBC : B ≠ C := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_right A B)
    (notMem_range_geodesicLine_of_mem_leftHalfPlane h)
  have hC : ((geodesicBetween A B)⁻¹ • C : ℍ).re < 0 := (mem_leftHalfPlane_iff _ _).1 h
  have hre : (geodesicLine 1 (dist A B)).re ≠ ((geodesicBetween A B)⁻¹ • C : ℍ).re := by
    rw [geodesicLine_one_apply, UpperHalfPlane.mk_re]
    exact hC.ne'
  rw [← Set.smul_mem_smul_set_iff (a := (geodesicBetween A B)⁻¹), smul_leftHalfPlane,
    ← geodesicBetween_smul _ hBC, inv_geodesicBetween_smul_left, inv_geodesicBetween_smul_right,
    mem_leftHalfPlane_geodesicBetween_iff_of_re_ne hre, geodesicLine_one_apply,
    UpperHalfPlane.mk_re, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I]
  have hd : 1 < Real.exp (dist A B) ^ 2 :=
    one_lt_pow₀ (Real.one_lt_exp_iff.2 (dist_pos.2 hAB)) two_ne_zero
  refine mul_neg_of_pos_of_neg (by linarith) ?_
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  nlinarith

/-- **Orientation is cyclically invariant**: for `A ≠ B`, if `C` lies to the right of the geodesic
from `A` to `B`, then `A` lies to the right of the geodesic from `B` to `C`. -/
theorem mem_rightHalfPlane_geodesicBetween_of_mem_rightHalfPlane {A B C : ℍ} (hAB : A ≠ B)
    (h : C ∈ rightHalfPlane (geodesicBetween A B)) :
    A ∈ rightHalfPlane (geodesicBetween B C) := by
  rw [← leftHalfPlane_geodesicBetween_swap hAB] at h
  have hAC : A ≠ C := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_right B A)
    (notMem_range_geodesicLine_of_mem_leftHalfPlane h)
  have hB := mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane hAB.symm h
  have hCB : C ≠ B := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_right A C)
    (notMem_range_geodesicLine_of_mem_leftHalfPlane hB)
  rw [← leftHalfPlane_geodesicBetween_swap hCB.symm]
  exact mem_leftHalfPlane_geodesicBetween_of_mem_leftHalfPlane hAC hB

/-! ### Additivity of unoriented angles and the angular order -/

/-- **Angles add**: if `C` and `D` lie to the left of the geodesic from `A` to `B`, and `D` lies to
the left of the geodesic from `A` to `C`, then the angle at `A` between `B` and `D` is the sum of
the angles between `B` and `C` and between `C` and `D`. -/
theorem interiorAngle_add {A B C D : ℍ} (hC : C ∈ leftHalfPlane (geodesicBetween A B))
    (hD : D ∈ leftHalfPlane (geodesicBetween A B))
    (hCD : D ∈ leftHalfPlane (geodesicBetween A C)) :
    interiorAngle A B D = interiorAngle A B C + interiorAngle A C D := by
  have hAC : A ≠ C := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_left A B)
    (notMem_range_geodesicLine_of_mem_leftHalfPlane hC)
  have hAD : A ≠ D := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_left A B)
    (notMem_range_geodesicLine_of_mem_leftHalfPlane hD)
  have h₁ := (orientedAngle_sign_eq_one_iff hAC).2 hC
  have h₂ := (orientedAngle_sign_eq_one_iff hAD).2 hCD
  have h₃ := (orientedAngle_sign_eq_one_iff hAD).2 hD
  have key' {θ : Real.Angle} (h : θ.sign = 1) : |θ.toReal| = θ.toReal :=
    abs_of_pos (Real.Angle.toReal_mem_Ioo_iff_sign_pos.2 h).1
  simp only [interiorAngle_eq_abs_toReal_orientedAngle, key' h₁, key' h₂, key' h₃]
  exact Complex.orientation.oangle_toReal_add_of_sign_eq (h₁.trans h₃.symm)
    (ne_of_eq_of_ne h₁ one_ne_zero)

/-- The angular order of two points to the left of a geodesic is read off the side of the
geodesic through the first. -/
theorem toReal_orientedAngle_lt_iff {A B C D : ℍ}
    (hC : C ∈ leftHalfPlane (geodesicBetween A B))
    (hD : D ∈ leftHalfPlane (geodesicBetween A B)) :
    (orientedAngle A B C).toReal < (orientedAngle A B D).toReal ↔
      D ∈ leftHalfPlane (geodesicBetween A C) := by
  have hAC : A ≠ C := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_left A B)
    (notMem_range_geodesicLine_of_mem_leftHalfPlane hC)
  have hAD : A ≠ D := ne_of_mem_of_not_mem (mem_range_geodesicLine_geodesicBetween_left A B)
    (notMem_range_geodesicLine_of_mem_leftHalfPlane hD)
  rw [← orientedAngle_sign_eq_one_iff hAD]
  have h₁ := (orientedAngle_sign_eq_one_iff hAC).2 hC
  have h₂ := (orientedAngle_sign_eq_one_iff hAD).2 hD
  exact (Complex.orientation.oangle_sign_eq_one_iff_toReal_lt_of_sign_eq (h₁.trans h₂.symm)
    (ne_of_eq_of_ne h₁ one_ne_zero)).symm

end TauCeti.UpperHalfPlane
