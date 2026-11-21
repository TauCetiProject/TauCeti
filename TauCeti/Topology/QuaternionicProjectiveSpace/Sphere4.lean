/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.QuaternionicProjectiveSpace.Homogeneous
public import TauCeti.Topology.Algebra.Quaternion.Unitary

/-!
# The quaternionic Hopf map `S⁷ → S⁴` and `HP¹ = S⁴`

The **quaternionic Hopf map** `h : S⁷ → S⁴` (`TauCeti.hopfSphere4`) sends a unit vector `(a, b)`
of `ℍ²` to the point `(|a|² - |b|², 2 a b*)` of the unit sphere of `ℝ × ℍ`, with the Euclidean
norm; here `b*` is the quaternion conjugate `star b`. It is invariant under right multiplication
by unit quaternions, since `(a q) (b q)* = a q q* b* = a b*`, and its fibres are exactly the
orbits of this action (`TauCeti.hopfSphere4_eq_hopfSphere4_iff`). It is onto
(`TauCeti.hopfSphere4_surjective`), so it descends to a homeomorphism `HP¹ ≃ₜ S⁴`
(`TauCeti.QuaternionicProjectiveSpace.homeomorphSphere4`) from the quaternionic projective line,
the quotient of `S⁷` by the unit quaternions. It sends the base point `[e₀]` to the north pole
`(1, 0)` and `[e₁]` to the south pole `(-1, 0)`.

## Main declarations

* `TauCeti.hopfSphere4`: the quaternionic Hopf map `S⁷ → S⁴`.
* `TauCeti.hopfSphere4_eq_hopfSphere4_iff`: its fibres are the orbits of the unit quaternions.
* `TauCeti.hopfSphere4_surjective`: it is onto.
* `TauCeti.QuaternionicProjectiveSpace.homeomorphSphere4`: `HP¹ ≃ₜ S⁴`, induced by the Hopf map.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 4.45 (the Hopf
  maps) and Example 0.6 (`HP¹ = S⁴`).
-/

public section

noncomputable section

open Metric MulOpposite Quaternion
open scoped RightActions

namespace TauCeti

/-! ### The quaternionic Hopf map -/

section Hopf

/-- The coordinates `(|a|² - |b|², 2 a b*)` of the quaternionic Hopf map at `(a, b)`. -/
private def hopfVector4 (a b : ℍ) : WithLp 2 (ℝ × ℍ) :=
  WithLp.toLp 2 (‖a‖ ^ 2 - ‖b‖ ^ 2, (2 : ℝ) • (a * star b))

private theorem norm_hopfVector4 {a b : ℍ} (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ‖hopfVector4 a b‖ = 1 := by
  have hsq : ‖hopfVector4 a b‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [hopfVector4, WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs, norm_smul,
      norm_mul, norm_star]
    linear_combination (‖a‖ ^ 2 + ‖b‖ ^ 2 + 1) * h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

/-- The two coordinates of a unit vector of `ℍ²` have square norms summing to `1`. -/
private theorem norm_sq_add_norm_sq (v : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    ‖(v : PiLp 2 fun _ : Fin 2 ↦ ℍ) 0‖ ^ 2 + ‖(v : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1‖ ^ 2 = 1 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 ↦ ℍ) (v : PiLp 2 fun _ : Fin 2 ↦ ℍ)
  rw [norm_eq_of_mem_sphere v, Fin.sum_univ_two] at h
  linarith

/-- **The quaternionic Hopf map** `S⁷ → S⁴`, `(a, b) ↦ (|a|² - |b|², 2 a b*)`, from the unit
sphere of `ℍ²` to the unit sphere of `ℝ × ℍ`. -/
def hopfSphere4 : C(sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1, sphere (0 : WithLp 2 (ℝ × ℍ)) 1) where
  toFun v := ⟨hopfVector4 ((v : PiLp 2 fun _ : Fin 2 ↦ ℍ) 0) ((v : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1),
    mem_sphere_zero_iff_norm.2 (norm_hopfVector4 (norm_sq_add_norm_sq v))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    unfold hopfVector4
    fun_prop

/-- The coordinates of the quaternionic Hopf map. -/
theorem coe_hopfSphere4_apply (v : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    (hopfSphere4 v : WithLp 2 (ℝ × ℍ)) =
      WithLp.toLp 2
        (‖(v : PiLp 2 fun _ : Fin 2 ↦ ℍ) 0‖ ^ 2 - ‖(v : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1‖ ^ 2,
        (2 : ℝ) • ((v : PiLp 2 fun _ : Fin 2 ↦ ℍ) 0 * star ((v : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1))) :=
  (rfl)

/-- **The quaternionic Hopf map is invariant under right multiplication by unit quaternions**:
`|a q| = |a|`, `|b q| = |b|` and `(a q) (b q)* = a q q* b* = a b*`. -/
@[simp]
theorem hopfSphere4_op_smul (q : sphere (0 : ℍ) 1) (v : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    hopfSphere4 (v <• q) = hopfSphere4 v := by
  have hq : ‖(q : ℍ)‖ = 1 := norm_eq_of_mem_sphere q
  have hqq : (q : ℍ) * star (q : ℍ) = 1 :=
    Unitary.mul_star_self_of_mem ((mem_unitary_iff_mem_sphere_zero_one _).2 q.2)
  have h (a b : ℍ) : a * (q : ℍ) * star (b * (q : ℍ)) = a * star b := by
    rw [star_mul, mul_assoc, ← mul_assoc (q : ℍ), hqq, one_mul]
  refine Subtype.ext ?_
  simp only [coe_hopfSphere4_apply, Sphere.coe_op_sphere_smul, unop_op, PiLp.smul_apply,
    op_smul_eq_mul, norm_mul, hq, mul_one, h]

/-- Two pairs `(a, b)`, `(a', b')` of quaternions with `|a|² + |b|² = 1 = |a'|² + |b'|²`,
`|a|² - |b|² = |a'|² - |b'|²` and `a b* = a' b'*` differ by a unit quaternion on the right. -/
private theorem exists_norm_eq_one_mul_eq {a b a' b' : ℍ} (hv : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1)
    (hw : ‖a'‖ ^ 2 + ‖b'‖ ^ 2 = 1) (h0 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = ‖a'‖ ^ 2 - ‖b'‖ ^ 2)
    (hz : a * star b = a' * star b') : ∃ q : ℍ, ‖q‖ = 1 ∧ a' * q = a ∧ b' * q = b := by
  have ha : ‖a‖ = ‖a'‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  have hb : ‖b‖ = ‖b'‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  by_cases ha' : a' = 0
  · -- Both first coordinates vanish, and the second coordinates are unit quaternions.
    have ha0 : a = 0 := norm_eq_zero.1 (by rw [ha, ha', norm_zero])
    have hb' : ‖b'‖ = 1 := by
      rw [ha', norm_zero] at hw
      nlinarith [norm_nonneg b']
    have hb'0 : b' ≠ 0 := norm_ne_zero_iff.1 (by rw [hb']; exact one_ne_zero)
    exact ⟨b'⁻¹ * b, by rw [norm_mul, norm_inv, hb, hb', inv_one, one_mul],
      by rw [ha', ha0, zero_mul], mul_inv_cancel_left₀ hb'0 b⟩
  · -- The quaternion is `a'⁻¹ a`. It carries `b'` to `b`: both sides of `b' a'⁻¹ a = b` give
    -- `b ā` after right multiplication by `ā`, because `a ā = |a|² = |a'|² = a' ā'` and
    -- `b ā = b' ā'`.
    have hconj : b * star a = b' * star a' := by
      simpa [star_mul] using congrArg star hz
    have hnorm : a * star a = a' * star a' := by
      rw [self_mul_star, self_mul_star, normSq_eq_norm_mul_self, normSq_eq_norm_mul_self, ha]
    have ha0 : a ≠ 0 := norm_ne_zero_iff.1 (by rw [ha]; exact norm_ne_zero_iff.2 ha')
    refine ⟨a'⁻¹ * a, by rw [norm_mul, norm_inv, ha, inv_mul_cancel₀ (norm_ne_zero_iff.2 ha')],
      mul_inv_cancel_left₀ ha' a, mul_right_cancel₀ (star_ne_zero.2 ha0) ?_⟩
    calc b' * (a'⁻¹ * a) * star a = b' * a'⁻¹ * (a * star a) := by simp only [mul_assoc]
      _ = b' * a'⁻¹ * (a' * star a') := by rw [hnorm]
      _ = b' * star a' := by rw [← mul_assoc, inv_mul_cancel_right₀ ha']
      _ = b * star a := hconj.symm

/-- **The fibres of the quaternionic Hopf map are the orbits of the unit quaternions**: two unit
vectors of `ℍ²` have the same image exactly when they differ by a unit quaternion on the right. -/
theorem hopfSphere4_eq_hopfSphere4_iff {v w : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1} :
    hopfSphere4 v = hopfSphere4 w ↔ ∃ q : sphere (0 : ℍ) 1, w <• q = v := by
  refine ⟨fun h ↦ ?_, fun ⟨q, hq⟩ ↦ by rw [← hq, hopfSphere4_op_smul]⟩
  have h' := congrArg (fun x : sphere (0 : WithLp 2 (ℝ × ℍ)) 1 ↦
    WithLp.ofLp (x : WithLp 2 (ℝ × ℍ))) h
  simp only [coe_hopfSphere4_apply, WithLp.ofLp_toLp, Prod.mk.injEq] at h'
  obtain ⟨q, hq, hqa, hqb⟩ := exists_norm_eq_one_mul_eq (norm_sq_add_norm_sq v)
    (norm_sq_add_norm_sq w) h'.1 (smul_right_injective ℍ two_ne_zero h'.2)
  refine ⟨⟨q, mem_sphere_zero_iff_norm.2 hq⟩, Subtype.ext (PiLp.ext fun i ↦ ?_)⟩
  fin_cases i <;> simp [hqa, hqb]

/-- **The quaternionic Hopf map is surjective**: for `t ≠ -1`, the point `(t, w)` of `S⁴` is the
image of `(r, (2 r)⁻¹ w*)` with `r = √((1 + t) / 2)`, and the south pole `(-1, 0)` is the image of
`(0, 1)`. -/
theorem hopfSphere4_surjective : Function.Surjective hopfSphere4 := by
  rintro ⟨x, hx⟩
  obtain ⟨⟨t, w⟩, rfl⟩ : ∃ p, WithLp.toLp 2 p = x := ⟨WithLp.ofLp x, by simp⟩
  have hsq : t ^ 2 + ‖w‖ ^ 2 = 1 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (t, w))
    rw [mem_sphere_zero_iff_norm.1 hx] at h
    simpa [Real.norm_eq_abs, sq_abs] using h.symm
  by_cases ht : t = -1
  · -- The south pole is the image of `e₁`.
    subst ht
    have hw : w = 0 := by
      rw [← norm_eq_zero]
      nlinarith [norm_nonneg w]
    subst hw
    refine ⟨⟨WithLp.toLp 2 (Pi.single 1 1), by simp⟩, Subtype.ext ?_⟩
    rw [coe_hopfSphere4_apply]
    simp
  · have ht1 : 0 < 1 + t := by
      have : -1 ≤ t := by nlinarith [norm_nonneg w]
      exact lt_of_le_of_ne (by linarith) (fun h ↦ ht (by linarith))
    set r := √((1 + t) / 2)
    have hr0 : 0 < r := Real.sqrt_pos.2 (by linarith)
    have hrr : r ^ 2 = (1 + t) / 2 := Real.sq_sqrt (by linarith)
    set b : ℍ := (2 * r)⁻¹ • star w
    have hb : ‖b‖ ^ 2 = (1 - t) / 2 := by
      have hnb : ‖b‖ = (2 * r)⁻¹ * ‖w‖ := by
        rw [norm_smul, _root_.norm_star, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 (mul_pos two_pos hr0))]
      rw [hnb, mul_pow, inv_pow, mul_pow, hrr]
      field_simp
      linear_combination hsq
    have hv : ‖(WithLp.toLp 2 ![(r : ℍ), b] : PiLp 2 fun _ : Fin 2 ↦ ℍ)‖ = 1 := by
      refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 ?_
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_coe,
        Real.norm_eq_abs, sq_abs, hrr, hb]
      ring
    refine ⟨⟨_, mem_sphere_zero_iff_norm.2 hv⟩, Subtype.ext ?_⟩
    rw [coe_hopfSphere4_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_coe,
      Real.norm_eq_abs, sq_abs, hrr, hb]
    congr 2
    · ring
    · have hsb : star b = (2 * r)⁻¹ • w := by
        simp only [b, Quaternion.star_smul, star_star]
      rw [hsb, coe_mul_eq_smul, smul_smul, smul_smul,
        mul_inv_cancel₀ (mul_pos two_pos hr0).ne', one_smul]

/-- The quaternionic Hopf map sends the first standard basis vector `e₀` of `ℍ²` to the north
pole `(1, 0)`. -/
@[simp]
theorem coe_hopfSphere4_single_zero :
    (hopfSphere4 ⟨PiLp.single 2 0 1, by simp⟩ : WithLp 2 (ℝ × ℍ)) =
      WithLp.toLp 2 (1, 0) := by
  rw [coe_hopfSphere4_apply]
  simp

/-- The quaternionic Hopf map sends the second standard basis vector `e₁` of `ℍ²` to the south
pole `(-1, 0)`. -/
@[simp]
theorem coe_hopfSphere4_single_one :
    (hopfSphere4 ⟨PiLp.single 2 1 1, by simp⟩ : WithLp 2 (ℝ × ℍ)) =
      WithLp.toLp 2 (-1, 0) := by
  rw [coe_hopfSphere4_apply]
  simp

end Hopf

namespace QuaternionicProjectiveSpace

/-! ### `HP¹ = S⁴` -/

section Sphere4

/-- The quaternionic Hopf map, descended to `HP¹`. -/
private def toSphere4 : QuaternionicProjectiveSpace 1 → sphere (0 : WithLp 2 (ℝ × ℍ)) 1 :=
  QuaternionicProjectiveSpace.lift 1 hopfSphere4 hopfSphere4_op_smul

private theorem toSphere4_mk (v : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    toSphere4 (mk 1 v) = hopfSphere4 v :=
  QuaternionicProjectiveSpace.lift_mk 1 _ _ v

private theorem continuous_toSphere4 : Continuous toSphere4 :=
  (isOpenQuotientMap_mk 1).isQuotientMap.continuous_iff.2 <|
    hopfSphere4.continuous.congr fun v ↦ (toSphere4_mk v).symm

private theorem toSphere4_bijective : Function.Bijective toSphere4 := by
  refine ⟨fun p p' h ↦ ?_, fun x ↦ ?_⟩
  · induction p using QuaternionicProjectiveSpace.inductionOn with | h v => ?_
    induction p' using QuaternionicProjectiveSpace.inductionOn with | h w => ?_
    rw [toSphere4_mk, toSphere4_mk] at h
    exact (mk_eq_mk_iff 1 v w).2 (hopfSphere4_eq_hopfSphere4_iff.1 h)
  · obtain ⟨v, rfl⟩ := hopfSphere4_surjective x
    exact ⟨mk 1 v, toSphere4_mk v⟩

/-- **The quaternionic projective line is the four-sphere**: the quaternionic Hopf map `S⁷ → S⁴`
descends to a homeomorphism from the quotient `HP¹` of `S⁷` by the unit quaternions. -/
def homeomorphSphere4 : QuaternionicProjectiveSpace 1 ≃ₜ sphere (0 : WithLp 2 (ℝ × ℍ)) 1 :=
  continuous_toSphere4.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ toSphere4_bijective)

/-- The homeomorphism `HP¹ ≃ₜ S⁴` sends `[v]` to the image of `v` under the Hopf map. -/
@[simp]
theorem homeomorphSphere4_mk (v : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    homeomorphSphere4 (mk 1 v) = hopfSphere4 v :=
  toSphere4_mk v

/-- The inverse of `HP¹ ≃ₜ S⁴` sends the image of `v` under the Hopf map to `[v]`. -/
@[simp]
theorem homeomorphSphere4_symm_hopfSphere4 (v : sphere (0 : PiLp 2 fun _ : Fin 2 ↦ ℍ) 1) :
    homeomorphSphere4.symm (hopfSphere4 v) = mk 1 v :=
  homeomorphSphere4.symm_apply_eq.2 (homeomorphSphere4_mk v).symm

/-- The base point `[e₀]` of `HP¹` goes to the north pole `(1, 0)`. -/
@[simp]
theorem coe_homeomorphSphere4_basePoint :
    (homeomorphSphere4 (basePoint 1) : WithLp 2 (ℝ × ℍ)) = WithLp.toLp 2 (1, 0) := by
  rw [basePoint_def, homeomorphSphere4_mk]
  simp

end Sphere4

end QuaternionicProjectiveSpace

end TauCeti
