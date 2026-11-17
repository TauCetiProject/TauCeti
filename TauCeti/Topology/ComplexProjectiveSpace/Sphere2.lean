/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
public import TauCeti.Topology.Sphere.Suspension

/-!
# The Hopf map `S³ → S²` and `CP¹ = S²`

The **Hopf map** `h : S³ → S²` (`TauCeti.hopfSphere2`) sends a unit vector `(a, b)` of `ℂ²` to
`(|a|² - |b|², 2 Re (a conj b), 2 Im (a conj b))`. It is invariant under unit complex scalars and
its fibres are exactly the circle orbits, so it descends to a homeomorphism `CP¹ ≃ₜ S²`
(`TauCeti.ComplexProjectiveSpace.homeomorphSphere2`) sending `[e₀]` to the north pole
and `[e₁]` to the south pole.

## Main declarations

* `TauCeti.hopfSphere2`: the Hopf map `S³ → S²`, with `TauCeti.hopfSphere2_eq_hopfSphere2_iff`
  (its fibres are the circle orbits) and `TauCeti.hopfSphere2_surjective`.
* `TauCeti.ComplexProjectiveSpace.homeomorphSphere2`: `CP¹ ≃ₜ S²`, induced by the Hopf map.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Example 4.45 (the Hopf
  map) and Example 0.6 (`CP¹ = S²`).
-/

public section

noncomputable section

open Metric Real ComplexConjugate Matrix

namespace TauCeti

/-! ### The Hopf map and `CP¹ = S²` -/

section Hopf

/-- The coordinates `(|a|² - |b|², 2 Re (a conj b), 2 Im (a conj b))` of the Hopf map at
`(a, b)`. -/
private def hopfVector (a b : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[‖a‖ ^ 2 - ‖b‖ ^ 2, 2 * (a * conj b).re, 2 * (a * conj b).im]

private theorem continuous_hopfVector : Continuous fun p : ℂ × ℂ ↦ hopfVector p.1 p.2 := by
  unfold hopfVector
  fun_prop

private theorem norm_hopfVector {a b : ℂ} (h : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) :
    ‖hopfVector a b‖ = 1 := by
  have hz : (a * conj b).re ^ 2 + (a * conj b).im ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    have h := Complex.normSq_apply (a * conj b)
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_conj] at h
    linear_combination -h
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp only [hopfVector, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  linear_combination (‖a‖ ^ 2 + ‖b‖ ^ 2 + 1) * h + 4 * hz

/-- The two coordinates of a unit vector of `ℂ²` have square norms summing to `1`. -/
private theorem norm_sq_add_norm_sq (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    ‖(v : EuclideanSpace ℂ (Fin 2)) 0‖ ^ 2 + ‖(v : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq (v : EuclideanSpace ℂ (Fin 2))
  rw [norm_eq_of_mem_sphere v, Fin.sum_univ_two] at h
  linarith

/-- **The Hopf map** `S³ → S²`, `(a, b) ↦ (|a|² - |b|², 2 Re (a conj b), 2 Im (a conj b))`, from
the unit sphere of `ℂ²` to the unit sphere of `ℝ³`. -/
def hopfSphere2 : C(sphere (0 : EuclideanSpace ℂ (Fin 2)) 1, Sphere2) where
  toFun v := ⟨hopfVector ((v : EuclideanSpace ℂ (Fin 2)) 0) ((v : EuclideanSpace ℂ (Fin 2)) 1),
    mem_sphere_zero_iff_norm.2 (norm_hopfVector (norm_sq_add_norm_sq v))⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_hopfVector.comp (f := fun v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦
      ((v : EuclideanSpace ℂ (Fin 2)) 0, (v : EuclideanSpace ℂ (Fin 2)) 1)) (by fun_prop)

/-- The coordinates of the Hopf map. -/
theorem coe_hopfSphere2_apply (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    (hopfSphere2 v : EuclideanSpace ℝ (Fin 3)) =
      !₂[‖(v : EuclideanSpace ℂ (Fin 2)) 0‖ ^ 2 - ‖(v : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2,
        2 * ((v : EuclideanSpace ℂ (Fin 2)) 0 * conj ((v : EuclideanSpace ℂ (Fin 2)) 1)).re,
        2 * ((v : EuclideanSpace ℂ (Fin 2)) 0 * conj ((v : EuclideanSpace ℂ (Fin 2)) 1)).im] :=
  (rfl)

/-- **The Hopf map is invariant under unit complex scalars**: `|c a| = |a|`, `|c b| = |b|` and
`(c a) conj (c b) = |c|² a conj b = a conj b`. -/
@[simp]
theorem hopfSphere2_smul (c : sphere (0 : ℂ) 1) (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    hopfSphere2 (c • v) = hopfSphere2 v := by
  have hc : ‖(c : ℂ)‖ = 1 := norm_eq_of_mem_sphere c
  have hcc : (c : ℂ) * conj (c : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    simp
  have h (a b : ℂ) : (c : ℂ) * a * conj ((c : ℂ) * b) = a * conj b := by
    rw [map_mul]
    linear_combination (a * conj b) * hcc
  refine Subtype.ext ?_
  simp only [coe_hopfSphere2_apply, Sphere.coe_sphere_smul, PiLp.smul_apply, smul_eq_mul,
    norm_mul, hc, one_mul, h]

/-- Two pairs `(a, b)`, `(a', b')` of complex numbers with `|a|² + |b|² = 1 = |a'|² + |b'|²`,
`|a|² - |b|² = |a'|² - |b'|²` and `a conj b = a' conj b'` differ by a unit complex scalar. -/
private theorem exists_norm_eq_one_mul_eq {a b a' b' : ℂ} (hv : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1)
    (hw : ‖a'‖ ^ 2 + ‖b'‖ ^ 2 = 1) (h0 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = ‖a'‖ ^ 2 - ‖b'‖ ^ 2)
    (hz : a * conj b = a' * conj b') : ∃ c : ℂ, ‖c‖ = 1 ∧ c * a' = a ∧ c * b' = b := by
  have ha : ‖a‖ = ‖a'‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  have hb : ‖b‖ = ‖b'‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by linarith)
  by_cases ha' : a' = 0
  · -- Both first coordinates vanish, and the second coordinates are unit complex numbers.
    have ha0 : a = 0 := norm_eq_zero.1 (by rw [ha, ha', norm_zero])
    have hb' : ‖b'‖ = 1 := by
      rw [ha', norm_zero] at hw
      nlinarith [norm_nonneg b']
    have hb'0 : b' ≠ 0 := norm_ne_zero_iff.1 (by rw [hb']; exact one_ne_zero)
    exact ⟨b / b', by rw [norm_div, hb, hb', div_one], by rw [ha', ha0, mul_zero],
      div_mul_cancel₀ _ hb'0⟩
  · -- The scalar is `a / a'`; it carries `b'` to `b` because `a conj b = a' conj b'` and
    -- `|a| = |a'|`.
    have hnorm : a * conj a = a' * conj a' := by
      rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq, ha]
    have hconj : conj a * b = conj a' * b' := by
      simpa [mul_comm] using congrArg conj hz
    have hkey : a' * conj a' * (a * b' - a' * b) = 0 := by
      linear_combination (-(a * a')) * hconj + (a' * b) * hnorm
    have hne : a' * conj a' ≠ 0 := by
      rw [Complex.mul_conj]
      exact_mod_cast (Complex.normSq_pos.2 ha').ne'
    have hb'b : a * b' = a' * b := sub_eq_zero.1 ((mul_eq_zero.1 hkey).resolve_left hne)
    refine ⟨a / a', by rw [norm_div, ha, div_self (norm_ne_zero_iff.2 ha')],
      div_mul_cancel₀ _ ha', ?_⟩
    rw [div_mul_eq_mul_div, hb'b, mul_div_cancel_left₀ _ ha']

/-- **The fibres of the Hopf map are the circle orbits**: two unit vectors of `ℂ²` have the same
image exactly when they differ by a unit complex scalar. -/
theorem hopfSphere2_eq_hopfSphere2_iff {v w : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1} :
    hopfSphere2 v = hopfSphere2 w ↔ ∃ c : sphere (0 : ℂ) 1, c • w = v := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ by rw [← hc, hopfSphere2_smul]⟩
  have hcoord (i : Fin 3) := congrArg (fun x : Sphere2 ↦ (x : EuclideanSpace ℝ (Fin 3)) i) h
  have h1 := hcoord 1
  have h2 := hcoord 2
  simp only [coe_hopfSphere2_apply] at h1 h2
  obtain ⟨c, hc, hca, hcb⟩ := exists_norm_eq_one_mul_eq (norm_sq_add_norm_sq v)
    (norm_sq_add_norm_sq w) (by simpa [coe_hopfSphere2_apply] using hcoord 0)
    (Complex.ext (by simpa using h1) (by simpa using h2))
  refine ⟨⟨c, mem_sphere_zero_iff_norm.2 hc⟩, Subtype.ext ?_⟩
  ext i
  fin_cases i <;> simp [hca, hcb]

/-- The Hopf map at `(α, β conj z)`, for real `α`, `β` and a unit complex number `z`. -/
private theorem hopfVector_ofReal_mul_conj (α β : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    hopfVector α (β * conj z) = !₂[α ^ 2 - β ^ 2, 2 * α * β * z.re, 2 * α * β * z.im] := by
  have h : (α : ℂ) * conj ((β : ℂ) * conj z) = ((α * β : ℝ) : ℂ) * z := by
    rw [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    push_cast
    ring
  simp only [hopfVector, h, norm_mul, Complex.norm_conj, hz, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Complex.re_ofReal_mul, Complex.im_ofReal_mul, mul_assoc]

/-- **The Hopf map is surjective**: the point `(cos πt, sin πt · z)` of `S²` is the image of
`(cos (πt / 2), sin (πt / 2) conj z)`. -/
theorem hopfSphere2_surjective : Function.Surjective hopfSphere2 := by
  intro x
  obtain ⟨⟨t, z⟩, rfl⟩ := suspensionToSphere_surjective x
  have hz : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
  set θ := π * (t : ℝ) / 2
  have hθ : π * (t : ℝ) = 2 * θ := by ring
  have hv : ‖(!₂[((cos θ : ℝ) : ℂ), ((sin θ : ℝ) : ℂ) * conj (z : ℂ)] :
      EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul, Complex.norm_conj, hz, mul_one,
      Complex.norm_real, Real.norm_eq_abs, sq_abs,
      cos_sq_add_sin_sq]
  refine ⟨⟨_, mem_sphere_zero_iff_norm.2 hv⟩, Subtype.ext ?_⟩
  rw [coe_hopfSphere2_apply, ← hopfVector]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hopfVector_ofReal_mul_conj _ _ hz]
  ext i
  fin_cases i <;> simp [hθ, cos_two_mul', sin_two_mul, mul_assoc, mul_left_comm]

/-- The Hopf map sends the first standard basis vector `e₀` of `ℂ²` to the north pole. -/
@[simp]
theorem hopfSphere2_single_zero :
    hopfSphere2 ⟨EuclideanSpace.single 0 1, by simp⟩ = Sphere2.north := by
  refine Subtype.ext ?_
  rw [coe_hopfSphere2_apply, Sphere2.coe_north]
  simp

/-- The Hopf map sends the second standard basis vector `e₁` of `ℂ²` to the south pole. -/
@[simp]
theorem hopfSphere2_single_one :
    hopfSphere2 ⟨EuclideanSpace.single 1 1, by simp⟩ = Sphere2.south := by
  refine Subtype.ext ?_
  rw [coe_hopfSphere2_apply, Sphere2.coe_south]
  simp

end Hopf

namespace ComplexProjectiveSpace

/-! ### `CP¹ = S²` -/

section Sphere2

/-- The Hopf map, descended to `CP¹`. -/
private def toSphere2 : ComplexProjectiveSpace 1 → Sphere2 :=
  ComplexProjectiveSpace.lift 1 hopfSphere2 hopfSphere2_smul

private theorem toSphere2_mk (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    toSphere2 (mk 1 v) = hopfSphere2 v :=
  ComplexProjectiveSpace.lift_mk 1 _ _ v

private theorem continuous_toSphere2 : Continuous toSphere2 :=
  (isOpenQuotientMap_mk 1).isQuotientMap.continuous_iff.2 <|
    hopfSphere2.continuous.congr fun v ↦ (toSphere2_mk v).symm

private theorem toSphere2_bijective : Function.Bijective toSphere2 := by
  refine ⟨fun p q h ↦ ?_, fun x ↦ ?_⟩
  · induction p using ComplexProjectiveSpace.inductionOn with | h v => ?_
    induction q using ComplexProjectiveSpace.inductionOn with | h w => ?_
    rw [toSphere2_mk, toSphere2_mk] at h
    exact (mk_eq_mk_iff 1 v w).2 (hopfSphere2_eq_hopfSphere2_iff.1 h)
  · obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
    exact ⟨mk 1 v, toSphere2_mk v⟩

/-- **`CP¹` is the two-sphere**: the Hopf map `S³ → S²` descends to a homeomorphism from the circle
quotient `CP¹` of `S³`. -/
def homeomorphSphere2 : ComplexProjectiveSpace 1 ≃ₜ Sphere2 :=
  continuous_toSphere2.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ toSphere2_bijective)

/-- The homeomorphism `CP¹ ≃ₜ S²` sends `[v]` to the image of `v` under the Hopf map. -/
@[simp]
theorem homeomorphSphere2_mk (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    homeomorphSphere2 (mk 1 v) = hopfSphere2 v :=
  toSphere2_mk v

/-- The inverse of `CP¹ ≃ₜ S²` sends the image of `v` under the Hopf map to `[v]`. -/
@[simp]
theorem homeomorphSphere2_symm_hopfSphere2 (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    homeomorphSphere2.symm (hopfSphere2 v) = mk 1 v :=
  homeomorphSphere2.symm_apply_eq.2 (homeomorphSphere2_mk v).symm

/-- The base point `[e₀]` of `CP¹` goes to the north pole. -/
@[simp]
theorem homeomorphSphere2_basePoint : homeomorphSphere2 (basePoint 1) = Sphere2.north := by
  rw [basePoint_def, homeomorphSphere2_mk, hopfSphere2_single_zero]

end Sphere2

end ComplexProjectiveSpace

end TauCeti
