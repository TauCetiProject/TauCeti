/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.SpecialUnitary
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The Möbius action of `SL(2, ℂ)` on hyperbolic three-space

Hyperbolic three-space `ℍ³` is the upper half-space `UpperHalfSpace ℂ` of points `(w, t)` with
`w : ℂ` and `0 < t`. A matrix `A = (a b; c d)` of `SL(2, ℂ)` acts on it by the Möbius
transformation

`A • (w, t) = (((a w + b) conj (c w + d) + a conj c t²) / J, t / J)`,
`J = |c w + d|² + |c|² t²`,

the Poincaré extension to `ℍ³` of the fractional linear action of `A` on the Riemann sphere. In
quaternionic terms, writing `q = x + y i + t j` for the point `(x + y i, t)`, the image
`A • (w, t)` has quaternion `(a q + b)(c q + d)⁻¹`
(`TauCeti.UpperHalfSpace.toQuaternion_smul`); the group laws follow from this formula. The
central elements `±1` act trivially, so the action descends to `PSL(2, ℂ)`, where it is faithful
and transitive, and the stabilizer of `j = (0, 1)` is the image of `SU(2)`. This is the action
through which Kleinian groups, the discrete subgroups of `PSL(2, ℂ)`, act on hyperbolic
three-space.

## Main definitions

* `TauCeti.UpperHalfSpace.toQuaternion`: the point `(x + y i, t)` as the quaternion
  `x + y i + t j`.
* `TauCeti.UpperHalfSpace.denom`: the denominator `J = |c w + d|² + |c|² t²`.
* `TauCeti.UpperHalfSpace.mobius`: the Möbius transformation of a matrix in `SL(2, ℂ)`, which
  is the action `MulAction SL(2, ℂ) (UpperHalfSpace ℂ)`; the action of `PSL(2, ℂ)` is the
  action of representatives.
* `TauCeti.UpperHalfSpace.j`: the point `(0, 1)`.

## Main results

* `TauCeti.UpperHalfSpace.toQuaternion_smul`: the quaternionic formula `(a q + b)(c q + d)⁻¹`.
* `TauCeti.UpperHalfSpace.height_smul`, `TauCeti.UpperHalfSpace.denom_mul`: the height of
  `A • p` is `height p / J`, and `J` is a cocycle.
* `TauCeti.UpperHalfSpace.mem_center_iff_forall_smul_eq`: the matrices acting trivially are
  exactly the central ones `±1`; hence `FaithfulSMul PSL(2, ℂ) (UpperHalfSpace ℂ)`.
* `TauCeti.UpperHalfSpace.exists_smul_j_eq`: the action is transitive.
* `TauCeti.UpperHalfSpace.smul_j_eq_j_iff`, `TauCeti.UpperHalfSpace.stabilizer_j`: a matrix fixes
  `j` iff it is unitary, and the stabilizer of `j` in `PSL(2, ℂ)` is the image of `SU(2)`.

## References

* J. Elstrodt, F. Grunewald, J. Mennicke, *Groups Acting on Hyperbolic Space*, Springer (1998),
  Chapter 1 (the quaternionic model of `ℍ³` and the action of `PSL(2, ℂ)` on it).
* A. F. Beardon, *The Geometry of Discrete Groups*, Springer GTM 91 (1983), Chapters 3 and 4
  (the Poincaré extension of Möbius transformations and their quaternionic representation).
-/

public section

noncomputable section

open Matrix ComplexConjugate
open scoped MatrixGroups Quaternion

namespace TauCeti.UpperHalfSpace

/-- The quaternion `x + y i + t j` of the point `(x + y i, t)` of the upper half-space over
`ℂ`. -/
def toQuaternion (p : UpperHalfSpace ℂ) : ℍ[ℝ] :=
  ⟨(p : WithLp 2 (ℂ × ℝ)).fst.re, (p : WithLp 2 (ℂ × ℝ)).fst.im, height p, 0⟩

@[simp]
theorem re_toQuaternion (p : UpperHalfSpace ℂ) :
    (toQuaternion p).re = (p : WithLp 2 (ℂ × ℝ)).fst.re :=
  (rfl)

@[simp]
theorem imI_toQuaternion (p : UpperHalfSpace ℂ) :
    (toQuaternion p).imI = (p : WithLp 2 (ℂ × ℝ)).fst.im :=
  (rfl)

@[simp]
theorem imJ_toQuaternion (p : UpperHalfSpace ℂ) : (toQuaternion p).imJ = height p :=
  (rfl)

@[simp]
theorem imK_toQuaternion (p : UpperHalfSpace ℂ) : (toQuaternion p).imK = 0 :=
  (rfl)

/-- A point of the upper half-space over `ℂ` is determined by its quaternion. -/
theorem toQuaternion_injective : Function.Injective toQuaternion := by
  intro p q h
  refine ext_fst_height (Complex.ext ?_ ?_) ?_
  · simpa using congrArg QuaternionAlgebra.re h
  · simpa using congrArg QuaternionAlgebra.imI h
  · simpa using congrArg QuaternionAlgebra.imJ h

/-- The denominator `|c w + d|² + |c|² t²` of the Möbius action of `A = (a b; c d)` at the point
`(w, t)`. -/
def denom (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) : ℝ :=
  Complex.normSq (A 1 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 1 1) +
    Complex.normSq (A 1 0) * height p ^ 2

/-- The formula `J = |c w + d|² + |c|² t²` for the denominator of the Möbius action. -/
theorem denom_def (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    denom A p = Complex.normSq (A 1 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 1 1) +
      Complex.normSq (A 1 0) * height p ^ 2 :=
  (rfl)

/-- The denominator `J` of the Möbius action is positive: if `c = 0` then `d ≠ 0`. -/
theorem denom_pos (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) : 0 < denom A p := by
  rcases eq_or_ne (A 1 0) 0 with hc | hc
  · have hd : A 1 1 ≠ 0 := SpecialLinearGroup.apply_one_one_ne_zero_of_apply_one_zero_eq_zero hc
    simpa [denom_def, hc] using hd
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _)
      (mul_pos (Complex.normSq_pos.2 hc) (pow_pos (height_pos p) 2))

/-- The denominator `J` of the Möbius action is nonzero. -/
theorem denom_ne_zero (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) : denom A p ≠ 0 :=
  (denom_pos A p).ne'

/-- The denominator `J` is the squared norm of the quaternion `c q + d`. -/
theorem normSq_coe_mul_toQuaternion_add (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    Quaternion.normSq ((A 1 0 : ℍ[ℝ]) * toQuaternion p + (A 1 1 : ℍ[ℝ])) = denom A p := by
  rw [Quaternion.normSq_def']
  simp [denom_def, Complex.normSq_apply]
  ring

/-- The numerator of the quaternionic Möbius transformation `(a q + b)(c q + d)⁻¹`, computed as
`(a q + b) conj (c q + d)`; its `j`-coordinate is `t det A = t`. -/
private theorem mul_star_toQuaternion (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    ((A 0 0 : ℍ[ℝ]) * toQuaternion p + (A 0 1 : ℍ[ℝ])) *
        star ((A 1 0 : ℍ[ℝ]) * toQuaternion p + (A 1 1 : ℍ[ℝ])) =
      ⟨((A 0 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 0 1) *
          conj (A 1 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 1 1) +
          A 0 0 * conj (A 1 0) * ((height p ^ 2 : ℝ) : ℂ)).re,
        ((A 0 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 0 1) *
          conj (A 1 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 1 1) +
          A 0 0 * conj (A 1 0) * ((height p ^ 2 : ℝ) : ℂ)).im, height p, 0⟩ := by
  have hdet := A.det_coe
  rw [det_fin_two] at hdet
  have hre := congrArg Complex.re hdet
  have him := congrArg Complex.im hdet
  simp only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im, Complex.one_re,
    Complex.one_im] at hre him
  ext
  · simp [-Complex.ofReal_pow]; ring
  · simp [-Complex.ofReal_pow]; ring
  · simp [-Complex.ofReal_pow]; linear_combination (height p) * hre
  · simp [-Complex.ofReal_pow]; linear_combination (height p) * him

/-- The Möbius action of `A = (a b; c d)` in `SL(2, ℂ)` on the upper half-space over `ℂ`:
`(w, t) ↦ (((a w + b) conj (c w + d) + a conj c t²) / J, t / J)` with
`J = |c w + d|² + |c|² t²`. -/
def mobius (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) : UpperHalfSpace ℂ :=
  mk (WithLp.toLp 2
      (((A 0 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 0 1) *
          conj (A 1 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 1 1) +
          A 0 0 * conj (A 1 0) * ((height p ^ 2 : ℝ) : ℂ)) / (denom A p : ℂ),
        height p / denom A p))
    (div_pos (height_pos p) (denom_pos A p))

/-- The quaternionic form of `mobius`; `toQuaternion_smul` is its public statement. -/
private theorem toQuaternion_mobius (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    toQuaternion (mobius A p) =
      ((A 0 0 : ℍ[ℝ]) * toQuaternion p + (A 0 1 : ℍ[ℝ])) *
        ((A 1 0 : ℍ[ℝ]) * toQuaternion p + (A 1 1 : ℍ[ℝ]))⁻¹ := by
  rw [Quaternion.inv_def, normSq_coe_mul_toQuaternion_add, Algebra.mul_smul_comm,
    mul_star_toQuaternion]
  have := denom_ne_zero A p
  ext <;> simp [mobius, toQuaternion, Complex.div_re, Complex.div_im, -Complex.ofReal_pow] <;>
    field_simp

/-- The point `c q + d` of the quaternionic Möbius transformation is nonzero. -/
theorem coe_mul_toQuaternion_add_ne_zero (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    (A 1 0 : ℍ[ℝ]) * toQuaternion p + (A 1 1 : ℍ[ℝ]) ≠ 0 := by
  rw [← Quaternion.normSq_ne_zero, normSq_coe_mul_toQuaternion_add]
  exact denom_ne_zero A p

/-- The identity matrix acts as the identity. -/
theorem mobius_one (p : UpperHalfSpace ℂ) : mobius 1 p = p := by
  refine toQuaternion_injective ?_
  simp [toQuaternion_mobius]

/-- The Möbius transformation of a product is the composite of the Möbius transformations. -/
theorem mobius_mul (A B : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    mobius (A * B) p = mobius A (mobius B p) := by
  -- composing quaternionic Möbius transformations multiplies their coefficient matrices
  have comp (a b c d : ℍ[ℝ]) {u v : ℍ[ℝ]} (hv : v ≠ 0) :
      (a * (u * v⁻¹) + b) * (c * (u * v⁻¹) + d)⁻¹ =
        (a * u + b * v) * (c * u + d * v)⁻¹ := by
    have h₁ : a * (u * v⁻¹) + b = (a * u + b * v) * v⁻¹ := by
      rw [add_mul, mul_assoc, mul_assoc, mul_inv_cancel₀ hv, mul_one]
    have h₂ : c * (u * v⁻¹) + d = (c * u + d * v) * v⁻¹ := by
      rw [add_mul, mul_assoc, mul_assoc, mul_inv_cancel₀ hv, mul_one]
    rw [h₁, h₂, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left₀ hv]
  refine toQuaternion_injective ?_
  rw [toQuaternion_mobius, toQuaternion_mobius, toQuaternion_mobius,
    comp _ _ _ _ (coe_mul_toQuaternion_add_ne_zero B p)]
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Quaternion.coeComplex_add, Quaternion.coeComplex_mul]
  refine congrArg₂ (· * ·) ?_ (congrArg _ ?_) <;> noncomm_ring

/-- `SL(2, ℂ)` acts on the upper half-space over `ℂ` by Möbius transformations. -/
instance : MulAction SL(2, ℂ) (UpperHalfSpace ℂ) where
  smul := mobius
  one_smul := mobius_one
  mul_smul := mobius_mul

/-- The action of `SL(2, ℂ)` is the Möbius transformation `mobius`. -/
theorem smul_def (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) : A • p = mobius A p :=
  (rfl)

/-- The horizontal coordinate of `A • (w, t)` is
`((a w + b) conj (c w + d) + a conj c t²) / J`. -/
theorem fst_smul (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    ((A • p : UpperHalfSpace ℂ) : WithLp 2 (ℂ × ℝ)).fst =
      ((A 0 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 0 1) *
          conj (A 1 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 1 1) +
          A 0 0 * conj (A 1 0) * ((height p ^ 2 : ℝ) : ℂ)) / (denom A p : ℂ) := by
  simp [smul_def, mobius]

/-- The height of `A • (w, t)` is `t / J`. -/
@[simp]
theorem height_smul (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    height (A • p) = height p / denom A p := by
  simp [smul_def, mobius]

/-- **The quaternionic form of the Möbius action**: with `q = x + y i + t j` the quaternion of
`(x + y i, t)`, the point `A • (x + y i, t)` has quaternion `(a q + b)(c q + d)⁻¹`. -/
theorem toQuaternion_smul (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    toQuaternion (A • p) =
      ((A 0 0 : ℍ[ℝ]) * toQuaternion p + (A 0 1 : ℍ[ℝ])) *
        ((A 1 0 : ℍ[ℝ]) * toQuaternion p + (A 1 1 : ℍ[ℝ]))⁻¹ :=
  toQuaternion_mobius A p

/-- The denominator of the Möbius action is a cocycle: `J(A B, p) = J(A, B • p) J(B, p)`. -/
theorem denom_mul (A B : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    denom (A * B) p = denom A (B • p) * denom B p := by
  have h := congrArg height (mul_smul A B p)
  rw [height_smul, height_smul, height_smul, div_div] at h
  rw [div_eq_div_iff (denom_ne_zero _ _)
    (mul_ne_zero (denom_ne_zero _ _) (denom_ne_zero _ _))] at h
  rw [mul_comm (denom A _)]
  exact (mul_left_cancel₀ (height_pos p).ne' h).symm

/-- The central elements `±1` of `SL(2, ℂ)` act trivially on the upper half-space. -/
theorem smul_eq_of_mem_center {A : SL(2, ℂ)} (hA : A ∈ Subgroup.center SL(2, ℂ))
    (p : UpperHalfSpace ℂ) : A • p = p := by
  rcases SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp hA with rfl | rfl
  · exact one_smul _ p
  · have hneg : ((-1 : ℂ) : ℍ[ℝ]) = -1 := by ext <;> simp
    refine toQuaternion_injective ?_
    simp [toQuaternion_smul, hneg]

/-- `PSL(2, ℂ)` acts on the upper half-space through representatives in `SL(2, ℂ)`; this is
well defined because the center `{±1}` acts trivially (`smul_eq_of_mem_center`). -/
instance : MulAction PSL(2, ℂ) (UpperHalfSpace ℂ) :=
  MulAction.compHom _ <| QuotientGroup.lift (Subgroup.center SL(2, ℂ))
    (MulAction.toPermHom SL(2, ℂ) (UpperHalfSpace ℂ)) fun A hA ↦ Equiv.ext fun p ↦ by
      simpa using smul_eq_of_mem_center hA p

/-- The `PSL(2, ℂ)` action of the class of `A` is the `SL(2, ℂ)` action of `A`. -/
@[simp]
theorem pslMk_smul (A : SL(2, ℂ)) (p : UpperHalfSpace ℂ) :
    (A : PSL(2, ℂ)) • p = A • p :=
  (rfl)

/-! ### Upper triangular matrices, the matrix `(0 -1; 1 0)` and transitivity -/

/-- An upper triangular `A = (a b; 0 a⁻¹)` acts on the horizontal coordinate by the complex
similarity `w ↦ a (a w + b)`. -/
theorem fst_smul_of_apply_one_zero_eq_zero {A : SL(2, ℂ)} (hc : A 1 0 = 0)
    (p : UpperHalfSpace ℂ) :
    ((A • p : UpperHalfSpace ℂ) : WithLp 2 (ℂ × ℝ)).fst =
      A 0 0 * (A 0 0 * (p : WithLp 2 (ℂ × ℝ)).fst + A 0 1) := by
  have hdet := SpecialLinearGroup.apply_zero_zero_mul_apply_one_one_of_apply_one_zero_eq_zero hc
  have hd : A 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one hdet
  rw [fst_smul, eq_inv_of_mul_eq_one_left hdet]
  simp only [denom_def, hc, zero_mul, zero_add, map_zero, mul_zero, add_zero]
  rw [Complex.normSq_eq_conj_mul_self]
  have := (map_ne_zero (starRingEnd ℂ)).mpr hd
  field_simp

/-- An upper triangular `A = (a b; 0 a⁻¹)` multiplies heights by `|a|²`. -/
theorem height_smul_of_apply_one_zero_eq_zero {A : SL(2, ℂ)} (hc : A 1 0 = 0)
    (p : UpperHalfSpace ℂ) : height (A • p) = Complex.normSq (A 0 0) * height p := by
  have hdet := SpecialLinearGroup.apply_zero_zero_mul_apply_one_one_of_apply_one_zero_eq_zero hc
  rw [height_smul, eq_inv_of_mul_eq_one_left hdet, map_inv₀]
  simp [denom_def, hc, div_eq_inv_mul]

/-- The matrix `S = (0 -1; 1 0)` sends the horizontal coordinate `w` of `(w, t)` to
`-conj w / (|w|² + t²)`. -/
theorem fst_smul_of_coe_eq_S {A : SL(2, ℂ)}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0]) (p : UpperHalfSpace ℂ) :
    ((A • p : UpperHalfSpace ℂ) : WithLp 2 (ℂ × ℝ)).fst =
      -conj (p : WithLp 2 (ℂ × ℝ)).fst /
        ((Complex.normSq (p : WithLp 2 (ℂ × ℝ)).fst + height p ^ 2 : ℝ) : ℂ) := by
  rw [fst_smul]
  simp [hA, denom_def, neg_div]

/-- The matrix `S = (0 -1; 1 0)` sends the height `t` of `(w, t)` to `t / (|w|² + t²)`. -/
theorem height_smul_of_coe_eq_S {A : SL(2, ℂ)}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![0, -1; 1, 0]) (p : UpperHalfSpace ℂ) :
    height (A • p) =
      height p / (Complex.normSq (p : WithLp 2 (ℂ × ℝ)).fst + height p ^ 2) := by
  rw [height_smul]
  simp [hA, denom_def]

/-- The point `(0, 1)` of the upper half-space over `ℂ`, whose quaternion is `j`. -/
def j : UpperHalfSpace ℂ :=
  mk (WithLp.toLp 2 (0, 1)) (by simp)

@[simp]
theorem fst_j : (j : WithLp 2 (ℂ × ℝ)).fst = 0 :=
  congrArg WithLp.fst (coe_mk _ _)

@[simp]
theorem height_j : height j = 1 :=
  height_mk _ _

/-- Every point `(w, t)` is the image of `j = (0, 1)` under the upper triangular matrix
`(√t, w / √t; 0, 1 / √t)`. -/
theorem exists_smul_j_eq (p : UpperHalfSpace ℂ) : ∃ A : SL(2, ℂ), A • j = p := by
  have hs : 0 < Real.sqrt (height p) := Real.sqrt_pos.2 (height_pos p)
  have hs' : (Real.sqrt (height p) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  let A : SL(2, ℂ) := ⟨!![(Real.sqrt (height p) : ℂ), (p : WithLp 2 (ℂ × ℝ)).fst /
    Real.sqrt (height p); 0, (Real.sqrt (height p) : ℂ)⁻¹], by simp [det_fin_two, hs']⟩
  have hA : (A : Matrix (Fin 2) (Fin 2) ℂ) = !![(Real.sqrt (height p) : ℂ),
      (p : WithLp 2 (ℂ × ℝ)).fst / Real.sqrt (height p);
      0, (Real.sqrt (height p) : ℂ)⁻¹] :=
    rfl
  have hc : A 1 0 = 0 := by simp [hA]
  refine ⟨A, ext_fst_height ?_ ?_⟩
  · rw [fst_smul_of_apply_one_zero_eq_zero hc]
    simp [hA]
    field_simp
  · rw [height_smul_of_apply_one_zero_eq_zero hc]
    simp [hA, Complex.normSq_ofReal, Real.mul_self_sqrt (height_pos p).le]

/-- `SL(2, ℂ)` acts transitively on the upper half-space. -/
instance : MulAction.IsPretransitive SL(2, ℂ) (UpperHalfSpace ℂ) :=
  .of_orbit exists_smul_j_eq

/-- `PSL(2, ℂ)` acts transitively on the upper half-space. -/
instance : MulAction.IsPretransitive PSL(2, ℂ) (UpperHalfSpace ℂ) :=
  .of_smul_eq (M := SL(2, ℂ)) (fun A ↦ (A : PSL(2, ℂ))) (pslMk_smul _ _)

/-! ### Faithfulness of the projective action and the stabilizer of `j` -/

/-- A matrix fixing a point `(w, t)` has `J = 1` there and fixes the numerator of the horizontal
coordinate. -/
private theorem denom_eq_one_and_of_smul_eq {A : SL(2, ℂ)} {w : ℂ} {t : ℝ} (ht : 0 < t)
    (h : A • mk (WithLp.toLp 2 (w, t)) (by simpa using ht) =
      mk (WithLp.toLp 2 (w, t)) (by simpa using ht)) :
    Complex.normSq (A 1 0 * w + A 1 1) + Complex.normSq (A 1 0) * t ^ 2 = 1 ∧
      (A 0 0 * w + A 0 1) * conj (A 1 0 * w + A 1 1) +
        A 0 0 * conj (A 1 0) * ((t ^ 2 : ℝ) : ℂ) = w := by
  set p : UpperHalfSpace ℂ := mk (WithLp.toLp 2 (w, t)) (by simpa using ht)
  have hd : denom A p = 1 := by
    have hh := congrArg height h
    rw [height_smul, div_eq_iff (denom_ne_zero A p)] at hh
    exact mul_left_cancel₀ (height_pos p).ne' (by linarith)
  have hf := congrArg (fun q : UpperHalfSpace ℂ ↦ (q : WithLp 2 (ℂ × ℝ)).fst) h
  simp only [fst_smul, hd, Complex.ofReal_one, div_one] at hf
  simp only [denom_def, p, coe_mk, height_mk] at hd hf
  exact ⟨hd, hf⟩

/-- **The kernel of the Möbius action** is the center `{±1}` of `SL(2, ℂ)`: a matrix fixes every
point of the upper half-space exactly when it is central. -/
theorem mem_center_iff_forall_smul_eq {A : SL(2, ℂ)} :
    A ∈ Subgroup.center SL(2, ℂ) ↔ ∀ p : UpperHalfSpace ℂ, A • p = p := by
  refine ⟨fun hA ↦ smul_eq_of_mem_center hA, fun h ↦ ?_⟩
  obtain ⟨h₁, f₁⟩ := denom_eq_one_and_of_smul_eq (w := 0) one_pos (h _)
  obtain ⟨h₂, -⟩ := denom_eq_one_and_of_smul_eq (w := 0) two_pos (h _)
  obtain ⟨-, f₃⟩ := denom_eq_one_and_of_smul_eq (w := 1) one_pos (h _)
  simp only [mul_zero, zero_add, one_pow, mul_one, Complex.ofReal_one] at h₁ h₂ f₁ f₃
  have hc : A 1 0 = 0 := by
    rw [← Complex.normSq_eq_zero]
    nlinarith [Complex.normSq_nonneg (A 1 0)]
  simp only [hc, map_zero, mul_zero, add_zero, zero_add] at h₁ f₁ f₃
  have hdd : A 1 1 * conj (A 1 1) = 1 := by
    rw [Complex.mul_conj, h₁, Complex.ofReal_one]
  have hd : A 1 1 ≠ 0 := left_ne_zero_of_mul_eq_one hdd
  have hb : A 0 1 = 0 := by
    simpa [(map_ne_zero (starRingEnd ℂ)).mpr hd] using f₁
  have hdet := SpecialLinearGroup.apply_zero_zero_mul_apply_one_one_of_apply_one_zero_eq_zero hc
  -- `a d = 1` and `d conj d = 1` give `a = conj d`; then `a conj d = 1` gives `conj d = d`
  have ha : A 0 0 = conj (A 1 1) := by
    linear_combination conj (A 1 1) * hdet - A 0 0 * hdd
  have hCC : conj (A 1 1) * conj (A 1 1) = 1 := by
    simpa [hb, ha] using f₃
  have hC : conj (A 1 1) = A 1 1 := by
    linear_combination A 1 1 * hCC - conj (A 1 1) * hdd
  rw [hC] at ha
  refine SpecialLinearGroup.mem_center_iff.mpr ⟨A 1 1, ?_, ?_⟩
  · simpa [sq, ← ha] using hdet
  · ext i k
    fin_cases i <;> fin_cases k <;> simp [ha, hb, hc]

/-- The action of `PSL(2, ℂ)` on the upper half-space is faithful: only the identity fixes every
point. -/
instance : FaithfulSMul PSL(2, ℂ) (UpperHalfSpace ℂ) where
  eq_of_smul_eq_smul {g₁ g₂} h := by
    induction g₁ using QuotientGroup.induction_on with | H A => ?_
    induction g₂ using QuotientGroup.induction_on with | H B => ?_
    refine QuotientGroup.eq.mpr (mem_center_iff_forall_smul_eq.mpr fun p ↦ ?_)
    rw [mul_smul, ← pslMk_smul B, ← h p, pslMk_smul, inv_smul_smul]

/-- A matrix of `SL(2, ℂ)` fixes `j = (0, 1)` exactly when it is unitary. -/
theorem smul_j_eq_j_iff {A : SL(2, ℂ)} :
    A • j = j ↔ (A : Matrix (Fin 2) (Fin 2) ℂ) ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff]
  constructor
  · intro h
    obtain ⟨hS, hN⟩ := denom_eq_one_and_of_smul_eq (w := 0) (t := 1) one_pos h
    simp only [mul_zero, zero_add, one_pow, mul_one, Complex.ofReal_one] at hS hN
    have hS' : A 1 0 * conj (A 1 0) + A 1 1 * conj (A 1 1) = 1 := by
      rw [Complex.mul_conj, Complex.mul_conj]
      exact_mod_cast by linarith
    have hdet := A.det_coe
    rw [det_fin_two] at hdet
    -- orthogonality of the rows and `det A = 1` force `a = conj d` and `b = -conj c`
    have ha : A 0 0 = conj (A 1 1) := by
      linear_combination (-A 0 0) * hS' + A 1 0 * hN + conj (A 1 1) * hdet
    have hb : A 0 1 = -conj (A 1 0) := by
      linear_combination (-A 0 1) * hS' + A 1 1 * hN - conj (A 1 0) * hdet
    have h₀₀ : A 0 0 * conj (A 0 0) + A 0 1 * conj (A 0 1) = 1 := by
      rw [ha, hb, Complex.conj_conj, map_neg, Complex.conj_conj]
      linear_combination hS'
    have h₀₁ : A 0 0 * conj (A 1 0) + A 0 1 * conj (A 1 1) = 0 := by
      rw [ha, hb]
      ring
    have h₁₀ : A 1 0 * conj (A 0 0) + A 1 1 * conj (A 0 1) = 0 := by
      rw [ha, hb, Complex.conj_conj, map_neg, Complex.conj_conj]
      ring
    rw [← Matrix.ext_iff]
    simpa [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using
      (⟨⟨h₀₀, h₀₁⟩, h₁₀, hS'⟩ : (_ ∧ _) ∧ _ ∧ _)
  · intro h
    have e₀₁ : A 0 0 * conj (A 1 0) + A 0 1 * conj (A 1 1) = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 0) 1
    have e₁₁ : A 1 0 * conj (A 1 0) + A 1 1 * conj (A 1 1) = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 1) 1
    have hd : denom A j = 1 := by
      simp only [denom_def, fst_j, height_j, mul_zero, zero_add, one_pow, mul_one]
      have := congrArg Complex.re e₁₁
      simp only [Complex.mul_conj, Complex.add_re, Complex.ofReal_re, Complex.one_re] at this
      linarith
    refine ext_fst_height ?_ ?_
    · rw [fst_smul, hd]
      simp only [fst_j, height_j, mul_zero, zero_add, one_pow, Complex.ofReal_one, mul_one,
        div_one]
      linear_combination e₀₁
    · rw [height_smul, hd, div_one]

/-- **The stabilizer of `j = (0, 1)` in `PSL(2, ℂ)` is the projective special unitary group**, the
image of `SU(2)`. -/
theorem stabilizer_j :
    MulAction.stabilizer PSL(2, ℂ) j =
      (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* PSL(2, ℂ)).range := by
  ext g
  induction g using QuotientGroup.induction_on with | H A => ?_
  rw [MulAction.mem_stabilizer_iff, pslMk_smul, smul_j_eq_j_iff,
    specialUnitaryGroup.mk_mem_range_toPSL_iff]

end TauCeti.UpperHalfSpace
