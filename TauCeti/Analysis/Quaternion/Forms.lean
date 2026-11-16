/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Quaternion
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The quaternionic forms `dq` and `Dq`

In the coordinates `q = t + i x + j y + k z` of `ℍ`, read on the integration domain `Fin 4 → ℝ`
in the order `(t, x, y, z)`, this file defines the constant quaternion-valued `1`-form

`dq = dt + i dx + j dy + k dz`

and the constant quaternion-valued `3`-form

`Dq = dx∧dy∧dz − i dt∧dy∧dz − j dt∧dz∧dx − k dt∧dx∧dy`.

Both forms are constant, so each is given by its value at every base point: a continuous real
linear map for `dq` and a continuous real alternating map for `Dq`. The form `Dq` is the surface
element of quaternionic analysis: classically, for `f` of class `C¹`, `d (Dq * f)` and
`d (f * Dq)` are the left and right Cauchy–Riemann–Fueter operators of `f` times the volume form,
and `Dq` is the form integrated over boundaries in the Cauchy–Fueter theorems. Quaternion
coefficients act on these forms on either
side through the module structures of `ℍ` and `ℍᵐᵒᵖ` on the target, so that
`(a • Dq) v = a * Dq v` and `(MulOpposite.op a • Dq) v = Dq v * a`; the order is part of every
statement.

On the coordinate triple obtained by deleting the `i`-th direction, `Dq` takes the value
`(-1) ^ i` times the `i`-th unit `1, i, j, k`. More intrinsically, `Dq` is the quaternionic
interior product of the volume form: for every `w`, the real inner product of `dq w` with
`Dq v` is the determinant of the `4 × 4` matrix with rows `w, v 0, v 1, v 2`. Quaternion
conjugation of the tangent vectors pulls `Dq` back to `-star Dq`.

## Main declarations

* `TauCeti.Quaternion.dqEquiv` and `TauCeti.Quaternion.dq`: the coordinate equivalence
  `(Fin 4 → ℝ) ≃L[ℝ] ℍ` and its underlying `1`-form `dq`.
* `TauCeti.Quaternion.exists_ball_subset_and_le_norm_affine_face`,
  `TauCeti.Quaternion.exists_ball_subset_and_le_norm_box_face`, and
  `TauCeti.Quaternion.closedCube_subset_closedBall`: positive face separation for interior points
  of affine parallelepipeds and coordinate boxes, and inclusion of a centred coordinate cube in a
  closed ball.
* `TauCeti.Quaternion.Dq`: the `3`-form `Dq`, as a continuous alternating map.
* `TauCeti.Quaternion.Dq_apply`: `Dq v` is the sum over the four coordinates `i` of
  `(-1) ^ i` times the `3 × 3` minor of `v` omitting coordinate `i`, times the `i`-th unit.
* `TauCeti.Quaternion.Dq_succAbove`: the value of `Dq` on the coordinate triple omitting the
  `i`-th direction is `(-1) ^ i` times the `i`-th unit.
* `TauCeti.Quaternion.inner_dq_Dq`: `⟪dq w, Dq v⟫_ℝ = det (w, v 0, v 1, v 2)`.
* `TauCeti.Quaternion.Dq_star`: the pullback of `Dq` under quaternion conjugation is `-star Dq`.
* `ContinuousLinearEquiv.Dq_map_succAbove`: the oriented affine face coefficient is the
  corresponding row of the cofactor transform, with the signed determinant.

## References

* A. Sudbery, *Quaternionic analysis*, Math. Proc. Cambridge Philos. Soc. 85 (1979), 199–225,
  for the forms `dq` and `Dq`.
* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, the form `dX` and equation (18) for the
  `3`-form, there called `Dx`.
-/

public section

open scoped Quaternion RealInnerProductSpace

namespace TauCeti.Quaternion

/-! ### The `1`-form `dq` -/

/-- The coordinate continuous linear equivalence `(Fin 4 → ℝ) ≃L[ℝ] ℍ` sending `h` to
`h 0 + i * h 1 + j * h 2 + k * h 3`. Its underlying continuous linear map is `dq`. -/
noncomputable def dqEquiv : (Fin 4 → ℝ) ≃L[ℝ] ℍ :=
  (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm.toContinuousLinearEquiv

/-- The constant quaternion-valued `1`-form `dq = dt + i dx + j dy + k dz` on the coordinate space
`Fin 4 → ℝ`: it sends `h` to `h 0 + i * h 1 + j * h 2 + k * h 3`, the quaternion with coordinates
`h`. -/
noncomputable def dq : (Fin 4 → ℝ) →L[ℝ] ℍ :=
  dqEquiv.toContinuousLinearMap

@[simp]
theorem toContinuousLinearMap_dqEquiv : dqEquiv.toContinuousLinearMap = dq :=
  (rfl)

@[simp]
theorem dqEquiv_apply (h : Fin 4 → ℝ) : dqEquiv h = dq h :=
  (rfl)

@[simp]
theorem dq_dqEquiv_symm (q : ℍ) : dq (dqEquiv.symm q) = q :=
  dqEquiv.apply_symm_apply q

@[simp]
theorem dqEquiv_symm_dq (x : Fin 4 → ℝ) : dqEquiv.symm (dq x) = x :=
  dqEquiv.symm_apply_apply x

theorem dq_injective : Function.Injective dq :=
  dqEquiv.injective

theorem dq_surjective : Function.Surjective dq :=
  dqEquiv.surjective

theorem dq_apply (h : Fin 4 → ℝ) : dq h = ⟨h 0, h 1, h 2, h 3⟩ :=
  (rfl)

@[simp]
theorem re_dq (h : Fin 4 → ℝ) : (dq h).re = h 0 :=
  (rfl)

@[simp]
theorem imI_dq (h : Fin 4 → ℝ) : (dq h).imI = h 1 :=
  (rfl)

@[simp]
theorem imJ_dq (h : Fin 4 → ℝ) : (dq h).imJ = h 2 :=
  (rfl)

@[simp]
theorem imK_dq (h : Fin 4 → ℝ) : (dq h).imK = h 3 :=
  (rfl)

/-- `dq` sends the `i`-th coordinate vector to the `i`-th unit of `1, i, j, k`. -/
@[simp]
theorem dq_single (i : Fin 4) (r : ℝ) :
    dq (Pi.single i r) = r • QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i := by
  rw [QuaternionAlgebra.basisOneIJK, Module.Basis.coe_ofEquivFun, ← map_smul, ← Pi.single_smul',
    smul_eq_mul, mul_one]
  rfl

/-- `dq` is the inverse of the coordinate map `QuaternionAlgebra.linearEquivTuple`. -/
theorem coe_dq : ⇑dq = (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).symm :=
  (rfl)

/-- The Euclidean norm of the quaternion with coordinates `x` is the norm of `x` in
`EuclideanSpace ℝ (Fin 4)`. -/
theorem norm_dq (x : Fin 4 → ℝ) : ‖dq x‖ = ‖WithLp.toLp 2 x‖ := by
  rw [← _root_.Quaternion.norm_toLp_equivTuple]
  congr 2
  simp only [coe_dq, _root_.Quaternion.equivTuple]
  exact (QuaternionAlgebra.linearEquivTuple (-1 : ℝ) 0 (-1)).apply_symm_apply x

/-- Every quaternion is the sum of the units `1, i, j, k` weighted by its real inner products
with them. -/
theorem _root_.Quaternion.sum_inner_dq_single_smul (q : ℍ) :
    ∑ i : Fin 4, ⟪q, dq (Pi.single i 1)⟫ • dq (Pi.single i 1) = q := by
  ext <;> simp [Fin.sum_univ_four, _root_.Quaternion.inner_def, dq_apply, Pi.single_apply]

/-- For an invertible affine map `u ↦ p + L u` on `Fin 4 → ℝ` and an interior point `x₀` whose
preimage `L.symm (x₀ - p)` lies in the open coordinate box `∏ i, Ioo (a i) (b i)`, there is an
open ball around `dq x₀` contained in the open parallelepiped image whose radius bounds the
distance from `dq x₀` to all eight extended face hyperplanes. -/
theorem exists_ball_subset_and_le_norm_affine_face
    {L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)} {p a b x₀ : Fin 4 → ℝ}
    (hx₀ : L.symm (x₀ - p) ∈ Set.pi Set.univ fun i ↦ Set.Ioo (a i) (b i)) :
    ∃ δ > 0,
      Metric.ball (dq x₀) δ ⊆
        dq '' ((fun u ↦ p + L u) '' Set.pi Set.univ fun i ↦ Set.Ioo (a i) (b i)) ∧
      ∀ (j : Fin 4) (c : ℝ), (c = a j ∨ c = b j) → ∀ u : Fin 3 → ℝ,
        δ ≤ ‖dq (p + L (j.insertNth c u)) - dq x₀‖ := by
  let e : (Fin 4 → ℝ) ≃ₜ ℍ :=
    (L.toHomeomorph.trans (Homeomorph.addLeft p)).trans dqEquiv.toHomeomorph
  have he (u : Fin 4 → ℝ) : e u = dq (p + L u) := by
    simp [e]
  let U := Set.pi Set.univ fun i ↦ Set.Ioo (a i) (b i)
  have hU : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo
  have hx₀' : dq x₀ ∈ e '' U := ⟨L.symm (x₀ - p), hx₀, by simp [he]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (e.isOpenMap U hU) (dq x₀) hx₀'
  refine ⟨δ, hδ, ?_, fun j c hc u ↦ ?_⟩
  · intro q hq
    obtain ⟨v, hv, rfl⟩ := hball hq
    exact ⟨p + L v, ⟨v, hv, rfl⟩, (he v).symm⟩
  · by_contra hn
    have hmem : e (j.insertNth c u) ∈ Metric.ball (dq x₀) δ := by
      simpa only [Metric.mem_ball, dist_eq_norm, he] using lt_of_not_ge hn
    obtain ⟨v, hv, hvq⟩ := hball hmem
    have hj := Set.mem_pi.mp hv j (Set.mem_univ j)
    rw [e.injective hvq, Fin.insertNth_apply_same] at hj
    rcases hc with rfl | rfl
    · exact lt_irrefl _ hj.1
    · exact lt_irrefl _ hj.2

/-- Positive separation of the eight extended face hyperplanes of a coordinate box from an interior
point `x₀`, together with an open ball around `dq x₀` inside the open box image. -/
theorem exists_ball_subset_and_le_norm_box_face {a b x₀ : Fin 4 → ℝ}
    (ha : ∀ i, a i < x₀ i) (hb : ∀ i, x₀ i < b i) :
    ∃ δ > 0, Metric.ball (dq x₀) δ ⊆ dq '' Set.pi Set.univ (fun i ↦ Set.Ioo (a i) (b i)) ∧
      ∀ (i : Fin 4) (c : ℝ), (c = a i ∨ c = b i) → ∀ u : Fin 3 → ℝ,
        δ ≤ ‖dq (i.insertNth c u) - dq x₀‖ := by
  simpa using exists_ball_subset_and_le_norm_affine_face
    (L := ContinuousLinearEquiv.refl ℝ (Fin 4 → ℝ)) (p := 0) (a := a) (b := b) (x₀ := x₀)
    (Set.mem_pi.mpr fun i _ ↦ by simpa using ⟨ha i, hb i⟩)

/-- The closed coordinate cube of side `R` centred at `x₀` has Euclidean half-diagonal
`√(4 (R / 2)²) = R`, hence maps under `dq` into `Metric.closedBall (dq x₀) R`. -/
theorem closedCube_subset_closedBall (x₀ : Fin 4 → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    dq '' Set.Icc (fun i ↦ x₀ i - R / 2) (fun i ↦ x₀ i + R / 2) ⊆
      Metric.closedBall (dq x₀) R := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, ← map_sub]
  have hcoord (i : Fin 4) : (x - x₀) i * (x - x₀) i ≤ (R / 2) * (R / 2) := by
    have hx1 : x₀ i - R / 2 ≤ x i := hx.1 i
    have hx2 : x i ≤ x₀ i + R / 2 := hx.2 i
    have hi : |(x - x₀) i| ≤ R / 2 := by
      rw [Pi.sub_apply, abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    simpa [abs_mul_abs_self] using mul_self_le_mul_self (abs_nonneg _) hi
  have hnsq := _root_.Quaternion.normSq_eq_norm_mul_self (dq (x - x₀))
  simp only [_root_.Quaternion.normSq_def', re_dq, imI_dq, imJ_dq, imK_dq] at hnsq
  nlinarith [hcoord 0, hcoord 1, hcoord 2, hcoord 3, norm_nonneg (dq (x - x₀)), hR]

/-! ### The `3`-form `Dq` -/

/-- The real `3`-form on `Fin 4 → ℝ` omitting the coordinate `i`: the determinant of the
`3 × 3` matrix of the remaining coordinates of three vectors. These are `dx∧dy∧dz`,
`dt∧dy∧dz`, `dt∧dx∧dz` and `dt∧dx∧dy`. -/
noncomputable def minorForm (i : Fin 4) : (Fin 4 → ℝ) [⋀^Fin 3]→L[ℝ] ℝ :=
  AlternatingMap.toContinuousAlternatingMap
    (Matrix.detRowAlternating.compLinearMap (LinearMap.funLeft ℝ ℝ i.succAbove))

theorem minorForm_apply (i : Fin 4) (v : Fin 3 → Fin 4 → ℝ) :
    minorForm i v = (Matrix.of fun r c ↦ v r (i.succAbove c)).det := by
  rw [minorForm, AlternatingMap.coe_toContinuousAlternatingMap,
    AlternatingMap.compLinearMap_apply]
  -- `Matrix.det` is `Matrix.detRowAlternating` evaluated on the rows of the matrix.
  rfl

/-- The constant quaternion-valued `3`-form
`Dq = dx∧dy∧dz − i dt∧dy∧dz − j dt∧dz∧dx − k dt∧dx∧dy` on the coordinate space `Fin 4 → ℝ`.
Its `i`-th coefficient is `(-1) ^ i` times the `i`-th unit `1, i, j, k`, against the real
`3`-form omitting the coordinate `i`. -/
noncomputable def Dq : (Fin 4 → ℝ) [⋀^Fin 3]→L[ℝ] ℍ :=
  ∑ i : Fin 4,
    (minorForm i).smulRight ((-1 : ℝ) ^ (i : ℕ) • QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i)


/-- `Dq v` is the sum over the coordinates `i` of `(-1) ^ i` times the minor of `v` omitting
coordinate `i`, times the `i`-th unit of `1, i, j, k`. -/
theorem Dq_apply (v : Fin 3 → Fin 4 → ℝ) :
    Dq v = ∑ i : Fin 4,
      ((-1 : ℝ) ^ (i : ℕ) * minorForm i v) • QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i := by
  simp only [Dq, ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smulRight_apply,
    mul_comm _ (minorForm _ v), mul_smul]

/-- The real part of `Dq` is `dx∧dy∧dz`. -/
@[simp]
theorem re_Dq (v : Fin 3 → Fin 4 → ℝ) : (Dq v).re = minorForm 0 v := by
  norm_num [Dq_apply, Fin.sum_univ_four, ← dq_single, Pi.single_apply]

/-- The `i`-component of `Dq` is `-dt∧dy∧dz`. -/
@[simp]
theorem imI_Dq (v : Fin 3 → Fin 4 → ℝ) : (Dq v).imI = -minorForm 1 v := by
  norm_num [Dq_apply, Fin.sum_univ_four, ← dq_single, Pi.single_apply]

/-- The `j`-component of `Dq` is `-dt∧dz∧dx = dt∧dx∧dz`. -/
@[simp]
theorem imJ_Dq (v : Fin 3 → Fin 4 → ℝ) : (Dq v).imJ = minorForm 2 v := by
  norm_num [Dq_apply, Fin.sum_univ_four, ← dq_single, Pi.single_apply]

/-- The `k`-component of `Dq` is `-dt∧dx∧dy`. -/
@[simp]
theorem imK_Dq (v : Fin 3 → Fin 4 → ℝ) : (Dq v).imK = -minorForm 3 v := by
  norm_num [Dq_apply, Fin.sum_univ_four, ← dq_single, Pi.single_apply]

/-- On the coordinate triple obtained by deleting the `i`-th direction, `Dq` takes the value
`(-1) ^ i` times the `i`-th unit of `1, i, j, k`: so `Dq (e_x, e_y, e_z) = 1`,
`Dq (e_t, e_y, e_z) = -i`, `Dq (e_t, e_x, e_z) = j` and `Dq (e_t, e_x, e_y) = -k`. -/
@[simp]
theorem Dq_succAbove (i : Fin 4) :
    Dq (fun r ↦ Pi.single (i.succAbove r) 1) =
      (-1 : ℝ) ^ (i : ℕ) • QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) i := by
  rw [← dq_single]
  fin_cases i <;> ext <;>
    norm_num [minorForm_apply, Matrix.det_fin_three, Pi.single_apply, Fin.succAbove, -dq_single]

/-- `Dq` is the quaternionic interior product of the volume form: the real inner product of
`dq w` with `Dq v` is the determinant of the matrix with rows `w, v 0, v 1, v 2`. -/
theorem inner_dq_Dq (w : Fin 4 → ℝ) (v : Fin 3 → Fin 4 → ℝ) :
    ⟪dq w, Dq v⟫ = (Matrix.of (Fin.cons w v : Fin 4 → Fin 4 → ℝ)).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four, Quaternion.inner_def]
  simp [minorForm_apply, Matrix.submatrix, Fin.succAbove]
  ring

/-- Conjugating the tangent vectors pulls `Dq` back to `-star Dq`: if `dq (w r)` is the conjugate of
`dq (v r)` for each `r`, then `Dq w = -star (Dq v)`. -/
theorem Dq_star {v w : Fin 3 → Fin 4 → ℝ} (h : ∀ r, dq (w r) = star (dq (v r))) :
    Dq w = -star (Dq v) := by
  have h0 r : w r 0 = v r 0 := by simpa using congrArg QuaternionAlgebra.re (h r)
  have h1 r : w r 1 = -v r 1 := by simpa using congrArg QuaternionAlgebra.imI (h r)
  have h2 r : w r 2 = -v r 2 := by simpa using congrArg QuaternionAlgebra.imJ (h r)
  have h3 r : w r 3 = -v r 3 := by simpa using congrArg QuaternionAlgebra.imK (h r)
  ext <;> simp [minorForm_apply, Matrix.det_fin_three, Fin.succAbove, h0, h1, h2, h3]
  ring

end TauCeti.Quaternion

open TauCeti.Quaternion

namespace ContinuousLinearEquiv

/-- Under an invertible real linear change of tangent coordinates, the interior-product
identity for `Dq` transforms by the signed determinant and the inverse change on the test vector. -/
theorem inner_dq_Dq_map (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ))
    (w : Fin 4 → ℝ) (v : Fin 3 → Fin 4 → ℝ) :
    ⟪dq w, Dq (fun r ↦ L (v r))⟫ =
      LinearMap.det L.toLinearMap * ⟪dq (L.symm w), Dq v⟫ := by
  rw [inner_dq_Dq, inner_dq_Dq]
  have h := (Pi.basisFun ℝ (Fin 4)).det_comp L.toLinearMap (Fin.cons (L.symm w) v)
  simp only [Pi.basisFun_det_apply] at h
  convert h using 1
  congr 1
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- The oriented tangent coefficient of an affine front face is the corresponding row
of the cofactor transform. The inverse is not transposed: its entry here is `(j,i)`. -/
theorem Dq_map_succAbove (L : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ)) (j : Fin 4) :
    (-1 : ℝ) ^ (j : ℕ) • Dq (fun r ↦ L (Pi.single (j.succAbove r) 1)) =
      LinearMap.det L.toLinearMap • dq (fun i ↦ L.symm (Pi.single i 1) j) := by
  have h (i : Fin 4) := inner_dq_Dq_map L (Pi.single i 1)
    (fun r ↦ Pi.single (j.succAbove r) 1)
  simp only [Dq_succAbove, inner_smul_right] at h
  have hs : (-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have h' (i : Fin 4) :
      ⟪dq (Pi.single i 1),
        (-1 : ℝ) ^ (j : ℕ) • Dq (fun r ↦ L (Pi.single (j.succAbove r) 1))⟫ =
      LinearMap.det L.toLinearMap * L.symm (Pi.single i 1) j := by
    rw [inner_smul_right, h]
    have hb (x : Fin 4 → ℝ) :
        ⟪dq x, QuaternionAlgebra.basisOneIJK (-1 : ℝ) 0 (-1) j⟫ = x j := by
      have he := dq_single j 1
      simp only [one_smul] at he
      rw [← he]
      fin_cases j <;> simp [Quaternion.inner_def, dq_apply]
    rw [hb]
    calc
      _ = ((-1 : ℝ) ^ (j : ℕ) * (-1 : ℝ) ^ (j : ℕ)) *
          (LinearMap.det L.toLinearMap * L.symm (Pi.single i 1) j) := by ring
      _ = _ := by rw [hs, one_mul]
  ext
  · simpa [Quaternion.inner_def, dq_apply] using h' 0
  · simpa [Quaternion.inner_def, dq_apply] using h' 1
  · simpa [Quaternion.inner_def, dq_apply] using h' 2
  · simpa [Quaternion.inner_def, dq_apply] using h' 3

end ContinuousLinearEquiv
