/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Central unipotents along an isotropic frame

For a hermitian Gram matrix `J` and a matrix `k` of isotropic columns, the matrices
`z(M) = 1 + k (M - Mᴴ) kᴴ J` preserve `J`, have determinant one, and fix `k` and its orthogonal
pointwise. The parameter is additive: `z(M + N) = z(M) z(N)`. Every isometry fixing `k`
pointwise commutes with them. Thus these are central translations in the unipotent radical
attached to the frame, used to take Fourier coefficients along that centre.

The matrix identities work over any star ring, without nondegeneracy or division by `2`;
the determinant and special-isometry statements use commutative coefficients. The construction
parametrizes skew parts `M - Mᴴ`; it does not assert that every skew-hermitian matrix
is such a part. With a dual frame, equality of the transformations is exactly equality of
the skew parts. In the standard hyperbolic space the formula is the upper block unipotent
matrix with upper right block `M - Mᴴ`. Scalar extension and continuity of the parameter
allow the same formulas to be used over local and adelic topological rings.

## References

* E. Freitag, *Singular Modular Forms and Theta Relations*, LNM 1487 (1991), for Fourier
  coefficients along unipotent centres and their role in singular forms.
-/

public section

namespace Matrix

variable {R n p q : Type*} [Fintype n] [DecidableEq n] [Fintype p]

section Ring

variable [Ring R] [StarRing R]

/-- The central translation `1 + k (M - Mᴴ) kᴴ J` along a frame `k`. It is a unipotent isometry
when `J` is hermitian and `kᴴ J k = 0`. -/
def frameUnipotent (J : Matrix n n R) (k : Matrix n p R) (M : Matrix p p R) : Matrix n n R :=
  1 + k * (M - Mᴴ) * kᴴ * J

/-- The defining matrix formula for a central translation. -/
theorem frameUnipotent_def (J : Matrix n n R) (k : Matrix n p R) (M : Matrix p p R) :
    J.frameUnipotent k M = 1 + k * (M - Mᴴ) * kᴴ * J := (rfl)

variable {J : Matrix n n R} {k : Matrix n p R}

@[simp]
theorem frameUnipotent_zero_frame (J : Matrix n n R) (M : Matrix p p R) :
    J.frameUnipotent 0 M = 1 := by simp [frameUnipotent_def]

/-- Only the skew part of the parameter matters. -/
theorem frameUnipotent_eq_of_sub_conjTranspose_eq {M N : Matrix p p R}
    (h : M - Mᴴ = N - Nᴴ) : J.frameUnipotent k M = J.frameUnipotent k N := by
  simp only [frameUnipotent_def, h]

/-- A hermitian parameter gives the identity transformation. -/
@[simp]
theorem frameUnipotent_eq_one_of_isHermitian {M : Matrix p p R} (hM : M.IsHermitian) :
    J.frameUnipotent k M = 1 := by simp [frameUnipotent_def, hM.eq]

/-- Action on column vectors. -/
theorem frameUnipotent_mulVec (M : Matrix p p R) (x : n → R) :
    J.frameUnipotent k M *ᵥ x = x + k *ᵥ ((M - Mᴴ) *ᵥ (kᴴ *ᵥ (J *ᵥ x))) := by
  simp [frameUnipotent_def, add_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- Central translations fix every vector orthogonal to the frame. -/
theorem frameUnipotent_mulVec_of_orthogonal (M : Matrix p p R) {x : n → R}
    (hx : kᴴ *ᵥ (J *ᵥ x) = 0) : J.frameUnipotent k M *ᵥ x = x := by
  simp [frameUnipotent_mulVec, hx]

/-- An isotropic frame is fixed pointwise. -/
@[simp]
theorem frameUnipotent_mul_frame (hk : kᴴ * J * k = 0) (M : Matrix p p R) :
    J.frameUnipotent k M * k = k := by
  simp [frameUnipotent_def, Matrix.add_mul, Matrix.mul_assoc, hk]

/-- The perturbations of the identity have pairwise zero products. -/
theorem frameUnipotent_sub_one_mul_sub_one (hk : kᴴ * J * k = 0) (M N : Matrix p p R) :
    (J.frameUnipotent k M - 1) * (J.frameUnipotent k N - 1) = 0 := by
  simp only [frameUnipotent_def, add_sub_cancel_left]
  calc
    _ = k * (M - Mᴴ) * (kᴴ * J * k) * (N - Nᴴ) * kᴴ * J := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by simp [hk]

/-- Addition of parameters is multiplication of central translations. -/
theorem frameUnipotent_add (hk : kᴴ * J * k = 0) (M N : Matrix p p R) :
    J.frameUnipotent k (M + N) = J.frameUnipotent k M * J.frameUnipotent k N := by
  have hzero := frameUnipotent_sub_one_mul_sub_one hk M N
  simp only [frameUnipotent_def, add_sub_cancel_left] at hzero
  simp only [frameUnipotent_def, conjTranspose_add, add_sub_add_comm,
    Matrix.mul_add, Matrix.add_mul, one_mul, mul_one]
  rw [hzero]
  abel

/-- The central translations commute with each other. -/
theorem frameUnipotent_commute (hk : kᴴ * J * k = 0) (M N : Matrix p p R) :
    Commute (J.frameUnipotent k M) (J.frameUnipotent k N) := by
  exact (frameUnipotent_add hk M N).symm.trans (by rw [add_comm, frameUnipotent_add hk])

/-- Negating the parameter gives a right inverse. -/
@[simp]
theorem frameUnipotent_mul_neg (hk : kᴴ * J * k = 0) (M : Matrix p p R) :
    J.frameUnipotent k M * J.frameUnipotent k (-M) = 1 := by
  rw [← frameUnipotent_add hk, add_neg_cancel]
  simp

/-- Negating the parameter gives a left inverse. -/
@[simp]
theorem frameUnipotent_neg_mul (hk : kᴴ * J * k = 0) (M : Matrix p p R) :
    J.frameUnipotent k (-M) * J.frameUnipotent k M = 1 := by
  rw [← frameUnipotent_add hk, neg_add_cancel]
  simp

/-- Transposed conjugation of the translation against its hermitian Gram matrix. -/
theorem conjTranspose_frameUnipotent_mul (hJ : J.IsHermitian) (M : Matrix p p R) :
    (J.frameUnipotent k M)ᴴ * J = J - J * k * (M - Mᴴ) * kᴴ * J := by
  simp only [frameUnipotent_def, conjTranspose_add, conjTranspose_one, conjTranspose_mul,
    conjTranspose_sub, conjTranspose_conjTranspose, hJ.eq, Matrix.add_mul, one_mul]
  simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- The central translations preserve a hermitian form. -/
theorem conjTranspose_frameUnipotent_mul_self (hJ : J.IsHermitian)
    (hk : kᴴ * J * k = 0) (M : Matrix p p R) :
    (J.frameUnipotent k M)ᴴ * J * J.frameUnipotent k M = J := by
  have hzero := frameUnipotent_sub_one_mul_sub_one hk M M
  simp only [frameUnipotent_def, add_sub_cancel_left] at hzero
  have hzero' :
      J * k * (M - Mᴴ) * kᴴ * J * (k * (M - Mᴴ) * kᴴ * J) = 0 := by
    simpa only [Matrix.mul_assoc, mul_zero] using congrArg (J * ·) hzero
  rw [conjTranspose_frameUnipotent_mul hJ, frameUnipotent_def]
  simp only [Matrix.sub_mul, Matrix.mul_add, mul_one]
  rw [hzero']
  simp only [Matrix.mul_assoc]
  abel

/-- Changing the coordinates of the isotropic frame acts on parameters by congruence. -/
theorem frameUnipotent_mul_right [Fintype q] (a : Matrix p q R) (M : Matrix q q R) :
    J.frameUnipotent (k * a) M = J.frameUnipotent k (a * M * aᴴ) := by
  simp [frameUnipotent_def, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- An isometry transports central translations along its image of the frame. No inverse or
nondegeneracy assumption is needed for this intertwining identity. -/
theorem mul_frameUnipotent {g : Matrix n n R} (hg : gᴴ * J * g = J) (M : Matrix p p R) :
    g * J.frameUnipotent k M = J.frameUnipotent (g * k) M * g := by
  simp only [frameUnipotent_def, Matrix.mul_add, Matrix.add_mul, mul_one, one_mul,
    conjTranspose_mul]
  simp only [Matrix.mul_assoc, hg]

/-- Every isometry fixing the frame pointwise centralizes the translations. -/
theorem commute_frameUnipotent {g : Matrix n n R} (hg : gᴴ * J * g = J)
    (hgk : g * k = k) (M : Matrix p p R) : Commute g (J.frameUnipotent k M) := by
  exact (mul_frameUnipotent (k := k) hg M).trans (by rw [hgk])

/-- Central translations commute with extension of scalars by a star ring homomorphism. -/
@[simp]
theorem map_frameUnipotent {S : Type*} [Ring S] [StarRing S]
    (J : Matrix n n R) (k : Matrix n p R) (M : Matrix p p R) (f : R →+* S)
    (hf : Function.Semiconj f star star) :
    (J.frameUnipotent k M).map f =
      (J.map f).frameUnipotent (k.map f) (M.map f) := by
  ext i j
  simp [frameUnipotent_def, Matrix.mul_apply, map_sum, conjTranspose_apply, hf.eq,
    Matrix.one_apply, apply_ite]

/-- The additive parameter of the central translations varies continuously. -/
theorem continuous_frameUnipotent [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R]
    (J : Matrix n n R) (k : Matrix n p R) : Continuous (J.frameUnipotent k) := by
  unfold frameUnipotent
  fun_prop

variable [DecidableEq p]

/-- A dual frame reads off the skew part from the displacement. -/
theorem conjTranspose_mul_frameUnipotent_sub_one_mul (hJ : J.IsHermitian)
    {l : Matrix n p R} (hl : kᴴ * J * l = 1) (M : Matrix p p R) :
    lᴴ * J * (J.frameUnipotent k M - 1) * l = M - Mᴴ := by
  have hl' : lᴴ * J * k = 1 := by
    simpa [conjTranspose_mul, hJ.eq, Matrix.mul_assoc] using congrArg conjTranspose hl
  calc
    _ = (lᴴ * J * k) * (M - Mᴴ) * (kᴴ * J * l) := by
      simp [frameUnipotent_def, Matrix.mul_assoc]
    _ = M - Mᴴ := by rw [hl', hl, one_mul, mul_one]

/-- With a dual frame, two translations agree exactly when their skew parameters agree. -/
theorem frameUnipotent_eq_iff (hJ : J.IsHermitian) {l : Matrix n p R}
    (hl : kᴴ * J * l = 1) (M N : Matrix p p R) :
    J.frameUnipotent k M = J.frameUnipotent k N ↔ M - Mᴴ = N - Nᴴ := by
  refine ⟨fun h ↦ ?_, frameUnipotent_eq_of_sub_conjTranspose_eq⟩
  calc
    M - Mᴴ = lᴴ * J * (J.frameUnipotent k M - 1) * l :=
      (conjTranspose_mul_frameUnipotent_sub_one_mul hJ hl M).symm
    _ = lᴴ * J * (J.frameUnipotent k N - 1) * l :=
      congrArg (fun z ↦ lᴴ * J * (z - 1) * l) h
    _ = N - Nᴴ := conjTranspose_mul_frameUnipotent_sub_one_mul hJ hl N

/-- With a dual frame, precisely the hermitian parameters give the identity. -/
theorem frameUnipotent_eq_one_iff (hJ : J.IsHermitian) {l : Matrix n p R}
    (hl : kᴴ * J * l = 1) (M : Matrix p p R) :
    J.frameUnipotent k M = 1 ↔ M.IsHermitian := by
  have hzero : J.frameUnipotent k (0 : Matrix p p R) = 1 :=
    frameUnipotent_eq_one_of_isHermitian isHermitian_zero
  rw [← hzero, frameUnipotent_eq_iff hJ hl, conjTranspose_zero, sub_zero, sub_eq_zero,
    IsHermitian, eq_comm]

/-- On the standard hyperbolic space, these are precisely the upper block translations with
skew block `M - Mᴴ`. In particular the construction need not be the identity. -/
theorem frameUnipotent_hyperbolic (M : Matrix p p R) :
    (fromBlocks (0 : Matrix p p R) 1 1 0).frameUnipotent
      (fromRows (1 : Matrix p p R) 0) M = fromBlocks 1 (M - Mᴴ) 0 1 := by
  simp only [frameUnipotent_def, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_one, conjTranspose_zero, fromRows_mul, one_mul, zero_mul]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply, fromCols_mul_fromBlocks]

end Ring

section CommRing

variable [CommRing R] [StarRing R] {J : Matrix n n R} {k : Matrix n p R}

/-- Central translations have determinant one. -/
@[simp]
theorem det_frameUnipotent (hk : kᴴ * J * k = 0) (M : Matrix p p R) :
    (J.frameUnipotent k M).det = 1 := by
  classical
  rw [frameUnipotent_def, Matrix.mul_assoc, Matrix.mul_assoc, det_one_add_mul_comm]
  simp [Matrix.mul_assoc, hk]

/-- The additive parameter group acts by special isometries. This uses the existing special
isometry group, with its entrywise involution `starRingEnd R`. -/
def frameUnipotentHom (hJ : J.IsHermitian) (hk : kᴴ * J * k = 0) :
    Multiplicative (Matrix p p R) →* J.specialIsometryGroup (starRingEnd R) where
  toFun M := ⟨⟨J.frameUnipotent k M.toAdd, det_frameUnipotent hk M.toAdd⟩,
    mem_specialIsometryGroup_iff.mpr
      (conjTranspose_frameUnipotent_mul_self hJ hk M.toAdd)⟩
  map_one' := by apply specialIsometryGroup_ext; simp
  map_mul' M N := by
    apply specialIsometryGroup_ext
    exact frameUnipotent_add hk M.toAdd N.toAdd

/-- The matrix underlying the bundled special isometry. -/
@[simp]
theorem coe_frameUnipotentHom (hJ : J.IsHermitian) (hk : kᴴ * J * k = 0)
    (M : Multiplicative (Matrix p p R)) :
    (((frameUnipotentHom hJ hk M : J.specialIsometryGroup (starRingEnd R)) :
      SpecialLinearGroup n R) : Matrix n n R) = J.frameUnipotent k M.toAdd := (rfl)

/-- The inverse of the bundled central translation has the negative parameter. -/
theorem coe_inv_frameUnipotentHom (hJ : J.IsHermitian) (hk : kᴴ * J * k = 0)
    (M : Multiplicative (Matrix p p R)) :
    ((((frameUnipotentHom hJ hk M)⁻¹ : J.specialIsometryGroup (starRingEnd R)) :
      SpecialLinearGroup n R) : Matrix n n R) = J.frameUnipotent k (-M.toAdd) := by
  rw [← map_inv, coe_frameUnipotentHom, toAdd_inv]

end CommRing

end Matrix
