/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.SymbolAlgebra.MatrixCorner
public import TauCeti.RingTheory.Idempotents.Matrix
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# The selected corner of a symbol algebra

The inverse images of matrix units under `algEquivMatrixOfPow` give the complete orthogonal
idempotents and the matrix units associated to the factor `X ^ d - c`. The selected corner has
its own unit, the selected idempotent, and is an algebra isomorphic to the smaller symbol algebra.
-/

public section

namespace TauCeti.SymbolAlgebra

variable {F : Type*} [Field F] (d s : ℕ) [NeZero d] [NeZero s] {ζ c b : F}
    (hζ : IsPrimitiveRoot ζ (d * s)) (hc : c ≠ 0) (hb : b ≠ 0)

/-- The matrix unit associated to the power presentation of a symbol algebra. -/
noncomputable def matrixUnitOfPow (i j : Fin s) : SymbolAlgebra (d * s) ζ (c ^ s) b :=
  (algEquivMatrixOfPow d s hζ hc hb).symm (Matrix.single i j 1)

/-- The matrix equivalence sends the chosen matrix units to the usual matrix units. -/
@[simp↓]
theorem matrixUnitOfPow_image (i j : Fin s) :
    algEquivMatrixOfPow d s hζ hc hb (matrixUnitOfPow d s hζ hc hb i j) =
      Matrix.single i j 1 :=
  (algEquivMatrixOfPow d s hζ hc hb).apply_symm_apply _

/-- The matrix units obey the usual multiplication law. -/
theorem matrixUnitOfPow_mul (i j k l : Fin s) :
    matrixUnitOfPow d s hζ hc hb i j * matrixUnitOfPow d s hζ hc hb k l =
      if j = k then matrixUnitOfPow d s hζ hc hb i l else 0 := by
  apply (algEquivMatrixOfPow d s hζ hc hb).injective
  by_cases h : j = k <;> simp [h, Matrix.single_mul_single_of_ne]

/-- The inverse images of the diagonal matrix units form a complete orthogonal family of
idempotents. -/
theorem matrixUnitOfPow_completeOrthogonalIdempotents :
    CompleteOrthogonalIdempotents fun i : Fin s => matrixUnitOfPow d s hζ hc hb i i :=
  CompleteOrthogonalIdempotents.map
    (algEquivMatrixOfPow d s hζ hc hb).symm.toRingHom
    Matrix.completeOrthogonalIdempotents_single_one

/-- The selected idempotent, corresponding to the factor `X ^ d - c`. -/
noncomputable def cornerIdempotentOfPow : SymbolAlgebra (d * s) ζ (c ^ s) b :=
  matrixUnitOfPow d s hζ hc hb 0 0

/-- The selected corner unit maps to the zeroth diagonal matrix unit. -/
@[simp]
theorem cornerIdempotentOfPow_image :
    algEquivMatrixOfPow d s hζ hc hb (cornerIdempotentOfPow d s hζ hc hb) =
      Matrix.single 0 0 1 :=
  matrixUnitOfPow_image d s hζ hc hb 0 0

/-- The selected matrix unit is idempotent. -/
theorem isIdempotentElem_cornerIdempotentOfPow :
    IsIdempotentElem (cornerIdempotentOfPow d s hζ hc hb) :=
  (Matrix.isIdempotentElem_single_one (α := SymbolAlgebra d (ζ ^ s) c b) (0 : Fin s)).map
    (algEquivMatrixOfPow d s hζ hc hb).symm.toRingEquiv

/-- Powers of the unit `y` recover the specified matrix units from the selected idempotent.
The statement accepts the caller's chosen unit representing `y`. -/
theorem matrixUnitOfPow_eq_y_pow_mul_cornerIdempotentOfPow
    (u : (SymbolAlgebra (d * s) ζ (c ^ s) b)ˣ) (hu : (u : SymbolAlgebra (d * s) ζ (c ^ s) b) = y)
    (i j : Fin s) :
    matrixUnitOfPow d s hζ hc hb i j =
      y ^ (i : ℕ) * cornerIdempotentOfPow d s hζ hc hb *
        (↑(u⁻¹ ^ (j : ℕ)) : SymbolAlgebra (d * s) ζ (c ^ s) b) := by
  let f := algEquivMatrixOfPow d s hζ hc hb
  apply f.injective
  rw [matrixUnitOfPow_image, map_mul, map_mul, map_pow,
    algEquivMatrixOfPow_y, cornerIdempotentOfPow_image]
  have hu' : (Units.map f.toMonoidHom u : Matrix (Fin s) (Fin s)
      (SymbolAlgebra d (ζ ^ s) c b)) = Matrix.weightedShift s y := by
    -- The value of the mapped unit is the image of its value.
    change f (u : SymbolAlgebra (d * s) ζ (c ^ s) b) = _
    rw [hu, algEquivMatrixOfPow_y]
  symm
  convert Matrix.weightedShift_pow_single_zero_mul_inv_pow s
    (y : SymbolAlgebra d (ζ ^ s) c b) (Units.map f.toMonoidHom u) hu' i j using 1; simp

/-- On the selected idempotent, `x ^ d` has the eigenvalue `c`. -/
theorem x_pow_mul_cornerIdempotentOfPow :
    (x : SymbolAlgebra (d * s) ζ (c ^ s) b) ^ d * cornerIdempotentOfPow d s hζ hc hb =
      c • cornerIdempotentOfPow d s hζ hc hb := by
  apply (algEquivMatrixOfPow d s hζ hc hb).injective
  simp only [map_mul, map_pow, algEquivMatrixOfPow_x, cornerIdempotentOfPow_image,
    map_smul, matrixCornerX_eq_diagonal, Matrix.diagonal_pow]
  rw [diagonal_mul_single]
  simp [x_pow, Matrix.smul_single, Algebra.algebraMap_eq_smul_one]

/-- The selected corner is the smaller symbol algebra, as a unital algebra with its own unit. -/
noncomputable def cornerAlgEquivOfPow :
    (isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).Corner ≃ₐ[F]
      SymbolAlgebra d (ζ ^ s) c b := by
  -- Express the carrier using the mapped matrix idempotent before constructing its algebra map.
  change ((Matrix.isIdempotentElem_single_one
    (α := SymbolAlgebra d (ζ ^ s) c b) (0 : Fin s)).map
      (algEquivMatrixOfPow d s hζ hc hb).symm.toRingEquiv).Corner ≃ₐ[F] _
  exact AlgEquiv.ofRingEquiv
    (f := ((Matrix.isIdempotentElem_single_one
      (α := SymbolAlgebra d (ζ ^ s) c b) (0 : Fin s)).cornerEquiv
        (algEquivMatrixOfPow d s hζ hc hb).symm.toRingEquiv).symm.trans
          (Matrix.cornerSingleOneEquiv 0)) fun r => by
    rw [RingEquiv.trans_apply, Matrix.cornerSingleOneEquiv_apply,
      IsIdempotentElem.val_cornerEquiv_symm_apply,
      IsIdempotentElem.Corner.val_algebraMap]
    -- A corner scalar is the ambient scalar multiple of the corner unit.
    change (algEquivMatrixOfPow d s hζ hc hb
      (r • (algEquivMatrixOfPow d s hζ hc hb).symm (Matrix.single 0 0 1))) 0 0 = _
    simp [Algebra.algebraMap_eq_smul_one]

/-- The corner equivalence reads the zeroth diagonal entry of the matrix image. -/
theorem cornerAlgEquivOfPow_apply
    (z : (isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).Corner) :
    cornerAlgEquivOfPow d s hζ hc hb z = algEquivMatrixOfPow d s hζ hc hb z.val 0 0 := by
  -- Use the mapped idempotent's carrier explicitly at this coercion boundary.
  change ((Matrix.isIdempotentElem_single_one
    (α := SymbolAlgebra d (ζ ^ s) c b) (0 : Fin s)).map
      (algEquivMatrixOfPow d s hζ hc hb).symm.toRingEquiv).Corner at z
  change (Matrix.cornerSingleOneEquiv (0 : Fin s))
    (((Matrix.isIdempotentElem_single_one
      (α := SymbolAlgebra d (ζ ^ s) c b) (0 : Fin s)).cornerEquiv
        (algEquivMatrixOfPow d s hζ hc hb).symm.toRingEquiv).symm z) = _
  rw [Matrix.cornerSingleOneEquiv_apply, IsIdempotentElem.val_cornerEquiv_symm_apply]
  rfl

/-- The inverse corner map includes a coefficient as the inverse image of a supported matrix. -/
@[simp]
theorem cornerAlgEquivOfPow_symm_apply_val (z : SymbolAlgebra d (ζ ^ s) c b) :
    ((cornerAlgEquivOfPow d s hζ hc hb).symm z).val =
      (algEquivMatrixOfPow d s hζ hc hb).symm (Matrix.single 0 0 z) := by
  -- Use the underlying corner equivalence before applying the ambient inclusion.
  change ((Matrix.isIdempotentElem_single_one
    (α := SymbolAlgebra d (ζ ^ s) c b) (0 : Fin s)).cornerEquiv
      (algEquivMatrixOfPow d s hζ hc hb).symm.toRingEquiv
        ((Matrix.cornerSingleOneEquiv 0).symm z)).val = _
  rw [IsIdempotentElem.val_cornerEquiv_apply, Matrix.val_cornerSingleOneEquiv_symm_apply]
  rfl

/-- Compression to the selected corner reads the zeroth diagonal entry. -/
theorem cornerAlgEquivOfPow_compress (z : SymbolAlgebra (d * s) ζ (c ^ s) b) :
    cornerAlgEquivOfPow d s hζ hc hb
      ((isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress z) =
        algEquivMatrixOfPow d s hζ hc hb z 0 0 := by
  rw [cornerAlgEquivOfPow_apply, IsIdempotentElem.val_compress, map_mul, map_mul,
    cornerIdempotentOfPow_image, Matrix.single_mul_mul_single]
  simp

/-- The compressed first generator is the smaller symbol algebra's first generator. -/
@[simp]
theorem cornerAlgEquivOfPow_compress_x :
    cornerAlgEquivOfPow d s hζ hc hb
      ((isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress x) = x := by
  rw [cornerAlgEquivOfPow_compress]
  simp

/-- The compressed `s`-th power of the second generator is the smaller second generator. -/
@[simp]
theorem cornerAlgEquivOfPow_compress_y_pow :
    cornerAlgEquivOfPow d s hζ hc hb
      ((isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress (y ^ s)) = y := by
  rw [cornerAlgEquivOfPow_compress]
  simp [Matrix.weightedShift_pow_card]

/-- The selected idempotent commutes with the first generator. -/
theorem cornerIdempotentOfPow_commute_x :
    Commute (cornerIdempotentOfPow d s hζ hc hb) x := by
  apply (algEquivMatrixOfPow d s hζ hc hb).injective
  simp only [map_mul, cornerIdempotentOfPow_image, algEquivMatrixOfPow_x,
    matrixCornerX_eq_diagonal]
  rw [single_mul_diagonal, diagonal_mul_single]
  simp

/-- The selected idempotent commutes with the `s`-th power of the second generator. -/
theorem cornerIdempotentOfPow_commute_y_pow :
    Commute (cornerIdempotentOfPow d s hζ hc hb) (y ^ s) := by
  apply (algEquivMatrixOfPow d s hζ hc hb).injective
  simp only [map_mul, map_pow, cornerIdempotentOfPow_image, algEquivMatrixOfPow_y,
    Matrix.weightedShift_pow_card, Matrix.scalar_apply]
  rw [single_mul_diagonal, diagonal_mul_single]
  simp

/-- The ambient image of the first corner generator is `e * x`. -/
theorem val_compress_x :
    ((isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress x).val =
      cornerIdempotentOfPow d s hζ hc hb * x :=
  IsIdempotentElem.val_compress_of_commute _ (cornerIdempotentOfPow_commute_x d s hζ hc hb)

/-- The ambient image of the second corner generator is `e * y ^ s`. -/
theorem val_compress_y_pow :
    ((isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress (y ^ s)).val =
      cornerIdempotentOfPow d s hζ hc hb * y ^ s :=
  IsIdempotentElem.val_compress_of_commute _ (cornerIdempotentOfPow_commute_y_pow d s hζ hc hb)


/-- The selected corner has dimension `d ^ 2`. -/
theorem finrank_cornerOfPow :
    Module.finrank F (isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).Corner = d ^ 2 := by
  rw [(cornerAlgEquivOfPow d s hζ hc hb).toLinearEquiv.finrank_eq]
  apply finrank_eq
  rw [← pow_mul, Nat.mul_comm s d]
  exact hζ.pow_eq_one

/-- The first generator of the corner has `d`-th power equal to its scalar `c`. -/
theorem compress_x_pow :
    ((isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress x) ^ d =
      algebraMap F _ c := by
  apply (cornerAlgEquivOfPow d s hζ hc hb).injective
  simp

/-- The second generator of the corner has `d`-th power equal to its scalar `b`. -/
theorem compress_y_pow_pow :
    ((isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress (y ^ s)) ^ d =
      algebraMap F _ b := by
  apply (cornerAlgEquivOfPow d s hζ hc hb).injective
  simp

/-- The corner generators satisfy the smaller symbol algebra's commutation relation. -/
theorem compress_y_pow_mul_compress_x :
    (isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress (y ^ s) *
      (isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress x =
        ζ ^ s • ((isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress x *
          (isIdempotentElem_cornerIdempotentOfPow d s hζ hc hb).compress (y ^ s)) := by
  apply (cornerAlgEquivOfPow d s hζ hc hb).injective
  simp [y_mul_x]

end TauCeti.SymbolAlgebra
