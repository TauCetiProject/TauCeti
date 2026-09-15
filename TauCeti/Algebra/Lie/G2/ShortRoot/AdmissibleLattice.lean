/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre

/-!
# The admissible lattice in the seven-dimensional representation of type G2

This file extends the integral seven-dimensional representation of the type-`G₂` Serre
presentation to the rational Serre algebra and proves that its coordinate `ℤ`-lattice is
preserved by the Serre Kostant form. The raising and lowering matrices have integral entries and
cube to zero; the two long-root generators square to zero, while each short-root generator squares
to twice a single unit matrix, so its divided square is again an integral matrix. The Cartan
matrices act diagonally through the weights `TauCeti.G2ShortRoot.weight`.

Thus the coordinate lattice is an admissible lattice for the explicit Serre-generator Kostant
form. Its weights span the full type-`G₂` character lattice by
`TauCeti.G2ShortRoot.span_range_weight_eq_top`. These are the lattice inputs of the Kostant
toral-closure construction of the short-root type-`G₂` carrier. That carrier is not identified
with the pinned simply connected group scheme of type `G₂`, and constructions on it transfer to
that scheme only along such an identification.

## Main declarations

* `TauCeti.G2ShortRoot.rationalSerreRepresentation`: the rational seven-dimensional
  representation.
* `TauCeti.G2ShortRoot.rep`: its extension to the universal enveloping algebra.
* `TauCeti.G2ShortRoot.rootIntMatrix` and `TauCeti.G2ShortRoot.rootDividedSquare`: the integral
  matrix of each numbered simple-root generator and of its divided square.
* `TauCeti.G2ShortRoot.isNilpotent_rep_serreRootGenerator`: the simple-root generators act
  nilpotently, with `pow_three_rep_serreRootGenerator_eq_zero` giving the cube.
* `TauCeti.G2ShortRoot.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.G2ShortRoot.rep_serreKostantForm_apply_mem_lattice`: the Serre Kostant form preserves
  the lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§22.3 and 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Extension from the integral representation -/

/-- Entrywise coercion from integral to rational matrices, as a homomorphism of Lie rings. -/
private noncomputable def castMatrixLieHom :
    Matrix (Fin 7) (Fin 7) ℤ →ₗ⁅ℤ⁆ Matrix (Fin 7) (Fin 7) ℚ :=
  ((Int.castRingHom ℚ).mapMatrix.toIntAlgHom).toLieHom

@[simp]
private theorem castMatrixLieHom_apply (M : Matrix (Fin 7) (Fin 7) ℤ) (a b : Fin 7) :
    castMatrixLieHom M a b = (M a b : ℚ) := by
  simp only [castMatrixLieHom, AlgHom.toLieHom_apply, RingHom.toIntAlgHom_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]

@[simp]
private theorem castMatrixLieHom_mul (M N : Matrix (Fin 7) (Fin 7) ℤ) :
    castMatrixLieHom (M * N) = castMatrixLieHom M * castMatrixLieHom N := by
  exact map_mul ((Int.castRingHom ℚ).mapMatrix.toIntAlgHom) M N

/-- The rational raising matrix obtained from the integral representation. -/
noncomputable def raisingMatrixRat (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℚ :=
  castMatrixLieHom (raisingMatrix i)

/-- The rational lowering matrix obtained from the integral representation. -/
noncomputable def loweringMatrixRat (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℚ :=
  castMatrixLieHom (loweringMatrix i)

/-- The rational Cartan matrix obtained from the integral representation. -/
noncomputable def cartanMatrixRat (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℚ :=
  castMatrixLieHom (cartanMatrix i)

/-- The entries of the rational raising matrix are the integral raising coefficients. -/
@[simp]
theorem raisingMatrixRat_apply (i : Fin 2) (a b : Fin 7) :
    raisingMatrixRat i a b = (raisingMatrix i a b : ℚ) := by
  rw [raisingMatrixRat, castMatrixLieHom_apply]

/-- The entries of the rational lowering matrix are the integral lowering coefficients. -/
@[simp]
theorem loweringMatrixRat_apply (i : Fin 2) (a b : Fin 7) :
    loweringMatrixRat i a b = (loweringMatrix i a b : ℚ) := by
  rw [loweringMatrixRat, castMatrixLieHom_apply]

/-- The rational Cartan matrix is diagonal with the weights on its diagonal. -/
@[simp]
theorem cartanMatrixRat_apply (i : Fin 2) (a b : Fin 7) :
    cartanMatrixRat i a b = if a = b then (weight a i : ℚ) else 0 := by
  rw [cartanMatrixRat, castMatrixLieHom_apply, cartanMatrix_apply]
  split_ifs <;> norm_num

private theorem cast_lie_eq_zero {x y : Matrix (Fin 7) (Fin 7) ℤ}
    (h : ⁅x, y⁆ = 0) : ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = 0 := by
  rw [← LieHom.map_lie, h, map_zero]

private theorem cast_lie_eq {x y z : Matrix (Fin 7) (Fin 7) ℤ}
    (h : ⁅x, y⁆ = z) : ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = castMatrixLieHom z := by
  rw [← LieHom.map_lie, h]

private theorem cast_lie_eq_smul {x y z : Matrix (Fin 7) (Fin 7) ℤ} (c : ℤ)
    (h : ⁅x, y⁆ = c • z) :
    ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = c • castMatrixLieHom z := by
  rw [← LieHom.map_lie, h, map_zsmul]

private theorem cast_lie_eq_neg_smul {x y z : Matrix (Fin 7) (Fin 7) ℤ} (c : ℤ)
    (h : ⁅x, y⁆ = -(c • z)) :
    ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = -(c • castMatrixLieHom z) := by
  rw [← LieHom.map_lie, h, map_neg, map_zsmul]

private theorem cast_ad_pow_lie_eq_zero {x y : Matrix (Fin 7) (Fin 7) ℤ} (n : ℕ)
    (h : (LieAlgebra.ad ℤ _ x ^ n) ⁅x, y⁆ = 0) :
    (LieAlgebra.ad ℚ _ (castMatrixLieHom x) ^ n)
      ⁅castMatrixLieHom x, castMatrixLieHom y⁆ = 0 := by
  have h' := congrArg castMatrixLieHom h
  rw [LieHom.map_ad_pow, LieHom.map_lie, map_zero] at h'
  rw [← TauCeti.ad_pow_apply_eq_ad_pow_apply ℤ ℚ]
  exact h'

/-- The rational matrices satisfy the type-`G₂` Serre relations. -/
theorem isSerreSystemRat :
    TauCeti.IsSerreSystem ℚ CartanMatrix.G₂ cartanMatrixRat raisingMatrixRat
      loweringMatrixRat where
  lie_H_H i j := by
    simpa only [cartanMatrixRat] using cast_lie_eq_zero (isSerreSystem.lie_H_H i j)
  lie_E_F_self i := by
    simpa only [raisingMatrixRat, loweringMatrixRat, cartanMatrixRat] using
      cast_lie_eq (isSerreSystem.lie_E_F_self i)
  lie_E_F_of_ne i j hij := by
    simpa only [raisingMatrixRat, loweringMatrixRat] using
      cast_lie_eq_zero (isSerreSystem.lie_E_F_of_ne i j hij)
  lie_H_E i j := by
    simpa only [cartanMatrixRat, raisingMatrixRat] using
      cast_lie_eq_smul (CartanMatrix.G₂ i j) (isSerreSystem.lie_H_E i j)
  lie_H_F i j := by
    simpa only [cartanMatrixRat, loweringMatrixRat] using
      cast_lie_eq_neg_smul (CartanMatrix.G₂ i j) (isSerreSystem.lie_H_F i j)
  ad_pow_lie_E_E i j := by
    simpa only [raisingMatrixRat] using
      cast_ad_pow_lie_eq_zero (-CartanMatrix.G₂ i j).toNat (isSerreSystem.ad_pow_lie_E_E i j)
  ad_pow_lie_F_F i j := by
    simpa only [loweringMatrixRat] using
      cast_ad_pow_lie_eq_zero (-CartanMatrix.G₂ i j).toNat (isSerreSystem.ad_pow_lie_F_F i j)

/-- The rational seven-dimensional representation of the type-`G₂` Serre presentation. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ CartanMatrix.G₂ →ₗ⁅ℚ⁆ Matrix (Fin 7) (Fin 7) ℚ :=
  TauCeti.serreLift isSerreSystemRat

/-- The rational Serre representation sends `H_i` to the rational Cartan matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreH (i : Fin 2) :
    rationalSerreRepresentation (TauCeti.serreH ℚ CartanMatrix.G₂ i) = cartanMatrixRat i :=
  TauCeti.serreLift_serreH isSerreSystemRat i

/-- The rational Serre representation sends `E_i` to the rational raising matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 2) :
    rationalSerreRepresentation (TauCeti.serreE ℚ CartanMatrix.G₂ i) = raisingMatrixRat i :=
  TauCeti.serreLift_serreE isSerreSystemRat i

/-- The rational Serre representation sends `F_i` to the rational lowering matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreF (i : Fin 2) :
    rationalSerreRepresentation (TauCeti.serreF ℚ CartanMatrix.G₂ i) = loweringMatrixRat i :=
  TauCeti.serreLift_serreF isSerreSystemRat i

/-! ## The numbered root generators -/

/-- The integral matrix of a numbered simple-root generator: a raising matrix at a positive
index, a lowering matrix at a negative one. -/
def rootIntMatrix : Fin 2 ⊕ Fin 2 → Matrix (Fin 7) (Fin 7) ℤ
  | .inl i => raisingMatrix i
  | .inr i => loweringMatrix i

/-- The integral matrix of the divided square of a numbered simple-root generator: a single unit
matrix for the two short-root generators, zero for the two long-root ones. -/
def rootDividedSquare : Fin 2 ⊕ Fin 2 → Matrix (Fin 7) (Fin 7) ℤ
  | .inl i => ![Matrix.single 2 4 1, 0] i
  | .inr i => ![Matrix.single 4 2 1, 0] i

/-- The integral matrix of a positive numbered root generator is the raising matrix. -/
@[simp]
theorem rootIntMatrix_inl (i : Fin 2) : rootIntMatrix (.inl i) = raisingMatrix i := (rfl)

/-- The integral matrix of a negative numbered root generator is the lowering matrix. -/
@[simp]
theorem rootIntMatrix_inr (i : Fin 2) : rootIntMatrix (.inr i) = loweringMatrix i := (rfl)

/-- The divided square of a positive numbered root generator: a single unit matrix at the
short-root index, zero at the long-root one. -/
@[simp]
theorem rootDividedSquare_inl (i : Fin 2) :
    rootDividedSquare (.inl i) = ![Matrix.single 2 4 1, 0] i := (rfl)

/-- The divided square of a negative numbered root generator: a single unit matrix at the
short-root index, zero at the long-root one. -/
@[simp]
theorem rootDividedSquare_inr (i : Fin 2) :
    rootDividedSquare (.inr i) = ![Matrix.single 4 2 1, 0] i := (rfl)

/-- Every numbered root generator squares to twice its divided square. -/
theorem rootIntMatrix_mul_self (k : Fin 2 ⊕ Fin 2) :
    rootIntMatrix k * rootIntMatrix k = 2 • rootDividedSquare k := by
  rcases k with i | i <;> fin_cases i
  · exact raisingMatrix_zero_mul_self
  · simp [rootIntMatrix, rootDividedSquare]
  · exact loweringMatrix_zero_mul_self
  · simp [rootIntMatrix, rootDividedSquare]

/-- Every numbered root generator cubes to zero. -/
theorem rootIntMatrix_pow_three (k : Fin 2 ⊕ Fin 2) : rootIntMatrix k ^ 3 = 0 := by
  cases k with
  | inl i => exact raisingMatrix_pow_three i
  | inr i => exact loweringMatrix_pow_three i

/-- The rational Serre representation sends a numbered root generator to the cast of its
integral matrix. -/
theorem rationalSerreRepresentation_serreRootGenerator (k : Fin 2 ⊕ Fin 2) :
    rationalSerreRepresentation (TauCeti.serreRootGenerator CartanMatrix.G₂ k) =
      (rootIntMatrix k).map (Int.castRingHom ℚ) := by
  cases k with
  | inl i => rw [TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE]; rfl
  | inr i => rw [TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF]; rfl

/-! ## The enveloping-algebra representation -/

/-- The rational representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ CartanMatrix.G₂) →ₐ[ℚ]
      Module.End ℚ (Fin 7 → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    (Matrix.toLinAlgEquiv'.toAlgHom.toLieHom.comp rationalSerreRepresentation)

/-- The enveloping-algebra inclusion acts by multiplying with the represented matrix. -/
theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ CartanMatrix.G₂) (v : Fin 7 → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = rationalSerreRepresentation x *ᵥ v := by
  simp [rep]

/-- A numbered root generator acts by its integral matrix. -/
theorem rep_serreRootGenerator_apply (k : Fin 2 ⊕ Fin 2) (v : Fin 7 → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreRootGenerator CartanMatrix.G₂ k))
      v = (rootIntMatrix k).map (Int.castRingHom ℚ) *ᵥ v := by
  rw [rep_ι_apply, rationalSerreRepresentation_serreRootGenerator]

/-- **The represented simple-root generator is the linear map of its rational matrix.** Reading
the operator this way transports identities between the integral matrices, such as the value of
the square and the vanishing of the cube, to identities between operators. -/
theorem rep_serreRootGenerator_eq_toLinAlgEquiv (k : Fin 2 ⊕ Fin 2) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreRootGenerator CartanMatrix.G₂ k)) =
      Matrix.toLinAlgEquiv' ((rootIntMatrix k).map (Int.castRingHom ℚ)) :=
  LinearMap.ext fun v => by
    rw [rep_serreRootGenerator_apply, Matrix.toLinAlgEquiv'_apply]

/-- The divided square of a numbered root generator acts by the integral matrix of its divided
square. -/
theorem dividedPower_two_rep_serreRootGenerator_apply (k : Fin 2 ⊕ Fin 2) (v : Fin 7 → ℚ) :
    Associative.dividedPower 2
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator CartanMatrix.G₂ k))) v =
      (rootDividedSquare k).map (Int.castRingHom ℚ) *ᵥ v := by
  have hsq : rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.G₂ k)) ^ 2 =
      Matrix.toLinAlgEquiv' ((2 : ℕ) • (rootDividedSquare k).map (Int.castRingHom ℚ)) := by
    rw [rep_serreRootGenerator_eq_toLinAlgEquiv, ← map_pow, ← RingHom.mapMatrix_apply, ← map_pow,
      pow_two, rootIntMatrix_mul_self, map_nsmul, RingHom.mapMatrix_apply]
  rw [Associative.dividedPower_def, LinearMap.smul_apply, hsq, map_nsmul,
    LinearMap.smul_apply, Matrix.toLinAlgEquiv'_apply, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  norm_num [Nat.factorial]

/-- Every simple-root generator acts with cube zero. -/
theorem pow_three_rep_serreRootGenerator_eq_zero (k : Fin 2 ⊕ Fin 2) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.G₂ k)) ^ 3 = 0 := by
  rw [rep_serreRootGenerator_eq_toLinAlgEquiv, ← map_pow, ← RingHom.mapMatrix_apply, ← map_pow,
    rootIntMatrix_pow_three, map_zero, map_zero]

/-- Every represented simple-root generator is nilpotent, with nilpotence index at most three. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 2 ⊕ Fin 2) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.G₂ k))) :=
  ⟨3, pow_three_rep_serreRootGenerator_eq_zero k⟩

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational module. -/
def lattice : Submodule ℤ (Fin 7 → ℚ) :=
  TauCeti.coordinateLattice (Fin 7)

/-- A vector belongs to the lattice exactly when every coordinate is integral. -/
@[simp]
theorem mem_lattice_iff {v : Fin 7 → ℚ} :
    v ∈ lattice ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a :=
  TauCeti.mem_coordinateLattice_iff (Fin 7)

/-- The coordinate basis of the lattice. -/
noncomputable def latticeBasis : Module.Basis (Fin 7) ℤ lattice :=
  TauCeti.coordinateLatticeBasis (Fin 7)

/-- Coercing a lattice basis vector to the rational module gives the corresponding coordinate
vector. -/
@[simp]
theorem coe_latticeBasis (a : Fin 7) :
    ((latticeBasis a : lattice) : Fin 7 → ℚ) = Pi.single a 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin 7) a

/-- Every simple-root generator preserves the coordinate lattice. -/
theorem rep_serreRootGenerator_apply_mem_lattice (k : Fin 2 ⊕ Fin 2) {v : Fin 7 → ℚ}
    (hv : v ∈ lattice) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.G₂ k)) v ∈ lattice := by
  rw [rep_serreRootGenerator_apply]
  exact TauCeti.map_intCast_mulVec_mem_coordinateLattice (Fin 7) _ hv

/-- The divided square of every simple-root generator preserves the coordinate lattice. -/
theorem dividedPower_two_rep_serreRootGenerator_apply_mem_lattice (k : Fin 2 ⊕ Fin 2)
    {v : Fin 7 → ℚ} (hv : v ∈ lattice) :
    Associative.dividedPower 2
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator CartanMatrix.G₂ k))) v ∈ lattice := by
  rw [dividedPower_two_rep_serreRootGenerator_apply]
  exact TauCeti.map_intCast_mulVec_mem_coordinateLattice (Fin 7) _ hv

/-- Each coordinate basis vector has the corresponding weight for the Cartan generators. -/
theorem isCartanWeightVector_single (a : Fin 7) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ CartanMatrix.G₂) rep (weight a) (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (TauCeti.serreH ℚ CartanMatrix.G₂) rep).mpr fun i ↦ ?_
  rw [rep_ι_apply, rationalSerreRepresentation_serreH]
  ext b
  by_cases h : b = a
  · subst b
    simp [Matrix.mulVec, dotProduct, cartanMatrixRat_apply, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, cartanMatrixRat_apply, Pi.single_apply, h]

/-- Every lattice-basis vector is a Cartan weight vector with its weight. -/
theorem isCartanWeightVector_latticeBasis (a : Fin 7) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ CartanMatrix.G₂) rep (weight a)
      ((latticeBasis a : lattice) : Fin 7 → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single a

/-- **The coordinate lattice is admissible for the type-`G₂` Serre Kostant form.** -/
theorem rep_serreKostantForm_apply_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ CartanMatrix.G₂)}
    (hu : u ∈ TauCeti.serreKostantForm CartanMatrix.G₂) {v : Fin 7 → ℚ}
    (hv : v ∈ lattice) : rep u v ∈ lattice := by
  rw [TauCeti.serreKostantForm_def] at hu
  exact
    TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice_of_pow_three_eq_zero
      (TauCeti.serreRootGenerator CartanMatrix.G₂) (TauCeti.serreH ℚ CartanMatrix.G₂) rep
      (wt := weight) pow_three_rep_serreRootGenerator_eq_zero
      (fun k _ hw ↦ rep_serreRootGenerator_apply_mem_lattice k hw)
      (fun k _ hw ↦ dividedPower_two_rep_serreRootGenerator_apply_mem_lattice k hw)
      isCartanWeightVector_single hu hv

end TauCeti.G2ShortRoot
