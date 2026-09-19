/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre

import TauCeti.Algebra.Lie.Matrix.IntegralCast

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
toral-closure construction for the short-root type-`G₂` representation. That integral toral
closure is not identified with the pinned simply connected group scheme of type `G₂`, and
constructions on it transfer to that scheme only along such an identification.

## Main declarations

* `TauCeti.G2ShortRoot.rationalSerreRepresentation`: the rational seven-dimensional
  representation.
* `TauCeti.G2ShortRoot.rep`: its extension to the universal enveloping algebra.
* `TauCeti.G2ShortRoot.rootMatrix` and
  `TauCeti.G2ShortRoot.rootDividedSquareMatrix`: the integral matrix of each numbered simple-root
  generator and of its divided square.
* `TauCeti.G2ShortRoot.isNilpotent_rep_serreRootGenerator`: the simple-root generators act
  nilpotently, with `pow_three_rep_serreRootGenerator_eq_zero` giving the cube.
* `TauCeti.G2ShortRoot.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.G2ShortRoot.rep_serreKostantForm_apply_mem_lattice`: the Serre Kostant form preserves
  the lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§22.3 and 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
* The formal organization follows `TauCeti.Algebra.Lie.F4.ShortRoot.AdmissibleLattice` and
  `TauCeti.Algebra.Lie.E7.Minuscule.AdmissibleLattice`.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Extension from the integral representation -/

/-- The rational raising matrix obtained from the integral representation. -/
noncomputable def raisingMatrixRat (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℚ :=
  matrixIntCastLieHom ℚ (raisingMatrix i)

/-- The rational lowering matrix obtained from the integral representation. -/
noncomputable def loweringMatrixRat (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℚ :=
  matrixIntCastLieHom ℚ (loweringMatrix i)

/-- The rational Cartan matrix obtained from the integral representation. -/
noncomputable def cartanMatrixRat (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℚ :=
  matrixIntCastLieHom ℚ (cartanMatrix i)

/-- The entries of the rational raising matrix are the integral raising coefficients. -/
@[simp]
theorem raisingMatrixRat_apply (i : Fin 2) (a b : Fin 7) :
    raisingMatrixRat i a b = (raisingMatrix i a b : ℚ) := by
  rw [raisingMatrixRat, matrixIntCastLieHom_apply]

/-- The entries of the rational lowering matrix are the integral lowering coefficients. -/
@[simp]
theorem loweringMatrixRat_apply (i : Fin 2) (a b : Fin 7) :
    loweringMatrixRat i a b = (loweringMatrix i a b : ℚ) := by
  rw [loweringMatrixRat, matrixIntCastLieHom_apply]

/-- The rational Cartan matrix is diagonal with the weights on its diagonal. -/
@[simp]
theorem cartanMatrixRat_apply (i : Fin 2) (a b : Fin 7) :
    cartanMatrixRat i a b = if a = b then (weight a i : ℚ) else 0 := by
  rw [cartanMatrixRat, matrixIntCastLieHom_apply, cartanMatrix_apply]
  split_ifs <;> norm_num

/-- The rational matrices satisfy the type-`G₂` Serre relations. -/
theorem isSerreSystemRat :
    TauCeti.IsSerreSystem ℚ CartanMatrix.G₂ cartanMatrixRat raisingMatrixRat
      loweringMatrixRat := by
  have h := isSerreSystem.map (matrixIntCastLieHom ℚ)
  have hH : matrixIntCastLieHom ℚ ∘ cartanMatrix = cartanMatrixRat := rfl
  have hE : matrixIntCastLieHom ℚ ∘ raisingMatrix = raisingMatrixRat := rfl
  have hF : matrixIntCastLieHom ℚ ∘ loweringMatrix = loweringMatrixRat := rfl
  rw [hH, hE, hF] at h
  refine { h with
    ad_pow_lie_E_E := ?_
    ad_pow_lie_F_F := ?_ }
  · intro i j
    rw [← ad_pow_apply_eq_ad_pow_apply ℤ ℚ]
    exact h.ad_pow_lie_E_E i j
  · intro i j
    rw [← ad_pow_apply_eq_ad_pow_apply ℤ ℚ]
    exact h.ad_pow_lie_F_F i j

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
def rootMatrix : Fin 2 ⊕ Fin 2 → Matrix (Fin 7) (Fin 7) ℤ
  | .inl i => raisingMatrix i
  | .inr i => loweringMatrix i

/-- The integral matrix of the divided square of a numbered simple-root generator: a single unit
matrix for the two short-root generators, zero for the two long-root ones. -/
def rootDividedSquareMatrix : Fin 2 ⊕ Fin 2 → Matrix (Fin 7) (Fin 7) ℤ
  | .inl i => ![Matrix.single 2 4 1, 0] i
  | .inr i => ![Matrix.single 4 2 1, 0] i

/-- The integral matrix of a positive numbered root generator is the raising matrix. -/
@[simp]
theorem rootMatrix_inl (i : Fin 2) : rootMatrix (.inl i) = raisingMatrix i := (rfl)

/-- The integral matrix of a negative numbered root generator is the lowering matrix. -/
@[simp]
theorem rootMatrix_inr (i : Fin 2) : rootMatrix (.inr i) = loweringMatrix i := (rfl)

/-- The divided square of a positive numbered root generator: a single unit matrix at the
short-root index, zero at the long-root one. -/
@[simp]
theorem rootDividedSquareMatrix_inl (i : Fin 2) :
    rootDividedSquareMatrix (.inl i) = ![Matrix.single 2 4 1, 0] i := (rfl)

/-- The divided square of a negative numbered root generator: a single unit matrix at the
short-root index, zero at the long-root one. -/
@[simp]
theorem rootDividedSquareMatrix_inr (i : Fin 2) :
    rootDividedSquareMatrix (.inr i) = ![Matrix.single 4 2 1, 0] i := (rfl)

/-- Every numbered root generator squares to twice its divided square. -/
theorem rootMatrix_mul_self (k : Fin 2 ⊕ Fin 2) :
    rootMatrix k * rootMatrix k = 2 • rootDividedSquareMatrix k := by
  rcases k with i | i <;> fin_cases i
  · exact raisingMatrix_zero_mul_self
  · simp [rootMatrix, rootDividedSquareMatrix]
  · exact loweringMatrix_zero_mul_self
  · simp [rootMatrix, rootDividedSquareMatrix]

/-- Every numbered root generator cubes to zero. -/
theorem rootMatrix_pow_three (k : Fin 2 ⊕ Fin 2) : rootMatrix k ^ 3 = 0 := by
  cases k with
  | inl i => exact raisingMatrix_pow_three i
  | inr i => exact loweringMatrix_pow_three i

/-- The rational Serre representation sends a numbered root generator to the cast of its
integral matrix. -/
theorem rationalSerreRepresentation_serreRootGenerator (k : Fin 2 ⊕ Fin 2) :
    rationalSerreRepresentation (TauCeti.serreRootGenerator CartanMatrix.G₂ k) =
      (rootMatrix k).map (Int.castRingHom ℚ) := by
  cases k with
  | inl i =>
      rw [TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE]
      ext a b
      simp [raisingMatrixRat, rootMatrix]
  | inr i =>
      rw [TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF]
      ext a b
      simp [loweringMatrixRat, rootMatrix]

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
      v = (rootMatrix k).map (Int.castRingHom ℚ) *ᵥ v := by
  rw [rep_ι_apply, rationalSerreRepresentation_serreRootGenerator]

/-- **The represented simple-root generator is the linear map of its rational matrix.** Reading
the operator this way transports identities between the integral matrices, such as the value of
the square and the vanishing of the cube, to identities between operators. -/
theorem rep_serreRootGenerator_eq_toLinAlgEquiv' (k : Fin 2 ⊕ Fin 2) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreRootGenerator CartanMatrix.G₂ k)) =
      Matrix.toLinAlgEquiv' ((rootMatrix k).map (Int.castRingHom ℚ)) :=
  LinearMap.ext fun v => by
    rw [rep_serreRootGenerator_apply, Matrix.toLinAlgEquiv'_apply]

/-- The divided square of a numbered root generator acts by the integral matrix of its divided
square. -/
theorem dividedPower_two_rep_serreRootGenerator_apply (k : Fin 2 ⊕ Fin 2) (v : Fin 7 → ℚ) :
    Associative.dividedPower 2
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator CartanMatrix.G₂ k))) v =
      (rootDividedSquareMatrix k).map (Int.castRingHom ℚ) *ᵥ v := by
  have hsq : rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.G₂ k)) ^ 2 =
      (2 : ℕ) • Matrix.toLinAlgEquiv'
        ((rootDividedSquareMatrix k).map (Int.castRingHom ℚ)) := by
    rw [rep_serreRootGenerator_eq_toLinAlgEquiv', ← map_pow, ← RingHom.mapMatrix_apply,
      ← map_pow, RingHom.mapMatrix_apply, pow_two, rootMatrix_mul_self]
    calc
      _ = Matrix.toLinAlgEquiv'
          ((RingHom.mapMatrix (Int.castRingHom ℚ)) (2 • rootDividedSquareMatrix k)) := by
        rw [RingHom.mapMatrix_apply]
      _ = Matrix.toLinAlgEquiv'
          (2 • (RingHom.mapMatrix (Int.castRingHom ℚ)) (rootDividedSquareMatrix k)) := by
        rw [map_nsmul]
      _ = 2 • Matrix.toLinAlgEquiv'
          ((RingHom.mapMatrix (Int.castRingHom ℚ)) (rootDividedSquareMatrix k)) :=
        map_nsmul Matrix.toLinAlgEquiv' 2 _
      _ = _ := by rw [RingHom.mapMatrix_apply]
  rw [Associative.dividedPower_def, LinearMap.smul_apply, hsq, LinearMap.smul_apply,
    Matrix.toLinAlgEquiv'_apply, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  norm_num [Nat.factorial]

/-- Every simple-root generator acts with cube zero. -/
theorem pow_three_rep_serreRootGenerator_eq_zero (k : Fin 2 ⊕ Fin 2) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.G₂ k)) ^ 3 = 0 := by
  rw [rep_serreRootGenerator_eq_toLinAlgEquiv', ← map_pow, ← RingHom.mapMatrix_apply,
    ← map_pow, RingHom.mapMatrix_apply, rootMatrix_pow_three]
  simp

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
  rw [lattice] at hv ⊢
  have hmatrix :
      (rootMatrix k).map (Int.castRingHom ℚ) =
        TauCeti.matrixIntCastLieHom ℚ (rootMatrix k) := by
    ext a b
    simp
  rw [hmatrix]
  exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (rootMatrix k) hv

/-- The divided square of every simple-root generator preserves the coordinate lattice. -/
theorem dividedPower_two_rep_serreRootGenerator_apply_mem_lattice (k : Fin 2 ⊕ Fin 2)
    {v : Fin 7 → ℚ} (hv : v ∈ lattice) :
    Associative.dividedPower 2
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator CartanMatrix.G₂ k))) v ∈ lattice := by
  rw [dividedPower_two_rep_serreRootGenerator_apply]
  rw [lattice] at hv ⊢
  have hmatrix :
      (rootDividedSquareMatrix k).map (Int.castRingHom ℚ) =
        TauCeti.matrixIntCastLieHom ℚ (rootDividedSquareMatrix k) := by
    ext a b
    simp
  rw [hmatrix]
  exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (rootDividedSquareMatrix k) hv

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
  exact TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice_of_pow_eq_zero
    (TauCeti.serreRootGenerator CartanMatrix.G₂) (TauCeti.serreH ℚ CartanMatrix.G₂) rep
    (wt := weight) 3 pow_three_rep_serreRootGenerator_eq_zero
    (fun k m hm v hv ↦ by
      have : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      rcases this with rfl | rfl | rfl
      · simpa using hv
      · simpa using rep_serreRootGenerator_apply_mem_lattice k hv
      · simpa using dividedPower_two_rep_serreRootGenerator_apply_mem_lattice k hv)
    isCartanWeightVector_single hu hv

end TauCeti.G2ShortRoot
