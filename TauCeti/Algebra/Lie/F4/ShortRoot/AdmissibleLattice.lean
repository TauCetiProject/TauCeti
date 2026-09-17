/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Basic
public import TauCeti.Algebra.Lie.Matrix.IntegralCast
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre

/-!
# The admissible lattice of the short-root representation of type F4

This file extends the integral twenty-six-dimensional representation of type `F₄` from
`TauCeti.Algebra.Lie.F4.ShortRoot.Basic` to the rationals, lifts it to the universal enveloping
algebra of the rational type-`F₄` Serre Lie algebra, and proves that the coordinate `ℤ`-lattice
of the rational module is admissible for the Serre Kostant form: it is stable under every
divided power of a simple root generator and every binomial coefficient in a Cartan generator.

The long simple root generators square to zero on the module, so for them only the first divided
power is nonzero. The short simple root generators have nilpotence index three: their squares are
twice the integral divided-square matrices of `TauCeti.Algebra.Lie.F4.ShortRoot.Basic`, so their
second divided powers are integral and their higher ones vanish. This is what distinguishes the
short-root module from a minuscule one, and it is why the admissibility statement goes through
the general divided-power criterion rather than the square-zero shortcut.

## Main definitions

* `TauCeti.F4ShortRoot.rationalSerreRepresentation`: the rational Serre representation.
* `TauCeti.F4ShortRoot.rep`: its extension to the universal enveloping algebra.
* `TauCeti.F4ShortRoot.lattice` and `TauCeti.F4ShortRoot.latticeBasis`: the coordinate lattice
  and its standard basis.

## Main results

* `TauCeti.F4ShortRoot.pow_three_rep_serreRootGenerator_eq_zero` and
  `TauCeti.F4ShortRoot.isNilpotent_rep_serreRootGenerator`: every represented simple root
  generator cubes to zero.
* `TauCeti.F4ShortRoot.rep_dividedPower_serreRootGenerator_apply_mem_lattice`: every divided
  power of a simple root generator preserves the lattice.
* `TauCeti.F4ShortRoot.isCartanWeightVector_latticeBasis`: each lattice basis vector is a
  weight vector for the Cartan generators, with weight read from the weight table.
* `TauCeti.F4ShortRoot.rep_serreKostantForm_apply_mem_lattice`: the lattice is admissible.

## References

* B. Kostant, *Groups over `ℤ`*, in *Algebraic Groups and Discontinuous Subgroups*, Proc.
  Sympos. Pure Math. IX (1966).
* R. Steinberg, *Lectures on Chevalley Groups*, §12, for admissible lattices and the lattice
  generated from a highest weight vector by divided powers.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.
-/

-- Adapted from `TauCeti.Algebra.Lie.E7.Minuscule.AdmissibleLattice`, with the same declaration
-- order.

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## Extension from the integral representation -/

/-- The rational raising matrix obtained from the integral short-root representation. -/
noncomputable def raisingMatrixRat (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℚ :=
  TauCeti.matrixIntCastLieHom ℚ (raisingMatrix i)

/-- The rational lowering matrix obtained from the integral short-root representation. -/
noncomputable def loweringMatrixRat (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℚ :=
  TauCeti.matrixIntCastLieHom ℚ (loweringMatrix i)

/-- The rational Cartan matrix obtained from the integral short-root representation. -/
noncomputable def cartanMatrixRat (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℚ :=
  TauCeti.matrixIntCastLieHom ℚ (cartanMatrix i)

/-- The entries of the rational raising matrix are the integral raising coefficients. -/
@[simp]
theorem raisingMatrixRat_apply (i : Fin 4) (a b : Fin 26) :
    raisingMatrixRat i a b =
      if a = raisingTarget i b then (raisingCoeff i b : ℚ) else 0 := by
  rw [raisingMatrixRat, TauCeti.matrixIntCastLieHom_apply, raisingMatrix_apply]
  split_ifs <;> norm_num

/-- The entries of the rational lowering matrix are the integral lowering coefficients. -/
@[simp]
theorem loweringMatrixRat_apply (i : Fin 4) (a b : Fin 26) :
    loweringMatrixRat i a b =
      if a = loweringTarget i b then (loweringCoeff i b : ℚ) else 0 := by
  rw [loweringMatrixRat, TauCeti.matrixIntCastLieHom_apply, loweringMatrix_apply]
  split_ifs <;> norm_num

/-- The rational Cartan matrix is diagonal with the short-root weights on its diagonal. -/
@[simp]
theorem cartanMatrixRat_apply (i : Fin 4) (a b : Fin 26) :
    cartanMatrixRat i a b = if a = b then (f4ShortRootWeight a i : ℚ) else 0 := by
  rw [cartanMatrixRat, TauCeti.matrixIntCastLieHom_apply, cartanMatrix_apply]
  split_ifs <;> norm_num

/-- The rational short-root matrices satisfy the type-`F₄` Serre relations. -/
theorem isSerreSystemRat :
    TauCeti.IsSerreSystem ℚ CartanMatrix.F₄ᵀ cartanMatrixRat raisingMatrixRat
      loweringMatrixRat := by
  have h := isSerreSystem.map (TauCeti.matrixIntCastLieHom ℚ)
  have hH : TauCeti.matrixIntCastLieHom ℚ ∘ cartanMatrix = cartanMatrixRat := by
    funext i
    rfl
  have hE : TauCeti.matrixIntCastLieHom ℚ ∘ raisingMatrix = raisingMatrixRat := by
    funext i
    rfl
  have hF : TauCeti.matrixIntCastLieHom ℚ ∘ loweringMatrix = loweringMatrixRat := by
    funext i
    rfl
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

/-- The rational twenty-six-dimensional short-root representation of the type-`F₄` Serre
presentation. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ CartanMatrix.F₄ᵀ →ₗ⁅ℚ⁆ Matrix (Fin 26) (Fin 26) ℚ :=
  TauCeti.serreLift isSerreSystemRat

/-- The rational Serre representation sends `H_i` to the rational Cartan matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreH (i : Fin 4) :
    rationalSerreRepresentation (TauCeti.serreH ℚ CartanMatrix.F₄ᵀ i) = cartanMatrixRat i :=
  TauCeti.serreLift_serreH isSerreSystemRat i

/-- The rational Serre representation sends `E_i` to the rational raising matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 4) :
    rationalSerreRepresentation (TauCeti.serreE ℚ CartanMatrix.F₄ᵀ i) = raisingMatrixRat i :=
  TauCeti.serreLift_serreE isSerreSystemRat i

/-- The rational Serre representation sends `F_i` to the rational lowering matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreF (i : Fin 4) :
    rationalSerreRepresentation (TauCeti.serreF ℚ CartanMatrix.F₄ᵀ i) = loweringMatrixRat i :=
  TauCeti.serreLift_serreF isSerreSystemRat i

/-! ## The enveloping-algebra representation -/

/-- The rational short-root representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ CartanMatrix.F₄ᵀ) →ₐ[ℚ]
      Module.End ℚ (Fin 26 → ℚ) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ
    (Matrix.toLinAlgEquiv'.toAlgHom.toLieHom.comp rationalSerreRepresentation)

/-- The enveloping-algebra inclusion is represented by the represented matrix. -/
theorem rep_ι (x : Matrix.ToLieAlgebra ℚ CartanMatrix.F₄ᵀ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      Matrix.toLinAlgEquiv' (rationalSerreRepresentation x) := by
  simp [rep]

/-- The enveloping-algebra inclusion acts by multiplying with the represented matrix. -/
theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ CartanMatrix.F₄ᵀ) (v : Fin 26 → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = rationalSerreRepresentation x *ᵥ v := by
  simp [rep]

/-- The enveloping-algebra representation sends the divided power of the inclusion of a Serre
element to the matrix divided power of the represented matrix, acting on `v`. -/
theorem rep_dividedPower_ι_apply (x : Matrix.ToLieAlgebra ℚ CartanMatrix.F₄ᵀ) (n : ℕ)
    (v : Fin 26 → ℚ) :
    rep (Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) v =
      Associative.dividedPower n (rationalSerreRepresentation x) *ᵥ v := by
  have h := Associative.map_dividedPower (Matrix.toLinAlgEquiv' (R := ℚ) (n := Fin 26)) n
    (rationalSerreRepresentation x)
  rw [Associative.map_dividedPower, rep_ι, ← h, Matrix.toLinAlgEquiv'_apply]

/-- **The represented power of an inclusion is the represented matrix power.** Powers pass through
`Matrix.toLinAlgEquiv'` because it is an algebra equivalence. -/
theorem rep_ι_pow (x : Matrix.ToLieAlgebra ℚ CartanMatrix.F₄ᵀ) (n : ℕ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) ^ n =
      Matrix.toLinAlgEquiv' (rationalSerreRepresentation x ^ n) := by
  rw [rep_ι, ← map_pow]

/-- The matrix a simple root generator is represented by: the rational raising or lowering
matrix. -/
noncomputable def rootMatrixRat : Fin 4 ⊕ Fin 4 → Matrix (Fin 26) (Fin 26) ℚ
  | .inl i => raisingMatrixRat i
  | .inr i => loweringMatrixRat i

/-- The integral matrix of a simple root generator: the raising or lowering matrix. -/
def rootMatrix : Fin 4 ⊕ Fin 4 → Matrix (Fin 26) (Fin 26) ℤ
  | .inl i => raisingMatrix i
  | .inr i => loweringMatrix i

/-- The integral divided square of a simple root generator. -/
def rootDividedSquareMatrix : Fin 4 ⊕ Fin 4 → Matrix (Fin 26) (Fin 26) ℤ
  | .inl i => raisingDividedSquareMatrix i
  | .inr i => loweringDividedSquareMatrix i

@[simp]
theorem rootMatrixRat_inl (i : Fin 4) : rootMatrixRat (.inl i) = raisingMatrixRat i := by
  rw [rootMatrixRat]

@[simp]
theorem rootMatrixRat_inr (i : Fin 4) : rootMatrixRat (.inr i) = loweringMatrixRat i := by
  rw [rootMatrixRat]

@[simp]
theorem rootMatrix_inl (i : Fin 4) : rootMatrix (.inl i) = raisingMatrix i := by
  rw [rootMatrix]

@[simp]
theorem rootMatrix_inr (i : Fin 4) : rootMatrix (.inr i) = loweringMatrix i := by
  rw [rootMatrix]

@[simp]
theorem rootDividedSquareMatrix_inl (i : Fin 4) :
    rootDividedSquareMatrix (.inl i) = raisingDividedSquareMatrix i := by
  rw [rootDividedSquareMatrix]

@[simp]
theorem rootDividedSquareMatrix_inr (i : Fin 4) :
    rootDividedSquareMatrix (.inr i) = loweringDividedSquareMatrix i := by
  rw [rootDividedSquareMatrix]

private theorem rootMatrixRat_eq_cast (k : Fin 4 ⊕ Fin 4) :
    rootMatrixRat k = TauCeti.matrixIntCastLieHom ℚ (rootMatrix k) := by
  cases k with
  | inl i => rw [rootMatrixRat_inl, rootMatrix_inl, raisingMatrixRat]
  | inr i => rw [rootMatrixRat_inr, rootMatrix_inr, loweringMatrixRat]

/-- The entries of the rational matrix of a simple root generator are the integral ones. -/
@[simp] theorem rootMatrixRat_apply (k : Fin 4 ⊕ Fin 4) (a b : Fin 26) :
    rootMatrixRat k a b = (rootMatrix k a b : ℚ) := by
  rw [rootMatrixRat_eq_cast, TauCeti.matrixIntCastLieHom_apply]

/-- The rational Serre representation sends a simple root generator to its rational matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreRootGenerator (k : Fin 4 ⊕ Fin 4) :
    rationalSerreRepresentation (TauCeti.serreRootGenerator CartanMatrix.F₄ᵀ k) =
      rootMatrixRat k := by
  cases k with
  | inl i => rw [TauCeti.serreRootGenerator_inl, rationalSerreRepresentation_serreE, rootMatrixRat]
  | inr i => rw [TauCeti.serreRootGenerator_inr, rationalSerreRepresentation_serreF, rootMatrixRat]

/-- The square of a rational simple root matrix is twice the cast of its divided square. -/
theorem rootMatrixRat_mul_self (k : Fin 4 ⊕ Fin 4) :
    rootMatrixRat k * rootMatrixRat k =
      (2 : ℚ) • (rootDividedSquareMatrix k).map (Int.cast : ℤ → ℚ) := by
  rw [rootMatrixRat_eq_cast, ← TauCeti.matrixIntCastLieHom_mul,
    ← TauCeti.matrixIntCastLieHom_eq_map]
  cases k with
  | inl i =>
      rw [rootMatrix_inl, rootDividedSquareMatrix_inl, raisingMatrix_mul_self, map_zsmul,
        ← Int.cast_smul_eq_zsmul ℚ]
      norm_num
  | inr i =>
      rw [rootMatrix_inr, rootDividedSquareMatrix_inr, loweringMatrix_mul_self, map_zsmul,
        ← Int.cast_smul_eq_zsmul ℚ]
      norm_num

/-- Every integral simple root matrix cubes to zero. -/
@[simp]
theorem rootMatrix_pow_three (k : Fin 4 ⊕ Fin 4) : rootMatrix k ^ 3 = 0 := by
  cases k with
  | inl i => rw [rootMatrix_inl, raisingMatrix_pow_three]
  | inr i => rw [rootMatrix_inr, loweringMatrix_pow_three]

/-- Every rational simple root matrix cubes to zero. -/
@[simp]
theorem rootMatrixRat_pow_three (k : Fin 4 ⊕ Fin 4) : rootMatrixRat k ^ 3 = 0 := by
  rw [rootMatrixRat_eq_cast, TauCeti.matrixIntCastLieHom_eq_map]
  calc
    (rootMatrix k).map (Int.cast : ℤ → ℚ) ^ 3 =
        ((rootMatrix k) ^ 3).map (Int.castRingHom ℚ) :=
      (Matrix.map_pow (rootMatrix k) (Int.castRingHom ℚ) 3).symm
    _ = 0 := by rw [rootMatrix_pow_three]; simp

/-- Every simple root generator acts with cube zero in the rational short-root
representation. -/
theorem pow_three_rep_serreRootGenerator_eq_zero (k : Fin 4 ⊕ Fin 4) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.F₄ᵀ k)) ^ 3 = 0 := by
  rw [rep_ι_pow, rationalSerreRepresentation_serreRootGenerator, rootMatrixRat_pow_three,
    map_zero]

/-- Every represented simple root generator is nilpotent, with nilpotence index at most three. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 4 ⊕ Fin 4) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.F₄ᵀ k))) :=
  ⟨3, pow_three_rep_serreRootGenerator_eq_zero k⟩

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational short-root module. -/
def lattice : Submodule ℤ (Fin 26 → ℚ) :=
  TauCeti.coordinateLattice (Fin 26)

/-- A short-root module vector belongs to the lattice exactly when every coordinate is
integral. -/
@[simp]
theorem mem_lattice_iff {v : Fin 26 → ℚ} :
    v ∈ lattice ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a :=
  TauCeti.mem_coordinateLattice_iff (Fin 26)

/-- The coordinate basis of the short-root lattice. -/
noncomputable def latticeBasis : Module.Basis (Fin 26) ℤ lattice :=
  TauCeti.coordinateLatticeBasis (Fin 26)

/-- Coercing a lattice basis vector to the rational module gives the corresponding coordinate
vector. -/
@[simp]
theorem coe_latticeBasis (a : Fin 26) :
    ((latticeBasis a : lattice) : Fin 26 → ℚ) = Pi.single a 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin 26) a

/-- The divided square of a rational simple root matrix is the cast of its integral divided
square. -/
theorem dividedPower_two_rootMatrixRat (k : Fin 4 ⊕ Fin 4) :
    Associative.dividedPower 2 (rootMatrixRat k) =
      (rootDividedSquareMatrix k).map (Int.cast : ℤ → ℚ) := by
  rw [Associative.dividedPower_def, pow_two, rootMatrixRat_mul_self, smul_smul]
  norm_num

/-- The divided powers of a rational simple root matrix of order at least three vanish. -/
theorem dividedPower_rootMatrixRat_eq_zero (k : Fin 4 ⊕ Fin 4) {n : ℕ} (hn : 3 ≤ n) :
    Associative.dividedPower n (rootMatrixRat k) = 0 := by
  rw [Associative.dividedPower_def, pow_eq_zero_of_le hn (rootMatrixRat_pow_three k), smul_zero]

/-- **Every divided power of a simple root generator preserves the short-root lattice.** -/
theorem rep_dividedPower_serreRootGenerator_apply_mem_lattice (k : Fin 4 ⊕ Fin 4) (n : ℕ)
    {v : Fin 26 → ℚ} (hv : v ∈ lattice) :
    rep (Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator CartanMatrix.F₄ᵀ k))) v ∈ lattice := by
  rw [rep_dividedPower_ι_apply, rationalSerreRepresentation_serreRootGenerator]
  match n with
  | 0 => simpa using hv
  | 1 =>
      rw [Associative.dividedPower_one, rootMatrixRat_eq_cast]
      exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice _ hv
  | 2 =>
      rw [dividedPower_two_rootMatrixRat, ← TauCeti.matrixIntCastLieHom_eq_map]
      exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice _ hv
  | n + 3 =>
      rw [dividedPower_rootMatrixRat_eq_zero k (by omega), Matrix.zero_mulVec]
      exact zero_mem _

/-- Each coordinate basis vector has the corresponding short-root weight for the Cartan
generators. -/
theorem isCartanWeightVector_single (a : Fin 26) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ CartanMatrix.F₄ᵀ) rep (f4ShortRootWeight a) (Pi.single a 1) := by
  refine (TauCeti.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (TauCeti.serreH ℚ CartanMatrix.F₄ᵀ) rep).mpr fun i ↦ ?_
  rw [rep_ι_apply, rationalSerreRepresentation_serreH]
  ext b
  by_cases h : b = a
  · subst b
    simp [Matrix.mulVec, dotProduct, cartanMatrixRat_apply, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, cartanMatrixRat_apply, Pi.single_apply, h]

/-- Every lattice-basis vector is a Cartan weight vector with its short-root weight. -/
theorem isCartanWeightVector_latticeBasis (a : Fin 26) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ CartanMatrix.F₄ᵀ) rep (f4ShortRootWeight a)
      ((latticeBasis a : lattice) : Fin 26 → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single a

/-- **The short-root coordinate lattice is admissible for the type-`F₄` Serre Kostant form.** -/
theorem rep_serreKostantForm_apply_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ (Matrix.ToLieAlgebra ℚ CartanMatrix.F₄ᵀ)}
    (hu : u ∈ TauCeti.serreKostantForm CartanMatrix.F₄ᵀ) {v : Fin 26 → ℚ}
    (hv : v ∈ lattice) : rep u v ∈ lattice := by
  rw [TauCeti.serreKostantForm_def] at hu
  exact UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice_of_pow_eq_zero
    (TauCeti.serreRootGenerator CartanMatrix.F₄ᵀ) (TauCeti.serreH ℚ CartanMatrix.F₄ᵀ) rep 3
    pow_three_rep_serreRootGenerator_eq_zero (fun k n _ _ hw => by
      rw [← Associative.map_dividedPower]
      exact rep_dividedPower_serreRootGenerator_apply_mem_lattice k n hw)
    isCartanWeightVector_single hu hv

end TauCeti.F4ShortRoot
