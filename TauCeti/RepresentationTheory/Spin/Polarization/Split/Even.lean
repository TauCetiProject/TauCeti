/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.Hyperbolic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.HyperbolicPair

/-!
# The standard split even-dimensional polarization

For a commutative ring `K`, the hyperbolic quadratic space on a finite free module `M` is
`M* × M` with quadratic form `(f, x) ↦ f x`. This file gives the coordinate instance
`M = Fin n → K` its canonical polarization: the two coordinate axes are the isotropic summands,
their polar pairing is evaluation, and the orthogonal remainder is zero. It is the instance
`M = Fin n → K` of `TauCeti.SpinPolarizationData.hyperbolic`.

Unlike the existence construction for a nondegenerate quadratic form over a separably closed
field, this polarization uses the fixed coordinate summands. Its named coordinate basis can be fed
directly into the spin representation and Kostant-lattice constructions.

## Main declarations

* `TauCeti.SplitEvenSpace`: the standard hyperbolic quadratic space `M* × M`.
* `TauCeti.splitEvenForm`: its quadratic form `(f, x) ↦ f x`.
* `TauCeti.splitEvenPolarization`: the canonical polarization by the two coordinate axes.
* `TauCeti.splitEvenBasis`: the coordinate basis of the first isotropic summand.
* `TauCeti.splitEvenDualBasis`: the basis of `M* × M` by dual coordinates and coordinates, in
  which the polar form has Gram matrix `fromBlocks 0 1 1 0`.
* `TauCeti.finrank_splitEvenPolarization_W`: the first isotropic summand has dimension `n`.
* `TauCeti.isHyperbolicFamily_splitEvenForm`: the coordinate hyperbolic pairs form a family of
  mutually orthogonal hyperbolic pairs.
* `TauCeti.splitEvenSpaceBaseChange`: the base change `SplitEvenSpace R n → SplitEvenSpace S n`
  along an algebra `R → S`, with `TauCeti.splitEvenForm_splitEvenSpaceBaseChange` showing that it
  carries the split form to its image in `S`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
-/

public section

namespace TauCeti

open Module

universe u

/-- The standard split even-dimensional quadratic space on `Fin n → K`: the product of its
dual coordinate module and coordinate module. -/
abbrev SplitEvenSpace (K : Type u) [CommRing K] (n : ℕ) :=
  Module.Dual K (Fin n → K) × (Fin n → K)

/-- The standard split quadratic form on `M* × M`, given by `(f, x) ↦ f x`. -/
def splitEvenForm (K : Type u) [CommRing K] (n : ℕ) :
    QuadraticForm K (SplitEvenSpace K n) :=
  QuadraticForm.dualProd K (Fin n → K)

/-- Evaluation formula for the standard split quadratic form. -/
@[simp]
theorem splitEvenForm_apply (K : Type u) [CommRing K] (n : ℕ)
    (x : SplitEvenSpace K n) : splitEvenForm K n x = x.1 x.2 := by
  simp [splitEvenForm]

/-- The standard split quadratic form is nondegenerate over every commutative ring. -/
theorem nondegenerate_splitEvenForm (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenForm K n).Nondegenerate := by
  rw [splitEvenForm]
  exact nondegenerate_dualProd (Module.eval_apply_injective K)

/-- Polarization formula for the standard split quadratic form. -/
@[simp]
theorem polar_splitEvenForm (K : Type u) [CommRing K] (n : ℕ)
    (x y : SplitEvenSpace K n) :
    QuadraticMap.polar (splitEvenForm K n) x y = x.1 y.2 + y.1 x.2 := by
  rw [splitEvenForm, polar_dualProd]

/-- The canonical polarization of the standard split quadratic space.

The coordinate axis is the first isotropic summand, the dual-coordinate axis is the second,
and the orthogonal remainder is zero. -/
noncomputable def splitEvenPolarization (K : Type u) [CommRing K] (n : ℕ) :
    SpinPolarizationData (splitEvenForm K n) :=
  SpinPolarizationData.hyperbolic (Module.eval_apply_injective K)

/-- The first isotropic summand of the standard split polarization is `Submodule.snd`. -/
private theorem splitEvenPolarization_W_eq_snd (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).W = Submodule.snd K (Module.Dual K (Fin n → K)) (Fin n → K) := by
  rw [splitEvenPolarization, SpinPolarizationData.hyperbolic_W]

/-- The first isotropic summand of the standard split polarization is the coordinate axis. -/
@[simp]
theorem splitEvenPolarization_W (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).W =
      (⊥ : Submodule K (Module.Dual K (Fin n → K))).prod ⊤ := by
  rw [splitEvenPolarization_W_eq_snd]
  ext
  simp

/-- The second isotropic summand of the standard split polarization is the dual-coordinate
axis. -/
@[simp]
theorem splitEvenPolarization_W' (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).W' =
      (⊤ : Submodule K (Module.Dual K (Fin n → K))).prod ⊥ := by
  rw [splitEvenPolarization, SpinPolarizationData.hyperbolic_W']
  ext
  simp

/-- The standard split even-dimensional polarization has no orthogonal remainder. -/
@[simp]
theorem splitEvenPolarization_line (K : Type u) [CommRing K] (n : ℕ) :
    (splitEvenPolarization K n).line = ⊥ :=
  SpinPolarizationData.hyperbolic_line _

/-- The coordinate basis of the first isotropic summand in the standard split polarization. -/
noncomputable def splitEvenBasis (K : Type u) [CommRing K] (n : ℕ) :
    Module.Basis (Fin n) K (splitEvenPolarization K n).W :=
  (SpinPolarizationData.hyperbolicBasis (Pi.basisFun K (Fin n))).map
    (LinearEquiv.ofEq _ _ (splitEvenPolarization_W_eq_snd K n).symm)

/-- A coordinate-basis vector of the first isotropic summand is the corresponding standard
coordinate vector on the second axis of the split space. -/
@[simp]
theorem coe_splitEvenBasis (K : Type u) [CommRing K] (n : ℕ) (i : Fin n) :
    ((splitEvenBasis K n i : (splitEvenPolarization K n).W) : SplitEvenSpace K n) =
      (0, Pi.single i 1) := by
  rw [splitEvenBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    SpinPolarizationData.coe_hyperbolicBasis_apply, Pi.basisFun_apply]

/-- The basis of the standard split space `M* × M` given by the dual coordinate functionals and
the coordinate vectors. -/
noncomputable def splitEvenDualBasis (K : Type u) [CommRing K] (n : ℕ) :
    Basis (Fin n ⊕ Fin n) K (SplitEvenSpace K n) :=
  (Pi.basisFun K (Fin n)).dualBasis.prod (Pi.basisFun K (Fin n))

/-- The first half of the split basis consists of the standard dual-coordinate axes. -/
@[simp]
theorem splitEvenDualBasis_inl (K : Type u) [CommRing K] (n : ℕ) (i : Fin n) :
    splitEvenDualBasis K n (Sum.inl i) = ((Pi.basisFun K (Fin n)).coord i, 0) := by
  simp [splitEvenDualBasis, Basis.prod_apply]

/-- The second half of the split basis consists of the standard coordinate axes. -/
@[simp]
theorem splitEvenDualBasis_inr (K : Type u) [CommRing K] (n : ℕ) (i : Fin n) :
    splitEvenDualBasis K n (Sum.inr i) = (0, Pi.single i 1) := by
  simp [splitEvenDualBasis, Basis.prod_apply, Pi.basisFun_apply]

/-- In the dual-coordinate and coordinate basis, the polar form of the standard split quadratic
form has Gram matrix `fromBlocks 0 1 1 0`. -/
theorem toMatrix_polarBilin_splitEvenForm (K : Type u) [CommRing K] (n : ℕ) :
    LinearMap.BilinForm.toMatrix (splitEvenDualBasis K n) (splitEvenForm K n).polarBilin =
      Matrix.fromBlocks 0 1 1 0 := by
  ext (i | i) (j | j) <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.one_apply, Pi.single_apply, eq_comm]

section BaseChange

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)

/-- The base change `(f, x) ↦ (f_S, x_S)` of a vector of the standard split space along an
algebra `R → S`: `f_S` is the functional whose coordinates `f_S eᵢ` are the images of `f eᵢ`, and
`x_S` is the coordinatewise image of `x`. -/
noncomputable def splitEvenSpaceBaseChange : SplitEvenSpace R n →ₗ[R] SplitEvenSpace S n where
  toFun m := (∑ i, algebraMap R S (m.1 (Pi.single i 1)) • LinearMap.proj i,
    fun i ↦ algebraMap R S (m.2 i))
  map_add' m m' := by
    refine Prod.ext (LinearMap.ext fun y ↦ ?_) (funext fun i ↦ ?_)
    · simp only [Prod.fst_add, LinearMap.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    · simp
  map_smul' c m := by
    refine Prod.ext (LinearMap.ext fun y ↦ ?_) (funext fun i ↦ ?_)
    · simp only [Prod.smul_fst, LinearMap.smul_apply, smul_eq_mul, map_mul, mul_smul,
        ← Finset.smul_sum, RingHom.id_apply, algebraMap_smul]
    · simp [Algebra.smul_def]

/-- The functional of a base-changed vector sends `y` to `∑ i, f eᵢ • yᵢ`. -/
theorem splitEvenSpaceBaseChange_fst_apply (m : SplitEvenSpace R n) (y : Fin n → S) :
    (splitEvenSpaceBaseChange R S n m).1 y = ∑ i, m.1 (Pi.single i 1) • y i := by
  simp only [splitEvenSpaceBaseChange, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, algebraMap_smul]

/-- The coordinates of the functional of a base-changed vector are the images of the coordinates
of the original functional. -/
@[simp]
theorem splitEvenSpaceBaseChange_fst_single (m : SplitEvenSpace R n) (i : Fin n) :
    (splitEvenSpaceBaseChange R S n m).1 (Pi.single i 1) =
      algebraMap R S (m.1 (Pi.single i 1)) := by
  rw [splitEvenSpaceBaseChange_fst_apply,
    Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp), Pi.single_eq_same,
    Algebra.algebraMap_eq_smul_one]

/-- The vector part of a base-changed vector is the coordinatewise image of the vector part. -/
@[simp]
theorem splitEvenSpaceBaseChange_snd (m : SplitEvenSpace R n) (i : Fin n) :
    (splitEvenSpaceBaseChange R S n m).2 i = algebraMap R S (m.2 i) :=
  (rfl)

/-- The split form of a base-changed vector is the image of the split form of the vector. -/
theorem splitEvenForm_splitEvenSpaceBaseChange (m : SplitEvenSpace R n) :
    splitEvenForm S n (splitEvenSpaceBaseChange R S n m) =
      algebraMap R S (splitEvenForm R n m) := by
  rw [splitEvenForm_apply, splitEvenForm_apply, splitEvenSpaceBaseChange_fst_apply]
  conv_rhs => rw [pi_eq_sum_univ' m.2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul, map_mul, splitEvenSpaceBaseChange_snd, Algebra.smul_def, mul_comm]

end BaseChange

variable (K : Type u) [Field K]

/-- The standard split space of `n` hyperbolic planes has dimension `2 * n`. -/
theorem finrank_splitEvenSpace (n : ℕ) : finrank K (SplitEvenSpace K n) = 2 * n := by
  simp [SplitEvenSpace, two_mul]

/-- The first isotropic summand in the standard split polarization has dimension `n`. -/
@[simp]
theorem finrank_splitEvenPolarization_W (n : ℕ) :
    finrank K (splitEvenPolarization K n).W = n := by
  rw [(splitEvenPolarization K n).finrank_W_eq_of_finrank_eq_two_mul
    (finrank_splitEvenSpace K n)]

/-- The first isotropic summand in a nonzero standard split polarization is nonzero. -/
theorem splitEvenPolarization_W_ne_bot {n : ℕ} (hn : n ≠ 0) :
    (splitEvenPolarization K n).W ≠ ⊥ :=
  Submodule.finrank_eq_zero.not.1 <| by
    simpa using hn

/-- The coordinate pairs `e_i = (0, δ_i)`, `f_i = (δ_i^*, 0)` form a family of mutually
orthogonal hyperbolic pairs for the standard split even form `(φ, x) ↦ φ x`. -/
theorem isHyperbolicFamily_splitEvenForm (K : Type u) [CommRing K] (n : ℕ) :
    QuadraticMap.IsHyperbolicFamily (splitEvenForm K n) (fun i => (0, Pi.single i 1))
      (fun i => (LinearMap.proj i, 0)) where
  left_isotropic _ := by simp
  right_isotropic _ := by simp
  polar_left_right _ := by simp
  polar_left_left _ _ _ := by simp
  polar_left_right_of_ne _ _ hij := by simp [Pi.single_eq_of_ne' hij]
  polar_right_right _ _ _ := by simp

end TauCeti
