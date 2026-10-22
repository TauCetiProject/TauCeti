/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.GeneralLinear
public import TauCeti.RepresentationTheory.Spin.Representation
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Center
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators
import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Spin groups of polarized six-dimensional quadratic spaces

Let `(V, Q)` be a six-dimensional quadratic space with a polarization `V = W ⊕ W'` into two
isotropic subspaces of dimension three, over a field of characteristic not two. The even Clifford
algebra acts on the even half `S⁺ = ⋀ᵉᵛᵉⁿ W` of the Fock module, a space of dimension four. This
file proves that this half-spin action identifies `Spin(Q)` with the special linear group of
`S⁺`:

* every Spin element acts on `S⁺` with determinant one;
* every endomorphism of `S⁺` of determinant one is the action of a Spin element.

In the matrix-product model of the even Clifford algebra of three hyperbolic planes,
`TauCeti.hyperbolicSixEvenUnitaryEquivGeneralLinear` identifies the reverse-unitary group
`U(C₀, σ)` with `GL₄(K)`. Under that identification `Spin(Q)` is exactly the determinant-one
subgroup, so `Spin(Q) ≅ SL₄(K)`. Over `ℚ` this is the split rational witness that the inclusion
`Spin(Q) ≤ U(C₀, σ)` is strict in dimension six, with `U(C₀, σ) ≅ GL₄(ℚ)` and `Spin(Q) ≅ SL₄(ℚ)`.

## The argument

Write `e₀, e₁, e₂` for a basis of `W`. The even half `S⁺` has basis `1, e₀e₁, e₀e₂, e₁e₂`. A vector
`v = w + w'` acts on the Fock module `⋀W` by `s ↦ w ∧ s + ⌊w'⌋ s`. Fix `v₀ = e₀ + f₀`, where `f₀`
is the vector of `W'` dual to `e₀`, so that `Q v₀ = 1`. The actions of `ι v₀ * ι v` and of
`ι v * ι v₀` on `S⁺` are explicit four-by-four matrices whose entries are the coordinates of `v`,
and each has determinant `(Q v) ^ 2`. Since `ι v₀ * ι v₀ = 1`, the action of `ι u * ι v` therefore
has determinant `(Q u) ^ 2 * (Q v) ^ 2`. Mathlib's Lipschitz group consists of products of vectors
(`CliffordAlgebra.mem_lipschitzGroup_iff_exists_list`), so a Spin element acts on `S⁺` with
determinant the square of its reverse norm, which is one.

Conversely, the canonical Spin lifts `1 + ι w * ι u` of the Eichler transvections, for `u` and
`w` among the basis vectors of `W` and `W'`, act on `S⁺` as the twelve elementary transvections in
the basis above. These generate the special linear group.

## Main results

* `TauCeti.det_spinPlusAction_spinGroupToEven`: a Spin element of a polarized six-dimensional
  space acts on the even half-spin module with determinant one.
* `TauCeti.exists_spinPlusAction_spinGroupToEven_eq_of_det_eq_one`: every determinant-one
  endomorphism of the even half-spin module is the action of a Spin element.
* `TauCeti.spinSixTransvectionLift`: a specified Spin lift of each elementary transvection,
  with its half-spin matrix and vector action computed explicitly.
* `TauCeti.mem_range_spinGroupToEvenUnitary_iff_det_hyperbolicSixEvenUnitaryEquivGeneralLinear`:
  for three hyperbolic planes, an even unitary element lies in Spin exactly when its image in
  `GL₄(K)` has determinant one.
* `TauCeti.hyperbolicSixSpinEquivSpecialLinear`: the Spin group of three hyperbolic planes is
  `SL₄(K)`, compatibly with `TauCeti.hyperbolicSixEvenUnitaryEquivGeneralLinear`; it specializes
  the polarized construction below.
* `TauCeti.spinGroupEquivSpecialLinearGroupOfFinrankEqSix`: the Spin-to-`SL₄` equivalence for a
  polarized six-dimensional quadratic space.
* `TauCeti.coe_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_apply`: its matrix formula in the
  basis `Module.finBasisOfFinrankEq` used by `Algebra.endAlgEquivMatrix`.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.D.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra Module

universe u v

/-! ### Coordinate data -/

section CoordinateData

variable {R : Type*} [CommRing R]

section Monomials

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The ordered even monomials `1, e₀e₁, e₀e₂, e₁e₂`. -/
noncomputable def _root_.Module.Basis.spinSixEvenMonomial (b : Basis (Fin 3) R M) :
    Fin 4 → ExteriorAlgebra R M :=
  ![1, ExteriorAlgebra.ι R (b 0) * ExteriorAlgebra.ι R (b 1),
    ExteriorAlgebra.ι R (b 0) * ExteriorAlgebra.ι R (b 2),
    ExteriorAlgebra.ι R (b 1) * ExteriorAlgebra.ι R (b 2)]

/-- Evaluation of the ordered even-monomial coordinates. -/
@[simp]
theorem _root_.Module.Basis.spinSixEvenMonomial_apply (b : Basis (Fin 3) R M) (j : Fin 4) :
    b.spinSixEvenMonomial j =
      ![1, ExteriorAlgebra.ι R (b 0) * ExteriorAlgebra.ι R (b 1),
        ExteriorAlgebra.ι R (b 0) * ExteriorAlgebra.ι R (b 2),
        ExteriorAlgebra.ι R (b 1) * ExteriorAlgebra.ι R (b 2)] j := by
  rw [Module.Basis.spinSixEvenMonomial]

end Monomials

section TransvectionVectors

variable {V : Type*} [AddCommGroup V] [Module R V] {Q : QuadraticForm R V}
  (P : SpinPolarizationData Q) (b : Basis (Fin 3) R P.W)

/-- The first vector of the Eichler-transvection lift of an elementary matrix transvection on
the even half-spin module. -/
noncomputable def spinSixTransvectionFirstVector (i j : Fin 4) : V :=
  !![(0 : V), (P.dualVector b 0 : V), (P.dualVector b 0 : V),
      (P.dualVector b 1 : V);
    (b 1 : V), 0, (b 1 : V), (b 0 : V);
    (b 2 : V), (b 2 : V), 0, (b 0 : V);
    (b 2 : V), (b 2 : V), (b 1 : V), 0] i j

/-- Evaluation of the first vector of an elementary Spin-six transvection lift. -/
theorem spinSixTransvectionFirstVector_apply (i j : Fin 4) :
    spinSixTransvectionFirstVector P b i j =
      !![(0 : V), (P.dualVector b 0 : V), (P.dualVector b 0 : V),
          (P.dualVector b 1 : V);
        (b 1 : V), 0, (b 1 : V), (b 0 : V);
        (b 2 : V), (b 2 : V), 0, (b 0 : V);
        (b 2 : V), (b 2 : V), (b 1 : V), 0] i j := by
  rw [spinSixTransvectionFirstVector]

/-- The second vector of the Eichler-transvection lift of an elementary matrix transvection on
the even half-spin module. -/
noncomputable def spinSixTransvectionSecondVector (i j : Fin 4) (c : R) : V :=
  !![(0 : V), ((c • P.dualVector b 1 : P.W') : V),
      ((c • P.dualVector b 2 : P.W') : V), ((c • P.dualVector b 2 : P.W') : V);
    ((c • b 0 : P.W) : V), 0, (((-c) • P.dualVector b 2 : P.W') : V),
      ((c • P.dualVector b 2 : P.W') : V);
    ((c • b 0 : P.W) : V), (((-c) • P.dualVector b 1 : P.W') : V), 0,
      (((-c) • P.dualVector b 1 : P.W') : V);
    ((c • b 1 : P.W) : V), ((c • P.dualVector b 0 : P.W') : V),
      (((-c) • P.dualVector b 0 : P.W') : V), 0] i j

/-- Evaluation of the second vector of an elementary Spin-six transvection lift. -/
theorem spinSixTransvectionSecondVector_apply (i j : Fin 4) (c : R) :
    spinSixTransvectionSecondVector P b i j c =
      !![(0 : V), ((c • P.dualVector b 1 : P.W') : V),
          ((c • P.dualVector b 2 : P.W') : V), ((c • P.dualVector b 2 : P.W') : V);
        ((c • b 0 : P.W) : V), 0, (((-c) • P.dualVector b 2 : P.W') : V),
          ((c • P.dualVector b 2 : P.W') : V);
        ((c • b 0 : P.W) : V), (((-c) • P.dualVector b 1 : P.W') : V), 0,
          (((-c) • P.dualVector b 1 : P.W') : V);
        ((c • b 1 : P.W) : V), ((c • P.dualVector b 0 : P.W') : V),
          (((-c) • P.dualVector b 0 : P.W') : V), 0] i j := by
  rw [spinSixTransvectionSecondVector]

/-- The second vector of an elementary Spin-six transvection lift vanishes at parameter zero. -/
@[simp]
theorem spinSixTransvectionSecondVector_zero (i j : Fin 4) :
    spinSixTransvectionSecondVector P b i j 0 = 0 := by
  fin_cases i <;> fin_cases j <;> simp [spinSixTransvectionSecondVector_apply]

end TransvectionVectors

end CoordinateData

variable {K : Type*} [Field K]

/-! ### Two vector actions on the even half of a three-generator exterior algebra -/

section FockModel

variable {M : Type*} [AddCommGroup M] [Module K M] (b : Basis (Fin 3) K M)

/-- The action `s ↦ x ∧ s + ⌊d⌋ s` of a vector on a Fock module, with creation part `x` and
annihilation part `d`. -/
private noncomputable def fockAction (x : M) (d : Dual K M) (s : ExteriorAlgebra K M) :
    ExteriorAlgebra K M :=
  ExteriorAlgebra.ι K x * s + contractLeft d s

/-- Every pair of vectors is orthogonal for the zero form, so exterior generators anticommute. -/
private theorem isOrtho_zero (x y : M) : (0 : QuadraticForm K M).IsOrtho x y := by
  simp [QuadraticMap.isOrtho_def]

private theorem ι_mul_ι_mul_self (x : M) (t : ExteriorAlgebra K M) :
    ExteriorAlgebra.ι K x * (ExteriorAlgebra.ι K x * t) = 0 := by
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

private theorem ι_eq_sum (x : M) :
    ExteriorAlgebra.ι K x = ∑ i, b.repr x i • ExteriorAlgebra.ι K (b i) := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  simp only [map_smul]

private theorem apply_eq_sum (x : M) (d : Dual K M) :
    d x = b.repr x 0 * d (b 0) + b.repr x 1 * d (b 1) + b.repr x 2 * d (b 2) := by
  calc d x = d (∑ i, b.repr x i • b i) := by rw [b.sum_repr]
    _ = _ := by rw [map_sum, Fin.sum_univ_three]; simp only [map_smul, smul_eq_mul]

/-! The generators anticommute; these instances put products in increasing order. -/

private theorem ι_one_mul_ι_zero_mul (t : ExteriorAlgebra K M) :
    ExteriorAlgebra.ι K (b 1) * (ExteriorAlgebra.ι K (b 0) * t) =
      -(ExteriorAlgebra.ι K (b 0) * (ExteriorAlgebra.ι K (b 1) * t)) :=
  ι_mul_ι_mul_of_isOrtho t (isOrtho_zero _ _)

private theorem ι_two_mul_ι_zero_mul (t : ExteriorAlgebra K M) :
    ExteriorAlgebra.ι K (b 2) * (ExteriorAlgebra.ι K (b 0) * t) =
      -(ExteriorAlgebra.ι K (b 0) * (ExteriorAlgebra.ι K (b 2) * t)) :=
  ι_mul_ι_mul_of_isOrtho t (isOrtho_zero _ _)

private theorem ι_two_mul_ι_one_mul (t : ExteriorAlgebra K M) :
    ExteriorAlgebra.ι K (b 2) * (ExteriorAlgebra.ι K (b 1) * t) =
      -(ExteriorAlgebra.ι K (b 1) * (ExteriorAlgebra.ι K (b 2) * t)) :=
  ι_mul_ι_mul_of_isOrtho t (isOrtho_zero _ _)

private theorem ι_one_mul_ι_zero :
    ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 0) =
      -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_zero _ _)

private theorem ι_two_mul_ι_zero :
    ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 0) =
      -(ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_zero _ _)

private theorem ι_two_mul_ι_one :
    ExteriorAlgebra.ι K (b 2) * ExteriorAlgebra.ι K (b 1) =
      -(ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)) :=
  ι_mul_ι_comm_of_isOrtho (isOrtho_zero _ _)

section Table

/- With these rewrites `simp` expands an action on a monomial into a combination of the ordered
monomials, which `module` then compares. -/
attribute [local simp] add_mul mul_add mul_sub sub_mul mul_assoc smul_mul_assoc mul_smul_comm
  ι_mul_ι_mul_self ExteriorAlgebra.ι_sq_zero contractLeft_ι_mul contractLeft_ι
  ι_one_mul_ι_zero_mul ι_two_mul_ι_zero_mul ι_two_mul_ι_one_mul ι_one_mul_ι_zero
  ι_two_mul_ι_zero ι_two_mul_ι_one Basis.coord_apply Basis.repr_self Finsupp.single_apply
  Algebra.algebraMap_eq_smul_one

/-! The four columns of the action of `v₀ = e₀ + f₀` after a vector with parts `x` and `d`. -/

private theorem fockAction_base_fockAction_one (x : M) (d : Dual K M) :
    fockAction (b 0) (b.coord 0) (fockAction x d 1) =
      b.repr x 0 • 1 + b.repr x 1 • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) +
        b.repr x 2 • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)) := by
  simp only [fockAction, ι_eq_sum b x, Fin.sum_univ_three]
  simp
  module

private theorem fockAction_base_fockAction_zero_one (x : M) (d : Dual K M) :
    fockAction (b 0) (b.coord 0)
        (fockAction x d (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1))) =
      -d (b 1) • 1 + d (b 0) • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) +
        b.repr x 2 • (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)) := by
  simp only [fockAction, ι_eq_sum b x, Fin.sum_univ_three]
  simp
  module

private theorem fockAction_base_fockAction_zero_two (x : M) (d : Dual K M) :
    fockAction (b 0) (b.coord 0)
        (fockAction x d (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2))) =
      -d (b 2) • 1 + d (b 0) • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)) -
        b.repr x 1 • (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)) := by
  simp only [fockAction, ι_eq_sum b x, Fin.sum_univ_three]
  simp
  module

private theorem fockAction_base_fockAction_one_two (x : M) (d : Dual K M) :
    fockAction (b 0) (b.coord 0)
        (fockAction x d (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2))) =
      -d (b 2) • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) +
        d (b 1) • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)) +
          b.repr x 0 • (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)) := by
  simp only [fockAction, ι_eq_sum b x, Fin.sum_univ_three]
  simp
  module

/-! The four columns of the action of a vector with parts `x` and `d` after `v₀ = e₀ + f₀`. -/

private theorem fockAction_fockAction_base_one (x : M) (d : Dual K M) :
    fockAction x d (fockAction (b 0) (b.coord 0) 1) =
      d (b 0) • 1 - b.repr x 1 • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) -
        b.repr x 2 • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)) := by
  simp only [fockAction, ι_eq_sum b x, Fin.sum_univ_three]
  simp
  module

private theorem fockAction_fockAction_base_zero_one (x : M) (d : Dual K M) :
    fockAction x d
        (fockAction (b 0) (b.coord 0) (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1))) =
      d (b 1) • 1 + b.repr x 0 • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) -
        b.repr x 2 • (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)) := by
  simp only [fockAction, ι_eq_sum b x, Fin.sum_univ_three]
  simp
  module

private theorem fockAction_fockAction_base_zero_two (x : M) (d : Dual K M) :
    fockAction x d
        (fockAction (b 0) (b.coord 0) (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2))) =
      d (b 2) • 1 + b.repr x 0 • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)) +
        b.repr x 1 • (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)) := by
  simp only [fockAction, ι_eq_sum b x, Fin.sum_univ_three]
  simp
  module

private theorem fockAction_fockAction_base_one_two (x : M) (d : Dual K M) :
    fockAction x d
        (fockAction (b 0) (b.coord 0) (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2))) =
      d (b 2) • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1)) -
        d (b 1) • (ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2)) +
          d (b 0) • (ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)) := by
  simp only [fockAction, ι_eq_sum b x, Fin.sum_univ_three]
  simp
  module

end Table

/-! ### The even half and its monomial basis -/

private theorem basis_empty_eq_one : b.ExteriorAlgebra ∅ = 1 := by
  rw [ExteriorAlgebra.basis_apply]
  simp only [ExteriorAlgebra.ιMulti_family]
  exact ExteriorAlgebra.ιMulti_zero_apply _

private theorem evenMonomial_eq :
    b.spinSixEvenMonomial = b.ExteriorAlgebra ∘ ![∅, {0, 1}, {0, 2}, {1, 2}] := by
  ext j
  fin_cases j
  · simp [Module.Basis.spinSixEvenMonomial, basis_empty_eq_one]
  · simp [Module.Basis.spinSixEvenMonomial,
      ExteriorAlgebra.basis_pair b (show (0 : Fin 3) < 1 by decide)]
  · simp [Module.Basis.spinSixEvenMonomial,
      ExteriorAlgebra.basis_pair b (show (0 : Fin 3) < 2 by decide)]
  · simp [Module.Basis.spinSixEvenMonomial,
      ExteriorAlgebra.basis_pair b (show (1 : Fin 3) < 2 by decide)]

private theorem evenMonomial_mem (j : Fin 4) :
    b.spinSixEvenMonomial j ∈ evenOdd (0 : QuadraticForm K M) 0 := by
  fin_cases j
  · simpa [Module.Basis.spinSixEvenMonomial] using
      SetLike.one_mem_graded (evenOdd (0 : QuadraticForm K M))
  all_goals exact ι_mul_ι_mem_evenOdd_zero _ _ _

private theorem linearIndependent_evenMonomial : LinearIndependent K b.spinSixEvenMonomial := by
  rw [evenMonomial_eq]
  exact b.ExteriorAlgebra.linearIndependent.comp _ (by decide)

include b in
private theorem finrank_evenOdd_zero_eq_four :
    finrank K (evenOdd (0 : QuadraticForm K M) 0) = 4 := by
  have : Nontrivial M := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
  have : Module.Finite K M := Module.Finite.of_basis b
  rw [finrank_evenOdd_zero, finrank_eq_card_basis b]
  simp

variable {N : Submodule K (ExteriorAlgebra K M)} (hN : N = evenOdd (0 : QuadraticForm K M) 0)

/-- The basis `1, e₀e₁, e₀e₂, e₁e₂` of the even half. -/
noncomputable def _root_.Module.Basis.spinSixEvenMonomialBasis : Basis (Fin 4) K N :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun j ↦ (⟨b.spinSixEvenMonomial j, hN ▸ evenMonomial_mem b j⟩ : N))
    (LinearIndependent.of_comp N.subtype (linearIndependent_evenMonomial b))
    (by rw [hN, finrank_evenOdd_zero_eq_four b]; rfl)

/-- The even-monomial basis has the prescribed exterior-algebra representatives. -/
@[simp]
theorem _root_.Module.Basis.coe_spinSixEvenMonomialBasis (j : Fin 4) :
    (b.spinSixEvenMonomialBasis hN j : ExteriorAlgebra K M) = b.spinSixEvenMonomial j := by
  simp [Module.Basis.spinSixEvenMonomialBasis]

/-- The matrix of the action of `v₀ = e₀ + f₀` after a vector with coordinates `X` in `W` and
`C` in `W'`. -/
private def baseAfterMatrix (X C : Fin 3 → K) : Matrix (Fin 4) (Fin 4) K :=
  !![X 0, -C 1, -C 2, 0;
     X 1, C 0, 0, -C 2;
     X 2, 0, C 0, C 1;
     0, X 2, -X 1, X 0]

/-- The matrix of the action of a vector with coordinates `X` in `W` and `C` in `W'` after
`v₀ = e₀ + f₀`. -/
private def baseBeforeMatrix (X C : Fin 3 → K) : Matrix (Fin 4) (Fin 4) K :=
  !![C 0, C 1, C 2, 0;
     -X 1, X 0, 0, C 2;
     -X 2, 0, X 0, -C 1;
     0, -X 2, X 1, C 0]

private theorem det_baseAfterMatrix (X C : Fin 3 → K) :
    (baseAfterMatrix X C).det = (X 0 * C 0 + X 1 * C 1 + X 2 * C 2) ^ 2 := by
  rw [baseAfterMatrix, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

private theorem det_baseBeforeMatrix (X C : Fin 3 → K) :
    (baseBeforeMatrix X C).det = (X 0 * C 0 + X 1 * C 1 + X 2 * C 2) ^ 2 := by
  rw [baseBeforeMatrix, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

private theorem toMatrix_eq_baseAfterMatrix (x : M) (d : Dual K M) (f : Module.End K N)
    (hf : ∀ s, (f s : ExteriorAlgebra K M) = fockAction (b 0) (b.coord 0) (fockAction x d s)) :
    LinearMap.toMatrix (b.spinSixEvenMonomialBasis hN) (b.spinSixEvenMonomialBasis hN) f =
      baseAfterMatrix (b.repr x) (fun i ↦ d (b i)) := by
  rw [← LinearMap.toMatrix_toLin (b.spinSixEvenMonomialBasis hN) (b.spinSixEvenMonomialBasis hN)
    (baseAfterMatrix _ _)]
  congr 1
  refine (b.spinSixEvenMonomialBasis hN).ext fun j ↦ Subtype.ext ?_
  rw [hf, Matrix.toLin_self, Submodule.coe_sum]
  simp only [Submodule.coe_smul, Module.Basis.coe_spinSixEvenMonomialBasis,
    Fin.sum_univ_four]
  fin_cases j
  · simp [Module.Basis.spinSixEvenMonomial, baseAfterMatrix, fockAction_base_fockAction_one]
  · simp [Module.Basis.spinSixEvenMonomial, baseAfterMatrix, fockAction_base_fockAction_zero_one]
  · simp [Module.Basis.spinSixEvenMonomial, baseAfterMatrix, fockAction_base_fockAction_zero_two]
    module
  · simp [Module.Basis.spinSixEvenMonomial, baseAfterMatrix, fockAction_base_fockAction_one_two]

private theorem toMatrix_eq_baseBeforeMatrix (x : M) (d : Dual K M) (f : Module.End K N)
    (hf : ∀ s, (f s : ExteriorAlgebra K M) = fockAction x d (fockAction (b 0) (b.coord 0) s)) :
    LinearMap.toMatrix (b.spinSixEvenMonomialBasis hN) (b.spinSixEvenMonomialBasis hN) f =
      baseBeforeMatrix (b.repr x) (fun i ↦ d (b i)) := by
  rw [← LinearMap.toMatrix_toLin (b.spinSixEvenMonomialBasis hN) (b.spinSixEvenMonomialBasis hN)
    (baseBeforeMatrix _ _)]
  congr 1
  refine (b.spinSixEvenMonomialBasis hN).ext fun j ↦ Subtype.ext ?_
  rw [hf, Matrix.toLin_self, Submodule.coe_sum]
  simp only [Submodule.coe_smul, Module.Basis.coe_spinSixEvenMonomialBasis,
    Fin.sum_univ_four]
  fin_cases j
  · simp [Module.Basis.spinSixEvenMonomial, baseBeforeMatrix, fockAction_fockAction_base_one]
    module
  · simp [Module.Basis.spinSixEvenMonomial, baseBeforeMatrix,
      fockAction_fockAction_base_zero_one]
    module
  · simp [Module.Basis.spinSixEvenMonomial, baseBeforeMatrix,
      fockAction_fockAction_base_zero_two]
  · simp [Module.Basis.spinSixEvenMonomial, baseBeforeMatrix, fockAction_fockAction_base_one_two]
    module

end FockModel

/-! ### The half-spin action of a polarized six-dimensional space -/

section Polarization

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  (P : SpinPolarizationData Q) (hline : P.line = ⊥)

/-- The component of a vector in the isotropic summand `W`. -/
private noncomputable def creationPart (v : V) : P.W := (P.decompositionEquiv.symm v).1.1

/-- The functional on `W` given by the component of a vector in `W'`. -/
private noncomputable def annihilationPart (v : V) : Dual K P.W :=
  P.pairingEquiv (P.decompositionEquiv.symm v).1.2

include hline in
private theorem creationPart_add (v : V) :
    (creationPart P v : V) + ((P.decompositionEquiv.symm v).1.2 : V) = v := by
  have h := P.decompositionEquiv_apply (P.decompositionEquiv.symm v)
  rw [P.decompositionEquiv.apply_symm_apply] at h
  have hz : ((P.decompositionEquiv.symm v).2 : V) = 0 := by
    have hmem : ((P.decompositionEquiv.symm v).2 : V) ∈ (⊥ : Submodule K V) :=
      hline ▸ (P.decompositionEquiv.symm v).2.2
    simpa using hmem
  rw [hz, add_zero] at h
  exact h.symm

include hline in
private theorem spinAction_ι_eq_fockAction (v : V) (s : ExteriorAlgebra K P.W) :
    spinAction Q P (ι Q v) s = fockAction (creationPart P v) (annihilationPart P v) s := by
  conv_lhs => rw [← creationPart_add P hline v]
  rw [map_add, map_add, LinearMap.add_apply, spinAction_ι_wedge, spinAction_ι_contract]
  -- Both sides are the defining formula of `fockAction` on the two polarization components.
  rfl

include hline in
private theorem annihilationPart_creationPart (v : V) :
    annihilationPart P v (creationPart P v) = Q v := by
  have h := P.quadraticForm_coe_add_coe_add_coe (creationPart P v)
    (P.decompositionEquiv.symm v).1.2 0
  rw [Submodule.coe_zero, add_zero, creationPart_add P hline, QuadraticMap.map_zero,
    add_zero] at h
  rw [h, annihilationPart, P.pairingEquiv_apply]

private theorem creationPart_coe_W (x : P.W) : creationPart P (x : V) = x := by
  simp [creationPart]

private theorem annihilationPart_coe_W (x : P.W) : annihilationPart P (x : V) = 0 := by
  simp [annihilationPart]

private theorem creationPart_coe_W' (y : P.W') : creationPart P (y : V) = 0 := by
  simp [creationPart]

private theorem annihilationPart_coe_W' (y : P.W') :
    annihilationPart P (y : V) = P.pairingEquiv y := by
  simp [annihilationPart]

@[simp]
private theorem creationPart_smul (c : K) (v : V) :
    creationPart P (c • v) = c • creationPart P v := by
  simp [creationPart]

@[simp]
private theorem annihilationPart_smul (c : K) (v : V) :
    annihilationPart P (c • v) = c • annihilationPart P v := by
  simp [annihilationPart]

@[simp]
private theorem creationPart_neg (v : V) : creationPart P (-v) = -creationPart P v := by
  simp [creationPart]

@[simp]
private theorem annihilationPart_neg (v : V) :
    annihilationPart P (-v) = -annihilationPart P v := by
  simp [annihilationPart]

variable (Q) in
/-- The even Clifford element `ι u * ι v`. -/
private def vectorPair (u v : V) : even Q :=
  ⟨ι Q u * ι Q v, by
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]
    exact ι_mul_ι_mem_evenOdd_zero Q u v⟩

private theorem coe_vectorPair (u v : V) :
    (vectorPair Q u v : CliffordAlgebra Q) = ι Q u * ι Q v := (rfl)

variable (b : Basis (Fin 3) K P.W)

/-- The vector `v₀ = e₀ + f₀`, of norm one. -/
private noncomputable def baseVector : V := (b 0 : V) + (P.dualVector b 0 : V)

private theorem creationPart_baseVector : creationPart P (baseVector P b) = b 0 := by
  simp [baseVector, creationPart]

private theorem annihilationPart_baseVector :
    annihilationPart P (baseVector P b) = b.coord 0 := by
  simp [baseVector, annihilationPart]

include hline in
private theorem quadraticForm_baseVector : Q (baseVector P b) = 1 := by
  rw [← annihilationPart_creationPart P hline, creationPart_baseVector,
    annihilationPart_baseVector]
  simp

include hline in
private theorem vectorPair_eq_mul (u v : V) :
    vectorPair Q u v = vectorPair Q u (baseVector P b) * vectorPair Q (baseVector P b) v := by
  apply Subtype.ext
  simp only [coe_vectorPair, Subalgebra.coe_mul]
  rw [mul_assoc, ← mul_assoc (ι Q (baseVector P b)), ι_sq_scalar,
    quadraticForm_baseVector P hline, map_one, one_mul]

include hline in
private theorem toMatrix_vectorPair_baseVector_left (v : V) :
    LinearMap.toMatrix (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (spinPlusAction Q P hline (vectorPair Q (baseVector P b) v)) =
      baseAfterMatrix (b.repr (creationPart P v)) (fun i ↦ annihilationPart P v (b i)) := by
  refine toMatrix_eq_baseAfterMatrix b (spinPlus_def P) _ _ _ fun s ↦ ?_
  rw [coe_spinPlusAction_apply, coe_vectorPair, map_mul, Module.End.mul_apply,
    spinAction_ι_eq_fockAction P hline, spinAction_ι_eq_fockAction P hline,
    creationPart_baseVector, annihilationPart_baseVector]

include hline in
private theorem toMatrix_vectorPair_baseVector_right (v : V) :
    LinearMap.toMatrix (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (spinPlusAction Q P hline (vectorPair Q v (baseVector P b))) =
      baseBeforeMatrix (b.repr (creationPart P v)) (fun i ↦ annihilationPart P v (b i)) := by
  refine toMatrix_eq_baseBeforeMatrix b (spinPlus_def P) _ _ _ fun s ↦ ?_
  rw [coe_spinPlusAction_apply, coe_vectorPair, map_mul, Module.End.mul_apply,
    spinAction_ι_eq_fockAction P hline, spinAction_ι_eq_fockAction P hline,
    creationPart_baseVector, annihilationPart_baseVector]

include hline b in
/-- **The half-spin determinant of a product of two vectors**: `ι u * ι v` acts on `S⁺` with
determinant `(Q u) ^ 2 * (Q v) ^ 2`. -/
private theorem det_spinPlusAction_vectorPair (u v : V) :
    LinearMap.det (spinPlusAction Q P hline (vectorPair Q u v)) = Q u ^ 2 * Q v ^ 2 := by
  rw [vectorPair_eq_mul P hline b, map_mul, map_mul LinearMap.det,
    ← LinearMap.det_toMatrix (b.spinSixEvenMonomialBasis (spinPlus_def P)),
    ← LinearMap.det_toMatrix (b.spinSixEvenMonomialBasis (spinPlus_def P)),
    toMatrix_vectorPair_baseVector_left P hline, toMatrix_vectorPair_baseVector_right P hline,
    det_baseAfterMatrix, det_baseBeforeMatrix, ← annihilationPart_creationPart P hline u,
    ← annihilationPart_creationPart P hline v, apply_eq_sum b (creationPart P u),
    apply_eq_sum b (creationPart P v)]

variable (Q) in
/-- A product of an even number of vectors, as an even Clifford element. -/
private def evenVectorProduct (l : List V) (hl : Even l.length) : even Q :=
  ⟨(l.map (ι Q)).prod, prod_map_ι_mem_even_of_even_length hl⟩

include hline b in
private theorem det_spinPlusAction_evenVectorProduct (n : ℕ) :
    ∀ (l : List V) (hl : l.length = 2 * n),
      LinearMap.det (spinPlusAction Q P hline (evenVectorProduct Q l ⟨n, by omega⟩)) =
        (l.map Q).prod ^ 2 := by
  induction n with
  | zero =>
    intro l hl
    obtain rfl : l = [] := List.length_eq_zero_iff.mp (by omega)
    have h1 : evenVectorProduct Q [] ⟨0, rfl⟩ = 1 := Subtype.ext (by simp [evenVectorProduct])
    simp [h1]
  | succ n ih =>
    intro l hl
    match l, hl with
    | a :: c :: l', hl =>
      have h' : l'.length = 2 * n := by simp at hl; omega
      have heq : evenVectorProduct Q (a :: c :: l') ⟨n + 1, by omega⟩ =
          vectorPair Q a c * evenVectorProduct Q l' ⟨n, by omega⟩ :=
        Subtype.ext (by simp [evenVectorProduct, coe_vectorPair, mul_assoc])
      rw [heq, map_mul, map_mul LinearMap.det, det_spinPlusAction_vectorPair P hline b,
        ih l' h']
      simp only [List.map_cons, List.prod_cons]
      ring

variable [Invertible (2 : K)]

include hline b in
private theorem det_spinPlusAction_spinGroupToEven_of_basis (s : spinGroup Q) :
    LinearMap.det (spinPlusAction Q P hline (spinGroupToEven Q s)) = 1 := by
  have hcoe : ((spinGroup.toUnits s : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = s := rfl
  obtain ⟨l, -, hl⟩ := mem_lipschitzGroup_iff_exists_list.mp
    (spinGroup.units_mem_lipschitzGroup (x := spinGroup.toUnits s) (hcoe ▸ s.2))
  rw [hcoe] at hl
  have hseven : (s : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]
    exact (spinGroup.mem_iff.mp s.2).2
  have hstar : star (s : CliffordAlgebra Q) * s = 1 :=
    congrArg Subtype.val (spinGroup.star_mul_self s)
  -- A Spin element is even and nonzero, so it is a product of an even number of vectors.
  have hlen : Even l.length := by
    by_contra hodd
    have hsodd : (s : CliffordAlgebra Q) ∈ evenOdd Q 1 := by
      rw [hl, ← (ZMod.natCast_eq_one_iff_odd).mpr (Nat.not_even_iff_odd.mp hodd)]
      exact prod_map_ι_mem_evenOdd l
    have hzero : (s : CliffordAlgebra Q) = 0 := by
      simpa using (evenOdd_isCompl Q).disjoint.le_bot ⟨hseven, hsodd⟩
    rw [hzero, mul_zero] at hstar
    simp at hstar
  obtain ⟨n, hn⟩ := hlen
  have heq : spinGroupToEven Q s = evenVectorProduct Q l ⟨n, hn⟩ :=
    Subtype.ext (by simp [evenVectorProduct, hl])
  -- Its reverse norm is the product of the norms of the vectors, and Spin elements have norm one.
  have hnorm : (l.map Q).prod = 1 := by
    rw [star_mul_self_eq_reverse_mul_self_of_mem_even hseven, hl,
      reverse_prod_map_ι_mul_prod_map_ι] at hstar
    exact algebraMap_injective Q (by simpa using hstar)
  rw [heq, det_spinPlusAction_evenVectorProduct P hline b n l (by omega), hnorm, one_pow]

/-- **Spin acts on the even half-spin module with determinant one.** For a polarization of a
six-dimensional quadratic space, every element of `Spin(Q)` acts on `S⁺ = ⋀ᵉᵛᵉⁿ W` by an
endomorphism of determinant one. -/
theorem det_spinPlusAction_spinGroupToEven (hW : finrank K P.W = 3) (s : spinGroup Q) :
    LinearMap.det (spinPlusAction Q P hline (spinGroupToEven Q s)) = 1 :=
  have : Module.Finite K P.W := Module.finite_of_finrank_pos (by omega)
  det_spinPlusAction_spinGroupToEven_of_basis P hline (finBasisOfFinrankEq K P.W hW) s

/-! ### The Spin lifts of the elementary transvections -/

omit [Invertible (2 : K)] in
private theorem polar_basis_dualVector {a a' : Fin 3} (h : a ≠ a') (c : K) :
    QuadraticMap.polar Q (b a : V) ((c • P.dualVector b a' : P.W') : V) = 0 := by
  rw [← P.pairingEquiv_apply]
  simp [h]

include hline in
private theorem toMatrix_spinTransvection {u w : V} (hQ : Q.Nondegenerate) (hu : Q u = 0)
    (huw : QuadraticMap.polar Q u w = 0) :
    LinearMap.toMatrix (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q (spinTransvection hQ hu huw))) =
      1 + baseBeforeMatrix (b.repr (creationPart P w)) (fun i ↦ annihilationPart P w (b i)) *
        baseAfterMatrix (b.repr (creationPart P u)) (fun i ↦ annihilationPart P u (b i)) := by
  have heven : spinGroupToEven Q (spinTransvection hQ hu huw) = 1 + vectorPair Q w u :=
    Subtype.ext (by simp [coe_vectorPair])
  rw [heven, map_add, map_one, map_add, LinearMap.toMatrix_one, vectorPair_eq_mul P hline b,
    map_mul, LinearMap.toMatrix_mul, toMatrix_vectorPair_baseVector_right P hline,
    toMatrix_vectorPair_baseVector_left P hline]

section Transvections

attribute [local simp] baseAfterMatrix baseBeforeMatrix Matrix.transvection Matrix.one_apply
  Matrix.single_apply Finsupp.single_apply

/-! Creation pairs `ι (c • e_a') * ι e_a` move the vacuum `1` to `e_a' ∧ e_a`; annihilation pairs
move `e_a ∧ e_a'` back to `1`; mixed pairs exchange two of `e₀e₁, e₀e₂, e₁e₂`. -/

omit [Invertible (2 : K)] in
private theorem spinSixTransvectionFirstVector_isotropic {i j : Fin 4} (hij : i ≠ j) :
    Q (spinSixTransvectionFirstVector P b i j) = 0 := by
  fin_cases i <;> fin_cases j
  all_goals try { exact (hij rfl).elim }
  all_goals
    simp [spinSixTransvectionFirstVector, P.isotropic_W, P.isotropic_W']

omit [Invertible (2 : K)] in
private theorem spinSixTransvectionVectors_polar {i j : Fin 4} (hij : i ≠ j) (c : K) :
    QuadraticMap.polar Q (spinSixTransvectionFirstVector P b i j)
      (spinSixTransvectionSecondVector P b i j c) = 0 := by
  fin_cases i <;> fin_cases j
  all_goals try { exact (hij rfl).elim }
  all_goals
    simp [spinSixTransvectionFirstVector, spinSixTransvectionSecondVector,
      P.polar_W_eq_zero, P.polar_W'_eq_zero]

omit [Invertible (2 : K)] in
/-- The canonical Spin lift of an elementary transvection on the even half-spin module of a
polarized six-dimensional quadratic space. -/
noncomputable def spinSixTransvectionLift {i j : Fin 4} (hij : i ≠ j) (c : K) : spinGroup Q :=
  spinTransvection (P.nondegenerate_of_line_eq_bot hline)
    (spinSixTransvectionFirstVector_isotropic P b hij)
    (spinSixTransvectionVectors_polar P b hij c)

/-- The canonical lift of an elementary transvection with parameter zero is the identity. -/
@[simp]
theorem spinSixTransvectionLift_zero {i j : Fin 4} (hij : i ≠ j) :
    spinSixTransvectionLift P hline b hij 0 = 1 := by
  rw [spinSixTransvectionLift]
  apply spinTransvection_eq_one_of_mem_span
  rw [spinSixTransvectionSecondVector_zero]
  exact Submodule.zero_mem _

private abbrev SpinSixLiftHasMatrix (i j : Fin 4) (hij : i ≠ j) (c : K) : Prop :=
    LinearMap.toMatrix (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q
          (spinSixTransvectionLift P hline b hij c))) = Matrix.transvection i j c

local macro "prove_spinSixLiftHasMatrixW" : tactic => `(tactic|
  (unfold SpinSixLiftHasMatrix
   rw [spinSixTransvectionLift, toMatrix_spinTransvection]
   ext k l
   fin_cases k <;> fin_cases l <;>
     simp [spinSixTransvectionFirstVector, spinSixTransvectionSecondVector,
       creationPart_coe_W, annihilationPart_coe_W]))

local macro "prove_spinSixLiftHasMatrixW'" : tactic => `(tactic|
  (unfold SpinSixLiftHasMatrix
   rw [spinSixTransvectionLift, toMatrix_spinTransvection]
   ext k l
   fin_cases k <;> fin_cases l <;>
     simp [spinSixTransvectionFirstVector, spinSixTransvectionSecondVector,
       creationPart_coe_W', annihilationPart_coe_W']))

local macro "prove_spinSixLiftHasMatrixMixed" : tactic => `(tactic|
  (unfold SpinSixLiftHasMatrix
   rw [spinSixTransvectionLift, toMatrix_spinTransvection]
   ext k l
   fin_cases k <;> fin_cases l <;>
     simp [spinSixTransvectionFirstVector, spinSixTransvectionSecondVector,
       creationPart_coe_W, annihilationPart_coe_W, creationPart_coe_W',
       annihilationPart_coe_W']))

include hline in
private theorem spinSixLiftHasMatrix_zero_one (c : K) :
    SpinSixLiftHasMatrix P hline b 0 1 (by decide) c := by
  prove_spinSixLiftHasMatrixW'

include hline in
private theorem spinSixLiftHasMatrix_zero_two (c : K) :
    SpinSixLiftHasMatrix P hline b 0 2 (by decide) c := by
  prove_spinSixLiftHasMatrixW'

include hline in
private theorem spinSixLiftHasMatrix_zero_three (c : K) :
    SpinSixLiftHasMatrix P hline b 0 3 (by decide) c := by
  prove_spinSixLiftHasMatrixW'

include hline in
private theorem spinSixLiftHasMatrix_one_zero (c : K) :
    SpinSixLiftHasMatrix P hline b 1 0 (by decide) c := by
  prove_spinSixLiftHasMatrixW

include hline in
private theorem spinSixLiftHasMatrix_one_two (c : K) :
    SpinSixLiftHasMatrix P hline b 1 2 (by decide) c := by
  prove_spinSixLiftHasMatrixMixed

include hline in
private theorem spinSixLiftHasMatrix_one_three (c : K) :
    SpinSixLiftHasMatrix P hline b 1 3 (by decide) c := by
  prove_spinSixLiftHasMatrixMixed

include hline in
private theorem spinSixLiftHasMatrix_two_zero (c : K) :
    SpinSixLiftHasMatrix P hline b 2 0 (by decide) c := by
  prove_spinSixLiftHasMatrixW

include hline in
private theorem spinSixLiftHasMatrix_two_one (c : K) :
    SpinSixLiftHasMatrix P hline b 2 1 (by decide) c := by
  prove_spinSixLiftHasMatrixMixed

include hline in
private theorem spinSixLiftHasMatrix_two_three (c : K) :
    SpinSixLiftHasMatrix P hline b 2 3 (by decide) c := by
  prove_spinSixLiftHasMatrixMixed

include hline in
private theorem spinSixLiftHasMatrix_three_zero (c : K) :
    SpinSixLiftHasMatrix P hline b 3 0 (by decide) c := by
  prove_spinSixLiftHasMatrixW

include hline in
private theorem spinSixLiftHasMatrix_three_one (c : K) :
    SpinSixLiftHasMatrix P hline b 3 1 (by decide) c := by
  prove_spinSixLiftHasMatrixMixed

include hline in
private theorem spinSixLiftHasMatrix_three_two (c : K) :
    SpinSixLiftHasMatrix P hline b 3 2 (by decide) c := by
  prove_spinSixLiftHasMatrixMixed

include hline in
/-- The half-spin matrix of the canonical lift is the elementary transvection it lifts. -/
@[simp]
theorem toMatrix_spinPlusAction_spinSixTransvectionLift {i j : Fin 4}
    (hij : i ≠ j) (c : K) :
    LinearMap.toMatrix (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (b.spinSixEvenMonomialBasis (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q
          (spinSixTransvectionLift P hline b hij c))) = Matrix.transvection i j c := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · convert spinSixLiftHasMatrix_zero_one P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_zero_two P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_zero_three P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_one_zero P hline b c using 1
    all_goals rfl
  · exact (hij rfl).elim
  · convert spinSixLiftHasMatrix_one_two P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_one_three P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_two_zero P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_two_one P hline b c using 1
    all_goals rfl
  · exact (hij rfl).elim
  · convert spinSixLiftHasMatrix_two_three P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_three_zero P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_three_one P hline b c using 1
    all_goals rfl
  · convert spinSixLiftHasMatrix_three_two P hline b c using 1
    all_goals rfl
  · exact (hij rfl).elim

/-- The vector action of the canonical lift is its defining Eichler transvection. -/
@[simp]
theorem spinVectorAction_spinSixTransvectionLift_apply {i j : Fin 4} (hij : i ≠ j) (c : K)
    (x : V) :
    spinVectorAction Q (spinSixTransvectionLift P hline b hij c) x =
      x + QuadraticMap.polar Q x (spinSixTransvectionFirstVector P b i j) •
          spinSixTransvectionSecondVector P b i j c -
        QuadraticMap.polar Q x (spinSixTransvectionSecondVector P b i j c) •
          spinSixTransvectionFirstVector P b i j -
        (Q (spinSixTransvectionSecondVector P b i j c) *
            QuadraticMap.polar Q x (spinSixTransvectionFirstVector P b i j)) •
          spinSixTransvectionFirstVector P b i j := by
  rw [spinSixTransvectionLift, ← coe_spinToSpecialOrthogonal_apply,
    coe_spinToSpecialOrthogonal_spinTransvection, QuadraticMap.transvection_apply]

end Transvections

include hline b in
private theorem exists_spinPlusAction_spinGroupToEven_eq_of_basis
    (f : Module.End K (spinPlus Q P)) (hf : LinearMap.det f = 1) :
    ∃ s : spinGroup Q, spinPlusAction Q P hline (spinGroupToEven Q s) = f := by
  let B := b.spinSixEvenMonomialBasis (spinPlus_def P)
  -- The half-spin matrices of Spin elements form a subgroup of `SL₄(K)`.
  let ψ : spinGroup Q →* Matrix.SpecialLinearGroup (Fin 4) K :=
    { toFun s := ⟨LinearMap.toMatrix B B (spinPlusAction Q P hline (spinGroupToEven Q s)), by
        rw [LinearMap.det_toMatrix]
        exact det_spinPlusAction_spinGroupToEven_of_basis P hline b s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' s t := Subtype.ext (by
        simp only [map_mul, LinearMap.toMatrix_mul]
        rfl) }
  -- It contains every elementary transvection, so it is everything.
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    exact ⟨spinSixTransvectionLift P hline b hij c,
      Subtype.ext (toMatrix_spinPlusAction_spinSixTransvectionLift P hline b hij c)⟩
  obtain ⟨s, hs⟩ : (⟨LinearMap.toMatrix B B f, by rw [LinearMap.det_toMatrix, hf]⟩ :
      Matrix.SpecialLinearGroup (Fin 4) K) ∈ ψ.range := hrange ▸ Subgroup.mem_top _
  exact ⟨s, (LinearMap.toMatrix B B).injective (congrArg Subtype.val hs)⟩

/-- **Every determinant-one endomorphism of the even half-spin module comes from Spin.** For a
polarization of a six-dimensional quadratic space, the canonical Spin lifts of the Eichler
transvections act on `S⁺` as the elementary transvections of a basis, which generate the special
linear group. -/
theorem exists_spinPlusAction_spinGroupToEven_eq_of_det_eq_one (hW : finrank K P.W = 3)
    (f : Module.End K (spinPlus Q P)) (hf : LinearMap.det f = 1) :
    ∃ s : spinGroup Q, spinPlusAction Q P hline (spinGroupToEven Q s) = f :=
  have : Module.Finite K P.W := Module.finite_of_finrank_pos (by omega)
  exists_spinPlusAction_spinGroupToEven_eq_of_basis P hline (finBasisOfFinrankEq K P.W hW) f hf

private noncomputable def spinGroupToSpecialLinear
    (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    [FiniteDimensional K V]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) :
    spinGroup Q →* Matrix.SpecialLinearGroup (Fin 4) K := by
  let e := P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
  let u := e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
    (P.nondegenerate_of_line_eq_bot hline) hV
  exact
    { toFun := fun s ↦ ⟨u (spinGroupToEvenUnitary Q s), by
          -- The `show` exposes the matrix coercion needed by `det_toMatrix`; the
          -- application lemma unfolds the general-linear equivalence, not the Spin action.
          rw [show (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) =
              LinearMap.toMatrix b b
                (spinPlusAction Q P hline (spinGroupToEven Q s)) by
              exact
                coe_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_spinGroupToEvenUnitary_apply
                  P hline hW hplus hV b hb s,
            LinearMap.det_toMatrix]
          exact det_spinPlusAction_spinGroupToEven P hline hWfin s⟩
      map_one' := Subtype.ext (by
        -- `Subtype.ext` leaves the `MonoidHom` value under the matrix coercion;
        -- this `change` unfolds only that coercion and the private `toFun` wrapper.
        change (u (spinGroupToEvenUnitary Q 1) : Matrix (Fin 4) (Fin 4) K) = 1
        rw [map_one, map_one, Units.val_one])
      map_mul' := fun s t ↦ Subtype.ext (by
        -- As above, expose the underlying matrix equality so `map_mul` and
        -- `Units.val_mul` can be applied to the two equivalence wrappers.
        change (u (spinGroupToEvenUnitary Q (s * t)) : Matrix (Fin 4) (Fin 4) K) =
          (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) *
            (u (spinGroupToEvenUnitary Q t) : Matrix (Fin 4) (Fin 4) K)
        rw [map_mul, map_mul, Units.val_mul]) }

private theorem spinGroupToSpecialLinear_bijective
    (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    [FiniteDimensional K V]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) :
    Function.Bijective (spinGroupToSpecialLinear P hline hWfin hW hplus hV b hb) := by
  let e := P.evenCliffordEquivProdMatrix (l := 3) hW (by omega)
  let u := e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
    (P.nondegenerate_of_line_eq_bot hline) hV
  constructor
  · intro s t h
    apply spinGroupToEvenUnitary_injective Q
    apply u.injective
    apply Units.ext
    have hmat := congrArg
      (fun z : Matrix.SpecialLinearGroup (Fin 4) K => (z : Matrix (Fin 4) (Fin 4) K)) h
    -- The equality is between special-linear subtypes; expose their underlying
    -- matrix values so injectivity of the unitary equivalence can consume it.
    change (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) =
      u (spinGroupToEvenUnitary Q t) at hmat
    dsimp [u, e]
    exact hmat
  · intro A
    let a : Module.End K (spinPlus Q P) :=
      (LinearMap.toMatrix b b).symm (A : Matrix (Fin 4) (Fin 4) K)
    have hdet : LinearMap.det a = 1 := by
      rw [← LinearMap.det_toMatrix b, LinearEquiv.apply_symm_apply]
      exact A.property
    obtain ⟨s, hs⟩ :=
      exists_spinPlusAction_spinGroupToEven_eq_of_det_eq_one P hline hWfin a hdet
    refine ⟨s, Subtype.ext ?_⟩
    -- Unfold the `MonoidHom` value only far enough to compare its matrix
    -- projection with the target special-linear subtype.
    change (spinGroupToSpecialLinear P hline hWfin hW hplus hV b hb s :
      Matrix (Fin 4) (Fin 4) K) = A
    have hmatrix :=
      coe_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_spinGroupToEvenUnitary_apply
        P hline hW hplus hV b hb s
    -- The preceding application lemma identifies the same matrix after the
    -- private `toFun` wrapper is unfolded; retain that projection explicitly.
    change (u (spinGroupToEvenUnitary Q s) : Matrix (Fin 4) (Fin 4) K) = A
    rw [hmatrix, hs]
    exact LinearEquiv.apply_symm_apply (LinearMap.toMatrix b b)
      (A : Matrix (Fin 4) (Fin 4) K)

/-- The first Clifford factor gives the Spin-to-special-linear equivalence associated to a
polarization of a six-dimensional quadratic space, in the basis
`Module.finBasisOfFinrankEq K (spinPlus Q P) hplus` used by `Algebra.endAlgEquivMatrix`. -/
noncomputable def spinGroupEquivSpecialLinearGroupOfFinrankEqSix
    (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    [FiniteDimensional K V]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) :
    spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
  MulEquiv.ofBijective (spinGroupToSpecialLinear P hline hWfin hW hplus hV b hb)
    (spinGroupToSpecialLinear_bijective P hline hWfin hW hplus hV b hb)

/-- The polarized Spin-to-special-linear equivalence is the matrix of the even half-spin action in
the basis `Module.finBasisOfFinrankEq K (spinPlus Q P) hplus`; `b` is a name for that basis. -/
theorem coe_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_apply
    (P : SpinPolarizationData Q) [FiniteDimensional K (spinPlus Q P)]
    [FiniteDimensional K V]
    (hline : P.line = ⊥)
    (hWfin : finrank K P.W = 3) (hW : P.W ≠ ⊥) (hplus : finrank K (spinPlus Q P) = 4)
    (hV : finrank K V = 6) (b : Basis (Fin 4) K (spinPlus Q P))
    (hb : b = Module.finBasisOfFinrankEq K (spinPlus Q P) hplus) (s : spinGroup Q) :
    (spinGroupEquivSpecialLinearGroupOfFinrankEqSix P hline hWfin hW hplus hV b hb s :
      Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix b b (spinPlusAction Q P hline (spinGroupToEven Q s)) := by
  rw [spinGroupEquivSpecialLinearGroupOfFinrankEqSix, MulEquiv.ofBijective_apply]
  -- `MulEquiv.ofBijective_apply` leaves the special-linear subtype wrapper;
  -- expose its matrix projection before applying the shared matrix formula.
  change (spinGroupToSpecialLinear P hline hWfin hW hplus hV b hb s :
    Matrix (Fin 4) (Fin 4) K) = _
  rw [spinGroupToSpecialLinear]
  exact coe_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_spinGroupToEvenUnitary_apply
    P hline hW hplus hV b hb s

end Polarization

/-! ### Three hyperbolic planes -/

section Hyperbolic

variable (K) [NeZero (2 : K)]

attribute [local instance] hyperbolicSixInvertibleTwo

omit [NeZero (2 : K)] in
/-- The even half-spin module of the split six-dimensional space has dimension four. -/
theorem finrank_hyperbolicSixSpinPlus :
    finrank K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) = 4 := by
  rw [finrank_spinPlus _ (splitEvenPolarization_W_ne_bot K (by norm_num)),
    finrank_splitEvenPolarization_W K 3]
  norm_num

/-- The split six-dimensional even half-spin module is finite-dimensional. -/
noncomputable instance hyperbolicSixSpinPlusFinite :
    FiniteDimensional K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
  Module.finite_of_finrank_pos (by rw [finrank_hyperbolicSixSpinPlus]; norm_num)

private theorem det_hyperbolicSixEvenUnitaryEquivGeneralLinear
    (x : evenUnitaryGroup (splitEvenForm K 3)) :
    (hyperbolicSixEvenUnitaryEquivGeneralLinear K x : Matrix (Fin 4) (Fin 4) K).det =
      LinearMap.det (spinPlusAction _ _ (splitEvenPolarization_line K 3)
        (evenUnitaryGroupEvenPart _ x)) := by
  have : Module.Finite K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
    Module.Finite.of_basis ((splitEvenBasis K 3).spinSixEvenMonomialBasis (spinPlus_def _))
  have h := hyperbolicSixEvenEquivMatrixProd_apply K (evenUnitaryGroupEvenPart _ x)
  rw [SpinPolarizationData.evenCliffordEquivProdMatrix_apply] at h
  rw [coe_hyperbolicSixEvenUnitaryEquivGeneralLinear_apply]
  simpa using congrArg (fun p ↦ Matrix.det p.1) h

private theorem hyperbolicSixEvenUnitaryEquivGeneralLinear_eq_of_spinPlusAction_eq
    {x y : evenUnitaryGroup (splitEvenForm K 3)}
    (h : spinPlusAction _ _ (splitEvenPolarization_line K 3) (evenUnitaryGroupEvenPart _ x) =
      spinPlusAction _ _ (splitEvenPolarization_line K 3) (evenUnitaryGroupEvenPart _ y)) :
    hyperbolicSixEvenUnitaryEquivGeneralLinear K x =
      hyperbolicSixEvenUnitaryEquivGeneralLinear K y := by
  have hx := hyperbolicSixEvenEquivMatrixProd_apply K (evenUnitaryGroupEvenPart _ x)
  have hy := hyperbolicSixEvenEquivMatrixProd_apply K (evenUnitaryGroupEvenPart _ y)
  rw [SpinPolarizationData.evenCliffordEquivProdMatrix_apply] at hx hy
  apply Units.ext
  rw [coe_hyperbolicSixEvenUnitaryEquivGeneralLinear_apply,
    coe_hyperbolicSixEvenUnitaryEquivGeneralLinear_apply]
  simp only [hx, hy, h]

/-- **Spin is the determinant-one part of the even unitary group of three hyperbolic planes.**
Under the identification `U(C₀, σ) ≅ GL₄(K)` by the first half-spin factor, an even unitary
element lies in `Spin(Q)` exactly when its matrix has determinant one. -/
theorem mem_range_spinGroupToEvenUnitary_iff_det_hyperbolicSixEvenUnitaryEquivGeneralLinear
    (x : evenUnitaryGroup (splitEvenForm K 3)) :
    x ∈ (spinGroupToEvenUnitary (splitEvenForm K 3)).range ↔
      (hyperbolicSixEvenUnitaryEquivGeneralLinear K x : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [det_hyperbolicSixEvenUnitaryEquivGeneralLinear]
  constructor
  · rintro ⟨s, rfl⟩
    rw [evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply]
    exact det_spinPlusAction_spinGroupToEven_of_basis _ _ (splitEvenBasis K 3) s
  · intro h
    obtain ⟨s, hs⟩ := exists_spinPlusAction_spinGroupToEven_eq_of_basis _
      (splitEvenPolarization_line K 3) (splitEvenBasis K 3) _ h
    replace hs := (congrArg (spinPlusAction _ _ (splitEvenPolarization_line K 3))
      (evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply _ s)).trans hs
    exact MonoidHom.mem_range.mpr ⟨s, (hyperbolicSixEvenUnitaryEquivGeneralLinear K).injective
      (hyperbolicSixEvenUnitaryEquivGeneralLinear_eq_of_spinPlusAction_eq K hs)⟩

/-- **The Spin group of three hyperbolic planes is `SL₄(K)`.** It is the determinant-one subgroup
of the reverse-unitary group `U(C₀, σ) ≅ GL₄(K)` of the half-spin matrix-product model. Over `ℚ`
this is the split rational six-dimensional form, with `U(C₀, σ) ≅ GL₄(ℚ)` and
`Spin(Q) ≅ SL₄(ℚ)`. -/
noncomputable abbrev hyperbolicSixSpinEquivSpecialLinear :
    spinGroup (splitEvenForm K 3) ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
  spinGroupEquivSpecialLinearGroupOfFinrankEqSix (splitEvenPolarization K 3)
    (splitEvenPolarization_line K 3) (by simp)
    (splitEvenPolarization_W_ne_bot K (by norm_num)) (by
      simpa using finrank_hyperbolicSixSpinPlus K) (finrank_splitEvenSpace K 3)
    (Module.finBasisOfFinrankEq K _ (finrank_hyperbolicSixSpinPlus K)) rfl

/-- The Spin equivalence is the general linear equivalence of the even unitary group, read on
Spin elements. -/
@[simp]
theorem coe_hyperbolicSixSpinEquivSpecialLinear_apply (s : spinGroup (splitEvenForm K 3)) :
    (hyperbolicSixSpinEquivSpecialLinear K s : Matrix (Fin 4) (Fin 4) K) =
      hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ s) :=
  by
    let P := splitEvenPolarization K 3
    let hline := splitEvenPolarization_line K 3
    let hW := splitEvenPolarization_W_ne_bot K (by norm_num : (3 : ℕ) ≠ 0)
    let hWfin : finrank K P.W = 3 := by simp [P]
    let hplus := finrank_hyperbolicSixSpinPlus K
    let hV := finrank_splitEvenSpace K 3
    let b := Module.finBasisOfFinrankEq K (spinPlus (splitEvenForm K 3) P) hplus
    dsimp [hyperbolicSixSpinEquivSpecialLinear] at ⊢
    rw [spinGroupEquivSpecialLinearGroupOfFinrankEqSix, MulEquiv.ofBijective_apply]
    -- Unfold the split specialization's special-linear subtype so the shared
    -- polarized matrix formula can be applied to its underlying value.
    change (spinGroupToSpecialLinear P hline hWfin hW hplus hV b rfl s :
      Matrix (Fin 4) (Fin 4) K) = _
    rw [spinGroupToSpecialLinear]
    let e := P.evenCliffordEquivProdMatrix (l := 3) hW hV
    -- The general-linear equivalence is an `AlgEquiv`; expose its matrix
    -- coercion before rewriting through the split product-model formulas.
    change ((e.evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix
      (P.nondegenerate_of_line_eq_bot hline) hV
      (spinGroupToEvenUnitary (splitEvenForm K 3) s)) : Matrix (Fin 4) (Fin 4) K) = _
    rw [AlgEquiv.coe_evenUnitaryGroupEquivGeneralLinearOfFinrankEqSix_apply,
      coe_hyperbolicSixEvenUnitaryEquivGeneralLinear_apply,
      hyperbolicSixEvenEquivMatrixProd_apply,
      evenUnitaryGroupEvenPart_spinGroupToEvenUnitary_apply]

/-- The even half-spin basis made from the canonical exterior monomials. -/
noncomputable abbrev spinSixHalfSpinMonomialBasis :
    Basis (Fin 4) K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
  (splitEvenBasis K 3).spinSixEvenMonomialBasis (spinPlus_def _)

/-- The finite-dimensional basis used by the split Spin-to-`SL₄` matrix equivalence. -/
noncomputable abbrev spinSixHalfSpinStandardBasis :
    Basis (Fin 4) K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
  Module.finBasisOfFinrankEq K _ (finrank_hyperbolicSixSpinPlus K)

/-- Conjugating the fixed `SL₄` coordinates by the canonical basis change gives the
monomial-basis matrix of the Spin half-spin action. -/
theorem spinSixBasisChange_conjugate_spinPlusAction
    (s : spinGroup (splitEvenForm K 3)) :
    (spinSixHalfSpinMonomialBasis K).toMatrix (spinSixHalfSpinStandardBasis K) *
        (hyperbolicSixSpinEquivSpecialLinear K s : Matrix (Fin 4) (Fin 4) K) *
        (spinSixHalfSpinStandardBasis K).toMatrix (spinSixHalfSpinMonomialBasis K) =
      LinearMap.toMatrix (spinSixHalfSpinMonomialBasis K) (spinSixHalfSpinMonomialBasis K)
        (spinPlusAction (splitEvenForm K 3) (splitEvenPolarization K 3)
          (splitEvenPolarization_line K 3) (spinGroupToEven _ s)) := by
  let P := splitEvenPolarization K 3
  let hline := splitEvenPolarization_line K 3
  let hW := splitEvenPolarization_W_ne_bot K (by norm_num : (3 : ℕ) ≠ 0)
  let hplus := finrank_hyperbolicSixSpinPlus K
  let hV := finrank_splitEvenSpace K 3
  let F := spinSixHalfSpinStandardBasis K
  have hmatrix : (hyperbolicSixSpinEquivSpecialLinear K s : Matrix (Fin 4) (Fin 4) K) =
      LinearMap.toMatrix F F
        (spinPlusAction (splitEvenForm K 3) P hline (spinGroupToEven _ s)) := by
    exact coe_spinGroupEquivSpecialLinearGroupOfFinrankEqSix_apply P hline
      (by simp [P]) hW hplus hV F rfl s
  rw [hmatrix]
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (b := spinSixHalfSpinMonomialBasis K) (b' := spinSixHalfSpinStandardBasis K)
    (c := spinSixHalfSpinMonomialBasis K) (c' := spinSixHalfSpinStandardBasis K)
    (f := spinPlusAction (splitEvenForm K 3) (splitEvenPolarization K 3)
      (splitEvenPolarization_line K 3) (spinGroupToEven _ s))

/-- The conjugated fixed-coordinate matrix of a canonical Spin lift is the elementary
transvection it lifts. -/
theorem spinSixBasisChange_transvection {i j : Fin 4} (hij : i ≠ j) (c : K) :
    (spinSixHalfSpinMonomialBasis K).toMatrix (spinSixHalfSpinStandardBasis K) *
        (hyperbolicSixSpinEquivSpecialLinear K
          (spinSixTransvectionLift (splitEvenPolarization K 3)
            (splitEvenPolarization_line K 3) (splitEvenBasis K 3) hij c) :
          Matrix (Fin 4) (Fin 4) K) *
        (spinSixHalfSpinStandardBasis K).toMatrix (spinSixHalfSpinMonomialBasis K) =
      Matrix.transvection i j c := by
  rw [spinSixBasisChange_conjugate_spinPlusAction]
  exact toMatrix_spinPlusAction_spinSixTransvectionLift
    (P := splitEvenPolarization K 3) (hline := splitEvenPolarization_line K 3)
    (b := splitEvenBasis K 3) hij c


/-- The inverse Spin equivalence is the inverse general linear equivalence on determinant-one
matrices. -/
@[simp]
theorem spinGroupToEvenUnitary_hyperbolicSixSpinEquivSpecialLinear_symm_apply
    (A : Matrix.SpecialLinearGroup (Fin 4) K) :
    spinGroupToEvenUnitary _ ((hyperbolicSixSpinEquivSpecialLinear K).symm A) =
      (hyperbolicSixEvenUnitaryEquivGeneralLinear K).symm A.toGL := by
  apply (hyperbolicSixEvenUnitaryEquivGeneralLinear K).injective
  apply Units.ext
  rw [MulEquiv.apply_symm_apply, ← coe_hyperbolicSixSpinEquivSpecialLinear_apply,
    MulEquiv.apply_symm_apply]
  simp

end Hyperbolic

end TauCeti
