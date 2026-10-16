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
# The Spin group of a split six-dimensional quadratic space is `SL₄`

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
* `TauCeti.mem_range_spinGroupToEvenUnitary_iff_det_hyperbolicSixEvenUnitaryEquivGeneralLinear`:
  for three hyperbolic planes, an even unitary element lies in Spin exactly when its image in
  `GL₄(K)` has determinant one.
* `TauCeti.hyperbolicSixSpinEquivSpecialLinear`: the Spin group of three hyperbolic planes is
  `SL₄(K)`, compatibly with `TauCeti.hyperbolicSixEvenUnitaryEquivGeneralLinear`.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.D.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra Module

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

/-- The ordered even monomials `1, e₀e₁, e₀e₂, e₁e₂`. -/
private noncomputable def evenMonomial : Fin 4 → ExteriorAlgebra K M :=
  ![1, ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 1),
    ExteriorAlgebra.ι K (b 0) * ExteriorAlgebra.ι K (b 2),
    ExteriorAlgebra.ι K (b 1) * ExteriorAlgebra.ι K (b 2)]

private theorem basis_empty_eq_one : b.ExteriorAlgebra ∅ = 1 := by
  rw [ExteriorAlgebra.basis_apply]
  simp only [ExteriorAlgebra.ιMulti_family]
  exact ExteriorAlgebra.ιMulti_zero_apply _

private theorem evenMonomial_eq :
    evenMonomial b = b.ExteriorAlgebra ∘ ![∅, {0, 1}, {0, 2}, {1, 2}] := by
  ext j
  fin_cases j
  · simp [evenMonomial, basis_empty_eq_one]
  · simp [evenMonomial, ExteriorAlgebra.basis_pair b (show (0 : Fin 3) < 1 by decide)]
  · simp [evenMonomial, ExteriorAlgebra.basis_pair b (show (0 : Fin 3) < 2 by decide)]
  · simp [evenMonomial, ExteriorAlgebra.basis_pair b (show (1 : Fin 3) < 2 by decide)]

private theorem evenMonomial_mem (j : Fin 4) :
    evenMonomial b j ∈ evenOdd (0 : QuadraticForm K M) 0 := by
  fin_cases j
  · simpa [evenMonomial] using SetLike.one_mem_graded (evenOdd (0 : QuadraticForm K M))
  all_goals exact ι_mul_ι_mem_evenOdd_zero _ _ _

private theorem linearIndependent_evenMonomial : LinearIndependent K (evenMonomial b) := by
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
private noncomputable def evenMonomialBasis : Basis (Fin 4) K N :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun j ↦ (⟨evenMonomial b j, hN ▸ evenMonomial_mem b j⟩ : N))
    (LinearIndependent.of_comp N.subtype (linearIndependent_evenMonomial b))
    (by rw [hN, finrank_evenOdd_zero_eq_four b]; rfl)

private theorem coe_evenMonomialBasis (j : Fin 4) :
    (evenMonomialBasis b hN j : ExteriorAlgebra K M) = evenMonomial b j := by
  simp [evenMonomialBasis]

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
    LinearMap.toMatrix (evenMonomialBasis b hN) (evenMonomialBasis b hN) f =
      baseAfterMatrix (b.repr x) (fun i ↦ d (b i)) := by
  rw [← LinearMap.toMatrix_toLin (evenMonomialBasis b hN) (evenMonomialBasis b hN)
    (baseAfterMatrix _ _)]
  congr 1
  refine (evenMonomialBasis b hN).ext fun j ↦ Subtype.ext ?_
  rw [hf, Matrix.toLin_self, Submodule.coe_sum]
  simp only [Submodule.coe_smul, coe_evenMonomialBasis, Fin.sum_univ_four]
  fin_cases j
  · simp [evenMonomial, baseAfterMatrix, fockAction_base_fockAction_one]
  · simp [evenMonomial, baseAfterMatrix, fockAction_base_fockAction_zero_one]
  · simp [evenMonomial, baseAfterMatrix, fockAction_base_fockAction_zero_two]
    module
  · simp [evenMonomial, baseAfterMatrix, fockAction_base_fockAction_one_two]

private theorem toMatrix_eq_baseBeforeMatrix (x : M) (d : Dual K M) (f : Module.End K N)
    (hf : ∀ s, (f s : ExteriorAlgebra K M) = fockAction x d (fockAction (b 0) (b.coord 0) s)) :
    LinearMap.toMatrix (evenMonomialBasis b hN) (evenMonomialBasis b hN) f =
      baseBeforeMatrix (b.repr x) (fun i ↦ d (b i)) := by
  rw [← LinearMap.toMatrix_toLin (evenMonomialBasis b hN) (evenMonomialBasis b hN)
    (baseBeforeMatrix _ _)]
  congr 1
  refine (evenMonomialBasis b hN).ext fun j ↦ Subtype.ext ?_
  rw [hf, Matrix.toLin_self, Submodule.coe_sum]
  simp only [Submodule.coe_smul, coe_evenMonomialBasis, Fin.sum_univ_four]
  fin_cases j
  · simp [evenMonomial, baseBeforeMatrix, fockAction_fockAction_base_one]
    module
  · simp [evenMonomial, baseBeforeMatrix, fockAction_fockAction_base_zero_one]
    module
  · simp [evenMonomial, baseBeforeMatrix, fockAction_fockAction_base_zero_two]
  · simp [evenMonomial, baseBeforeMatrix, fockAction_fockAction_base_one_two]
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
    LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (vectorPair Q (baseVector P b) v)) =
      baseAfterMatrix (b.repr (creationPart P v)) (fun i ↦ annihilationPart P v (b i)) := by
  refine toMatrix_eq_baseAfterMatrix b (spinPlus_def P) _ _ _ fun s ↦ ?_
  rw [coe_spinPlusAction_apply, coe_vectorPair, map_mul, Module.End.mul_apply,
    spinAction_ι_eq_fockAction P hline, spinAction_ι_eq_fockAction P hline,
    creationPart_baseVector, annihilationPart_baseVector]

include hline in
private theorem toMatrix_vectorPair_baseVector_right (v : V) :
    LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
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
    ← LinearMap.det_toMatrix (evenMonomialBasis b (spinPlus_def P)),
    ← LinearMap.det_toMatrix (evenMonomialBasis b (spinPlus_def P)),
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
    LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q (spinTransvection hQ hu huw))) =
      1 + baseBeforeMatrix (b.repr (creationPart P w)) (fun i ↦ annihilationPart P w (b i)) *
        baseAfterMatrix (b.repr (creationPart P u)) (fun i ↦ annihilationPart P u (b i)) := by
  have heven : spinGroupToEven Q (spinTransvection hQ hu huw) = 1 + vectorPair Q w u :=
    Subtype.ext (by simp [coe_vectorPair])
  rw [heven, map_add, map_one, map_add, LinearMap.toMatrix_one, vectorPair_eq_mul P hline b,
    map_mul, LinearMap.toMatrix_mul, toMatrix_vectorPair_baseVector_right P hline,
    toMatrix_vectorPair_baseVector_left P hline]

include hline in
/-- A Spin transvection whose matrix on `S⁺` is a given matrix. -/
private theorem exists_toMatrix_spinGroupToEven_eq {u w : V} (hQ : Q.Nondegenerate)
    (hu : Q u = 0) (huw : QuadraticMap.polar Q u w = 0) {A : Matrix (Fin 4) (Fin 4) K}
    (hA : 1 + baseBeforeMatrix (b.repr (creationPart P w)) (fun i ↦ annihilationPart P w (b i)) *
        baseAfterMatrix (b.repr (creationPart P u)) (fun i ↦ annihilationPart P u (b i)) = A) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = A :=
  ⟨_, (toMatrix_spinTransvection P hline b hQ hu huw).trans hA⟩

section Transvections

attribute [local simp] baseAfterMatrix baseBeforeMatrix Matrix.transvection Matrix.one_apply
  Matrix.single_apply Finsupp.single_apply

/-! Creation pairs `ι (c • e_a') * ι e_a` move the vacuum `1` to `e_a' ∧ e_a`; annihilation pairs
move `e_a ∧ e_a'` back to `1`; mixed pairs exchange two of `e₀e₁, e₀e₂, e₁e₂`. -/

include hline in
private theorem exists_toMatrix_eq_transvection_one_zero (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 1 0 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 1 : V))
    (w := ((c • b 0 : P.W) : V)) (P.isotropic_W _) (P.polar_W_eq_zero _ _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W]
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_two_zero (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 2 0 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 2 : V))
    (w := ((c • b 0 : P.W) : V)) (P.isotropic_W _) (P.polar_W_eq_zero _ _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W]
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_three_zero (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 3 0 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 2 : V))
    (w := ((c • b 1 : P.W) : V)) (P.isotropic_W _) (P.polar_W_eq_zero _ _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W]
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_zero_one (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 0 1 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (P.dualVector b 0 : V))
    (w := ((c • P.dualVector b 1 : P.W') : V)) (P.isotropic_W' _) (P.polar_W'_eq_zero _ _) ?_
  simp only [creationPart_coe_W', annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_zero_two (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 0 2 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (P.dualVector b 0 : V))
    (w := ((c • P.dualVector b 2 : P.W') : V)) (P.isotropic_W' _) (P.polar_W'_eq_zero _ _) ?_
  simp only [creationPart_coe_W', annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_zero_three (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 0 3 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (P.dualVector b 1 : V))
    (w := ((c • P.dualVector b 2 : P.W') : V)) (P.isotropic_W' _) (P.polar_W'_eq_zero _ _) ?_
  simp only [creationPart_coe_W', annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_two_three (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 2 3 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 0 : V))
    (w := (((-c) • P.dualVector b 1 : P.W') : V)) (P.isotropic_W _)
    (polar_basis_dualVector P b (by decide) _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W, creationPart_coe_W',
    annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_one_three (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 1 3 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 0 : V))
    (w := ((c • P.dualVector b 2 : P.W') : V)) (P.isotropic_W _)
    (polar_basis_dualVector P b (by decide) _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W, creationPart_coe_W',
    annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_three_two (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 3 2 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 1 : V))
    (w := (((-c) • P.dualVector b 0 : P.W') : V)) (P.isotropic_W _)
    (polar_basis_dualVector P b (by decide) _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W, creationPart_coe_W',
    annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_one_two (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 1 2 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 1 : V))
    (w := (((-c) • P.dualVector b 2 : P.W') : V)) (P.isotropic_W _)
    (polar_basis_dualVector P b (by decide) _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W, creationPart_coe_W',
    annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_three_one (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 3 1 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 2 : V))
    (w := ((c • P.dualVector b 0 : P.W') : V)) (P.isotropic_W _)
    (polar_basis_dualVector P b (by decide) _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W, creationPart_coe_W',
    annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

include hline in
private theorem exists_toMatrix_eq_transvection_two_one (hQ : Q.Nondegenerate) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection 2 1 c := by
  refine exists_toMatrix_spinGroupToEven_eq P hline b hQ (u := (b 2 : V))
    (w := (((-c) • P.dualVector b 1 : P.W') : V)) (P.isotropic_W _)
    (polar_basis_dualVector P b (by decide) _) ?_
  simp only [creationPart_coe_W, annihilationPart_coe_W, creationPart_coe_W',
    annihilationPart_coe_W']
  ext k l
  fin_cases k <;> fin_cases l <;> simp

end Transvections

include hline in
private theorem exists_toMatrix_eq_transvection (hQ : Q.Nondegenerate) {i j : Fin 4}
    (hij : i ≠ j) (c : K) :
    ∃ s : spinGroup Q, LinearMap.toMatrix (evenMonomialBasis b (spinPlus_def P))
        (evenMonomialBasis b (spinPlus_def P))
        (spinPlusAction Q P hline (spinGroupToEven Q s)) = Matrix.transvection i j c := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact exists_toMatrix_eq_transvection_zero_one P hline b hQ c
  · exact exists_toMatrix_eq_transvection_zero_two P hline b hQ c
  · exact exists_toMatrix_eq_transvection_zero_three P hline b hQ c
  · exact exists_toMatrix_eq_transvection_one_zero P hline b hQ c
  · exact absurd rfl hij
  · exact exists_toMatrix_eq_transvection_one_two P hline b hQ c
  · exact exists_toMatrix_eq_transvection_one_three P hline b hQ c
  · exact exists_toMatrix_eq_transvection_two_zero P hline b hQ c
  · exact exists_toMatrix_eq_transvection_two_one P hline b hQ c
  · exact absurd rfl hij
  · exact exists_toMatrix_eq_transvection_two_three P hline b hQ c
  · exact exists_toMatrix_eq_transvection_three_zero P hline b hQ c
  · exact exists_toMatrix_eq_transvection_three_one P hline b hQ c
  · exact exists_toMatrix_eq_transvection_three_two P hline b hQ c
  · exact absurd rfl hij

include hline b in
private theorem exists_spinPlusAction_spinGroupToEven_eq_of_basis
    (f : Module.End K (spinPlus Q P)) (hf : LinearMap.det f = 1) :
    ∃ s : spinGroup Q, spinPlusAction Q P hline (spinGroupToEven Q s) = f := by
  let B := evenMonomialBasis b (spinPlus_def P)
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
    obtain ⟨s, hs⟩ := exists_toMatrix_eq_transvection P hline b
      (P.nondegenerate_of_line_eq_bot hline) hij c
    exact ⟨s, Subtype.ext hs⟩
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

end Polarization

/-! ### Three hyperbolic planes -/

private theorem spinGroupToEven_eq_evenUnitaryGroupEvenPart {V : Type*} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (s : spinGroup Q) :
    spinGroupToEven Q s = evenUnitaryGroupEvenPart Q (spinGroupToEvenUnitary Q s) :=
  Subtype.ext (by simp [coe_evenUnitaryGroupEvenPart])

section Hyperbolic

variable (K) [NeZero (2 : K)]

attribute [local instance] hyperbolicSixInvertibleTwo

private theorem det_hyperbolicSixEvenUnitaryEquivGeneralLinear
    (x : evenUnitaryGroup (splitEvenForm K 3)) :
    (hyperbolicSixEvenUnitaryEquivGeneralLinear K x : Matrix (Fin 4) (Fin 4) K).det =
      LinearMap.det (spinPlusAction _ _ (splitEvenPolarization_line K 3)
        (evenUnitaryGroupEvenPart _ x)) := by
  have : Module.Finite K (spinPlus (splitEvenForm K 3) (splitEvenPolarization K 3)) :=
    Module.Finite.of_basis (evenMonomialBasis (splitEvenBasis K 3) (spinPlus_def _))
  have h := hyperbolicSixEvenEquivMatrixProd_apply K (evenUnitaryGroupEvenPart _ x)
  rw [SpinPolarizationData.evenCliffordEquivProdMatrix_apply] at h
  rw [coe_hyperbolicSixEvenUnitaryEquivGeneralLinear_apply]
  exact (congrArg (fun p ↦ Matrix.det p.1) h).trans (Algebra.det_endAlgEquivMatrix _ _ _ _)

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
    rw [← spinGroupToEven_eq_evenUnitaryGroupEvenPart]
    exact det_spinPlusAction_spinGroupToEven_of_basis _ _ (splitEvenBasis K 3) s
  · intro h
    obtain ⟨s, hs⟩ := exists_spinPlusAction_spinGroupToEven_eq_of_basis _
      (splitEvenPolarization_line K 3) (splitEvenBasis K 3) _ h
    replace hs := (congrArg (spinPlusAction _ _ (splitEvenPolarization_line K 3))
      (spinGroupToEven_eq_evenUnitaryGroupEvenPart s).symm).trans hs
    exact MonoidHom.mem_range.mpr ⟨s, (hyperbolicSixEvenUnitaryEquivGeneralLinear K).injective
      (hyperbolicSixEvenUnitaryEquivGeneralLinear_eq_of_spinPlusAction_eq K hs)⟩

private theorem det_hyperbolicSixEvenUnitaryEquivGeneralLinear_spinGroupToEvenUnitary
    (s : spinGroup (splitEvenForm K 3)) :
    (hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ s) :
      Matrix (Fin 4) (Fin 4) K).det = 1 :=
  (mem_range_spinGroupToEvenUnitary_iff_det_hyperbolicSixEvenUnitaryEquivGeneralLinear K _).mp
    ⟨s, rfl⟩

/-- The Spin group of three hyperbolic planes maps to `SL₄(K)` through
`hyperbolicSixEvenUnitaryEquivGeneralLinear`. -/
private noncomputable def hyperbolicSixSpinToSpecialLinear :
    spinGroup (splitEvenForm K 3) →* Matrix.SpecialLinearGroup (Fin 4) K where
  toFun s := ⟨hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ s),
    det_hyperbolicSixEvenUnitaryEquivGeneralLinear_spinGroupToEvenUnitary K s⟩
  map_one' := Subtype.ext <| by
    -- Unfold the subtype coercion to the matrix of the general linear equivalence.
    change ((hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ 1) :
      Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1
    rw [map_one, map_one, Units.val_one]
  map_mul' s t := Subtype.ext <| by
    -- Unfold the subtype coercions to matrices of the general linear equivalence.
    change ((hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ (s * t)) :
      Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        (hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ s) :
          Matrix (Fin 4) (Fin 4) K) *
        (hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ t) :
          Matrix (Fin 4) (Fin 4) K)
    rw [map_mul, map_mul, Units.val_mul]

private theorem coe_hyperbolicSixSpinToSpecialLinear_apply (s : spinGroup (splitEvenForm K 3)) :
    (hyperbolicSixSpinToSpecialLinear K s : Matrix (Fin 4) (Fin 4) K) =
      hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ s) :=
  (rfl)

private theorem hyperbolicSixSpinToSpecialLinear_bijective :
    Function.Bijective (hyperbolicSixSpinToSpecialLinear K) := by
  refine ⟨fun s t h ↦ spinGroupToEvenUnitary_injective _
    ((hyperbolicSixEvenUnitaryEquivGeneralLinear K).injective
      (Units.ext (congrArg Subtype.val h))), fun A ↦ ?_⟩
  obtain ⟨s, hs⟩ :=
    (mem_range_spinGroupToEvenUnitary_iff_det_hyperbolicSixEvenUnitaryEquivGeneralLinear K
      ((hyperbolicSixEvenUnitaryEquivGeneralLinear K).symm A.toGL)).mpr (by simp)
  refine ⟨s, Subtype.ext ?_⟩
  rw [coe_hyperbolicSixSpinToSpecialLinear_apply, hs, MulEquiv.apply_symm_apply]
  simp

/-- **The Spin group of three hyperbolic planes is `SL₄(K)`.** It is the determinant-one subgroup
of the reverse-unitary group `U(C₀, σ) ≅ GL₄(K)` of the half-spin matrix-product model. Over `ℚ`
this is the split rational six-dimensional form, with `U(C₀, σ) ≅ GL₄(ℚ)` and
`Spin(Q) ≅ SL₄(ℚ)`. -/
noncomputable def hyperbolicSixSpinEquivSpecialLinear :
    spinGroup (splitEvenForm K 3) ≃* Matrix.SpecialLinearGroup (Fin 4) K :=
  MulEquiv.ofBijective _ (hyperbolicSixSpinToSpecialLinear_bijective K)

/-- The Spin equivalence is the general linear equivalence of the even unitary group, read on
Spin elements. -/
@[simp]
theorem coe_hyperbolicSixSpinEquivSpecialLinear_apply (s : spinGroup (splitEvenForm K 3)) :
    (hyperbolicSixSpinEquivSpecialLinear K s : Matrix (Fin 4) (Fin 4) K) =
      hyperbolicSixEvenUnitaryEquivGeneralLinear K (spinGroupToEvenUnitary _ s) :=
  (rfl)

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
