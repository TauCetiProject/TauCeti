/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Action
import Mathlib.Data.Fintype.EquivFin
import TauCeti.LinearAlgebra.SymplecticGroup
import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TwoStrands

/-!
# The Brauer algebra acts by intertwiners of the symplectic group

The action `TauCeti.brauerActionSymp` of the Brauer algebra `B_d(-2n)` on the tensor power
`V^{⊗d}` of `V = (Fin n ⊕ Fin n) → k` commutes with the diagonal action `g ↦ g^{⊗d}` of every
matrix `g` preserving the standard alternating form, that is, satisfying `gᵀ * J * g = J`
(`TauCeti.commute_brauerActionSymp_piTensorProductMap`). Equivalently, the image of `B_d(-2n)`
lies in the commutant of the symplectic group `Sp(2n, k)` acting on `V^{⊗d}`
(`TauCeti.range_brauerActionSymp_le_centralizer`). This is the equivariance half of Brauer's
Schur-Weyl duality for the symplectic group.

Every Brauer diagram is a loop-free stack of cap-cup generators `capCup a b` (`a ≠ b`) above a
permutation diagram (`TauCeti.BrauerDiagram.capCup_induction_on`). Under `brauerActionSymp`, a
permutation diagram acts as `TauCeti.symplecticPermTensorAction`, which commutes with every
diagonal linear map, and `capCup a b` acts as `TauCeti.symplecticCupCapAt`, which commutes with
`g^{⊗d}` whenever `gᵀ * J * g = J` (`TauCeti.commute_symplecticCupCapAt_piTensorProductMap`). In
the monomial basis this also gives matrix-level commutation between
`TauCeti.BrauerDiagram.symplecticActionMatrix` and `Matrix.kroneckerPower` over any finite index
type (`TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`).

On two strands (`d = 2`), combining `TauCeti.range_brauerActionSymp_two` with the two-strand
commutant theorem of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/TwoStrands.lean`
identifies the image of `B₂(-2n)` with the full commutant of `Sp(2n)` over every integral domain
with a unit of order greater than `4`, and in particular over every field of characteristic zero
(`TauCeti.range_brauerActionSymp_two_eq_centralizer` and
`TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero`).

## Main results

* `TauCeti.commute_brauerActionSymp_piTensorProductMap`: every element of `B_d(-2n)` acts on
  `V^{⊗d}` by an operator commuting with `A^{⊗d}` whenever `Aᵀ * J * A = J`.
* `TauCeti.BrauerDiagram.commute_symplecticActionMatrix_kroneckerPower`: for any finite index type
  `l`, the symplectic matrix of a Brauer diagram commutes with the Kronecker power of every matrix
  `A` satisfying `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymp_tensorPower` and
  `TauCeti.range_brauerActionSymp_le_centralizer`: every element of `B_d(-2n)` acts by an
  intertwiner of `(stdSymplecticRep k n).tensorPower d`, so the image of `brauerActionSymp` lies in
  the commutant of `Sp(2n, k)`.
* `TauCeti.range_brauerActionSymp_two_eq_centralizer` and
  `TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero`: **Brauer duality on two strands**
  expressed directly in terms of `brauerActionSymp`.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapters 5, 9, and 10.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

universe u

section Intertwiner

variable (k : Type u) [CommRing k] (n d : ℕ)

/-- **The Brauer algebra commutes with symplectic matrices.** Every element of `B_d(-2n)` acts on
`⨂[k]^d ((Fin n ⊕ Fin n) → k)` by an operator commuting with the diagonal action of each matrix `A`
satisfying `Aᵀ * J * A = J`. -/
theorem commute_brauerActionSymp_piTensorProductMap (x : BrauerAlgebra k (-(2 * n : k)) d)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hA : Aᵀ * Matrix.J (Fin n) k * A = Matrix.J (Fin n) k) :
    Commute (brauerActionSymp k n d x) (PiTensorProduct.map fun _ : Fin d => A.mulVecLin) := by
  set T := PiTensorProduct.map fun _ : Fin d => A.mulVecLin
  -- Every diagram is a loop-free stack of `capCup` generators above a permutation diagram.
  have hD (D : BrauerDiagram d) :
      Commute (brauerActionSymp k n d (BrauerAlgebra.of D)) T := by
    induction D using BrauerDiagram.capCup_induction_on with
    | permToBrauer σ =>
      rw [brauerActionSymp_of_permToBrauer, symplecticPermTensorAction_def]
      exact PiTensorProduct.commute_signReindexRepresentation_map σ A.mulVecLin
    | capCup_compose a b X hab hloop ih =>
      rw [← BrauerAlgebra.of_mul_of_of_middleLoopCount_eq_zero hloop, map_mul,
        brauerActionSymp_of_capCup k n d hab]
      exact (commute_symplecticCupCapAt_piTensorProductMap hA hab).mul_left ih
  -- Both products are `k`-linear in `x`, so equality on the diagram basis extends to all of `B_d`.
  have hlin : (LinearMap.mulRight k T).comp (brauerActionSymp k n d).toLinearMap =
      (LinearMap.mulLeft k T).comp (brauerActionSymp k n d).toLinearMap :=
    (BrauerAlgebra.basis k (-(2 * n : k)) d).ext fun D => by
      simpa [BrauerAlgebra.basis_apply] using (hD D).eq
  exact LinearMap.congr_fun hlin x

/-- **The Brauer algebra acts by intertwiners of the symplectic group.** Every element of
`B_d(-2n)` acts on `⨂[k]^d ((Fin n ⊕ Fin n) → k)` by an operator commuting with the `d`-th tensor
power of the standard representation of `Sp(2n, k)`. -/
theorem commute_brauerActionSymp_tensorPower (x : BrauerAlgebra k (-(2 * n : k)) d)
    (g : Matrix.symplecticGroup (Fin n) k) :
    Commute (brauerActionSymp k n d x) ((stdSymplecticRep k n).tensorPower d g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_brauerActionSymp_piTensorProductMap k n d x
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := k)).mp g.prop)

/-- **The image of the Brauer algebra lies in the commutant of the symplectic group** acting on the
tensor power `⨂[k]^d ((Fin n ⊕ Fin n) → k)`. -/
theorem range_brauerActionSymp_le_centralizer :
    (brauerActionSymp k n d).range ≤
      Subalgebra.centralizer k (Set.range ((stdSymplecticRep k n).tensorPower d)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionSymp_tensorPower k n d x g).symm.eq

end Intertwiner

namespace BrauerDiagram

/-- **The symplectic matrix of a Brauer diagram commutes with symplectic Kronecker powers.** For any
finite index type `l` and matrix `A : Matrix (l ⊕ l) (l ⊕ l) k` with `Aᵀ * J * A = J`, the matrix
`TauCeti.BrauerDiagram.symplecticActionMatrix` of `D` commutes with `A.kroneckerPower (Fin d)`. -/
theorem commute_symplecticActionMatrix_kroneckerPower {k : Type u} [CommRing k] {l : Type*}
    [Fintype l] [DecidableEq l] {d : ℕ} (D : BrauerDiagram d)
    {A : Matrix (l ⊕ l) (l ⊕ l) k} (hA : Aᵀ * Matrix.J l k * A = Matrix.J l k) :
    Commute (D.symplecticActionMatrix k l) (A.kroneckerPower (Fin d)) := by
  set m := Fintype.card l
  let e : l ≃ Fin m := Fintype.equivFin l
  let s : l ⊕ l ≃ Fin m ⊕ Fin m := e.sumCongr e
  let p : (Fin d → l ⊕ l) ≃ (Fin d → Fin m ⊕ Fin m) := Equiv.piCongrRight fun _ => s
  set A' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k := A.submatrix s.symm s.symm
  have hJ : (Matrix.J l k).submatrix s.symm s.symm = Matrix.J (Fin m) k := by
    ext x y
    rcases x with i | i <;> rcases y with j | j <;> simp [s, Matrix.J, Matrix.one_apply]
  have hA' : A'ᵀ * Matrix.J (Fin m) k * A' = Matrix.J (Fin m) k := by
    dsimp only [A']
    rw [Matrix.transpose_submatrix, ← hJ, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hA]
  have hlin := (commute_brauerActionSymp_piTensorProductMap k m d (BrauerAlgebra.of D) hA').eq
  have hmat := congrArg
    (LinearMap.toMatrix (symplecticTensorPowerBasis k m d) (symplecticTensorPowerBasis k m d)) hlin
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, brauerActionSymp_of, LinearMap.toMatrix_toLin,
    A'.toMatrix_piTensorProductMap_symplecticTensorPowerBasis] at hmat
  have hW (v u : Fin d → Fin m ⊕ Fin m) :
      symplecticArcWeight k (p.symm u) (p.symm v) = symplecticArcWeight k u v := by
    ext x y
    rcases x with i | i <;> rcases y with j | j
    · simpa [p] using congrFun (congrFun hJ (u i)) (u j)
    · simp [p]
    · simp [p]
    · simpa [p] using congrFun (congrFun hJ (v i)) (v j)
  have hM : (D.symplecticActionMatrix k l).submatrix p.symm p.symm =
      D.symplecticActionMatrix k (Fin m) := by
    ext v u
    simp [hW]
  have hK : (A.kroneckerPower (Fin d)).submatrix p.symm p.symm = A'.kroneckerPower (Fin d) := by
    ext v u
    simp [A', p, Matrix.kroneckerPower_apply]
  rw [← hM, ← hK, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv] at hmat
  rw [Commute, SemiconjBy]
  ext v u
  simpa [p] using congrFun (congrFun hmat (p v)) (p u)

end BrauerDiagram

/-! ### Brauer duality on two strands -/

section TwoStrands

/-- **Brauer duality for the symplectic group on two strands.** Over an integral domain `k`
containing a unit `t` with `t ^ m ≠ 1` for `0 < m ≤ 4`, the image of `B₂(-2n)` under
`TauCeti.brauerActionSymp` is the full commutant of `Sp(2n, k)` on the tensor square of `k^{2n}`. -/
theorem range_brauerActionSymp_two_eq_centralizer {k : Type u} [CommRing k] [IsDomain k] (n : ℕ)
    (ht : ∃ t : kˣ, ∀ m : ℕ, 0 < m → m ≤ 4 → t ^ m ≠ 1) :
    (brauerActionSymp k n 2).range =
      Subalgebra.centralizer k (Set.range ((stdSymplecticRep k n).tensorPower 2)) := by
  rw [range_brauerActionSymp_two, adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer ht]

/-- **Brauer duality for the symplectic group on two strands in characteristic zero**: over any
field `K` of characteristic zero, the image of `B₂(-2n)` under `TauCeti.brauerActionSymp` is the
full commutant of `Sp(2n, K)` on `(K^{2n})^{⊗2}`. -/
theorem range_brauerActionSymp_two_eq_centralizer_of_charZero {K : Type u} [Field K] [CharZero K]
    (n : ℕ) :
    (brauerActionSymp K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2)) := by
  rw [range_brauerActionSymp_two,
    adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer_of_charZero]

end TwoStrands

end TauCeti
