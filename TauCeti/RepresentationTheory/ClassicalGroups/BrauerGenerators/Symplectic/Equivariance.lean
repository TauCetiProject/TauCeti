/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.Action

import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Symplectic.TwoStrands

/-!
# The Brauer algebra acts by intertwiners of the symplectic group

The action `TauCeti.brauerActionSymp` of the Brauer algebra `B_d(-2n)` on the tensor power
`(k^{2n})^{⊗d}` commutes with the diagonal action `A ↦ A^{⊗d}` of every matrix `A` preserving the
standard alternating form `Aᵀ * Matrix.J (Fin n) k * A = Matrix.J (Fin n) k`. Equivalently, the
image of `B_d(-2n)` lies in the commutant of the symplectic group acting on `(k^{2n})^{⊗d}`
(`TauCeti.range_brauerActionSymp_le_centralizer`). This is the equivariance half of Brauer's
Schur-Weyl duality for the symplectic group.

Because the image of `B_d(-2n)` is generated as a `k`-algebra by the sign-twisted permutations and
the single-arc operators on distinct strands (`TauCeti.range_brauerActionSymp_eq_adjoin_union`),
and the operators commuting with `A^{⊗d}` form a subalgebra (`Subalgebra.centralizer`),
equivariance of the entire Brauer algebra reduces to the two generator families:

* permutation diagrams act by `TauCeti.symplecticPermTensorAction`, which commutes with the
  diagonal action of *every* linear map (`PiTensorProduct.commute_signReindexRepresentation_map`);
* cap-cup diagrams on distinct strands act by `TauCeti.symplecticCupCapAt`, which commutes with
  `A^{⊗d}` whenever `Aᵀ * J * A = J` (`TauCeti.commute_symplecticCupCapAt_piTensorProductMap`).

On two strands (`d = 2`), combining `TauCeti.range_brauerActionSymp_two_eq_adjoin` with the
two-strand commutant calculation of
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/TwoStrands.lean` upgrades
the inclusion to an equality (`TauCeti.range_brauerActionSymp_two_eq_centralizer`,
`TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero`).

## Main results

* `TauCeti.commute_brauerActionSymp_piTensorProductMap`: every element of `B_d(-2n)` acts by an
  operator commuting with `A^{⊗d}` when `Aᵀ * J * A = J`.
* `TauCeti.commute_brauerActionSymp_tensorPower` and
  `TauCeti.range_brauerActionSymp_le_centralizer`: the action commutes with the tensor-power
  representation of `Matrix.symplecticGroup (Fin n) k`, so the image of `B_d(-2n)` lies in its
  commutant.
* `TauCeti.range_brauerActionSymp_two_eq_centralizer` and
  `TauCeti.range_brauerActionSymp_two_eq_centralizer_of_charZero`: on two strands, the image of
  `B_2(-2n)` equals the commutant of the symplectic group.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Dipper, S. Doty, and J. Hu, *Brauer algebras, symplectic Schur algebras and Schur-Weyl
  duality*, Transactions of the American Mathematical Society 360 (2008), 189-213, §1.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), Chapter 10.
-/

public section

open Matrix
open scoped TensorProduct

namespace TauCeti

universe u

section CommRing

variable (k : Type u) [CommRing k] (n d : ℕ)

/-- **The symplectic Brauer action commutes with symplectic matrices.** Every element of the Brauer
algebra `B_d(-2n)` acts on `(k^{2n})^{⊗d}` by an operator commuting with the diagonal action of
each matrix `A` satisfying `Aᵀ * J * A = J`. -/
theorem commute_brauerActionSymp_piTensorProductMap (x : BrauerAlgebra k (-(2 * n : k)) d)
    {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k}
    (hA : Aᵀ * Matrix.J (Fin n) k * A = Matrix.J (Fin n) k) :
    Commute (brauerActionSymp k n d x)
      (PiTensorProduct.map fun _ : Fin d => A.mulVecLin) := by
  set T : Module.End k (⨂[k]^d ((Fin n ⊕ Fin n) → k)) :=
    PiTensorProduct.map fun _ : Fin d => A.mulVecLin
  have hle : (brauerActionSymp k n d).range ≤ Subalgebra.centralizer k ({T} : Set _) := by
    rw [range_brauerActionSymp_eq_adjoin_union, Algebra.adjoin_le_iff]
    rintro _ (⟨σ, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      rw [symplecticPermTensorAction_def]
      exact (PiTensorProduct.commute_signReindexRepresentation_map σ A.mulVecLin).symm.eq
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (commute_symplecticCupCapAt_piTensorProductMap hA hij).symm.eq
  have hx := hle ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff] at hx
  exact Commute.symm (hx T rfl)

/-- **The Brauer algebra acts by intertwiners of the symplectic group.** Every element of
`B_d(-2n)` acts on `(k^{2n})^{⊗d}` by an operator commuting with the tensor power of the standard
representation of `Matrix.symplecticGroup (Fin n) k`. -/
theorem commute_brauerActionSymp_tensorPower (x : BrauerAlgebra k (-(2 * n : k)) d)
    (g : Matrix.symplecticGroup (Fin n) k) :
    Commute (brauerActionSymp k n d x) ((stdSymplecticRep k n).tensorPower d g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdSymplecticRep_apply] using
    commute_brauerActionSymp_piTensorProductMap k n d x
      ((SymplecticGroup.mem_iff' (l := Fin n) (R := k)).mp g.prop)

/-- **The image of the Brauer algebra lies in the commutant of the symplectic group** acting on
`(k^{2n})^{⊗d}`. -/
theorem range_brauerActionSymp_le_centralizer :
    (brauerActionSymp k n d).range ≤
      Subalgebra.centralizer k (Set.range ((stdSymplecticRep k n).tensorPower d)) := by
  rintro _ ⟨x, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionSymp_tensorPower k n d x g).symm.eq

/-- **Brauer duality for the symplectic group on two strands.** Over an integral domain containing
a unit `t` with `t ^ m ≠ 1` for `0 < m ≤ 4`, the image of `B_2(-2n)` in the endomorphisms of
`k^{2n} ⊗ k^{2n}` equals the commutant of the diagonal action of the symplectic group. -/
theorem range_brauerActionSymp_two_eq_centralizer [IsDomain k]
    (ht : ∃ t : kˣ, ∀ m : ℕ, 0 < m → m ≤ 4 → t ^ m ≠ 1) :
    (brauerActionSymp k n 2).range =
      Subalgebra.centralizer k (Set.range ((stdSymplecticRep k n).tensorPower 2)) :=
  (range_brauerActionSymp_two_eq_adjoin k n).trans
    (adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer ht)

end CommRing

section CharZero

/-- **Brauer duality for the symplectic group on two strands in characteristic zero**: over a field
of characteristic zero, the image of `B_2(-2n)` on `K^{2n} ⊗ K^{2n}` equals the commutant of the
symplectic group. -/
theorem range_brauerActionSymp_two_eq_centralizer_of_charZero
    (K : Type u) [Field K] [CharZero K] (n : ℕ) :
    (brauerActionSymp K n 2).range =
      Subalgebra.centralizer K (Set.range ((stdSymplecticRep K n).tensorPower 2)) :=
  (range_brauerActionSymp_two_eq_adjoin K n).trans
    adjoin_symplecticCrossing_symplecticCupCap_eq_centralizer_of_charZero

end CharZero

end TauCeti
