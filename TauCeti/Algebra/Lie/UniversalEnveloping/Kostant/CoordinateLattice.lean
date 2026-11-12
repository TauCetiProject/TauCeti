/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.MatrixRepresentation
public import TauCeti.LinearAlgebra.CoordinateLattice

/-!
# Kostant-form stability of a coordinate lattice

A standard Chevalley carrier is built from a rational representation on a coordinate space
`ι → ℚ` whose coordinate `ℤ`-lattice is preserved by the Kostant integral form. This file proves
that stability once, from the two properties every such representation supplies: each designated
root operator is square-zero and preserves the coordinate lattice, and each standard coordinate
vector is a Cartan weight vector with integral weights. A root operator that cubes rather than
squares to zero is covered by the second criterion below, where the divided square is the one
further operator whose integrality has to be checked; in particular this applies to any family of
cube-zero integral matrices whose squares are even integral matrices.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.ringChoose_apply_mem_coordinateLattice`: the Cartan
  binomial operators preserve the coordinate lattice.
* `TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice` and
  `TauCeti.UniversalEnvelopingAlgebra.kostantForm_integralMatrix_mem_coordinateLattice`: the whole
  Kostant form preserves the coordinate lattice, including for cube-zero integral matrix families.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {κ : Type v} {ν : Type w}

attribute [local instance] TauCeti.moduleNNRat

variable {ι : Type*} [Finite ι] [DecidableEq ι]

/-- Every Cartan binomial operator preserves the coordinate lattice, because the standard
coordinate vectors are weight vectors with integral weights. -/
theorem ringChoose_apply_mem_coordinateLattice (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ (ι → ℚ))
    {wt : ι → κ → ℤ} (hwt : ∀ a, IsCartanWeightVector h ρ (wt a) (Pi.single a 1))
    (i : κ) (m : ℕ) {v : ι → ℚ} (hv : v ∈ TauCeti.coordinateLattice ι) :
    ρ (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ (h i)) m) v ∈
      TauCeti.coordinateLattice ι := by
  rw [Ring.map_choose]
  refine TauCeti.ringChoose_end_apply_mem_coordinateLattice_of_apply_eq_intCast_smul
    ι (weight := fun a => wt a i) ?_ m hv
  intro a
  rw [Pi.basisFun_apply]
  exact (isCartanWeightVector_iff h ρ).1 (hwt a) i

/-- The coordinate lattice is Kostant-stable when each root operator is nilpotent with a common
bound and all divided powers below that bound preserve the lattice. -/
theorem kostantForm_apply_mem_coordinateLattice_of_pow_eq_zero (e : ν → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ (ι → ℚ))
    {wt : ι → κ → ℤ} (d : ℕ)
    (hpow : ∀ k, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) ^ d = 0)
    (hstab : ∀ k m, m < d → ∀ v ∈ TauCeti.coordinateLattice ι,
      Associative.dividedPower m (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) v ∈
        TauCeti.coordinateLattice ι)
    (hwt : ∀ a, IsCartanWeightVector h ρ (wt a) (Pi.single a 1))
    {u : _root_.UniversalEnvelopingAlgebra ℚ L} (hu : u ∈ kostantForm e h)
    {v : ι → ℚ} (hv : v ∈ TauCeti.coordinateLattice ι) :
    ρ u v ∈ TauCeti.coordinateLattice ι :=
  kostantForm_apply_mem e h ρ (TauCeti.coordinateLattice ι)
    (fun k m _ hw => by
      rw [Associative.map_dividedPower]
      exact Associative.dividedPower_apply_mem_of_pow_eq_zero _
        (TauCeti.coordinateLattice ι) (zero_mem _) d (hpow k)
        (fun j hj _ hjv => hstab k j hj _ hjv) m hw)
    (fun i m _ hw => ringChoose_apply_mem_coordinateLattice h ρ hwt i m hw) u hu hv

/-- **The coordinate lattice of a standard representation is an admissible lattice.** The Kostant
`ℤ`-form presented by square-zero root operators and Cartan operators with integral coordinate
weights preserves the coordinate `ℤ`-lattice. -/
theorem kostantForm_apply_mem_coordinateLattice (e : ν → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ (ι → ℚ))
    {wt : ι → κ → ℤ}
    (hsq : ∀ k, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) ^ 2 = 0)
    (hstab : ∀ k, ∀ v ∈ TauCeti.coordinateLattice ι,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) v ∈ TauCeti.coordinateLattice ι)
    (hwt : ∀ a, IsCartanWeightVector h ρ (wt a) (Pi.single a 1))
    {u : _root_.UniversalEnvelopingAlgebra ℚ L} (hu : u ∈ kostantForm e h)
    {v : ι → ℚ} (hv : v ∈ TauCeti.coordinateLattice ι) :
    ρ u v ∈ TauCeti.coordinateLattice ι :=
  kostantForm_apply_mem_coordinateLattice_of_pow_eq_zero e h ρ 2 hsq
    (fun k m hm v hv => by
      have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl
      · simpa using hv
      · simpa using hstab k v hv)
    hwt hu hv

section IntegralMatrix
open TauCeti (coordinateLattice matrixIntCastLieHom)
attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The standard coordinate lattice is preserved by the Kostant `ℤ`-form of any family of cube-zero
integral matrices whose squares are even integral matrices. -/
theorem kostantForm_integralMatrix_mem_coordinateLattice {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0) :
    ∀ u ∈ kostantForm (fun i => matrixIntCastLieHom ℚ (E i)) Empty.elim,
      ∀ v ∈ (coordinateLattice n).toAddSubgroup,
        representation ℚ (Matrix n n ℚ) (n → ℚ) u v ∈ (coordinateLattice n).toAddSubgroup := by
  intro u hu v hv
  refine kostantForm_apply_mem_coordinateLattice_of_pow_eq_zero
    (fun i => matrixIntCastLieHom ℚ (E i)) Empty.elim (representation ℚ (Matrix n n ℚ) (n → ℚ))
    (wt := fun _ => Empty.elim) 3 (fun i => pow_three_representation_matrix_eq_zero (hcube i))
    (fun i m hm w hw => ?_) (fun a => (isCartanWeightVector_iff Empty.elim _).mpr Empty.rec) hu hv
  obtain rfl | rfl | rfl : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  · simpa using hw
  · rw [Associative.dividedPower_one, representation_ι_apply, Matrix.lie_apply]
    exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (E i) hw
  · rw [dividedPower_two_representation_matrix_apply
      (by rw [← TauCeti.matrixIntCastLieHom_mul, hsq i, map_nsmul])]
    exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (D i) hw

end IntegralMatrix

end TauCeti.UniversalEnvelopingAlgebra
