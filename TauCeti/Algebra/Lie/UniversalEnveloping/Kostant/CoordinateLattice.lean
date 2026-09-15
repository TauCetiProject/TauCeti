/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.CoordinateLattice

/-!
# Kostant-form stability of a coordinate lattice

A standard Chevalley carrier is built from a rational representation on a coordinate space
`ι → ℚ` whose coordinate `ℤ`-lattice is preserved by the Kostant integral form. This file proves
that stability once, from the two properties every such representation supplies: each designated
root operator is square-zero and preserves the coordinate lattice, and each standard coordinate
vector is a Cartan weight vector with integral weights. A root operator that cubes rather than
squares to zero is covered by the second criterion below, where the divided square is the one
further operator whose integrality has to be checked.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.ringChoose_apply_mem_coordinateLattice`: the Cartan
  binomial operators preserve the coordinate lattice.
* `TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice`: the whole Kostant
  form preserves the coordinate lattice.
* `TauCeti.UniversalEnvelopingAlgebra.kostantForm_apply_mem_coordinateLattice_of_pow_three_eq_zero`:
  the same when the root operators cube rather than square to zero, the divided square then being
  the one further operator whose integrality has to be checked. This is the situation of a simple
  root vector acting on a three-term weight string, such as a short root vector of type `G₂` on the
  seven-dimensional module.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This is a shared prerequisite for the Chevalley--Demazure carriers in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`.
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
  kostantForm_apply_mem e h ρ (TauCeti.coordinateLattice ι)
    (fun k m _ hw => by
      rw [Associative.map_dividedPower]
      exact Associative.dividedPower_apply_mem_of_pow_two_eq_zero _ _ (hsq k)
        (fun hw' => hstab k _ hw') m hw)
    (fun i m _ hw => ringChoose_apply_mem_coordinateLattice h ρ hwt i m hw) u hu hv

/-- **The coordinate lattice of a standard representation is admissible for cube-zero root
operators.** The Kostant `ℤ`-form presented by root operators that cube to zero and preserve the
coordinate lattice together with their divided squares, and by Cartan operators with integral
coordinate weights, preserves the coordinate `ℤ`-lattice. -/
theorem kostantForm_apply_mem_coordinateLattice_of_pow_three_eq_zero (e : ν → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ (ι → ℚ))
    {wt : ι → κ → ℤ}
    (hcube : ∀ k, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) ^ 3 = 0)
    (hstab : ∀ k, ∀ v ∈ TauCeti.coordinateLattice ι,
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) v ∈ TauCeti.coordinateLattice ι)
    (hstab₂ : ∀ k, ∀ v ∈ TauCeti.coordinateLattice ι,
      Associative.dividedPower 2 (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) v ∈
        TauCeti.coordinateLattice ι)
    (hwt : ∀ a, IsCartanWeightVector h ρ (wt a) (Pi.single a 1))
    {u : _root_.UniversalEnvelopingAlgebra ℚ L} (hu : u ∈ kostantForm e h)
    {v : ι → ℚ} (hv : v ∈ TauCeti.coordinateLattice ι) :
    ρ u v ∈ TauCeti.coordinateLattice ι :=
  kostantForm_apply_mem e h ρ (TauCeti.coordinateLattice ι)
    (fun k m _ hw => by
      rw [Associative.map_dividedPower]
      exact Associative.dividedPower_apply_mem_of_pow_three_eq_zero _
        (TauCeti.coordinateLattice ι).toAddSubgroup (hcube k)
        (fun hw' => hstab k _ hw') (fun hw' => hstab₂ k _ hw') m hw)
    (fun i m _ hw => ringChoose_apply_mem_coordinateLattice h ρ hwt i m hw) u hu hv

end TauCeti.UniversalEnvelopingAlgebra
