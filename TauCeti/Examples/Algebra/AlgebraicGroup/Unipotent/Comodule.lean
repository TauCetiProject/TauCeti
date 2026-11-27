/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Comodule

/-!
# Checks for the comodule definition of unipotence

Examples and non-examples of unipotent affine groups under the comodule definition.

* `𝔾ₐ` is unipotent over every field
  (`TauCeti.AdditiveGroup.unipotentCommHopfAlgProperty_coordinateHopfAlgebra`).
* A diagonalizable group `D(A)` with nontrivial character group `A` is not unipotent: a character
  `a ≠ 1` is a group-like element of `k[A]` different from `1`.
* In particular `μₙ` for `n ≠ 1` is not unipotent, in every characteristic. For `n = p` in
  characteristic `p` this holds although `μₚ` has only the trivial point over an algebraic
  closure: the comodule definition sees the nonreduced structure that the geometric-point
  criterion misses. The multiplicative group `𝔾ₘ = μ₀` is not unipotent either.
* In characteristic `p`, the Frobenius kernel `αₚ` is unipotent
  (`TauCeti.AlphaP.unipotentCommHopfAlgProperty_coordinateRing`) and not smooth, its coordinate
  ring `k[x] / (xᵖ)` being nonreduced (`TauCeti.AlphaP.coordinateRing_not_isReduced`).
-/

public section

namespace TauCeti.Examples.UnipotentComodule

open TauCeti

universe u

variable (k : Type u) [Field k]

/-- A diagonalizable group with a nontrivial character group is not unipotent. -/
theorem not_unipotent_diagonalizable (A : FGCommGrpCat.{u}) [Nontrivial A] :
    ¬ unipotentCommHopfAlgProperty k (DiagonalizableGroup.coordinateRing k A).obj := by
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  refine not_unipotentCommHopfAlgProperty_of_isGroupLikeElem (H := MonoidAlgebra k A)
    (MonoidAlgebra.isGroupLikeElem_single_one a) fun h ↦ ha ?_
  rw [MonoidAlgebra.one_def] at h
  exact MonoidAlgebra.single_left_injective one_ne_zero h

/-- `μₙ` is not unipotent for `n ≠ 1`, in every characteristic, including `n = p` in
characteristic `p`, where its only point over an algebraic closure is trivial. -/
theorem not_unipotent_rootsOfUnity (n : ℕ) (hn : n ≠ 1) :
    ¬ unipotentCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k (RootsOfUnityGroup.characterGroup.{u} n)).obj :=
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hn
  not_unipotent_diagonalizable k _

/-- The multiplicative group `𝔾ₘ = μ₀` is not unipotent. -/
theorem not_unipotent_multiplicativeGroup :
    ¬ unipotentCommHopfAlgProperty k
      (DiagonalizableGroup.coordinateRing k (RootsOfUnityGroup.characterGroup.{u} 0)).obj :=
  not_unipotent_rootsOfUnity k 0 zero_ne_one

/-- `𝔾ₐ` is unipotent. -/
example : unipotentCommHopfAlgProperty k (AdditiveGroup.coordinateHopfAlgebra k) :=
  AdditiveGroup.unipotentCommHopfAlgProperty_coordinateHopfAlgebra k

/-- In characteristic `p`, `αₚ` is unipotent, and its coordinate ring is not reduced. -/
example (p : ℕ) [Fact p.Prime] [CharP k p] :
    unipotentCommHopfAlgProperty k (CommHopfAlgCat.of k (AlphaP.CoordinateRing (R := k) p)) ∧
      ¬ IsReduced (AlphaP.CoordinateRing (R := k) p) :=
  ⟨AlphaP.unipotentCommHopfAlgProperty_coordinateRing p k, AlphaP.coordinateRing_not_isReduced p⟩

end TauCeti.Examples.UnipotentComodule
