/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.RelationModule.Presentation
import TauCeti.NumberTheory.LocalField.Generation.Presentation

/-!
# Relation-module surjections for arbitrary finite local Galois layers

Let `L/K` be a finite Galois extension of finite extensions of `ℚ_p`, and put
`N = [K : ℚ_p]`. For every generating family of `Gal(L/K)` with at least `N + 2` members, its
relation module over `ℤ_p` surjects onto the completed multiplicative group `A(L)`.
There is no tame-ramification hypothesis and no free presentation supplied as input.

Gaschütz's lemma lifts the prescribed family to topological generators of `G_K`, giving
a compatible surjection from the free profinite group on the same index type. Lyndon's
isomorphism and local reciprocity then give the relation-module surjection.

The conclusion only asserts surjectivity. Identifying the kernel with `ℤ_p[Gal(L/K)]`
requires additional information about the induced map on second cohomology.

## Main results

* `TauCeti.exists_relationModule_surjective_of_card_le`: every generating family of size at least
  `[K : ℚ_p] + 2` gives an equivariant surjection from its relation module onto `A(L)`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (5.6.6) and the proof of (7.4.2)(i).
-/

public section

namespace TauCeti

/-- For a finite Galois extension `L/K` of finite extensions of `ℚ_p`, the relation module
of every generating family of `Gal(L/K)` with at least `[K : ℚ_p] + 2` members admits a
`ℤ_p[Gal(L/K)]`-linear surjection onto the completed multiplicative group `A(L)`.
No ramification hypothesis or choice of presentation of the absolute Galois group is needed. -/
theorem exists_relationModule_surjective_of_card_le (p : ℕ) [Fact p.Prime]
    (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra ℚ_[p] K]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L] [Module.Finite ℚ_[p] L]
    [IsGalois K L] {ι : Type} [Fintype ι] {g : ι → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤)
    (hι : Module.finrank ℚ_[p] K + 2 ≤ Fintype.card ι) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[
        MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive ↑(padicCompletionUnits p L),
      Function.Surjective β := by
  classical
  have : FiniteDimensional K L := .right ℚ_[p] K L
  have : Nontrivial ℚ_[p] := DivisionRing.toNontrivial
  have : Algebra.IsAlgebraic ℚ_[p] L := Algebra.IsAlgebraic.of_finite ℚ_[p] L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  let _ := algebraicExtensionValuativeRel ℚ_[p] L
  let _ := algebraicExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  have := algebraicExtension_valuativeExtension ℚ_[p] L
  let j : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_presentation_of_card_le p K L hg hι j
  obtain ⟨β, hβ, -⟩ :=
    exists_relationModule_surjective_of_presentation p K L hg j φ hcomp hφ
  exact ⟨β, hβ⟩

end TauCeti
