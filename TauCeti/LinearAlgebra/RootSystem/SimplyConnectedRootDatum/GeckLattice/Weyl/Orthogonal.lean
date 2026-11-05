/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.SimpleRootRelations

/-!
# Orthogonal Weyl representatives in the Geck carrier

The pinned simple Weyl representative at one Bourbaki node centralizes both root subgroups at an
orthogonal node. Consequently the two representatives commute: this is the length-two braid
relation inside the carrier, not merely a relation between their images in the Weyl group.

These identities are used when collecting words in the root subgroups and torus normalizer.
They hold over every commutative value ring, including rings of bad characteristic and
nonreduced rings. They do not assert that arbitrary Weyl words with the same Weyl-group image
have equal representatives.

The proofs use the zero-pairing Chevalley relations in
`GeckLattice.SimpleRootRelations` and the pinned root word from `GeckLattice.Weyl.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType

universe v

variable (t : DynkinType) (ht : t.Valid)

/-- A pinned simple Weyl representative commutes with the raising subgroup at an orthogonal
Bourbaki node. -/
theorem commute_geckSimpleWeylPoint_geckSimpleRaisingPoints (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = 0) (A : Type v) [CommRing A] (u : Multiplicative A) :
    Commute (t.geckSimpleWeylPoint ht i A) (t.geckRootSubgroupPoints ht (.inl j) A u) := by
  have hne : i ≠ j := by
    rintro rfl
    simp at hij
  rw [geckSimpleWeylPoint_def]
  exact ((t.commute_geckSimpleRaisingPoints ht i j hij A _ u).mul_left
    (t.commute_geckSimpleLowering_raisingPoints ht i j hne A _ u)).mul_left
      (t.commute_geckSimpleRaisingPoints ht i j hij A _ u)

/-- A pinned simple Weyl representative commutes with the lowering subgroup at an orthogonal
Bourbaki node. -/
theorem commute_geckSimpleWeylPoint_geckSimpleLoweringPoints (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = 0) (A : Type v) [CommRing A] (u : Multiplicative A) :
    Commute (t.geckSimpleWeylPoint ht i A) (t.geckRootSubgroupPoints ht (.inr j) A u) := by
  have hne : i ≠ j := by
    rintro rfl
    simp at hij
  rw [geckSimpleWeylPoint_def]
  exact ((t.commute_geckSimpleRaising_loweringPoints ht i j hne A _ u).mul_left
    (t.commute_geckSimpleLoweringPoints ht i j hij A _ u)).mul_left
      (t.commute_geckSimpleRaising_loweringPoints ht i j hne A _ u)

/-- **The length-two braid relation in the Geck carrier.** Pinned simple Weyl representatives
at orthogonal Bourbaki nodes commute over every commutative ring. -/
theorem commute_geckSimpleWeylPoint (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = 0) (A : Type v) [CommRing A] :
    Commute (t.geckSimpleWeylPoint ht i A) (t.geckSimpleWeylPoint ht j A) := by
  rw [geckSimpleWeylPoint_def t ht j]
  exact ((t.commute_geckSimpleWeylPoint_geckSimpleRaisingPoints ht i j hij A _).mul_right
    (t.commute_geckSimpleWeylPoint_geckSimpleLoweringPoints ht i j hij A _)).mul_right
      (t.commute_geckSimpleWeylPoint_geckSimpleRaisingPoints ht i j hij A _)

end TauCeti.DynkinType
