/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic
import TauCeti.LinearAlgebra.FreeModule.ModN

/-!
# The maximal elementary-2 quotient distributes over products

The maximal elementary-2 quotient `G / G²` of `TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic`
sends a product of commutative groups to the product of the quotients, `ZMod 2`-linearly: `(G ×
H)/(G × H)²` is `G/G² × H/H²`, and the same holds for an arbitrary indexed product. Reading `ZMod
2`-dimensions over a finite index, the **2-rank is additive**:

`TauCeti.twoRank (G × H) = TauCeti.twoRank G + TauCeti.twoRank H`

and `TauCeti.twoRank (∀ i, G i) = ∑ i, TauCeti.twoRank (G i)`.

Both structural equivalences specialize `ModN.prodLinearEquiv` and `ModN.piLinearEquiv` (from
`TauCeti.LinearAlgebra.FreeModule.ModN`) at `n = 2` on `Additive`.

This is the structural tool behind computing a class group's 2-rank from a decomposition: a finite
abelian group is a product of cyclic groups, and its 2-rank is the number of even-order factors.
For instance the class group `(ℤ/2)²` of `ℚ(√-21)` has 2-rank `1 + 1 = 2`, matching the genus
theory count `t - 1 = 3 - 1` from its `t = 3` ramified primes `2`, `3` and `7`.

## Main results

* `TauCeti.elementaryTwoQuotientProdLinearEquiv`: the `ZMod 2`-linear equivalence
  `(G × H)/(G × H)² ≃ₗ G/G² × H/H²`, with `TauCeti.twoRank_prod` and
  `TauCeti.card_elementaryTwoQuotient_prod` its dimension and cardinality readings.
* `TauCeti.elementaryTwoQuotientPiLinearEquiv`: the `ZMod 2`-linear equivalence
  `(∀ i, G i)/(…)² ≃ₗ ∀ i, (G i)/(G i)²` over an arbitrary index, with `TauCeti.twoRank_pi` and
  `TauCeti.card_elementaryTwoQuotient_pi` its dimension and cardinality readings over a finite
  index.
-/

public section

namespace TauCeti

section Prod

private theorem elementaryTwoQuotientMk_eq_modNMkQ {G : Type*} [CommGroup G] (g : G) :
    elementaryTwoQuotientMk g = ModN.mkQ 2 (Additive.ofMul g) :=
  elementaryTwoQuotientMk_eq_mkQ g

/-- **The elementary-2 quotient of a product is the product of the elementary-2 quotients.** For
commutative groups `G` and `H`, the class map identifies `(G × H)/(G × H)²` with `G/G² × H/H²`
`ZMod 2`-linearly, specializing `ModN.prodLinearEquiv` at `n = 2`. -/
noncomputable def elementaryTwoQuotientProdLinearEquiv (G H : Type*) [CommGroup G] [CommGroup H] :
    ElementaryTwoQuotient (G × H) ≃ₗ[ZMod 2]
      ElementaryTwoQuotient G × ElementaryTwoQuotient H :=
  ModN.prodLinearEquiv (Additive G) (Additive H) 2

/-- The product equivalence sends the class of `(a, b)` to the pair of classes. -/
@[simp] theorem elementaryTwoQuotientProdLinearEquiv_mk (G H : Type*) [CommGroup G] [CommGroup H]
    (p : G × H) :
    elementaryTwoQuotientProdLinearEquiv G H (elementaryTwoQuotientMk p) =
      (elementaryTwoQuotientMk p.1, elementaryTwoQuotientMk p.2) := by
  simp only [elementaryTwoQuotientProdLinearEquiv, elementaryTwoQuotientMk_eq_modNMkQ]
  exact ModN.prodLinearEquiv_mkQ (Additive G) (Additive H) 2 (Additive.ofMul p)

/-- The inverse product equivalence sends a pair of classes to the class of the pair. -/
@[simp] theorem elementaryTwoQuotientProdLinearEquiv_symm_mk (G H : Type*)
    [CommGroup G] [CommGroup H] (a : G) (b : H) : (elementaryTwoQuotientProdLinearEquiv G H).symm
        (elementaryTwoQuotientMk a, elementaryTwoQuotientMk b) =
      elementaryTwoQuotientMk (a, b) := by
  rw [LinearEquiv.symm_apply_eq, elementaryTwoQuotientProdLinearEquiv_mk]

/-- **The 2-rank is additive over products.** For commutative groups whose elementary-2 quotients
are finite-dimensional, `twoRank (G × H) = twoRank G + twoRank H`. -/
theorem twoRank_prod (G H : Type*) [CommGroup G] [CommGroup H]
    [Module.Finite (ZMod 2) (ElementaryTwoQuotient G)]
    [Module.Finite (ZMod 2) (ElementaryTwoQuotient H)] :
    twoRank (G × H) = twoRank G + twoRank H := by
  rw [twoRank_def, (elementaryTwoQuotientProdLinearEquiv G H).finrank_eq, Module.finrank_prod,
    ← twoRank_def, ← twoRank_def]

/-- The cardinality reading of `TauCeti.elementaryTwoQuotientProdLinearEquiv`:
`|(G × H)/(G × H)²| = |G/G²| · |H/H²|`. -/
theorem card_elementaryTwoQuotient_prod (G H : Type*) [CommGroup G] [CommGroup H] :
    Nat.card (ElementaryTwoQuotient (G × H)) =
      Nat.card (ElementaryTwoQuotient G) * Nat.card (ElementaryTwoQuotient H) := by
  rw [Nat.card_congr (elementaryTwoQuotientProdLinearEquiv G H).toEquiv, Nat.card_prod]

end Prod

section Pi

variable {ι : Type*} (G : ι → Type*) [∀ i, CommGroup (G i)]

/-- **The elementary-2 quotient of an indexed product is the product of the elementary-2
quotients.** For a family of commutative groups `G i` over an arbitrary index, the class map
identifies `(∀ i, G i)/(…)²` with `∀ i, (G i)/(G i)²` `ZMod 2`-linearly, specializing
`ModN.piLinearEquiv` at `n = 2`. -/
noncomputable def elementaryTwoQuotientPiLinearEquiv :
    ElementaryTwoQuotient (∀ i, G i) ≃ₗ[ZMod 2] ∀ i, ElementaryTwoQuotient (G i) :=
  ModN.piLinearEquiv (fun i ↦ Additive (G i)) 2

/-- The indexed-product equivalence sends the class of `g` to the family of componentwise
classes. -/
@[simp] theorem elementaryTwoQuotientPiLinearEquiv_mk (g : ∀ i, G i) :
    elementaryTwoQuotientPiLinearEquiv G (elementaryTwoQuotientMk g) =
      fun i => elementaryTwoQuotientMk (g i) := by
  simp only [elementaryTwoQuotientPiLinearEquiv, elementaryTwoQuotientMk_eq_modNMkQ]
  exact ModN.piLinearEquiv_mkQ (fun i ↦ Additive (G i)) 2 (Additive.ofMul g)

/-- The inverse indexed-product equivalence sends a family of componentwise classes to the class
of the assembled family. -/
@[simp] theorem elementaryTwoQuotientPiLinearEquiv_symm_mk (g : ∀ i, G i) :
    (elementaryTwoQuotientPiLinearEquiv G).symm (fun i => elementaryTwoQuotientMk (g i)) =
      elementaryTwoQuotientMk g := by
  rw [LinearEquiv.symm_apply_eq, elementaryTwoQuotientPiLinearEquiv_mk]

/-- **The 2-rank is additive over finite indexed products.** For a finite family of commutative
groups whose elementary-2 quotients are finite-dimensional,
`twoRank (∀ i, G i) = ∑ i, twoRank (G i)`. -/
theorem twoRank_pi [Fintype ι] [∀ i, Module.Finite (ZMod 2) (ElementaryTwoQuotient (G i))] :
    twoRank (∀ i, G i) = ∑ i, twoRank (G i) := by
  rw [twoRank_def, (elementaryTwoQuotientPiLinearEquiv G).finrank_eq, Module.finrank_pi_fintype]
  simp only [twoRank_def]

/-- The cardinality reading of `TauCeti.elementaryTwoQuotientPiLinearEquiv`:
`|(∀ i, G i)/(…)²| = ∏ i, |(G i)/(G i)²|`. -/
theorem card_elementaryTwoQuotient_pi [Fintype ι] :
    Nat.card (ElementaryTwoQuotient (∀ i, G i)) =
      ∏ i, Nat.card (ElementaryTwoQuotient (G i)) := by
  rw [Nat.card_congr (elementaryTwoQuotientPiLinearEquiv G).toEquiv, Nat.card_pi]

end Pi

end TauCeti
