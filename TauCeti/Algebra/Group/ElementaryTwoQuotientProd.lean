/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.Algebra.Group.ElementaryTwoQuotient

/-!
# The maximal elementary-2 quotient distributes over products

The maximal elementary-2 quotient `G / G²` of `TauCeti.Algebra.Group.ElementaryTwoQuotient` sends a
product of commutative groups to the product of the quotients, `ZMod 2`-linearly: `(G × H)/(G × H)²`
is `G/G² × H/H²`, and the same holds for a finite indexed product. Reading `ZMod 2`-dimensions, the
**2-rank is additive**:

`TauCeti.twoRank (G × H) = TauCeti.twoRank G + TauCeti.twoRank H`

and `TauCeti.twoRank (∀ i, G i) = ∑ i, TauCeti.twoRank (G i)`.

This is the structural tool behind computing a class group's 2-rank from a decomposition: a finite
abelian group is a product of cyclic groups, and its 2-rank is the number of even-order factors.
This product additivity supports the Layer 2 class-group quotient API and the later Layer 3
genus-field/2-rank theorem in the multiquadratic roadmap. For instance the class group `(ℤ/2)²`
of `ℚ(√-21)` has 2-rank `1 + 1 = 2`, matching the `t - 1 = 3 - 1` count of ramified primes in the
worked examples.

## Main results

* `TauCeti.elementaryTwoQuotientProdLinearEquiv`: the `ZMod 2`-linear equivalence
  `(G × H)/(G × H)² ≃ₗ G/G² × H/H²`, with `TauCeti.twoRank_prod` and
  `TauCeti.card_elementaryTwoQuotient_prod` its dimension and cardinality readings.
* `TauCeti.elementaryTwoQuotientPiLinearEquiv`: the `ZMod 2`-linear equivalence
  `(∀ i, G i)/(…)² ≃ₗ ∀ i, (G i)/(G i)²` over a finite index, with `TauCeti.twoRank_pi` and
  `TauCeti.card_elementaryTwoQuotient_pi` its dimension and cardinality readings.
-/

public section

namespace TauCeti

/-- The induced map of a trivial homomorphism is the zero map. -/
private theorem elementaryTwoQuotientMap_one_apply {A B : Type*} [CommGroup A] [CommGroup B]
    (x : ElementaryTwoQuotient A) :
    elementaryTwoQuotientMap (1 : A →* B) x = 0 := by
  obtain ⟨a, rfl⟩ := elementaryTwoQuotientMk_surjective (G := A) x
  rw [elementaryTwoQuotientMap_mk]
  simp

section Prod

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- The product of the two structural inclusions recovers a pair: `inl a * inr b = (a, b)`. -/
private theorem inl_mul_inr_eq (a : G) (b : H) :
    MonoidHom.inl G H a * MonoidHom.inr G H b = (a, b) := by
  ext <;> simp

/-- **The elementary-2 quotient of a product is the product of the elementary-2 quotients.** For
commutative groups `G` and `H`, the class map identifies `(G × H)/(G × H)²` with `G/G² × H/H²`
`ZMod 2`-linearly: the projections `G × H → G`, `G × H → H` induce the two components, and the
inclusions `a ↦ (a, 1)`, `b ↦ (1, b)` induce the inverse. -/
noncomputable def elementaryTwoQuotientProdLinearEquiv (G H : Type*) [CommGroup G] [CommGroup H] :
    ElementaryTwoQuotient (G × H) ≃ₗ[ZMod 2]
      ElementaryTwoQuotient G × ElementaryTwoQuotient H where
  toFun x :=
    (elementaryTwoQuotientMap (MonoidHom.fst G H) x,
      elementaryTwoQuotientMap (MonoidHom.snd G H) x)
  map_add' x y := by
    simp only [map_add, Prod.mk_add_mk]
  map_smul' c x := by
    simp only [map_smul, Prod.smul_mk, RingHom.id_apply]
  invFun p :=
    elementaryTwoQuotientMap (MonoidHom.inl G H) p.1 +
      elementaryTwoQuotientMap (MonoidHom.inr G H) p.2
  left_inv x := by
    obtain ⟨p, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G × H) x
    simp only [elementaryTwoQuotientMap_mk, ← elementaryTwoQuotientMk_mul, inl_mul_inr_eq,
      MonoidHom.coe_fst, MonoidHom.coe_snd, Prod.mk.eta]
  right_inv p := by
    obtain ⟨u, v⟩ := p
    obtain ⟨a, rfl⟩ := elementaryTwoQuotientMk_surjective (G := G) u
    obtain ⟨b, rfl⟩ := elementaryTwoQuotientMk_surjective (G := H) v
    simp only [elementaryTwoQuotientMap_mk, ← elementaryTwoQuotientMk_mul, inl_mul_inr_eq,
      MonoidHom.coe_fst, MonoidHom.coe_snd]

/-- The product equivalence sends the class of `(a, b)` to the pair of classes. -/
@[simp] theorem elementaryTwoQuotientProdLinearEquiv_mk (G H : Type*) [CommGroup G] [CommGroup H]
    (p : G × H) :
    elementaryTwoQuotientProdLinearEquiv G H (elementaryTwoQuotientMk p) =
      (elementaryTwoQuotientMk p.1, elementaryTwoQuotientMk p.2) := by
  simp only [elementaryTwoQuotientProdLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, elementaryTwoQuotientMap_mk, MonoidHom.coe_fst, MonoidHom.coe_snd]

/-- The inverse product equivalence sends a pair of classes to the class of the pair. -/
@[simp] theorem elementaryTwoQuotientProdLinearEquiv_symm_mk (G H : Type*)
    [CommGroup G] [CommGroup H] (a : G) (b : H) :
    (elementaryTwoQuotientProdLinearEquiv G H).symm
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

variable {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, CommGroup (G i)]

omit [Fintype ι] in
/-- Evaluating at `j` after the single-support inclusion at `j` is the identity. -/
private theorem evalMonoidHom_comp_mulSingle_self [DecidableEq ι] (j : ι) :
    (Pi.evalMonoidHom G j).comp (MonoidHom.mulSingle G j) = MonoidHom.id (G j) := by
  ext x
  simp [Pi.mulSingle_eq_same]

omit [Fintype ι] in
/-- Evaluating at `j` after the single-support inclusion at a different index is trivial. -/
private theorem evalMonoidHom_comp_mulSingle_ne [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    (Pi.evalMonoidHom G j).comp (MonoidHom.mulSingle G i) = 1 := by
  ext x
  simp [Pi.mulSingle_eq_of_ne (Ne.symm h)]

/-- **The elementary-2 quotient of a finite indexed product is the product of the elementary-2
quotients.** For a finite family of commutative groups `G i`, the class map identifies
`(∀ i, G i)/(…)²` with `∀ i, (G i)/(G i)²` `ZMod 2`-linearly: the evaluation maps induce the
components, and the single-support inclusions `Pi.mulSingle` induce the inverse. -/
noncomputable def elementaryTwoQuotientPiLinearEquiv :
    ElementaryTwoQuotient (∀ i, G i) ≃ₗ[ZMod 2] ∀ i, ElementaryTwoQuotient (G i) := by
  classical
  exact
    { toFun := fun x i => elementaryTwoQuotientMap (Pi.evalMonoidHom G i) x
      map_add' := by
        intro x y
        funext i
        simp only [map_add, Pi.add_apply]
      map_smul' := by
        intro c x
        funext i
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply]
      invFun := fun p => ∑ i, elementaryTwoQuotientMap (MonoidHom.mulSingle G i) (p i)
      left_inv := by
        intro x
        obtain ⟨g, rfl⟩ := elementaryTwoQuotientMk_surjective (G := ∀ i, G i) x
        simp only [elementaryTwoQuotientMap_mk]
        rw [← elementaryTwoQuotientMk_prod]
        exact congrArg _ (Finset.univ_prod_mulSingle g)
      right_inv := by
        intro p
        funext j
        -- Beta-reduce the bundled `toFun`/`invFun` at index `j` so `map_sum` can fire on the sum.
        change elementaryTwoQuotientMap (Pi.evalMonoidHom G j)
            (∑ i, elementaryTwoQuotientMap (MonoidHom.mulSingle G i) (p i)) = p j
        rw [map_sum, Finset.sum_eq_single j]
        · rw [← elementaryTwoQuotientMap_comp_apply, evalMonoidHom_comp_mulSingle_self,
            elementaryTwoQuotientMap_id_apply]
        · intro i _ hij
          rw [← elementaryTwoQuotientMap_comp_apply, evalMonoidHom_comp_mulSingle_ne G hij]
          rw [elementaryTwoQuotientMap_one_apply]
        · intro hj
          exact absurd (Finset.mem_univ j) hj }

/-- The indexed-product equivalence sends the class of `g` to the family of componentwise
classes. -/
@[simp] theorem elementaryTwoQuotientPiLinearEquiv_mk (g : ∀ i, G i) :
    elementaryTwoQuotientPiLinearEquiv G (elementaryTwoQuotientMk g) =
      fun i => elementaryTwoQuotientMk (g i) := by
  funext i
  simp only [elementaryTwoQuotientPiLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, elementaryTwoQuotientMap_mk, Pi.evalMonoidHom_apply]

/-- The inverse indexed-product equivalence sends a family of componentwise classes to the class
of the assembled family. -/
@[simp] theorem elementaryTwoQuotientPiLinearEquiv_symm_mk (g : ∀ i, G i) :
    (elementaryTwoQuotientPiLinearEquiv G).symm (fun i => elementaryTwoQuotientMk (g i)) =
      elementaryTwoQuotientMk g := by
  classical
  rw [LinearEquiv.symm_apply_eq, elementaryTwoQuotientPiLinearEquiv_mk]

/-- **The 2-rank is additive over finite indexed products.** For a finite family of commutative
groups whose elementary-2 quotients are finite-dimensional,
`twoRank (∀ i, G i) = ∑ i, twoRank (G i)`. -/
theorem twoRank_pi [∀ i, Module.Finite (ZMod 2) (ElementaryTwoQuotient (G i))] :
    twoRank (∀ i, G i) = ∑ i, twoRank (G i) := by
  classical
  rw [twoRank_def, (elementaryTwoQuotientPiLinearEquiv G).finrank_eq, Module.finrank_pi_fintype]
  simp only [twoRank_def]

/-- The cardinality reading of `TauCeti.elementaryTwoQuotientPiLinearEquiv`:
`|(∀ i, G i)/(…)²| = ∏ i, |(G i)/(G i)²|`. -/
theorem card_elementaryTwoQuotient_pi :
    Nat.card (ElementaryTwoQuotient (∀ i, G i)) =
      ∏ i, Nat.card (ElementaryTwoQuotient (G i)) := by
  classical
  rw [Nat.card_congr (elementaryTwoQuotientPiLinearEquiv G).toEquiv, Nat.card_pi]

end Pi

end TauCeti
