/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative

/-!
# The cup product with a relative class after pulling back

Let `P = (X, A)` be a topological pair, `g : X ⟶ Z` a map and `u ∈ Hⁿ(X, A; K)` a relative class
with coefficients in a commutative ring `K`. This file defines the map

`Hᵖ(Z; M) ⟶ Hᵐ(X, A; M)`,  `a ↦ g^*a ⌣ u`,  `p + n = m`,

(`TopPair.pullbackCup`), the pull-back along `g` followed by the cup product of absolute and
relative cohomology (`TopPair.singularCup`), for any `K`-module of coefficients `M`, and proves that
it is natural in maps of pairs (`TopPair.pullbackCup_naturality`). For the Thom pair `(E, E₀)` of a
vector bundle and its projection, it is the Thom map `TauCeti.thomMap`, which the Thom isomorphism
asserts to be bijective when `u` is a Thom class.

## Main definitions and results

* `TopPair.pullbackCup`: the map `a ↦ g^*a ⌣ u`, bilinear in `u` and `a`.
* `TopPair.pullbackCup_naturality`: its naturality in maps of pairs.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe w

namespace TopPair

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- For a pair `P = (X, A)`, a map `g : X ⟶ Z` and a class `u ∈ Hⁿ(X, A; K)`, the map
`Hᵖ(Z; M) ⟶ Hᵐ(X, A; M)`, `a ↦ g^*a ⌣ u`, `p + n = m`, as a `K`-bilinear map of `u` and `a`. The
chain coefficients are `K`, and the pairing of values is the right unitor `M ⊗ K ≅ M`. -/
def pullbackCup (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) (n p m : ℕ) (h : p + n = m) :
    P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      Z.singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        P.singularCohomology (ModuleCat.of K K) K M m :=
  (P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h ∘ₗ
    (TopCat.singularCohomologyMap g p).hom).flip

variable {M}

/-- The map `a ↦ g^*a ⌣ u` is the cup product of the pull-back of `a` with `u`. -/
theorem pullbackCup_apply (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z) {n p m : ℕ}
    (h : p + n = m) (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Z.singularCohomology (ModuleCat.of K K) K M p) :
    P.pullbackCup M g n p m h u a =
      P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap g p a) u :=
  (rfl)

/-- **Naturality of `a ↦ g^*a ⌣ u`.** For a map of pairs `φ : P ⟶ P'` and maps `g : P.fst ⟶ Z`,
`g' : P'.fst ⟶ Z'` and `f : Z ⟶ Z'` with `φ ≫ g' = g ≫ f` on the ambient spaces,
`g^*(f^*a) ⌣ φ^*u = φ^*(g'^*a ⌣ u)`. -/
theorem pullbackCup_naturality {P P' : TopPair.{w}} (φ : P ⟶ P') {Z Z' : TopCat.{w}}
    (g : P.fst ⟶ Z) (g' : P'.fst ⟶ Z') (f : Z ⟶ Z') (hg : Hom.fst φ ≫ g' = g ≫ f) {n p m : ℕ}
    (h : p + n = m) (u : P'.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Z'.singularCohomology (ModuleCat.of K K) K M p) :
    P.pullbackCup M g n p m h (TopPair.singularCohomologyMap φ n u)
        (TopCat.singularCohomologyMap f p a) =
      TopPair.singularCohomologyMap φ m (P'.pullbackCup M g' n p m h u a) := by
  rw [pullbackCup_apply, pullbackCup_apply, ← TopPair.singularCup_naturality,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, ← hg,
    TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply]
  -- The two sides agree up to how the module morphisms are coerced to functions.
  rfl

end TopPair
