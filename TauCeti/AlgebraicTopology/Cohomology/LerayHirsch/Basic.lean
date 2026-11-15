/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Pullback

/-!
# The Leray–Hirsch map of a pair

Let `P = (X, A)` be a topological pair, `g : X ⟶ Z` a map and `c p : ι p → Hᵖ(X, A; K)` a family
of classes with coefficients in a commutative ring `K`, indexed by a type `ι p` in each degree
`p`. The **Leray–Hirsch map** of these classes in degree `n` is

`⨁_{p + q = n} ⨁_{i : ι p} H^q(Z; M) ⟶ Hⁿ(X, A; M)`,  `(a_{p,i}) ↦ ∑ g^*a_{p,i} ⌣ c p i`,

(`TopPair.lerayHirsch`), for any `K`-module of coefficients `M`; each summand is the map
`a ↦ g^*a ⌣ c p i` of `TopPair.pullbackCup`. When `g` is the projection of a fibre bundle, `A` is
empty, the cohomology of the fibre is free and finitely generated in each degree and the classes
restrict on every fibre to a basis of it, the Leray–Hirsch theorem asserts that this map is
bijective. For the Thom pair of a vector bundle and a single Thom
class it is the Thom map `TauCeti.thomMap`. The trivial-bundle case with absolute classes is
`TopCat.lerayHirschProdOfClasses_bijective`.

The source `⨁_{p + q = n} ⨁_{i : ι p} H^q(Z; M)` is `TopCat.LerayHirschSource`, on which a map
`f : Z ⟶ Z'` acts summandwise by pull-back (`TopCat.lerayHirschSourceMap`). The Leray–Hirsch map
is natural in maps of pairs covering maps of the targets (`TopPair.lerayHirsch_naturality`), so its
bijectivity is invariant under isomorphisms (`TopPair.bijective_lerayHirsch_iff_of_isIso`). That
it is bijective is local on the base, by Mayer–Vietoris; this is in
`TauCeti.AlgebraicTopology.Cohomology.LerayHirsch.MayerVietoris`.

## Main definitions and results

* `TopCat.LerayHirschSource`, `TopCat.lerayHirschSourceMap`: the source of the Leray–Hirsch map
  and the summandwise pull-back on it.
* `TopPair.lerayHirsch`: the Leray–Hirsch map of a pair, a map and a family of classes,
  characterized on summands by `TopPair.lerayHirsch_lof`.
* `TopPair.lerayHirsch_naturality`, `TopPair.bijective_lerayHirsch_iff_of_isIso`: naturality and
  invariance of bijectivity under isomorphisms.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4D.1 (Leray–Hirsch).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory TopCat
open scoped DirectSum

universe w

namespace TopCat

variable {K : Type w} [CommRing K]

/-! ### The source of the Leray–Hirsch map -/

/-- The source `⨁_{p + q = n} ⨁_{i : ι p} H^q(Z; M)` of the Leray–Hirsch map in degree `n` for a
family of classes indexed by `ι p` in each degree `p`. The summand indexed by `p + q = n` and
`i : ι p` carries the base degree `q`. -/
abbrev LerayHirschSource (Z : TopCat.{w}) (M : ModuleCat.{w} K) (ι : ℕ → Type w) (n : ℕ) :
    Type w :=
  ⨁ j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1,
    Z.singularCohomology (ModuleCat.of K K) K M j.1.1.2

variable {M : ModuleCat.{w} K} {ι : ℕ → Type w}

/-- The pull-back `f^*` along `f : Z ⟶ Z'`, applied in each summand of the source of the
Leray–Hirsch map. -/
def lerayHirschSourceMap {Z Z' : TopCat.{w}} (f : Z ⟶ Z') (n : ℕ) :
    Z'.LerayHirschSource M ι n →ₗ[K] Z.LerayHirschSource M ι n :=
  DirectSum.lmap (R := K)
    (M := fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
      Z'.singularCohomology (ModuleCat.of K K) K M j.1.1.2)
    (N := fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
      Z.singularCohomology (ModuleCat.of K K) K M j.1.1.2)
    fun j ↦ (TopCat.singularCohomologyMap f j.1.1.2).hom

/-- The pull-back on the source of the Leray–Hirsch map acts on each component. -/
@[simp]
theorem lerayHirschSourceMap_apply {Z Z' : TopCat.{w}} (f : Z ⟶ Z') {n : ℕ}
    (a : Z'.LerayHirschSource M ι n) (j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1) :
    lerayHirschSourceMap f n a j = TopCat.singularCohomologyMap f j.1.1.2 (a j) :=
  (rfl)

/-- The pull-back on the source of the Leray–Hirsch map is bijective along an isomorphism. -/
theorem bijective_lerayHirschSourceMap {Z Z' : TopCat.{w}} (f : Z ⟶ Z') [IsIso f] (n : ℕ) :
    Function.Bijective (lerayHirschSourceMap (M := M) (ι := ι) f n) :=
  ⟨(DirectSum.lmap_injective _).2 fun j ↦ ((TauCeti.singularCohomologyFunctor _ K M
      j.1.1.2).mapIso (asIso f).op).toLinearEquiv.injective,
    (DirectSum.lmap_surjective _).2 fun j ↦ ((TauCeti.singularCohomologyFunctor _ K M
      j.1.1.2).mapIso (asIso f).op).toLinearEquiv.surjective⟩

variable [∀ p, DecidableEq (ι p)]

/-- The pull-back on the source of the Leray–Hirsch map preserves the summands. -/
@[simp]
theorem lerayHirschSourceMap_lof {Z Z' : TopCat.{w}} (f : Z ⟶ Z') {n : ℕ}
    (j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1)
    (a : Z'.singularCohomology (ModuleCat.of K K) K M j.1.1.2) :
    lerayHirschSourceMap f n (DirectSum.lof K _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦ Z'.singularCohomology (ModuleCat.of K K) K M j.1.1.2) j a) =
      DirectSum.lof K _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n}, ι pq.1.1 ↦
        Z.singularCohomology (ModuleCat.of K K) K M j.1.1.2) j
        (TopCat.singularCohomologyMap f j.1.1.2 a) := by
  rw [lerayHirschSourceMap, DirectSum.lmap_lof]

end TopCat

namespace TopPair

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K) {ι : ℕ → Type w}
  [∀ p, DecidableEq (ι p)]

/-! ### The Leray–Hirsch map of a pair -/

section Definition

/-- **The Leray–Hirsch map** of a pair `P = (X, A)`, a map `g : X ⟶ Z` and a family of classes
`c p : ι p → Hᵖ(X, A; K)`, in degree `n`,
`⨁_{p + q = n} ⨁_{i : ι p} H^q(Z; M) ⟶ Hⁿ(X, A; M)`, sending `a` in the summand indexed by
`p + q = n` and `i : ι p` to `g^*a ⌣ c p i` (`TopPair.pullbackCup`). -/
def lerayHirsch (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z)
    (c : ∀ p, ι p → P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) (n : ℕ) :
    Z.LerayHirschSource M ι n →ₗ[K] P.singularCohomology (ModuleCat.of K K) K M n :=
  DirectSum.toModule K _ _ fun j ↦
    P.pullbackCup M g j.1.1.1 j.1.1.2 n ((add_comm _ _).trans j.1.2) (c j.1.1.1 j.2)

variable {M}

/-- The Leray–Hirsch map sends `a` in the summand indexed by `p + q = n` and `i : ι p` to
`g^*a ⌣ c p i`. -/
@[simp]
theorem lerayHirsch_lof (P : TopPair.{w}) {Z : TopCat.{w}} (g : P.fst ⟶ Z)
    (c : ∀ p, ι p → P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) {n : ℕ}
    (p q : ℕ) (h : p + q = n) (i : ι p) (a : Z.singularCohomology (ModuleCat.of K K) K M q) :
    P.lerayHirsch M g c n (DirectSum.lof K _ (fun j : Σ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
        ι pq.1.1 ↦ Z.singularCohomology (ModuleCat.of K K) K M j.1.1.2) ⟨⟨(p, q), h⟩, i⟩ a) =
      P.pullbackCup M g p q n (by rw [add_comm, h]) (c p i) a := by
  simp [lerayHirsch]

/-- **Naturality of the Leray–Hirsch map.** For a map of pairs `φ : P ⟶ P'` and maps
`g : P.fst ⟶ Z`, `g' : P'.fst ⟶ Z'` and `f : Z ⟶ Z'` with `φ ≫ g' = g ≫ f` on the ambient spaces,
the Leray–Hirsch map of the classes `φ^* c` at the componentwise pull-back `f^* a` is the
pull-back along `φ` of the Leray–Hirsch map of the classes `c` at `a`. -/
theorem lerayHirsch_naturality {P P' : TopPair.{w}} (φ : P ⟶ P') {Z Z' : TopCat.{w}}
    (g : P.fst ⟶ Z) (g' : P'.fst ⟶ Z') (f : Z ⟶ Z') (hg : Hom.fst φ ≫ g' = g ≫ f)
    (c : ∀ p, ι p → P'.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) (n : ℕ)
    (a : Z'.LerayHirschSource M ι n) :
    P.lerayHirsch M g (fun p i ↦ TopPair.singularCohomologyMap φ p (c p i)) n
        (lerayHirschSourceMap f n a) =
      TopPair.singularCohomologyMap φ n (P'.lerayHirsch M g' c n a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    obtain ⟨⟨⟨p, q⟩, h⟩, i⟩ := j
    rw [← DirectSum.lof_eq_of K, lerayHirschSourceMap_lof, lerayHirsch_lof, lerayHirsch_lof]
    exact pullbackCup_naturality φ g g' f hg _ (c p i) x
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Bijectivity of the Leray–Hirsch map is invariant under isomorphisms `φ : P ⟶ P'` of pairs and
`f : Z ⟶ Z'` of targets with `φ ≫ g' = g ≫ f` on the ambient spaces. -/
theorem bijective_lerayHirsch_iff_of_isIso {P P' : TopPair.{w}} (φ : P ⟶ P') {Z Z' : TopCat.{w}}
    {g : P.fst ⟶ Z} {g' : P'.fst ⟶ Z'} (f : Z ⟶ Z') [IsIso φ] [IsIso f]
    (hg : Hom.fst φ ≫ g' = g ≫ f)
    (c : ∀ p, ι p → P'.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) (n : ℕ) :
    Function.Bijective
        (P.lerayHirsch M g (fun p i ↦ TopPair.singularCohomologyMap φ p (c p i)) n) ↔
      Function.Bijective (P'.lerayHirsch M g' c n) := by
  have hf := bijective_lerayHirschSourceMap (M := M) (ι := ι) f n
  have hφ : Function.Bijective (TopPair.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
      (M := M) φ n) :=
    ((TopPair.singularCohomologyFunctor _ K M n).mapIso (asIso φ).op).toLinearEquiv.bijective
  have hc : ⇑(P.lerayHirsch M g (fun p i ↦ TopPair.singularCohomologyMap φ p (c p i)) n) ∘
      ⇑(lerayHirschSourceMap f n) = TopPair.singularCohomologyMap φ n ∘ P'.lerayHirsch M g' c n :=
    funext fun a ↦ lerayHirsch_naturality φ g g' f hg c n a
  constructor
  · intro h'
    have := h'.comp hf
    rw [hc] at this
    exact (Function.Bijective.of_comp_iff' hφ _).1 this
  · intro h'
    have := hφ.comp h'
    rw [← hc] at this
    exact (Function.Bijective.of_comp_iff _ hf).1 this

end Definition

end TopPair

