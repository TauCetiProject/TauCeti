/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# The Thom map of a pair over a base

Let `P = (X, A)` be a pair of spaces, `π : X ⟶ Y` a map to a base and `u ∈ Hⁿ(X, A; K)` a relative
class with coefficients in a commutative ring `K`. The **Thom map** of `u` is

`Φ_u : Hᵖ(Y; M) ⟶ Hᵖ⁺ⁿ(X, A; M)`,  `a ↦ π^*a ⌣ u`

(`TopPair.thomMap`), for any `K`-module of coefficients `M`. It sends the unit `1 ∈ H⁰(Y; K)` to
`u` (`TopPair.thomMap_one`). It is natural in maps of pairs over
maps of bases (`TopPair.thomMap_naturality`), so its bijectivity is invariant under isomorphisms
(`TopPair.bijective_thomMap_iff_of_isIso`). For the Thom pair `(E, E₀)` of a vector bundle over its
projection, and `u` a Thom class, it is the map `TauCeti.thomMap` of the Thom isomorphism.

For a subset `Z ⊆ X` and a subset `S ⊆ Y` of the base, restricting `u ∈ Hⁿ(X, Z)` to the pair
`(π⁻¹ S, π⁻¹ S ∩ Z)` over the restriction `π⁻¹ S ⟶ S` of `π` gives the **Thom map over `S`**
(`TopCat.thomMapRestrict`). For a vector bundle and `Z` its nonzero vectors, this pair is the Thom
pair `(E|_S, E₀|_S)` of the restriction of the bundle to `S`. The Mayer–Vietoris gluing step for
these maps is in `TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Thom`.

## Main definitions and results

* `TopPair.thomMap`: the Thom map `a ↦ π^*a ⌣ u` of a pair over a base.
* `TopPair.thomMap_one`: `Φ_u(1) = u`.
* `TopPair.thomMap_naturality`, `TopPair.bijective_thomMap_iff_of_isIso`: naturality and invariance
  of bijectivity under isomorphisms.
* `TopCat.thomMapRestrict`: the Thom map over a subset of the base.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.D.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe w

namespace TopPair

variable {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom map** of a pair `P = (X, A)` over a base `π : X ⟶ Y`: for a relative class
`u ∈ Hⁿ(X, A; K)`, the map `Hᵖ(Y; M) ⟶ Hᵐ(X, A; M)`, `a ↦ π^*a ⌣ u`, `p + n = m`, as a
`K`-bilinear map of `u` and `a`. -/
def thomMap (P : TopPair.{w}) {Y : TopCat.{w}} (π : P.fst ⟶ Y) (n p m : ℕ) (h : p + n = m) :
    P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      Y.singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        P.singularCohomology (ModuleCat.of K K) K M m :=
  (P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h ∘ₗ
    (TopCat.singularCohomologyMap π p).hom).flip

variable {M}

/-- The Thom map is the cup product of the pull-back to `X` with `u`. -/
theorem thomMap_apply (P : TopPair.{w}) {Y : TopCat.{w}} (π : P.fst ⟶ Y) {n p m : ℕ}
    (h : p + n = m) (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Y.singularCohomology (ModuleCat.of K K) K M p) :
    P.thomMap M π n p m h u a =
      P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap π p a) u :=
  (rfl)

/-- **The Thom map sends `1` to `u`**: the image of the class of the constant `0`-cocycle with
value `1 ∈ K` is `u`. -/
@[simp]
theorem thomMap_one (P : TopPair.{w}) {Y : TopCat.{w}} (π : P.fst ⟶ Y) {n : ℕ} (h : 0 + n = n)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    P.thomMap (ModuleCat.of K K) π n 0 n h u
        ((Y.singularCochainComplex (ModuleCat.of K K) K (ModuleCat.of K K)).homologyπ 0
          (Y.constSingularCocycle K (𝟙 (ModuleCat.of K K)))) = u := by
  rw [thomMap_apply]
  refine (congrArg (fun x ↦ P.singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
    (ρ_ (ModuleCat.of K K)).hom 0 n n h x u)
    (TopCat.singularCohomologyMap_homologyπ_constSingularCocycle π K
      (𝟙 (ModuleCat.of K K)))).trans ?_
  exact P.singularCup_constSingularCocycle_left K (η := 𝟙 _) (by monoidal) (by monoidal) h u

/-- **Naturality of the Thom map.** A map of pairs `φ : P' ⟶ P` covering a map of bases
`g : Y' ⟶ Y` intertwines the Thom map of `u` with that of its pull-back `φ^*u`:
`Φ_{φ^*u}(g^*a) = φ^*Φ_u(a)`. -/
theorem thomMap_naturality {P P' : TopPair.{w}} {Y Y' : TopCat.{w}} {π : P.fst ⟶ Y}
    {π' : P'.fst ⟶ Y'} (φ : P' ⟶ P) (g : Y' ⟶ Y) (hφ : Hom.fst φ ≫ π = π' ≫ g) {n p m : ℕ}
    (h : p + n = m) (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : Y.singularCohomology (ModuleCat.of K K) K M p) :
    P'.thomMap M π' n p m h (TopPair.singularCohomologyMap φ n u)
        (TopCat.singularCohomologyMap g p a) =
      TopPair.singularCohomologyMap φ m (P.thomMap M π n p m h u a) := by
  rw [thomMap_apply, thomMap_apply, ← singularCup_naturality, ← ConcreteCategory.comp_apply,
    ← TopCat.singularCohomologyMap_comp, ← hφ, TopCat.singularCohomologyMap_comp,
    ConcreteCategory.comp_apply]
  rfl

/-- Bijectivity of the Thom map is invariant under isomorphisms of pairs over isomorphisms of
bases. -/
theorem bijective_thomMap_iff_of_isIso {P P' : TopPair.{w}} {Y Y' : TopCat.{w}} {π : P.fst ⟶ Y}
    {π' : P'.fst ⟶ Y'} (φ : P' ⟶ P) (g : Y' ⟶ Y) [IsIso φ] [IsIso g]
    (hφ : Hom.fst φ ≫ π = π' ≫ g) {n p m : ℕ} (h : p + n = m)
    (u : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (P'.thomMap M π' n p m h (TopPair.singularCohomologyMap φ n u)) ↔
      Function.Bijective (P.thomMap M π n p m h u) := by
  have hg : Function.Bijective (TopCat.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
      (M := M) g p) :=
    ((TauCeti.singularCohomologyFunctor _ K _ p).mapIso (asIso g).op).toLinearEquiv.bijective
  have hφ' : Function.Bijective (TopPair.singularCohomologyMap (R := ModuleCat.of K K) (k := K)
      (M := M) φ m) :=
    ((TopPair.singularCohomologyFunctor _ K _ m).mapIso (asIso φ).op).toLinearEquiv.bijective
  have hc : ⇑(P'.thomMap M π' n p m h (TopPair.singularCohomologyMap φ n u)) ∘
      TopCat.singularCohomologyMap g p =
        TopPair.singularCohomologyMap φ m ∘ P.thomMap M π n p m h u :=
    funext fun a ↦ thomMap_naturality φ g hφ h u a
  constructor
  · intro h'
    have := h'.comp hg
    rw [hc] at this
    exact (Function.Bijective.of_comp_iff' hφ' _).1 this
  · intro h'
    have := hφ'.comp h'
    rw [← hc] at this
    exact (Function.Bijective.of_comp_iff _ hg).1 this

end TopPair

namespace TopCat

variable {K : Type w} [CommRing K] {X Y : TopCat.{w}} (π : X ⟶ Y) (Z : Set X)

/-! ### Restriction over a subset of the base -/

section Restrict

variable (M : ModuleCat.{w} K)

/-- The Thom map over a subset `S` of the base: the Thom map of the restriction of
`u ∈ Hⁿ(X, Z)` to the pair `(π⁻¹ S, π⁻¹ S ∩ Z)` over the restriction `π⁻¹ S ⟶ S` of `π`, from
`Hᵖ(S; M)` to `Hᵐ(π⁻¹ S, π⁻¹ S ∩ Z; M)`. -/
def thomMapRestrict (S : Set Y) (n p m : ℕ) (h : p + n = m) :
    (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (of S).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).singularCohomology
          (ModuleCat.of K K) K M m :=
  (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).thomMap M
      (ofHom (π.hom.restrictPreimage S)) n p m h ∘ₗ
    (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n).hom

variable {M} in
/-- The Thom map over `S` is the Thom map of the restriction of `u` to the pair over `S`. -/
theorem thomMapRestrict_apply (S : Set Y) {n p m : ℕ} (h : p + n = m)
    (u : (TopPair.ofSubset Z).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (of S).singularCohomology (ModuleCat.of K K) K M p) :
    thomMapRestrict π Z M S n p m h u a =
      (TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)).thomMap M
        (ofHom (π.hom.restrictPreimage S)) n p m h
        (TopPair.singularCohomologyMap (restrictPreimagePairMap π Z S) n u) a :=
  (rfl)

end Restrict

end TopCat
