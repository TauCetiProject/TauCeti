/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Relative
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Analysis.Convex.Contractible
import TauCeti.AlgebraicTopology.Cohomology.Cap.Pushforward
import TauCeti.AlgebraicTopology.Cohomology.CrossProduct
import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Cross

/-!
# Capping a relative cross product with a class of either factor

Let `(X, B)` be a pair and `Y` a space, and consider the product pair
`(X, B) × Y = (X × Y, B × Y)`. For a relative class `o ∈ Hₘ(X, B; R)` and a class
`x ∈ H_q(Y; S)`, the relative cross product `o × x` lies in `Hₘ₊q(X × Y, B × Y; R ⊗ S)`. This file
shows that capping it with the pull-back of a relative cohomology class `u ∈ Hᵐ(X, B)` along the
first projection, and pushing forward along the second projection, gives back `x` scaled by the
Kronecker pairing of `u` and `o`:

`pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x`

(`TopCat.singularCap_singularHomologyCrossRel`), for every class `u` in the image of the connecting
morphism `δ : Hᵐ⁻¹(B) ⟶ Hᵐ(X, B)`. Every class is in that image when `Hᵐ(X) = 0`
(`TopCat.singularCap_singularHomologyCrossRel_of_isZero`), for instance when `X` is a vector space
and `B` the complement of the origin, so that `(X × Y, B × Y)` is the Thom pair of the product
bundle `X × Y → Y`, `o` is a local orientation of `X` and `u` its dual local cohomology class. Then
`pr₁^* u` is a Thom class of the product bundle, and the formula says that the homology Thom map
`z ↦ pr₂_*(z ⌢ pr₁^* u)` is the inverse of the suspension isomorphism `x ↦ o × x`. The restriction
to the image of `δ` comes from the method of proof, which reduces relative products to absolute
ones through the connecting morphisms.

The proof reduces to absolute products through the connecting morphisms. For `u = δσ`, capping
with `δσ` is capping the boundary with `σ` (`TopPair.singularCap_singularCohomologyδ`), and the
boundary of `o × x` is `∂o × x` (`TopCat.singularHomologyCrossRel_comp_singularHomologyδ`). The
Kronecker pairing of a cap product is that of a cup product
(`TopCat.singularCap_comp_singularKronecker`), the cup product of the pull-backs along the two
projections is the cohomology cross product (`TauCeti.singularCross_eq_singularCup`), and the
Kronecker pairing of cross products is the product of the Kronecker pairings
(`TopCat.singularHomologyCross_comp_singularKronecker_singularCross`). So both sides have the same
Kronecker pairing with every class with injective coefficients, and such pairings separate the
classes of `H_q(Y; S)` (`TopCat.singularKronecker_bijective`).

The connecting morphisms are compatible with the Kronecker pairing,
`⟨δσ, o⟩ = ⟨σ, ∂o⟩` (`TopPair.singularKronecker_singularCohomologyδ`), so the scalar `⟨σ, ∂o⟩`
produced by the proof is `⟨u, o⟩`.

For a finite-dimensional real normed space `V` and the Thom pair `(V × Y, (V ∖ 0) × Y)` of the
product bundle, the homology Thom map `a ↦ pr₂_*(a ⌢ pr₁^* u)` is then a left inverse of the
bijection `x ↦ o × x` (`TauCeti.bijective_singularHomologyCrossRel_tmul_complSingleton`), for a
generator `o` of `H_r(V, V ∖ 0; k)` and its dual class `u`
(`TauCeti.exists_singularKronecker_complSingleton_eq_one`). It is linear over the cohomology of `Y`
up to the sign `(-1)^(r j)` by the projection formula
(`TopPair.map_singularCap_absoluteSingularCap`), so capping with the pull-back of `ψ ∈ Hʲ(Y; k)`
along the second projection is

`(o × x) ⌢ pr₂^* ψ = (-1)^(r j) o × (x ⌢ ψ)`

(`TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul`), for every `o` since both sides are
linear in `o`. The positive degree `r ≠ 0` is needed for the homology Thom map.

The pair is in the first factor, as for the relative cross product
`TopCat.singularHomologyCrossRel`, and the coefficients are modules over a commutative ring `k`.

## Main results

* `TopCat.singularHomologyCrossRel_comp_singularCap_comp_singularKronecker`: the Kronecker pairing
  `⟨c, pr₂_*((o × x) ⌢ pr₁^* δσ)⟩ = ⟨δσ, o⟩ ⟨c, x⟩`, with coefficients in any module.
* `TopCat.singularCap_singularHomologyCrossRel`: `pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x` for `u`
  in the image of `δ`.
* `TopCat.singularCap_singularHomologyCrossRel_of_isZero`: the same for every `u` when
  `Hᵐ(X) = 0`.
* `TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul`:
  `(o × x) ⌢ pr₂^* ψ = (-1)^(r j) o × (x ⌢ ψ)` on the Thom pair of a product bundle.

## References

* E. H. Spanier, *Algebraic Topology*, Chapter 5, Sections 6 and 7 (the slant and cap products of
  cross products, and the Thom isomorphism).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (cap products) and Section 4.D (the Thom isomorphism of a product bundle).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology

universe w

namespace TopCat

variable {k : Type w} [CommRing k] {X Y : TopCat.{w}} {B : Set X} {R S : ModuleCat.{w} k}

variable {p q : ℕ} {I : ModuleCat.{w} k}

/-- On `B × Y`: the homeomorphism `B × Y ≅ fst⁻¹(B)`, capping with the pull-back of `σ` to
`fst⁻¹(B)`, pushing forward to `Y` and evaluating `c` is capping with the pull-back of `σ` along the
first projection of `B × Y` and evaluating the pull-back of `c` along the second. -/
private lemma map_prodPreimageFstIso_hom_comp_singularCap_comp_singularKronecker
    (σ : (TopPair.ofSubset B).snd.singularCohomology R k (𝟙_ (ModuleCat.{w} k)) p)
    (c : Y.singularCohomology S k I q) :
    ((singularHomologyFunctor (ModuleCat.{w} k) (p + q)).obj (R ⊗ S)).map
        (prodPreimageFstIso X Y B).hom ≫
      (TopPair.ofSubset (fst X Y ⁻¹' B)).snd.singularCap k (𝟙 (R ⊗ S)) (λ_ S).hom p q (p + q) rfl
        (TopCat.singularCohomologyMap (TopPair.Hom.snd (TopPair.ofSubsetMap (fst X Y)
          (Set.mapsTo_preimage _ _) : TopPair.ofSubset (fst X Y ⁻¹' B) ⟶ TopPair.ofSubset B)) p
          σ) ≫
      ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).map
        (TopPair.ofSubset (fst X Y ⁻¹' B)).map ≫
      ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).map
        (snd X Y : (TopPair.ofSubset (fst X Y ⁻¹' B)).fst ⟶ Y) ≫
      Y.singularKronecker k q c =
        ((TopPair.ofSubset B).snd ⊗ Y).singularCap k (𝟙 (R ⊗ S)) (λ_ S).hom p q (p + q) rfl
          (TopCat.singularCohomologyMap (fst (TopPair.ofSubset B).snd Y) p σ) ≫
        ((TopPair.ofSubset B).snd ⊗ Y).singularKronecker k q
          (TopCat.singularCohomologyMap (snd (TopPair.ofSubset B).snd Y) q c) := by
  -- Move the homeomorphism past the cap product, then read the composites of maps of spaces on
  -- `B × Y` as its two projections. The first rewrite is given its arguments: the source
  -- `(TopPair.ofSubset (fst X Y ⁻¹' B)).fst` of `snd X Y` is `X ⊗ Y` only up to unfolding, so the
  -- pattern `?F.map ?f ≫ ?F.map ?g` would not be found.
  rw [← Functor.map_comp_assoc ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S)
      (TopPair.ofSubset (fst X Y ⁻¹' B)).map
      (snd X Y : (TopPair.ofSubset (fst X Y ⁻¹' B)).fst ⟶ Y),
    ← reassoc_of% (TopCat.singularCap_naturality
    (prodPreimageFstIso X Y B).hom k (𝟙 (R ⊗ S)) (λ_ S).hom p q (p + q) rfl _),
    ← Functor.map_comp_assoc, prodPreimageFstIso_hom_comp_map_snd X Y B,
    ← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp,
    prodPreimageFstIso_hom_comp_ofSubsetMap_fst_snd X Y B,
    singularKronecker_naturality]

/-- **The Kronecker pairing of `pr₂_*((o × x) ⌢ pr₁^* δσ)`.** For `σ ∈ Hᵖ(B)` and a class
`c ∈ H^q(Y; S, I)`, evaluating `c` on `pr₂_*((o × x) ⌢ pr₁^* δσ)`, for `o ∈ Hₚ₊₁(X, B; R)` and
`x ∈ H_q(Y; S)`, is the product of the evaluations `⟨δσ, o⟩` and `⟨c, x⟩`. -/
theorem singularHomologyCrossRel_comp_singularCap_comp_singularKronecker
    (σ : (TopPair.ofSubset B).snd.singularCohomology R k (𝟙_ (ModuleCat.{w} k)) p)
    (c : Y.singularCohomology S k I q) :
    singularHomologyCrossRel X Y B R S (p + 1) q (p + q + 1) (by omega) ≫
        (TopPair.ofSubset (fst X Y ⁻¹' B)).singularCap k (𝟙 (R ⊗ S)) (λ_ S).hom (p + 1) q
          (p + q + 1) (by omega) (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _) :
              TopPair.ofSubset (fst X Y ⁻¹' B) ⟶ TopPair.ofSubset B) (p + 1)
            ((TopPair.ofSubset B).singularCohomologyδ R k (𝟙_ _) p (p + 1) rfl σ)) ≫
        ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).map
          (snd X Y : (TopPair.ofSubset (fst X Y ⁻¹' B)).fst ⟶ Y) ≫
        Y.singularKronecker k q c =
      ((TopPair.ofSubset B).singularKronecker k (p + 1)
          ((TopPair.ofSubset B).singularCohomologyδ R k (𝟙_ _) p (p + 1) rfl σ) ⊗ₘ
        Y.singularKronecker k q c) ≫ (λ_ I).hom := by
  -- The pull-back of `δσ` to the product pair is `δ` of the pull-back of `σ` to `B × Y`.
  rw [← ConcreteCategory.comp_apply, TopPair.singularCohomologyδ_naturality _ p (p + 1) rfl,
    ConcreteCategory.comp_apply, TopPair.singularCap_singularCohomologyδ _ k (𝟙 (R ⊗ S))
      (λ_ S).hom p q (p + q) rfl]
  simp only [Category.assoc]
  rw [singularHomologyCrossRel_comp_singularHomologyδ_assoc X Y B R S (p + 1) q (p + q + 1) _ rfl
    rfl]
  have hJ : singularHomologyCross (TopPair.ofSubset B).snd Y R S p q (p + q) rfl ≫
      ((TopPair.ofSubset B).snd ⊗ Y).singularCap k (𝟙 (R ⊗ S)) (λ_ S).hom p q (p + q) rfl
        (TopCat.singularCohomologyMap (fst (TopPair.ofSubset B).snd Y) p σ) ≫
      ((TopPair.ofSubset B).snd ⊗ Y).singularKronecker k q
        (TopCat.singularCohomologyMap (snd (TopPair.ofSubset B).snd Y) q c) =
        ((TopPair.ofSubset B).snd.singularKronecker k p σ ⊗ₘ Y.singularKronecker k q c) ≫
          (λ_ I).hom := by
    rw [TopCat.singularCap_comp_singularKronecker, ← TauCeti.singularCross_eq_singularCup]
    exact singularHomologyCross_comp_singularKronecker_singularCross (λ_ I).hom _ Y p q (p + q) rfl
      σ c
  -- The target of `(TopPair.ofSubset B).singularHomologyδ R (p + 1) p` is the homology
  -- `(TopPair.toSSetPair.obj (TopPair.ofSubset B)).left.homology R p` of the subspace of the
  -- simplicial pair, while the source of `(TopPair.ofSubset B).snd.singularKronecker k p σ` (and
  -- of `hJ`'s right side) is `((singularHomologyFunctor (ModuleCat k) p).obj R).obj
  -- (TopPair.ofSubset B).snd`. The two agree only up to unfolding, so `whiskerRight_comp_tensorHom`
  -- is given its arguments, `hJ` is rewritten with `erw`, and the final reassociation is a term.
  conv_rhs =>
    rw [TopPair.singularKronecker_singularCohomologyδ,
      ← whiskerRight_comp_tensorHom ((TopPair.ofSubset B).singularHomologyδ R (p + 1) p)
        ((TopPair.ofSubset B).snd.singularKronecker k p σ) (Y.singularKronecker k q c),
      Category.assoc]
    erw [← hJ]
    rw [← map_prodPreimageFstIso_hom_comp_singularCap_comp_singularKronecker σ c]
  exact (Category.assoc _ _ _).trans <| congrArg (_ ≫ ·) <| (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) <| congrArg (_ ≫ ·) (Category.assoc _ _ _)

/-- **Capping a relative cross product with a class of the first factor**,
`pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x`: for a relative class `u ∈ Hᵖ⁺¹(X, B)` in the image of the
connecting morphism `Hᵖ(B) ⟶ Hᵖ⁺¹(X, B)`, a relative class `o ∈ Hₚ₊₁(X, B; R)` and a class
`x ∈ H_q(Y; S)`, capping the relative cross product `o × x ∈ Hₚ₊q₊₁(X × Y, B × Y; R ⊗ S)` with the
pull-back of `u` along the first projection and pushing forward along the second projection gives
`x` scaled by the Kronecker pairing `⟨u, o⟩`. -/
theorem singularCap_singularHomologyCrossRel
    (u : (TopPair.ofSubset B).singularCohomology R k (𝟙_ (ModuleCat.{w} k)) (p + 1))
    (hu : u ∈ Set.range ((TopPair.ofSubset B).singularCohomologyδ R k (𝟙_ _) p (p + 1) rfl))
    (o : ((TopPair.ofSubset B).singularHomology R (p + 1) : ModuleCat.{w} k))
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).obj Y) :
    ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).map
        (snd X Y : (TopPair.ofSubset (fst X Y ⁻¹' B)).fst ⟶ Y)
      ((TopPair.ofSubset (fst X Y ⁻¹' B)).singularCap k (𝟙 (R ⊗ S)) (λ_ S).hom (p + 1) q
          (p + q + 1) (by omega) (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _) :
              TopPair.ofSubset (fst X Y ⁻¹' B) ⟶ TopPair.ofSubset B) (p + 1) u)
        (singularHomologyCrossRel X Y B R S (p + 1) q (p + q + 1) (by omega) (o ⊗ₜ x))) =
      ((TopPair.ofSubset B).singularKronecker k (p + 1) u o : k) • x := by
  obtain ⟨σ, rfl⟩ := hu
  -- Classes of `H_q(Y; S)` are separated by their Kronecker pairings with classes with injective
  -- coefficients: the inclusion into an injective module is such a pairing.
  let ι := Injective.ι (((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).obj Y)
  apply (ModuleCat.mono_iff_injective ι).1 inferInstance
  obtain ⟨c, hc⟩ := (Y.singularKronecker_bijective k (R := S) q).2 ι
  rw [← hc, map_smul]
  have h := ConcreteCategory.congr_hom
    (singularHomologyCrossRel_comp_singularCap_comp_singularKronecker σ c) (o ⊗ₜ x)
  simp only [ConcreteCategory.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply] at h
  exact h

/-- **Capping a relative cross product with a class of the first factor, when `Hᵖ⁺¹(X) = 0`**:
`pr₂_*((o × x) ⌢ pr₁^* u) = ⟨u, o⟩ • x` for every relative class `u ∈ Hᵖ⁺¹(X, B)`. By the exact
sequence of the pair, every such class comes from `Hᵖ(B)`; this is the case of a vector space `X`
with `B` the complement of the origin, where `pr₁^* u` is a Thom class of the product bundle
`X × Y → Y` when `u` is a local cohomology generator. -/
theorem singularCap_singularHomologyCrossRel_of_isZero
    (hX : IsZero (X.singularCohomology R k (𝟙_ (ModuleCat.{w} k)) (p + 1)))
    (u : (TopPair.ofSubset B).singularCohomology R k (𝟙_ (ModuleCat.{w} k)) (p + 1))
    (o : ((TopPair.ofSubset B).singularHomology R (p + 1) : ModuleCat.{w} k))
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).obj Y) :
    ((singularHomologyFunctor (ModuleCat.{w} k) q).obj S).map
        (snd X Y : (TopPair.ofSubset (fst X Y ⁻¹' B)).fst ⟶ Y)
      ((TopPair.ofSubset (fst X Y ⁻¹' B)).singularCap k (𝟙 (R ⊗ S)) (λ_ S).hom (p + 1) q
          (p + q + 1) (by omega) (TopPair.singularCohomologyMap
            (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _) :
              TopPair.ofSubset (fst X Y ⁻¹' B) ⟶ TopPair.ofSubset B) (p + 1) u)
        (singularHomologyCrossRel X Y B R S (p + 1) q (p + q + 1) (by omega) (o ⊗ₜ x))) =
      ((TopPair.ofSubset B).singularKronecker k (p + 1) u o : k) • x := by
  refine singularCap_singularHomologyCrossRel u ?_ o x
  have hu : u ∈ LinearMap.range
      ((TopPair.ofSubset B).singularCohomologyδ R k (𝟙_ _) p (p + 1) rfl).hom := by
    rw [((TopPair.ofSubset B).singularCohomology_exact_relative R k _ p
      (p + 1)).moduleCat_range_eq_ker, LinearMap.mem_ker]
    exact ConcreteCategory.congr_hom
      (hX.eq_of_tgt ((TopPair.ofSubset B).singularCohomologyπ R k _ (p + 1)) 0) u
  exact LinearMap.mem_range.1 hu

end TopCat

namespace TauCeti

open Set Module

variable {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {k : Type w} [CommRing k] (L : ModuleCat.{w} k)

/-- The case of `TauCeti.absoluteSingularCap_singularHomologyCrossRel_tmul` where `o` generates the
local homology of `V` at `0` and `V` has dimension `p + 1`. -/
private theorem absoluteSingularCap_singularHomologyCrossRel_tmul_of_span_eq_top (Y : TopCat.{w})
    {p j q n m : ℕ} (hr : finrank ℝ V = p + 1)
    {o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) (p + 1)} (ho : Submodule.span k {o} = ⊤)
    (hn : p + 1 + (j + q) = n) (hm : p + 1 + q = m) (h : j + m = n)
    (ψ : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) (j + q)).obj L).obj Y) :
    (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).absoluteSingularCap k
        (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n h
        (TopCat.singularCohomologyMap (snd (TopCat.of V) Y :
          (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).fst ⟶ Y) j ψ)
        (TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          (p + 1) (j + q) n hn (o ⊗ₜ x)) =
      ((-1 : ℤ) ^ ((p + 1) * j)) •
        TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          (p + 1) q m hm (o ⊗ₜ Y.singularCap k (λ_ L).inv (λ_ L).hom j q (j + q) rfl ψ x) := by
  obtain rfl : m = p + q + 1 := by omega
  obtain rfl : n = p + (j + q) + 1 := by omega
  -- The class `u ∈ Hᵖ⁺¹(V, V ∖ 0; k)` with `⟨u, o⟩ = 1`.
  have hx : (0 : V) ∈ (OpenPartialHomeomorph.refl V).source := mem_univ _
  obtain ⟨u, huo⟩ := exists_singularKronecker_complSingleton_eq_one
    (OpenPartialHomeomorph.refl V) hx hr ho
  -- The homology Thom map `a ↦ pr₂_*(a ⌢ pr₁^* u)` is a left inverse of `y ↦ o × y`.
  have : ContractibleSpace (TopCat.of V) := inferInstanceAs (ContractibleSpace V)
  have hX := isZero_singularCohomology_of_contractibleSpace (𝟙_ (ModuleCat.{w} k)) k
    (𝟙_ (ModuleCat.{w} k)) (TopCat.of V) (n := p + 1) (by omega)
  have hΦ (q' : ℕ) (y : ((singularHomologyFunctor (ModuleCat.{w} k) q').obj L).obj Y) :=
    (TopCat.singularCap_singularHomologyCrossRel_of_isZero hX u o y).trans
      (by rw [huo, one_smul])
  -- Write the left side as `o × b`, and compute `b` with the Thom map.
  obtain ⟨b, hb⟩ := (bijective_singularHomologyCrossRel_tmul_complSingleton
    (OpenPartialHomeomorph.refl V) hx Y L hr ho q (p + q + 1) hm).2
    ((TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).absoluteSingularCap k
        (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j (p + q + 1)
        (p + (j + q) + 1) h (TopCat.singularCohomologyMap (snd (TopCat.of V) Y :
          (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).fst ⟶ Y) j ψ)
        (TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          (p + 1) (j + q) (p + (j + q) + 1) hn (o ⊗ₜ x)))
  beta_reduce at hb
  have hb' : b = ((-1 : ℤ) ^ ((p + 1) * j)) • Y.singularCap k (λ_ L).inv (λ_ L).hom j q (j + q)
      rfl ψ x := by
    refine (hΦ q b).symm.trans ?_
    rw [hb]
    have hpf := TopPair.map_singularCap_absoluteSingularCap
      (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)) (𝟙 (𝟙_ (ModuleCat.{w} k) ⊗ L))
      (snd (TopCat.of V) Y) h hm hn rfl
      (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (fst (TopCat.of V) Y)
        (mapsTo_preimage _ _) : TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ) ⟶
          TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ) (p + 1) u) ψ
      (TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L (p + 1)
        (j + q) (p + (j + q) + 1) hn (o ⊗ₜ x))
    -- The Thom map takes `o × x` back to `x`. The homology of the product pair is typed as
    -- `TopPair.singularHomology` in `hpf` and as the object of a homology functor in `hΦ`; the two
    -- agree only up to unfolding, so `hΦ` is applied under the sign by unification, not `rw`.
    exact hpf.trans (congrArg (fun y ↦ ((-1 : ℤ) ^ ((p + 1) * j)) •
      Y.singularCap k (λ_ L).inv (λ_ L).hom j q (j + q) rfl ψ y) (hΦ (j + q) x))
  rw [← hb, hb', TensorProduct.tmul_smul, map_zsmul]

/-- **Capping the Thom isomorphism of a product bundle with a class of the base.** Let `V` be a
finite-dimensional real normed space, `o ∈ H_r(V, V ∖ 0; k)` with `r ≠ 0`, `Y` a space,
`x ∈ H_{j+q}(Y; L)` and `ψ ∈ Hʲ(Y; k)`. In the Thom pair `(V × Y, (V ∖ 0) × Y)` of the product
bundle, capping the relative cross product `o × x` with the pull-back `pr₂^* ψ` of `ψ` along the
projection to `Y` is `(-1)^(r j)` times the cross product of `o` with `x ⌢ ψ`. The proof inverts
`x ↦ o × x` by the homology Thom map of `TopCat.singularCap_singularHomologyCrossRel_of_isZero`,
which is only available in positive degree, hence the hypothesis `r ≠ 0`. -/
theorem absoluteSingularCap_singularHomologyCrossRel_tmul (Y : TopCat.{w}) {r j q n m : ℕ}
    (hr₀ : r ≠ 0) (hn : r + (j + q) = n) (hm : r + q = m) (h : j + m = n)
    (o : (TopPair.ofSubset (X := TopCat.of V) {(0 : V)}ᶜ).singularHomology
      (C := ModuleCat.{w} k) (𝟙_ _) r)
    (ψ : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) j)
    (x : ((singularHomologyFunctor (ModuleCat.{w} k) (j + q)).obj L).obj Y) :
    (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).absoluteSingularCap k
        (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).inv (λ_ (𝟙_ (ModuleCat.{w} k) ⊗ L)).hom j m n h
        (TopCat.singularCohomologyMap (snd (TopCat.of V) Y :
          (TopPair.ofSubset (fst (TopCat.of V) Y ⁻¹' {(0 : V)}ᶜ)).fst ⟶ Y) j ψ)
        (TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          r (j + q) n hn (o ⊗ₜ x)) =
      ((-1 : ℤ) ^ (r * j)) •
        TopCat.singularHomologyCrossRel (TopCat.of V) Y {(0 : V)}ᶜ (𝟙_ (ModuleCat.{w} k)) L
          r q m hm (o ⊗ₜ Y.singularCap k (λ_ L).inv (λ_ L).hom j q (j + q) rfl ψ x) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr₀
  have hx : (0 : V) ∈ (OpenPartialHomeomorph.refl V).source := mem_univ _
  by_cases hr : finrank ℝ V = p + 1
  · -- Both sides are linear in `o`, a multiple of a generator of the local homology.
    obtain ⟨g, hg⟩ := exists_span_singularHomology_complSingleton_eq_top
      (OpenPartialHomeomorph.refl V) hx (k := k) hr
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hg ▸ Submodule.mem_top (x := o))
    rw [← TensorProduct.smul_tmul', map_smul, map_smul,
      absoluteSingularCap_singularHomologyCrossRel_tmul_of_span_eq_top L Y hr hg hn hm h ψ x,
      ← TensorProduct.smul_tmul', map_smul, smul_comm]
  · -- Otherwise the local homology vanishes in degree `p + 1`, so `o = 0`.
    have := ModuleCat.subsingleton_of_isZero (isZero_singularHomology_complSingleton_of_ne
      (𝟙_ (ModuleCat.{w} k)) (OpenPartialHomeomorph.refl V) hx rfl (Ne.symm hr))
    rw [Subsingleton.elim o 0, TensorProduct.zero_tmul, TensorProduct.zero_tmul, map_zero,
      map_zero, map_zero, smul_zero]

end TauCeti

end
