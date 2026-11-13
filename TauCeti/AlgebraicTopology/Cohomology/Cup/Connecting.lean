/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative

/-!
# The connecting morphism of a pair and the cup product

Let `(X, A)` be a topological pair. Relative cohomology `H*(X, A)` is a module over the absolute
cohomology `H*(X)` through the cup product of absolute and relative classes
(`TopPair.singularCup`), and `H*(A)` is one through restriction to `A` followed by the cup product
of `A`. The maps `H*(X, A) ⟶ H*(X)` and `H*(X) ⟶ H*(A)` of the long exact sequence of the pair are
module maps (`TopPair.singularCohomologyπ_singularCup` and `TopCat.singularCup_naturality`). This
file shows that the connecting morphism `δ : H^q(A) ⟶ H^{q+1}(X, A)` is one too, up to the Koszul
sign: for `a ∈ Hᵖ(X)` and `b ∈ H^q(A)`,

`δ (a|_A ⌣ b) = (-1)ᵖ a ⌣ δ b`

(`TopPair.singularCohomologyδ_singularCup`). So the whole long exact sequence of the pair is a long
exact sequence of `H*(X)`-modules, the connecting morphism being of degree one.

The proof is the usual computation at the level of cochains. Represent `a` by a cocycle `α` on
`X` and `b` by a cocycle `β` on `A`, and lift `β` to a cochain `x` on `X`, so that `δ b` is the
class of the relative cocycle `dx`. Then `α ⌣ x` lifts `α|_A ⌣ β`, and by the Leibniz rule its
coboundary is `(-1)ᵖ α ⌣ dx`, since `α` is a cocycle.

For the Thom pair `(E, E₀)` of a vector bundle `π : E → B`, a relative class of the form `u = δ σ`
with `σ ∈ H^{r-1}(E₀)` has Thom map `a ↦ π^*a ⌣ u = (-1)ᵖ δ (π^*a|_{E₀} ⌣ σ)`; for a product bundle
`B × F` this reads the Thom map off the cohomology of `B × (F ∖ {0})`.

## Main results

* `TopPair.singularCohomologyδ_singularCup`: `δ (a|_A ⌣ b) = (-1)ᵖ a ⌣ δ b`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, Lemma 3.6 (the coboundary of a cup product) and the relative cup products.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C}

namespace TopPair

variable (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]

/-- **The connecting morphism of a pair is linear over absolute cohomology, up to sign.** For a
pair `(X, A)`, `a ∈ Hᵖ(X)` and `b ∈ H^q(A)`, the connecting morphism
`δ : Hⁿ(A) ⟶ Hⁿ⁺¹(X, A)` sends the cup product `a|_A ⌣ b` to `(-1)ᵖ a ⌣ δ b`, where `a ⌣ δ b` is the
cup product of absolute and relative cohomology. -/
theorem singularCohomologyδ_singularCup (P : TopPair.{w}) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    {p q n q' m : ℕ} (h : p + q = n) (hq : q + 1 = q') (hm : n + 1 = m) (h' : p + q' = m)
    (a : P.fst.singularCohomology R k M p) (b : P.snd.singularCohomology S k N q) :
    P.singularCohomologyδ T k L n m hm
        (P.snd.singularCup k u μ p q n h (TopCat.singularCohomologyMap P.map p a) b) =
      ((-1 : ℤ) ^ p) •
        P.singularCup k u μ p q' m h' a (P.singularCohomologyδ S k N q q' hq b) := by
  subst hq hm h
  -- Represent `a` by a cocycle `α` and `δ b` by a relative cocycle `ζ`.
  obtain ⟨α, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨ζ, hζ⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ (q + 1)
    (P.singularCohomologyδ S k N q (q + 1) rfl b)
  -- Lift `b` to a cochain `x` on `X` whose coboundary is the image of `ζ` on the nose.
  obtain ⟨x, β, hdx, hgx, rfl⟩ :=
    (P.shortExact_singularCochainComplexShortComplex S k N).moduleCat_exists_d_eq_of_δ_eq
      q (q + 1) rfl b ζ hζ.symm
  rw [← hζ, TopCat.singularCohomologyMap,
    TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_homologyπ_apply,
    TopCat.singularCup_homologyπ, singularCup_homologyπ, ← map_zsmul]
  refine (P.shortExact_singularCochainComplexShortComplex T k L).moduleCat_δ_homologyπ
    (p + q) (p + q + 1) rfl _
    (TauCeti.ChainComplex.cupCochain k (P.fst.alexanderWhitneyDiagonal u) μ p q (p + q) rfl
      ((P.fst.singularCochainComplex R k M).iCycles p α) x) ?_ _ ?_
  · -- `α ⌣ x` restricts to `α|_A ⌣ β` on `A`.
    rw [TauCeti.ChainComplex.iCycles_cupCycles,
      TauCeti.ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply, ← hgx]
    exact (TauCeti.ChainComplex.cupCochain_naturality (k := k) (P.fst.alexanderWhitneyDiagonal u)
      μ (P.snd.alexanderWhitneyDiagonal u) _ _ _
      (TopCat.alexanderWhitneyDiagonal_naturality P.map u) p q (p + q) rfl _ x).symm
  · -- The coboundary of `α ⌣ x` is `(-1)ᵖ α ⌣ dx`, and `dx` is the image of `ζ`.
    -- `hdx` read on cochains: both maps of cochain modules act by precomposition, by definition
    -- (`TauCeti.ChainComplex.linearYonedaFunctor_map_f_hom_apply` and
    -- `TauCeti.ChainComplex.linearYonedaObj_d_apply`, both proved by `rfl`).
    have hdx' : (P.singularChainComplexπ S).f (q + 1) ≫
        (P.singularCochainComplex S k N).iCycles (q + 1) ζ =
          ((TopCat.toSSet.obj P.fst).chainComplex S).d (q + 1) q ≫ x := hdx.symm
    have e₁ := singularChainComplexπ_f_cupCochain_rightAlexanderWhitneyDiagonal (k := k) P u μ p
      (q + 1) (p + q + 1) h' ((P.fst.singularCochainComplex R k M).iCycles p α)
      ((P.singularCochainComplex S k N).iCycles (q + 1) ζ)
    have e₂ := TauCeti.ChainComplex.d_comp_cupCochain (k := k) (P.fst.alexanderWhitneyDiagonal u)
      μ p q (p + q) rfl ((P.fst.singularCochainComplex R k M).iCycles p α) x
    -- The first term of the Leibniz rule vanishes, since `α` is a cocycle.
    have h₀ : TauCeti.ChainComplex.cupCochain k (P.fst.alexanderWhitneyDiagonal u) μ (p + 1) q
        (p + q + 1) (by lia) (((TopCat.toSSet.obj P.fst).chainComplex R).d (p + 1) p ≫
          (P.fst.singularCochainComplex R k M).iCycles p α) x = 0 := by
      rw [TauCeti.ChainComplex.d_comp_linearYonedaObj_iCycles]
      exact LinearMap.map_zero₂ _ x
    rw [h₀, zero_add] at e₂
    rw [map_zsmul, map_zsmul, TauCeti.ChainComplex.iCycles_cupCycles]
    -- As for `hdx'`, the two sides of the goal are precompositions by definition.
    exact (congrArg _ (e₁.trans (congrArg _ hdx'))).trans e₂.symm

end TopPair
