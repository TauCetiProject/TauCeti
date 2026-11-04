/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CrossProduct
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.RelativeCup

/-!
# Relative cup and cross products in singular cohomology

Relative cup products are cup products along the descents of the Alexander–Whitney diagonal to
relative chains (`TauCeti/AlgebraicTopology/Singular/AlexanderWhitney/RelativeCup.lean`).

* **Absolute–relative product.**  For a pair `(X, A)`, a cochain on `X` cupped with a cochain
  vanishing on `A` vanishes on `A`.  This gives `TopPair.singularCup :
  Hᵖ(X; R, M) × H^q(X, A; S, N) ⟶ Hⁿ(X, A; T, L)`, which needs no hypothesis on `A`.  It is
  associative and unital, so it makes `H*(X, A)` a module over `H*(X)`; it is natural in maps of
  pairs and maps to the absolute cup product under `H*(X, A) ⟶ H*(X)`.
* **Relative cup product.**  For subsets `U` and `V` of `X`, a cochain vanishing on `U` cupped with
  a cochain vanishing on `V` vanishes on the chains `C(U) + C(V)` of the singular simplices lying
  in `U` or in `V`, but not in general on the chains of `U ∪ V`.  When `U` and `V` are open in
  `U ∪ V`, the small-chain theorem shows that restricting cochains from `C(X, U ∪ V)` to
  `C(X)/(C(U) + C(V))` is an isomorphism on cohomology.  Its inverse gives
  `TopCat.singularRelativeCup : Hᵖ(X, U) × H^q(X, V) ⟶ Hⁿ(X, U ∪ V)`, natural in maps carrying `U`
  and `V` into `U'` and `V'`, and mapping to the absolute cup product.  Some such hypothesis is
  needed: for arbitrary subsets the singular cochains vanishing on `U ∪ V` need not compute the
  cohomology of the quotient by `C(U) + C(V)`.
* **Relative cross product.**  For open `A ⊆ X` and `B ⊆ Y`, the cross product
  `TauCeti.singularRelativeCross : Hᵖ(X, A) × H^q(Y, B) ⟶ Hⁿ(X × Y, A × Y ∪ X × B)` is the relative
  cup product of the pullbacks along the two projections, where `A × Y` and `X × B` are the
  preimages of `A` and `B`.  It is natural in both pairs and maps to the absolute cross product
  `TauCeti.singularCross`.  When `A` and `B` are the complements of the zero sections of two
  vector bundles, this is the pairing on the cohomology of their Thom pairs.

## Main definitions and results

* `TopPair.singularCup`, with `TopPair.singularCup_homologyπ` computing it on classes of cocycles,
  `TopPair.singularCohomologyπ_singularCup` its compatibility with the absolute cup product,
  `TopPair.singularCup_naturality`, and the module laws `TopPair.singularCup_assoc` and
  `TopPair.singularCup_constSingularCocycle_left`.
* `TopCat.singularRelativeCup`, characterized by
  `TopCat.homologyMap_cochainComplexMap_singularRelativeCup`, with
  `TopCat.singularCohomologyπ_singularRelativeCup` and `TopCat.singularRelativeCup_naturality`.
* `TauCeti.singularRelativeCross`, with `TauCeti.singularRelativeCross_apply`,
  `TauCeti.singularCohomologyπ_singularRelativeCross` and
  `TauCeti.singularRelativeCross_naturality`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the relative cup products `Hᵏ(X) × Hˡ(X, A) ⟶ Hᵏ⁺ˡ(X, A)` and
  `Hᵏ(X, A) × Hˡ(X, B) ⟶ Hᵏ⁺ˡ(X, A ∪ B)` for `A` and `B` open, and the relative cross product
  `Hᵏ(X, A) × Hˡ(Y, B) ⟶ Hᵏ⁺ˡ(X × Y, A × Y ∪ X × B)` for `A` and `B` open.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomologicalComplex

universe w v u

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C}

namespace TopPair

/-! ### The action of absolute cohomology on relative cohomology -/

section Cochain

variable {k : Type*} [CommSemiring k] [Linear k C] [MonoidalLinear k C]

/-- Precomposed with the quotient map to relative chains, the cup product of an absolute cochain
`φ` with a relative cochain `ψ` along the right relative Alexander–Whitney diagonal is the absolute
cup product of `φ` with `ψ` pulled back to absolute chains. -/
lemma singularChainComplexπ_f_cupCochain_rightAlexanderWhitneyDiagonal (P : TopPair.{w})
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (φ : ((TopCat.toSSet.obj P.fst).chainComplex R).X p ⟶ M)
    (ψ : (P.singularChainComplex S).X q ⟶ N) :
    (P.singularChainComplexπ T).f n ≫
        TauCeti.ChainComplex.cupCochain k (P.rightAlexanderWhitneyDiagonal u) μ p q n h φ ψ =
      TauCeti.ChainComplex.cupCochain k (P.fst.alexanderWhitneyDiagonal u) μ p q n h φ
        ((P.singularChainComplexπ S).f q ≫ ψ) := by
  simpa using (TauCeti.ChainComplex.cupCochain_naturality (k := k)
    (P.rightAlexanderWhitneyDiagonal u) μ (P.fst.alexanderWhitneyDiagonal u)
    (P.singularChainComplexπ T) (𝟙 _) (P.singularChainComplexπ S)
    (P.singularChainComplexπ_rightAlexanderWhitneyDiagonal u) p q n h φ ψ).symm

variable {R₁ R₂ T₁₂ T₂₃ M₁ M₂ M₃ M₁₂ M₂₃ : C}

/-- **Associativity of the action of absolute cochains on relative cochains**:
`(φ₁ ⌣ φ₂) ⌣ ψ = φ₁ ⌣ (φ₂ ⌣ ψ)` for absolute cochains `φ₁`, `φ₂` and a relative cochain `ψ`, under
the coassociativity and associativity hypotheses of
`TopCat.cupCochain_alexanderWhitneyDiagonal_assoc`. -/
lemma cupCochain_rightAlexanderWhitneyDiagonal_assoc (P : TopPair.{w})
    {u₁₂ : T₁₂ ⟶ R₁ ⊗ R₂} {u : T ⟶ T₁₂ ⊗ S} {u₂₃ : T₂₃ ⟶ R₂ ⊗ S} {u' : T ⟶ R₁ ⊗ T₂₃}
    (hu : u ≫ u₁₂ ▷ S ≫ (α_ R₁ R₂ S).hom = u' ≫ R₁ ◁ u₂₃)
    {μ₁₂ : M₁ ⊗ M₂ ⟶ M₁₂} {μ : M₁₂ ⊗ M₃ ⟶ L} {μ₂₃ : M₂ ⊗ M₃ ⟶ M₂₃} {μ' : M₁ ⊗ M₂₃ ⟶ L}
    (hμ : μ₁₂ ▷ M₃ ≫ μ = (α_ M₁ M₂ M₃).hom ≫ M₁ ◁ μ₂₃ ≫ μ')
    {p q r m m' n : ℕ} (h₁₂ : p + q = m) (h : m + r = n) (h₂₃ : q + r = m') (h' : p + m' = n)
    (φ₁ : ((TopCat.toSSet.obj P.fst).chainComplex R₁).X p ⟶ M₁)
    (φ₂ : ((TopCat.toSSet.obj P.fst).chainComplex R₂).X q ⟶ M₂)
    (ψ : (P.singularChainComplex S).X r ⟶ M₃) :
    TauCeti.ChainComplex.cupCochain k (P.rightAlexanderWhitneyDiagonal u) μ m r n h
        (TauCeti.ChainComplex.cupCochain k (P.fst.alexanderWhitneyDiagonal u₁₂) μ₁₂ p q m h₁₂ φ₁
          φ₂) ψ =
      TauCeti.ChainComplex.cupCochain k (P.rightAlexanderWhitneyDiagonal u') μ' p m' n h' φ₁
        (TauCeti.ChainComplex.cupCochain k (P.rightAlexanderWhitneyDiagonal u₂₃) μ₂₃ q r m' h₂₃
          φ₂ ψ) := by
  rw [← cancel_epi ((P.singularChainComplexπ T).f n),
    singularChainComplexπ_f_cupCochain_rightAlexanderWhitneyDiagonal,
    singularChainComplexπ_f_cupCochain_rightAlexanderWhitneyDiagonal]
  -- Term-mode step: `rw` cannot rewrite inside the second argument, whose ambient chains appear
  -- both as `(toSSetPair.obj P).right.chainComplex R` and as
  -- `(TopCat.toSSet.obj P.fst).chainComplex R`.
  exact (TopCat.cupCochain_alexanderWhitneyDiagonal_assoc P.fst hu hμ h₁₂ h h₂₃ h' _ _ _).trans
    (congrArg _ (singularChainComplexπ_f_cupCochain_rightAlexanderWhitneyDiagonal P u₂₃ μ₂₃ q r m'
      h₂₃ φ₂ ψ).symm)

/-- **The unit law for the action of absolute cochains on relative cochains**: the constant
`0`-cochain with value `e` acts as the identity, under the hypotheses of
`TopCat.cupCochain_constCochain_left`. -/
lemma cupCochain_rightAlexanderWhitneyDiagonal_constCochain_left (P : TopPair.{w})
    {u : S ⟶ R ⊗ S} {μ : M ⊗ N ⟶ N}
    {e : R ⟶ M} {η : 𝟙_ C ⟶ M} (hu : u ≫ e ▷ S = (λ_ S).inv ≫ η ▷ S)
    (hμ : η ▷ N ≫ μ = (λ_ N).hom) {q : ℕ} (h : 0 + q = q)
    (ψ : (P.singularChainComplex S).X q ⟶ N) :
    TauCeti.ChainComplex.cupCochain k (P.rightAlexanderWhitneyDiagonal u) μ 0 q q h
      ((TopCat.toSSet.obj P.fst).constCochain e) ψ = ψ := by
  rw [← cancel_epi ((P.singularChainComplexπ S).f q),
    singularChainComplexπ_f_cupCochain_rightAlexanderWhitneyDiagonal]
  exact TopCat.cupCochain_constCochain_left P.fst hu hμ h _

end Cochain

variable (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]

/-- **The cup product of absolute and relative singular cohomology**,
`Hᵖ(X; R, M) × H^q(X, A; S, N) ⟶ Hⁿ(X, A; T, L)` for a pair `(X, A)` and `p + q = n`: the cup
product along the right relative Alexander–Whitney diagonal `P.rightAlexanderWhitneyDiagonal u`
and the pairing `μ : M ⊗ N ⟶ L`.  It makes relative cohomology a module over absolute cohomology
(`TopPair.singularCup_assoc` and `TopPair.singularCup_constSingularCocycle_left`). -/
def singularCup (P : TopPair.{w}) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n) :
    P.fst.singularCohomology R k M p →ₗ[k] P.singularCohomology S k N q →ₗ[k]
      P.singularCohomology T k L n :=
  TauCeti.ChainComplex.cup k (P.rightAlexanderWhitneyDiagonal u) μ p q n h

/-- The cup product of absolute and relative singular cohomology is the cohomological cup product
along the right relative Alexander–Whitney diagonal. -/
lemma singularCup_def (P : TopPair.{w}) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ)
    (h : p + q = n) :
    P.singularCup k u μ p q n h =
      TauCeti.ChainComplex.cup k (P.rightAlexanderWhitneyDiagonal u) μ p q n h :=
  (rfl)

/-- The cup product of the classes of an absolute and a relative cocycle is the class of their cup
product. -/
@[simp]
lemma singularCup_homologyπ (P : TopPair.{w}) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ)
    (h : p + q = n) (a : (P.fst.singularCochainComplex R k M).cycles p)
    (b : (P.singularCochainComplex S k N).cycles q) :
    P.singularCup k u μ p q n h ((P.fst.singularCochainComplex R k M).homologyπ p a)
        ((P.singularCochainComplex S k N).homologyπ q b) =
      (P.singularCochainComplex T k L).homologyπ n
        (TauCeti.ChainComplex.cupCycles k (P.rightAlexanderWhitneyDiagonal u) μ p q n h a b) :=
  TauCeti.ChainComplex.cup_homologyπ _ _ _ _ _ _ _ _

/-- **Compatibility with the absolute cup product**: the image in `Hⁿ(X)` of the cup product of
`a ∈ Hᵖ(X)` with `b ∈ H^q(X, A)` is the cup product of `a` with the image of `b` in `H^q(X)`. -/
@[simp]
lemma singularCohomologyπ_singularCup (P : TopPair.{w}) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) (a : P.fst.singularCohomology R k M p)
    (b : P.singularCohomology S k N q) :
    P.singularCohomologyπ T k L n (P.singularCup k u μ p q n h a b) =
      P.fst.singularCup k u μ p q n h a (P.singularCohomologyπ S k N q b) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  rw [singularCup_homologyπ, singularCohomologyπ, singularCohomologyπ,
    singularCochainComplexShortComplex_f_eq, singularCochainComplexShortComplex_f_eq]
  -- The maps to absolute cohomology are now `homologyMap` of `Hom(π, -)`; the lemmas below state
  -- them with source and target written as `linearYonedaObj`, which is by definition
  -- `TopPair.singularCochainComplex`.
  refine (TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_homologyπ_apply
    (P.singularChainComplexπ T) n _).trans ?_
  refine Eq.trans ?_ (congrArg _
    (TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_homologyπ_apply
      (P.singularChainComplexπ S) q b)).symm
  -- Term-mode steps: `rw` cannot match here, since the ambient chains appear both as
  -- `(toSSetPair.obj P).right.chainComplex R` and as `(TopCat.toSSet.obj P.fst).chainComplex R`.
  refine Eq.trans ?_ (TopCat.singularCup_homologyπ P.fst k u μ p q n h a _).symm
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  refine (TauCeti.ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply _ n _).trans ?_
  refine Eq.trans ?_ (TauCeti.ChainComplex.iCycles_cupCycles
    (P.fst.alexanderWhitneyDiagonal u) μ p q n h a _).symm
  refine (congrArg (_ ≫ ·) (TauCeti.ChainComplex.iCycles_cupCycles
    (P.rightAlexanderWhitneyDiagonal u) μ p q n h a b)).trans <|
    (singularChainComplexπ_f_cupCochain_rightAlexanderWhitneyDiagonal P u μ p q n h _ _).trans ?_
  exact congrArg _ (TauCeti.ChainComplex.iCycles_cyclesMap_linearYonedaFunctor_map_apply _ q b).symm

/-- **Naturality of the cup product of absolute and relative cohomology** in maps of pairs. -/
lemma singularCup_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (u : T ⟶ R ⊗ S)
    (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n) (a : P'.fst.singularCohomology R k M p)
    (b : P'.singularCohomology S k N q) :
    P.singularCup k u μ p q n h (TopCat.singularCohomologyMap (Hom.fst f) p a)
        (TopPair.singularCohomologyMap f q b) =
      TopPair.singularCohomologyMap f n (P'.singularCup k u μ p q n h a b) :=
  TauCeti.ChainComplex.cup_naturality _ μ _ _ _ _ (rightAlexanderWhitneyDiagonal_naturality f u)
    p q n h a b

section Laws

variable {R₁ R₂ T₁₂ T₂₃ M₁ M₂ M₃ M₁₂ M₂₃ : C}

/-- **Associativity of the action of absolute cohomology on relative cohomology**:
`(a ⌣ b) ⌣ c = a ⌣ (b ⌣ c)` for `a`, `b` absolute and `c` relative, under the hypotheses of
`TopCat.singularCup_assoc`. -/
lemma singularCup_assoc (P : TopPair.{w})
    {u₁₂ : T₁₂ ⟶ R₁ ⊗ R₂} {u : T ⟶ T₁₂ ⊗ S} {u₂₃ : T₂₃ ⟶ R₂ ⊗ S} {u' : T ⟶ R₁ ⊗ T₂₃}
    (hu : u ≫ u₁₂ ▷ S ≫ (α_ R₁ R₂ S).hom = u' ≫ R₁ ◁ u₂₃)
    {μ₁₂ : M₁ ⊗ M₂ ⟶ M₁₂} {μ : M₁₂ ⊗ M₃ ⟶ L} {μ₂₃ : M₂ ⊗ M₃ ⟶ M₂₃} {μ' : M₁ ⊗ M₂₃ ⟶ L}
    (hμ : μ₁₂ ▷ M₃ ≫ μ = (α_ M₁ M₂ M₃).hom ≫ M₁ ◁ μ₂₃ ≫ μ')
    {p q r m m' n : ℕ} (h₁₂ : p + q = m) (h : m + r = n) (h₂₃ : q + r = m') (h' : p + m' = n)
    (a : P.fst.singularCohomology R₁ k M₁ p) (b : P.fst.singularCohomology R₂ k M₂ q)
    (c : P.singularCohomology S k M₃ r) :
    P.singularCup k u μ m r n h (P.fst.singularCup k u₁₂ μ₁₂ p q m h₁₂ a b) c =
      P.singularCup k u' μ' p m' n h' a (P.singularCup k u₂₃ μ₂₃ q r m' h₂₃ b c) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  obtain ⟨c, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ r c
  simp only [singularCup_homologyπ, TopCat.singularCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simp only [TauCeti.ChainComplex.iCycles_cupCycles]
  exact cupCochain_rightAlexanderWhitneyDiagonal_assoc P hu hμ h₁₂ h h₂₃ h' _ _ _

/-- **The unit law for the action of absolute cohomology on relative cohomology**: the class of
the constant `0`-cocycle with value `e` acts as the identity, under the hypotheses of
`TopCat.cupCochain_constCochain_left`. -/
lemma singularCup_constSingularCocycle_left (P : TopPair.{w}) {u : S ⟶ R ⊗ S} {μ : M ⊗ N ⟶ N}
    {e : R ⟶ M} {η : 𝟙_ C ⟶ M} (hu : u ≫ e ▷ S = (λ_ S).inv ≫ η ▷ S)
    (hμ : η ▷ N ≫ μ = (λ_ N).hom) {q : ℕ} (h : 0 + q = q) (b : P.singularCohomology S k N q) :
    P.singularCup k u μ 0 q q h
      ((P.fst.singularCochainComplex R k M).homologyπ 0 (P.fst.constSingularCocycle k e)) b =
        b := by
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  rw [singularCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [TauCeti.ChainComplex.iCycles_cupCycles, TopCat.iCycles_constSingularCocycle]
  exact cupCochain_rightAlexanderWhitneyDiagonal_constCochain_left P hu hμ h _

end Laws

end TopPair

namespace TopCat

/-! ### The relative cup product of an excisive couple -/

variable (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C] {X Y : TopCat.{w}}

/-- **The relative cup product** `Hᵖ(X, U; R, M) × H^q(X, V; S, N) ⟶ Hⁿ(X, U ∪ V; T, L)` for
subsets `U` and `V` of `X` which are open in `U ∪ V`, and `p + q = n`: the cup product along the
relative Alexander–Whitney diagonal `TopCat.relativeAlexanderWhitneyDiagonal U V u` and the pairing
`μ : M ⊗ N ⟶ L`, which lands in the cohomology of the chains of `X` relative to its singular
simplices lying in `U` or in `V`, followed by the inverse of the small-chain isomorphism with the
cohomology of `(X, U ∪ V)` (`TopCat.homologyMap_cochainComplexMap_singularRelativeCup`). -/
def singularRelativeCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V)))
    (p q n : ℕ) (h : p + q = n) :
    (TopPair.ofSubset U).singularCohomology R k M p →ₗ[k]
      (TopPair.ofSubset V).singularCohomology S k N q →ₗ[k]
        (TopPair.ofSubset (U ∪ V)).singularCohomology T k L n :=
  have := isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion T k L U V hU hV n
  (TauCeti.ChainComplex.cup k (relativeAlexanderWhitneyDiagonal U V u) μ p q n h).compr₂
    (inv (homologyMap (SSetPair.cochainComplexMap (R := T) (k := k) (M := L)
      (smallSingularSubcomplexPairToUnion U V)) n)).hom

/-- The relative cup product is characterized by its image under the small-chain isomorphism: the
cup product along the relative Alexander–Whitney diagonal. -/
@[simp]
lemma homologyMap_cochainComplexMap_singularRelativeCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (U V : Set X) (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset U).singularCohomology R k M p)
    (b : (TopPair.ofSubset V).singularCohomology S k N q) :
    homologyMap (SSetPair.cochainComplexMap (R := T) (k := k) (M := L)
        (smallSingularSubcomplexPairToUnion U V)) n
        (singularRelativeCup k u μ U V hU hV p q n h a b) =
      TauCeti.ChainComplex.cup k (relativeAlexanderWhitneyDiagonal U V u) μ p q n h a b := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion T k L U V hU hV n
  simp [singularRelativeCup]


/-- **Compatibility with the absolute cup product**: the image in `Hⁿ(X)` of the relative cup
product of `a ∈ Hᵖ(X, U)` and `b ∈ H^q(X, V)` is the cup product of the images of `a` in `Hᵖ(X)` and
of `b` in `H^q(X)`. -/
@[simp]
lemma singularCohomologyπ_singularRelativeCup (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (U V : Set X)
    (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V))) (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V)))
    (p q n : ℕ) (h : p + q = n) (a : (TopPair.ofSubset U).singularCohomology R k M p)
    (b : (TopPair.ofSubset V).singularCohomology S k N q) :
    (TopPair.ofSubset (U ∪ V)).singularCohomologyπ T k L n
        (singularRelativeCup k u μ U V hU hV p q n h a b) =
      X.singularCup k u μ p q n h ((TopPair.ofSubset U).singularCohomologyπ R k M p a)
        ((TopPair.ofSubset V).singularCohomologyπ S k N q b) := by
  -- The map to absolute cohomology factors through the small-chain isomorphism.
  have hπ : (TopPair.ofSubset (U ∪ V)).singularCohomologyπ T k L n =
      homologyMap (K := ((TopPair.ofSubset (U ∪ V)).singularChainComplex T).linearYonedaObj k L)
        (L := ((toSSet.obj X).chainComplex T).linearYonedaObj k L)
        ((TauCeti.ChainComplex.linearYonedaFunctor k L).map
          ((X.smallSingularSubcomplex ![U, V]).pair.chainComplexπ T ≫
            SSetPair.chainComplexMap (smallSingularSubcomplexPairToUnion U V) T).op) n := by
    rw [chainComplexπ_smallSingularSubcomplexPairToUnion, TopPair.singularCohomologyπ,
      TopPair.singularCochainComplexShortComplex_f_eq]
    -- The two sides now differ only in the implicit source and target of `homologyMap`, written
    -- as the cochain complexes of the pair on the left and as `linearYonedaObj` on the right;
    -- `TopPair.singularCochainComplex` is by definition `linearYonedaObj` of the relative chains.
    rfl
  rw [hπ]
  refine (TauCeti.ChainComplex.homologyMap_linearYonedaFunctor_map_comp_apply _ _ n _).trans ?_
  rw [homologyMap_cochainComplexMap_singularRelativeCup, TauCeti.singularCup_def]
  exact (TauCeti.ChainComplex.cup_naturality (relativeAlexanderWhitneyDiagonal U V u) μ
    (X.alexanderWhitneyDiagonal u) _ _ _ (chainComplexπ_relativeAlexanderWhitneyDiagonal U V u)
    p q n h a b).symm

/-- **Naturality of the relative cup product** in maps `f : X ⟶ Y` carrying `U` into `U'` and `V`
into `V'`. -/
lemma singularRelativeCup_naturality (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) {U V : Set X}
    {U' V' : Set Y} (hU : IsOpen ((↑) ⁻¹' U : Set ↥(U ∪ V)))
    (hV : IsOpen ((↑) ⁻¹' V : Set ↥(U ∪ V))) (hU' : IsOpen ((↑) ⁻¹' U' : Set ↥(U' ∪ V')))
    (hV' : IsOpen ((↑) ⁻¹' V' : Set ↥(U' ∪ V'))) (f : X ⟶ Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset U').singularCohomology R k M p)
    (b : (TopPair.ofSubset V').singularCohomology S k N q) :
    singularRelativeCup k u μ U V hU hV p q n h
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap f hfU) p a)
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap f hfV) q b) =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap f (hfU.union_union hfV)) n
        (singularRelativeCup k u μ U' V' hU' hV' p q n h a b) := by
  have := isIso_homologyMap_cochainComplexMap_smallSingularSubcomplexPairToUnion T k L U V hU hV n
  apply (ModuleCat.mono_iff_injective (homologyMap (SSetPair.cochainComplexMap (R := T) (k := k)
    (M := L) (smallSingularSubcomplexPairToUnion U V)) n)).1 inferInstance
  -- The small-chain isomorphisms are natural in `f`.
  have hc : TopPair.singularCohomologyMap (TopPair.ofSubsetMap f (hfU.union_union hfV)) n ≫
      homologyMap (SSetPair.cochainComplexMap (R := T) (k := k) (M := L)
        (smallSingularSubcomplexPairToUnion U V)) n =
      homologyMap (SSetPair.cochainComplexMap (R := T) (k := k) (M := L)
          (smallSingularSubcomplexPairToUnion U' V')) n ≫
        homologyMap (SSetPair.cochainComplexMap (R := T) (k := k) (M := L)
          (smallSingularSubcomplexPairMap f hfU hfV)) n := by
    rw [TopPair.singularCohomologyMap_eq, ← homologyMap_comp, ← homologyMap_comp,
      ← SSetPair.cochainComplexMap_comp, ← SSetPair.cochainComplexMap_comp,
      smallSingularSubcomplexPairToUnion_comp_ofSubsetMap]
  rw [homologyMap_cochainComplexMap_singularRelativeCup, ← ConcreteCategory.comp_apply, hc,
    ConcreteCategory.comp_apply, homologyMap_cochainComplexMap_singularRelativeCup]
  exact TauCeti.ChainComplex.cup_naturality _ μ _ _ _ _
    (relativeAlexanderWhitneyDiagonal_naturality f hfU hfV u) p q n h a b

end TopCat

namespace TauCeti

/-! ### The relative cross product -/

variable (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]

/-- **The relative cross product** `Hᵖ(X, A; R, M) × H^q(Y, B; S, N) ⟶
Hⁿ(X × Y, A × Y ∪ X × B; R ⊗ S, L)` for open subsets `A ⊆ X` and `B ⊆ Y`, and `p + q = n`: the
relative cup product (`TopCat.singularRelativeCup`) of the pullbacks of the two classes along the
projections `(X × Y, A × Y) ⟶ (X, A)` and `(X × Y, X × B) ⟶ (Y, B)`.  Here `A × Y` and `X × B` are
the preimages of `A` and `B` under the projections, which are open, so the relative cup product
applies.  It maps to the absolute cross product `TauCeti.singularCross`
(`TauCeti.singularCohomologyπ_singularRelativeCross`). -/
def singularRelativeCross (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A)
    (hB : IsOpen B) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n) :
    (TopPair.ofSubset A).singularCohomology R k M p →ₗ[k]
      (TopPair.ofSubset B).singularCohomology S k N q →ₗ[k]
        (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularCohomology (R ⊗ S) k L n :=
  (TopCat.singularRelativeCup k (𝟙 (R ⊗ S)) μ (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)
    (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union hA)
    (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union hB) p q n h).compl₁₂
    (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _)) p).hom
    (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _)) q).hom

/-- The relative cross product is the relative cup product of the pullbacks along the two
projections. -/
lemma singularRelativeCross_apply (X Y : TopCat.{w}) {A : Set X} {B : Set Y} (hA : IsOpen A)
    (hB : IsOpen B) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    singularRelativeCross k X Y hA hB μ p q n h a b =
      TopCat.singularRelativeCup k (𝟙 (R ⊗ S)) μ (fst X Y ⁻¹' A) (snd X Y ⁻¹' B)
        (TopCat.isOpen_subtypeVal_preimage_preimage_fst_union hA)
        (TopCat.isOpen_subtypeVal_preimage_preimage_snd_union hB) p q n h
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _))
          p a)
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ _))
          q b) :=
  (rfl)

/-- **Compatibility with the absolute cross product**: the image in `Hⁿ(X × Y)` of the relative
cross product of `a ∈ Hᵖ(X, A)` and `b ∈ H^q(Y, B)` is the cross product of the images of `a` in
`Hᵖ(X)` and of `b` in `H^q(Y)`. -/
@[simp]
lemma singularCohomologyπ_singularRelativeCross (X Y : TopCat.{w}) {A : Set X} {B : Set Y}
    (hA : IsOpen A) (hB : IsOpen B) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset A).singularCohomology R k M p)
    (b : (TopPair.ofSubset B).singularCohomology S k N q) :
    (TopPair.ofSubset (fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)).singularCohomologyπ (R ⊗ S) k L n
        (singularRelativeCross k X Y hA hB μ p q n h a b) =
      singularCross k X Y μ p q n h ((TopPair.ofSubset A).singularCohomologyπ R k M p a)
        ((TopPair.ofSubset B).singularCohomologyπ S k N q b) := by
  have hfst := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality (R := R) (k := k)
    (M := M) (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ A)) p) a
  have hsnd := ConcreteCategory.congr_hom (TopPair.singularCohomologyπ_naturality (R := S) (k := k)
    (M := N) (TopPair.ofSubsetMap (snd X Y) (Set.mapsTo_preimage _ B)) q) b
  rw [TopPair.ofSubsetMap_fst] at hfst hsnd
  simp only [ConcreteCategory.comp_apply] at hfst hsnd
  rw [singularRelativeCross_apply, TopCat.singularCohomologyπ_singularRelativeCup]
  exact (congrArg₂ (fun x y ↦ (X ⊗ Y).singularCup k (𝟙 (R ⊗ S)) μ p q n h x y) hfst.symm
    hsnd.symm).trans (singularCross_eq_singularCup k X Y μ p q n h _ _).symm

/-- **Naturality of the relative cross product** in maps `f : X ⟶ X'` carrying `A` into `A'` and
`g : Y ⟶ Y'` carrying `B` into `B'`. -/
lemma singularRelativeCross_naturality {X Y X' Y' : TopCat.{w}} {A : Set X} {B : Set Y}
    {A' : Set X'} {B' : Set Y'} (hA : IsOpen A) (hB : IsOpen B) (hA' : IsOpen A')
    (hB' : IsOpen B') (f : X ⟶ X') (g : Y ⟶ Y') (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B')
    (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (a : (TopPair.ofSubset A').singularCohomology R k M p)
    (b : (TopPair.ofSubset B').singularCohomology S k N q) :
    singularRelativeCross k X Y hA hB μ p q n h
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap f hf) p a)
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap g hg) q b) =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (f ⊗ₘ g)
          ((TopCat.mapsTo_tensorHom_preimage_fst f g hf).union_union
            (TopCat.mapsTo_tensorHom_preimage_snd f g hg))) n
        (singularRelativeCross k X' Y' hA' hB' μ p q n h a b) := by
  rw [singularRelativeCross_apply, singularRelativeCross_apply,
    ← TopCat.singularRelativeCup_naturality, ← TopPair.singularCohomologyMap_comp_apply,
    ← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
    ← TopPair.singularCohomologyMap_comp_apply,
    TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (tensorHom_fst f g),
    TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (tensorHom_snd f g)]
  exacts [TopCat.mapsTo_tensorHom_preimage_fst f g hf, TopCat.mapsTo_tensorHom_preimage_snd f g hg]

end TauCeti
