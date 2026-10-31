/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The coefficient long exact sequence and the Bockstein homomorphism

Let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be a short exact sequence of coefficients in a `k`-linear abelian
category `C` with coproducts, and let `R : C` be projective; for the usual singular cohomology
with coefficients in `k`-modules, take `C := ModuleCat k` and `R := k`. The singular chains
`Cₙ(X; R)` of a space are a coproduct of copies of `R`, hence projective
(`SSet.projective_chainComplex_X_of_projective`), and so are the relative chains `Cₙ(X, A; R)` of a
pair, which are a direct summand of `Cₙ(X; R)`. The functors `Hom(C(X; R), -)` and
`Hom(C(X, A; R), -)` of the coefficients are therefore exact, which gives short exact sequences of
singular cochain complexes

`0 ⟶ C*(X; M₁) ⟶ C*(X; M₂) ⟶ C*(X; M₃) ⟶ 0`,
`0 ⟶ C*(X, A; M₁) ⟶ C*(X, A; M₂) ⟶ C*(X, A; M₃) ⟶ 0`.

Their connecting morphisms are the Bockstein homomorphisms `Hⁿ(X; M₃) ⟶ Hⁿ⁺¹(X; M₁)` and
`Hⁿ(X, A; M₃) ⟶ Hⁿ⁺¹(X, A; M₁)`, and their long exact cohomology sequences are the coefficient long
exact sequences

`⋯ ⟶ Hⁿ(X; M₁) ⟶ Hⁿ(X; M₂) ⟶ Hⁿ(X; M₃) ⟶ Hⁿ⁺¹(X; M₁) ⟶ ⋯`,

whose maps between the cohomology groups with the same degree are induced by the coefficient maps.
The Bockstein homomorphism is natural in continuous maps, respectively maps of pairs, and in
morphisms of short exact sequences of coefficients.

Exactness in the coefficients is the only input: for a fixed chain complex `K` whose terms are
projective, `Hom(K, -)` is exact (`ChainComplex.shortExact_map_linearYonedaObjFunctor`). It is not
the long exact sequence of a pair, which instead uses that the chain sequence of a pair splits in
each degree.

## Main declarations

* `TopCat.singularCochainComplexCoefficientShortComplex` and
  `TopCat.shortExact_singularCochainComplexCoefficientShortComplex`: the short exact sequence of
  singular cochain complexes induced by a short exact sequence of coefficients.
* `TopCat.singularCohomologyBockstein`: the Bockstein homomorphism `Hⁿ(X; M₃) ⟶ Hᵐ(X; M₁)` for
  `n + 1 = m`, with the three exactness statements `TopCat.singularCohomology_exact_coefficient₁`,
  `TopCat.singularCohomology_exact_coefficient₂` and `TopCat.singularCohomology_exact_coefficient₃`
  and the naturality statements `TopCat.singularCohomologyBockstein_naturality` and
  `TopCat.singularCohomologyBockstein_naturality_coefficients`.
* `TopPair.singularCochainComplexCoefficientShortComplex`, `TopPair.singularCohomologyBockstein`
  and their exactness and naturality statements: the same for relative singular cohomology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.E.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C]

/-- The sequence of singular cochain complexes `C*(X; S.X₁) ⟶ C*(X; S.X₂) ⟶ C*(X; S.X₃)` induced by
a short complex `S` of coefficients: its maps are postcomposition with the maps of `S`. -/
abbrev singularCochainComplexCoefficientShortComplex (X : TopCat.{w}) (S : ShortComplex C) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  S.map (((toSSet.obj X).chainComplex R).linearYonedaObjFunctor k)

variable {R k} in
/-- The morphism from the coefficient cochain sequence of `Y` to that of `X` induced by a continuous
map `f : X ⟶ Y`: its components are the cochain maps induced by `f`. -/
def singularCochainComplexCoefficientShortComplexMap {X Y : TopCat.{w}} (f : X ⟶ Y)
    (S : ShortComplex C) :
    Y.singularCochainComplexCoefficientShortComplex R k S ⟶
      X.singularCochainComplexCoefficientShortComplex R k S :=
  S.mapNatTrans (ChainComplex.linearYonedaObjFunctorMap k (SSet.chainComplexMap (toSSet.map f) R))

section

variable {R k} {X Y : TopCat.{w}} (f : X ⟶ Y) (S : ShortComplex C)

@[simp]
lemma singularCochainComplexCoefficientShortComplexMap_τ₁ :
    (singularCochainComplexCoefficientShortComplexMap (R := R) (k := k) f S).τ₁ =
      singularCochainComplexMap f := by
  rw [singularCochainComplexCoefficientShortComplexMap, ShortComplex.mapNatTrans_τ₁,
    ChainComplex.linearYonedaObjFunctorMap_app]

@[simp]
lemma singularCochainComplexCoefficientShortComplexMap_τ₂ :
    (singularCochainComplexCoefficientShortComplexMap (R := R) (k := k) f S).τ₂ =
      singularCochainComplexMap f := by
  rw [singularCochainComplexCoefficientShortComplexMap, ShortComplex.mapNatTrans_τ₂,
    ChainComplex.linearYonedaObjFunctorMap_app]

@[simp]
lemma singularCochainComplexCoefficientShortComplexMap_τ₃ :
    (singularCochainComplexCoefficientShortComplexMap (R := R) (k := k) f S).τ₃ =
      singularCochainComplexMap f := by
  rw [singularCochainComplexCoefficientShortComplexMap, ShortComplex.mapNatTrans_τ₃,
    ChainComplex.linearYonedaObjFunctorMap_app]

end

variable [Projective R]

/-- A short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of coefficients induces a short exact sequence
`0 ⟶ C*(X; M₁) ⟶ C*(X; M₂) ⟶ C*(X; M₃) ⟶ 0` of singular cochain complexes. -/
lemma shortExact_singularCochainComplexCoefficientShortComplex (X : TopCat.{w})
    {S : ShortComplex C} (hS : S.ShortExact) :
    (X.singularCochainComplexCoefficientShortComplex R k S).ShortExact :=
  ((toSSet.obj X).chainComplex R).shortExact_map_linearYonedaObjFunctor k hS

/-- The Bockstein homomorphism `Hⁿ(X; M₃) ⟶ Hᵐ(X; M₁)`, for `n + 1 = m`, of a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of coefficients: the connecting morphism of the long exact cohomology
sequence of the short exact sequence of singular cochain complexes. -/
def singularCohomologyBockstein (X : TopCat.{w}) {S : ShortComplex C} (hS : S.ShortExact)
    (n m : ℕ) (h : n + 1 = m := by lia) :
    X.singularCohomology R k S.X₃ n ⟶ X.singularCohomology R k S.X₁ m :=
  (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS).δ n m (by simpa)

section Exactness

variable (X : TopCat.{w}) {S : ShortComplex C} (hS : S.ShortExact)

@[reassoc (attr := simp)]
lemma comp_singularCohomologyBockstein (n m : ℕ) (h : n + 1 = m := by lia) :
    HomologicalComplex.homologyMap (((toSSet.obj X).chainComplex R).linearYonedaObjMap k S.g) n ≫
      X.singularCohomologyBockstein R k hS n m h = 0 :=
  (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS).comp_δ n m (by simpa)

@[reassoc (attr := simp)]
lemma singularCohomologyBockstein_comp (n m : ℕ) (h : n + 1 = m := by lia) :
    X.singularCohomologyBockstein R k hS n m h ≫
      HomologicalComplex.homologyMap (((toSSet.obj X).chainComplex R).linearYonedaObjMap k S.f) m =
        0 :=
  (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS).δ_comp n m (by simpa)

/-- Exactness at `Hᵐ(X; M₁)`: `Hⁿ(X; M₃) ⟶ Hᵐ(X; M₁) ⟶ Hᵐ(X; M₂)` is exact for `n + 1 = m`. -/
lemma singularCohomology_exact_coefficient₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (X.singularCohomologyBockstein_comp R k hS n m h)).Exact :=
  (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS).homology_exact₁ n m
    (by simpa)

include hS in
/-- Exactness at `Hⁿ(X; M₂)`: `Hⁿ(X; M₁) ⟶ Hⁿ(X; M₂) ⟶ Hⁿ(X; M₃)` is exact. -/
lemma singularCohomology_exact_coefficient₂ (n : ℕ) :
    ((X.singularCochainComplexCoefficientShortComplex R k S).map
      (HomologicalComplex.homologyFunctor _ _ n)).Exact :=
  (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS).homology_exact₂ n

/-- Exactness at `Hⁿ(X; M₃)`: `Hⁿ(X; M₂) ⟶ Hⁿ(X; M₃) ⟶ Hᵐ(X; M₁)` is exact for `n + 1 = m`. -/
lemma singularCohomology_exact_coefficient₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (X.comp_singularCohomologyBockstein R k hS n m h)).Exact :=
  (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS).homology_exact₃ n m
    (by simpa)

end Exactness

section Naturality

variable {S : ShortComplex C} (hS : S.ShortExact)

/-- The Bockstein homomorphism is natural in the space: for a continuous map `f : X ⟶ Y`, following
`Hⁿ(Y; M₃) ⟶ Hᵐ(Y; M₁)` by the map induced by `f` agrees with following the map induced by `f` by
`Hⁿ(X; M₃) ⟶ Hᵐ(X; M₁)`. -/
@[reassoc]
lemma singularCohomologyBockstein_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    Y.singularCohomologyBockstein R k hS n m h ≫ TopCat.singularCohomologyMap f m =
      TopCat.singularCohomologyMap f n ≫ X.singularCohomologyBockstein R k hS n m h := by
  have := HomologicalComplex.HomologySequence.δ_naturality
    (singularCochainComplexCoefficientShortComplexMap f S)
    (Y.shortExact_singularCochainComplexCoefficientShortComplex R k hS)
    (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS) n m (by simpa)
  rw [singularCochainComplexCoefficientShortComplexMap_τ₁,
    singularCochainComplexCoefficientShortComplexMap_τ₃] at this
  exact this

/-- The Bockstein homomorphism is natural in the short exact sequence of coefficients: a morphism
`φ : S ⟶ S'` of short exact sequences of coefficients commutes with the Bockstein homomorphisms of
`S` and `S'` and the maps on singular cohomology induced by its components. -/
@[reassoc]
lemma singularCohomologyBockstein_naturality_coefficients (X : TopCat.{w}) {S' : ShortComplex C}
    (hS' : S'.ShortExact) (φ : S ⟶ S') (n m : ℕ) (h : n + 1 = m := by lia) :
    X.singularCohomologyBockstein R k hS n m h ≫
        HomologicalComplex.homologyMap
          (((toSSet.obj X).chainComplex R).linearYonedaObjMap k φ.τ₁) m =
      HomologicalComplex.homologyMap
          (((toSSet.obj X).chainComplex R).linearYonedaObjMap k φ.τ₃) n ≫
        X.singularCohomologyBockstein R k hS' n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((((toSSet.obj X).chainComplex R).linearYonedaObjFunctor k).mapShortComplex.map φ)
    (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS)
    (X.shortExact_singularCochainComplexCoefficientShortComplex R k hS') n m (by simpa)

end Naturality

end TopCat

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (P : TopPair.{w}) (R : C) (k : Type*) [Ring k] [Linear k C]

/-- The sequence of relative singular cochain complexes
`C*(X, A; S.X₁) ⟶ C*(X, A; S.X₂) ⟶ C*(X, A; S.X₃)` of a pair `(X, A)` induced by a short complex
`S` of coefficients: its maps are postcomposition with the maps of `S`. -/
abbrev singularCochainComplexCoefficientShortComplex (S : ShortComplex C) :
    ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  S.map ((P.singularChainComplex R).linearYonedaObjFunctor k)

variable {R k} in
/-- The morphism from the coefficient cochain sequence of `(Y, B)` to that of `(X, A)` induced by a
map of pairs `f : (X, A) ⟶ (Y, B)`: its components are the relative cochain maps induced by `f`. -/
def singularCochainComplexCoefficientShortComplexMap {P P' : TopPair.{w}} (f : P ⟶ P')
    (S : ShortComplex C) :
    P'.singularCochainComplexCoefficientShortComplex R k S ⟶
      P.singularCochainComplexCoefficientShortComplex R k S :=
  S.mapNatTrans (ChainComplex.linearYonedaObjFunctorMap k (singularChainComplexMap f R))

section

variable {R k} {P P' : TopPair.{w}} (f : P ⟶ P') (S : ShortComplex C)

@[simp]
lemma singularCochainComplexCoefficientShortComplexMap_τ₁ :
    (singularCochainComplexCoefficientShortComplexMap (R := R) (k := k) f S).τ₁ =
      singularCochainComplexMap f := by
  rw [singularCochainComplexCoefficientShortComplexMap, ShortComplex.mapNatTrans_τ₁,
    ChainComplex.linearYonedaObjFunctorMap_app]

@[simp]
lemma singularCochainComplexCoefficientShortComplexMap_τ₂ :
    (singularCochainComplexCoefficientShortComplexMap (R := R) (k := k) f S).τ₂ =
      singularCochainComplexMap f := by
  rw [singularCochainComplexCoefficientShortComplexMap, ShortComplex.mapNatTrans_τ₂,
    ChainComplex.linearYonedaObjFunctorMap_app]

@[simp]
lemma singularCochainComplexCoefficientShortComplexMap_τ₃ :
    (singularCochainComplexCoefficientShortComplexMap (R := R) (k := k) f S).τ₃ =
      singularCochainComplexMap f := by
  rw [singularCochainComplexCoefficientShortComplexMap, ShortComplex.mapNatTrans_τ₃,
    ChainComplex.linearYonedaObjFunctorMap_app]

end

variable [Projective R]

/-- A short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of coefficients induces a short exact sequence
`0 ⟶ C*(X, A; M₁) ⟶ C*(X, A; M₂) ⟶ C*(X, A; M₃) ⟶ 0` of relative singular cochain complexes. -/
lemma shortExact_singularCochainComplexCoefficientShortComplex {S : ShortComplex C}
    (hS : S.ShortExact) : (P.singularCochainComplexCoefficientShortComplex R k S).ShortExact :=
  (P.singularChainComplex R).shortExact_map_linearYonedaObjFunctor k hS

/-- The Bockstein homomorphism `Hⁿ(X, A; M₃) ⟶ Hᵐ(X, A; M₁)`, for `n + 1 = m`, of a short exact
sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of coefficients: the connecting morphism of the long exact
cohomology sequence of the short exact sequence of relative singular cochain complexes. -/
def singularCohomologyBockstein {S : ShortComplex C} (hS : S.ShortExact) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    P.singularCohomology R k S.X₃ n ⟶ P.singularCohomology R k S.X₁ m :=
  (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS).δ n m (by simpa)

section Exactness

variable {S : ShortComplex C} (hS : S.ShortExact)

@[reassoc (attr := simp)]
lemma comp_singularCohomologyBockstein (n m : ℕ) (h : n + 1 = m := by lia) :
    HomologicalComplex.homologyMap ((P.singularChainComplex R).linearYonedaObjMap k S.g) n ≫
      P.singularCohomologyBockstein R k hS n m h = 0 :=
  (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS).comp_δ n m (by simpa)

@[reassoc (attr := simp)]
lemma singularCohomologyBockstein_comp (n m : ℕ) (h : n + 1 = m := by lia) :
    P.singularCohomologyBockstein R k hS n m h ≫
      HomologicalComplex.homologyMap ((P.singularChainComplex R).linearYonedaObjMap k S.f) m = 0 :=
  (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS).δ_comp n m (by simpa)

/-- Exactness at `Hᵐ(X, A; M₁)`: `Hⁿ(X, A; M₃) ⟶ Hᵐ(X, A; M₁) ⟶ Hᵐ(X, A; M₂)` is exact for
`n + 1 = m`. -/
lemma singularCohomology_exact_coefficient₁ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (P.singularCohomologyBockstein_comp R k hS n m h)).Exact :=
  (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS).homology_exact₁ n m
    (by simpa)

include hS in
/-- Exactness at `Hⁿ(X, A; M₂)`: `Hⁿ(X, A; M₁) ⟶ Hⁿ(X, A; M₂) ⟶ Hⁿ(X, A; M₃)` is exact. -/
lemma singularCohomology_exact_coefficient₂ (n : ℕ) :
    ((P.singularCochainComplexCoefficientShortComplex R k S).map
      (HomologicalComplex.homologyFunctor _ _ n)).Exact :=
  (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS).homology_exact₂ n

/-- Exactness at `Hⁿ(X, A; M₃)`: `Hⁿ(X, A; M₂) ⟶ Hⁿ(X, A; M₃) ⟶ Hᵐ(X, A; M₁)` is exact for
`n + 1 = m`. -/
lemma singularCohomology_exact_coefficient₃ (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (P.comp_singularCohomologyBockstein R k hS n m h)).Exact :=
  (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS).homology_exact₃ n m
    (by simpa)

end Exactness

section Naturality

variable {S : ShortComplex C} (hS : S.ShortExact)

/-- The relative Bockstein homomorphism is natural in maps of pairs: for `f : (X, A) ⟶ (Y, B)`,
following `Hⁿ(Y, B; M₃) ⟶ Hᵐ(Y, B; M₁)` by the map induced by `f` agrees with following the map
induced by `f` by `Hⁿ(X, A; M₃) ⟶ Hᵐ(X, A; M₁)`. -/
@[reassoc]
lemma singularCohomologyBockstein_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (n m : ℕ)
    (h : n + 1 = m := by lia) :
    P'.singularCohomologyBockstein R k hS n m h ≫ TopPair.singularCohomologyMap f m =
      TopPair.singularCohomologyMap f n ≫ P.singularCohomologyBockstein R k hS n m h := by
  have := HomologicalComplex.HomologySequence.δ_naturality
    (singularCochainComplexCoefficientShortComplexMap f S)
    (P'.shortExact_singularCochainComplexCoefficientShortComplex R k hS)
    (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS) n m (by simpa)
  rw [singularCochainComplexCoefficientShortComplexMap_τ₁,
    singularCochainComplexCoefficientShortComplexMap_τ₃] at this
  exact this

/-- The relative Bockstein homomorphism is natural in the short exact sequence of coefficients: a
morphism `φ : S ⟶ S'` of short exact sequences of coefficients commutes with the Bockstein
homomorphisms of `S` and `S'` and the maps on relative singular cohomology induced by its
components. -/
@[reassoc]
lemma singularCohomologyBockstein_naturality_coefficients {S' : ShortComplex C}
    (hS' : S'.ShortExact) (φ : S ⟶ S') (n m : ℕ) (h : n + 1 = m := by lia) :
    P.singularCohomologyBockstein R k hS n m h ≫
        HomologicalComplex.homologyMap ((P.singularChainComplex R).linearYonedaObjMap k φ.τ₁) m =
      HomologicalComplex.homologyMap ((P.singularChainComplex R).linearYonedaObjMap k φ.τ₃) n ≫
        P.singularCohomologyBockstein R k hS' n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    (((P.singularChainComplex R).linearYonedaObjFunctor k).mapShortComplex.map φ)
    (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS)
    (P.shortExact_singularCochainComplexCoefficientShortComplex R k hS') n m (by simpa)

end Naturality

end TopPair
