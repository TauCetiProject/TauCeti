/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coefficients

/-!
# The coefficient long exact sequence in singular homology

Let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be a short exact sequence of coefficients in an abelian category `C`
with exact coproducts (`AB4`), for instance `ModuleCat k`. The singular `n`-chains of a space are a
coproduct of copies of the coefficient object, one for each singular `n`-simplex, so they give a
short exact sequence of singular chain complexes

`0 ⟶ C(X; M₁) ⟶ C(X; M₂) ⟶ C(X; M₃) ⟶ 0`

(`TopCat.shortExact_singularChainComplexCoefficientShortComplex`). Its connecting morphism is the
**Bockstein homomorphism** `Hₙ(X; M₃) ⟶ Hₘ(X; M₁)`, for `m + 1 = n`
(`TopCat.singularHomologyBockstein`), and its long exact homology sequence is the coefficient long
exact sequence

`⋯ ⟶ Hₙ(X; M₁) ⟶ Hₙ(X; M₂) ⟶ Hₙ(X; M₃) ⟶ Hₙ₋₁(X; M₁) ⟶ ⋯`,

whose maps between homology groups of the same degree are induced by the coefficient maps. The
Bockstein homomorphism is natural in continuous maps and in morphisms of short exact sequences of
coefficients.

For `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/2 ⟶ 0`, with first map multiplication by two, this is the sequence relating
integral and mod-two homology; see `TauCeti.AlgebraicTopology.Singular.Coefficients.ModTwo`.
The cohomological counterpart is `TopCat.singularCohomologyBockstein`.

## Main declarations

* `TopCat.singularChainComplexCoefficientShortComplex` and
  `TopCat.shortExact_singularChainComplexCoefficientShortComplex`: the short exact sequence of
  singular chain complexes induced by a short exact sequence of coefficients.
* `TopCat.singularHomologyBockstein`: the Bockstein homomorphism `Hₙ(X; M₃) ⟶ Hₘ(X; M₁)`.
* `TopCat.singularHomology_exact_coefficient₁`, `TopCat.singularHomology_exact_coefficient₂`,
  `TopCat.singularHomology_exact_coefficient₃`: exactness at the three kinds of terms.
* `TopCat.singularHomologyBockstein_naturality`,
  `TopCat.singularHomologyBockstein_naturality_coefficients`: naturality.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.E (Bockstein homomorphisms) and Section 2.1, Theorem 2.16 (the long exact sequence
  of a short exact sequence of chain complexes).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- The sequence of singular chain complexes `C(X; S.X₁) ⟶ C(X; S.X₂) ⟶ C(X; S.X₃)` induced by a
short complex `S` of coefficients: its maps are the chain maps induced by the maps of `S`. -/
abbrev singularChainComplexCoefficientShortComplex (X : TopCat.{w}) (S : ShortComplex C) :
    ShortComplex (ChainComplex C ℕ) :=
  S.map ((singularChainComplexFunctor C).flip.obj X)

/-- The morphism from the coefficient chain sequence of `X` to that of `Y` induced by a continuous
map `f : X ⟶ Y`: its components are the chain maps induced by `f`. -/
abbrev singularChainComplexCoefficientShortComplexMap {X Y : TopCat.{w}} (f : X ⟶ Y)
    (S : ShortComplex C) :
    X.singularChainComplexCoefficientShortComplex S ⟶
      Y.singularChainComplexCoefficientShortComplex S :=
  S.mapNatTrans ((singularChainComplexFunctor C).flip.map f)

variable [AB4OfSize.{w} C]

/-- A short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of coefficients induces a short exact sequence
`0 ⟶ C(X; M₁) ⟶ C(X; M₂) ⟶ C(X; M₃) ⟶ 0` of singular chain complexes. -/
lemma shortExact_singularChainComplexCoefficientShortComplex (X : TopCat.{w})
    {S : ShortComplex C} (hS : S.ShortExact) :
    (X.singularChainComplexCoefficientShortComplex S).ShortExact :=
  hS.map_simplicialChains (toSSet.obj X)

variable [CategoryWithHomology C]

/-- The Bockstein homomorphism `Hₙ(X; M₃) ⟶ Hₘ(X; M₁)`, for `m + 1 = n`, of a short exact sequence
`0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of coefficients: the connecting morphism of the long exact homology
sequence of the short exact sequence of singular chain complexes. -/
def singularHomologyBockstein (X : TopCat.{w}) {S : ShortComplex C} (hS : S.ShortExact)
    (n m : ℕ) (h : m + 1 = n := by lia) :
    ((singularHomologyFunctor C n).obj S.X₃).obj X ⟶
      ((singularHomologyFunctor C m).obj S.X₁).obj X :=
  (X.shortExact_singularChainComplexCoefficientShortComplex hS).δ n m (by simpa)

/-- The Bockstein homomorphism is, by definition, the connecting morphism of the short exact
sequence `0 ⟶ C(X; M₁) ⟶ C(X; M₂) ⟶ C(X; M₃) ⟶ 0` of singular chain complexes. -/
lemma singularHomologyBockstein_eq_δ (X : TopCat.{w}) {S : ShortComplex C} (hS : S.ShortExact)
    (n m : ℕ) (h : m + 1 = n := by lia) :
    X.singularHomologyBockstein hS n m h =
      (X.shortExact_singularChainComplexCoefficientShortComplex hS).δ n m (by simpa) :=
  (rfl)

section Exactness

variable (X : TopCat.{w}) {S : ShortComplex C} (hS : S.ShortExact)

@[reassoc (attr := simp)]
lemma comp_singularHomologyBockstein (n m : ℕ) (h : m + 1 = n := by lia) :
    ((singularHomologyFunctor C n).map S.g).app X ≫ X.singularHomologyBockstein hS n m h = 0 :=
  (X.shortExact_singularChainComplexCoefficientShortComplex hS).comp_δ n m (by simpa)

@[reassoc (attr := simp)]
lemma singularHomologyBockstein_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    X.singularHomologyBockstein hS n m h ≫ ((singularHomologyFunctor C m).map S.f).app X = 0 :=
  (X.shortExact_singularChainComplexCoefficientShortComplex hS).δ_comp n m (by simpa)

/-- Exactness at `Hₘ(X; M₁)`: `Hₙ(X; M₃) ⟶ Hₘ(X; M₁) ⟶ Hₘ(X; M₂)` is exact for `m + 1 = n`. -/
lemma singularHomology_exact_coefficient₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (X.singularHomologyBockstein_comp hS n m h)).Exact :=
  (X.shortExact_singularChainComplexCoefficientShortComplex hS).homology_exact₁ n m (by simpa)

include hS in
/-- Exactness at `Hₙ(X; M₂)`: `Hₙ(X; M₁) ⟶ Hₙ(X; M₂) ⟶ Hₙ(X; M₃)` is exact. -/
lemma singularHomology_exact_coefficient₂ (n : ℕ) :
    ((X.singularChainComplexCoefficientShortComplex S).map
      (HomologicalComplex.homologyFunctor _ _ n)).Exact :=
  (X.shortExact_singularChainComplexCoefficientShortComplex hS).homology_exact₂ n

/-- Exactness at `Hₙ(X; M₃)`: `Hₙ(X; M₂) ⟶ Hₙ(X; M₃) ⟶ Hₘ(X; M₁)` is exact for `m + 1 = n`. -/
lemma singularHomology_exact_coefficient₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (X.comp_singularHomologyBockstein hS n m h)).Exact :=
  (X.shortExact_singularChainComplexCoefficientShortComplex hS).homology_exact₃ n m (by simpa)

end Exactness

section Naturality

variable {S : ShortComplex C} (hS : S.ShortExact)

/-- The Bockstein homomorphism is natural in the space: for a continuous map `f : X ⟶ Y`, following
`Hₙ(X; M₃) ⟶ Hₘ(X; M₁)` by the map induced by `f` agrees with following the map induced by `f` by
`Hₙ(Y; M₃) ⟶ Hₘ(Y; M₁)`. -/
@[reassoc]
lemma singularHomologyBockstein_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    X.singularHomologyBockstein hS n m h ≫ ((singularHomologyFunctor C m).obj S.X₁).map f =
      ((singularHomologyFunctor C n).obj S.X₃).map f ≫ Y.singularHomologyBockstein hS n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    (singularChainComplexCoefficientShortComplexMap f S)
    (X.shortExact_singularChainComplexCoefficientShortComplex hS)
    (Y.shortExact_singularChainComplexCoefficientShortComplex hS) n m (by simpa)

/-- The Bockstein homomorphism is natural in the short exact sequence of coefficients: a morphism
`φ : S ⟶ S'` of short exact sequences of coefficients commutes with the Bockstein homomorphisms of
`S` and `S'` and the maps on singular homology induced by its components. -/
@[reassoc]
lemma singularHomologyBockstein_naturality_coefficients (X : TopCat.{w}) {S' : ShortComplex C}
    (hS' : S'.ShortExact) (φ : S ⟶ S') (n m : ℕ) (h : m + 1 = n := by lia) :
    X.singularHomologyBockstein hS n m h ≫ ((singularHomologyFunctor C m).map φ.τ₁).app X =
      ((singularHomologyFunctor C n).map φ.τ₃).app X ≫
        X.singularHomologyBockstein hS' n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    (((singularChainComplexFunctor C).flip.obj X).mapShortComplex.map φ)
    (X.shortExact_singularChainComplexCoefficientShortComplex hS)
    (X.shortExact_singularChainComplexCoefficientShortComplex hS') n m (by simpa)

end Naturality

end TopCat
