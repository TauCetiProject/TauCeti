/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Relative singular cohomology and the long exact sequence of a pair

The relative singular cochain complex of a topological pair `(X, A)` is obtained by applying the
contravariant functor `Hom(-, M)` to its relative singular chain complex `C(X, A)`.  In each degree
the short exact sequence of chain complexes `0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0` splits, since the
singular simplices of `A` form a subset of those of `X`.  Applying `Hom(-, M)` therefore gives a
short exact sequence of cochain complexes

`0 ⟶ C*(X, A) ⟶ C*(X) ⟶ C*(A) ⟶ 0`,

whose long exact cohomology sequence is the long exact sequence of the pair

`⋯ ⟶ Hⁿ(X, A) ⟶ Hⁿ(X) ⟶ Hⁿ(A) ⟶ Hⁿ⁺¹(X, A) ⟶ ⋯`.

A map of pairs `(X, A) ⟶ (Y, B)` induces maps from the relative cochains and cohomology of
`(Y, B)` to those of `(X, A)`, and the connecting morphism is natural for these maps.

## Main declarations

* `TopPair.singularCochainComplex`, `TopPair.singularCohomology`, and the maps
  `TopPair.singularCochainComplexMap` and `TopPair.singularCohomologyMap` induced by maps of
  pairs, with `TopPair.singularCohomologyFunctor` the functor `TopPairᵒᵖ ⥤ ModuleCat k`.
* `TopPair.shortExact_singularCochainComplexShortComplex`: the cochain sequence of a pair is short
  exact.
* `TopPair.singularCohomologyδ`: the connecting morphism `Hⁿ(A) ⟶ Hᵐ(X, A)` for `n + 1 = m`, with
  the three exactness statements `TopPair.singularCohomology_exact_relative`,
  `TopPair.singularCohomology_exact_space` and `TopPair.singularCohomology_exact_subspace`, and its
  naturality `TopPair.singularCohomologyδ_naturality`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
* J. Riou and A. Yang, [relative homology of simplicial-set pairs in
  Mathlib](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/AlgebraicTopology/SimplicialSet/Homology/Relative.lean).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace TopPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (P : TopPair.{w}) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

/-- The relative singular cochain complex of a topological pair: in degree `n`, the `k`-module of
morphisms from the relative singular `n`-chains with coefficients in `R` to `M`. -/
abbrev singularCochainComplex : CochainComplex (ModuleCat.{v} k) ℕ :=
  (P.singularChainComplex R).linearYonedaObj k M

variable {P R k M}

/-- The cochain map on relative singular cochains induced by a map of topological pairs. -/
abbrev singularCochainComplexMap {P P' : TopPair.{w}} (f : P ⟶ P') :
    P'.singularCochainComplex R k M ⟶ P.singularCochainComplex R k M :=
  (TauCeti.ChainComplex.linearYonedaFunctor k M).map (singularChainComplexMap f R).op

/-- The degree-`n` component of the cochain map induced by `f` acts by precomposition with the
degree-`n` component of the induced relative singular chain map. -/
@[simp]
lemma singularCochainComplexMap_f_apply {P P' : TopPair.{w}} (f : P ⟶ P') (n : ℕ)
    (g : (P'.singularCochainComplex R k M).X n) :
    (singularCochainComplexMap (R := R) (k := k) (M := M) f).f n g =
      (singularChainComplexMap f R).f n ≫ g := rfl

@[simp]
lemma singularCochainComplexMap_id (P : TopPair.{w}) :
    singularCochainComplexMap (R := R) (k := k) (M := M) (𝟙 P) = 𝟙 _ := by
  simp [singularCochainComplexMap, singularChainComplexMap]

@[reassoc]
lemma singularCochainComplexMap_comp {P P' P'' : TopPair.{w}} (f : P ⟶ P') (g : P' ⟶ P'') :
    singularCochainComplexMap (R := R) (k := k) (M := M) (f ≫ g) =
      singularCochainComplexMap g ≫ singularCochainComplexMap f := by
  simp [singularCochainComplexMap, singularChainComplexMap]

variable (P R k M)

/-- The relative singular cohomology of a topological pair in degree `n`. -/
protected abbrev singularCohomology (n : ℕ) : ModuleCat.{v} k :=
  (P.singularCochainComplex R k M).homology n

variable {P R k M}

/-- The map on relative singular cohomology induced by a map of topological pairs. -/
protected abbrev singularCohomologyMap {P P' : TopPair.{w}} (f : P ⟶ P') (n : ℕ) :
    P'.singularCohomology R k M n ⟶ P.singularCohomology R k M n :=
  HomologicalComplex.homologyMap (singularCochainComplexMap f) n

@[simp]
lemma singularCohomologyMap_id (P : TopPair.{w}) (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (𝟙 P) n = 𝟙 _ := by
  simp [TopPair.singularCohomologyMap]

@[reassoc]
lemma singularCohomologyMap_comp {P P' P'' : TopPair.{w}} (f : P ⟶ P') (g : P' ⟶ P'') (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (f ≫ g) n =
      TopPair.singularCohomologyMap g n ≫ TopPair.singularCohomologyMap f n := by
  simp [TopPair.singularCohomologyMap, singularCochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp]

variable (R k M)

/-- Relative singular cohomology in degree `n` as a contravariant functor from topological pairs
to `k`-modules. -/
@[expose, simps]
def singularCohomologyFunctor (n : ℕ) : TopPair.{w}ᵒᵖ ⥤ ModuleCat.{v} k where
  obj P := P.unop.singularCohomology R k M n
  map f := TopPair.singularCohomologyMap f.unop n
  map_comp f g := singularCohomologyMap_comp g.unop f.unop n

section LongExactSequence

variable (P)

/-- The cochain sequence `C*(X, A) ⟶ C*(X) ⟶ C*(A)` of a topological pair `(X, A)`: its maps are
induced by the quotient map from the chains of `X` to the relative chains of `(X, A)`, and by the
inclusion of `A` into `X`. -/
abbrev singularCochainComplexShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk (X₁ := P.singularCochainComplex R k M) (X₂ := P.fst.singularCochainComplex R k M)
    (X₃ := P.snd.singularCochainComplex R k M)
    ((TauCeti.ChainComplex.linearYonedaFunctor k M).map (P.singularChainComplexπ R).op)
    (TopCat.singularCochainComplexMap P.map)
    -- The chain sequence of `P` has the chains of `P.fst` and `P.snd` as its middle and left terms
    -- by definition (`toSSetPair_obj_right`, `toSSetPair_obj_left`), so applying `Hom(-, M)` to it
    -- gives this sequence on the nose.
    ((P.singularChainComplexShortComplex R).op.map
      (TauCeti.ChainComplex.linearYonedaFunctor k M)).zero

/-- The cochain sequence `0 ⟶ C*(X, A) ⟶ C*(X) ⟶ C*(A) ⟶ 0` of a topological pair is short
exact. -/
lemma shortExact_singularCochainComplexShortComplex :
    (P.singularCochainComplexShortComplex R k M).ShortExact :=
  -- As in `singularCochainComplexShortComplex`, the sequence is `Hom(-, M)` applied to the chain
  -- sequence of `P` on the nose.
  TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (P.shortExact_singularChainComplexShortComplex R)

/-- The map `Hⁿ(X, A) ⟶ Hⁿ(X)` from relative to absolute singular cohomology, induced by the
quotient map from the singular chains of `X` to the relative chains of `(X, A)`. -/
abbrev singularCohomologyπ (n : ℕ) :
    P.singularCohomology R k M n ⟶ P.fst.singularCohomology R k M n :=
  HomologicalComplex.homologyMap (P.singularCochainComplexShortComplex R k M).f n

/-- The connecting morphism `Hⁿ(A) ⟶ Hᵐ(X, A)` of the long exact sequence of a topological pair
`(X, A)`, where `n + 1 = m`. -/
abbrev singularCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    P.snd.singularCohomology R k M n ⟶ P.singularCohomology R k M m :=
  (P.shortExact_singularCochainComplexShortComplex R k M).δ n m (by simpa)

@[reassoc]
lemma singularCohomologyδ_comp_singularCohomologyπ (n m : ℕ) (h : n + 1 = m := by lia) :
    P.singularCohomologyδ R k M n m h ≫ P.singularCohomologyπ R k M m = 0 :=
  (P.shortExact_singularCochainComplexShortComplex R k M).δ_comp n m (by simpa)

@[reassoc (attr := simp)]
lemma singularCohomologyπ_comp_singularCohomologyMap (n : ℕ) :
    P.singularCohomologyπ R k M n ≫ TopCat.singularCohomologyMap P.map n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp, (P.singularCochainComplexShortComplex R k M).zero,
    HomologicalComplex.homologyMap_zero]

@[reassoc (attr := simp)]
lemma singularCohomologyMap_comp_singularCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    TopCat.singularCohomologyMap P.map n ≫ P.singularCohomologyδ R k M n m h = 0 :=
  (P.shortExact_singularCochainComplexShortComplex R k M).comp_δ n m (by simpa)

/-- Exactness at relative cohomology: `Hⁿ(A) ⟶ Hᵐ(X, A) ⟶ Hᵐ(X)` is exact for `n + 1 = m`. -/
lemma singularCohomology_exact_relative (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (P.singularCohomologyδ_comp_singularCohomologyπ R k M n m h)).Exact :=
  (P.shortExact_singularCochainComplexShortComplex R k M).homology_exact₁ n m (by simpa)

/-- Exactness at ambient cohomology: `Hⁿ(X, A) ⟶ Hⁿ(X) ⟶ Hⁿ(A)` is exact. -/
lemma singularCohomology_exact_space (n : ℕ) :
    (ShortComplex.mk _ _ (P.singularCohomologyπ_comp_singularCohomologyMap R k M n)).Exact :=
  (P.shortExact_singularCochainComplexShortComplex R k M).homology_exact₂ n

/-- Exactness at subspace cohomology: `Hⁿ(X) ⟶ Hⁿ(A) ⟶ Hᵐ(X, A)` is exact for `n + 1 = m`. -/
lemma singularCohomology_exact_subspace (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (P.singularCohomologyMap_comp_singularCohomologyδ R k M n m h)).Exact :=
  (P.shortExact_singularCochainComplexShortComplex R k M).homology_exact₃ n m (by simpa)

variable {P R k M}

/-- The morphism of cochain sequences `C*(Y, B) ⟶ C*(Y) ⟶ C*(B)` to `C*(X, A) ⟶ C*(X) ⟶ C*(A)`
induced by a map of pairs `(X, A) ⟶ (Y, B)`. -/
@[expose, simps]
def singularCochainComplexShortComplexMap {P P' : TopPair.{w}} (f : P ⟶ P') :
    P'.singularCochainComplexShortComplex R k M ⟶ P.singularCochainComplexShortComplex R k M where
  τ₁ := singularCochainComplexMap f
  τ₂ := TopCat.singularCochainComplexMap (Hom.fst f)
  τ₃ := TopCat.singularCochainComplexMap (Hom.snd f)
  comm₁₂ := by
    have h := congrArg (fun φ ↦ (TauCeti.ChainComplex.linearYonedaFunctor k M).map φ.op)
      (((SSetPair.chainComplexFunctorπ C).app R).naturality (toSSetPair.map f))
    simp only [op_comp, Functor.map_comp] at h
    -- `h` is the required square, with the chain maps of `toSSetPair.map f` written through the
    -- bifunctors of `SSetPair` rather than through `toSSet` and `singularChainComplexπ`.
    exact h.symm
  comm₂₃ := by
    rw [← TopCat.singularCochainComplexMap_comp, ← TopCat.singularCochainComplexMap_comp, Hom.w]

/-- The map from relative to absolute cohomology is natural in the pair. -/
@[reassoc]
lemma singularCohomologyπ_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (n : ℕ) :
    P'.singularCohomologyπ R k M n ≫ TopCat.singularCohomologyMap (Hom.fst f) n =
      TopPair.singularCohomologyMap f n ≫ P.singularCohomologyπ R k M n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (singularCochainComplexShortComplexMap (R := R) (k := k) (M := M) f).comm₁₂).symm.trans
        (HomologicalComplex.homologyMap_comp _ _ n)

/-- The connecting morphism of the long exact sequence of a topological pair is natural: for a
map of pairs `f : (X, A) ⟶ (Y, B)`, following `Hⁿ(B) ⟶ Hᵐ(Y, B)` by the map induced by `f` on
relative cohomology agrees with following the map induced by `f` on `Hⁿ(B)` by
`Hⁿ(A) ⟶ Hᵐ(X, A)`. -/
@[reassoc]
lemma singularCohomologyδ_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (n m : ℕ)
    (h : n + 1 = m := by lia) :
    P'.singularCohomologyδ R k M n m h ≫ TopPair.singularCohomologyMap f m =
      TopCat.singularCohomologyMap (Hom.snd f) n ≫ P.singularCohomologyδ R k M n m h :=
  HomologicalComplex.HomologySequence.δ_naturality (singularCochainComplexShortComplexMap f)
    (P'.shortExact_singularCochainComplexShortComplex R k M)
    (P.shortExact_singularCochainComplexShortComplex R k M) n m (by simpa)

end LongExactSequence

end TopPair
