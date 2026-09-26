/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.AlgebraicTopology.Singular.Relative
public import TauCeti.CategoryTheory.Abelian.DiagramLemmas.CokernelComp
public import TauCeti.Topology.Category.TopTriple

/-!
# The long exact sequence of a triple in relative singular homology

For a triple `B ⊆ A ⊆ X` of topological spaces the relative singular chain complexes of the
three pairs it determines form a short exact sequence

`0 ⟶ C(A, B) ⟶ C(X, B) ⟶ C(X, A) ⟶ 0`,

because each of them is the quotient of the singular chains of the ambient space by those of the
subspace.  The associated long homology sequence is the long exact sequence of the triple

`⋯ ⟶ Hₙ(A, B) ⟶ Hₙ(X, B) ⟶ Hₙ(X, A) ⟶ Hₙ₋₁(A, B) ⟶ ⋯`.

Each of the three pairs is a functor of the triple, so the three relative homology groups are
functorial as well, and the connecting morphism is natural for morphisms of triples.

The source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

namespace TopTriple

section

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (T : TopTriple.{w}) (R : C)

@[reassoc]
lemma singularChainComplexπ_comp_innerToTotal :
    (innerPair.obj T).singularChainComplexπ R ≫
        TopPair.singularChainComplexMap (innerToTotal.app T) R =
      SSet.chainComplexMap (TopCat.toSSet.map T.outerMap) R ≫
        (totalPair.obj T).singularChainComplexπ R := by
  rw [← innerToTotal_app_fst]
  exact (((SSetPair.chainComplexFunctorπ C).app R).naturality
    (TopPair.toSSetPair.map (innerToTotal.app T))).symm

@[reassoc]
lemma singularChainComplexπ_comp_totalToOuter :
    (totalPair.obj T).singularChainComplexπ R ≫
        TopPair.singularChainComplexMap (totalToOuter.app T) R =
      (outerPair.obj T).singularChainComplexπ R := by
  -- The map of pairs `(X, B) ⟶ (X, A)` is the identity on the ambient space `X`, so the map
  -- it induces on the chains of that ambient space is the identity.  The two pairs share that
  -- ambient space only definitionally, so the identity is taken at the outer pair, which is the
  -- form the rewrite below needs.
  have key : SSet.chainComplexMap (TopPair.toSSetPair.map (totalToOuter.app T)).right R =
      𝟙 ((TopPair.toSSetPair.obj (outerPair.obj T)).right.chainComplex R) := by
    have h : TopCat.toSSet.map (TopPair.Hom.fst (totalToOuter.app T)) = 𝟙 _ := by
      rw [totalToOuter_app_fst, TopCat.toSSet.map_id]
    exact (congrArg (((SSet.chainComplexFunctor C).obj R).map) h).trans
      (((SSet.chainComplexFunctor C).obj R).map_id _)
  conv_rhs => rw [← Category.id_comp ((outerPair.obj T).singularChainComplexπ R), ← key]
  exact (((SSetPair.chainComplexFunctorπ C).app R).naturality
    (TopPair.toSSetPair.map (totalToOuter.app T))).symm

lemma singularChainComplexMap_innerToTotal_comp_totalToOuter :
    TopPair.singularChainComplexMap (innerToTotal.app T) R ≫
      TopPair.singularChainComplexMap (totalToOuter.app T) R = 0 :=
  -- The epimorphism and, below, the monomorphism are supplied explicitly rather than by
  -- instance search: the surrounding composites present these maps in definitionally equal
  -- but syntactically different forms.
  comp_eq_zero_of_epi (inferInstanceAs (Epi ((innerPair.obj T).singularChainComplexπ R)))
    (TopPair.chainComplexMap_comp_singularChainComplexπ (outerPair.obj T) R)
    (T.singularChainComplexπ_comp_innerToTotal R)
    (T.singularChainComplexπ_comp_totalToOuter R)

/-- The chain complex sequence of a triple `(X, A, B)`: the relative singular chains of `(A, B)`,
of `(X, B)` and of `(X, A)`. -/
noncomputable abbrev singularChainComplexShortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk _ _ (T.singularChainComplexMap_innerToTotal_comp_totalToOuter R)

/-- The morphism from the relative singular chain sequence of the pair `(X, A)` to that of the
triple `(X, A, B)` given by the quotient maps modulo the chains of `B`. -/
@[simps]
private noncomputable def outerPairToShortComplexMap :
    (outerPair.obj T).singularChainComplexShortComplex R ⟶
      T.singularChainComplexShortComplex R where
  τ₁ := (innerPair.obj T).singularChainComplexπ R
  τ₂ := (totalPair.obj T).singularChainComplexπ R
  τ₃ := 𝟙 _
  comm₁₂ := T.singularChainComplexπ_comp_innerToTotal R
  comm₂₃ := (T.singularChainComplexπ_comp_totalToOuter R).trans (Category.comp_id _).symm

/-- The morphism of relative singular chain sequences induced by a morphism of triples, used to
prove the naturality of the connecting morphism. -/
private noncomputable def singularChainComplexShortComplexMap {T T' : TopTriple.{w}} (φ : T ⟶ T')
    (R : C) : T.singularChainComplexShortComplex R ⟶ T'.singularChainComplexShortComplex R where
  τ₁ := TopPair.singularChainComplexMap (innerPair.map φ) R
  τ₂ := TopPair.singularChainComplexMap (totalPair.map φ) R
  τ₃ := TopPair.singularChainComplexMap (outerPair.map φ) R
  comm₁₂ := (Functor.whiskerRight innerToTotal
    (TopPair.toSSetPair ⋙ (SSetPair.chainComplexFunctor C).obj R)).naturality φ
  comm₂₃ := (Functor.whiskerRight totalToOuter
    (TopPair.toSSetPair ⋙ (SSetPair.chainComplexFunctor C).obj R)).naturality φ

end

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
  (T : TopTriple.{w}) (R : A)

/-- The relative singular chain sequence of a triple is short exact. -/
lemma shortExact_singularChainComplexShortComplex :
    (T.singularChainComplexShortComplex R).ShortExact := by
  refine shortExact_of_isColimit_cokernelCofork ?_
    (inferInstanceAs (Mono (SSet.chainComplexMap
      (TopPair.toSSetPair.obj (outerPair.obj T)).hom R)))
    ((innerPair.obj T).isColimitCokernelCoforkSingularChainComplex R)
    ((totalPair.obj T).isColimitCokernelCoforkSingularChainComplex R)
    ((outerPair.obj T).isColimitCokernelCoforkSingularChainComplex R)
    (T.singularChainComplexπ_comp_innerToTotal R)
    (T.singularChainComplexπ_comp_totalToOuter R)
  -- It remains to see that the chains of `B ⟶ A ⟶ X` compose to the chains of `B ⟶ X`.
  have h : TopCat.toSSet.map T.innerMap ≫ TopCat.toSSet.map T.outerMap =
      TopCat.toSSet.map T.totalMap := by
    rw [← Functor.map_comp, T.innerMap_comp_outerMap]
  exact (((SSet.chainComplexFunctor A).obj R).map_comp _ _).symm.trans (congrArg _ h)

/-- The connecting morphism `Hₙ(X, A) ⟶ Hₘ(A, B)` in the long exact sequence of a triple, for
`m + 1 = n`. -/
@[no_expose]
noncomputable def singularHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (outerPair.obj T).singularHomology R n ⟶ (innerPair.obj T).singularHomology R m :=
  (T.shortExact_singularChainComplexShortComplex R).δ n m (by simpa)

@[reassoc (attr := simp)]
lemma singularHomologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    T.singularHomologyδ R n m h ≫ TopPair.singularHomologyMap (innerToTotal.app T) R m = 0 :=
  (T.shortExact_singularChainComplexShortComplex R).δ_comp n m (by simpa)

@[reassoc (attr := simp)]
lemma comp_singularHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    TopPair.singularHomologyMap (totalToOuter.app T) R n ≫ T.singularHomologyδ R n m h = 0 :=
  (T.shortExact_singularChainComplexShortComplex R).comp_δ n m (by simpa)

@[reassoc (attr := simp)]
lemma singularHomologyMap_innerToTotal_comp_totalToOuter (n : ℕ) :
    TopPair.singularHomologyMap (innerToTotal.app T) R n ≫
      TopPair.singularHomologyMap (totalToOuter.app T) R n = 0 := by
  simp [← HomologicalComplex.homologyMap_comp,
    T.singularChainComplexMap_innerToTotal_comp_totalToOuter R]

/-- Exactness at `Hₘ(A, B)` in the long exact sequence of a triple. -/
lemma singularHomology_exact_inner (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (T.singularHomologyδ_comp R n m h)).Exact :=
  (T.shortExact_singularChainComplexShortComplex R).homology_exact₁ n m (by simpa)

/-- Exactness at `Hₙ(X, B)` in the long exact sequence of a triple. -/
lemma singularHomology_exact_total (n : ℕ) :
    (ShortComplex.mk _ _ (T.singularHomologyMap_innerToTotal_comp_totalToOuter R n)).Exact :=
  (T.shortExact_singularChainComplexShortComplex R).homology_exact₂ n

/-- Exactness at `Hₙ(X, A)` in the long exact sequence of a triple. -/
lemma singularHomology_exact_outer (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (T.comp_singularHomologyδ R n m h)).Exact :=
  (T.shortExact_singularChainComplexShortComplex R).homology_exact₃ n m (by simpa)

/-- The connecting morphism of a triple `(X, A, B)` is the connecting morphism of the pair
`(X, A)` followed by the map `Hₘ(A) ⟶ Hₘ(A, B)`.  This factorization is what makes two consecutive
connecting morphisms of a filtration compose to zero. -/
@[reassoc]
lemma singularHomologyδ_eq_comp_singularHomologyπ (n m : ℕ) (h : m + 1 = n := by lia) :
    T.singularHomologyδ R n m h =
      (outerPair.obj T).singularHomologyδ R n m h ≫
        (innerPair.obj T).singularHomologyπ R m := by
  have key := HomologicalComplex.HomologySequence.δ_naturality
    (outerPairToShortComplexMap T R)
    ((outerPair.obj T).shortExact_singularChainComplexShortComplex R)
    (T.shortExact_singularChainComplexShortComplex R) n m (by simpa)
  simp only [outerPairToShortComplexMap_τ₁, outerPairToShortComplexMap_τ₃,
    HomologicalComplex.homologyMap_id, Category.id_comp] at key
  exact key.symm

/-- The connecting morphism of the long exact sequence of a triple is natural: for a morphism of
triples `φ : (X, A, B) ⟶ (X', A', B')`, following `Hₙ(X, A) ⟶ Hₘ(A, B)` by the map induced by `φ`
on `Hₘ(A, B)` agrees with following the map induced by `φ` on `Hₙ(X, A)` by
`Hₙ(X', A') ⟶ Hₘ(A', B')`. -/
@[reassoc]
lemma singularHomologyδ_naturality {T T' : TopTriple.{w}} (φ : T ⟶ T') (R : A) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    T.singularHomologyδ R n m h ≫ TopPair.singularHomologyMap (innerPair.map φ) R m =
      TopPair.singularHomologyMap (outerPair.map φ) R n ≫ T'.singularHomologyδ R n m h :=
  HomologicalComplex.HomologySequence.δ_naturality
    (singularChainComplexShortComplexMap φ R)
    (T.shortExact_singularChainComplexShortComplex R)
    (T'.shortExact_singularChainComplexShortComplex R) n m (by simpa)

/-- The map `H₀(X, B) ⟶ H₀(X, A)` at the end of the long exact sequence of a triple is an
epimorphism. -/
instance : Epi (TopPair.singularHomologyMap (totalToOuter.app T) R 0) :=
  have := (T.shortExact_singularChainComplexShortComplex R).epi_g
  HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)

end

end TopTriple

end TauCeti
