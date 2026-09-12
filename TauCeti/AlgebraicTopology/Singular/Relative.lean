/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.EpiMono
public import Mathlib.Topology.Category.TopPair

/-!
# Relative singular chains

This file sends a topological pair to the corresponding pair of singular simplicial sets and
defines its relative singular chain complex.  The complex is the cokernel of the inclusion of the
singular chains of the subspace into those of the ambient space.  In an abelian coefficient
category this gives the short exact sequence of chain complexes used to construct the connecting
morphisms in relative singular homology.

The construction follows the quotient-chain presentation in Eilenberg--Steenrod, *Foundations of
Algebraic Topology*, Chapters I--III, and is implemented using Mathlib's `SSetPair` relative-chain
functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

/-- An embedding of topological spaces induces a monomorphism of singular simplicial sets. -/
instance (P : TopPair.{w}) : Mono (TopCat.toSSet.map P.map) := by
  let _ : Mono P.map := (TopCat.mono_iff_injective _).mpr P.isEmbedding_map.injective
  apply Functor.map_mono

/-- The singular simplicial-set pair associated to a topological pair. -/
def toSSetPair : TopPair.{w} ⥤ SSetPair.{w} :=
  MorphismProperty.Comma.lift
    (MorphismProperty.Arrow.forget TopCat.isEmbedding ⊤ ⊤ ⋙ TopCat.toSSet.mapArrow)
    (fun P ↦ inferInstanceAs (Mono (TopCat.toSSet.map P.map)))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

@[simp]
lemma toSSetPair_obj_left (P : TopPair.{w}) :
    (toSSetPair.obj P).left = TopCat.toSSet.obj P.snd := rfl

@[simp]
lemma toSSetPair_obj_right (P : TopPair.{w}) :
    (toSSetPair.obj P).right = TopCat.toSSet.obj P.fst := rfl

@[simp]
lemma toSSetPair_obj_hom (P : TopPair.{w}) :
    (toSSetPair.obj P).hom = TopCat.toSSet.map P.map := rfl

@[simp]
lemma toSSetPair_map_left {P P' : TopPair.{w}} (f : P ⟶ P') :
    (toSSetPair.map f).left = TopCat.toSSet.map (Hom.snd f) := rfl

@[simp]
lemma toSSetPair_map_right {P P' : TopPair.{w}} (f : P ⟶ P') :
    (toSSetPair.map f).right = TopCat.toSSet.map (Hom.fst f) := rfl

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The relative singular chain complex functor on topological pairs. -/
@[no_expose]
noncomputable def singularChainComplexFunctor :
    C ⥤ TopPair.{w} ⥤ ChainComplex C ℕ :=
  SSetPair.chainComplexFunctor C ⋙
    (Functor.whiskeringLeft _ _ _).obj toSSetPair

variable {C} (P P' : TopPair.{w}) (f : P ⟶ P') (R : C)

/-- The relative singular chain complex of a topological pair. -/
noncomputable abbrev singularChainComplex : ChainComplex C ℕ :=
  (toSSetPair.obj P).chainComplex R

variable {P P'} in
/-- The chain map on relative singular chains induced by a map of topological pairs. -/
noncomputable abbrev singularChainComplexMap :
    P.singularChainComplex R ⟶ P'.singularChainComplex R :=
  SSetPair.chainComplexMap (toSSetPair.map f) R

/-- The quotient map from ambient singular chains to relative singular chains. -/
noncomputable abbrev singularChainComplexπ :
    (toSSetPair.obj P).right.chainComplex R ⟶ P.singularChainComplex R :=
  (toSSetPair.obj P).chainComplexπ R

@[simp]
lemma singularChainComplex_condition :
    SSet.chainComplexMap (TopCat.toSSet.map P.map) R ≫ P.singularChainComplexπ R = 0 := by
  rw [← toSSetPair_obj_hom]
  exact (toSSetPair.obj P).chainComplex_condition R

/-- The cokernel cofork presenting the relative singular chain complex as the quotient of the
ambient singular chains by the subspace singular chains. -/
noncomputable abbrev cokernelCoforkSingularChainComplex :
    CokernelCofork (SSet.chainComplexMap (toSSetPair.obj P).hom R) :=
  (toSSetPair.obj P).cokernelCoforkChainComplex R

/-- The relative singular chain complex is the cokernel of the map from the singular chains of
the subspace to those of the ambient space. -/
@[no_expose]
noncomputable def isColimitCokernelCoforkSingularChainComplex :
    IsColimit (P.cokernelCoforkSingularChainComplex R) :=
  (toSSetPair.obj P).isColimitCokernelCoforkChainComplex R

/-- The chain complex sequence of a topological pair: subspace chains, ambient chains, and
relative chains. -/
noncomputable abbrev singularChainComplexShortComplex : ShortComplex (ChainComplex C ℕ) :=
  (toSSetPair.obj P).chainComplexShortComplex R

section

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
  (P : TopPair.{w}) (R : A)

/-- The singular chain sequence of a topological pair is short exact. -/
lemma shortExact_singularChainComplexShortComplex :
    (P.singularChainComplexShortComplex R).ShortExact :=
  (toSSetPair.obj P).shortExact_chainComplexShortComplex R

end

section Homology

variable [CategoryWithHomology C]

/-- The relative singular homology of a topological pair in degree `n`. -/
protected noncomputable abbrev singularHomology (n : ℕ) : C :=
  (toSSetPair.obj P).homology R n

variable {P P'} in
/-- The map on relative singular homology induced by a map of topological pairs. -/
protected noncomputable abbrev singularHomologyMap (n : ℕ) :
    P.singularHomology R n ⟶ P'.singularHomology R n :=
  SSetPair.homologyMap (toSSetPair.map f) R n

/-- Relative singular homology as a functor on topological pairs. -/
@[implicit_reducible]
noncomputable def singularHomologyFunctor (n : ℕ) : TopPair.{w} ⥤ C :=
  toSSetPair ⋙ SSetPair.homologyFunctor R n

/-- The map from ambient singular homology to relative singular homology. -/
noncomputable abbrev singularHomologyπ (n : ℕ) :
    (toSSetPair.obj P).right.homology R n ⟶ P.singularHomology R n :=
  (toSSetPair.obj P).homologyπ R n

@[simp]
lemma singularHomologyMap_map_singularHomologyπ (n : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map P.map) R n ≫ P.singularHomologyπ R n = 0 := by
  rw [← toSSetPair_obj_hom]
  exact (toSSetPair.obj P).homologyMap_hom_homologyπ R n

end Homology

section LongExactSequence

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
  (P : TopPair.{w}) (R : A)

/-- The connecting morphism from relative singular homology in degree `n` to the singular homology
of the subspace in degree `m`, where `m + 1 = n`. -/
noncomputable abbrev singularHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    P.singularHomology R n ⟶ (toSSetPair.obj P).left.homology R m :=
  (toSSetPair.obj P).homologyδ R n m h

@[simp]
lemma singularHomologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    P.singularHomologyδ R n m h ≫ SSet.homologyMap (TopCat.toSSet.map P.map) R m = 0 := by
  rw [← toSSetPair_obj_hom]
  exact (toSSetPair.obj P).homologyδ_comp R n m h

@[simp]
lemma singularHomologyπ_comp_singularHomologyδ
    (n m : ℕ) (h : m + 1 = n := by lia) :
    P.singularHomologyπ R n ≫ P.singularHomologyδ R n m h = 0 :=
  (toSSetPair.obj P).comp_homologyδ R n m h

/-- Exactness at subspace homology in the long exact sequence of a topological pair. -/
lemma singularHomology_exact_subspace (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (P.singularHomologyδ_comp R n m h)).Exact :=
  (toSSetPair.obj P).homology_exact₁ R n m h

/-- Exactness at ambient homology in the long exact sequence of a topological pair. -/
lemma singularHomology_exact_space (n : ℕ) :
    (ShortComplex.mk _ _ (P.singularHomologyMap_map_singularHomologyπ R n)).Exact :=
  (toSSetPair.obj P).homology_exact₂ R n

/-- Exactness at relative homology in the long exact sequence of a topological pair. -/
lemma singularHomology_exact_relative (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (P.singularHomologyπ_comp_singularHomologyδ R n m h)).Exact :=
  (toSSetPair.obj P).homology_exact₃ R n m h

/-- The map from ambient zeroth homology to relative zeroth homology is an epimorphism. -/
instance : Epi (P.singularHomologyπ R 0) := inferInstance

end LongExactSequence

end TopPair
