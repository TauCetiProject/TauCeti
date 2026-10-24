/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Relative
public import TauCeti.CategoryTheory.Abelian.DiagramLemmas.CokernelComp
public import TauCeti.Topology.Category.TopTriple
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The triple sequence with local coefficients

For a triple `B ⊆ A ⊆ X` and a module-valued local system `L` on `X`, the native
relative twisted chain complexes form a short exact sequence
`0 ⟶ C(A,B;L|A) ⟶ C(X,B;L) ⟶ C(X,A;L) ⟶ 0`.
Its homology sequence is the long exact sequence of the triple, natural under
morphisms of the coefficient system. The connecting map factors through the connecting
map of `(X,A)` and the quotient to `(A,B)`, as needed
for successive connecting maps in a filtered space.

The construction follows `TauCeti.TopTriple.shortExact_singularChainComplexShortComplex`
and the cokernel presentations in `TopPair.twistedChainComplex`. Pullback along a
composite inclusion is compared explicitly with iterated pullback; no triviality
or freeness of the coefficient system is required.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits
open TauCeti.LocalCoefficientSystem

universe u v w

namespace TauCeti.TopTriple

variable {R : Type u} [Ring R] (T : TopTriple.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R T.fst)

-- This comparison is only used to identify the middle quotient in the triple sequence.
private def compositeSystemIso :
    (totalPair.obj T).subspaceSystem L ≅
      (innerPair.obj T).subspaceSystem ((outerPair.obj T).subspaceSystem L) :=
  eqToIso (congrArg (fun k : T.thd ⟶ T.fst ↦ (LocalCoefficientSystem.pullback k.hom).obj L)
      T.innerMap_comp_outerMap.symm) ≪≫
    (pullbackCompIso T.innerMap.hom T.outerMap.hom).app L

private lemma twistedChainComplexMap_total :
    twistedChainComplexMap T.totalMap L =
      (twistedChainComplexCoefficientIso (T.compositeSystemIso L)).hom ≫
        twistedChainComplexMap T.innerMap ((outerPair.obj T).subspaceSystem L) ≫
          twistedChainComplexMap T.outerMap L := by
  rw [twistedChainComplexMap_congr T.totalMap L T.innerMap_comp_outerMap.symm,
    twistedChainComplexMap_comp]
  simp only [compositeSystemIso, twistedChainComplexCoefficientIso_hom, Iso.trans_hom,
    twistedChainComplexCoefficientMap_comp, Iso.app_hom, Category.assoc]

private lemma composite_comp_twistedChainComplexπ :
    (twistedChainComplexMap T.innerMap ((outerPair.obj T).subspaceSystem L) ≫
        twistedChainComplexMap T.outerMap L) ≫
      (totalPair.obj T).twistedChainComplexπ L = 0 := by
  rw [← cancel_epi (twistedChainComplexCoefficientIso (T.compositeSystemIso L)).hom,
    ← Category.assoc, ← T.twistedChainComplexMap_total L, comp_zero]
  exact (totalPair.obj T).twistedChainComplexMap_comp_twistedChainComplexπ L

/-- The map `C(A,B;L|A) ⟶ C(X,B;L)` induced by inclusion of pairs. -/
def twistedChainComplexInnerToTotal :
    (innerPair.obj T).twistedChainComplex ((outerPair.obj T).subspaceSystem L) ⟶
      (totalPair.obj T).twistedChainComplex L :=
  (innerPair.obj T).twistedChainComplexDesc _
    (twistedChainComplexMap T.outerMap L ≫ (totalPair.obj T).twistedChainComplexπ L)
    (by simpa only [Category.assoc] using T.composite_comp_twistedChainComplexπ L)

-- Normalize the pair functor projections so the quotient rules also match in importing modules.
/-- The quotient map to `(X,B)` commutes with the inclusion of `(A,B)`. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_innerToTotal :
    dsimp% ((innerPair.obj T).twistedChainComplexπ ((outerPair.obj T).subspaceSystem L) ≫
        T.twistedChainComplexInnerToTotal L =
      twistedChainComplexMap T.outerMap L ≫ (totalPair.obj T).twistedChainComplexπ L) :=
  (innerPair.obj T).twistedChainComplexπ_comp_twistedChainComplexDesc _ _ _

private def isColimitCompositeCokernel :
    IsColimit (CokernelCofork.ofπ ((totalPair.obj T).twistedChainComplexπ L)
      (T.composite_comp_twistedChainComplexπ L)) := by
  have ht := (totalPair.obj T).isColimitCokernelCoforkTwistedChainComplex L
  rw [TopPair.cokernelCoforkTwistedChainComplex_def] at ht
  exact isCokernelOfComp
    (twistedChainComplexCoefficientIso (T.compositeSystemIso L)).hom
    (twistedChainComplexMap T.totalMap L) ht
    (T.composite_comp_twistedChainComplexπ L)
    (by simpa only [Category.assoc] using (T.twistedChainComplexMap_total L).symm)

/-- The quotient map `C(X,B;L) ⟶ C(X,A;L)` induced by the identity on ambient chains. -/
def twistedChainComplexTotalToOuter :
    (totalPair.obj T).twistedChainComplex L ⟶ (outerPair.obj T).twistedChainComplex L :=
  (totalPair.obj T).twistedChainComplexDesc L
    ((outerPair.obj T).twistedChainComplexπ L) (by
      rw [T.twistedChainComplexMap_total L]
      have h := (outerPair.obj T).twistedChainComplexMap_comp_twistedChainComplexπ L
      simp only [Category.assoc, h, comp_zero])

/-- The quotient from `(X,B)` to `(X,A)` is induced by the identity of `C(X;L)`. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_totalToOuter :
    dsimp% ((totalPair.obj T).twistedChainComplexπ L ≫ T.twistedChainComplexTotalToOuter L =
      (outerPair.obj T).twistedChainComplexπ L) :=
  (totalPair.obj T).twistedChainComplexπ_comp_twistedChainComplexDesc _ _ _

lemma twistedChainComplexInnerToTotal_comp_totalToOuter :
    T.twistedChainComplexInnerToTotal L ≫ T.twistedChainComplexTotalToOuter L = 0 := by
  apply (cancel_epi ((innerPair.obj T).twistedChainComplexπ
    ((outerPair.obj T).subspaceSystem L))).1
  rw [← Category.assoc, T.twistedChainComplexπ_comp_innerToTotal L, Category.assoc,
    T.twistedChainComplexπ_comp_totalToOuter L, comp_zero]
  simpa only [outerPair_obj_map] using
    (outerPair.obj T).twistedChainComplexMap_comp_twistedChainComplexπ L

/-- The relative twisted chain sequence of a triple. -/
abbrev twistedChainComplexShortComplex :
    ShortComplex (ChainComplex (ModuleCat.{max v w} R) ℕ) :=
  ShortComplex.mk _ _ (T.twistedChainComplexInnerToTotal_comp_totalToOuter L)

/-- The relative twisted chain sequence of a triple is short exact. -/
lemma shortExact_twistedChainComplexShortComplex :
    (T.twistedChainComplexShortComplex L).ShortExact := by
  have hi := (innerPair.obj T).isColimitCokernelCoforkTwistedChainComplex
    ((outerPair.obj T).subspaceSystem L)
  have ho := (outerPair.obj T).isColimitCokernelCoforkTwistedChainComplex L
  rw [TopPair.cokernelCoforkTwistedChainComplex_def] at hi ho
  exact shortExact_of_isColimit_cokernelCofork rfl
    (by
      have : Mono T.outerMap := (TopCat.mono_iff_injective _).2 T.isEmbedding_outerMap.injective
      infer_instance)
    hi (T.isColimitCompositeCokernel L) ho
    (T.twistedChainComplexπ_comp_innerToTotal L)
    (T.twistedChainComplexπ_comp_totalToOuter L)

section Coefficients

variable {L} {K : LocalCoefficientSystem.{u, v, max v w} R T.fst} (η : L ⟶ K)

/-- Inclusion of relative twisted chains commutes with change of the ambient local system. -/
@[reassoc]
lemma twistedChainComplexInnerToTotal_naturality :
    T.twistedChainComplexInnerToTotal L ≫ (totalPair.obj T).twistedChainComplexCoefficientMap η =
      (innerPair.obj T).twistedChainComplexCoefficientMap
          ((LocalCoefficientSystem.pullback T.outerMap.hom).map η) ≫
        T.twistedChainComplexInnerToTotal K := by
  apply (cancel_epi ((innerPair.obj T).twistedChainComplexπ
    ((outerPair.obj T).subspaceSystem L))).1
  simp only [T.twistedChainComplexπ_comp_innerToTotal_assoc L,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    T.twistedChainComplexπ_comp_innerToTotal K]
  exact twistedChainComplexMap_naturality_assoc T.outerMap η _

/-- The quotient between relative twisted chains commutes with coefficient morphisms. -/
@[reassoc]
lemma twistedChainComplexTotalToOuter_naturality :
    T.twistedChainComplexTotalToOuter L ≫ (outerPair.obj T).twistedChainComplexCoefficientMap η =
      (totalPair.obj T).twistedChainComplexCoefficientMap η ≫
        T.twistedChainComplexTotalToOuter K := by
  apply (cancel_epi ((totalPair.obj T).twistedChainComplexπ L)).1
  simp only [T.twistedChainComplexπ_comp_totalToOuter_assoc L,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    T.twistedChainComplexπ_comp_totalToOuter K]

/-- A coefficient morphism induces a morphism of the short exact triple sequences. -/
def twistedChainComplexShortComplexCoefficientMap :
    T.twistedChainComplexShortComplex L ⟶ T.twistedChainComplexShortComplex K :=
  ShortComplex.homMk
    ((innerPair.obj T).twistedChainComplexCoefficientMap
      ((LocalCoefficientSystem.pullback T.outerMap.hom).map η))
    ((totalPair.obj T).twistedChainComplexCoefficientMap η)
    ((outerPair.obj T).twistedChainComplexCoefficientMap η)
    (T.twistedChainComplexInnerToTotal_naturality η).symm
    (T.twistedChainComplexTotalToOuter_naturality η).symm

@[simp]
lemma twistedChainComplexShortComplexCoefficientMap_τ₁ :
    (T.twistedChainComplexShortComplexCoefficientMap η).τ₁ =
      (innerPair.obj T).twistedChainComplexCoefficientMap
        ((LocalCoefficientSystem.pullback T.outerMap.hom).map η) := (rfl)

@[simp]
lemma twistedChainComplexShortComplexCoefficientMap_τ₂ :
    (T.twistedChainComplexShortComplexCoefficientMap η).τ₂ =
      (totalPair.obj T).twistedChainComplexCoefficientMap η := (rfl)

@[simp]
lemma twistedChainComplexShortComplexCoefficientMap_τ₃ :
    (T.twistedChainComplexShortComplexCoefficientMap η).τ₃ =
      (outerPair.obj T).twistedChainComplexCoefficientMap η := (rfl)

end Coefficients

instance : Epi (T.twistedChainComplexTotalToOuter L) :=
  (T.shortExact_twistedChainComplexShortComplex L).epi_g

/-- The map `Hₖ(A,B;L|A) ⟶ Hₖ(X,B;L)` induced by inclusion of pairs. -/
abbrev twistedHomologyInnerToTotal (k : ℕ) :=
  HomologicalComplex.homologyMap (T.twistedChainComplexInnerToTotal L) k

/-- The quotient map `Hₖ(X,B;L) ⟶ Hₖ(X,A;L)`. -/
abbrev twistedHomologyTotalToOuter (k : ℕ) :=
  HomologicalComplex.homologyMap (T.twistedChainComplexTotalToOuter L) k

/-- The triple sequence ends with a surjection on degree-zero relative homology. -/
instance : Epi (T.twistedHomologyTotalToOuter L 0) :=
  HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)

/-- The connecting map `Hₙ(X,A;L) ⟶ Hₘ(A,B;L|A)` of the triple, for `m+1=n`. -/
def twistedHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (outerPair.obj T).twistedHomology L n ⟶
      (innerPair.obj T).twistedHomology ((outerPair.obj T).subspaceSystem L) m :=
  (T.shortExact_twistedChainComplexShortComplex L).δ n m (by simpa)

/-- The triple connecting map is the connecting map of its short exact chain sequence. -/
lemma twistedHomologyδ_def (n m : ℕ) (h : m + 1 = n := by lia) :
    T.twistedHomologyδ L n m h =
      (T.shortExact_twistedChainComplexShortComplex L).δ n m (by simpa) := (rfl)

@[reassoc (attr := simp)]
lemma twistedHomologyInnerToTotal_comp_totalToOuter (k : ℕ) :
    T.twistedHomologyInnerToTotal L k ≫ T.twistedHomologyTotalToOuter L k = 0 := by
  rw [← HomologicalComplex.homologyMap_comp,
    T.twistedChainComplexInnerToTotal_comp_totalToOuter L, HomologicalComplex.homologyMap_zero]

@[reassoc (attr := simp)]
lemma twistedHomologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    T.twistedHomologyδ L n m h ≫ T.twistedHomologyInnerToTotal L m = 0 :=
  (T.shortExact_twistedChainComplexShortComplex L).δ_comp n m (by simpa)

@[reassoc (attr := simp)]
lemma comp_twistedHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    T.twistedHomologyTotalToOuter L n ≫ T.twistedHomologyδ L n m h = 0 :=
  (T.shortExact_twistedChainComplexShortComplex L).comp_δ n m (by simpa)

/-- Exactness at `Hₘ(A,B;L|A)` in the triple sequence. -/
lemma twistedHomology_exact_inner (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (T.twistedHomologyδ_comp L n m h)).Exact :=
  (T.shortExact_twistedChainComplexShortComplex L).homology_exact₁ n m (by simpa)

/-- Exactness at `Hₙ(X,B;L)` in the triple sequence. -/
lemma twistedHomology_exact_total (n : ℕ) :
    (ShortComplex.mk _ _ (T.twistedHomologyInnerToTotal_comp_totalToOuter L n)).Exact :=
  (T.shortExact_twistedChainComplexShortComplex L).homology_exact₂ n

/-- Exactness at `Hₙ(X,A;L)` in the triple sequence. -/
lemma twistedHomology_exact_outer (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (T.comp_twistedHomologyδ L n m h)).Exact :=
  (T.shortExact_twistedChainComplexShortComplex L).homology_exact₃ n m (by simpa)

/-- The morphism from the pair sequence to the triple sequence given by quotienting by `B`. -/
@[simps! τ₁ τ₂ τ₃]
private def outerPairToTwistedShortComplexMap :
    (outerPair.obj T).twistedChainComplexShortComplex L ⟶ T.twistedChainComplexShortComplex L :=
  ShortComplex.homMk
    ((innerPair.obj T).twistedChainComplexπ ((outerPair.obj T).subspaceSystem L))
    ((totalPair.obj T).twistedChainComplexπ L) (𝟙 _)
    (T.twistedChainComplexπ_comp_innerToTotal L)
    (by simpa only [Category.comp_id] using T.twistedChainComplexπ_comp_totalToOuter L)

/-- The triple boundary is the pair boundary followed by the quotient to `(A,B)`. -/
@[reassoc]
lemma twistedHomologyδ_eq_comp_twistedHomologyπ (n m : ℕ) (h : m + 1 = n := by lia) :
    T.twistedHomologyδ L n m h =
      (outerPair.obj T).twistedHomologyδ L n m h ≫
        (innerPair.obj T).twistedHomologyπ ((outerPair.obj T).subspaceSystem L) m := by
  have key := HomologicalComplex.HomologySequence.δ_naturality
    (T.outerPairToTwistedShortComplexMap L)
    ((outerPair.obj T).shortExact_twistedChainComplexShortComplex L)
    (T.shortExact_twistedChainComplexShortComplex L) n m (by simpa)
  simpa only [outerPairToTwistedShortComplexMap_τ₁, outerPairToTwistedShortComplexMap_τ₃,
    HomologicalComplex.homologyMap_id, Category.id_comp, twistedHomologyδ_def] using key.symm

/-- The triple connecting map is natural under morphisms of local coefficient systems. -/
@[reassoc]
lemma twistedHomologyδ_naturality_coefficient
    {K : LocalCoefficientSystem.{u, v, max v w} R T.fst} (η : L ⟶ K)
    (n m : ℕ) (h : m + 1 = n := by lia) :
    T.twistedHomologyδ L n m h ≫
        (innerPair.obj T).twistedHomologyCoefficientMap
          ((LocalCoefficientSystem.pullback T.outerMap.hom).map η) m =
      (outerPair.obj T).twistedHomologyCoefficientMap η n ≫ T.twistedHomologyδ K n m h := by
  exact HomologicalComplex.HomologySequence.δ_naturality
    (T.twistedChainComplexShortComplexCoefficientMap η)
    (T.shortExact_twistedChainComplexShortComplex L)
    (T.shortExact_twistedChainComplexShortComplex K) n m (by simpa)

/-- The triple boundary is an isomorphism when the two adjacent total relative groups vanish. -/
theorem isIso_twistedHomologyδ_of_isZero (n m : ℕ)
    (hn : IsZero ((totalPair.obj T).twistedHomology L n))
    (hm : IsZero ((totalPair.obj T).twistedHomology L m)) (h : m + 1 = n := by lia) :
    IsIso (T.twistedHomologyδ L n m h) :=
  (T.shortExact_twistedChainComplexShortComplex L).isIso_δ n m (by simpa) hn hm

end TauCeti.TopTriple
