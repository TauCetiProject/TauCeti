/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
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

-- The pair API uses pair projections and restricted systems; `erw` unfolds those wrappers
-- when matching them with the triple's maps and iterated restrictions.
private lemma composite_comp_twistedChainComplexπ :
    (twistedChainComplexMap T.innerMap ((outerPair.obj T).subspaceSystem L) ≫
        twistedChainComplexMap T.outerMap L) ≫
      (totalPair.obj T).twistedChainComplexπ L = 0 := by
  erw [TopPair.twistedChainComplexMap_naturality_pair (innerToTotal.app T) L,
    Category.assoc, TopPair.twistedChainComplexMap_comp_twistedChainComplexπ, comp_zero]

private def isColimitCompositeCokernel :
    IsColimit (CokernelCofork.ofπ ((totalPair.obj T).twistedChainComplexπ L)
      (T.composite_comp_twistedChainComplexπ L)) := by
  have ht := (totalPair.obj T).isColimitCokernelCoforkTwistedChainComplex L
  rw [TopPair.cokernelCoforkTwistedChainComplex_def] at ht
  have : IsIso (TopPair.twistedSubspaceChainComplexMap (innerToTotal.app T) L) := by
    rw [TopPair.twistedSubspaceChainComplexMap_def]
    have hid : IsIso (twistedChainComplexMap (𝟙 T.thd)
        ((totalPair.obj T).subspaceSystem L)) := by
      rw [twistedChainComplexMap_id]
      infer_instance
    exact IsIso.comp_isIso'
      (inferInstanceAs (IsIso (twistedChainComplexCoefficientMap
        (TopPair.subspaceSystemPullbackIso (innerToTotal.app T) L).hom))) hid
  exact isCokernelOfComp
    (inv (TopPair.twistedSubspaceChainComplexMap (innerToTotal.app T) L))
    (twistedChainComplexMap T.totalMap L) ht
    (T.composite_comp_twistedChainComplexπ L) (by
      -- By `innerToTotal_app_fst`, `erw` reduces the ambient pair component to
      -- `T.outerMap` inside the pullback types, and the source pair map to `T.innerMap`.
      erw [TopPair.twistedChainComplexMap_naturality_pair (innerToTotal.app T) L,
        IsIso.inv_hom_id_assoc])

/-- The quotient map `C(X,B;L) ⟶ C(X,A;L)` induced by the identity on ambient chains. -/
def twistedChainComplexTotalToOuter :
    (totalPair.obj T).twistedChainComplex L ⟶ (outerPair.obj T).twistedChainComplex L :=
  (totalPair.obj T).twistedChainComplexCoefficientMap ((pullbackIdIso T.fst).inv.app L) ≫
    TopPair.twistedChainComplexMap (totalToOuter.app T) L

/-- The quotient from `(X,B)` to `(X,A)` is induced by the identity of `C(X;L)`. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_comp_totalToOuter :
    dsimp% ((totalPair.obj T).twistedChainComplexπ L ≫ T.twistedChainComplexTotalToOuter L =
      (outerPair.obj T).twistedChainComplexπ L) := by
  dsimp only [twistedChainComplexTotalToOuter]
  -- By `totalToOuter_app_fst`, `erw` reduces the ambient pair component to the
  -- identity on `T.fst` inside the dependent coefficient pullback.
  erw [TopPair.twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    TopPair.twistedChainComplexπ_comp_twistedChainComplexMap]
  erw [twistedChainComplexMap_id, ← twistedChainComplexCoefficientMap_comp_assoc]
  simp only [Iso.inv_hom_id_app, Functor.id_obj,
    LocalCoefficientSystem.twistedChainComplexCoefficientMap_id,
    Category.id_comp]

@[reassoc (attr := simp)]
lemma twistedChainComplexMap_innerToTotal_comp_totalToOuter :
    TopPair.twistedChainComplexMap (innerToTotal.app T) L ≫
      T.twistedChainComplexTotalToOuter L = 0 := by
  apply (cancel_epi ((innerPair.obj T).twistedChainComplexπ
    ((outerPair.obj T).subspaceSystem L))).1
  -- By `innerToTotal_app_fst`, `erw` identifies the pair map's coefficient pullback
  -- with restriction along `T.outerMap` in the quotient's source.
  erw [← Category.assoc, TopPair.twistedChainComplexπ_comp_twistedChainComplexMap, Category.assoc,
    T.twistedChainComplexπ_comp_totalToOuter L, comp_zero]
  exact (outerPair.obj T).twistedChainComplexMap_comp_twistedChainComplexπ L

/-- The relative twisted chain sequence of a triple. -/
abbrev twistedChainComplexShortComplex :
    ShortComplex (ChainComplex (ModuleCat.{max v w} R) ℕ) :=
  ShortComplex.mk _ _ (T.twistedChainComplexMap_innerToTotal_comp_totalToOuter L)

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
    (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (innerToTotal.app T) L)
    (T.twistedChainComplexπ_comp_totalToOuter L)

section Coefficients

variable {L} {K : LocalCoefficientSystem.{u, v, max v w} R T.fst} (η : L ⟶ K)

/-- The quotient between relative twisted chains commutes with coefficient morphisms. -/
@[reassoc]
lemma twistedChainComplexTotalToOuter_naturality :
    T.twistedChainComplexTotalToOuter L ≫ (outerPair.obj T).twistedChainComplexCoefficientMap η =
      (totalPair.obj T).twistedChainComplexCoefficientMap η ≫
        T.twistedChainComplexTotalToOuter K := by
  dsimp only [twistedChainComplexTotalToOuter]
  -- By `totalToOuter_app_fst`, `erw` identifies the pair naturality equation's
  -- coefficient pullback with the identity used by `pullbackIdIso`.
  erw [Category.assoc, TopPair.twistedChainComplexMap_naturality,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc,
    ← TopPair.twistedChainComplexCoefficientMap_comp_assoc]
  congr 1
  exact congrArg (fun φ ↦ (totalPair.obj T).twistedChainComplexCoefficientMap φ)
    ((pullbackIdIso T.fst).inv.naturality η).symm

/-- A coefficient morphism induces a morphism of the short exact triple sequences. -/
def twistedChainComplexShortComplexCoefficientMap :
    T.twistedChainComplexShortComplex L ⟶ T.twistedChainComplexShortComplex K :=
  ShortComplex.homMk
    ((innerPair.obj T).twistedChainComplexCoefficientMap
      ((LocalCoefficientSystem.pullback T.outerMap.hom).map η))
    ((totalPair.obj T).twistedChainComplexCoefficientMap η)
    ((outerPair.obj T).twistedChainComplexCoefficientMap η)
    (TopPair.twistedChainComplexMap_naturality (innerToTotal.app T) L η).symm
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

/-- The quotient map `Hₖ(X,B;L) ⟶ Hₖ(X,A;L)`. -/
abbrev twistedHomologyTotalToOuter (k : ℕ) :=
  HomologicalComplex.homologyMap (T.twistedChainComplexTotalToOuter L) k

/-- The quotient on relative twisted homology commutes with change of coefficients.
For the inner inclusion, use `TopPair.twistedHomologyMap_naturality`. -/
@[reassoc]
lemma twistedHomologyTotalToOuter_naturality_coefficient
    {K : LocalCoefficientSystem.{u, v, max v w} R T.fst} (η : L ⟶ K) (k : ℕ) :
    T.twistedHomologyTotalToOuter L k ≫
        (outerPair.obj T).twistedHomologyCoefficientMap η k =
      (totalPair.obj T).twistedHomologyCoefficientMap η k ≫
        T.twistedHomologyTotalToOuter K k :=
  ((HomologicalComplex.homologyMap_comp _ _ _).symm).trans
    ((congrArg (fun φ ↦ HomologicalComplex.homologyMap φ k)
      (T.twistedChainComplexTotalToOuter_naturality η)).trans
      (HomologicalComplex.homologyMap_comp _ _ _))

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
lemma twistedHomologyMap_innerToTotal_comp_totalToOuter (k : ℕ) :
    TopPair.twistedHomologyMap (innerToTotal.app T) L k ≫
      T.twistedHomologyTotalToOuter L k = 0 := by
  rw [← HomologicalComplex.homologyMap_comp,
    T.twistedChainComplexMap_innerToTotal_comp_totalToOuter L, HomologicalComplex.homologyMap_zero]

@[simp]
lemma twistedHomologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    T.twistedHomologyδ L n m h ≫ TopPair.twistedHomologyMap (innerToTotal.app T) L m = 0 :=
  (T.shortExact_twistedChainComplexShortComplex L).δ_comp n m (by simpa)

-- The pair map's coefficient pullback needs semireducible unfolding, so `reassoc` does not
-- normalize this composite. State the right-associated form explicitly for `simp`.
@[simp]
lemma twistedHomologyδ_comp_assoc (n m : ℕ) (h : m + 1 = n)
    {M : ModuleCat.{max v w} R} (f : (totalPair.obj T).twistedHomology L m ⟶ M) :
    T.twistedHomologyδ L n m h ≫
      TopPair.twistedHomologyMap (innerToTotal.app T) L m ≫ f = 0 := by
  erw [← Category.assoc, T.twistedHomologyδ_comp L n m h, zero_comp]

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
    (ShortComplex.mk _ _ (T.twistedHomologyMap_innerToTotal_comp_totalToOuter L n)).Exact :=
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
    (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap (innerToTotal.app T) L)
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
  simp only [outerPairToTwistedShortComplexMap_τ₁, outerPairToTwistedShortComplexMap_τ₃,
    HomologicalComplex.homologyMap_id, Category.id_comp] at key
  exact key.symm

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
