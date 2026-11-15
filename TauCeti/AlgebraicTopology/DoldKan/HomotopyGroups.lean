/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.MooreComplex
public import TauCeti.Algebra.Homology.Embedding.TruncLE

/-!
# Homotopy groups under Dold–Kan

The underlying Kan complex of the Dold–Kan simplicial module associated to a chain complex
has the homology of that complex as its homotopy groups. The comparisons are natural in
chain maps, including the bijection between path components and degree-zero homology.
For a cochain complex `K`, good truncation gives the corresponding formula
`πₙ(Γ(τ≥0 K), 0) ≃ H⁻ⁿ(K)`. Degree zero uses cycles rather than all of `K.X 0`.
For commutative rings this is the mapping object of `TauCeti.cochainToSSet` and the
simplicial enrichment of a differential graded category.

The construction combines the simplicial-module Moore comparison with the counit of
Joël Riou's abelian Dold–Kan equivalence in Mathlib. This identifies homotopy groups with
the original complex, rather than the normalized Moore complex of its denormalization.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter III, §2.
* J. Lurie, *Higher Algebra*, Remark 1.3.1.12.
-/

public noncomputable section

open CategoryTheory SimplicialObject HomologicalComplex
open scoped Simplicial

universe u

namespace ChainComplex

variable {R : Type*} [Ring R] (K : ChainComplex (ModuleCat.{u} R) ℕ)

/-- Positive homotopy groups of the Dold–Kan simplicial module are the homology groups
of the original complex. The base point is the zero vertex. -/
def doldKanPiAddEquivHomology (n : ℕ) :
    Additive (SSet.KanComplex.π (n + 1)
      (Idempotents.DoldKan.Γ.obj K ⋙ forget (ModuleCat R))
      (0 : (Idempotents.DoldKan.Γ.obj K) _⦋0⦌)) ≃+ K.homology (n + 1) :=
  (piAddEquivNormalizedMooreComplexHomology (Idempotents.DoldKan.Γ.obj K) n).trans
    ((homologyFunctor _ _ (n + 1)).mapIso
      (Abelian.DoldKan.equivalence.counitIso.app K)).toLinearEquiv.toAddEquiv

/-- Path components of the Dold–Kan simplicial module are degree-zero homology. -/
def doldKanPiZeroEquivHomology :
    SSet.KanComplex.π 0 (Idempotents.DoldKan.Γ.obj K ⋙ forget (ModuleCat R))
      (0 : (Idempotents.DoldKan.Γ.obj K) _⦋0⦌) ≃ K.homology 0 :=
  (piZeroEquivNormalizedMooreComplexHomology (Idempotents.DoldKan.Γ.obj K)).trans
    ((homologyFunctor _ _ 0).mapIso
      (Abelian.DoldKan.equivalence.counitIso.app K)).toLinearEquiv.toEquiv

variable {K} {L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The positive-degree Dold–Kan comparison is natural in chain maps. -/
lemma doldKanPiAddEquivHomology_map (f : K ⟶ L) (n : ℕ)
    (a : SSet.KanComplex.π (n + 1)
      (Idempotents.DoldKan.Γ.obj K ⋙ forget (ModuleCat R))
      (0 : (Idempotents.DoldKan.Γ.obj K) _⦋0⦌)) :
    L.doldKanPiAddEquivHomology n
        (.ofMul (SSet.KanComplex.π.map
          (Functor.whiskerRight (Idempotents.DoldKan.Γ.map f) (forget (ModuleCat R)))
          (map_zero ((Idempotents.DoldKan.Γ.map f).app _).hom) a)) =
      homologyMap f (n + 1) (K.doldKanPiAddEquivHomology n (.ofMul a)) := by
  unfold doldKanPiAddEquivHomology
  erw [AddEquiv.trans_apply, AddEquiv.trans_apply,
    piAddEquivNormalizedMooreComplexHomology_map]
  erw [LinearEquiv.coe_toAddEquiv, Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
  have h := congrArg (fun g ↦ homologyMap g (n + 1))
    (Abelian.DoldKan.equivalence.counitIso.hom.naturality f)
  rw [homologyMap_comp, homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h
    (piAddEquivNormalizedMooreComplexHomology _ n (.ofMul a))

/-- The degree-zero Dold–Kan comparison is natural in chain maps. -/
lemma doldKanPiZeroEquivHomology_map (f : K ⟶ L)
    (a : SSet.KanComplex.π 0
      (Idempotents.DoldKan.Γ.obj K ⋙ forget (ModuleCat R))
      (0 : (Idempotents.DoldKan.Γ.obj K) _⦋0⦌)) :
    L.doldKanPiZeroEquivHomology
        (SSet.KanComplex.π.map
          (Functor.whiskerRight (Idempotents.DoldKan.Γ.map f) (forget (ModuleCat R)))
          (map_zero ((Idempotents.DoldKan.Γ.map f).app _).hom) a) =
      homologyMap f 0 (K.doldKanPiZeroEquivHomology a) := by
  unfold doldKanPiZeroEquivHomology
  erw [Equiv.trans_apply, Equiv.trans_apply,
    piZeroEquivNormalizedMooreComplexHomology_map]
  erw [LinearEquiv.coe_toEquiv, Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
  have h := congrArg (fun g ↦ homologyMap g 0)
    (Abelian.DoldKan.equivalence.counitIso.hom.naturality f)
  rw [homologyMap_comp, homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h
    (piZeroEquivNormalizedMooreComplexHomology _ a)

/-- The zero vertex represents the zero homology class. -/
@[simp]
lemma doldKanPiZeroEquivHomology_one (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    K.doldKanPiZeroEquivHomology 1 = 0 := by
  have h := doldKanPiZeroEquivHomology_map (0 : K ⟶ K) 1
  erw [SSet.KanComplex.π.map_one] at h
  simpa using h

end ChainComplex

namespace CochainComplex

variable {R : Type*} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Positive homotopy groups of the Dold–Kan good truncation of a cochain complex are
its negative cohomology groups. Chain degree `n + 1` corresponds to cochain degree `-(n + 1)`. -/
def doldKanPiAddEquivHomology (n : ℕ) :
    Additive (SSet.KanComplex.π (n + 1)
      (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat) ⋙
        forget (ModuleCat R))
      (0 : (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat)) _⦋0⦌)) ≃+
      K.homology (-((n + 1 : ℕ) : ℤ)) :=
  (ChainComplex.doldKanPiAddEquivHomology (K.truncLE' ComplexShape.embeddingDownNat) n).trans
    (K.truncLE'HomologyIso ComplexShape.embeddingDownNat (n + 1)).toLinearEquiv.toAddEquiv

/-- Path components of the Dold–Kan good truncation of a cochain complex are its
zeroth cohomology group. -/
def doldKanPiZeroEquivHomology :
    SSet.KanComplex.π 0
      (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat) ⋙
        forget (ModuleCat R))
      (0 : (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat)) _⦋0⦌) ≃
      K.homology 0 :=
  (ChainComplex.doldKanPiZeroEquivHomology (K.truncLE' ComplexShape.embeddingDownNat)).trans
    (K.truncLE'HomologyIso ComplexShape.embeddingDownNat 0).toLinearEquiv.toEquiv

variable {K} {L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The positive-degree cochain comparison is natural in cochain maps. -/
lemma doldKanPiAddEquivHomology_map (f : K ⟶ L) (n : ℕ)
    (a : SSet.KanComplex.π (n + 1)
      (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat) ⋙
        forget (ModuleCat R))
      (0 : (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat)) _⦋0⦌)) :
    L.doldKanPiAddEquivHomology n
        (.ofMul (SSet.KanComplex.π.map
          (Functor.whiskerRight
            (Idempotents.DoldKan.Γ.map (truncLE'Map f ComplexShape.embeddingDownNat))
            (forget (ModuleCat R)))
          (map_zero ((Idempotents.DoldKan.Γ.map
            (truncLE'Map f ComplexShape.embeddingDownNat)).app _).hom) a)) =
      homologyMap f (-((n + 1 : ℕ) : ℤ)) (K.doldKanPiAddEquivHomology n (.ofMul a)) := by
  unfold doldKanPiAddEquivHomology
  erw [AddEquiv.trans_apply, AddEquiv.trans_apply,
    ChainComplex.doldKanPiAddEquivHomology_map,
    LinearEquiv.coe_toAddEquiv, Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
  exact ConcreteCategory.congr_hom (truncLE'HomologyIso_hom_naturality f (n + 1))
    (ChainComplex.doldKanPiAddEquivHomology (K.truncLE' ComplexShape.embeddingDownNat) n (.ofMul a))

/-- The degree-zero cochain comparison is natural in cochain maps. -/
lemma doldKanPiZeroEquivHomology_map (f : K ⟶ L)
    (a : SSet.KanComplex.π 0
      (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat) ⋙
        forget (ModuleCat R))
      (0 : (Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat)) _⦋0⦌)) :
    L.doldKanPiZeroEquivHomology
        (SSet.KanComplex.π.map
          (Functor.whiskerRight
            (Idempotents.DoldKan.Γ.map (truncLE'Map f ComplexShape.embeddingDownNat))
            (forget (ModuleCat R)))
          (map_zero ((Idempotents.DoldKan.Γ.map
            (truncLE'Map f ComplexShape.embeddingDownNat)).app _).hom) a) =
      homologyMap f 0 (K.doldKanPiZeroEquivHomology a) := by
  unfold doldKanPiZeroEquivHomology
  erw [Equiv.trans_apply, Equiv.trans_apply, ChainComplex.doldKanPiZeroEquivHomology_map,
    LinearEquiv.coe_toEquiv, Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply]
  exact ConcreteCategory.congr_hom (truncLE'HomologyIso_hom_naturality f 0)
    (ChainComplex.doldKanPiZeroEquivHomology (K.truncLE' ComplexShape.embeddingDownNat) a)

/-- The zero vertex of the good truncation represents the zero cohomology class. -/
@[simp]
lemma doldKanPiZeroEquivHomology_one (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K.doldKanPiZeroEquivHomology 1 = 0 := by
  have h := doldKanPiZeroEquivHomology_map (0 : K ⟶ K) 1
  erw [SSet.KanComplex.π.map_one] at h
  simpa using h

end CochainComplex
