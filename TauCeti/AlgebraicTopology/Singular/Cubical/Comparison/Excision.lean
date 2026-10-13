/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative

/-!
# The long exact sequence and excision for cubical singular chains

The short exact sequence `0 ⟶ N(A) ⟶ N(X) ⟶ N(X, A) ⟶ 0` of normalized cubical chains of a
topological pair gives the **long exact sequence of the pair** in cubical homology, with
connecting morphism `TopPair.cubicalHomologyδ`.  The comparison maps form a morphism of short
exact sequences from the simplicial one, so this connecting morphism corresponds to the singular
one under the comparison isomorphisms (`TopPair.singularCubicalHomologyIso_hom_cubicalHomologyδ`).

**Excision** is transported from relative singular homology: a map of pairs inducing isomorphisms
on relative singular homology induces isomorphisms on relative cubical homology
(`TopPair.isIso_homologyMap_cubicalChainComplexMap_of_isIso`), which applies to the excision maps
of `TauCeti.AlgebraicTopology.Singular.Excision`.

## Main definitions

* `TopPair.cubicalHomologyδ`: the connecting morphism `Hₙ(X, A) ⟶ Hₘ(A)` of cubical homology.

## Main results

* `TopPair.cubicalHomology_exact_subspace`, `TopPair.cubicalHomology_exact_space`,
  `TopPair.cubicalHomology_exact_relative`: exactness of the long exact sequence.
* `TopPair.singularCubicalHomologyIso_hom_cubicalHomologyδ`: compatibility of the connecting
  morphisms with the comparison.
* `TopPair.isIso_homologyMap_cubicalChainComplexMap_excisionMap`,
  `TopPair.isIso_homologyMap_cubicalChainComplexMap_excisionMap_compl`: excision.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Princeton, 1952,
  Chapters I–III and VII.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti Topology

universe u

namespace TopPair

variable (k : Type u) [Ring k] (P : TopPair.{u})

/-! ### The long exact sequence of a pair -/

/-- The **connecting morphism** `Hₙ(X, A) ⟶ Hₘ(A)` of the long exact sequence of a pair in cubical
homology, for `m + 1 = n`. -/
def cubicalHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (P.cubicalChainComplex k).homology n ⟶
      ((normalizedCubicalChainComplex k).obj P.snd).homology m :=
  (shortExact_cubicalChainComplexShortComplex k P).δ n m h

theorem cubicalHomologyδ_def (n m : ℕ) (h : m + 1 = n := by lia) :
    P.cubicalHomologyδ k n m h = (shortExact_cubicalChainComplexShortComplex k P).δ n m h :=
  (rfl)

/-- The connecting morphism followed by the map induced by the inclusion of the subspace is
zero. -/
@[reassoc (attr := simp)]
theorem cubicalHomologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    P.cubicalHomologyδ k n m h ≫
      HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map P.map) m = 0 :=
  (shortExact_cubicalChainComplexShortComplex k P).δ_comp n m h

/-- The map to relative homology followed by the connecting morphism is zero. -/
@[reassoc (attr := simp)]
theorem comp_cubicalHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n ≫
      P.cubicalHomologyδ k n m h = 0 :=
  (shortExact_cubicalChainComplexShortComplex k P).comp_δ n m h

/-- Exactness at the cubical homology of the subspace. -/
theorem cubicalHomology_exact_subspace (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk (P.cubicalHomologyδ k n m h)
      (HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map P.map) m)
      (P.cubicalHomologyδ_comp k n m h)).Exact :=
  (shortExact_cubicalChainComplexShortComplex k P).homology_exact₁ n m h

/-- Exactness at the cubical homology of the ambient space. -/
theorem cubicalHomology_exact_space (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map P.map) n)
      (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n)
      (by rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (shortExact_cubicalChainComplexShortComplex k P).homology_exact₂ n

/-- Exactness at the relative cubical homology. -/
theorem cubicalHomology_exact_relative (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n)
      (P.cubicalHomologyδ k n m h)
      (P.comp_cubicalHomologyδ k n m h)).Exact :=
  (shortExact_cubicalChainComplexShortComplex k P).homology_exact₃ n m h

/-- **The connecting morphisms of cubical and singular homology correspond** under the comparison
isomorphisms. -/
theorem singularCubicalHomologyIso_hom_cubicalHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (singularCubicalHomologyIso k P n).hom ≫ P.cubicalHomologyδ k n m h =
      (P.shortExact_singularChainComplexShortComplex (ModuleCat.of k k)).δ n m h ≫
        (TauCeti.singularCubicalHomologyIso k P.snd m).hom := by
  rw [singularCubicalHomologyIso_hom, TauCeti.singularCubicalHomologyIso_hom,
    ← singularToCubicalShortComplex_τ₁, ← singularToCubicalShortComplex_τ₃]
  exact (HomologicalComplex.HomologySequence.δ_naturality (singularToCubicalShortComplex k P)
    (P.shortExact_singularChainComplexShortComplex _)
    (shortExact_cubicalChainComplexShortComplex k P) n m h).symm

/-! ### Excision -/

variable {k}

/-- A map of pairs inducing isomorphisms on relative singular homology induces isomorphisms on
relative cubical homology. -/
theorem isIso_homologyMap_cubicalChainComplexMap_of_isIso {P P' : TopPair.{u}} (f : P ⟶ P')
    (n : ℕ) [IsIso (P.singularHomologyMap f (ModuleCat.of k k) n)] :
    IsIso (HomologicalComplex.homologyMap (cubicalChainComplexMap k f) n) := by
  have := singularCubicalHomologyIso_hom_naturality k f n
  rw [← Iso.eq_inv_comp] at this
  rw [this]
  infer_instance

/-- **Excision for cubical homology.** If the interiors of `A` and `B` cover `X`, the inclusion of
pairs `(A, A ∩ B) ⟶ (X, B)` induces isomorphisms on relative cubical homology. -/
theorem isIso_homologyMap_cubicalChainComplexMap_excisionMap {X : TopCat.{u}} (A B : Set X)
    (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cubicalChainComplexMap k (excisionMap A B)) n) :=
  have := isIso_singularHomologyMap_excisionMap (ModuleCat.of k k) A B h n
  isIso_homologyMap_cubicalChainComplexMap_of_isIso _ n

/-- **Excision of a set with closure in the interior of the subspace**, for cubical homology. -/
theorem isIso_homologyMap_cubicalChainComplexMap_excisionMap_compl {X : TopCat.{u}} (B Z : Set X)
    (h : closure Z ⊆ interior B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cubicalChainComplexMap k (excisionMap Zᶜ B)) n) :=
  have := isIso_singularHomologyMap_excisionMap_compl (ModuleCat.of k k) B Z h n
  isIso_homologyMap_cubicalChainComplexMap_of_isIso _ n

end TopPair
