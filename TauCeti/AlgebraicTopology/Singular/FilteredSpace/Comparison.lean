/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic

/-!
# The comparison theorem for filtered spaces

Let `X : ℤ → Set Y` and `X' : ℤ → Set Y'` be increasing families of subsets of topological spaces,
and let `φ : Y ⟶ Y'` be a continuous map carrying each `X q` into `X' q`. It induces a morphism of
the spectral sequences of the filtered spaces (`TauCeti.filteredSpaceSpectralSequenceMap`), which
on the first page is the map `Hₙ(X (q + 1), X q) ⟶ Hₙ(X' (q + 1), X' q)` induced by `φ`.

Since the spectral sequences of finite filtrations converge to the singular homology of the
spaces, this gives the **comparison theorem for filtered spaces**: if both filtrations are empty at
a stage `a` and everything at a stage `b`, and `φ` induces isomorphisms
`Hₙ(X (q + 1), X q) ≅ Hₙ(X' (q + 1), X' q)` for every `a ≤ q < b` and every `n`, then `φ` induces
isomorphisms `Hₙ(Y) ≅ Hₙ(Y')` in every degree. For the sublevels `X q = {f ≤ a q}` and
`X' q = {g ≤ a q}` of functions with `g ∘ φ ≤ f`, the hypotheses only concern the homology of the
critical bands.

## Main results

* `TauCeti.isIso_singularHomologyFunctor_map_of_isIso_singularHomologyMap`: the comparison
  theorem.

## References

* C. A. Weibel, *An introduction to homological algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press, 1994, Comparison Theorem 5.2.12.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {Y Y' : TopCat.{w}} {X : ℤ → Set Y} {X' : ℤ → Set Y'} (hX : Monotone X) (hX' : Monotone X')

/-- Outside the stages `a ≤ q < b` of a filtration that is empty at `a` and everything at `b`,
consecutive stages agree. -/
private lemma succ_subset_of_not_le_and_lt {Z : Type*} {W : ℤ → Set Z} (hW : Monotone W) {a b q : ℤ}
    (ha : W a = ∅) (hb : W b = Set.univ) (hq : ¬(a ≤ q ∧ q < b)) : W (q + 1) ⊆ W q := by
  rcases lt_or_ge q a with hqa | hbq
  · exact (hW (by lia : q + 1 ≤ a)).trans (ha ▸ Set.empty_subset _)
  · exact fun _ _ ↦ hW (not_lt.mp fun h ↦ hq ⟨hbq, h⟩) (hb ▸ Set.mem_univ _)

/-- The map of singular chains induced by a map of filtered spaces is a quasi-isomorphism in
degree `n` as soon as its restriction to the top stages of the filtrations is a
quasi-isomorphism in degree `-n` of the reindexed complexes. -/
private lemma isIso_singularHomologyFunctor_map_of_isIso_homologyMap_app_top (φ : Y ⟶ Y')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) (n : ℕ)
    (h : IsIso (homologyMap ((filteredSpaceFiltrationMap R hX hX' φ hφ).app ⊤) (-n))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map φ) := by
  have : IsIso (CochainComplex.filtrationEInt (singularChainFiltration R X) ⊤).arrow := by
    rw [CochainComplex.filtrationEInt_top]
    infer_instance
  have : IsIso (CochainComplex.filtrationEInt (singularChainFiltration R X') ⊤).arrow := by
    rw [CochainComplex.filtrationEInt_top]
    infer_instance
  -- The top stages of the filtrations are the whole complexes, so the identity
  -- `α_⊤ ≫ ι' = ι ≫ φ_*` of `filteredSpaceFiltrationMap_app_comp` has isomorphisms `ι` and `ι'`.
  have hC : IsIso (homologyMap (CochainComplex.filtrationFunctorArrow _
      (monotone_singularChainFiltration R hX) ⊤ ≫ extendMap
        (SSet.chainComplexMap (TopCat.toSSet.map φ) R) ComplexShape.embeddingDownNat) (-n)) := by
    rw [← filteredSpaceFiltrationMap_app_comp R hX hX' φ hφ ⊤, homologyMap_comp]
    infer_instance
  rw [homologyMap_comp] at hC
  have := IsIso.of_isIso_comp_left (homologyMap (CochainComplex.filtrationFunctorArrow _
    (monotone_singularChainFiltration R hX) ⊤) (-n)) (homologyMap (extendMap
      (SSet.chainComplexMap (TopCat.toSSet.map φ) R) ComplexShape.embeddingDownNat) (-n))
  rw [singularHomologyFunctor_obj_map]
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 ((quasiIsoAt_extendMap_iff _ _ rfl).1
    ((quasiIsoAt_iff_isIso_homologyMap _ _).2 this))

/-- **The comparison theorem for filtered spaces.** Let `X` and `X'` be finite increasing
filtrations of spaces `Y` and `Y'`, empty at a stage `a` and everything at a stage `b`, and let
`φ : Y ⟶ Y'` carry each `X q` into `X' q`. If for every `a ≤ q < b` the map of pairs
`(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` induced by `φ` induces isomorphisms on relative singular
homology in every degree, then `φ` induces isomorphisms on singular homology in every degree. -/
theorem isIso_singularHomologyFunctor_map_of_isIso_singularHomologyMap (φ : Y ⟶ Y')
    (hφ : ∀ q, Set.MapsTo φ (X q) (X' q)) {a b : ℤ} (ha : X a = ∅) (ha' : X' a = ∅)
    (hb : X b = Set.univ) (hb' : X' b = Set.univ)
    (h : ∀ q, a ≤ q → q < b → ∀ n, IsIso (TopPair.singularHomologyMap
      (filteredSpaceStepMap hX hX' φ hφ (Int.le_add_one le_rfl : q ≤ q + 1)) R n))
    (n : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map φ) := by
  refine isIso_singularHomologyFunctor_map_of_isIso_homologyMap_app_top R hX hX' φ hφ n ?_
  refine CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page _
    (monotone_singularChainFiltration R hX) _ (monotone_singularChainFiltration R hX')
    (filteredSpaceFiltrationMap R hX hX' φ hφ) (singularChainFiltration_eq_bot R ha)
    (singularChainFiltration_eq_bot R ha') (singularChainFiltration_eq_top R hb)
    (singularChainFiltration_eq_top R hb') 2 le_rfl (fun pq ↦ ?_) (-n)
  rw [← filteredSpaceSpectralSequenceMap_def]
  refine isIso_filteredSpaceSpectralSequenceMap_hom_f R hX hX' φ hφ (fun q k ↦ ?_) 2 le_rfl pq
  by_cases hq : a ≤ q ∧ q < b
  · exact h q hq.1 hq.2 k
  · -- Outside `a ≤ q < b` both pairs `(X (q + 1), X q)` and `(X' (q + 1), X' q)` are trivial.
    exact isIso_of_source_target_iso_zero _
      (TopPair.isZero_singularHomology_of_surjective_map
        (TopPair.ofInclusion (hX (Int.le_add_one le_rfl))) R (fun (y : X (q + 1)) ↦
          ⟨(⟨y.1, succ_subset_of_not_le_and_lt hX ha hb hq y.2⟩ : X q), rfl⟩) k).isoZero
      (TopPair.isZero_singularHomology_of_surjective_map
        (TopPair.ofInclusion (hX' (Int.le_add_one le_rfl))) R (fun (y : X' (q + 1)) ↦
          ⟨(⟨y.1, succ_subset_of_not_le_and_lt hX' ha' hb' hq y.2⟩ : X' q), rfl⟩) k).isoZero

end TauCeti
