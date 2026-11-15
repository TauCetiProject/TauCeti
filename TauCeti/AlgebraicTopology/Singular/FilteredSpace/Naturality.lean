/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Comparison
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
public import TauCeti.Topology.Order.Sublevel

/-!
# The comparison theorem for filtered spaces

Let `X : ℤ → Set Y` and `X' : ℤ → Set Y'` be increasing families of subsets of topological spaces,
and let `g : Y ⟶ Y'` be a continuous map carrying each `X q` into `X' q`. Then `g` induces a
morphism of spectral sequences (`TauCeti.filteredSpaceSpectralSequenceMap`) which, on the first
page, is the map induced in relative homology by the maps of pairs
`(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` (`TauCeti.filteredSpaceStepMap`), so that it is an
isomorphism from the first page on as soon as these maps are isomorphisms in homology
(`TauCeti.isIso_filteredSpaceSpectralSequenceMap_hom_f`).

This file deduces the comparison theorem: if both filtrations are finite, empty at an index `a`
and the whole space at an index `b`, and `g` induces isomorphisms on the relative singular
homology of the pairs `(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` for `a ≤ q < b`, then `g` induces
isomorphisms on the singular homology of `Y` and `Y'`
(`TauCeti.isIso_singularHomologyFunctor_map_of_isIso_filteredSpaceStepMap`).

For the sublevel filtration `X q = {f ≤ v q}` of a function `f : Y → ℝ` cut at increasing values
`v q`, such as the critical-band filtration of a Morse or Morse–Bott function, a map `g` with
`f' ∘ g ≤ f` carries each sublevel of `f` into the sublevel of `f'` at the same value. So when
both functions take their values in `(v a, v b]`, a map which is an isomorphism on the relative
homology of every band is an isomorphism in homology
(`TauCeti.isIso_singularHomologyFunctor_map_of_isIso_sublevelPair`).

## Main results

* `TauCeti.isIso_singularHomologyFunctor_map_of_isIso_filteredSpaceStepMap`: the comparison
  theorem for finite filtrations of spaces.
* `TauCeti.isIso_singularHomologyFunctor_map_of_isIso_sublevelPair`: its form for sublevel
  filtrations.

## References

* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 3.4, the comparison theorem.
* R. L. Cohen, K. Iga and P. Norbury, *Topics in Morse Theory*, lecture notes, 2006,
  Theorems 15.6–15.7, the spectral sequence of the critical-band filtration.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  {Y Y' : TopCat.{w}} {X : ℤ → Set Y} {X' : ℤ → Set Y'}

section Comparison

variable (hX : Monotone X) (hX' : Monotone X') (g : Y ⟶ Y')
  (hg : ∀ q, Set.MapsTo g (X q) (X' q))

/-- Outside the indices `a ≤ q < b` of a filtration which is empty at `a` and everything at `b`,
consecutive stages agree. -/
private lemma eq_of_lt_or_le {X : ℤ → Set Y} (hX : Monotone X) {a b : ℤ} (ha : X a = ∅)
    (hb : X b = Set.univ) {q : ℤ} (hq : ¬(a ≤ q ∧ q < b)) : X (q + 1) = X q := by
  rcases lt_or_ge q a with hqa | hqa
  · rw [Set.eq_empty_of_subset_empty ((hX (by lia : q + 1 ≤ a)).trans ha.le),
      Set.eq_empty_of_subset_empty ((hX hqa.le).trans ha.le)]
  · rw [Set.eq_univ_of_univ_subset (hb.symm.subset.trans (hX (by lia : b ≤ q + 1))),
      Set.eq_univ_of_univ_subset (hb.symm.subset.trans (hX (by lia : b ≤ q)))]

/-- A pair `(X (q + 1), X q)` of equal consecutive stages has no relative homology. -/
private lemma isZero_singularHomology_ofInclusion_of_eq {q : ℤ} (hq : X (q + 1) = X q) (n : ℕ) :
    IsZero ((TopPair.ofInclusion (hX (by lia : q ≤ q + 1))).singularHomology R n) :=
  (TopPair.isZero_singularHomology_ofInclusion_congr R _ (subset_refl (X q)) hq rfl n).2
    (TopPair.isZero_singularHomology_ofInclusion_self R _ n)

/-- The top stages of the filtrations are the whole singular chain complexes, on which the
morphism of filtrations induced by `g` is the singular chain map of `g`. So an isomorphism in
cohomology there is an isomorphism in singular homology. -/
private lemma isIso_singularHomologyFunctor_map_of_isIso_homologyMap_app_top (n : ℕ)
    (hα : IsIso (HomologicalComplex.homologyMap ((filteredSpaceFiltrationMap R hX hX' g hg).app ⊤)
      (-n : ℤ))) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g) := by
  have hX₀ : IsIso (CochainComplex.filtrationEInt (singularChainFiltration R X) ⊤).arrow := by
    rw [CochainComplex.filtrationEInt_top]
    infer_instance
  have hX₀' : IsIso (CochainComplex.filtrationEInt (singularChainFiltration R X') ⊤).arrow := by
    rw [CochainComplex.filtrationEInt_top]
    infer_instance
  have hcomm := congrArg (HomologicalComplex.homologyMap · (-n : ℤ))
    (filteredSpaceFiltrationMap_app_comp R hX hX' g hg ⊤)
  simp only [HomologicalComplex.homologyMap_comp] at hcomm
  have : IsIso (HomologicalComplex.homologyMap
      ((CochainComplex.filtrationFunctorObjIso _ (monotone_singularChainFiltration R hX) ⊤).hom ≫
        (CochainComplex.filtrationEInt (singularChainFiltration R X) ⊤).arrow) (-n : ℤ) ≫
      HomologicalComplex.homologyMap
        (extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat)
        (-n : ℤ)) := by
    rw [HomologicalComplex.homologyMap_comp, ← hcomm]
    infer_instance
  have hg' : IsIso (HomologicalComplex.homologyMap
      (extendMap (SSet.chainComplexMap (TopCat.toSSet.map g) R) ComplexShape.embeddingDownNat)
      (-n : ℤ)) :=
    IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap
      ((CochainComplex.filtrationFunctorObjIso _ (monotone_singularChainFiltration R hX) ⊤).hom ≫
        (CochainComplex.filtrationEInt (singularChainFiltration R X) ⊤).arrow) (-n : ℤ)) _
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 <|
    (quasiIsoAt_extendMap_iff (SSet.chainComplexMap (TopCat.toSSet.map g) R)
      ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)).1
        ((quasiIsoAt_iff_isIso_homologyMap _ _).2 hg')

/-- **The comparison theorem for filtered spaces.** Let `X` and `X'` be finite filtrations of `Y`
and `Y'`, empty at the index `a` and everything at the index `b`, and let `g : Y ⟶ Y'` carry each
`X q` into `X' q`. If `g` induces isomorphisms on the relative singular homology of the pairs
`(X (q + 1), X q) ⟶ (X' (q + 1), X' q)` for `a ≤ q < b` in every degree, then it induces
isomorphisms on the singular homology of `Y` and `Y'`. -/
theorem isIso_singularHomologyFunctor_map_of_isIso_filteredSpaceStepMap {a b : ℤ}
    (ha : X a = ∅) (ha' : X' a = ∅) (hb : X b = Set.univ) (hb' : X' b = Set.univ)
    (h : ∀ q, a ≤ q → q < b → ∀ n : ℕ, IsIso (TopPair.singularHomologyMap
      (filteredSpaceStepMap hX hX' g hg (by lia : q ≤ q + 1)) R n))
    (n : ℕ) : IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g) := by
  have h' (q : ℤ) (n : ℕ) : IsIso (TopPair.singularHomologyMap
      (filteredSpaceStepMap hX hX' g hg (by lia : q ≤ q + 1)) R n) := by
    by_cases hq : a ≤ q ∧ q < b
    · exact h q hq.1 hq.2 n
    · exact isIso_of_source_target_iso_zero _
        (isZero_singularHomology_ofInclusion_of_eq R hX (eq_of_lt_or_le hX ha hb hq) n).isoZero
        (isZero_singularHomology_ofInclusion_of_eq R hX' (eq_of_lt_or_le hX' ha' hb' hq) n).isoZero
  have hα := CochainComplex.isIso_homologyMap_of_isIso_spectralSequence_page _
    (monotone_singularChainFiltration R hX) _ (monotone_singularChainFiltration R hX')
    (filteredSpaceFiltrationMap R hX hX' g hg) (singularChainFiltration_eq_bot R ha)
    (singularChainFiltration_eq_bot R ha') (singularChainFiltration_eq_top R hb)
    (singularChainFiltration_eq_top R hb') 2 le_rfl
    (by
      rw [← filteredSpaceSpectralSequenceMap_def]
      exact isIso_filteredSpaceSpectralSequenceMap_hom_f R hX hX' g hg h' 2 le_rfl) (-n)
  exact isIso_singularHomologyFunctor_map_of_isIso_homologyMap_app_top R hX hX' g hg n hα

end Comparison

section Sublevel

variable (g : Y ⟶ Y') {f : Y → ℝ} {f' : Y' → ℝ} (hgf : ∀ y, f' (g y) ≤ f y)

/-- **Comparison of sublevel filtrations.** Let `f : Y → ℝ` and `f' : Y' → ℝ`, and let
`g : Y ⟶ Y'` satisfy `f' ∘ g ≤ f`, so that `g` carries each sublevel `{f ≤ c}` into
`{f' ≤ c}`. Cut both functions at the values of a monotone `v : ℤ → ℝ`, with all values of `f`
and `f'` in `(v a, v b]`. If `g` induces isomorphisms on the relative singular homology of the
sublevel pairs `({f ≤ v (q + 1)}, {f ≤ v q}) ⟶ ({f' ≤ v (q + 1)}, {f' ≤ v q})` for `a ≤ q < b` in
every degree, for instance of the critical bands of two Morse–Bott functions, then it induces
isomorphisms on singular homology. -/
theorem isIso_singularHomologyFunctor_map_of_isIso_sublevelPair {v : ℤ → ℝ} (hv : Monotone v)
    {a b : ℤ} (ha : ∀ y, v a < f y) (ha' : ∀ y, v a < f' y) (hb : ∀ y, f y ≤ v b)
    (hb' : ∀ y, f' y ≤ v b)
    (h : ∀ q, a ≤ q → q < b → ∀ n : ℕ, IsIso (TopPair.singularHomologyMap
      (filteredSpaceStepMap (X := fun q ↦ {y | f y ≤ v q}) (X' := fun q ↦ {y | f' y ≤ v q})
        ((sublevel_mono f).comp hv) ((sublevel_mono f').comp hv) g
        (fun _ _ hy ↦ (hgf _).trans hy) (by lia : q ≤ q + 1)) R n))
    (n : ℕ) : IsIso (((AlgebraicTopology.singularHomologyFunctor A n).obj R).map g) :=
  isIso_singularHomologyFunctor_map_of_isIso_filteredSpaceStepMap R ((sublevel_mono f).comp hv)
    ((sublevel_mono f').comp hv) g (fun _ _ hy ↦ (hgf _).trans hy)
    (Set.eq_empty_of_forall_notMem fun y hy ↦ (ha y).not_ge hy)
    (Set.eq_empty_of_forall_notMem fun y hy ↦ (ha' y).not_ge hy)
    (Set.eq_univ_of_forall hb) (Set.eq_univ_of_forall hb') h n

end Sublevel

end TauCeti
