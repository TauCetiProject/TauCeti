/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-!
# The homology sequence modulo a Serre class

Let `P` be a Serre class in an abelian category `C`, and let `φ : S₁ ⟶ S₂` be a morphism of short
exact sequences `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of homological complexes. The five lemma for the long
exact homology sequences holds modulo `P`: if `φ.τ₁` and `φ.τ₃` induce isomorphisms modulo `P` on
homology in degree `j`, `φ.τ₃` is an epimorphism modulo `P` in the degree before `j` and `φ.τ₁` a
monomorphism modulo `P` in the degree after `j`, then `φ.τ₂` induces an isomorphism modulo `P` in
degree `j` (`HomologicalComplex.HomologySequence.isoModSerre_homologyMap_τ₂`). For the class of zero
objects this is `HomologicalComplex.HomologySequence.isIso_homologyMap_τ₂` of Mathlib.

The proof passes to the localization of `C` with respect to `P`, which is abelian and into which
the localization functor is exact, and applies the four lemmas there to the image of the long
exact sequence. Exactness of that image is the general fact that a functor preserving homology
sends exact sequences to exact sequences (`CategoryTheory.ComposableArrows.Exact.map`).

## Main results

* `CategoryTheory.ComposableArrows.Exact.map`: a functor preserving homology preserves exactness of
  composable arrows.
* `HomologicalComplex.HomologySequence.monoModSerre_homologyMap_τ₂`,
  `HomologicalComplex.HomologySequence.epiModSerre_homologyMap_τ₂`,
  `HomologicalComplex.HomologySequence.isoModSerre_homologyMap_τ₂`: the four and five lemmas
  modulo a Serre class for the middle map.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter I.
-/

public section

open CategoryTheory Limits ComposableArrows Abelian

namespace CategoryTheory.ComposableArrows

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A functor which preserves zero morphisms and homology sends an exact sequence of composable
arrows to an exact sequence. -/
lemma Exact.map {n : ℕ} {S : ComposableArrows C n} (hS : S.Exact) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [F.PreservesHomology] :
    ((F.mapComposableArrows n).obj S).Exact where
  zero i hi := by
    simpa only [Functor.mapComposableArrows_obj_map, Functor.map_comp, F.map_zero] using
      congrArg F.map (hS.zero i hi)
  exact i hi := (hS.exact i hi).map F

end CategoryTheory.ComposableArrows

namespace HomologicalComplex.HomologySequence

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
  (P : ObjectProperty C) [P.IsSerreClass]

include hS₁ hS₂

/-- The map `φ.τ₂` is a monomorphism modulo a Serre class `P` on homology in degree `j` if `φ.τ₁`
and `φ.τ₃` are monomorphisms modulo `P` in degree `j` and `φ.τ₃` is an epimorphism modulo `P` in
the degrees preceding `j`. -/
lemma monoModSerre_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → P.epiModSerre (homologyMap φ.τ₃ i))
    (h₂ : P.monoModSerre (homologyMap φ.τ₁ j))
    (h₃ : P.monoModSerre (homologyMap φ.τ₃ j)) :
    P.monoModSerre (homologyMap φ.τ₂ j) := by
  -- Pass to the abelian localization `L`, which is exact.
  let L := P.isoModSerre.Q
  let := Localization.preadditive L P.isoModSerre
  have := Localization.functor_additive L P.isoModSerre
  let := ObjectProperty.SerreClassLocalization.abelian L P
  have := ObjectProperty.SerreClassLocalization.preservesFiniteLimits L P
  have := ObjectProperty.SerreClassLocalization.preservesFiniteColimits L P
  simp only [← ObjectProperty.SerreClassLocalization.mono_map_iff L P,
    ← ObjectProperty.SerreClassLocalization.epi_map_iff L P] at h₁ h₂ h₃ ⊢
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    -- The image of the exact sequence `H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃)`.
    exact mono_of_epi_of_mono_of_mono
      ((L.mapComposableArrows 3).map
        ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij)))
      ((composableArrows₅_exact hS₁ i j hij).δ₀.δ₀.map L)
      ((composableArrows₅_exact hS₂ i j hij).δ₀.δ₀.map L) (h₁ i hij) h₂ h₃
  · -- With no preceding degree, `H_j(X₁) ⟶ H_j(X₂)` is a monomorphism.
    have := hS₂.mono_f
    have := mono_homologyMap_of_mono_of_not_rel S₂.f j (by simpa using hj)
    exact mono_of_mono_of_mono_of_mono ((L.mapComposableArrows 2).map (mapComposableArrows₂ φ j))
      ((composableArrows₂_exact hS₁ j).map L) (Functor.map_mono L (homologyMap S₂.f j)) h₂ h₃

/-- The map `φ.τ₂` is an epimorphism modulo a Serre class `P` on homology in degree `j` if `φ.τ₁`
and `φ.τ₃` are epimorphisms modulo `P` in degree `j` and `φ.τ₁` is a monomorphism modulo `P` in
the degrees following `j`. -/
lemma epiModSerre_homologyMap_τ₂ (j : ι)
    (h₁ : P.epiModSerre (homologyMap φ.τ₁ j))
    (h₂ : P.epiModSerre (homologyMap φ.τ₃ j))
    (h₃ : ∀ k, c.Rel j k → P.monoModSerre (homologyMap φ.τ₁ k)) :
    P.epiModSerre (homologyMap φ.τ₂ j) := by
  -- Pass to the abelian localization `L`, which is exact.
  let L := P.isoModSerre.Q
  let := Localization.preadditive L P.isoModSerre
  have := Localization.functor_additive L P.isoModSerre
  let := ObjectProperty.SerreClassLocalization.abelian L P
  have := ObjectProperty.SerreClassLocalization.preservesFiniteLimits L P
  have := ObjectProperty.SerreClassLocalization.preservesFiniteColimits L P
  simp only [← ObjectProperty.SerreClassLocalization.mono_map_iff L P,
    ← ObjectProperty.SerreClassLocalization.epi_map_iff L P] at h₁ h₂ h₃ ⊢
  by_cases hj : ∃ k, c.Rel j k
  · obtain ⟨k, hjk⟩ := hj
    -- The image of the exact sequence `H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃) ⟶ H_k(X₁)`.
    exact epi_of_epi_of_epi_of_mono
      ((L.mapComposableArrows 3).map
        ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ j k hjk)))
      ((composableArrows₅_exact hS₁ j k hjk).δlast.δlast.map L)
      ((composableArrows₅_exact hS₂ j k hjk).δlast.δlast.map L) h₁ h₂ (h₃ k hjk)
  · -- With no following degree, `H_j(X₂) ⟶ H_j(X₃)` is an epimorphism.
    have := hS₁.epi_g
    have := epi_homologyMap_of_epi_of_not_rel S₁.g j (by simpa using hj)
    exact epi_of_epi_of_epi_of_epi ((L.mapComposableArrows 2).map (mapComposableArrows₂ φ j))
      ((composableArrows₂_exact hS₂ j).map L) (Functor.map_epi L (homologyMap S₁.g j)) h₁ h₂

/-- **The five lemma modulo a Serre class for the middle map.** The map `φ.τ₂` is an isomorphism
modulo a Serre class `P` on homology in degree `j` if `φ.τ₁` and `φ.τ₃` are isomorphisms modulo
`P` in degree `j`, `φ.τ₃` is an epimorphism modulo `P` in the degrees preceding `j`, and `φ.τ₁` is
a monomorphism modulo `P` in the degrees following `j`. -/
lemma isoModSerre_homologyMap_τ₂ (j : ι)
    (h₁ : ∀ i, c.Rel i j → P.epiModSerre (homologyMap φ.τ₃ i))
    (h₂ : P.isoModSerre (homologyMap φ.τ₁ j))
    (h₃ : P.isoModSerre (homologyMap φ.τ₃ j))
    (h₄ : ∀ k, c.Rel j k → P.monoModSerre (homologyMap φ.τ₁ k)) :
    P.isoModSerre (homologyMap φ.τ₂ j) :=
  ⟨monoModSerre_homologyMap_τ₂ φ hS₁ hS₂ P j h₁ h₂.1 h₃.1,
    epiModSerre_homologyMap_τ₂ φ hS₁ hS₂ P j h₂.2 h₃.2 h₄⟩

end HomologicalComplex.HomologySequence
