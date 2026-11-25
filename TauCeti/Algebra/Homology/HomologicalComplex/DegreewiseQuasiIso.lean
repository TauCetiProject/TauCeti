/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Quasi-isomorphisms in a single degree

This file records two degreewise criteria for a map of homological complexes to be a
quasi-isomorphism in a given degree, the form in which they are used when only part of the
homology of a complex is controlled, for instance through a tower of truncations.

* `HomologicalComplex.quasiIsoAt_map_of_preservesLeftHomologyOf`: a functor which preserves the
  homology of the short complexes in degree `i` of two complexes sends a quasi-isomorphism in degree
  `i` between them to a quasi-isomorphism in degree `i`. This is the degreewise form of Mathlib's
  `HomologicalComplex.quasiIsoAt_map_of_preservesHomology`; it applies to left exact functors, such
  as global sections of sheaves, on complexes whose homology they happen to preserve.
* `CategoryTheory.ShortComplex.ShortExact.quasiIsoAt_g`: in a short exact sequence of complexes,
  the second map is a quasi-isomorphism in degree `i` as soon as the first term is exact in degree
  `i` and in the degree following `i`. This is the degreewise form of
  `CategoryTheory.ShortComplex.ShortExact.quasiIso_g_iff`, read off from the long exact homology
  sequence.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

/-- A functor preserving the homology of the short complexes in degree `i` of two homological
complexes sends a map between them which is a quasi-isomorphism in degree `i` to a
quasi-isomorphism in degree `i`. -/
lemma quasiIsoAt_map_of_preservesLeftHomologyOf {C D ι : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [CategoryWithHomology D] {c : ComplexShape ι} (F : C ⥤ D)
    [F.Additive] {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [F.PreservesLeftHomologyOf (K.sc i)] [F.PreservesLeftHomologyOf (L.sc i)]
    [QuasiIsoAt f i] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map f) i := by
  rw [quasiIsoAt_iff] at *
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F ((shortComplexFunctor C c i).map f)

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

open HomologicalComplex

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)

include hS in
/-- In a short exact sequence of complexes, the second map is a quasi-isomorphism in degree `i` as
soon as the first term is exact in degree `i` and in the degree following `i`. -/
lemma quasiIsoAt_g (i : ι) (h₁ : S.X₁.ExactAt i) (h₂ : ∀ j, c.Rel i j → S.X₁.ExactAt j) :
    QuasiIsoAt S.g i := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap S.g i) :=
    (hS.homology_exact₂ i).mono_g (h₁.isZero_homology.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.g i) := by
    by_cases! hi : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hi
      exact (hS.homology_exact₃ i j hij).epi_f ((h₂ j hij).isZero_homology.eq_of_tgt _ _)
    · have := hS.epi_g
      exact epi_homologyMap_of_epi_of_not_rel S.g i hi
  exact isIso_of_mono_of_epi _

end CategoryTheory.ShortComplex.ShortExact
