/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Quasi-isomorphisms in a single degree under functors

This file records a degreewise criterion for a functor to send a map of homological complexes which
is a quasi-isomorphism in a given degree to a quasi-isomorphism in that degree, the form in which it
is used when only part of the homology of a complex is controlled, for instance through a tower of
truncations.

* `HomologicalComplex.quasiIsoAt_map_of_preservesLeftHomologyOf`: a functor which preserves the
  homology of the short complexes in degree `i` of two complexes sends a quasi-isomorphism in degree
  `i` between them to a quasi-isomorphism in degree `i`. This is the degreewise form of Mathlib's
  `HomologicalComplex.quasiIsoAt_map_of_preservesHomology`; it applies to left exact functors, such
  as global sections of sheaves, on complexes whose homology they happen to preserve.

The degreewise criterion for the second map of a short exact sequence of complexes,
`CategoryTheory.ShortComplex.ShortExact.quasiIsoAt_g`, is in
`TauCeti.Algebra.Homology.HomologySequenceLemmas`.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

/-- A functor preserving the homology of the short complexes in degree `i` of two homological
complexes sends a map between them which is a quasi-isomorphism in degree `i` to a
quasi-isomorphism in degree `i`. -/
lemma quasiIsoAt_map_of_preservesLeftHomologyOf {C D ι : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] {c : ComplexShape ι} (F : C ⥤ D)
    [F.PreservesZeroMorphisms] {K L : HomologicalComplex C c} (f : K ⟶ L) (i : ι) [K.HasHomology i]
    [L.HasHomology i] [((F.mapHomologicalComplex c).obj K).HasHomology i]
    [((F.mapHomologicalComplex c).obj L).HasHomology i] [F.PreservesLeftHomologyOf (K.sc i)]
    [F.PreservesLeftHomologyOf (L.sc i)] [QuasiIsoAt f i] :
    QuasiIsoAt ((F.mapHomologicalComplex c).map f) i := by
  rw [quasiIsoAt_iff] at *
  have : (F.mapShortComplex.obj ((shortComplexFunctor C c i).obj K)).HasHomology :=
    ‹((F.mapHomologicalComplex c).obj K).HasHomology i›
  have : (F.mapShortComplex.obj ((shortComplexFunctor C c i).obj L)).HasHomology :=
    ‹((F.mapHomologicalComplex c).obj L).HasHomology i›
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology F ((shortComplexFunctor C c i).map f)

end HomologicalComplex
