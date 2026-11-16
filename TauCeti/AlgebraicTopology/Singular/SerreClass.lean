/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.SerreClass
public import TauCeti.AlgebraicTopology.Singular.Empty
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate

/-!
# Singular homology of pairs modulo a Serre class

Let `Q` be a Serre class in an abelian coefficient category, for instance the torsion abelian
groups. This file proves the five lemma modulo `Q` for the ambient spaces of topological pairs: a
map of pairs `f : (X, A) ⟶ (X', A')` inducing isomorphisms modulo `Q` on `Hₙ(A)` and `Hₙ(X, A)`,
an epimorphism modulo `Q` on `Hₙ₊₁(X, A)` and a monomorphism modulo `Q` on `Hₙ₋₁(A)`, induces an
isomorphism modulo `Q` on `Hₙ(X)` (`TopPair.isoModSerre_homologyMap_fst`). When the subspaces are
empty, an isomorphism modulo `Q` on relative homology is one on the homology of the spaces
(`TopPair.isoModSerre_homologyMap_fst_of_isEmpty`). For the class of zero objects these are
`TopPair.isIso_homologyMap_fst_of_isIso` and `TopPair.isIso_homologyMap_fst_of_isEmpty`.

These are the steps of Serre's comparison arguments modulo a class of abelian groups along a
filtration of a space by subspaces, such as the skeletal filtration of the total space of a
fibration.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294, Chapter I.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)
  (Q : ObjectProperty A) [Q.IsSerreClass] {P P' : TopPair.{w}} (f : P ⟶ P')

/-- **The five lemma modulo a Serre class for the ambient space of a pair.** A map of pairs
`f : (X, A) ⟶ (X', A')` inducing isomorphisms modulo a Serre class `Q` on `Hₙ(A)` and `Hₙ(X, A)`,
an epimorphism modulo `Q` on `Hₙ₊₁(X, A)` and a monomorphism modulo `Q` on `Hₘ(A)` for
`m + 1 = n`, induces an isomorphism modulo `Q` on `Hₙ(X)`. -/
lemma isoModSerre_homologyMap_fst (n : ℕ)
    (hrel' : Q.epiModSerre (TopPair.singularHomologyMap f R (n + 1)))
    (hsnd : Q.isoModSerre (SSet.homologyMap (TopCat.toSSet.map (Hom.snd f)) R n))
    (hrel : Q.isoModSerre (TopPair.singularHomologyMap f R n))
    (hsnd' : ∀ m, m + 1 = n →
      Q.monoModSerre (SSet.homologyMap (TopCat.toSSet.map (Hom.snd f)) R m)) :
    Q.isoModSerre (SSet.homologyMap (TopCat.toSSet.map (Hom.fst f)) R n) := by
  have := HomologicalComplex.HomologySequence.isoModSerre_homologyMap_τ₂
    (SSetPair.chainComplexShortComplexMap (toSSetPair.map f) R)
    ((toSSetPair.obj P).shortExact_chainComplexShortComplex R)
    ((toSSetPair.obj P').shortExact_chainComplexShortComplex R) Q n
  simp only [SSetPair.chainComplexShortComplexMap_τ₁, SSetPair.chainComplexShortComplexMap_τ₂,
    SSetPair.chainComplexShortComplexMap_τ₃, ComplexShape.down_Rel] at this
  -- The homology maps of these chain maps are `SSet.homologyMap` and
  -- `TopPair.singularHomologyMap` by definition.
  exact this (fun i (hi : n + 1 = i) ↦ hi ▸ hrel') hsnd hrel fun m (hm : m + 1 = n) ↦ hsnd' m hm

/-- A map of pairs `f : (X, ∅) ⟶ (X', ∅)` whose subspaces are empty induces an isomorphism modulo
a Serre class `Q` on `Hₙ(X) ⟶ Hₙ(X')` if it induces one on `Hₙ(X, ∅) ⟶ Hₙ(X', ∅)`. Only the target
subspace needs to be assumed empty, since `f` maps the source subspace into it. -/
lemma isoModSerre_homologyMap_fst_of_isEmpty [IsEmpty P'.snd] (n : ℕ)
    (hrel : Q.isoModSerre (TopPair.singularHomologyMap f R n)) :
    Q.isoModSerre (SSet.homologyMap (TopCat.toSSet.map (Hom.fst f)) R n) := by
  have : IsEmpty P.snd := ⟨fun a ↦ isEmptyElim (Hom.snd f a)⟩
  -- For a pair `T` with empty subspace, `Hₙ(X) ⟶ Hₙ(X, ∅)` is an isomorphism, by the long exact
  -- sequence of the pair: the homology of the empty subspace vanishes.
  have hπ (T : TopPair.{w}) [IsEmpty T.snd] : IsIso (T.singularHomologyπ R n) := by
    have hA (m : ℕ) : IsZero ((toSSetPair.obj T).left.homology R m) :=
      SSet.isZero_homology_of_hasDimensionLT _ R m 0
    have := (T.singularHomology_exact_space R n).mono_g ((hA n).eq_of_src _ _)
    cases n with
    | zero => exact isIso_of_mono_of_epi _
    | succ m =>
      have := (T.singularHomology_exact_relative R (m + 1) m).epi_f ((hA m).eq_of_tgt _ _)
      exact isIso_of_mono_of_epi _
  -- Through these isomorphisms, the map on `Hₙ(X)` is the map on `Hₙ(X, ∅)`.
  have h : Q.isoModSerre (SSet.homologyMap (TopCat.toSSet.map (Hom.fst f)) R n ≫
      P'.singularHomologyπ R n) := by
    rw [singularHomologyπ_naturality]
    exact Q.isoModSerre.comp_mem _ _ (Q.isomorphisms_le_isoModSerre _ (hπ P)) hrel
  exact Q.isoModSerre.of_postcomp _ _ (Q.isomorphisms_le_isoModSerre _ (hπ P')) h

end TopPair
