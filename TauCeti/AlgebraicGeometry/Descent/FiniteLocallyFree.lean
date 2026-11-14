/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.Descent.Fpqc
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Effective fpqc descent of finite locally free schemes

Let `p : S' ⟶ S` be surjective, flat and quasi-compact, over an arbitrary base `S`. A finite
locally free scheme over `S'`, equipped with a descent datum relative to `p`, descends to a finite
locally free scheme over `S`. Here finite local freeness means finite, flat, and locally of finite
presentation; no Noetherian hypothesis is imposed. The comparison is an isomorphism of descent
data, so it retains the cocycle, rather than just identifying the underlying schemes.

The rank function of the descended scheme pulls back to the original rank function. In
particular, prescribed ranks of finite subgroup schemes can be retained during descent.
Uniqueness and descent of morphisms are supplied by `DescentDatum.baseChangeHomEquiv`
and `DescentDatum.Hom.descendIso`.

A finite scheme is affine over its base, so effective descent for schemes affine over the cover
(`TauCeti.DescentDatum.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact`) supplies the
descended scheme. Finiteness, flatness and local finite presentation each satisfy fpqc descent,
so they pass to it (`TauCeti.DescentDatum.Hom.mem_of_descendsAlong`), and the rank of a base
change is the pulled-back rank (`AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd`).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1 and Corollaire 2.2.
* The Stacks Project, *Descent*, Section 35.23 (properties local in the fpqc topology).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S} [Surjective p] [Flat p] [QuasiCompact p]

/-- **Effective fpqc descent of finite locally free schemes.** Let `p : S' ⟶ S` be surjective,
flat and quasi-compact. Every descent datum relative to `p` on a finite locally free `X ⟶ S'` is
isomorphic to the canonical datum on the base change of a finite locally free `X₀ ⟶ S`, and the
rank of `X` is the rank of `X₀` pulled back along `p`. -/
theorem exists_finiteLocallyFree_baseChange_hom_isIso {X : Over S'} [IsFinite X.hom]
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] (D : DescentDatum p X) :
    ∃ X₀ : Over S, IsFinite X₀.hom ∧ Flat X₀.hom ∧ LocallyOfFinitePresentation X₀.hom ∧
      ∃ f : Hom (baseChange p X₀) D, IsIso f.hom ∧ X.hom.finrank = X₀.hom.finrank ∘ p := by
  obtain ⟨X₀, -, f, hf⟩ := D.exists_isAffineHom_baseChange_hom_isIso_of_quasiCompact
  have : IsFinite X₀.hom := f.mem_of_descendsAlong (P := @IsFinite) inferInstance
  have : Flat X₀.hom := f.mem_of_descendsAlong (P := @Flat) inferInstance
  have : LocallyOfFinitePresentation X₀.hom :=
    f.mem_of_descendsAlong (P := @LocallyOfFinitePresentation) inferInstance
  refine ⟨X₀, inferInstance, inferInstance, inferInstance, f, hf, ?_⟩
  -- The comparison is over `S'`, and finite-flat rank is invariant under this isomorphism.
  have : IsIso f.hom.left := (Over.forget _).map_isIso f.hom
  funext s
  have h := f.hom.w
  simp only [Over.pullback_obj_hom] at h
  rw [← Scheme.Hom.finrank_comp_left_of_isIso f.hom.left X.hom, h]
  exact Scheme.Hom.finrank_pullback_snd _ _ s

end TauCeti.DescentDatum
