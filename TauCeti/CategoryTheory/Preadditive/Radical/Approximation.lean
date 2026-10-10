/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Basic.Finite.Sigma
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite approximations of the categorical radical

For a finite family of objects whose radical morphism spaces into `Y` are finite-dimensional,
one radical morphism from a finite biproduct absorbs every radical morphism from that family.
Take one copy of each object for each vector of a basis of its radical space. The resulting
evaluation morphism is the first step in constructing right almost-split morphisms in categories
of finite representation type.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, V.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {k : Type*} [DivisionRing k] [Linear k C] [HasFiniteBiproducts C]

/-- A finite family with finite-dimensional radical spaces admits a single radical morphism
through which all its radical morphisms factor. Its source is a finite biproduct of copies of
the given objects. -/
theorem exists_radical_biproduct_factorization {ι : Type*} [Finite ι] (X : ι → C) (Y : C)
    [∀ i, FiniteDimensional k (jacobsonRadicalSubmodule k (X i) Y)] :
    ∃ (n : ι → ℕ) (f : (⨁ fun j : Σ i, Fin (n i) ↦ X j.1) ⟶ Y),
      f ∈ jacobsonRadical _ Y ∧ ∀ i (g : X i ⟶ Y), g ∈ jacobsonRadical (X i) Y →
        ∃ h : X i ⟶ (⨁ fun j : Σ i, Fin (n i) ↦ X j.1), h ≫ f = g := by
  classical
  let n i := Module.finrank k (jacobsonRadicalSubmodule k (X i) Y)
  let b i := Module.finBasis k (jacobsonRadicalSubmodule k (X i) Y)
  let Z (j : Σ i, Fin (n i)) := X j.1
  let f : (⨁ Z) ⟶ Y := biproduct.desc fun j ↦ (b j.1 j.2).val
  let := Fintype.ofFinite ι
  refine ⟨n, f, ?_, fun i g hg ↦ ?_⟩
  · simp only [f, biproduct.desc_eq]
    exact (jacobsonRadical _ Y).sum_mem fun j _ ↦
      comp_mem_jacobsonRadical_left _ (mem_jacobsonRadicalSubmodule.mp (b j.1 j.2).property)
  · let g' : jacobsonRadicalSubmodule k (X i) Y :=
      ⟨g, mem_jacobsonRadicalSubmodule.mpr hg⟩
    refine ⟨∑ j, (b i).repr g' j • biproduct.ι Z ⟨i, j⟩, ?_⟩
    simp only [Preadditive.sum_comp, Linear.smul_comp, f, biproduct.ι_desc]
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using
      congrArg (jacobsonRadicalSubmodule k (X i) Y).subtype ((b i).sum_repr g')

end TauCeti
