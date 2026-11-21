/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Obj
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Tensoring with a complex of flat modules is exact

Let `P` be a homological complex of modules over a commutative ring `R` whose terms are flat. Then
the functor `X ↦ X ⊗ P` (`HomologicalComplex.objTensor`) carries short exact sequences of modules
to short exact sequences of complexes
(`HomologicalComplex.shortExact_map_objTensor_of_flat`): in each degree `n` it is tensoring on the
right with the flat module `P.X n` (`HomologicalComplex.objTensorCompEvalIso`).
-/

public section

namespace HomologicalComplex

open CategoryTheory Limits MonoidalCategory

universe u

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  (P : HomologicalComplex (ModuleCat.{u} R) c) [∀ n, Module.Flat R (P.X n)]

/-- **Tensoring with a complex of flat modules is exact**: if every term of `P` is flat, then
`X ↦ X ⊗ P` carries short exact sequences of modules to short exact sequences of complexes. -/
theorem shortExact_map_objTensor_of_flat {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.map P.objTensor).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  rw [← ShortComplex.map_comp]
  refine ShortComplex.shortExact_of_iso (S.mapNatIso (P.objTensorCompEvalIso n)).symm ?_
  refine .mk' (Module.Flat.rTensor_shortComplex_exact _ S hS.exact) ?_ ?_
  · rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.rTensor_preserves_injective_linearMap _
      ((ModuleCat.mono_iff_injective _).1 hS.mono_f)
  · rw [ModuleCat.epi_iff_surjective]
    exact LinearMap.rTensor_surjective _ ((ModuleCat.epi_iff_surjective _).1 hS.epi_g)

end HomologicalComplex
