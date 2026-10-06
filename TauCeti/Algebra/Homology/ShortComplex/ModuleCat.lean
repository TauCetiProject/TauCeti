/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finiteness and dimension of homology of short complexes of modules

For a short complex `X₁ ⟶ X₂ ⟶ X₃` of modules, its homology is the kernel of the second map
modulo the range of the first.  This file records two consequences of that description:

* over a ring for which the middle module is noetherian, the homology is finitely generated;
* over a division ring, when the middle term is finite-dimensional, the dimension of the homology
  plus the dimension of the range of the first map is the dimension of the kernel of the second.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.1 and 1.3.
-/

public section

open CategoryTheory Limits Module

universe u v

namespace CategoryTheory.ShortComplex

/-- The homology of a short complex of modules with noetherian middle term is finitely generated. -/
theorem finite_homology {k : Type u} [Ring k] (S : ShortComplex (ModuleCat.{v} k))
    [IsNoetherian k S.X₂] : Module.Finite k S.homology :=
  -- The homology object of `S.moduleCatLeftHomologyData` is this quotient by construction.
  have : Module.Finite k S.moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles))
  .equiv S.moduleCatHomologyIso.toLinearEquiv.symm

variable {k : Type u} [DivisionRing k]

/-- The homology of a short complex `X₁ ⟶ X₂ ⟶ X₃` of vector spaces with `X₂` finite-dimensional
has dimension `dim ker g - dim im f`. -/
theorem finrank_homology_add_finrank_range_f (S : ShortComplex (ModuleCat.{v} k))
    [Module.Finite k S.X₂] :
    finrank k S.homology + finrank k (LinearMap.range S.f.hom) =
      finrank k (LinearMap.ker S.g.hom) := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq, moduleCatLeftHomologyData_H,
    ← Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)]
  congr 1
  rw [← Submodule.finrank_map_subtype_eq, ← LinearMap.range_comp]
  -- `S.moduleCatToCycles` is the corestriction of `S.f` to `ker S.g`, so composing it with the
  -- inclusion of `ker S.g` gives `S.f` back by definition; rewriting with
  -- `LinearMap.subtype_comp_codRestrict` fails because Mathlib's corestriction proof is only
  -- well-typed up to unfolding the concrete-category coercions.
  rfl

end CategoryTheory.ShortComplex
