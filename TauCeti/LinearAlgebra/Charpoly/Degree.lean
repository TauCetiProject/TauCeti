/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Characteristic polynomials of the zero space and of nonzero spaces

The characteristic polynomial of an endomorphism of a finite free module has degree the rank of
the module. So on the zero module it is `1` and has no roots, while on a nonzero module its image
in any algebraically closed field has a root. These are the degenerate and nondegenerate cases of
statements quantifying over all characteristic roots, such as purity of an endomorphism: the zero
module satisfies them vacuously, and on a nonzero module they constrain at least one root.

## Main results

* `LinearMap.charpoly_eq_one_of_subsingleton`: on the zero module the characteristic polynomial is
  `1`.
* `LinearMap.exists_mem_roots_map_charpoly`: on a nonzero module the characteristic polynomial has
  a root in every algebraically closed field it maps to.
-/

public section

open Module Polynomial

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- The characteristic polynomial of an endomorphism of the zero module is `1`. -/
@[simp]
theorem charpoly_eq_one_of_subsingleton [Subsingleton M] (f : Module.End R M) : f.charpoly = 1 := by
  nontriviality R
  rw [Subsingleton.elim f 1, charpoly_one, finrank_eq_zero_of_subsingleton, pow_zero]

/-- The characteristic polynomial of an endomorphism of a nonzero module has a root in every
algebraically closed field `Ω` it maps to. -/
theorem exists_mem_roots_map_charpoly [Nontrivial M] {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    (φ : R →+* Ω) (f : Module.End R M) : ∃ z, z ∈ (f.charpoly.map φ).roots := by
  have := φ.domain_nontrivial
  have hdeg : 0 < (f.charpoly.map φ).natDegree := by
    rw [f.charpoly_monic.natDegree_map, charpoly_natDegree]
    exact (finrank_pos_iff_of_free R M).mpr inferInstance
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ (natDegree_pos_iff_degree_pos.mp hdeg).ne'
  exact ⟨z, mem_roots'.mpr ⟨(f.charpoly_monic.map φ).ne_zero, hz⟩⟩

end LinearMap
