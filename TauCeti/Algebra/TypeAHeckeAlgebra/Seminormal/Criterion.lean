/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Finite
public import Mathlib.RingTheory.SimpleModule.Basic

import TauCeti.Algebra.TypeAHeckeAlgebra.Seminormal.Split
import TauCeti.Algebra.TypeAHeckeAlgebra.Symmetrizer.Eigenline
import TauCeti.GroupTheory.Perm.Poincare
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# The semisimplicity criterion for the type-A Hecke algebra

Over any field, the type-A Hecke algebra is semisimple exactly when its quantum factorial
at `q²` is nonzero. Necessity uses Tau Ceti's full symmetrizer eigenline obstruction and
the symmetric-group Poincaré product formula. Sufficiency uses Tau Ceti's split seminormal
decomposition and semisimplicity of finite products of full matrix algebras.

## References

* H. H. Andersen, C. Stroppel and D. Tubbenhauer, *Semisimplicity of Hecke and
  (walled) Brauer algebras*, Theorem 5.1, arXiv:1507.07676.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

/-- The type-A Hecke algebra over a field is semisimple if and only if the product of
its quantum integers at `q²` is nonzero. -/
theorem isSemisimpleRing_typeAHeckeAlgebra_iff {K : Type*} [Field K] (q : Kˣ) (n : ℕ) :
    IsSemisimpleRing (TypeAHeckeAlgebra K q n) ↔
      (∏ r ∈ Finset.range n, ∑ j ∈ Finset.range (r + 1), ((q : K) ^ 2) ^ j) ≠ 0 := by
  constructor
  · intro h
    let := h
    have hn := sum_pow_length_ne_zero_of_isSemisimpleRing
      (q := q) (cs := permCoxeterSystem n)
    simp only [pow_mul, sum_pow_permCoxeterSystem_length] at hn
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range] at hn
    simpa only [Nat.add_sub_cancel, Nat.add_comm 1] using hn
  · intro h
    obtain ⟨e⟩ := nonempty_algEquiv_pi_matrix_of_prod_ne_zero q n h
    exact e.symm.toRingEquiv.isSemisimpleRing

end TauCeti.TypeAHeckeAlgebra
