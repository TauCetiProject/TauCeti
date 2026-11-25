/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.Ring

/-!
# Bilinear forms on finitely supported functions

Coordinate expansions for bilinear forms on `I →₀ R`, independent of any particular algebraic
application of those forms.

## Main results

* `LinearMap.BilinForm.IsAlt.apply_eq_erase`: an alternating form is determined by its values on
  the coefficient-erased arguments and its cross terms with a coordinate vector.
-/

public section

namespace LinearMap.BilinForm

variable {I : Type*}

/-- An alternating form on `I →₀ R`, expanded along `a = a_k e_k + a°` and `b = b_k e_k + b°`
with `a° = a - a_k e_k`: `Λ'(a, b) = Λ'(a°, b°) + a_k * Λ'(e_k, b°) - b_k * Λ'(e_k, a°)`. -/
theorem IsAlt.apply_eq_erase {R : Type*} [CommRing R] {Λ' : LinearMap.BilinForm R (I →₀ R)}
    (hΛ' : Λ'.IsAlt) (k : I) (a b : I →₀ R) :
    Λ' a b = Λ' (a.erase k) (b.erase k) + a k * Λ' (Finsupp.single k 1) (b.erase k) -
      b k * Λ' (Finsupp.single k 1) (a.erase k) := by
  have hs (n : R) : Finsupp.single k n = n • Finsupp.single k (1 : R) := by
    rw [Finsupp.smul_single_one]
  conv_lhs => rw [← Finsupp.single_add_erase k a, ← Finsupp.single_add_erase k b,
    hs (a k), hs (b k)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hΛ'.self_eq_zero, ← hΛ'.neg_eq (a.erase k)]
  ring

end LinearMap.BilinForm
