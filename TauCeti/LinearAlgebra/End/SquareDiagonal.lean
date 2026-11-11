/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Semisimple
import Mathlib.FieldTheory.Separable
import TauCeti.Algebra.Polynomial.RingDivision

/-!
# Endomorphisms with diagonal square

Let `f` be an endomorphism of a vector space over a field of characteristic not two, and `b` a
finite basis on which `f²` acts diagonally, `f (f (bᵢ)) = dᵢ bᵢ`, with `f (bᵢ) = 0` whenever
`dᵢ = 0`. Then `f` is semisimple: it is killed by the squarefree polynomial `(∏ₜ (X² - t)) X`, the
product running over the nonzero values `t` of `d`.

For example, a rotation generator `(x, y) ↦ (-c y, c x)` has square `-c²` and a hyperbolic generator
`(x, y) ↦ (c x, -c y)` has square `c²`; this is how the elliptic and hyperbolic blocks of
Williamson's classification are shown to have semisimple regular elements.

## Main results

* `Module.End.isSemisimple_of_apply_apply_basis_eq_smul`: an endomorphism whose square acts
  diagonally on a finite basis, and which kills the basis vectors where the square does, is
  semisimple.
-/

public section

open Polynomial

namespace Module.End

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite ι]

/-- An endomorphism `f` whose square acts diagonally on a finite basis, `f (f (bᵢ)) = dᵢ bᵢ`, and
which kills `bᵢ` whenever `dᵢ = 0`, is semisimple in characteristic not two: it is killed by the
squarefree polynomial `(∏ₜ (X² - t)) X` over the nonzero values `t` of `d`. -/
theorem isSemisimple_of_apply_apply_basis_eq_smul (h2 : (2 : K) ≠ 0) {f : End K V}
    (b : Basis ι K V) (d : ι → K) (hd : ∀ i, f (f (b i)) = d i • b i)
    (h0 : ∀ i, d i = 0 → f (b i) = 0) : f.IsSemisimple := by
  classical
  have := Fintype.ofFinite ι
  set S := (Finset.univ.image d).filter (· ≠ 0)
  refine isSemisimple_of_squarefree_aeval_eq_zero (p := (∏ t ∈ S, (X ^ 2 - C t)) * X) ?_ ?_
  · refine (Separable.mul (separable_prod' (fun s _ t _ hst ↦ ?_) fun t ht ↦ ?_) separable_X
      (IsCoprime.prod_left fun t ht ↦ ?_)).squarefree
    · exact isCoprime_sub_C_of_isUnit_sub _ (sub_ne_zero.2 hst).isUnit
    · exact separable_X_pow_sub_C _ (by exact_mod_cast h2) (Finset.mem_filter.1 ht).2
    · refine ⟨-C t⁻¹, C t⁻¹ * X, ?_⟩
      have h : C t⁻¹ * C t = (1 : K[X]) := by
        rw [← C_mul, inv_mul_cancel₀ (Finset.mem_filter.1 ht).2, C_1]
      linear_combination h
  · -- A basis vector `bᵢ` is killed by `X` if `dᵢ = 0` and by the factor `X² - dᵢ` otherwise,
    -- and the factors commute.
    refine b.ext fun i ↦ ?_
    rw [LinearMap.zero_apply]
    by_cases hi : d i = 0
    · rw [map_mul, mul_apply_eq_comp, aeval_X, h0 i hi, map_zero]
    have hS : d i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hi⟩
    rw [← Finset.prod_erase_mul _ _ hS, mul_right_comm, map_mul, mul_apply_eq_comp]
    have hi : aeval f (X ^ 2 - C (d i)) (b i) = 0 := by
      rw [map_sub, map_pow, aeval_X, aeval_C, sq, LinearMap.sub_apply, mul_apply_eq_comp, hd,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self, sub_self]
    rw [hi, map_zero]

end Module.End
