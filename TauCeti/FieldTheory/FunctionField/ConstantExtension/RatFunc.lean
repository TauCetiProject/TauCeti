/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic

/-!
# Constant field extensions of the rational function field

For a field extension `k' / k`, the rational function field `k'(X)` is the constant field
extension `k(X) · k'` of `k(X)`, for any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`.
When `k' / k` is finite, the place at infinity of `k'(X)` is the only place over the place at
infinity of `k(X)`.

## Main results

* `TauCeti.constantCompositum_ratFunc_eq_top`: `k'(X)` is the compositum of `k(X)` and `k'`.
* `TauCeti.Place.restrict_ratFunc_eq_infty_iff`: a place of `k'(X)` lies over the place at
  infinity of `k(X)` exactly when it is the place at infinity of `k'(X)`.
-/

public section

namespace TauCeti

variable {k k' : Type*} [Field k] [Field k']

/-- **`k'(X)` is the compositum of `k(X)` with the constants `k'`**, for any `k(X)`-algebra
structure on `k'(X)` sending `X` to `X`. -/
theorem constantCompositum_ratFunc_eq_top [Algebra (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) :
    constantCompositum (RatFunc k) k' (RatFunc k') = ⊤ := by
  set K := constantCompositum (RatFunc k) k' (RatFunc k')
  have hXK : (RatFunc.X : RatFunc k') ∈ K := hX ▸ K.algebraMap_mem RatFunc.X
  -- Every polynomial over `k'` lies in `K`, hence so does every fraction of polynomials.
  have hpoly (p : Polynomial k') : algebraMap (Polynomial k') (RatFunc k') p ∈ K := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact K.add_mem hp hq
    | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_X,
        RatFunc.algebraMap_C]
      exact K.mul_mem (by simpa [RatFunc.algebraMap_eq_C] using
        algebraMap_mem_constantCompositum (RatFunc k) k' (RatFunc k') c) (K.pow_mem hXK n)
  refine eq_top_iff.mpr fun f _ ↦ ?_
  rw [← RatFunc.num_div_denom f]
  exact K.div_mem (hpoly _) (hpoly _)

namespace Place

variable [Algebra k k'] [FiniteDimensional k k']
variable [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]

/-- **The place at infinity of `k'(X)` is the only place over the place at infinity of `k(X)`**,
for a finite extension `k' / k` and any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`. -/
theorem restrict_ratFunc_eq_infty_iff
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X)
    (P' : Place k' (RatFunc k')) :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k)
      (constantCompositum_ratFunc_eq_top hX)
    P'.restrict k (RatFunc k) = infty k ↔ P' = infty k' := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k)
    (constantCompositum_ratFunc_eq_top hX)
  rw [← X_notMem_integers_iff_eq_infty, ← X_notMem_integers_iff_eq_infty,
    mem_integers_restrict_iff, hX]

end Place

end TauCeti
