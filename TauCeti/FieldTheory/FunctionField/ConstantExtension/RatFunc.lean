/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Extension
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Constant field extensions of the rational function field

For a field extension `k' / k`, the rational function field `k'(X)` is the constant field
extension `k(X) · k'` of `k(X)`, for any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`.
A polynomial over `k` is carried to the same polynomial over `k'`; in particular, in
characteristic `p`, `X ^ p - a` becomes `(X - b) ^ p` when `b ^ p = a`. When `k' / k` is finite,
the place at infinity of `k'(X)` is the only place over the place at infinity of `k(X)`.

## Main results

* `TauCeti.constantCompositum_eq_top_of_X_mem`: a compositum `F · k'` inside `k'(X)` containing
  `X` is all of `k'(X)`.
* `TauCeti.constantCompositum_ratFunc_eq_top`: `k'(X)` is the compositum of `k(X)` and `k'`.
* `TauCeti.algebraMap_ratFunc_algebraMap_polynomial`: the image in `k'(X)` of a polynomial over
  `k` is that polynomial with its coefficients mapped into `k'`.
* `TauCeti.algebraMap_ratFunc_algebraMap_X_pow_sub_C`: in characteristic `p`, `X ^ p - a` becomes
  `(X - b) ^ p` in `k'(X)` when `b ^ p = a`.
* `TauCeti.Place.restrict_ratFunc_eq_infty_iff`: a place of `k'(X)` lies over the place at
  infinity of `k(X)` exactly when it is the place at infinity of `k'(X)`.
-/

public section

namespace TauCeti

variable {k k' : Type*} [Field k] [Field k']

/-- **A compositum with `k'` containing `X` is all of `k'(X)`**: for any field `F` inside `k'(X)`,
if `X` lies in `F · k'`, then `F · k' = k'(X)`. -/
theorem constantCompositum_eq_top_of_X_mem {F : Type*} [Field F] [Algebra F (RatFunc k')]
    (hX : (RatFunc.X : RatFunc k') ∈ constantCompositum F k' (RatFunc k')) :
    constantCompositum F k' (RatFunc k') = ⊤ := by
  set K := constantCompositum F k' (RatFunc k')
  -- `K` contains the constants `k'`, so it is an intermediate field of `k'(X) / k'`; it contains
  -- `X`, which generates `k'(X)` over `k'`.
  let E : IntermediateField k' (RatFunc k') :=
    { K.toSubfield with
      algebraMap_mem' := algebraMap_mem_constantCompositum F k' (RatFunc k') }
  have hE : E = ⊤ := eq_top_iff.mpr <|
    RatFunc.adjoin_X.symm.le.trans (IntermediateField.adjoin_simple_le_iff.mpr hX)
  exact eq_top_iff.mpr fun f _ ↦ (hE ▸ IntermediateField.mem_top : f ∈ E)

/-- **`k'(X)` is the compositum of `k(X)` with the constants `k'`**, for any `k(X)`-algebra
structure on `k'(X)` sending `X` to `X`. -/
theorem constantCompositum_ratFunc_eq_top [Algebra (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) :
    constantCompositum (RatFunc k) k' (RatFunc k') = ⊤ :=
  constantCompositum_eq_top_of_X_mem (hX ▸ IntermediateField.algebraMap_mem _ RatFunc.X)

open Polynomial in
/-- **The image in `k'(X)` of a polynomial over `k` is that polynomial with its coefficients mapped
into `k'`**, for any `k(X)`-algebra structure on `k'(X)` over `k` sending `X` to `X`. -/
theorem algebraMap_ratFunc_algebraMap_polynomial [Algebra k k']
    [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) (q : k[X]) :
    algebraMap (RatFunc k) (RatFunc k') (algebraMap k[X] (RatFunc k) q) =
      algebraMap k'[X] (RatFunc k') (q.map (algebraMap k k')) := by
  have h := map_aeval_eq_aeval_map (φ := algebraMap k k')
    (ψ := algebraMap (RatFunc k) (RatFunc k')) ?_ q RatFunc.X
  · rwa [RatFunc.aeval_X_left_eq_algebraMap, hX, RatFunc.aeval_X_left_eq_algebraMap] at h
  · rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

open Polynomial in
/-- **`X ^ p - a = (X - b) ^ p` in `k'(X)`** for `b ∈ k'` with `b ^ p = a`, in characteristic `p`,
for any `k(X)`-algebra structure on `k'(X)` over `k` sending `X` to `X`. -/
theorem algebraMap_ratFunc_algebraMap_X_pow_sub_C [Algebra k k']
    [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) {p : ℕ} [Fact p.Prime]
    [CharP k p] {a : k} {b : k'} (hb : b ^ p = algebraMap k k' a) :
    algebraMap (RatFunc k) (RatFunc k') (algebraMap k[X] (RatFunc k) (X ^ p - C a)) =
      algebraMap k'[X] (RatFunc k') (X - C b) ^ p := by
  have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
  rw [algebraMap_ratFunc_algebraMap_polynomial hX, Polynomial.map_sub, Polynomial.map_pow, map_X,
    map_C, ← hb, ← map_pow, sub_pow_char, ← C_pow]

namespace Place

variable [Algebra k k'] [FiniteDimensional k k']
variable [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]

/-- **The place at infinity of `k'(X)` is the only place over the place at infinity of `k(X)`**,
for a finite extension `k' / k` and any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`. -/
@[simp]
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
