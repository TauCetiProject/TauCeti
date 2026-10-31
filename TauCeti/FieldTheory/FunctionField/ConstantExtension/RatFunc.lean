/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Constant field extensions of the rational function field

For a field extension `k' / k`, the rational function field `k'(X)` is the constant field
extension `k(X) · k'` of `k(X)`, for any `k(X)`-algebra structure on `k'(X)` sending `X` to `X`.
A polynomial over `k` is carried to the same polynomial over `k'`. When `k' / k` is finite, the
place at infinity of `k'(X)` is the only place over the place at infinity of `k(X)`. In any
algebraic extension of `k(X)`, a place lies over the place of an irreducible polynomial exactly
when that polynomial vanishes there.

## Main results

* `TauCeti.constantCompositum_eq_top_of_X_mem`: a compositum `F · k'` inside `k'(X)` containing
  `X` is all of `k'(X)`.
* `TauCeti.constantCompositum_ratFunc_eq_top`: `k'(X)` is the compositum of `k(X)` and `k'`.
* `TauCeti.algebraMap_ratFunc_algebraMap_polynomial`: the image in `k'(X)` of a polynomial over
  `k` is that polynomial with its coefficients mapped into `k'`.
* `TauCeti.Place.restrict_eq_adicOfIrreducible_iff`: a place of an algebraic extension of `k(X)`
  lies over the place of an irreducible polynomial `q` exactly when `q` vanishes there.
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
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X, hX,
      Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, map_pow, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C,
      ← IsScalarTower.algebraMap_apply, ← RatFunc.algebraMap_eq_C,
      ← IsScalarTower.algebraMap_apply k k' (RatFunc k')]

namespace Place

section Restrict

variable {F' : Type*} [Field F'] [Algebra k k'] [Algebra k' F'] [Algebra (RatFunc k) F']
variable [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k (RatFunc k) F']
variable [Algebra.IsIntegral (RatFunc k) F']

open Polynomial in
/-- **A place lies over the place of an irreducible polynomial `q` of `k(X)` exactly when `q`
vanishes there**, in any algebraic extension of `k(X)`. -/
theorem restrict_eq_adicOfIrreducible_iff {q : k[X]} (hq : Irreducible q) (Q : Place k' F') :
    Q.restrict k (RatFunc k) = adicOfIrreducible hq ↔
      0 < Q.ord (algebraMap (RatFunc k) F' (algebraMap k[X] (RatFunc k) q)) := by
  rw [← ord_algebraMap_pos_iff hq, ord_algebraMap_restrict k (RatFunc k) Q]
  have he : (0 : ℤ) < ramificationIdx (RatFunc k) Q := by
    exact_mod_cast ramificationIdx_pos (RatFunc k) Q
  exact ⟨fun h ↦ mul_pos he h, fun h ↦ pos_of_mul_pos_right h he.le⟩

end Restrict

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
