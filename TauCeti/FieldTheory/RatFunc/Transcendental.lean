/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import Mathlib.FieldTheory.Separable

/-!
# The rational function field as a base for a transcendental element

Let `F` be an extension of a field `k` and let `x ∈ F` be transcendental over `k`. Mathlib's
`RatFunc.algEquivOfTranscendental` identifies `k(X)` with the intermediate field `k⟮x⟯`;
composing with its inclusion into `F` makes `F` an algebra over `k(X)` in which `X` acts as `x`.
This file packages that algebra structure together with the transfers along it of the scalar
tower over `k` and of separability over `k⟮x⟯`.

The structure is not an instance: it depends on the element `x` and on a proof, and distinct
transcendental elements induce distinct `k(X)`-algebra structures on the same `F`. It is meant
to be introduced locally with `letI`.

The nonconstant rational function `X - X⁻¹` is also shown to be transcendental.
Consequently substitution at it loses no polynomial information, including in positive
characteristic.

## Main definitions

* `TauCeti.ratFuncAlgebraOfTranscendental`: the `k(X)`-algebra structure on `F` sending `X`
  to `x`.

## Main results

* `TauCeti.algebraMap_ratFuncAlgebraOfTranscendental_X`: the variable `X` acts as `x`.
* `TauCeti.isScalarTower_ratFuncAlgebraOfTranscendental`: the structure extends the given
  `k`-algebra structure.
* `TauCeti.isSeparable_ratFuncAlgebraOfTranscendental`: separability over `k⟮x⟯` transfers to
  separability over `k(X)`.
* `TauCeti.ratFuncAlgebraOfTranscendental_eq_liftAlgebra`: when `x` is the image of `X` under a
  `k[X]`-algebra structure, the structure is Mathlib's `RatFunc.liftAlgebra`.
* `TauCeti.transcendental_ratFunc_X_sub_inv`: `X - X⁻¹` is transcendental.
-/

public section

noncomputable section

namespace TauCeti

open scoped IntermediateField
open scoped Polynomial

/-- The rational function `X - X⁻¹` is transcendental over the coefficient field,
in every characteristic. -/
theorem transcendental_ratFunc_X_sub_inv (k : Type*) [Field k] :
    Transcendental k (RatFunc.X - RatFunc.X⁻¹ : RatFunc k) := by
  apply RatFunc.transcendental_of_ne_C
  rintro ⟨c, hc⟩
  have he : Polynomial.aeval (RatFunc.X : RatFunc k)
      (Polynomial.X ^ 2 - Polynomial.C c * Polynomial.X - 1) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_mul, map_one]
    rw [RatFunc.algebraMap_eq_C]
    have hx := RatFunc.X_ne_zero (K := k)
    field_simp at hc
    linear_combination hc
  have hp := (transcendental_iff_injective.mp (RatFunc.transcendental_X (K := k)))
    (he.trans (map_zero _).symm)
  have hcoeff := congrArg (fun p : k[X] ↦ p.coeff 2) hp
  norm_num [Polynomial.coeff_one] at hcoeff

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F] {x : F}

/-- The `RatFunc k`-algebra structure on `F` induced by a transcendental element `x`, with
`RatFunc.X` acting as `x`. -/
@[instance_reducible]
noncomputable def ratFuncAlgebraOfTranscendental (hx : Transcendental k x) :
    Algebra (RatFunc k) F :=
  (k⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom).toRingHom.toAlgebra

/-- The structure map of `ratFuncAlgebraOfTranscendental hx` is the embedding through `k(x)`. -/
theorem algebraMap_ratFuncAlgebraOfTranscendental_apply (hx : Transcendental k x)
    (r : RatFunc k) :
    letI := ratFuncAlgebraOfTranscendental hx
    algebraMap (RatFunc k) F r = ((RatFunc.algEquivOfTranscendental x hx r : k⟮x⟯) : F) := by
  let _ := ratFuncAlgebraOfTranscendental hx
  rw [RingHom.algebraMap_toAlgebra]
  rfl

/-- Under `ratFuncAlgebraOfTranscendental hx`, the rational-function variable maps to `x`. -/
@[simp]
theorem algebraMap_ratFuncAlgebraOfTranscendental_X (hx : Transcendental k x) :
    letI := ratFuncAlgebraOfTranscendental hx
    algebraMap (RatFunc k) F RatFunc.X = x := by
  let _ := ratFuncAlgebraOfTranscendental hx
  rw [algebraMap_ratFuncAlgebraOfTranscendental_apply,
    RatFunc.algEquivOfTranscendental_X]

/-- The `RatFunc k`-algebra structure induced by `x` extends the given `k`-algebra structure. -/
theorem isScalarTower_ratFuncAlgebraOfTranscendental (hx : Transcendental k x) :
    letI := ratFuncAlgebraOfTranscendental hx
    IsScalarTower k (RatFunc k) F := by
  let _ := ratFuncAlgebraOfTranscendental hx
  exact .of_algebraMap_eq fun c ↦
    ((k⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom).commutes c).symm

/-- Separability over `k(x)` transfers to the rational-function algebra structure induced by
`x`. -/
theorem isSeparable_ratFuncAlgebraOfTranscendental (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] :
    letI := ratFuncAlgebraOfTranscendental hx
    Algebra.IsSeparable (RatFunc k) F := by
  let _ := ratFuncAlgebraOfTranscendental hx
  -- Transport separability along the identification `k(X) ≃ k(x)`. Its compatibility condition
  -- reads, at an element `r` of `k(x)`, as `algebraMap (RatFunc k) F (e.symm r) = r` for
  -- `e := RatFunc.algEquivOfTranscendental x hx`, which is what the structure map computes.
  refine Algebra.IsSeparable.of_equiv_equiv
    (RatFunc.algEquivOfTranscendental x hx).symm.toRingEquiv (RingEquiv.refl F) ?_
  ext r
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_ratFuncAlgebraOfTranscendental_apply]
  simp

open scoped RatFunc in
/-- When `F` is already a `k[X]`-algebra in which `X` acts as `x`, the structure induced by `x` is
Mathlib's scoped `RatFunc.liftAlgebra`, the extension of the `k[X]`-action to fractions: the two
`k(X)`-algebra structures agree on `k[X]`, hence everywhere. This lets results stated for
`ratFuncAlgebraOfTranscendental` be read in the `RatFunc.liftAlgebra` structure. -/
theorem ratFuncAlgebraOfTranscendental_eq_liftAlgebra [Algebra k[X] F] [IsScalarTower k k[X] F]
    [FaithfulSMul k[X] F] (hx : Transcendental k x) (hX : algebraMap k[X] F Polynomial.X = x) :
    ratFuncAlgebraOfTranscendental hx = RatFunc.liftAlgebra k F := by
  subst hX
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  -- Both structure maps send a polynomial `p` to its image in `F`.
  have h := IsLocalization.ringHom_ext (nonZeroDivisors k[X])
    (j := @algebraMap (RatFunc k) F _ _ (ratFuncAlgebraOfTranscendental hx))
    (k := @algebraMap (RatFunc k) F _ _ (RatFunc.liftAlgebra k F)) <| RingHom.ext fun p ↦ by
      simp only [RingHom.comp_apply, algebraMap_ratFuncAlgebraOfTranscendental_apply,
        RatFunc.algEquivOfTranscendental_algebraMap,
        IntermediateField.AdjoinSimple.coe_aeval_gen_apply,
        ← IsScalarTower.algebraMap_apply k[X] (RatFunc k) F]
      rw [← IsScalarTower.coe_toAlgHom' k k[X] F, Polynomial.aeval_algHom_apply,
        Polynomial.aeval_X_left_apply]
  exact congrArg (· r) h

end TauCeti
