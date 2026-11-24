/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Algebra.Module.LinearMap.Polynomial
import Mathlib.Algebra.CharP.Lemmas

/-!
# Examples of determinant polynomials

These examples compute the determinant polynomial `LinearMap.detPoly` in the basic cases.

* A ring `R` acting by scalars on a free module of rank `r`, with the basis `1` of `R`, has
  determinant polynomial `X ^ r`.
* The Gaussian integers `ℤ[i]` with basis `(1, i)`, acting on `ℂ` with `i` acting by `√−1` or by
  `−√−1`, have determinant polynomials `X₀ + √−1 X₁` and `X₀ − √−1 X₁`. Here the action of
  `ℤ[i] ⊗ ℂ` is written as the linear family on `ℂ²` in which the coordinate vectors act by `1`
  and by `±√−1`.
* The value at the coordinates of `-x` is the value at `0` of the characteristic polynomial of
  `x`, with no extra sign: for `x = 1` acting on a line both sides are `-1`.
* Over a field `k` of characteristic `3`, the two linear families on `k²` acting on `k³`, in which
  the coordinate vectors act by `1` and `t`, and by `1` and `-t`, for `t ≠ 0`, have the same
  (zero) trace maps but different determinant polynomials `(X₀ + t X₁)³` and `(X₀ - t X₁)³`.
  When `t ^ 2 = -1` (as for `t` a square root of `-1` in `𝔽₉`), these are the two actions of
  `ℤ[i] ⊗ k` in the basis `(1, i)` in which `i` acts by `t` and by `-t`. Traces do not determine a
  module in positive characteristic, while determinant polynomials can tell these two apart.
-/

public section

open Module MvPolynomial

namespace TauCeti.DetPolyExamples

/-- A commutative ring acting on a free module of rank `r` by scalars has determinant polynomial
`X ^ r` with respect to the basis `1`. -/
theorem detPoly_lsmul (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] :
    (LinearMap.lsmul R M).detPoly (Basis.singleton Unit R) = X () ^ finrank R M := by
  have : LinearMap.lsmul R M = (LinearMap.id : R →ₗ[R] R).smulRight LinearMap.id := by
    ext; simp
  rw [this, LinearMap.detPoly_smulRight_id]
  simp

/-- The linear family on `ℂ²` in which the first coordinate vector acts on `ℂ` by `1` and the
second by `s`. When `s ^ 2 = -1`, that is for `s = ±√−1`, it is the action of `ℤ[i] ⊗ ℂ`, in the
basis `(1, i)`, for which `i` acts by `s`. -/
noncomputable def gaussianAction (s : ℂ) : (Fin 2 → ℂ) →ₗ[ℂ] Module.End ℂ ℂ :=
  (LinearMap.proj (0 : Fin 2) + s • LinearMap.proj (1 : Fin 2) : (Fin 2 → ℂ) →ₗ[ℂ] ℂ).smulRight
    LinearMap.id

/-- The linear family on `K²` in which the first coordinate vector acts on `M` by `1` and the
second by `s` has determinant polynomial `(X₀ + s X₁) ^ finrank K M`. -/
theorem detPoly_proj_add_smul_proj_smulRight_id (K M : Type*) [CommRing K] [AddCommGroup M]
    [Module K M] [Module.Free K M] [Module.Finite K M] (s : K) :
    LinearMap.detPoly ((LinearMap.proj (0 : Fin 2) + s • LinearMap.proj (1 : Fin 2) :
        (Fin 2 → K) →ₗ[K] K).smulRight (LinearMap.id : Module.End K M)) (Pi.basisFun K (Fin 2)) =
      (X 0 + C s * X 1) ^ finrank K M := by
  rw [LinearMap.detPoly_smulRight_id]
  simp [Fin.sum_univ_two]

/-- With the second coordinate vector acting on `ℂ` by `s`, the determinant polynomial is the
linear form `X₀ + s X₁`. -/
theorem detPoly_gaussianAction (s : ℂ) :
    (gaussianAction s).detPoly (Pi.basisFun ℂ (Fin 2)) = X 0 + C s * X 1 := by
  rw [gaussianAction, detPoly_proj_add_smul_proj_smulRight_id]
  simp

/-- With `i` acting by `√−1`, the determinant polynomial is `X₀ + √−1 X₁`. -/
theorem detPoly_gaussianAction_I :
    (gaussianAction Complex.I).detPoly (Pi.basisFun ℂ (Fin 2)) = X 0 + C Complex.I * X 1 :=
  detPoly_gaussianAction _

/-- With `i` acting by `−√−1`, the determinant polynomial is `X₀ − √−1 X₁`. -/
theorem detPoly_gaussianAction_neg_I :
    (gaussianAction (-Complex.I)).detPoly (Pi.basisFun ℂ (Fin 2)) =
      X 0 - C Complex.I * X 1 := by
  rw [detPoly_gaussianAction, map_neg, neg_mul, ← sub_eq_add_neg]

/-- For `x = 1` acting by scalars on the line `ℚ`, the determinant polynomial at the coordinates
of `-1` and the characteristic polynomial of `1` at `0` are both `-1`. -/
theorem eval_detPoly_neg_one_lsmul :
    eval ((Basis.singleton Unit ℚ).repr (-1)) ((LinearMap.lsmul ℚ ℚ).detPoly
        (Basis.singleton Unit ℚ)) = -1 ∧
      ((LinearMap.lsmul ℚ ℚ) 1).charpoly.eval 0 = -1 := by
  refine ⟨by simp [detPoly_lsmul], ?_⟩
  rw [← LinearMap.eval_detPoly_neg_eq_charpoly_eval_zero _ (Basis.singleton Unit ℚ)]
  simp [detPoly_lsmul]

section CharThree

variable {k : Type*} [Field k] [CharP k 3]

/-- The linear family on `k²` in which the first coordinate vector acts on `k³` by `1` and the
second by `t`. When `t ^ 2 = -1`, it is the action of `ℤ[i] ⊗ k`, in the basis `(1, i)`, for which
`i` acts by `t`. -/
noncomputable def charThreeAction (t : k) : (Fin 2 → k) →ₗ[k] Module.End k (Fin 3 → k) :=
  (LinearMap.proj (0 : Fin 2) + t • LinearMap.proj (1 : Fin 2) : (Fin 2 → k) →ₗ[k] k).smulRight
    LinearMap.id

/-- In characteristic `3`, the families in which the second coordinate vector acts on `k³` by `t`
and by `-t` have the same trace maps, both zero. -/
theorem trace_charThreeAction (t : k) (x : Fin 2 → k) :
    LinearMap.trace k _ (charThreeAction t x) = 0 := by
  have h3 : (3 : k) = 0 := CharP.cast_eq_zero k 3
  simp [charThreeAction, LinearMap.trace_id, h3]

omit [CharP k 3] in
/-- The family in which the second coordinate vector acts on `k³` by `t` has determinant polynomial
`(X₀ + t X₁)³`. -/
theorem detPoly_charThreeAction (t : k) :
    (charThreeAction t).detPoly (Pi.basisFun k (Fin 2)) = (X 0 + C t * X 1) ^ 3 := by
  rw [charThreeAction, detPoly_proj_add_smul_proj_smulRight_id, Module.finrank_fin_fun]

/-- In characteristic `3`, for `t ≠ 0`, the families in which the second coordinate vector acts on
`k³` by `t` and by `-t` have different determinant polynomials, `(X₀ + t X₁)³` and
`(X₀ - t X₁)³`. -/
theorem detPoly_charThreeAction_ne {t : k} (ht : t ≠ 0) :
    (charThreeAction t).detPoly (Pi.basisFun k (Fin 2)) ≠
      (charThreeAction (-t)).detPoly (Pi.basisFun k (Fin 2)) := by
  intro h
  have h2 : (2 : k) ≠ 0 := by
    intro h2
    have := (CharP.cast_eq_zero_iff k 3 2).mp (by exact_mod_cast h2)
    omega
  rw [detPoly_charThreeAction, detPoly_charThreeAction] at h
  have h3 : t ^ 3 = (-t) ^ 3 := by simpa using congrArg (eval ![0, 1]) h
  have h' : t ^ 3 * 2 = 0 := by linear_combination h3
  simp [h2, ht] at h'

end CharThree

end TauCeti.DetPolyExamples
