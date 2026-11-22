/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.RingTheory.TensorProduct.Basic
import TauCeti.RingTheory.TensorProduct.FractionRing

/-!
# Rational function fields as fraction rings of tensor products

For any field extension `K / k` (not necessarily algebraic) and any `k`-algebra map
`RatFunc k → RatFunc K` fixing the indeterminate `RatFunc.X`, the rational function field
`RatFunc K` is a fraction field of `RatFunc k ⊗[k] K` along any compatible
`RatFunc k ⊗[k] K`-algebra structure (`TauCeti.isFractionRing_ratFunc_tensorProduct`). This
follows from identifying `k[X] ⊗[k] K` with `K[X]` and transferring the fraction-ring property
along the localization `k[X] → RatFunc k` via
`TauCeti.isFractionRing_tensorProduct_of_isFractionRing_base_tensorProduct`.

In particular, equipping `RatFunc K` with the `RatFunc k ⊗[k] K`-algebra structure that multiplies
the scalar maps from `RatFunc k` and `K` (`TauCeti.ratFuncTensorProductAlgebra`) makes `RatFunc K`
a specified fraction field of `RatFunc k ⊗[k] K`
(`TauCeti.isFractionRing_ratFuncTensorProductAlgebra`).

## Main declarations

* `TauCeti.isFractionRing_ratFunc_tensorProduct`: `RatFunc K` is a fraction ring of
  `RatFunc k ⊗[k] K` whenever `algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X` and the
  `RatFunc k`- and `K`-scalar maps form scalar towers through `RatFunc k ⊗[k] K`.
* `TauCeti.ratFuncTensorProductAlgebra`: the `RatFunc k ⊗[k] K`-algebra structure on `RatFunc K`
  given by multiplying the scalar maps from `RatFunc k` and `K`.
* `TauCeti.algebraMap_ratFuncTensorProductAlgebra_tmul`,
  `TauCeti.isScalarTower_ratFunc_ratFuncTensorProductAlgebra`,
  `TauCeti.isScalarTower_right_ratFuncTensorProductAlgebra`: pure-tensor formula and scalar-tower
  properties of `TauCeti.ratFuncTensorProductAlgebra`.
* `TauCeti.isFractionRing_ratFuncTensorProductAlgebra`: `RatFunc K` is a fraction ring of
  `RatFunc k ⊗[k] K` under `TauCeti.ratFuncTensorProductAlgebra`.
-/

public section

open scoped Polynomial TensorProduct

namespace TauCeti

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  Algebra.TensorProduct.right_isScalarTower

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Auxiliary `k[X] ⊗[k] K`-algebra structure on `RatFunc K` via `k[X] ⊗[k] K ≃ₐ[k] K[X]`, used to
descend `IsFractionRing K[X] (RatFunc K)` to `RatFunc k ⊗[k] K`. -/
@[instance_reducible]
private noncomputable def polynomialTensorRatFuncAlgebra : Algebra (k[X] ⊗[k] K) (RatFunc K) :=
  ((algebraMap K[X] (RatFunc K)).comp
    ((Algebra.TensorProduct.comm k k[X] K).trans (polyEquivTensor k K).symm).toRingHom).toAlgebra

variable [Algebra (RatFunc k) (RatFunc K)] [IsScalarTower k (RatFunc k) (RatFunc K)]

/-- Under `polynomialTensorRatFuncAlgebra`, `algebraMap` sends a pure tensor `p ⊗ₜ c` to the product
of the constant image of `c` and the image of `p` via `RatFunc k`. -/
private theorem algebraMap_polynomialTensorRatFuncAlgebra_tmul
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) (p : k[X]) (c : K) :
    letI := polynomialTensorRatFuncAlgebra (k := k) (K := K)
    algebraMap (k[X] ⊗[k] K) (RatFunc K) (p ⊗ₜ[k] c) =
      algebraMap K (RatFunc K) c *
        algebraMap (RatFunc k) (RatFunc K) (algebraMap k[X] (RatFunc k) p) := by
  let _ := polynomialTensorRatFuncAlgebra (k := k) (K := K)
  have halg : algebraMap (k[X] ⊗[k] K) (RatFunc K) (p ⊗ₜ[k] c) =
      algebraMap K[X] (RatFunc K) ((polyEquivTensor k K).symm (c ⊗ₜ[k] p)) := rfl
  rw [halg, polyEquivTensor_symm_apply_tmul_eq_smul, Algebra.smul_def]
  simp [algebraMap_ratFunc_algebraMap_polynomial hX]

/-- **`RatFunc K` is a fraction field of `RatFunc k ⊗[k] K`**, for any `k`-algebra map
`RatFunc k → RatFunc K` sending `X` to `X` and any compatible `RatFunc k ⊗[k] K`-algebra
structure on `RatFunc K`. Here `K/k` may be transcendental. -/
theorem isFractionRing_ratFunc_tensorProduct
    [Algebra (RatFunc k ⊗[k] K) (RatFunc K)]
    [IsScalarTower (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K)]
    [IsScalarTower K (RatFunc k ⊗[k] K) (RatFunc K)]
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    IsFractionRing (RatFunc k ⊗[k] K) (RatFunc K) := by
  -- Identify `k[X] ⊗[k] K` with the polynomial ring `K[X]`, whose fraction field is `RatFunc K`.
  let e : k[X] ⊗[k] K ≃ₐ[k] K[X] :=
    (Algebra.TensorProduct.comm k k[X] K).trans (polyEquivTensor k K).symm
  have : IsDomain (k[X] ⊗[k] K) := e.toMulEquiv.isDomain
  let _ := polynomialTensorRatFuncAlgebra (k := k) (K := K)
  have : IsFractionRing (k[X] ⊗[k] K) (RatFunc K) :=
    _root_.IsFractionRing.of_ringEquiv_left e.toRingEquiv fun _ ↦ rfl
  refine isFractionRing_tensorProduct_of_isFractionRing_base_tensorProduct
    (k := k) (A := k[X]) (F := RatFunc k) (K := K) (Q := RatFunc K) fun p c ↦ ?_
  rw [algebraMap_polynomialTensorRatFuncAlgebra_tmul hX, algebraMap_tensorProduct_tmul, mul_comm]

/-- The `RatFunc k ⊗[k] K`-algebra structure on `RatFunc K` given by multiplying the scalar maps
from `RatFunc k` and `K`. -/
@[instance_reducible]
noncomputable def ratFuncTensorProductAlgebra : Algebra (RatFunc k ⊗[k] K) (RatFunc K) :=
  (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K))
    (IsScalarTower.toAlgHom k K (RatFunc K))).toRingHom.toAlgebra

/-- Under `TauCeti.ratFuncTensorProductAlgebra`, `algebraMap` sends a pure tensor `f ⊗ₜ c` to the
product of the two scalar images in `RatFunc K`. -/
theorem algebraMap_ratFuncTensorProductAlgebra_tmul (f : RatFunc k) (c : K) :
    letI := ratFuncTensorProductAlgebra (k := k) (K := K)
    algebraMap (RatFunc k ⊗[k] K) (RatFunc K) (f ⊗ₜ[k] c) =
      algebraMap (RatFunc k) (RatFunc K) f * algebraMap K (RatFunc K) c := by
  let _ := ratFuncTensorProductAlgebra (k := k) (K := K)
  have h : algebraMap (RatFunc k ⊗[k] K) (RatFunc K) =
      (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k (RatFunc k) (RatFunc K))
        (IsScalarTower.toAlgHom k K (RatFunc K))).toRingHom := rfl
  simp [h]

/-- Left scalar tower for `TauCeti.ratFuncTensorProductAlgebra`. -/
theorem isScalarTower_ratFunc_ratFuncTensorProductAlgebra :
    letI := ratFuncTensorProductAlgebra (k := k) (K := K)
    IsScalarTower (RatFunc k) (RatFunc k ⊗[k] K) (RatFunc K) := by
  let _ := ratFuncTensorProductAlgebra (k := k) (K := K)
  exact .of_algebraMap_eq fun _ ↦ by simp [algebraMap_ratFuncTensorProductAlgebra_tmul]

/-- Right scalar tower for `TauCeti.ratFuncTensorProductAlgebra`. -/
theorem isScalarTower_right_ratFuncTensorProductAlgebra :
    letI := ratFuncTensorProductAlgebra (k := k) (K := K)
    IsScalarTower K (RatFunc k ⊗[k] K) (RatFunc K) := by
  let _ := ratFuncTensorProductAlgebra (k := k) (K := K)
  exact .of_algebraMap_eq fun _ ↦ by
    simp [Algebra.TensorProduct.right_algebraMap_apply,
      algebraMap_ratFuncTensorProductAlgebra_tmul]

/-- **`RatFunc K` is a fraction field of `RatFunc k ⊗[k] K`** under
`TauCeti.ratFuncTensorProductAlgebra` whenever `algebraMap (RatFunc k) (RatFunc K)` fixes `X`. -/
theorem isFractionRing_ratFuncTensorProductAlgebra
    (hX : algebraMap (RatFunc k) (RatFunc K) RatFunc.X = RatFunc.X) :
    letI := ratFuncTensorProductAlgebra (k := k) (K := K)
    IsFractionRing (RatFunc k ⊗[k] K) (RatFunc K) := by
  let _ := ratFuncTensorProductAlgebra (k := k) (K := K)
  have := isScalarTower_ratFunc_ratFuncTensorProductAlgebra (k := k) (K := K)
  have := isScalarTower_right_ratFuncTensorProductAlgebra (k := k) (K := K)
  exact isFractionRing_ratFunc_tensorProduct hX

end TauCeti
