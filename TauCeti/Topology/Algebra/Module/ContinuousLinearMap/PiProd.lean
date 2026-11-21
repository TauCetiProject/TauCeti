/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Continuous linear maps on products and Pi types

This file collects supplementary results about continuous linear maps on indexed products `ι → R`
and binary products `M₁ × M₂`.

## Main results

* `ContinuousLinearMap.eq_smul_id_of_unique`: every continuous linear endomorphism of a
  one-coordinate space `ι → R` over a topological commutative semiring `R` with continuous scalar
  multiplication is a scalar multiple of the identity.
* `TauCeti.prodMap_id`: the `prodMap` of two continuous linear identities is the identity.
-/

public section

namespace ContinuousLinearMap

variable {R : Type*} [CommSemiring R] [TopologicalSpace R]

/-- Every continuous linear endomorphism of a one-coordinate space `ι → R` is a scalar multiple of
the identity. -/
theorem eq_smul_id_of_unique {ι : Type*} [Unique ι] [ContinuousConstSMul R R]
    (T : (ι → R) →L[R] (ι → R)) :
    T = T (fun _ ↦ 1) default • ContinuousLinearMap.id R (ι → R) := by
  ext v i
  have hv : v = v default • (fun _ : ι ↦ (1 : R)) := by
    ext j
    simp [Unique.eq_default j]
  conv_lhs => rw [hv]
  simp [Unique.eq_default i, mul_comm]

end ContinuousLinearMap

namespace TauCeti

/-- The product map of two continuous linear identities is the identity on the product. -/
@[simp]
theorem prodMap_id {R M₁ M₂ : Type*} [Semiring R]
    [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R M₁]
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M₂] :
    (ContinuousLinearMap.id R M₁).prodMap (ContinuousLinearMap.id R M₂) =
      ContinuousLinearMap.id R (M₁ × M₂) :=
  rfl

end TauCeti
