/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.WithLp
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Linear-algebraic structure on the `WithLp` type synonym

Mathlib transfers `Module.Finite` across `WithLp.linearEquiv` (`WithLp.instModuleFinite`) and lifts
semilinear equivalences via `LinearEquiv.withLpCongr`. This file supplies the companion free-module
instance, the `finrank` identity, and the purely algebraic associator
`LinearEquiv.withLpProdAssoc` underlying `LinearIsometryEquiv.withLpProdAssoc`.

## Main definitions and results

* `WithLp.instModuleFree`: `WithLp p V` is free over `K` whenever `V` is.
* `WithLp.finrank_eq`: `Module.finrank K (WithLp p V) = Module.finrank K V`.
* `LinearEquiv.withLpProdAssoc`: reassociating `WithLp p (WithLp p (M₁ × M₂) × M₃)` to
  `WithLp p (M₁ × WithLp p (M₂ × M₃))` as a `K`-linear equivalence, with no metric or seminorm
  assumptions.
-/

public section

open scoped ENNReal

namespace WithLp

variable (p : ℝ≥0∞) (K V : Type*) [Semiring K] [AddCommGroup V] [Module K V]

instance instModuleFree [Module.Free K V] : Module.Free K (WithLp p V) :=
  Module.Free.of_equiv (WithLp.linearEquiv p K V).symm

/-- `WithLp` does not change `Module.finrank`. -/
@[simp]
theorem finrank_eq : Module.finrank K (WithLp p V) = Module.finrank K V :=
  (WithLp.linearEquiv p K V).finrank_eq

end WithLp

namespace LinearEquiv

variable (p : ℝ≥0∞) (K M₁ M₂ M₃ : Type*) [Semiring K]
  [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂] [AddCommGroup M₃] [Module K M₃]

/-- Associativity of iterated `WithLp` binary products as a linear equivalence, with no metric or
seminorm assumptions. When the factors are seminormed modules and `1 ≤ p`, this is the underlying
linear equivalence of `LinearIsometryEquiv.withLpProdAssoc`. -/
def withLpProdAssoc :
    WithLp p (WithLp p (M₁ × M₂) × M₃) ≃ₗ[K] WithLp p (M₁ × WithLp p (M₂ × M₃)) where
  toFun x := .toLp p ((WithLp.ofLp (WithLp.ofLp x).1).1,
    .toLp p ((WithLp.ofLp (WithLp.ofLp x).1).2, (WithLp.ofLp x).2))
  invFun x := .toLp p (.toLp p ((WithLp.ofLp x).1, (WithLp.ofLp (WithLp.ofLp x).2).1),
    (WithLp.ofLp (WithLp.ofLp x).2).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {p K M₁ M₂ M₃}

/-- Forward evaluation of `LinearEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssoc_apply (x : WithLp p (WithLp p (M₁ × M₂) × M₃)) :
    withLpProdAssoc p K M₁ M₂ M₃ x =
      WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).1,
        WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).2, (WithLp.ofLp x).2)) :=
  (rfl)

/-- Inverse evaluation of `LinearEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssoc_symm_apply (x : WithLp p (M₁ × WithLp p (M₂ × M₃))) :
    (withLpProdAssoc p K M₁ M₂ M₃).symm x =
      WithLp.toLp p (WithLp.toLp p ((WithLp.ofLp x).1, (WithLp.ofLp (WithLp.ofLp x).2).1),
        (WithLp.ofLp (WithLp.ofLp x).2).2) :=
  (rfl)

end LinearEquiv
