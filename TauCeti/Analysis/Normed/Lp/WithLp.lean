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

Supplies `WithLp.instModuleFree`, `WithLp.finrank_eq`, and the purely algebraic associator
`LinearEquiv.withLpProdAssoc` on iterated binary `WithLp` products.
-/

public section

open scoped ENNReal

namespace WithLp

variable (p : ℝ≥0∞) (K V : Type*) [Semiring K] [AddCommGroup V] [Module K V]

instance instModuleFree [Module.Free K V] : Module.Free K (WithLp p V) :=
  Module.Free.of_equiv (WithLp.linearEquiv p K V).symm

/-- `WithLp` does not change `Module.finrank`.

Not `@[simp]`: collides in `simpNF` with Mathlib's `finrank_euclideanSpace` as well as
`WithLp.finrank_prod` and `WithLp.finrank_complexification`. -/
theorem finrank_eq : Module.finrank K (WithLp p V) = Module.finrank K V :=
  (WithLp.linearEquiv p K V).finrank_eq

end WithLp

namespace LinearEquiv

variable (p : ℝ≥0∞) (K M₁ M₂ M₃ : Type*) [Semiring K]
  [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂] [AddCommGroup M₃] [Module K M₃]

/-- Associativity of iterated `WithLp` binary products as a linear equivalence, with no metric or
seminorm assumptions. -/
def withLpProdAssoc :
    WithLp p (WithLp p (M₁ × M₂) × M₃) ≃ₗ[K] WithLp p (M₁ × WithLp p (M₂ × M₃)) :=
  (WithLp.linearEquiv p K (WithLp p (M₁ × M₂) × M₃)) ≪≫ₗ
    ((WithLp.linearEquiv p K (M₁ × M₂)).prodCongr (.refl K M₃)) ≪≫ₗ
    LinearEquiv.prodAssoc K M₁ M₂ M₃ ≪≫ₗ
    ((LinearEquiv.refl K M₁).prodCongr (WithLp.linearEquiv p K (M₂ × M₃)).symm) ≪≫ₗ
    (WithLp.linearEquiv p K (M₁ × WithLp p (M₂ × M₃))).symm

variable {p K M₁ M₂ M₃}

/-- Forward evaluation of `LinearEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssoc_apply (x : WithLp p (WithLp p (M₁ × M₂) × M₃)) :
    withLpProdAssoc p K M₁ M₂ M₃ x =
      WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).1,
        WithLp.toLp p ((WithLp.ofLp (WithLp.ofLp x).1).2, (WithLp.ofLp x).2)) := (rfl)

/-- Inverse evaluation of `LinearEquiv.withLpProdAssoc`. -/
@[simp]
theorem withLpProdAssoc_symm_apply (x : WithLp p (M₁ × WithLp p (M₂ × M₃))) :
    (withLpProdAssoc p K M₁ M₂ M₃).symm x =
      WithLp.toLp p (WithLp.toLp p ((WithLp.ofLp x).1, (WithLp.ofLp (WithLp.ofLp x).2).1),
        (WithLp.ofLp (WithLp.ofLp x).2).2) := (rfl)

end LinearEquiv
