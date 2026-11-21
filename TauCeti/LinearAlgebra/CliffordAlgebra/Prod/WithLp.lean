/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.WithLp

/-!
# Graded tensor decomposition of Clifford algebras on `WithLp` products

When a quadratic form `Q` on `WithLp p (M₁ × M₂)` decomposes as `Q x = Q₁ x.1 + Q₂ x.2`,
extending scalars to an `R`-algebra `A` identifies `CliffordAlgebra (Q.baseChange A)` with the
graded tensor product `evenOdd (Q₁.baseChange A) ᵍ⊗[A] evenOdd (Q₂.baseChange A)` via
`QuadraticMap.IsometryEquiv.baseChangeProd` of `QuadraticMap.IsometryEquiv.withLpProd` and
Mathlib's `CliffordAlgebra.prodEquiv` (`CliffordAlgebra.baseChangeWithLpProdEquiv`).

## Main definitions and results

* `CliffordAlgebra.baseChangeWithLpProdEquiv`: graded-algebra equivalence between
  `CliffordAlgebra (Q.baseChange A)` and
  `evenOdd (Q₁.baseChange A) ᵍ⊗[A] evenOdd (Q₂.baseChange A)`.
* `CliffordAlgebra.baseChangeWithLpProdEquiv_ι_tmul_toLp`: action on
  `ι (a ⊗ₜ WithLp.toLp p (v, w))`.
* `CliffordAlgebra.baseChangeWithLpProdEquiv_symm_ι_tmul_one` and
  `CliffordAlgebra.baseChangeWithLpProdEquiv_symm_one_tmul_ι`: inverse images of single-factor
  generators.
-/

public section

noncomputable section

open scoped ENNReal TensorProduct

namespace CliffordAlgebra

variable {p : ℝ≥0∞} {R : Type*} (A : Type*) [CommRing R] [Invertible (2 : R)]
  [CommRing A] [Algebra R A] {M₁ M₂ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  {Q : QuadraticForm R (WithLp p (M₁ × M₂))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)

include hQ in
/-- After extending scalars to `A`, the Clifford algebra of an orthogonal-sum quadratic form on
`WithLp p (M₁ × M₂)` is isomorphic to the graded tensor product
`evenOdd (Q₁.baseChange A) ᵍ⊗[A] evenOdd (Q₂.baseChange A)`. -/
def baseChangeWithLpProdEquiv :
    CliffordAlgebra (Q.baseChange A) ≃ₐ[A]
      evenOdd (Q₁.baseChange A) ᵍ⊗[A] evenOdd (Q₂.baseChange A) :=
  (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd A)).trans
    (prodEquiv (Q₁.baseChange A) (Q₂.baseChange A))

/-- On a pure tensor `a ⊗ₜ (v, w)`, `baseChangeWithLpProdEquiv` sends `ι (a ⊗ₜ (v, w))` to
`ι (a ⊗ₜ v) ᵍ⊗ 1 + 1 ᵍ⊗ ι (a ⊗ₜ w)`. -/
@[simp]
theorem baseChangeWithLpProdEquiv_ι_tmul_toLp (a : A) (v : M₁) (w : M₂) :
    baseChangeWithLpProdEquiv A hQ (ι (Q.baseChange A) (a ⊗ₜ WithLp.toLp p (v, w))) =
      ι (Q₁.baseChange A) (a ⊗ₜ v) ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ ι (Q₂.baseChange A) (a ⊗ₜ w) := by
  simp [baseChangeWithLpProdEquiv, equivOfIsometry_apply,
    QuadraticMap.IsometryEquiv.baseChangeProd_tmul]

/-- The inverse of `baseChangeWithLpProdEquiv` factors as `toProd` followed by the inverse of
`equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd A)`. -/
theorem baseChangeWithLpProdEquiv_symm_apply
    (x : evenOdd (Q₁.baseChange A) ᵍ⊗[A] evenOdd (Q₂.baseChange A)) :
    (baseChangeWithLpProdEquiv A hQ).symm x =
      (equivOfIsometry ((QuadraticMap.IsometryEquiv.withLpProd hQ).baseChangeProd A)).symm
        (toProd (Q₁.baseChange A) (Q₂.baseChange A) x) := by
  rw [baseChangeWithLpProdEquiv, AlgEquiv.symm_trans_apply]
  rfl

/-- The inverse of `baseChangeWithLpProdEquiv` sends `ι (a ⊗ₜ v) ᵍ⊗ 1` to the left-summand
vector. -/
@[simp]
theorem baseChangeWithLpProdEquiv_symm_ι_tmul_one (a : A) (v : M₁) :
    (baseChangeWithLpProdEquiv A hQ).symm (ι (Q₁.baseChange A) (a ⊗ₜ v) ᵍ⊗ₜ 1) =
      ι (Q.baseChange A) (a ⊗ₜ WithLp.toLp p (v, 0)) :=
  (baseChangeWithLpProdEquiv A hQ).injective (by simp)

/-- The inverse of `baseChangeWithLpProdEquiv` sends `1 ᵍ⊗ ι (a ⊗ₜ w)` to the right-summand
vector. -/
@[simp]
theorem baseChangeWithLpProdEquiv_symm_one_tmul_ι (a : A) (w : M₂) :
    (baseChangeWithLpProdEquiv A hQ).symm (1 ᵍ⊗ₜ ι (Q₂.baseChange A) (a ⊗ₜ w)) =
      ι (Q.baseChange A) (a ⊗ₜ WithLp.toLp p (0, w)) :=
  (baseChangeWithLpProdEquiv A hQ).injective (by simp)

end CliffordAlgebra
