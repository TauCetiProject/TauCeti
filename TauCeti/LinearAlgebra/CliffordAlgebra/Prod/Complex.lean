/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.BaseChange

/-!
# Graded complex tensor product of real Clifford actions over `WithLp 2`

Let `V₁` and `V₂` be real modules with quadratic forms `Q₁` and `Q₂`, let `Q` be a quadratic form on
`WithLp 2 (V₁ × V₂)` satisfying `Q (v, w) = Q₁ v + Q₂ w`, and let `E` and `F` be complex vector
spaces carrying real algebra maps `ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E` and
`ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F`. Over `R = ℝ` and `A = ℂ`, any complex modules `E`
and `F` carry their restricted real module structures and `IsScalarTower ℝ ℂ` instances
automatically, so `AlgHom.cliffordProdBaseChange` specializes without auxiliary scalar-tower
hypotheses and transports along `WithLp.linearEquiv 2 ℝ (V₁ × V₂)` to an action
`AlgHom.cliffordComplexProdLp` of `CliffordAlgebra Q` on `E ⊗[ℂ] F`. Neither inner products,
orientations, nor finite-dimensionality are required.

## Main definitions

* `AlgHom.cliffordComplexProdLp`: the graded complex tensor-product action of a real Clifford
  algebra over `WithLp 2 (V₁ × V₂)` on `E ⊗[ℂ] F`.

## Main results

* `AlgHom.cliffordComplexProdLp_eq_comp`: factorization of `AlgHom.cliffordComplexProdLp` through
  `AlgHom.cliffordProdBaseChange` and `WithLp.linearEquiv`.
* `AlgHom.cliffordComplexProdLp_ι`, `AlgHom.cliffordComplexProdLp_ι_toLp`: generator evaluation of
  `AlgHom.cliffordComplexProdLp`.
-/

public section

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace AlgHom

variable {V₁ V₂ E F : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
  {Q₁ : QuadraticForm ℝ V₁} {Q₂ : QuadraticForm ℝ V₂}
  {Q : QuadraticForm ℝ (WithLp 2 (V₁ × V₂))}
  (hQ : ∀ x, Q x = Q₁ (WithLp.ofLp x).1 + Q₂ (WithLp.ofLp x).2)
  [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]

/-- **The graded complex tensor product over an `L²` orthogonal direct sum**: acts on `E ⊗[ℂ] F`
for any quadratic form `Q` on `WithLp 2 (V₁ × V₂)` satisfying `Q (v, w) = Q₁ v + Q₂ w`, sending `x`
to `c₁(x.fst) ⊗ 1 + γ ⊗ c₂(x.snd)`. -/
def cliffordComplexProdLp (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E) (γ : Module.End ℂ E)
    (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) :
    CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ (E ⊗[ℂ] F) :=
  (ρ₁.cliffordProdBaseChange γ hγ hγρ ρ₂).comp
    (CliffordAlgebra.map ⟨(WithLp.linearEquiv 2 ℝ (V₁ × V₂)).toLinearMap, fun x ↦ (hQ x).symm⟩)

/-- `AlgHom.cliffordComplexProdLp` factors through `AlgHom.cliffordProdBaseChange` along the
coordinate isometry `WithLp.linearEquiv`. -/
theorem cliffordComplexProdLp_eq_comp (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) :
    ρ₁.cliffordComplexProdLp hQ γ hγ hγρ ρ₂ =
      (ρ₁.cliffordProdBaseChange γ hγ hγρ ρ₂).comp
        (CliffordAlgebra.map
          ⟨(WithLp.linearEquiv 2 ℝ (V₁ × V₂)).toLinearMap, fun x ↦ (hQ x).symm⟩) :=
  (rfl)

/-- On any `x : WithLp 2 (V₁ × V₂)`, `AlgHom.cliffordComplexProdLp` acts by
`c₁(x.fst) ⊗ 1 + γ ⊗ c₂(x.snd)`. -/
@[simp]
theorem cliffordComplexProdLp_ι (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) (x : WithLp 2 (V₁ × V₂)) :
    ρ₁.cliffordComplexProdLp hQ γ hγ hγρ ρ₂ (ι Q x) =
      (ρ₁ (ι Q₁ x.fst)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ x.snd)) := by
  rw [cliffordComplexProdLp, AlgHom.comp_apply, map_apply_ι,
    ← QuadraticMap.Isometry.coe_toLinearMap]
  simp

/-- On `WithLp.toLp 2 (v, w)`, `AlgHom.cliffordComplexProdLp` acts by
`c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. -/
theorem cliffordComplexProdLp_ι_toLp (ρ₁ : CliffordAlgebra Q₁ →ₐ[ℝ] Module.End ℂ E)
    (γ : Module.End ℂ E) (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
    (ρ₂ : CliffordAlgebra Q₂ →ₐ[ℝ] Module.End ℂ F) (v : V₁) (w : V₂) :
    ρ₁.cliffordComplexProdLp hQ γ hγ hγρ ρ₂ (ι Q (WithLp.toLp 2 (v, w))) =
      (ρ₁ (ι Q₁ v)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ w)) := by
  simp

end AlgHom
