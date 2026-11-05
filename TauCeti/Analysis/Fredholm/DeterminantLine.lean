/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.LinearAlgebra.Determinant.Exact

/-!
# The determinant line of a Fredholm operator

A Fredholm operator `T : E →L[𝕜] F` has finite-dimensional kernel and cokernel, so its
determinant line `det (ker T) ⊗ (det (F ⧸ range T))^*` (`LinearMap.detLine`) is a line over `𝕜`.
Orientations of moduli spaces in Morse and Floer theory are orientations of these lines for
the linearized operators.

Kernel and cokernel jump as the operator varies, so the determinant lines of a family are
compared through a **stabilization**. Adjoin finitely many directions `D₂ : Λ →L[𝕜] F`, with `Λ`
finite-dimensional, so that `D₁.coprod D₂ : E × Λ →L[𝕜] F` is onto. The stabilized operator has
no cokernel, and it stays onto, with kernel of the same dimension, under small perturbations of
`D₁`. The exact sequence
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → 0` of
`TauCeti.Analysis.Fredholm.Parametric` then identifies the determinant line of `D₁` with
`det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*` (`ContinuousLinearMap.detLineCoprodEquiv`). This is the
fibrewise comparison through which the determinant lines of a continuous family of Fredholm
operators form a line bundle.

## Main results

* `ContinuousLinearMap.IsFredholm.finrank_detLine`: the determinant line of a Fredholm operator is
  one-dimensional.
* `ContinuousLinearMap.detLineCoprodEquiv`: for a surjective stabilization `D₁.coprod D₂` by a
  finite-dimensional space `Λ`, the isomorphism
  `det (ker (D₁.coprod D₂)) ⊗ (det Λ)^* ≃ det (ker D₁) ⊗ (det (F ⧸ range D₁))^*`.
* `ContinuousLinearMap.detLineCoprodEquiv_tmul`: its value on exterior products.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The determinant line `det (ker T) ⊗ (det (F ⧸ range T))^*` of a Fredholm operator is
one-dimensional. -/
theorem IsFredholm.finrank_detLine {T : E →L[𝕜] F} (hT : IsFredholm T) :
    finrank 𝕜 (T : E →ₗ[𝕜] F).detLine = 1 :=
  have := hT.finite_ker
  have := hT.finite_coker
  LinearMap.finrank_detLine _

section Stabilization

variable {𝕜 E Λ F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F}
  [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ]

variable (D₁ D₂) in
/-- **The determinant line of a stabilized operator.** If adjoining the finite-dimensional
directions `D₂ : Λ →L[𝕜] F` makes `D₁.coprod D₂ : E × Λ →L[𝕜] F` surjective and `D₁` has
finite-dimensional kernel, the exact sequence
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → 0` identifies
`det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*` with the determinant line
`det (ker D₁) ⊗ (det (F ⧸ range D₁))^*` of `D₁`. This is `TauCeti.detLineFourTermEquiv` for that
sequence; its value is `ContinuousLinearMap.detLineCoprodEquiv_tmul`. -/
noncomputable def detLineCoprodEquiv (h : Function.Surjective (D₁.coprod D₂)) :
    TauCeti.detLine 𝕜 (D₁.coprod D₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) ≃ₗ[𝕜]
      (D₁ : E →ₗ[𝕜] F).detLine :=
  TauCeti.detLineFourTermEquiv (kerCoprodHom_injective D₁ D₂)
    (exact_kerCoprodHom_parameterProj D₁ D₂) (exact_parameterProj_parameterToCoker D₁ D₂)
    ((parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).2 h)

/-- **The value of `ContinuousLinearMap.detLineCoprodEquiv` on exterior products.** Let `u` be a
family of `dim (ker D₁)` vectors of `ker D₁`, let `v` be a family of `dim (range p)` vectors of
the kernel of `D₁.coprod D₂`, where `p` is the parameter projection
`ContinuousLinearMap.parameterProj`, and let `z` be a family of `dim (F ⧸ range D₁)` parameters.
Let `β` be the exterior product of the vectors `(u i, 0)` followed by `v`, and `γ` the exterior
product of the parameter components `p ∘ v` followed by `z`. Then `β ⊗ φ` goes to `α ⊗ ψ`, with
`α` the exterior product of `u` and `ψ` the functional taking the value `φ γ` at the exterior
product of the classes of `D₂ ∘ z` in the cokernel. -/
theorem detLineCoprodEquiv_tmul (h : Function.Surjective (D₁.coprod D₂))
    (u : Fin (finrank 𝕜 D₁.ker) → D₁.ker)
    (v : Fin (finrank 𝕜 (parameterProj D₁ D₂).range) → (D₁.coprod D₂).ker)
    (z : Fin (finrank 𝕜 (F ⧸ D₁.range)) → Λ) {β : TauCeti.detLine 𝕜 (D₁.coprod D₂).ker}
    (hβ : (β : ExteriorAlgebra 𝕜 (D₁.coprod D₂).ker) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (kerCoprodHom D₁ D₂ ∘ u) v))
    {γ : TauCeti.detLine 𝕜 Λ} (hγ : (γ : ExteriorAlgebra 𝕜 Λ) =
      ExteriorAlgebra.ιMulti 𝕜 _ (Fin.append (parameterProj D₁ D₂ ∘ v) z))
    (φ : Dual 𝕜 (TauCeti.detLine 𝕜 Λ)) :
    TensorProduct.rid 𝕜 _
        ((Dual.eval 𝕜 _ (exteriorPower.ιMulti 𝕜 _ (parameterToCoker D₁ D₂ ∘ z))).lTensor _
          (detLineCoprodEquiv D₁ D₂ h (β ⊗ₜ φ))) =
      φ γ • exteriorPower.ιMulti 𝕜 _ u :=
  TauCeti.detLineFourTermEquiv_tmul _ _ _ _ u v z hβ hγ φ

end Stabilization

end ContinuousLinearMap
