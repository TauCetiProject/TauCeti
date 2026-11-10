/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.Fredholm.Parametric
public import TauCeti.LinearAlgebra.Determinant.Exact
import TauCeti.LinearAlgebra.Exact

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

Different stabilizations must give compatible identifications, since nearby operators may need
different ones. If `ι : Λ → Λ'` is injective with `D₂' ∘ ι = D₂`, the stabilized kernels and the
stabilizing spaces both grow by `Λ' ⧸ range ι`, and cancelling this common quotient gives an
isomorphism `det (ker (D₁.coprod D₂')) ⊗ (det Λ')^* ≃ det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*`
(`ContinuousLinearMap.detLineCoprodMapEquiv`) built from the stabilized operators alone. Through
the identifications with the determinant line of `D₁` it is multiplication by
`(-1) ^ (dim (F ⧸ range D₁) * (dim Λ' - dim Λ))`
(`ContinuousLinearMap.detLineCoprodEquiv_detLineCoprodMapEquiv`). The map `ι` covers enlarging
a stabilizer, including a stabilizer `Λ` to `Λ × Λ''`, and changing it by an isomorphism, so any
two stabilizations are compared through their product.

## Main results

* `ContinuousLinearMap.IsFredholm.finrank_detLine`: the determinant line of a Fredholm operator is
  one-dimensional.
* `ContinuousLinearMap.detLineCoprodEquiv`: for a surjective stabilization `D₁.coprod D₂` by a
  finite-dimensional space `Λ`, the isomorphism
  `det (ker (D₁.coprod D₂)) ⊗ (det Λ)^* ≃ det (ker D₁) ⊗ (det (F ⧸ range D₁))^*`.
* `ContinuousLinearMap.detLineCoprodEquiv_tmul`: its value on exterior products.
* `ContinuousLinearMap.detLineCoprodMapEquiv`: the change-of-stabilizer isomorphism for an
  injective map `ι : Λ → Λ'` of stabilizers.
* `ContinuousLinearMap.detLineCoprodEquiv_detLineCoprodMapEquiv`: through
  `ContinuousLinearMap.detLineCoprodEquiv`, the change of stabilizer is a sign.

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

section ChangeOfStabilizer

/-! ### Changing the stabilizer -/

variable {𝕜 E Λ Λ' F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup Λ'] [Module 𝕜 Λ']
  [TopologicalSpace Λ'] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {D₂' : Λ' →L[𝕜] F} {ι : Λ →ₗ[𝕜] Λ'}
  [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 Λ']

variable (D₁) in
/-- **Changing the stabilizer.** Let `ι : Λ → Λ'` be an injective linear map with
`D₂' ∘ ι = D₂`, and let `D₁.coprod D₂` be onto. Then the kernel of `D₁.coprod D₂'` contains that
of `D₁.coprod D₂` through `(x, l) ↦ (x, ι l)` (`ContinuousLinearMap.kerCoprodMap`), both `Λ'`
and that kernel have quotient `Λ' ⧸ range ι`, and cancelling this common quotient
(`TauCeti.detLineShortExactCancelEquiv`) gives the isomorphism
`det (ker (D₁.coprod D₂')) ⊗ (det Λ')^* ≃ det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*`. It is built
from the two stabilized operators and `ι` alone, without reference to `ker D₁` or
`F ⧸ range D₁`. Through `ContinuousLinearMap.detLineCoprodEquiv` it is the identity of the
determinant line of `D₁` up to sign
(`ContinuousLinearMap.detLineCoprodEquiv_detLineCoprodMapEquiv`). -/
noncomputable def detLineCoprodMapEquiv (hι : ∀ l, D₂' (ι l) = D₂ l)
    (hι' : Function.Injective ι) (h : Function.Surjective (D₁.coprod D₂)) :
    TauCeti.detLine 𝕜 (D₁.coprod D₂').ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ') ≃ₗ[𝕜]
      TauCeti.detLine 𝕜 (D₁.coprod D₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ) :=
  have := finiteDimensional_ker_coprod D₁ D₂
  TauCeti.detLineShortExactCancelEquiv (kerCoprodMap_injective hι hι') (exact_kerCoprodMap hι)
    (surjective_mkQ_comp_parameterProj hι h) hι' (LinearMap.exact_map_mkQ_range ι)
    (Submodule.mkQ_surjective _)

/-- **Independence of the stabilizer.** Under `ContinuousLinearMap.detLineCoprodEquiv`, the
change-of-stabilizer isomorphism `ContinuousLinearMap.detLineCoprodMapEquiv` for an injective
`ι : Λ → Λ'` with `D₂' ∘ ι = D₂` becomes multiplication by
`(-1) ^ (dim (F ⧸ range D₁) * (dim Λ' - dim Λ))` on the determinant line of `D₁`. This is
`TauCeti.detLineFourTermEquiv_detLineShortExactCancelEquiv` for the two exact sequences
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → F ⧸ range D₁ → 0` and
`0 → ker D₁ → ker (D₁.coprod D₂') → Λ' → F ⧸ range D₁ → 0`. -/
theorem detLineCoprodEquiv_detLineCoprodMapEquiv (hι : ∀ l, D₂' (ι l) = D₂ l)
    (hι' : Function.Injective ι) (h : Function.Surjective (D₁.coprod D₂))
    (x : TauCeti.detLine 𝕜 (D₁.coprod D₂').ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ')) :
    detLineCoprodEquiv D₁ D₂ h (detLineCoprodMapEquiv D₁ hι hι' h x) =
      (-1 : 𝕜) ^ (finrank 𝕜 (F ⧸ D₁.range) * (finrank 𝕜 Λ' - finrank 𝕜 Λ)) •
        detLineCoprodEquiv D₁ D₂' (surjective_coprod_of_comp hι h) x := by
  have := finiteDimensional_ker_coprod D₁ D₂
  have hm : finrank 𝕜 Λ' - finrank 𝕜 Λ = finrank 𝕜 (Λ' ⧸ LinearMap.range ι) := by
    have := (LinearMap.exact_map_mkQ_range ι).finrank_eq_add hι' (Submodule.mkQ_surjective _)
    omega
  rw [hm]
  -- Both `detLineCoprodEquiv`s are `TauCeti.detLineFourTermEquiv`s of parametric exact sequences,
  -- whose exactness data the eight placeholders recover by unfolding.
  refine TauCeti.detLineFourTermEquiv_detLineShortExactCancelEquiv _ _ _ _ _ _ _ _
    (kerCoprodMap_injective hι hι') (exact_kerCoprodMap hι)
    (surjective_mkQ_comp_parameterProj hι h) hι' (LinearMap.exact_map_mkQ_range ι)
    (Submodule.mkQ_surjective _) ?_ ?_ ?_ x
  · exact LinearMap.ext fun x ↦ Subtype.ext (by simp [coe_kerCoprodMap])
  · exact LinearMap.ext fun v ↦ by simp [coe_kerCoprodMap]
  · exact LinearMap.ext fun l ↦ by simp [hι]

end ChangeOfStabilizer

end ContinuousLinearMap
