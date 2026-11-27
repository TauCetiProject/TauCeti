/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft
import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial

/-!
# Tensor products of scalar tests

The *scalar tests* on a manifold `M` are the bundle tests of the trivial line `Bundle.Trivial M ℝ`,
the compactly supported smooth real functions on `M`. The tensor product of a scalar test `φ` on `M`
and a scalar test `ψ` on `N` is the scalar test

`(φ ⊗ ψ)(x, y) = φ x * ψ y`

on `M × N` (`TauCeti.BundleTest.tensor`). It is bilinear, supported in the product of the supports
(`TauCeti.BundleTest.tsupport_tensor_subset`), and multiplying it by `(x, y) ↦ f x * g y` multiplies
the factors by `f` and `g` (`TauCeti.BundleTest.smulLeftCLM_mulProd_tensor`).

## Main declarations

* `TauCeti.BundleTest.tensor`: the tensor product `φ ⊗ ψ` of scalar tests.
* `TauCeti.BundleTest.tensor_apply`: its values `φ x * ψ y`.
-/

public noncomputable section

open Bundle Set Function ContMDiffSection
open scoped ContDiff Manifold

namespace TauCeti.BundleTest

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The section `(x, y) ↦ φ x * ψ y` of the trivial line over `M × N`. -/
private def tensorSection (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) : Cₛ^∞⟮I.prod J; ℝ, Bundle.Trivial (M × N) ℝ⟯ :=
  trivialEquiv.symm ((trivialEquiv ((ofCompactlySupported I ℝ _).symm φ).val).mulProd
    (trivialEquiv ((ofCompactlySupported J ℝ _).symm ψ).val))

private theorem tensorSection_apply (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) (z : M × N) :
    (tensorSection φ ψ z : ℝ) = φ z.1 * ψ z.2 := by
  simp [tensorSection]

private theorem tsupport_tensorSection_subset (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    (tensorSection φ ψ).tsupport ⊆ closure {x | φ x ≠ 0} ×ˢ closure {y | ψ y ≠ 0} := by
  have h := ContMDiffMap.tsupport_mulProd_subset
    (trivialEquiv ((ofCompactlySupported I ℝ _).symm φ).val)
    (trivialEquiv ((ofCompactlySupported J ℝ _).symm ψ).val)
  rw [_root_.tsupport, _root_.tsupport, _root_.tsupport, coe_trivialEquiv, coe_trivialEquiv] at h
  rw [tsupport_def, tensorSection, coe_trivialEquiv_symm]
  exact h

/-- The **tensor product** `(φ ⊗ ψ)(x, y) = φ x * ψ y` of a scalar test `φ` on `M` and a scalar
test `ψ` on `N`, a scalar test on `M × N`. -/
def tensor (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    BundleTest (I.prod J) ℝ (Bundle.Trivial (M × N) ℝ) :=
  ofCompactlySupported _ _ _ ⟨tensorSection φ ψ, mem_compactlySupported.2 <|
    (φ.isCompact_tsupport.prod ψ.isCompact_tsupport).of_isClosed_subset
      (ContMDiffSection.isClosed_tsupport _) (tsupport_tensorSection_subset φ ψ)⟩

/-- The tensor product of scalar tests is `(φ ⊗ ψ)(x, y) = φ x * ψ y`. -/
@[simp]
theorem tensor_apply (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) (z : M × N) :
    (φ.tensor ψ z : ℝ) = φ z.1 * ψ z.2 := by
  rw [tensor, coe_ofCompactlySupported]
  exact tensorSection_apply φ ψ z

/-- The closed support of `φ ⊗ ψ` lies in the product of the closed supports of `φ` and `ψ`. -/
theorem tsupport_tensor_subset (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    closure {z | φ.tensor ψ z ≠ 0} ⊆ closure {x | φ x ≠ 0} ×ˢ closure {y | ψ y ≠ 0} := by
  rw [tensor, LinearEquiv.symm_apply_apply, ← tsupport_def]
  exact tsupport_tensorSection_subset φ ψ

/-- The tensor product with the zero scalar test on the left vanishes. -/
@[simp]
theorem zero_tensor (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    (0 : BundleTest I ℝ (Bundle.Trivial M ℝ)).tensor ψ = 0 :=
  BundleTest.ext fun z ↦ by simp only [zero_apply, tensor_apply]; exact zero_mul _

/-- The tensor product with the zero scalar test on the right vanishes. -/
@[simp]
theorem tensor_zero (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) :
    φ.tensor (0 : BundleTest J ℝ (Bundle.Trivial N ℝ)) = 0 :=
  BundleTest.ext fun z ↦ by simp only [zero_apply, tensor_apply]; exact mul_zero _

/-- The tensor product of scalar tests is additive in its first factor. -/
theorem add_tensor (φ φ' : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) : (φ + φ').tensor ψ = φ.tensor ψ + φ'.tensor ψ :=
  BundleTest.ext fun z ↦ by simp only [add_apply, tensor_apply]; exact add_mul _ _ _

/-- The tensor product of scalar tests is additive in its second factor. -/
theorem tensor_add (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ ψ' : BundleTest J ℝ (Bundle.Trivial N ℝ)) : φ.tensor (ψ + ψ') = φ.tensor ψ + φ.tensor ψ' :=
  BundleTest.ext fun z ↦ by simp only [add_apply, tensor_apply]; exact mul_add _ _ _

/-- The tensor product of scalar tests is homogeneous in its first factor. -/
theorem smul_tensor (a : ℝ) (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) : (a • φ).tensor ψ = a • φ.tensor ψ :=
  BundleTest.ext fun z ↦ by simp only [smul_apply, tensor_apply]; exact mul_assoc _ _ _

/-- The tensor product of scalar tests is homogeneous in its second factor. -/
theorem tensor_smul (a : ℝ) (φ : BundleTest I ℝ (Bundle.Trivial M ℝ))
    (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) : φ.tensor (a • ψ) = a • φ.tensor ψ :=
  BundleTest.ext fun z ↦ by simp only [smul_apply, tensor_apply]; exact mul_left_comm _ _ _

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- Multiplying `φ ⊗ ψ` by the smooth function `(x, y) ↦ f x * g y` multiplies `φ` by `f` and `ψ`
by `g`. -/
theorem smulLeftCLM_mulProd_tensor (f : C^∞⟮I, M; ℝ⟯) (g : C^∞⟮J, N; ℝ⟯)
    (φ : BundleTest I ℝ (Bundle.Trivial M ℝ)) (ψ : BundleTest J ℝ (Bundle.Trivial N ℝ)) :
    smulLeftCLM (f.mulProd g) (φ.tensor ψ) = (smulLeftCLM f φ).tensor (smulLeftCLM g ψ) := by
  refine BundleTest.ext fun z ↦ ?_
  simp only [smulLeftCLM_apply, tensor_apply, ContMDiffMap.mulProd_apply, smul_eq_mul]
  ring

end TauCeti.BundleTest
