/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.RingTheory.Derivation.DifferentialOperator

/-!
# First-jet extension as a differential operator

The first-jet extension sends a smooth section of `V` to a smooth section of `J¹V`.
It is linear over the ground field, but generally not over smooth functions: its Leibniz rule is

`j¹(f s)(x) = f(x) • j¹s(x) + ofDeriv ((df)(x).smulRight (s(x)))`.

Consequently its commutator with multiplication by `f` is a smooth-function-linear map,
and first-jet extension is a differential operator of order at most one in the iterated
commutator filtration. The formula identifies the derivative contribution intrinsically
in the kernel of the first-jet projection, without choosing a connection. Nonzero values
of `df` and `s` at a common point witness that the operator does not have order zero.

Neither finite rank nor finite dimension of the base is needed.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.16–12.17.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti.FirstJetBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I]

variable (I F V) in
/-- The ground-field-linear first-jet extension of smooth sections. -/
def jetExtension : Cₛ^∞⟮I; F, V⟯ →ₗ[𝕜]
    Cₛ^∞⟮I; F × (E →L[𝕜] F), FirstJetBundle I F V⟯ where
  toFun s := ⟨jet I F s, by
    have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    have : ContMDiffVectorBundle (∞ + 1) F V I := by
      simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
    exact contMDiff_jet (n := ∞) I F (by simpa using s.contMDiff)⟩
  map_add' s t := ContMDiffSection.ext fun x ↦
    jet_add (s.contMDiff.mdifferentiable (by simp) x) (t.contMDiff.mdifferentiable (by simp) x)
  map_smul' c s := ContMDiffSection.ext fun x ↦ jet_const_smul c s x

/-- Jet extension evaluates to the pointwise first jet. -/
@[simp]
theorem jetExtension_apply (s : Cₛ^∞⟮I; F, V⟯) (x : M) :
    jetExtension I F V s x = jet I F s x := (rfl)

section Leibniz

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

/-- The first-jet extension of a smooth-function multiple satisfies the pointwise Leibniz rule. -/
theorem jetExtension_smul_apply (f : C^∞⟮I, M; 𝕜⟯) (s : Cₛ^∞⟮I; F, V⟯) (x : M) :
    jetExtension I F V (f • s) x = f x • jetExtension I F V s x +
      ofDeriv I F x ((mvfderiv I f x).smulRight (s x)) := by
  have hfs : ⇑(f • s) = (f : M → 𝕜) • (s : ∀ x, V x) :=
    funext fun y ↦ ContMDiffSection.smul_apply f s y
  rw [jetExtension_apply, jetExtension_apply, hfs]
  exact jet_smul (f.contMDiff.mdifferentiable (by simp) x)
    (s.contMDiff.mdifferentiable (by simp) x)

/-- The commutator of jet extension and multiplication is insertion of `df ⊗ s`. -/
theorem smulCommutator_jetExtension_apply (f : C^∞⟮I, M; 𝕜⟯)
    (s : Cₛ^∞⟮I; F, V⟯) (x : M) :
    smulCommutator 𝕜 f (jetExtension I F V) s x =
      ofDeriv I F x ((mvfderiv I f x).smulRight (s x)) := by
  rw [smulCommutator_apply_apply]
  simp only [ContMDiffSection.coe_sub, Pi.sub_apply, ContMDiffSection.smul_apply,
    jetExtension_smul_apply, add_sub_cancel_left]

end Leibniz

/-- The commutator of first-jet extension with multiplication is smooth-function-linear. -/
theorem smulCommutator_jetExtension_smul (f g : C^∞⟮I, M; 𝕜⟯)
    (s : Cₛ^∞⟮I; F, V⟯) :
    smulCommutator 𝕜 f (jetExtension I F V) (g • s) =
      g • smulCommutator 𝕜 f (jetExtension I F V) s := by
  have : ∀ x, IsTopologicalAddGroup (V x) := VectorBundle.isTopologicalAddGroup 𝕜 F V
  have : ∀ x, ContinuousSMul 𝕜 (V x) := VectorBundle.continuousSMul 𝕜 F V
  ext x
  simp only [ContMDiffSection.smul_apply, smulCommutator_jetExtension_apply]
  rw [← map_smul]
  congr 1
  ext v
  exact smul_comm _ _ _

/-- First-jet extension is a differential operator of order at most one. -/
theorem jetExtension_mem_differentialOperators_one :
    jetExtension I F V ∈ differentialOperators 𝕜 C^∞⟮I, M; 𝕜⟯
      Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F × (E →L[𝕜] F), FirstJetBundle I F V⟯ 1 := by
  rw [mem_differentialOperators_succ_iff]
  intro f
  rw [mem_differentialOperators_zero_iff]
  exact smulCommutator_jetExtension_smul f

/-- A nonzero scalar derivative and a nonzero section value at the same point witness that
first-jet extension does not have order zero. -/
theorem jetExtension_notMem_differentialOperators_zero (f : C^∞⟮I, M; 𝕜⟯)
    (s : Cₛ^∞⟮I; F, V⟯) (x : M) (hf : mvfderiv I f x ≠ 0) (hs : s x ≠ 0) :
    jetExtension I F V ∉ differentialOperators 𝕜 C^∞⟮I, M; 𝕜⟯
      Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F × (E →L[𝕜] F), FirstJetBundle I F V⟯ 0 := by
  have : ∀ x, IsTopologicalAddGroup (V x) := VectorBundle.isTopologicalAddGroup 𝕜 F V
  have : ∀ x, ContinuousSMul 𝕜 (V x) := VectorBundle.continuousSMul 𝕜 F V
  intro hj
  have hz := congrArg (fun D ↦ D s x)
    (smulCommutator_eq_zero_of_mem_differentialOperators_zero hj f)
  rw [smulCommutator_jetExtension_apply] at hz
  have h := (ofDeriv_injective I F x) (hz.trans (map_zero (ofDeriv I F x)).symm)
  apply hf
  ext v
  simpa only [ContinuousLinearMap.smulRight_apply, zero_apply, smul_eq_zero, hs, or_false]
    using DFunLike.congr_fun h v

end TauCeti.FirstJetBundle
