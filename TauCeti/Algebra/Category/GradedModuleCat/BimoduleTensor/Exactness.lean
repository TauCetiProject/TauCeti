/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
import TauCeti.LinearAlgebra.Dual.FiniteProjective
import TauCeti.LinearAlgebra.Dual.Opposite
import TauCeti.LinearAlgebra.TensorProduct.Balanced.DualHom

/-!
# Exactness of a finite-projective graded bimodule tensor action

A graded `(A,B)`-bimodule finite projective as a right `B`-module acts on graded
left `B`-modules by an exact functor to graded left `A`-modules. Its underlying
balanced tensor carrier is naturally the ground-ring linear Hom module out of
its opposite dual. Opposite-dual reflexivity and finite projectivity supply this
identification, and projective lifting proves exactness on underlying modules.
The existing graded exactness criterion then gives preservation of homology.

Only finiteness over the balancing algebra on the right is needed. Neither
algebra nor the bimodule is required to be finite over the commutative ground
ring. The carrier equivalence is not asserted to preserve the internal grading
or the outer left action. The two module carrier universes are independent.
-/

public section
noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory MulOpposite
open scoped TensorProduct

universe vM vN uk uA uB

variable {k : Type uk} {A : Type uA} {B : Type uB}
  [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B)

attribute [local instance] instModuleMulOppositeCarrierTensorProduct
  instIsScalarTowerMulOppositeCarrierTensorProduct

private theorem rightDual_finite_projective
    (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
    [Module.Finite Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M] :
    Module.Finite B (M →ₗ[Bᵐᵒᵖ] B) ∧ Module.Projective B (M →ₗ[Bᵐᵒᵖ] B) :=
  ⟨Module.Finite.of_surjective (opDualCodomainEquiv B M).symm.toLinearMap
    (opDualCodomainEquiv B M).symm.surjective,
    Module.Projective.of_equiv (opDualCodomainEquiv B M).symm⟩

variable [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece]

/-- The underlying tensor carrier is Hom from the opposite dual of a finite projective
right module. This equivalence is linear over the ground ring. -/
def bimoduleModuleTensorHomEquiv
    (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
    [Module.Finite Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M]
    (N : GradedModuleCat.{vN} Δ.piece) :
    GradedModuleCat.bimoduleModuleTensorObj Γ Δ M N ≃ₗ[k]
      ((M →ₗ[Bᵐᵒᵖ] B) →ₗ[B] N) := by
  let : Module.Finite B (M →ₗ[Bᵐᵒᵖ] B) := (rightDual_finite_projective Γ Δ M).1
  let : Module.Projective B (M →ₗ[Bᵐᵒᵖ] B) := (rightDual_finite_projective Γ Δ M).2
  exact (GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv Γ Δ M N).trans
    ((BalancedTensorProduct.congr ((unopDualEvalEquiv B M).restrictScalars k)
      (LinearEquiv.refl k N)
      (fun a m ↦ (unopDualEvalEquiv B M).map_smul (op a) m) (fun _ _ ↦ rfl)).trans
      (balancedDualTensorHomEquiv k B (M →ₗ[Bᵐᵒᵖ] B) N))

/-- The tensor–Hom equivalence evaluates a pure tensor by applying the functional. -/
@[simp]
theorem bimoduleModuleTensorHomEquiv_tmul
    (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
    [Module.Finite Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M]
    (N : GradedModuleCat.{vN} Δ.piece) (m : M) (n : N) (p : M →ₗ[Bᵐᵒᵖ] B) :
    bimoduleModuleTensorHomEquiv Γ Δ M N
        (GradedModuleCat.bimoduleModuleTensorTmul Γ Δ M N m n) p =
      p m • n := by
  let : Module.Finite B (M →ₗ[Bᵐᵒᵖ] B) := (rightDual_finite_projective Γ Δ M).1
  let : Module.Projective B (M →ₗ[Bᵐᵒᵖ] B) := (rightDual_finite_projective Γ Δ M).2
  have hc := BalancedTensorProduct.congr_tmul
    ((unopDualEvalEquiv B M).restrictScalars k) (LinearEquiv.refl k N)
    (fun a m ↦ (unopDualEvalEquiv B M).map_smul (op a) m) (fun _ _ ↦ rfl) m n
  unfold bimoduleModuleTensorHomEquiv
  rw [LinearEquiv.trans_apply,
    GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv_tmul,
    LinearEquiv.trans_apply]
  rw [hc]
  simp only [LinearEquiv.restrictScalars_apply, LinearEquiv.refl_apply,
    balancedDualTensorHomEquiv_apply, balancedDualTensorHom_tmul,
    unopDualEvalEquiv_apply]

/-- The tensor–Hom equivalence is natural in the graded left-module argument. -/
theorem bimoduleModuleTensorHomEquiv_naturality
    (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
    [Module.Finite Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M]
    {N N' : GradedModuleCat.{vN} Δ.piece} (f : N ⟶ N') :
    (f.hom.compRight k).comp (bimoduleModuleTensorHomEquiv Γ Δ M N).toLinearMap =
      (bimoduleModuleTensorHomEquiv Γ Δ M N').toLinearMap.comp
        ((((GradedModuleCat.bimoduleModuleTensor Γ Δ).obj M).map f).hom.restrictScalars k) := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro p
  -- Expose LinearMap.comp, compRight, restrictScalars and LinearEquiv.toLinearMap
  -- as applications before induction on the underlying balanced tensor carrier.
  change f.hom (bimoduleModuleTensorHomEquiv Γ Δ M N z p) =
    bimoduleModuleTensorHomEquiv Γ Δ M N'
      ((((GradedModuleCat.bimoduleModuleTensor Γ Δ).obj M).map f).hom z) p
  obtain ⟨t, rfl⟩ :=
    (GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv Γ Δ M N).symm.surjective z
  induction t using BalancedTensorProduct.induction_on with
  | ht m n =>
    simp only [GradedModuleCat.bimoduleModuleTensorUnderlyingEquiv_symm_tmul]
    -- The curried bimoduleModuleTensor functor defines this map using
    -- bimoduleModuleTensorMap with the identity in the bimodule variable.
    -- Expose that representation to apply its named pure-tensor computation.
    change f.hom (bimoduleModuleTensorHomEquiv Γ Δ M N
      (GradedModuleCat.bimoduleModuleTensorTmul Γ Δ M N m n) p) =
      bimoduleModuleTensorHomEquiv Γ Δ M N'
        ((GradedModuleCat.bimoduleModuleTensorMap Γ Δ (𝟙 M) f).hom
          (GradedModuleCat.bimoduleModuleTensorTmul Γ Δ M N m n)) p
    rw [GradedModuleCat.bimoduleModuleTensorMap_tmul, GradedModuleCat.hom_id,
      LinearMap.id_apply, bimoduleModuleTensorHomEquiv_tmul, bimoduleModuleTensorHomEquiv_tmul]
    exact f.hom.map_smul _ _
  | ha x y hx hy =>
    simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hx hy

/-- A graded bimodule finite projective over the balancing algebra on the right acts
by a functor preserving homology of graded left modules. -/
theorem bimoduleModuleTensor_preservesHomology
    (M : GradedModuleCat.{vM} (Γ.tensorProduct Δ.opposite).piece)
    [Module.Finite Bᵐᵒᵖ M] [Module.Projective Bᵐᵒᵖ M] :
    ((GradedModuleCat.bimoduleModuleTensor.{vM, vN} Γ Δ).obj M).PreservesHomology := by
  let P := M →ₗ[Bᵐᵒᵖ] B
  let : Module.Projective B P := (rightDual_finite_projective Γ Δ M).2
  apply Functor.preservesHomology_of_map_exact
    ((GradedModuleCat.bimoduleModuleTensor.{vM, vN} Γ Δ).obj M)
  intro S hS
  apply GradedModuleCat.exact_iff.mpr
  have H := GradedModuleCat.exact_iff.mp hS
  have hHom : Function.Exact
      ((S.f.hom.compRight k) : (P →ₗ[B] S.X₁) →ₗ[k] (P →ₗ[B] S.X₂))
      ((S.g.hom.compRight k) : (P →ₗ[B] S.X₂) →ₗ[k] (P →ₗ[B] S.X₃)) := by
    intro φ
    constructor
    · intro hφ
      let φRange : P →ₗ[B] LinearMap.range S.f.hom :=
        φ.codRestrict _ fun p ↦ (H (φ p)).1 (by
          simpa using congrArg (fun f : P →ₗ[B] S.X₃ ↦ f p) hφ)
      obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property S.f.hom.rangeRestrict φRange
        (by rintro ⟨y, x, hx⟩; exact ⟨x, Subtype.ext hx⟩)
      refine ⟨ψ, ?_⟩
      ext p
      exact congrArg Subtype.val (LinearMap.congr_fun hψ p)
    · rintro ⟨ψ, rfl⟩
      ext p
      exact H.apply_apply_eq_zero (ψ p)
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (bimoduleModuleTensorHomEquiv_naturality Γ Δ M S.f)
    (bimoduleModuleTensorHomEquiv_naturality Γ Δ M S.g)).mp hHom

end TauCeti.GradedModuleCat
