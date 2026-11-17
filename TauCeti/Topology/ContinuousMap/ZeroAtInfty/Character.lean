/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.ContinuousMap.Ideals
import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization

/-!
# Characters of `C₀(Y, 𝕜)`

On a regular locally compact space `α`, Urysohn cutoffs in `C₀(α, β)` show that point evaluations
`ZeroAtInftyContinuousMap.evalNonUnitalAlgHom 𝕜 x : C₀(α, β) →ₙₐ[𝕜] β` are nonzero
(`ZeroAtInftyContinuousMap.evalNonUnitalAlgHom_ne_zero`) and, when `α` is `T₁`, separate points
(`ZeroAtInftyContinuousMap.evalNonUnitalAlgHom_injective`).

For an `RCLike` scalar field `𝕜` and a weakly locally compact Hausdorff space `Y`, lifting a
nonzero non-unital algebra character `ψ : C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜` to the one-point compactification via
Mathlib's `ZeroAtInftyContinuousMap.unitizationAlgEquiv` and
`WeakDual.CharacterSpace.continuousMapEval_bijective` shows that every nonzero character of
`C₀(Y, 𝕜)` is point evaluation at a unique point of `Y`
(`ZeroAtInftyContinuousMap.existsUnique_eq_evalNonUnitalAlgHom`).

## Main results

* `ZeroAtInftyContinuousMap.evalNonUnitalAlgHom_ne_zero`: point evaluation on `C₀(α, β)` is
  nonzero on a regular locally compact space for nontrivial `β`.
* `ZeroAtInftyContinuousMap.evalNonUnitalAlgHom_injective`: point evaluations separate points on
  a regular locally compact `T₁` space for nontrivial `β`.
* `ZeroAtInftyContinuousMap.existsUnique_eq_evalNonUnitalAlgHom`: every nonzero character
  `C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜` on a weakly locally compact Hausdorff space is point evaluation at a unique
  point of `Y`.

## References

* Gerald J. Murphy, *C*-Algebras and Operator Theory*, Section 1.3 (characters of `C₀(X)`).
* Bruce Blackadar, *Operator Algebras*, Section II.2.2 (Gelfand theory for non-unital algebras).
-/

public section

open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

section Separation

variable {𝕜 α β : Type*} [TopologicalSpace α] [RegularSpace α] [LocallyCompactSpace α]
  [Semiring 𝕜] [TopologicalSpace β] [NonUnitalNonAssocSemiring β]
  [IsTopologicalSemiring β] [Module 𝕜 β] [ContinuousConstSMul 𝕜 β] [MulActionWithZero ℝ β]
  [ContinuousSMul ℝ β] [Nontrivial β]

/-- On a regular locally compact space, point evaluation `evalNonUnitalAlgHom 𝕜 x` on `C₀(α, β)`
is nonzero whenever `β` is nontrivial. -/
theorem evalNonUnitalAlgHom_ne_zero (x : α) :
    evalNonUnitalAlgHom 𝕜 (β := β) x ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_ne (0 : β)
  obtain ⟨f, hfx, -, -, -⟩ := exists_eqOn_const_zero_of_isCompact
    (isCompact_singleton (x := x)) isClosed_empty (Set.disjoint_empty _) a
  intro h0
  exact ha <| by simpa [hfx rfl] using congr($h0 f)

/-- On a regular locally compact `T₁` space, distinct points induce distinct evaluation
homomorphisms `C₀(α, β) →ₙₐ[𝕜] β` whenever `β` is nontrivial. -/
theorem evalNonUnitalAlgHom_injective [T1Space α] :
    Function.Injective (evalNonUnitalAlgHom 𝕜 (α := α) (β := β)) := by
  intro x y hxy
  by_contra hne
  obtain ⟨a, ha⟩ := exists_ne (0 : β)
  obtain ⟨f, hfx, hfy, -, -⟩ := exists_eqOn_const_zero_of_isCompact
    (isCompact_singleton (x := x)) isClosed_singleton (Set.disjoint_singleton.2 hne) a
  have h : f x = f y := by simpa using congr($hxy f)
  rw [hfx rfl, hfy rfl] at h
  exact ha h

end Separation

section Classification

variable {𝕜 Y : Type*} [RCLike 𝕜] [TopologicalSpace Y] [WeaklyLocallyCompactSpace Y] [T2Space Y]

/-- Every nonzero algebra character `C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜` on a weakly locally compact Hausdorff space
is point evaluation at a unique point of `Y`. -/
theorem existsUnique_eq_evalNonUnitalAlgHom (ψ : C₀(Y, 𝕜) →ₙₐ[𝕜] 𝕜) (hψ : ψ ≠ 0) :
    ∃! y : Y, ψ = evalNonUnitalAlgHom 𝕜 y := by
  let χ : C(OnePoint Y, 𝕜) →ₐ[𝕜] 𝕜 :=
    (Unitization.lift ψ).comp (unitizationAlgEquiv Y 𝕜 𝕜).symm.toAlgHom
  obtain ⟨z, hz⟩ :=
    (WeakDual.CharacterSpace.continuousMapEval_bijective (OnePoint Y) 𝕜).2
      (WeakDual.CharacterSpace.equivAlgHom.symm χ)
  have hval (f : C₀(Y, 𝕜)) : ψ f = f.toOnePoint z := by
    have h1 := congr($hz f.toOnePoint)
    simp only [WeakDual.CharacterSpace.continuousMapEval_apply_apply,
      WeakDual.CharacterSpace.equivAlgHom_symm_coe] at h1
    rw [h1]
    simp only [χ, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, coe_unitizationAlgEquiv_symm]
    rw [← unitizationEquiv_inr, Equiv.symm_apply_apply]
    simp [Unitization.lift]
  cases z with
  | infty =>
    exfalso
    apply hψ
    ext f
    simpa using hval f
  | coe y =>
    have hy : ψ = evalNonUnitalAlgHom 𝕜 y := by
      ext f
      simpa using hval f
    exact ⟨y, hy, fun y' hy' => (evalNonUnitalAlgHom_injective (hy.symm.trans hy')).symm⟩

end Classification

end ZeroAtInftyContinuousMap
