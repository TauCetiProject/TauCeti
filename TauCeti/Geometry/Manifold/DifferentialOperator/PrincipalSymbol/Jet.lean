/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Jet
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Jet.Symbol
import TauCeti.Geometry.Manifold.Algebra.SmoothFunctions
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The principal symbol through jets

Let `P : Γ(V) → Γ(W)` be a differential operator of order at most `m` between smooth sections of
real vector bundles over a manifold without boundary, in Grothendieck's sense of iterated
commutators with multiplication operators. It factors at each point `x` through the fibre of the
jet bundle, `(P s)(x) = A_x (jᵐs(x))` (`LinearMap.jetFactorOfMemDifferentialOperators`). This file
identifies its principal symbol with the restriction of `A_x` to the top-order jets
`TauCeti.JetBundle.ofTop`, the kernel of the truncation `(JₘV)ₓ → (Jₘ₋₁V)ₓ`:

`σ(P)(ξ) v = A_x (ofTop (ξ ⊗ ⋯ ⊗ ξ ⊗ v))`,

where `ξ ⊗ ⋯ ⊗ ξ ⊗ v` is the multilinear map `(v₁, …, vₘ) ↦ ξ(v₁) ⋯ ξ(vₘ) v`
(`TauCeti.sectionPrincipalSymbol_apply_eq_jetFactorOfMemDifferentialOperators`). Equivalently the
commutator symbol is `[⋯[P, ξ₁], …, ξₘ] v = A_x (ofTop (m! • (ξ₁ ⊗ ⋯ ⊗ ξₘ ⊗ v)))`
(`TauCeti.sectionCommutatorSymbol_apply_eq_jetFactorOfMemDifferentialOperators`). So the algebraic
principal symbol, defined by iterated commutators, is the top-order part of the jet factorization:
the coefficient of the derivatives of highest order.

The proof lifts the covectors `ξᵢ` to functions `fᵢ` vanishing at `x`. Modulo functions vanishing
at `x`, the iterated commutator `[⋯[P, f₁], …, fₘ] s` is `P (f₁ ⋯ fₘ s)`
(`TauCeti.commutatorSymbol_apply_sub_apply_prod_smul_mem_smul_top`), and the jet of
`f₁ ⋯ fₘ s` at `x` is the top-order jet `ofTop (m! • (dₓf₁ ⊗ ⋯ ⊗ dₓfₘ ⊗ s(x)))`
(`TauCeti.JetBundle.jet_prod_smul`).

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*, §§12, 19.
* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

open JetBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] {x : M}

/-- **The commutator symbol through jets.** The commutator symbol of a differential operator `P`
of order at most `m` at `(ξ₁, …, ξₘ)`, applied to `v`, is its jet factor at `x` applied to the
top-order jet `ofTop (m! • (ξ₁ ⊗ ⋯ ⊗ ξₘ ⊗ v))`, where `ξ₁ ⊗ ⋯ ⊗ ξₘ ⊗ v` is the multilinear map
`(v₁, …, vₘ) ↦ ξ₁(v₁) ⋯ ξₘ(vₘ) v`. -/
theorem sectionCommutatorSymbol_apply_eq_jetFactorOfMemDifferentialOperators
    (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionCommutatorSymbol I hx P ξ v =
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).jetFactorOfMemDifferentialOperators P.property x
        (ofTop I F V m x (m.factorial •
          (ContinuousMultilinearMap.mkPiRing ℝ (Fin m) v).compContinuousLinearMap ξ)) := by
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ x v
  rw [ContMDiffSection.evalLinearMap_apply]
  -- Lift the covectors to functions `fᵢ` vanishing at `x`.
  set f : Fin m → C^∞⟮I, M; ℝ⟯ := fun i ↦ covectorLift I hx (ξ i)
  have hf : ∀ i, f i x = 0 := fun i ↦ covectorLift_apply_self hx (ξ i)
  have hξ : ξ = fun i ↦ mvfderiv I (f i) x := funext fun i ↦ (mvfderiv_covectorLift hx (ξ i)).symm
  -- Modulo functions vanishing at `x`, the iterated commutator is `P ((f₁ ⋯ fₘ) • s)`.
  have hcomm := apply_eq_zero_of_mem_smoothVanishingIdeal_smul_top
    (commutatorSymbol_apply_sub_apply_prod_smul_mem_smul_top P
      (fun i ↦ mem_smoothVanishingIdeal_iff.2 (hf i)) s)
  rw [ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at hcomm
  have hprod : ⇑((∏ i, f i) • s) = fun y ↦ (∏ i, f i y) • s y := by
    rw [ContMDiffSection.coe_smul_contMDiffMap]
    funext y
    simp only [Pi.smul_apply', ← ContMDiffMap.evalAlgHom_apply (𝕜 := ℝ), map_prod]
  conv_lhs => rw [hξ]
  rw [sectionCommutatorSymbol_mvfderiv, hcomm,
    ← LinearMap.jetFactorOfMemDifferentialOperators_jet P.property, hprod,
    jet_prod_smul f hf s, ← hξ]

/-- **The principal symbol through jets.** The principal symbol `σ(P)(ξ)` of a differential operator
`P` of order at most `m`, applied to `v`, is its jet factor at `x` applied to the top-order jet
`ofTop (ξ ⊗ ⋯ ⊗ ξ ⊗ v)`, where `ξ ⊗ ⋯ ⊗ ξ ⊗ v` is the multilinear map
`(v₁, …, vₘ) ↦ ξ(v₁) ⋯ ξ(vₘ) v`. The principal symbol is the top-order part of the factorization of
`P` through jets. -/
theorem sectionPrincipalSymbol_apply_eq_jetFactorOfMemDifferentialOperators
    (hx : I.IsInteriorPoint x) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (v : V x) :
    sectionPrincipalSymbol I hx P ξ v =
      (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).jetFactorOfMemDifferentialOperators P.property x
        (ofTop I F V m x
          ((ContinuousMultilinearMap.mkPiRing ℝ (Fin m) v).compContinuousLinearMap fun _ ↦ ξ)) := by
  have hm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 m.factorial_ne_zero
  rw [sectionPrincipalSymbol_def, LinearMap.smul_apply,
    sectionCommutatorSymbol_apply_eq_jetFactorOfMemDifferentialOperators, map_nsmul, map_nsmul,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm, one_smul]

end TauCeti
