/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.LinearAlgebra.Dual.BaseChange

import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# Base change of the Auslander–Bridger transpose over commutative rings

Let `R` be a commutative ring, `A` a commutative `R`-algebra, and `f : P₁ →ₗ[R] P₀` a linear map
between finitely generated projective `R`-modules. For a finitely generated projective module `P`,
scalar extension commutes with linear duality:
`A ⊗[R] Hom_R(P, R) ≃ₗ[A] Hom_A(A ⊗[R] P, A)` (`TauCeti.Module.Dual.baseChangeEvaluationEquiv`).
Applying cokernel scalar extension (`LinearMap.cokernelBaseChangeEquiv`) to the defining cokernel
sequence `Hom_R(P₀, R) → Hom_R(P₁, R) → Tr f → 0` therefore identifies the base change of the
transpose with the transpose of the base-changed map:

  `A ⊗[R] AuslanderReitenTranspose f ≃ₗ[A] AuslanderReitenTranspose (f.baseChange A)`.

This compatibility allows invariants of transposed presentations, such as Fitting ideals, to be
computed locally on `Spec R`, where finitely generated projective modules become free.

## Main definitions

* `TauCeti.AuslanderReitenTranspose.baseChangeHom`: the canonical `A`-linear comparison map
  `A ⊗[R] AuslanderReitenTranspose f →ₗ[A] AuslanderReitenTranspose (f.baseChange A)`, defined
  without finiteness or projectivity assumptions.
* `TauCeti.AuslanderReitenTranspose.baseChangeEquiv`: the `A`-linear isomorphism when `P₀` and `P₁`
  are finitely generated projective `R`-modules.

## Main results

* `TauCeti.AuslanderReitenTranspose.baseChangeHom_tmul_mk`,
  `TauCeti.AuslanderReitenTranspose.baseChangeEquiv_tmul_mk`, and
  `TauCeti.AuslanderReitenTranspose.baseChangeEquiv_symm_mk_baseChange`: action of the base-change
  comparison map and equivalence (and its inverse) on functional representatives.
* `TauCeti.AuslanderReitenTranspose.baseChangeEquiv_toLinearMap`: `baseChangeEquiv` has underlying
  linear map `baseChangeHom`.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), Section 2.1.
* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. (2) 197 (2023),
  Appendix B.2, proof of Lemma B.4.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.AuslanderReitenTranspose

section CommRing

variable {R P₀ P₁ : Type*} [CommRing R] [AddCommMonoid P₀] [Module R P₀]
  [AddCommMonoid P₁] [Module R P₁]

variable (A : Type*) [CommRing A] [Algebra R A]

private theorem map_range_baseChange_dualMap_le (f : P₁ →ₗ[R] P₀) :
    (LinearMap.range (f.dualMap.baseChange A)).map
        (TauCeti.Module.Dual.baseChangeEvaluation (R := R) (A := A) (M := P₁)) ≤
      LinearMap.range (f.baseChange A).dualMap := by
  rw [← LinearMap.range_comp, f.baseChangeEvaluation_comp_baseChange_dualMap]
  exact LinearMap.range_comp_le_range _ _

/-- The canonical `A`-linear comparison map
`A ⊗[R] AuslanderReitenTranspose f →ₗ[A] AuslanderReitenTranspose (f.baseChange A)`, sending
`a ⊗ [φ]` to `a • [φ_A]`. No finiteness or projectivity is needed to form this map. -/
def baseChangeHom (f : P₁ →ₗ[R] P₀) :
    A ⊗[R] AuslanderReitenTranspose f →ₗ[A] AuslanderReitenTranspose (f.baseChange A) :=
  (cokernelDualMapEquiv (f.baseChange A)).symm.toLinearMap ∘ₗ
    Submodule.mapQ _ _ (TauCeti.Module.Dual.baseChangeEvaluation (R := R) (A := A) (M := P₁))
      (Submodule.map_le_iff_le_comap.1 (map_range_baseChange_dualMap_le A f)) ∘ₗ
    (f.dualMap.cokernelBaseChangeEquiv (S := A)).toLinearMap ∘ₗ
    ((cokernelDualMapEquiv f).baseChange R A _ _).toLinearMap

/-- `baseChangeHom` sends a pure tensor `a ⊗ [φ]` to `a • [φ_A]`. -/
@[simp]
theorem baseChangeHom_tmul_mk (f : P₁ →ₗ[R] P₀) (a : A) (φ : Module.Dual R P₁) :
    baseChangeHom A f (a ⊗ₜ[R] mk f φ) =
      a • mk (f.baseChange A) (Module.Dual.baseChange A φ) := by
  simp only [baseChangeHom, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.baseChange_tmul, cokernelDualMapEquiv_mk, LinearMap.cokernelBaseChangeEquiv_tmul,
    Submodule.mapQ_apply, TauCeti.Module.Dual.baseChangeEvaluation_tmul_eq_smul,
    Submodule.Quotient.mk_smul, map_smul, cokernelDualMapEquiv_symm_mk]

private theorem map_range_baseChange_dualMap_eq [Module.Finite R P₀] [Module.Projective R P₀]
    (f : P₁ →ₗ[R] P₀) :
    (LinearMap.range (f.dualMap.baseChange A)).map
        (TauCeti.Module.Dual.baseChangeEvaluation (R := R) (A := A) (M := P₁)) =
      LinearMap.range (f.baseChange A).dualMap := by
  rw [← LinearMap.range_comp, f.baseChangeEvaluation_comp_baseChange_dualMap,
    ← TauCeti.Module.Dual.baseChangeEvaluationEquiv_toLinearMap,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

section FiniteProjective

variable [Module.Finite R P₀] [Module.Projective R P₀]
  [Module.Finite R P₁] [Module.Projective R P₁]

private theorem baseChangeHom_bijective (f : P₁ →ₗ[R] P₀) :
    Function.Bijective (baseChangeHom A f) := by
  have he : Function.Bijective
      (TauCeti.Module.Dual.baseChangeEvaluation (R := R) (A := A) (M := P₁)) := by
    rw [← TauCeti.Module.Dual.baseChangeEvaluationEquiv_toLinearMap]
    exact (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := R) (A := A) (M := P₁)).bijective
  have hmapQ : Function.Bijective
      (Submodule.mapQ _ _ (TauCeti.Module.Dual.baseChangeEvaluation (R := R) (A := A) (M := P₁))
        (Submodule.map_le_iff_le_comap.1 (map_range_baseChange_dualMap_le A f))) := by
    refine ⟨LinearMap.ker_eq_bot.1 ?_, LinearMap.range_eq_top.1 ?_⟩
    · rw [Submodule.ker_mapQ, ← map_range_baseChange_dualMap_eq A f,
        Submodule.comap_map_eq_of_injective he.1]
      simp
    · rw [Submodule.range_mapQ, LinearMap.range_eq_top.2 he.2, Submodule.map_top,
        LinearMap.range_eq_top]
      exact Submodule.mkQ_surjective _
  exact ((cokernelDualMapEquiv (f.baseChange A)).symm.bijective).comp
    (hmapQ.comp ((f.dualMap.cokernelBaseChangeEquiv (S := A)).bijective.comp
      ((cokernelDualMapEquiv f).baseChange R A _ _).bijective))

/-- **Base change commutes with the transpose of a finite projective presentation.** For a
commutative ring `R`, a commutative `R`-algebra `A`, and a linear map `f : P₁ →ₗ[R] P₀` between
finitely generated projective `R`-modules, `A ⊗[R] Tr f` is canonically `A`-linearly isomorphic
to `Tr (f.baseChange A)`. -/
def baseChangeEquiv (f : P₁ →ₗ[R] P₀) :
    A ⊗[R] AuslanderReitenTranspose f ≃ₗ[A] AuslanderReitenTranspose (f.baseChange A) :=
  LinearEquiv.ofBijective (baseChangeHom A f) (baseChangeHom_bijective A f)

/-- The underlying linear map of `baseChangeEquiv` is `baseChangeHom`. -/
@[simp]
theorem baseChangeEquiv_toLinearMap (f : P₁ →ₗ[R] P₀) :
    (baseChangeEquiv A f).toLinearMap = baseChangeHom A f := by
  ext z
  simp [baseChangeEquiv]

/-- `baseChangeEquiv` sends a pure tensor `a ⊗ [φ]` to `a • [φ_A]`. -/
@[simp]
theorem baseChangeEquiv_tmul_mk (f : P₁ →ₗ[R] P₀) (a : A) (φ : Module.Dual R P₁) :
    baseChangeEquiv A f (a ⊗ₜ[R] mk f φ) =
      a • mk (f.baseChange A) (Module.Dual.baseChange A φ) := by
  rw [← LinearEquiv.coe_toLinearMap, baseChangeEquiv_toLinearMap, baseChangeHom_tmul_mk]

/-- The inverse of `baseChangeEquiv` carries the class of a base-changed functional `φ_A` back to
`1 ⊗ [φ]`. -/
@[simp]
theorem baseChangeEquiv_symm_mk_baseChange (f : P₁ →ₗ[R] P₀) (φ : Module.Dual R P₁) :
    (baseChangeEquiv A f).symm (mk (f.baseChange A) (Module.Dual.baseChange A φ)) =
      1 ⊗ₜ[R] mk f φ := by
  apply (baseChangeEquiv A f).injective
  simp

end FiniteProjective

end CommRing

end TauCeti.AuslanderReitenTranspose
