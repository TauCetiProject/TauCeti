/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
public import TauCeti.Algebra.HopfAlgebra.Module.Dual

/-!
# Inverse-antipode contragredient representations

For a bijective antipode, the left contragredient acts by
`(a φ)(v) = φ(ρ(S⁻¹(a))v)`. It complements the `S`-contragredient
`AlgHom.hopfDual`. Taking these two contragredients in either order gives
the original representation on its double dual, under ordinary evaluation.
For reflexive modules, evaluation is therefore an intertwining linear
equivalence, natural in intertwiners. These are the representation-level
comparisons underlying left and right Hopf-module duality.

The construction follows `AlgHom.hopfDual`, reusing Mathlib's
`Module.Dual.transpose` and `Module.evalEquiv`. See C. Kassel,
*Quantum Groups*, Chapter III, for the dual action conventions.
-/

public noncomputable section

open Module TauCeti.HopfAlgebra

namespace AlgHom

variable {R H V : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V]

/-- The contragredient representation defined by the inverse antipode. -/
def hopfLeftDual (ρ : H →ₐ[R] Module.End R V)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    H →ₐ[R] Module.End R (Dual R V) :=
  .ofLinearMap (Dual.transpose.comp (ρ.toLinearMap.comp (inverseAntipode hS)))
    (by ext φ v; simp [Dual.transpose_apply])
    (fun a b => by
      ext φ v
      simp [Dual.transpose_apply, inverseAntipode_mul, Module.End.mul_apply])

/-- The left contragredient precomposes a functional with the inverse antipode action. -/
@[simp]
theorem hopfLeftDual_apply (ρ : H →ₐ[R] Module.End R V)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    (a : H) (φ : Dual R V) (v : V) :
    ρ.hopfLeftDual hS a φ v = φ (ρ (inverseAntipode hS a) v) := (rfl)

/-- Taking the inverse-antipode dual after the antipode dual cancels their twists on evaluation. -/
@[simp]
theorem hopfDual_hopfLeftDual_eval (ρ : H →ₐ[R] Module.End R V)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) (a : H) (v : V) :
    (ρ.hopfDual.hopfLeftDual hS) a (Dual.eval R V v) = Dual.eval R V (ρ a v) := by
  ext φ
  simp

/-- Taking the antipode dual after the inverse-antipode dual cancels their twists on evaluation. -/
@[simp]
theorem hopfLeftDual_hopfDual_eval (ρ : H →ₐ[R] Module.End R V)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) (a : H) (v : V) :
    (ρ.hopfLeftDual hS).hopfDual a (Dual.eval R V v) = Dual.eval R V (ρ a v) := by
  ext φ
  simp

variable [Module.IsReflexive R V]

/-- On a reflexive module, inverse evaluation intertwines the mixed double dual with the
original representation, when the inverse-antipode dual is taken last. -/
@[simp]
theorem hopfDual_hopfLeftDual_evalEquiv_symm (ρ : H →ₐ[R] Module.End R V)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    (a : H) (Φ : Dual R (Dual R V)) :
    (Module.evalEquiv R V).symm ((ρ.hopfDual.hopfLeftDual hS) a Φ) =
      ρ a ((Module.evalEquiv R V).symm Φ) := by
  obtain ⟨v, rfl⟩ := (Module.evalEquiv R V).surjective Φ
  simp only [Module.evalEquiv_apply, hopfDual_hopfLeftDual_eval]
  simp only [← Module.evalEquiv_apply, LinearEquiv.symm_apply_apply]

/-- On a reflexive module, inverse evaluation intertwines the mixed double dual with the
original representation, when the antipode dual is taken last. -/
@[simp]
theorem hopfLeftDual_hopfDual_evalEquiv_symm (ρ : H →ₐ[R] Module.End R V)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    (a : H) (Φ : Dual R (Dual R V)) :
    (Module.evalEquiv R V).symm ((ρ.hopfLeftDual hS).hopfDual a Φ) =
      ρ a ((Module.evalEquiv R V).symm Φ) := by
  obtain ⟨v, rfl⟩ := (Module.evalEquiv R V).surjective Φ
  simp only [Module.evalEquiv_apply, hopfLeftDual_hopfDual_eval]
  simp only [← Module.evalEquiv_apply, LinearEquiv.symm_apply_apply]

end AlgHom

namespace LinearMap

variable {R H V W : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  {ρ : H →ₐ[R] Module.End R V} {σ : H →ₐ[R] Module.End R W}

/-- Transposing an intertwiner intertwines the inverse-antipode contragredients. -/
theorem hopfLeftDual_intertwines (f : V →ₗ[R] W)
    (hf : ∀ (a : H) (v : V), f (ρ a v) = σ a (f v))
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) (a : H) (φ : Dual R W) :
    f.dualMap (σ.hopfLeftDual hS a φ) = ρ.hopfLeftDual hS a (f.dualMap φ) := by
  ext v
  simp [hf]

end LinearMap
