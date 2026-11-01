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

For modules rather than representations, `TauCeti.BialgebraModule.LeftDual` is a type synonym of
the native dual carrying the inverse-antipode contragredient action. On a reflexive module,
`TauCeti.BialgebraModule.leftDualEvalEquiv` is evaluation as an `H`-linear equivalence with the
`S`-contragredient `TauCeti.BialgebraModule.Dual` of this left contragredient. It identifies the
module with the right dual of its left dual, from which left duals of finite-dimensional
modules are obtained.

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

namespace TauCeti.BialgebraModule

/-- The linear dual over `R`, with a separate carrier for the inverse-antipode contragredient
action `(a φ)(m) = φ(S⁻¹(a) m)` of a Hopf algebra `H` with bijective antipode.

As for `Dual`, the synonym keeps the `H`-action apart from other actions on the native dual,
the base action is restriction of the `H`-action along the algebra map, and `leftDualEquiv`
identifies it with the native dual. -/
def LeftDual (R H M : Type*) [CommSemiring R] [Semiring H] [HopfAlgebra R H]
    [AddCommMonoid M] [Module R M]
    (_hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :=
  Module.Dual R M

variable (R H M : Type*) [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid M] [Module R M]
  (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))

instance : AddCommMonoid (LeftDual R H M hS) := inferInstanceAs (AddCommMonoid (Module.Dual R M))

instance (R H M : Type*) [CommRing R] [Semiring H] [HopfAlgebra R H] [AddCommGroup M]
    [Module R M] (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H)) :
    AddCommGroup (LeftDual R H M hS) :=
  inferInstanceAs (AddCommGroup (Module.Dual R M))

variable [Module H M] [IsScalarTower R H M]

/-- The inverse-antipode contragredient module structure on the dual carrier. -/
@[no_expose] noncomputable instance : Module H (LeftDual R H M hS) :=
  Module.compHom (Module.Dual R M) ((Algebra.lsmul R R M).hopfLeftDual hS).toRingHom

/-- The base action is restriction of the contragredient action along the algebra map.
The priority keeps this presentation ahead of generic natural and integer scalar actions. -/
noncomputable instance (priority := 1100) : Module R (LeftDual R H M hS) :=
  Module.compHom (LeftDual R H M hS) (algebraMap R H)

/-- The inverse-antipode contragredient module is compatible with its base scalar action. -/
instance : IsScalarTower R H (LeftDual R H M hS) :=
  IsScalarTower.of_compHom R H (LeftDual R H M hS)

/-- The underlying `R`-linear identification with the native dual. -/
noncomputable def leftDualEquiv : LeftDual R H M hS ≃ₗ[R] Module.Dual R M :=
  let e : LeftDual R H M hS ≃+ Module.Dual R M := AddEquiv.refl _
  e.toLinearEquiv fun r φ =>
    LinearMap.congr_fun (((Algebra.lsmul R R M).hopfLeftDual hS).commutes r) φ

/-- An element of `H` acts on a functional by precomposition with the action of its inverse
antipode. -/
@[simp]
theorem leftDualEquiv_smul_apply (h : H) (φ : LeftDual R H M hS) (m : M) :
    leftDualEquiv R H M hS (h • φ) m = leftDualEquiv R H M hS φ (inverseAntipode hS h • m) :=
  (rfl)

/-- The inverse-antipode dual of a finite projective module is finite. -/
instance [Module.Projective R M] [Module.Finite R M] : Module.Finite R (LeftDual R H M hS) :=
  Module.Finite.equiv (leftDualEquiv R H M hS).symm

variable [Module.IsReflexive R M]

/-- Evaluation identifies a reflexive module with the antipode contragredient of its
inverse-antipode contragredient: `m` is sent to the functional `φ ↦ φ m`. -/
noncomputable def leftDualEvalEquiv : M ≃ₗ[H] Dual R H (LeftDual R H M hS) :=
  let e : M ≃ₗ[R] Dual R H (LeftDual R H M hS) :=
    (Module.evalEquiv R M).trans
      ((leftDualEquiv R H M hS).dualMap.trans (dualEquiv R H (LeftDual R H M hS)).symm)
  e.toAddEquiv.toLinearEquiv fun h m =>
    (dualEquiv R H (LeftDual R H M hS)).injective <| LinearMap.ext fun φ => by
      simp [e]

/-- The evaluation equivalence sends `m` to the functional `φ ↦ φ m`. -/
@[simp]
theorem dualEquiv_leftDualEvalEquiv_apply (m : M) (φ : LeftDual R H M hS) :
    dualEquiv R H (LeftDual R H M hS) (leftDualEvalEquiv R H M hS m) φ =
      leftDualEquiv R H M hS φ m := by
  simp [leftDualEvalEquiv]

end TauCeti.BialgebraModule
