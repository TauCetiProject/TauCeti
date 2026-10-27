/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Contragredient Hopf algebra representations

For a representation `ρ : H →ₐ[R] Module.End R V`, its contragredient acts on the native
module dual by `(a φ)(v) = φ(ρ(S(a))v)`. Transposition reverses composition, so the antipode's
antimultiplicativity makes this an algebra representation. Transposing an intertwiner gives
an intertwiner in the reverse direction.

The ordinary evaluation map into the double dual intertwines the action twisted by `S²`.
If `S²(a) = g a g⁻¹` for a unit `g`, evaluation after `ρ(g)` instead intertwines the original
action. On a reflexive module this is a natural linear equivalence with the double
contragredient. In particular it supplies the underlying maps of the pivotal comparison
for finite-dimensional Hopf modules; tensor compatibility requires additional group-like data.

The construction uses Mathlib's `Module.Dual.transpose`, `Module.evalEquiv` and
`LinearMap.GeneralLinearGroup.generalLinearEquiv`. The dual and double-dual conventions are those of
Kassel, *Quantum Groups*, Chapter XIV.
-/

public noncomputable section

open Module HopfAlgebra

namespace AlgHom

variable {R H V : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V]

/-- The contragredient representation, with action through the antipode on the argument
of a linear functional. -/
def hopfDual (ρ : H →ₐ[R] Module.End R V) : H →ₐ[R] Module.End R (Dual R V) :=
  .ofLinearMap (Dual.transpose.comp (ρ.toLinearMap.comp (antipode R)))
    (by ext φ v; simp [Dual.transpose_apply])
    (fun a b => by
      ext φ v
      simp [Dual.transpose_apply, antipode_mul_antidistrib, Module.End.mul_apply])

/-- The contragredient action on a functional is precomposition with the antipode action. -/
@[simp]
theorem hopfDual_apply (ρ : H →ₐ[R] Module.End R V) (a : H) (φ : Dual R V) (v : V) :
    ρ.hopfDual a φ v = φ (ρ (antipode R a) v) := (rfl)

/-- Evaluation into the double contragredient intertwines the action twisted by `S²`. -/
theorem hopfDual_hopfDual_eval (ρ : H →ₐ[R] Module.End R V) (a : H) (v : V) :
    ρ.hopfDual.hopfDual a (Dual.eval R V v) =
      Dual.eval R V (ρ (antipode R (antipode R a)) v) := by
  ext φ
  simp

variable [Module.IsReflexive R V]

/-- Evaluation after the action of a unit. When the unit implements the square of the
antipode, this is the intertwining equivalence with the double contragredient. -/
def unitEvalEquiv (ρ : H →ₐ[R] Module.End R V) (g : Hˣ) :
    V ≃ₗ[R] Dual R (Dual R V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R V (Units.map ρ.toMonoidHom g)).trans
    (Module.evalEquiv R V)

/-- The double-dual comparison sends `v` to the functional `φ ↦ φ(gv)`. -/
@[simp]
theorem unitEvalEquiv_apply (ρ : H →ₐ[R] Module.End R V) (g : Hˣ) (v : V)
    (φ : Dual R V) : ρ.unitEvalEquiv g v φ = φ (ρ (g : H) v) := (rfl)

/-- The inverse comparison evaluates the double functional, then acts by `g⁻¹`. -/
@[simp]
theorem unitEvalEquiv_symm_apply (ρ : H →ₐ[R] Module.End R V) (g : Hˣ)
    (Φ : Dual R (Dual R V)) :
    (ρ.unitEvalEquiv g).symm Φ = ρ (↑g⁻¹ : H) ((Module.evalEquiv R V).symm Φ) := (rfl)

/-- If `g` implements `S²`, the double-dual comparison intertwines the original action
with the double contragredient. -/
theorem unitEvalEquiv_intertwines (ρ : H →ₐ[R] Module.End R V) (g : Hˣ)
    (hg : ∀ a : H, antipode R (antipode R a) = (g : H) * a * ↑g⁻¹)
    (a : H) (v : V) :
    ρ.unitEvalEquiv g (ρ a v) = ρ.hopfDual.hopfDual a (ρ.unitEvalEquiv g v) := by
  have hcancel : ρ (↑g⁻¹ : H) (ρ (g : H) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  ext φ
  simp [hg, Module.End.mul_apply, hcancel]

end AlgHom

namespace LinearMap

variable {R H V W : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  {ρ : H →ₐ[R] Module.End R V} {σ : H →ₐ[R] Module.End R W}

/-- The transpose of an intertwiner intertwines the contragredients in the reverse direction. -/
theorem hopfDual_intertwines (f : V →ₗ[R] W)
    (hf : ∀ (a : H) (v : V), f (ρ a v) = σ a (f v)) (a : H) (φ : Dual R W) :
    f.dualMap (σ.hopfDual a φ) = ρ.hopfDual a (f.dualMap φ) := by
  ext v
  simp [hf]

variable [Module.IsReflexive R V] [Module.IsReflexive R W]

/-- Evaluation after a fixed unit is natural in intertwining maps. -/
theorem unitEvalEquiv_natural (f : V →ₗ[R] W)
    (hf : ∀ (a : H) (v : V), f (ρ a v) = σ a (f v)) (g : Hˣ) (v : V) :
    f.dualMap.dualMap (ρ.unitEvalEquiv g v) = σ.unitEvalEquiv g (f v) := by
  ext φ
  simp [hf]

end LinearMap
