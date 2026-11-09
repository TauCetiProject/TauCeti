/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Affine equivalences

This file records computations with affine equivalences. In particular, identifying the
commutator of two homotheties as a translation supports affine representations that detect
infinite-order elements, such as those used for Euclidean triangle groups.

## Main definitions

* `AffineEquiv.semidirectSubgroup`: for a group `W` of linear automorphisms of a module `V` and a
  `W`-stable additive subgroup `L`, the affine automorphisms with linear part in `W` and
  translation part in `L`, a copy of the semidirect product `L ⋊ W` in the affine group.
* `AffineEquiv.toGL`: the embedding of the affine group of a commutative ring `R` into
  `GL (Fin 2) R` sending `x ↦ a * x + b` to the matrix `!![a, b; 0, 1]`.

## Main results

* `AffineEquiv.apply_eq_linear_add`: an affine equivalence between modules is its linear part
  followed by the translation by the image of `0`.
* `AffineEquiv.apply_eq_linear_one_mul_add`: an affine self-equivalence of a commutative ring is
  `x ↦ a * x + b`.
* `AffineEquiv.linear_mul_apply_one`: the linear coefficients `a` of affine self-equivalences of a
  commutative ring multiply as the maps compose.
* `TauCeti.AffineEquiv.commutatorElement_homothetyUnitsMulHom`: the commutator of
  homotheties about two points is a translation.
-/

public section

open scoped commutatorElement

namespace AffineEquiv

variable {k V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂]
  [Module k V₂]

/-- An affine equivalence between modules is its linear part followed by the translation by
`f 0`; this is `AffineMap.decomp` evaluated at a point. -/
theorem apply_eq_linear_add (f : V₁ ≃ᵃ[k] V₂) (x : V₁) : f x = f.linear x + f 0 :=
  congrFun f.toAffineMap.decomp x

/-- The inverse of an affine equivalence `f` between modules sends `0` to
`f.linear.symm (-f 0)`. -/
theorem symm_apply_zero (f : V₁ ≃ᵃ[k] V₂) : f.symm 0 = f.linear.symm (-f 0) := by
  rw [LinearEquiv.eq_symm_apply]
  exact eq_neg_of_add_eq_zero_left (by rw [← apply_eq_linear_add, apply_symm_apply])

/-- **The semidirect product `L ⋊ W` in the affine group.** For a group `W` of linear automorphisms
of a module `V` and an additive subgroup `L` stable under `W`, the affine automorphisms of `V`
whose linear part lies in `W` and whose translation part `f 0` lies in `L`. -/
def semidirectSubgroup (W : Subgroup (V₁ ≃ₗ[k] V₁)) (L : AddSubgroup V₁)
    (hL : ∀ w ∈ W, ∀ v ∈ L, w v ∈ L) : Subgroup (V₁ ≃ᵃ[k] V₁) where
  carrier := {f | f.linear ∈ W ∧ f 0 ∈ L}
  one_mem' := ⟨by rw [← linearHom_apply, map_one]; exact one_mem W, by simp [zero_mem L]⟩
  mul_mem' := by
    rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
    refine ⟨by rw [← linearHom_apply, map_mul]; exact mul_mem hf hg, ?_⟩
    rw [coe_mul, Function.comp_apply, apply_eq_linear_add f (g 0)]
    exact add_mem (hL _ hf _ hg0) hf0
  inv_mem' := by
    rintro f ⟨hf, hf0⟩
    have hlin : f⁻¹.linear = f.linear⁻¹ := by rw [← linearHom_apply, map_inv, linearHom_apply]
    refine ⟨hlin ▸ inv_mem hf, ?_⟩
    rw [inv_def, symm_apply_zero, ← LinearEquiv.coe_inv]
    exact hL _ (inv_mem hf) _ (neg_mem hf0)

@[simp]
theorem mem_semidirectSubgroup_iff {W : Subgroup (V₁ ≃ₗ[k] V₁)} {L : AddSubgroup V₁}
    {hL : ∀ w ∈ W, ∀ v ∈ L, w v ∈ L} {f : V₁ ≃ᵃ[k] V₁} :
    f ∈ semidirectSubgroup W L hL ↔ f.linear ∈ W ∧ f 0 ∈ L :=
  Iff.rfl

section Ring

variable {R : Type*}

/-- The linear coefficient `f.linear 1` of an affine self-equivalence of a nontrivial ring is
nonzero. -/
theorem linear_one_ne_zero [Ring R] [Nontrivial R] (f : R ≃ᵃ[R] R) : f.linear 1 ≠ 0 :=
  f.linear.map_ne_zero_iff.2 one_ne_zero

variable [CommRing R]

/-- The linear part of an affine self-equivalence of a commutative ring is multiplication by
`f.linear 1`. -/
theorem linear_apply_eq_linear_one_mul (f : R ≃ᵃ[R] R) (x : R) : f.linear x = f.linear 1 * x := by
  simpa [mul_comm] using f.linear.map_smul x 1

/-- An affine self-equivalence of a commutative ring is `x ↦ a * x + b`, with `a = f.linear 1` and
`b = f 0`. -/
theorem apply_eq_linear_one_mul_add (f : R ≃ᵃ[R] R) (x : R) : f x = f.linear 1 * x + f 0 := by
  rw [apply_eq_linear_add f x, linear_apply_eq_linear_one_mul]

/-- The linear coefficient `f.linear 1` of an affine self-equivalence of a commutative ring is a
unit, with inverse `f.linear.symm 1`. -/
theorem isUnit_linear_one (f : R ≃ᵃ[R] R) : IsUnit (f.linear 1) :=
  IsUnit.of_mul_eq_one (f.linear.symm 1) <| by
    rw [← linear_apply_eq_linear_one_mul, LinearEquiv.apply_symm_apply]

/-- The linear coefficients of affine self-equivalences of a commutative ring multiply as the maps
compose. -/
theorem linear_mul_apply_one (f g : R ≃ᵃ[R] R) : (f * g).linear 1 = f.linear 1 * g.linear 1 :=
  linear_apply_eq_linear_one_mul f (g.linear 1)

/-- The invertible matrix `!![a, b; 0, 1]` of an affine self-equivalence `x ↦ a * x + b` of a
commutative ring. The matrices of affine maps multiply as the maps compose. -/
noncomputable def toGL : (R ≃ᵃ[R] R) →* GL (Fin 2) R where
  toFun f := Matrix.GeneralLinearGroup.mk'' !![f.linear 1, f 0; 0, 1]
    (by simpa [Matrix.det_fin_two_of] using f.isUnit_linear_one)
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [one_def]
  map_mul' f g := by
    have h0 : (f * g) 0 = f.linear 1 * g 0 + f 0 := by
      rw [coe_mul, Function.comp_apply, apply_eq_linear_one_mul_add f]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [linear_mul_apply_one, h0, Matrix.mul_apply, Fin.sum_univ_two]

/-- The matrix of an affine self-equivalence `x ↦ a * x + b` is `!![a, b; 0, 1]`. -/
@[simp]
theorem coe_toGL (f : R ≃ᵃ[R] R) :
    (toGL f : Matrix (Fin 2) (Fin 2) R) = !![f.linear 1, f 0; 0, 1] := by
  simp [toGL]

end Ring

end AffineEquiv

namespace TauCeti

namespace AffineEquiv

variable {R V P : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- The commutator of homotheties with ratios `ω` and `η` about `p` and `q`, respectively, is
translation by `((ω - 1) * (1 - η)) • (q -ᵥ p)`. -/
@[simp]
theorem commutatorElement_homothetyUnitsMulHom (p q : P) (ω η : Rˣ) :
    ⁅_root_.AffineEquiv.homothetyUnitsMulHom p ω, _root_.AffineEquiv.homothetyUnitsMulHom q η⁆ =
      _root_.AffineEquiv.constVAdd R P ((((ω : R) - 1) * (1 - η)) • (q -ᵥ p)) := by
  rw [commutatorElement_def, ← map_inv, ← map_inv]
  ext z
  -- Write every point as a vector based at `p`, reducing to a computation in `V`.
  rw [← vsub_vadd q p, ← vsub_vadd z p]
  generalize q -ᵥ p = u
  generalize z -ᵥ p = w
  simp only [_root_.AffineEquiv.coe_mul, Function.comp_apply,
    _root_.AffineEquiv.coe_homothetyUnitsMulHom_apply, AffineMap.homothety_apply,
    _root_.AffineEquiv.constVAdd_apply, vadd_vsub_vadd_cancel_right, vadd_vadd, vadd_vsub]
  congr 1
  linear_combination (norm := module)
    ω.mul_inv • (((η : R) * ↑η⁻¹) • (w - u) + (η : R) • u) + η.mul_inv • (w - u)

end AffineEquiv

end TauCeti
