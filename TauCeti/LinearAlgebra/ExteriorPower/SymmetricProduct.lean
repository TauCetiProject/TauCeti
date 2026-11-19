/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.ExteriorPower
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Symmetric exterior product of linear maps on the second exterior power

When `2` is invertible in a commutative ring `R`, any two linear maps `f, g : M →ₗ[R] N` induce
`exteriorPower.symmMap₂ f g : ⋀[R]^2 M →ₗ[R] ⋀[R]^2 N` given on pure wedges by
`(f ∧ g)(u ∧ v) = ⅟2 • (f u ∧ g v + g u ∧ f v)`. On the diagonal `symmMap₂ f f = map 2 f`, and
pairing an endomorphism with `id` gives half the derivation action `exteriorPower.lieMap 2`.

In Riemannian geometry (`Böhm–Wilking, Section 2`; cf. `Besse, Section 1.G` for the unnormalized
bilinear-form Kulkarni–Nomizu product `h ⊙ k`), this `⅟2`-normalized operator wedge product is the
operator-side counterpart of the Kulkarni–Nomizu product, expressing the scalar curvature operator
via `id ∧ id = id` and the traceless-Ricci operator via `Ric₀ ∧ id`.

## Main definitions

* `exteriorPower.symmMap₂`: `(f, g) ↦ (u ∧ v ↦ ⅟2 • (f u ∧ g v + g u ∧ f v))`.

## Main results

* `exteriorPower.symmMap₂_apply_ιMulti`, `exteriorPower.symmMap₂_comm`,
  `exteriorPower.symmMap₂_self`, `exteriorPower.symmMap₂_id_right`,
  `exteriorPower.symmMap₂_id_left`, `exteriorPower.symmMap₂_comp_symmMap₂`,
  `exteriorPower.map_comp_symmMap₂`, and `exteriorPower.symmMap₂_comp_map`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. 167 (2008), 1079–1097, Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
-/

public section

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private noncomputable def symmWedgeBilin (f g : M →ₗ[R] N) : M →ₗ[R] M →ₗ[R] ⋀[R]^2 N :=
  LinearMap.mk₂ R (fun u v ↦ ⅟(2 : R) • (ιMulti R 2 ![f u, g v] + ιMulti R 2 ![g u, f v]))
    (fun _ _ _ ↦ by simp only [map_add, ιMulti_two_add_left]; module)
    (fun _ _ _ ↦ by simp only [map_smul, ιMulti_two_smul_left]; module)
    (fun _ _ _ ↦ by simp only [map_add, ιMulti_two_add_right]; module)
    (fun _ _ _ ↦ by simp only [map_smul, ιMulti_two_smul_right]; module)

private theorem isAlt_symmWedgeBilin (f g : M →ₗ[R] N) : (symmWedgeBilin f g).IsAlt := fun x ↦ by
  simp [symmWedgeBilin, ιMulti_two_swap (f x) (g x)]

/-- The symmetric exterior product of two linear maps `f, g : M →ₗ[R] N` on the second exterior
power, characterized by `symmMap₂ f g (u ∧ v) = ⅟2 • (f u ∧ g v + g u ∧ f v)`. -/
noncomputable def symmMap₂ :
    (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) →ₗ[R] (⋀[R]^2 M →ₗ[R] ⋀[R]^2 N) := by
  refine LinearMap.mk₂ R (fun f g ↦ alternatingMapLinearEquiv
    (isAlt_symmWedgeBilin f g).toAlternatingMap) ?_ ?_ ?_ ?_ <;>
  refine fun _ _ _ ↦ linearMap_ext_ιMulti_two fun _ _ ↦ ?_ <;>
  simp only [LinearMap.add_apply, LinearMap.smul_apply, symmWedgeBilin,
    alternatingMapLinearEquiv_apply_ιMulti, LinearMap.IsAlt.toAlternatingMap_apply,
    LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, ιMulti_two_add_left,
    ιMulti_two_add_right, ιMulti_two_smul_left, ιMulti_two_smul_right] <;> module

/-- On `u ∧ v`, `symmMap₂ f g` evaluates to `⅟2 • (f u ∧ g v + g u ∧ f v)`. -/
@[simp] theorem symmMap₂_apply_ιMulti (f g : M →ₗ[R] N) (u v : M) :
    symmMap₂ f g (ιMulti R 2 ![u, v]) =
      ⅟(2 : R) • (ιMulti R 2 ![f u, g v] + ιMulti R 2 ![g u, f v]) := by
  simp [symmMap₂, symmWedgeBilin]

/-- Tuple-indexed form of `symmMap₂_apply_ιMulti`. -/
theorem symmMap₂_apply_ιMulti_tuple (f g : M →ₗ[R] N) (v : Fin 2 → M) :
    symmMap₂ f g (ιMulti R 2 v) =
      ⅟(2 : R) • (ιMulti R 2 ![f (v 0), g (v 1)] + ιMulti R 2 ![g (v 0), f (v 1)]) := by
  rw [← symmMap₂_apply_ιMulti, ← FinVec.etaExpand_eq v]; rfl

/-- `symmMap₂` is symmetric in its two linear-map arguments. -/
theorem symmMap₂_comm (f g : M →ₗ[R] N) : symmMap₂ f g = symmMap₂ g f :=
  linearMap_ext_ιMulti_two fun _ _ ↦ by simp only [symmMap₂_apply_ιMulti, add_comm]

/-- On the diagonal `(f, f)`, `symmMap₂` agrees with `exteriorPower.map 2 f`. -/
@[simp] theorem symmMap₂_self (f : M →ₗ[R] N) : symmMap₂ f f = map 2 f :=
  linearMap_ext_ιMulti_two fun _ _ ↦ by simp only [symmMap₂_apply_ιMulti, map_apply_ιMulti_two,
    ← two_smul R, smul_smul, invOf_mul_self, one_smul]

/-- Pairing an endomorphism `f` with `id` gives half the derivation action `lieMap 2 f`. -/
theorem symmMap₂_id_right (f : Module.End R M) :
    symmMap₂ f LinearMap.id = ⅟(2 : R) • lieMap 2 f :=
  linearMap_ext_ιMulti_two fun _ _ ↦ by simp only [symmMap₂_apply_ιMulti, LinearMap.id_apply,
    LinearMap.smul_apply, lieMap_two_apply_ιMulti]

/-- Pairing `id` with an endomorphism `f` gives half the derivation action `lieMap 2 f`. -/
theorem symmMap₂_id_left (f : Module.End R M) :
    symmMap₂ LinearMap.id f = ⅟(2 : R) • lieMap 2 f := by rw [symmMap₂_comm, symmMap₂_id_right]

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- Composition law for `symmMap₂`:
`(f₁ ∧ g₁) ∘ (f₂ ∧ g₂) = ⅟2 • ((f₁ ∘ f₂) ∧ (g₁ ∘ g₂) + (f₁ ∘ g₂) ∧ (g₁ ∘ f₂))`. -/
theorem symmMap₂_comp_symmMap₂ (f₁ g₁ : N →ₗ[R] P) (f₂ g₂ : M →ₗ[R] N) :
    (symmMap₂ f₁ g₁).comp (symmMap₂ f₂ g₂) =
      ⅟(2 : R) • (symmMap₂ (f₁.comp f₂) (g₁.comp g₂) + symmMap₂ (f₁.comp g₂) (g₁.comp f₂)) :=
  linearMap_ext_ιMulti_two fun _ _ ↦ by simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.add_apply, symmMap₂_apply_ιMulti, map_smul, map_add]; module

/-- Naturality of `symmMap₂` under post-composition with `map 2 h`. -/
theorem map_comp_symmMap₂ (h : N →ₗ[R] P) (f g : M →ₗ[R] N) :
    (map 2 h).comp (symmMap₂ f g) = symmMap₂ (h.comp f) (h.comp g) := by
  rw [← symmMap₂_self h, symmMap₂_comp_symmMap₂, symmMap₂_comm (h.comp g) (h.comp f), ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

/-- Naturality of `symmMap₂` under pre-composition with `map 2 h`. -/
theorem symmMap₂_comp_map (f g : N →ₗ[R] P) (h : M →ₗ[R] N) :
    (symmMap₂ f g).comp (map 2 h) = symmMap₂ (f.comp h) (g.comp h) := by
  rw [← symmMap₂_self h, symmMap₂_comp_symmMap₂, ← two_smul R, smul_smul, invOf_mul_self, one_smul]

end exteriorPower
