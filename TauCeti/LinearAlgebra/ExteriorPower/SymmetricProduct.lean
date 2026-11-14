/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.ExteriorPower.Square

/-!
# Symmetric exterior product of linear maps on the second exterior power

When `2` is invertible in a commutative ring `R`, any two linear maps `f, g : M →ₗ[R] N` induce a
linear map `exteriorPower.symmMap₂ f g : ⋀[R]^2 M →ₗ[R] ⋀[R]^2 N` determined on decomposable
bivectors by

`(f ∧ g)(u ∧ v) = ⅟2 • (f u ∧ g v + g u ∧ f v)`.

This is the polarized bilinear form associated with the quadratic assignment `f ↦ ⋀² f`:
`symmMap₂ f f = exteriorPower.map 2 f`, so in particular `symmMap₂ id id = id` (whereas omitting
the factor `⅟2` would send `id` to `2 • id`). Pairing an endomorphism `f` with `id` recovers half
the derivation action `exteriorPower.lieMap 2 f`.

In Riemannian geometry (`Besse, Section 1.G`), `symmMap₂` is the operator-side counterpart of the
Kulkarni–Nomizu product of symmetric bilinear forms, expressing the scalar curvature operator as a
multiple of `id ∧ id = id` and the traceless-Ricci curvature operator through `Ric₀ ∧ id`.

## Main definitions

* `exteriorPower.symmMap₂`: the symmetric bilinear map sending `f, g : M →ₗ[R] N` to
  `u ∧ v ↦ ⅟2 • (f u ∧ g v + g u ∧ f v)` on `⋀[R]^2 M →ₗ[R] ⋀[R]^2 N`.

## Main results

* `exteriorPower.symmMap₂_apply_ιMulti`: evaluation on a decomposable bivector `u ∧ v`.
* `exteriorPower.symmMap₂_comm`: symmetry in the two linear maps.
* `exteriorPower.symmMap₂_self` and `exteriorPower.symmMap₂_id`: `symmMap₂ f f = map 2 f` and
  `symmMap₂ id id = id`.
* `exteriorPower.symmMap₂_id_right` and `exteriorPower.symmMap₂_id_left`: comparison with
  `exteriorPower.lieMap 2`.
* `exteriorPower.map_comp_symmMap₂` and `exteriorPower.symmMap₂_comp_map`: naturality under
  post- and pre-composition.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
-/

public section

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private noncomputable def symmWedgeBilin (f g : M →ₗ[R] N) : M →ₗ[R] M →ₗ[R] ⋀[R]^2 N :=
  LinearMap.mk₂ R
    (fun u v ↦ ⅟(2 : R) • (ιMulti R 2 ![f u, g v] + ιMulti R 2 ![g u, f v]))
    (fun u₁ u₂ v ↦ by
      simp only [map_add, ιMulti_two_add_left]
      module)
    (fun c u v ↦ by
      simp only [map_smul, ιMulti_two_smul_left]
      module)
    (fun u v₁ v₂ ↦ by
      simp only [map_add, ιMulti_two_add_right]
      module)
    (fun c u v ↦ by
      simp only [map_smul, ιMulti_two_smul_right]
      module)

private theorem isAlt_symmWedgeBilin (f g : M →ₗ[R] N) : (symmWedgeBilin f g).IsAlt := fun x ↦ by
  simp only [symmWedgeBilin, LinearMap.mk₂_apply]
  have hswap : ![g x, f x] = ![f x, g x] ∘ Equiv.swap 0 1 := by
    funext i; fin_cases i <;> rfl
  rw [hswap, (ιMulti R 2).map_add_swap _ (by decide), smul_zero]

/-- The symmetric exterior product of two linear maps `f, g : M →ₗ[R] N` on the second exterior
power, characterized by `symmMap₂ f g (u ∧ v) = ⅟2 • (f u ∧ g v + g u ∧ f v)`. -/
noncomputable def symmMap₂ :
    (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) →ₗ[R] (⋀[R]^2 M →ₗ[R] ⋀[R]^2 N) :=
  LinearMap.mk₂ R
    (fun f g ↦ alternatingMapLinearEquiv (isAlt_symmWedgeBilin f g).toAlternatingMap)
    (fun f₁ f₂ g ↦ linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
        alternatingMapLinearEquiv_apply_ιMulti, LinearMap.IsAlt.toAlternatingMap_apply,
        symmWedgeBilin, LinearMap.mk₂_apply, ιMulti_two_add_left, ιMulti_two_add_right]
      module)
    (fun c f g ↦ linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
        alternatingMapLinearEquiv_apply_ιMulti, LinearMap.IsAlt.toAlternatingMap_apply,
        symmWedgeBilin, LinearMap.mk₂_apply, ιMulti_two_smul_left, ιMulti_two_smul_right]
      module)
    (fun f g₁ g₂ ↦ linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
        alternatingMapLinearEquiv_apply_ιMulti, LinearMap.IsAlt.toAlternatingMap_apply,
        symmWedgeBilin, LinearMap.mk₂_apply, ιMulti_two_add_left, ιMulti_two_add_right]
      module)
    (fun c f g ↦ linearMap_ext <| AlternatingMap.ext fun v ↦ by
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
        alternatingMapLinearEquiv_apply_ιMulti, LinearMap.IsAlt.toAlternatingMap_apply,
        symmWedgeBilin, LinearMap.mk₂_apply, ιMulti_two_smul_left, ιMulti_two_smul_right]
      module)

/-- On `u ∧ v`, `symmMap₂ f g` evaluates to `⅟2 • (f u ∧ g v + g u ∧ f v)`. -/
@[simp]
theorem symmMap₂_apply_ιMulti (f g : M →ₗ[R] N) (u v : M) :
    symmMap₂ f g (ιMulti R 2 ![u, v]) =
      ⅟(2 : R) • (ιMulti R 2 ![f u, g v] + ιMulti R 2 ![g u, f v]) := by
  simp [symmMap₂, symmWedgeBilin, alternatingMapLinearEquiv_apply_ιMulti,
    LinearMap.IsAlt.toAlternatingMap_apply]

/-- Tuple-indexed form of `symmMap₂_apply_ιMulti`. -/
theorem symmMap₂_apply_ιMulti_tuple (f g : M →ₗ[R] N) (v : Fin 2 → M) :
    symmMap₂ f g (ιMulti R 2 v) =
      ⅟(2 : R) • (ιMulti R 2 ![f (v 0), g (v 1)] + ιMulti R 2 ![g (v 0), f (v 1)]) := by
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hv]
  exact symmMap₂_apply_ιMulti f g (v 0) (v 1)

/-- `symmMap₂` is symmetric in its two linear-map arguments. -/
theorem symmMap₂_comm (f g : M →ₗ[R] N) : symmMap₂ f g = symmMap₂ g f :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    simp only [LinearMap.compAlternatingMap_apply, symmMap₂_apply_ιMulti_tuple, add_comm]

/-- On the diagonal `(f, f)`, `symmMap₂` agrees with `exteriorPower.map 2 f`. -/
@[simp]
theorem symmMap₂_self (f : M →ₗ[R] N) : symmMap₂ f f = map 2 f :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    simp only [LinearMap.compAlternatingMap_apply, symmMap₂_apply_ιMulti_tuple, map_apply_ιMulti]
    have hfv : f ∘ v = ![f (v 0), f (v 1)] := by funext i; fin_cases i <;> rfl
    rw [hfv, ← two_smul R, smul_smul, invOf_mul_self, one_smul]

/-- The symmetric exterior product of the identity with itself is the identity on `⋀[R]^2 M`. -/
theorem symmMap₂_id : symmMap₂ (LinearMap.id : M →ₗ[R] M) LinearMap.id = LinearMap.id := by
  rw [symmMap₂_self, map_id]

/-- Pairing an endomorphism `f` with `id` gives half the derivation action `lieMap 2 f`. -/
theorem symmMap₂_id_right (f : Module.End R M) :
    symmMap₂ f LinearMap.id = ⅟(2 : R) • lieMap 2 f :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [hv]
    simp only [LinearMap.compAlternatingMap_apply, symmMap₂_apply_ιMulti, LinearMap.id_apply,
      LinearMap.smul_apply, lieMap_two_apply_ιMulti]

/-- Pairing `id` with an endomorphism `f` gives half the derivation action `lieMap 2 f`. -/
theorem symmMap₂_id_left (f : Module.End R M) :
    symmMap₂ LinearMap.id f = ⅟(2 : R) • lieMap 2 f := by
  rw [symmMap₂_comm, symmMap₂_id_right]

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- Naturality of `symmMap₂` under post-composition with `map 2 h`. -/
theorem map_comp_symmMap₂ (h : N →ₗ[R] P) (f g : M →ₗ[R] N) :
    (map 2 h).comp (symmMap₂ f g) = symmMap₂ (h.comp f) (h.comp g) :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    have h₁ : h ∘ ![f (v 0), g (v 1)] = ![h (f (v 0)), h (g (v 1))] := by
      funext i; fin_cases i <;> rfl
    have h₂ : h ∘ ![g (v 0), f (v 1)] = ![h (g (v 0)), h (f (v 1))] := by
      funext i; fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      symmMap₂_apply_ιMulti_tuple, map_smul, map_add, map_apply_ιMulti, h₁, h₂]

/-- Naturality of `symmMap₂` under pre-composition with `map 2 h`. -/
theorem symmMap₂_comp_map (f g : N →ₗ[R] P) (h : M →ₗ[R] N) :
    (symmMap₂ f g).comp (map 2 h) = symmMap₂ (f.comp h) (g.comp h) :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by
    have hv : h ∘ v = ![h (v 0), h (v 1)] := by funext i; fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, map_apply_ιMulti, hv,
      symmMap₂_apply_ιMulti_tuple, Matrix.cons_val_zero, Matrix.cons_val_one]

end exteriorPower
