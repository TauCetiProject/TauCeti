/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PolynomialLaw.Basic

/-!
# The polynomial law of a linear map

An `R`-linear map `u : M →ₗ[R] N` induces the polynomial law `u.toPolynomialLaw : M →ₚₗ[R] N`
whose component at a commutative `R`-algebra `S` is the base change
`u.baseChange S : S ⊗[R] M → S ⊗[R] N`. These are exactly the polynomial laws which are homogeneous
of degree one (see `TauCeti.RingTheory.PolynomialLaw.Homogeneous`).

## Main declarations

* `LinearMap.toPolynomialLaw`: the polynomial law induced by a linear map.
* `LinearMap.toPolynomialLaw_toFun`: its component at an algebra in any universe is the base
  change of the linear map.
* `LinearMap.ground_toPolynomialLaw`, `LinearMap.toPolynomialLaw_injective`: the ground map of
  `u.toPolynomialLaw` is `u`, so a linear map is determined by its polynomial law.
* `LinearMap.toPolynomialLaw_id`, `LinearMap.toPolynomialLaw_comp`: compatibility with identities
  and composition.
* `LinearMap.toPolynomialLawₗ`: `LinearMap.toPolynomialLaw` as an `R`-linear map.

## References

* N. Roby, *Lois polynômes et lois formelles en théorie des modules*, Ann. Sci. École Norm.
  Sup. (3) 80 (1963), 213-348
-/

public section

noncomputable section

universe u

open TensorProduct

namespace LinearMap

variable {R : Type u} [CommSemiring R] {M N P : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- The polynomial law `M →ₚₗ[R] N` induced by an `R`-linear map `u`: its component at a
commutative `R`-algebra `S` is the base change `u.baseChange S : S ⊗[R] M → S ⊗[R] N`. -/
def toPolynomialLaw (u : M →ₗ[R] N) : M →ₚₗ[R] N where
  toFun' S _ _ := u.baseChange S
  isCompat' φ := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul s m => simp
    | add x y hx hy => simp_all

theorem toPolynomialLaw_toFun' (u : M →ₗ[R] N) (S : Type u) [CommSemiring S] [Algebra R S] :
    u.toPolynomialLaw.toFun' S = u.baseChange S :=
  (rfl)

/-- The component of `u.toPolynomialLaw` at an `R`-algebra in an arbitrary universe is the base
change of `u`. -/
@[simp]
theorem toPolynomialLaw_toFun (u : M →ₗ[R] N) (S : Type*) [CommSemiring S] [Algebra R S] :
    u.toPolynomialLaw.toFun S = u.baseChange S := by
  ext x
  obtain ⟨n, ψ, p, rfl⟩ := PolynomialLaw.exists_lift x
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.toFun'_eq_toFun, toPolynomialLaw_toFun']
  induction p using TensorProduct.inductionOn with
  | tmul s m => simp
  | add x y hx hy => simp_all

/-- The ground map of the polynomial law of a linear map `u` is `u`. -/
@[simp]
theorem ground_toPolynomialLaw (u : M →ₗ[R] N) : u.toPolynomialLaw.ground = u := by
  ext m
  simp [PolynomialLaw.ground_apply]

/-- A linear map is determined by its polynomial law. -/
theorem toPolynomialLaw_injective :
    Function.Injective (toPolynomialLaw : (M →ₗ[R] N) → M →ₚₗ[R] N) := fun u v huv ↦ by
  ext m
  simpa using congr(PolynomialLaw.ground $huv m)

@[simp]
theorem toPolynomialLaw_inj {u v : M →ₗ[R] N} : u.toPolynomialLaw = v.toPolynomialLaw ↔ u = v :=
  toPolynomialLaw_injective.eq_iff

/-- The identity linear map induces the identity polynomial law. -/
@[simp]
theorem toPolynomialLaw_id : (LinearMap.id : M →ₗ[R] M).toPolynomialLaw = PolynomialLaw.id := by
  ext S _ _ x
  simp only [toPolynomialLaw_toFun', PolynomialLaw.id_apply', baseChange_id, LinearMap.id_apply,
    id_eq]

/-- The polynomial law of `v ∘ₗ u` is the composite of the polynomial laws of `v` and `u`. -/
@[simp]
theorem toPolynomialLaw_comp (v : N →ₗ[R] P) (u : M →ₗ[R] N) :
    (v ∘ₗ u).toPolynomialLaw = v.toPolynomialLaw.comp u.toPolynomialLaw := by
  ext S _ _ x
  simp only [toPolynomialLaw_toFun', PolynomialLaw.comp_toFun', baseChange_comp,
    LinearMap.coe_comp]

@[simp]
theorem toPolynomialLaw_zero : (0 : M →ₗ[R] N).toPolynomialLaw = 0 := by
  ext S _ _ x
  simp

@[simp]
theorem toPolynomialLaw_add (u v : M →ₗ[R] N) :
    (u + v).toPolynomialLaw = u.toPolynomialLaw + v.toPolynomialLaw := by
  ext S _ _ x
  simp [baseChange_add]

@[simp]
theorem toPolynomialLaw_smul (r : R) (u : M →ₗ[R] N) :
    (r • u).toPolynomialLaw = r • u.toPolynomialLaw := by
  ext S _ _ x
  simp [baseChange_smul]

variable (R M N) in
/-- `LinearMap.toPolynomialLaw`, bundled as an `R`-linear map. -/
def toPolynomialLawₗ : (M →ₗ[R] N) →ₗ[R] M →ₚₗ[R] N where
  toFun := toPolynomialLaw
  map_add' := toPolynomialLaw_add
  map_smul' := toPolynomialLaw_smul

@[simp]
theorem toPolynomialLawₗ_apply (u : M →ₗ[R] N) : toPolynomialLawₗ R M N u = u.toPolynomialLaw :=
  (rfl)

theorem toPolynomialLawₗ_injective : Function.Injective (toPolynomialLawₗ R M N) :=
  toPolynomialLaw_injective

end LinearMap
