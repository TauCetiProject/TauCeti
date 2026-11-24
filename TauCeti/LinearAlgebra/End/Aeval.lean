/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Polynomials in intertwined endomorphisms

A (semi)linear map `f` intertwining two endomorphisms `g` and `g₂` intertwines every polynomial
in them: polynomial evaluation at `g₂` after `f` agrees with `f` after evaluation at `g`, with the
coefficients transported along the ring homomorphism of `f`. This extends Mathlib's
`Module.End.commute_pow_left_of_commute` from powers to polynomials. The linear case, where no
transport of coefficients is needed, is `Module.End.aeval_comp_of_comp_eq`.

Consequently a linear map intertwining two endomorphisms with coprime minimal polynomials is zero
(`Module.End.eq_zero_of_comp_eq_of_isCoprime_minpoly`): the minimal polynomial of the source
endomorphism kills it, while evaluated at the target endomorphism it is invertible.

Along a linear retract `π ∘ₗ σ = id`, polynomial evaluation with zero constant coefficient commutes
with extending an endomorphism by zero (`Module.End.aeval_comp_comp_of_comp_eq_id`), and for any
polynomial `P` with invertible constant coefficient `LinearMap.kerAevalCompCompEquiv` identifies
`ker P(σ ∘ₗ u ∘ₗ π)` with `ker P(u)`.
-/

public section

open Polynomial

namespace Module.End

section CommSemiring

variable {R M M₂ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂]

/-- A semilinear map intertwining two endomorphisms intertwines every polynomial in them, with
coefficients transported along the ring homomorphism. -/
theorem aeval_map_comp_of_comp_eq {R₂ : Type*} [CommSemiring R₂] [Module R₂ M₂] {σ : R →+* R₂}
    {f : M →ₛₗ[σ] M₂} {g : End R M} {g₂ : End R₂ M₂} (h : g₂.comp f = f.comp g) (p : R[X]) :
    (aeval g₂ (p.map σ)).comp f = f.comp (aeval g p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.map_add, LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n a =>
    ext x
    have hn := LinearMap.congr_fun (commute_pow_left_of_commute h n) x
    simp only [LinearMap.comp_apply] at hn
    simp [aeval_monomial, Algebra.algebraMap_eq_smul_one, hn]

/-- A linear map intertwining two endomorphisms intertwines every polynomial in them. -/
theorem aeval_comp_of_comp_eq [Module R M₂] {f : M →ₗ[R] M₂} {g : End R M} {g₂ : End R M₂}
    (h : g₂.comp f = f.comp g) (p : R[X]) : (aeval g₂ p).comp f = f.comp (aeval g p) := by
  simpa using aeval_map_comp_of_comp_eq h p

/-- Extending an endomorphism along a retract commutes with evaluating a polynomial whose constant
coefficient is zero: the polynomial vanishes on the kernel of the retraction. -/
theorem aeval_comp_comp_of_comp_eq_id [Module R M₂] {π : M₂ →ₗ[R] M} {σ : M →ₗ[R] M₂}
    (h : π ∘ₗ σ = LinearMap.id) (u : End R M) {B : R[X]} (hB0 : B.coeff 0 = 0) :
    aeval (σ ∘ₗ u ∘ₗ π) B = σ ∘ₗ aeval u B ∘ₗ π := by
  obtain ⟨Q, rfl⟩ := X_dvd_iff.2 hB0
  have hr : u.comp π = π.comp (σ ∘ₗ u ∘ₗ π) := by
    rw [← LinearMap.comp_assoc, ← LinearMap.comp_assoc, h, LinearMap.id_comp]
  have hQ := aeval_comp_of_comp_eq hr Q
  simp only [map_mul, aeval_X, mul_eq_comp, LinearMap.comp_assoc]
  rw [← hQ]

end CommSemiring

section CommRing

variable {R M M₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₂]
  [Module R M₂]

/-- A linear map intertwining two endomorphisms with coprime minimal polynomials is zero. -/
theorem eq_zero_of_comp_eq_of_isCoprime_minpoly {f : M →ₗ[R] M₂} {g : End R M} {g₂ : End R M₂}
    (h : g₂.comp f = f.comp g) (hc : IsCoprime (minpoly R g) (minpoly R g₂)) : f = 0 := by
  obtain ⟨u, v, huv⟩ := hc
  have hf : (aeval g₂ (minpoly R g)).comp f = 0 := by
    simpa using aeval_map_comp_of_comp_eq h (minpoly R g)
  have h₁ : aeval g₂ u * aeval g₂ (minpoly R g) = 1 := by
    simpa using congrArg (aeval g₂) huv
  calc f = (aeval g₂ u * aeval g₂ (minpoly R g)).comp f := by
        rw [h₁, Module.End.one_eq_id, LinearMap.id_comp]
    _ = 0 := by rw [Module.End.mul_eq_comp, LinearMap.comp_assoc, hf, LinearMap.comp_zero]

end CommRing

end Module.End

namespace LinearMap

variable {R M F : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid F]
  [Module R F]

/-- Along a linear retract `π ∘ₗ σ = id`, for any polynomial `P` with invertible constant
coefficient, the retraction and section identify `ker P(σ ∘ₗ u ∘ₗ π)` with `ker P(u)`. -/
noncomputable def kerAevalCompCompEquiv {π : F →ₗ[R] M} {σ : M →ₗ[R] F}
    (h : π ∘ₗ σ = LinearMap.id) (u : Module.End R M) {P : R[X]} (hP : IsUnit (P.coeff 0)) :
    ker (aeval (σ ∘ₗ u ∘ₗ π) P) ≃ₗ[R] ker (aeval u P) :=
  LinearEquiv.ofLinearMap
    ((π.comp (Submodule.subtype _)).codRestrict _ fun y ↦ mem_ker.mpr <| by
      have hr : u.comp π = π.comp (σ ∘ₗ u ∘ₗ π) := by rw [← comp_assoc, ← comp_assoc, h, id_comp]
      simpa [mem_ker.mp y.property] using
        LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hr P) (y : F))
    ((σ.comp (Submodule.subtype _)).codRestrict _ fun x ↦ mem_ker.mpr <| by
      have hs : (σ ∘ₗ u ∘ₗ π).comp σ = σ.comp u := by rw [comp_assoc, comp_assoc, h, comp_id]
      simpa [mem_ker.mp x.property] using
        LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hs P) (x : M))
    (LinearMap.ext fun x ↦ Subtype.ext (LinearMap.congr_fun h (x : M)))
    (LinearMap.ext fun y ↦ Subtype.ext <| by
      have hr : u.comp π = π.comp (σ ∘ₗ u ∘ₗ π) := by rw [← comp_assoc, ← comp_assoc, h, id_comp]
      have hπy : aeval u P (π y) = 0 := by
        simpa [mem_ker.mp y.property] using
          LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hr P) (y : F)
      have hdiv : π (aeval (σ ∘ₗ u ∘ₗ π) P.divX (y : F)) = aeval u P.divX (π y) :=
        (LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hr P.divX) (y : F)).symm
      have h₁ : σ (u (aeval u P.divX (π y))) + P.coeff 0 • (y : F) = 0 := by
        have hF :=
          LinearMap.congr_fun (congrArg (aeval (σ ∘ₗ u ∘ₗ π)) (X_mul_divX_add P).symm) (y : F)
        rw [mem_ker.mp y.property] at hF
        simpa [-X_mul_divX_add, Algebra.algebraMap_eq_smul_one, hdiv] using hF.symm
      have h₂ : σ (u (aeval u P.divX (π y))) + P.coeff 0 • σ (π y) = 0 := by
        have hM :=
          congrArg σ (LinearMap.congr_fun (congrArg (aeval u) (X_mul_divX_add P).symm) (π y))
        rw [hπy, map_zero] at hM
        simpa [-X_mul_divX_add, Algebra.algebraMap_eq_smul_one] using hM.symm
      have hsmul : P.coeff 0 • σ (π y) = P.coeff 0 • (y : F) := by
        rw [← add_zero (P.coeff 0 • σ (π y)), ← h₁, add_left_comm, ← add_assoc, h₂, zero_add]
      simpa [← mul_smul, hP.val_inv_mul] using congrArg ((↑hP.unit⁻¹ : R) • ·) hsmul)

/-- The polynomial-kernel equivalence along a retract applies the retraction. -/
@[simp] theorem coe_kerAevalCompCompEquiv_apply {π : F →ₗ[R] M} {σ : M →ₗ[R] F}
    (h : π ∘ₗ σ = LinearMap.id) (u : Module.End R M) {P : R[X]} (hP : IsUnit (P.coeff 0))
    (x : ker (aeval (σ ∘ₗ u ∘ₗ π) P)) : (kerAevalCompCompEquiv h u hP x : M) = π x := by
  simp [kerAevalCompCompEquiv]

/-- The inverse polynomial-kernel equivalence along a retract applies the section. -/
@[simp] theorem coe_kerAevalCompCompEquiv_symm_apply {π : F →ₗ[R] M} {σ : M →ₗ[R] F}
    (h : π ∘ₗ σ = LinearMap.id) (u : Module.End R M) {P : R[X]} (hP : IsUnit (P.coeff 0))
    (x : ker (aeval u P)) : ((kerAevalCompCompEquiv h u hP).symm x : F) = σ x := by
  simp [kerAevalCompCompEquiv]

end LinearMap
