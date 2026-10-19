/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.SubstInv
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Formal coordinates and automorphisms of power series rings

A formal coordinate over a commutative ring `R` is a power series `φ = u X + ⋯` with zero
constant coefficient and unit linear coefficient `u`. Under composition, `(φ * ψ) (X) = φ (ψ (X))`,
formal coordinates form a group `TauCeti.FormalCoordinate R`: the identity is `X`, and the inverse
of `φ` is Mathlib's compositional inverse `PowerSeries.substInvOfIsUnit`, whose coefficients are
determined recursively from the linear coefficient (`PowerSeries.substInvFun`) and which is the
unique compositional inverse (`PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X`). The linear
coefficient is a group homomorphism to `Rˣ`.

Each formal coordinate `φ` gives the substitution automorphism `σ_φ : f ↦ f (φ)` of the
`R`-algebra `R⟦X⟧`. Since `f (ψ) (φ) = f (ψ (φ))`, the automorphisms compose as
`σ_φ ∘ σ_ψ = σ_(ψ ∘ φ)`, so `φ ↦ σ_φ` reverses products: it is an injective group homomorphism
from formal coordinates to the opposite of the automorphism group `R⟦X⟧ ≃ₐ[R] R⟦X⟧`, whose
multiplication is composition. Every substitution automorphism preserves constant coefficients,
so it fixes the ideal `(X)` and induces the identity on `R⟦X⟧ / (X) = R`.

Over a field `K` the dictionary is complete. Every `K`-algebra endomorphism `σ` of `K⟦X⟧` sends
`X` to a series of zero constant coefficient, since `σ` maps the units `X - c`, `c ≠ 0`, to
units; hence `σ` is the substitution of `σ X`, without any continuity hypothesis
(`PowerSeries.algHom_eq_substAlgHom`). For an automorphism, `σ X` has a compositional inverse,
so its linear coefficient is nonzero. Thus `φ ↦ σ_φ` is an isomorphism between the formal
coordinates over `K` and the opposite of `K⟦X⟧ ≃ₐ[K] K⟦X⟧`, with inverse `σ ↦ σ X`.

## Main definitions

* `TauCeti.FormalCoordinate R`: the group of formal coordinates under composition.
* `TauCeti.FormalCoordinate.linearCoeff`: the linear coefficient, as a homomorphism to `Rˣ`.
* `TauCeti.FormalCoordinate.substAlgEquiv φ`: the substitution automorphism `f ↦ f (φ)`.
* `TauCeti.FormalCoordinate.substAlgEquivHom`: the antihomomorphism `φ ↦ σ_φ`.
* `TauCeti.FormalCoordinate.ofAlgEquiv σ`: over a field, the formal coordinate `σ X`.
* `TauCeti.FormalCoordinate.substAlgEquivMulEquiv K`: over a field, the isomorphism between
  formal coordinates and the opposite of the automorphism group of `K⟦X⟧`.

## Main results

* `TauCeti.FormalCoordinate.substAlgEquiv_mul`: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`.
* `TauCeti.FormalCoordinate.constantCoeff_substAlgEquiv`: substitution automorphisms preserve
  constant coefficients.
* `AlgHom.constantCoeff_apply_X`: over a field, every algebra endomorphism of `K⟦X⟧` sends `X`
  to a series of zero constant coefficient.
* `AlgHom.apply_eq_subst`: over a field, every algebra endomorphism `σ` of `K⟦X⟧` is the
  substitution of `σ X`.
* `TauCeti.FormalCoordinate.substAlgEquiv_ofAlgEquiv`: over a field, every automorphism of
  `K⟦X⟧` is the substitution of its value at `X`.
-/

public section

open PowerSeries

/-- Over a field `K`, every `K`-algebra endomorphism `σ` of `K⟦X⟧` sends `X` to a series of zero
constant coefficient: if `σ X` had constant coefficient `c ≠ 0`, the unit `X - c` would map to
the nonunit `σ X - c`. -/
theorem AlgHom.constantCoeff_apply_X {K : Type*} [Field K] (σ : K⟦X⟧ →ₐ[K] K⟦X⟧) :
    constantCoeff (σ X) = 0 := by
  by_contra hc
  have hu : IsUnit (X - C (constantCoeff (σ X)) : K⟦X⟧) := by
    simpa [isUnit_iff_constantCoeff] using hc
  have hσ : σ (X - C (constantCoeff (σ X))) = σ X - C (constantCoeff (σ X)) := by
    rw [map_sub, ← algebraMap_eq, AlgHom.commutes]
  simpa [hσ, isUnit_iff_constantCoeff] using hu.map σ

/-- Over a field `K`, every `K`-algebra endomorphism `σ` of `K⟦X⟧` is the substitution
`f ↦ f (σ X)`. -/
theorem AlgHom.apply_eq_subst {K : Type*} [Field K] (σ : K⟦X⟧ →ₐ[K] K⟦X⟧) (f : K⟦X⟧) :
    σ f = f.subst (σ X) := by
  rw [← coe_substAlgHom (.of_constantCoeff_zero' σ.constantCoeff_apply_X),
    ← algHom_eq_substAlgHom σ.constantCoeff_apply_X]

namespace TauCeti

/-- A formal coordinate over `R`: a power series `φ = u X + ⋯` with zero constant coefficient
and unit linear coefficient `u`. These are the changes of formal parameter `X ↦ φ`. -/
@[ext]
structure FormalCoordinate (R : Type*) [CommRing R] where
  /-- The power series `φ` of the coordinate change `X ↦ φ`. -/
  toPowerSeries : R⟦X⟧
  constantCoeff_toPowerSeries : constantCoeff toPowerSeries = 0
  isUnit_coeff_one : IsUnit (coeff 1 toPowerSeries)

namespace FormalCoordinate

variable {R : Type*} [CommRing R]

attribute [simp] constantCoeff_toPowerSeries

/-- Power series can be substituted into a formal coordinate. -/
theorem hasSubst (φ : FormalCoordinate R) : HasSubst φ.toPowerSeries :=
  .of_constantCoeff_zero' φ.constantCoeff_toPowerSeries

/-- The product `φ * ψ` of formal coordinates is the composite `φ ∘ ψ`, the series `φ (ψ)`. -/
noncomputable instance : Mul (FormalCoordinate R) where
  mul φ ψ :=
    { toPowerSeries := φ.toPowerSeries.subst ψ.toPowerSeries
      constantCoeff_toPowerSeries :=
        constantCoeff_subst_eq_zero ψ.constantCoeff_toPowerSeries _ φ.constantCoeff_toPowerSeries
      isUnit_coeff_one := by
        rw [coeff_one_subst ψ.constantCoeff_toPowerSeries, Algebra.algebraMap_self_apply]
        exact φ.isUnit_coeff_one.mul ψ.isUnit_coeff_one }

/-- The identity coordinate `X`. -/
noncomputable instance : One (FormalCoordinate R) where
  one := ⟨X, constantCoeff_X, by simp⟩

/-- The inverse of a formal coordinate is its compositional inverse. -/
noncomputable instance : Inv (FormalCoordinate R) where
  inv φ :=
    { toPowerSeries := φ.toPowerSeries.substInvOfIsUnit φ.isUnit_coeff_one
      constantCoeff_toPowerSeries := constantCoeff_substInvOfIsUnit _ _
      isUnit_coeff_one := by simp }

@[simp]
theorem toPowerSeries_mul (φ ψ : FormalCoordinate R) :
    (φ * ψ).toPowerSeries = φ.toPowerSeries.subst ψ.toPowerSeries := (rfl)

@[simp]
theorem toPowerSeries_one : (1 : FormalCoordinate R).toPowerSeries = X := (rfl)

@[simp]
theorem toPowerSeries_inv (φ : FormalCoordinate R) :
    φ⁻¹.toPowerSeries = φ.toPowerSeries.substInvOfIsUnit φ.isUnit_coeff_one := (rfl)

/-- Substituting `φ` and then `ψ` is substituting the composite `φ ∘ ψ = φ * ψ`. -/
theorem subst_subst (φ ψ : FormalCoordinate R) (f : R⟦X⟧) :
    PowerSeries.subst ψ.toPowerSeries (f.subst φ.toPowerSeries) = f.subst (φ * ψ).toPowerSeries :=
  subst_comp_subst_apply φ.hasSubst ψ.hasSubst f

/-- Formal coordinates form a group under composition. -/
noncomputable instance : Group (FormalCoordinate R) where
  mul_assoc φ ψ χ := FormalCoordinate.ext (subst_subst ψ χ _)
  one_mul φ := by
    ext1
    simp [subst_X φ.hasSubst]
  mul_one φ := by
    ext1
    simp
  inv_mul_cancel φ := by
    ext1
    simp [subst_substInvOfIsUnit_left _ φ.constantCoeff_toPowerSeries]

/-- The linear coefficient of a formal coordinate, as a homomorphism to the units of `R`. -/
noncomputable def linearCoeff : FormalCoordinate R →* Rˣ where
  toFun φ := φ.isUnit_coeff_one.unit
  map_one' := by ext; simp
  map_mul' φ ψ := by
    ext
    simp [coeff_one_subst ψ.constantCoeff_toPowerSeries]

@[simp]
theorem val_linearCoeff (φ : FormalCoordinate R) :
    (linearCoeff φ : R) = coeff 1 φ.toPowerSeries := (rfl)

/-- The substitution automorphism `σ_φ : f ↦ f (φ)` of `R⟦X⟧`, with inverse the substitution of
the compositional inverse of `φ`. -/
noncomputable def substAlgEquiv (φ : FormalCoordinate R) : R⟦X⟧ ≃ₐ[R] R⟦X⟧ :=
  .ofAlgHom (substAlgHom φ.hasSubst) (substAlgHom φ⁻¹.hasSubst)
    (AlgHom.ext fun f ↦ by
      rw [AlgHom.comp_apply, coe_substAlgHom, coe_substAlgHom, subst_subst, inv_mul_cancel]
      simp)
    (AlgHom.ext fun f ↦ by
      rw [AlgHom.comp_apply, coe_substAlgHom, coe_substAlgHom, subst_subst, mul_inv_cancel]
      simp)

@[simp]
theorem substAlgEquiv_apply (φ : FormalCoordinate R) (f : R⟦X⟧) :
    φ.substAlgEquiv f = f.subst φ.toPowerSeries := by
  simp [substAlgEquiv, coe_substAlgHom]

theorem substAlgEquiv_X (φ : FormalCoordinate R) : φ.substAlgEquiv X = φ.toPowerSeries := by
  simp [subst_X φ.hasSubst]

@[simp]
theorem substAlgEquiv_symm (φ : FormalCoordinate R) : φ.substAlgEquiv.symm = φ⁻¹.substAlgEquiv :=
  AlgEquiv.ext fun f ↦ by simp [substAlgEquiv, coe_substAlgHom]

/-- Substitution automorphisms reverse composition: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`, since
`f (φ (ψ)) = f (φ) (ψ)`. -/
theorem substAlgEquiv_mul (φ ψ : FormalCoordinate R) :
    (φ * ψ).substAlgEquiv = ψ.substAlgEquiv * φ.substAlgEquiv :=
  AlgEquiv.ext fun f ↦ by simp [subst_subst]

@[simp]
theorem substAlgEquiv_one : (1 : FormalCoordinate R).substAlgEquiv = 1 :=
  AlgEquiv.ext fun f ↦ by simp

/-- A formal coordinate is determined by its substitution automorphism. -/
theorem substAlgEquiv_injective :
    Function.Injective (substAlgEquiv : FormalCoordinate R → R⟦X⟧ ≃ₐ[R] R⟦X⟧) := fun φ ψ h ↦
  FormalCoordinate.ext <| by rw [← substAlgEquiv_X, h, substAlgEquiv_X]

/-- Substitution automorphisms preserve constant coefficients: they fix the ideal `(X)` and
induce the identity on `R⟦X⟧ / (X) = R`. -/
theorem constantCoeff_substAlgEquiv (φ : FormalCoordinate R) (f : R⟦X⟧) :
    constantCoeff (φ.substAlgEquiv f) = constantCoeff f := by
  rw [substAlgEquiv_apply]
  -- the multivariate constant coefficient of `f (φ)` is its univariate one
  exact (constantCoeff_subst_of_constantCoeff_zero φ.constantCoeff_toPowerSeries f).trans
    (Algebra.algebraMap_self_apply _)

/-- The map `φ ↦ σ_φ` from formal coordinates to the opposite of the automorphism group of `R⟦X⟧`.
It is a homomorphism because `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`. -/
noncomputable def substAlgEquivHom : FormalCoordinate R →* (R⟦X⟧ ≃ₐ[R] R⟦X⟧)ᵐᵒᵖ where
  toFun φ := .op φ.substAlgEquiv
  map_one' := by simp
  map_mul' φ ψ := by simp [substAlgEquiv_mul]

@[simp]
theorem substAlgEquivHom_apply (φ : FormalCoordinate R) :
    substAlgEquivHom φ = .op φ.substAlgEquiv := (rfl)

theorem substAlgEquivHom_injective :
    Function.Injective (substAlgEquivHom : FormalCoordinate R →* (R⟦X⟧ ≃ₐ[R] R⟦X⟧)ᵐᵒᵖ) :=
  MulOpposite.op_injective.comp substAlgEquiv_injective

section Field

variable {K : Type*} [Field K]

/-- Over a field, the formal coordinate `σ X` defined by an automorphism `σ` of `K⟦X⟧`. Its
linear coefficient is a unit because `σ⁻¹ X` is a compositional inverse of `σ X`. -/
noncomputable def ofAlgEquiv (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) : FormalCoordinate K where
  toPowerSeries := σ X
  constantCoeff_toPowerSeries := σ.toAlgHom.constantCoeff_apply_X
  isUnit_coeff_one := isUnit_coeff_one_of_subst_eq_X (P := σ.symm X)
    (.of_constantCoeff_zero' σ.toAlgHom.constantCoeff_apply_X)
    (by simpa using (σ.toAlgHom.apply_eq_subst (σ.symm X)).symm)

@[simp]
theorem toPowerSeries_ofAlgEquiv (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) : (ofAlgEquiv σ).toPowerSeries = σ X :=
  (rfl)

/-- Over a field, every automorphism of `K⟦X⟧` is the substitution of its value at `X`. -/
@[simp]
theorem substAlgEquiv_ofAlgEquiv (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) : (ofAlgEquiv σ).substAlgEquiv = σ :=
  AlgEquiv.ext fun f ↦ by simpa using (σ.toAlgHom.apply_eq_subst f).symm

@[simp]
theorem ofAlgEquiv_substAlgEquiv (φ : FormalCoordinate K) : ofAlgEquiv φ.substAlgEquiv = φ :=
  FormalCoordinate.ext φ.substAlgEquiv_X

variable (K) in
/-- Over a field, `φ ↦ σ_φ` is an isomorphism between the group of formal coordinates and the
opposite of the automorphism group of `K⟦X⟧`, with inverse `σ ↦ σ X`. -/
noncomputable def substAlgEquivMulEquiv : FormalCoordinate K ≃* (K⟦X⟧ ≃ₐ[K] K⟦X⟧)ᵐᵒᵖ where
  __ := substAlgEquivHom
  invFun σ := ofAlgEquiv σ.unop
  left_inv := ofAlgEquiv_substAlgEquiv
  right_inv σ := MulOpposite.unop_injective (substAlgEquiv_ofAlgEquiv σ.unop)

@[simp]
theorem substAlgEquivMulEquiv_apply (φ : FormalCoordinate K) :
    substAlgEquivMulEquiv K φ = .op φ.substAlgEquiv := (rfl)

@[simp]
theorem substAlgEquivMulEquiv_symm_apply (σ : (K⟦X⟧ ≃ₐ[K] K⟦X⟧)ᵐᵒᵖ) :
    (substAlgEquivMulEquiv K).symm σ = ofAlgEquiv σ.unop := (rfl)

end Field

end FormalCoordinate

end TauCeti
