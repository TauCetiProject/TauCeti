/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Data.PNat.Defs
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
coefficient is a group homomorphism to `Rˣ`; its kernel consists of the strict coordinates
`X + ∑_{i ≥ 1} bᵢ X^(i + 1)`, which correspond to arbitrary families `(bᵢ)` of coefficients.
Applying a ring homomorphism to the coefficients is a group homomorphism of formal coordinates.

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
* `TauCeti.FormalCoordinate.map f`: base change of formal coordinates along `f : R →+* S`.
* `TauCeti.FormalCoordinate.ofStrictCoeffs b`: the strict coordinate `X + ∑ bᵢ X^(i + 1)`.
* `TauCeti.FormalCoordinate.strictCoeffsEquiv`: strict coordinates correspond to their
  coefficient families `ℕ+ → R`.
* `TauCeti.FormalCoordinate.substAlgEquiv φ`: the substitution automorphism `f ↦ f (φ)`.
* `TauCeti.FormalCoordinate.substAlgEquivHom`: the antihomomorphism `φ ↦ σ_φ`.
* `TauCeti.FormalCoordinate.ofAlgEquiv σ`: over a field, the formal coordinate `σ X`.
* `TauCeti.FormalCoordinate.substAlgEquivMulEquiv K`: over a field, the isomorphism between
  formal coordinates and the opposite of the automorphism group of `K⟦X⟧`.

## Main results

* `TauCeti.FormalCoordinate.subst_subst_inv`, `TauCeti.FormalCoordinate.subst_inv_subst`:
  `φ (φ⁻¹ (x)) = x = φ⁻¹ (φ (x))` for every substitutable multivariate series `x`.
* `TauCeti.FormalCoordinate.substAlgEquiv_mul`: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`.
* `TauCeti.FormalCoordinate.map_substAlgEquiv`: substitution commutes with base change of the
  coefficients.
* `TauCeti.FormalCoordinate.constantCoeff_substAlgEquiv`: substitution automorphisms preserve
  constant coefficients.
* `TauCeti.FormalCoordinate.substAlgEquiv_ofAlgEquiv`: over a field, every automorphism of
  `K⟦X⟧` is the substitution of its value at `X`.
-/

public section

open PowerSeries

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

/-- A formal coordinate can be substituted into any power series. -/
theorem hasSubst (φ : FormalCoordinate R) : HasSubst φ.toPowerSeries :=
  .of_constantCoeff_zero' φ.constantCoeff_toPowerSeries

@[simp]
theorem X_subst_toPowerSeries (φ : FormalCoordinate R) :
    (X : R⟦X⟧).subst φ.toPowerSeries = φ.toPowerSeries :=
  subst_X φ.hasSubst

/-- Over a nontrivial ring a formal coordinate has order one. -/
@[simp]
theorem order_toPowerSeries [Nontrivial R] (φ : FormalCoordinate R) : φ.toPowerSeries.order = 1 :=
  order_eq_nat.mpr ⟨φ.isUnit_coeff_one.ne_zero, fun i hi ↦ by
    simp [Nat.lt_one_iff.mp hi]⟩

/-- Over a nontrivial ring a formal coordinate is a nonzero power series. -/
theorem toPowerSeries_ne_zero [Nontrivial R] (φ : FormalCoordinate R) : φ.toPowerSeries ≠ 0 :=
  fun h ↦ by simpa [h] using φ.isUnit_coeff_one

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
    simp
  mul_one φ := by
    ext1
    simp
  inv_mul_cancel φ := by
    ext1
    simp [subst_substInvOfIsUnit_left _ φ.constantCoeff_toPowerSeries]

/-- A formal coordinate composed with its inverse is `X`. -/
theorem toPowerSeries_mul_inv (φ : FormalCoordinate R) : (φ * φ⁻¹).toPowerSeries = X := by
  rw [mul_inv_cancel, toPowerSeries_one]

/-- The inverse of a formal coordinate composed with it is `X`. -/
theorem toPowerSeries_inv_mul (φ : FormalCoordinate R) : (φ⁻¹ * φ).toPowerSeries = X := by
  rw [inv_mul_cancel, toPowerSeries_one]

section Points

variable {σ : Type*} {x : MvPowerSeries σ R}

/-- A formal coordinate evaluated at a substitutable series `x` is again substitutable. -/
theorem hasSubst_subst (φ : FormalCoordinate R) (hx : HasSubst x) :
    HasSubst (PowerSeries.subst x φ.toPowerSeries) := by
  simpa [coe_substAlgHom] using φ.hasSubst.comp hx

/-- Evaluating the composite `φ ∘ ψ` at `x` is evaluating `φ` at `ψ (x)`. -/
theorem subst_toPowerSeries_mul (φ ψ : FormalCoordinate R) (hx : HasSubst x) :
    PowerSeries.subst x (φ * ψ).toPowerSeries =
      PowerSeries.subst (PowerSeries.subst x ψ.toPowerSeries) φ.toPowerSeries := by
  rw [toPowerSeries_mul, subst_comp_subst_apply ψ.hasSubst hx]

/-- `φ (φ⁻¹ (x)) = x`. -/
theorem subst_subst_inv (φ : FormalCoordinate R) (hx : HasSubst x) :
    PowerSeries.subst (PowerSeries.subst x φ⁻¹.toPowerSeries) φ.toPowerSeries = x := by
  rw [← subst_toPowerSeries_mul _ _ hx, mul_inv_cancel, toPowerSeries_one, subst_X hx]

/-- `φ⁻¹ (φ (x)) = x`. -/
theorem subst_inv_subst (φ : FormalCoordinate R) (hx : HasSubst x) :
    PowerSeries.subst (PowerSeries.subst x φ.toPowerSeries) φ⁻¹.toPowerSeries = x := by
  rw [← subst_toPowerSeries_mul _ _ hx, inv_mul_cancel, toPowerSeries_one, subst_X hx]

end Points

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
  simp

@[simp]
theorem substAlgEquiv_symm (φ : FormalCoordinate R) : φ.substAlgEquiv.symm = φ⁻¹.substAlgEquiv :=
  AlgEquiv.ext fun f ↦ by simp [substAlgEquiv, coe_substAlgHom]

/-- Substitution automorphisms reverse composition: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`, since
`f (φ (ψ)) = f (φ) (ψ)`. -/
@[simp]
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

/-- Substitution by a formal coordinate preserves constant coefficients. -/
@[simp]
theorem constantCoeff_subst_toPowerSeries (φ : FormalCoordinate R) (f : R⟦X⟧) :
    constantCoeff (f.subst φ.toPowerSeries) = constantCoeff f := by
  -- the multivariate constant coefficient of `f (φ)` is its univariate one
  exact (constantCoeff_subst_of_constantCoeff_zero φ.constantCoeff_toPowerSeries f).trans
    (Algebra.algebraMap_self_apply _)

/-- Substitution automorphisms preserve constant coefficients: they fix the ideal `(X)` and
induce the identity on `R⟦X⟧ / (X) = R`. -/
theorem constantCoeff_substAlgEquiv (φ : FormalCoordinate R) (f : R⟦X⟧) :
    constantCoeff (φ.substAlgEquiv f) = constantCoeff f := by
  simp

/-- The map `φ ↦ σ_φ` from formal coordinates to the opposite of the automorphism group of `R⟦X⟧`.
It is a homomorphism because `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`. -/
noncomputable def substAlgEquivHom : FormalCoordinate R →* (R⟦X⟧ ≃ₐ[R] R⟦X⟧)ᵐᵒᵖ where
  toFun φ := .op φ.substAlgEquiv
  map_one' := by simp
  map_mul' φ ψ := by simp

@[simp]
theorem substAlgEquivHom_apply (φ : FormalCoordinate R) :
    substAlgEquivHom φ = .op φ.substAlgEquiv := (rfl)

theorem substAlgEquivHom_injective :
    Function.Injective (substAlgEquivHom : FormalCoordinate R →* (R⟦X⟧ ≃ₐ[R] R⟦X⟧)ᵐᵒᵖ) :=
  MulOpposite.op_injective.comp substAlgEquiv_injective

section map

variable {S : Type*} [CommRing S]

/-- Base change of formal coordinates along a ring homomorphism `f : R →+* S`, applying `f` to
every coefficient. It is a group homomorphism since base change commutes with composition. -/
noncomputable def map (f : R →+* S) : FormalCoordinate R →* FormalCoordinate S where
  toFun φ :=
    { toPowerSeries := PowerSeries.map f φ.toPowerSeries
      constantCoeff_toPowerSeries := by
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
          φ.constantCoeff_toPowerSeries, map_zero]
      isUnit_coeff_one := by simpa using φ.isUnit_coeff_one.map f }
  map_one' := FormalCoordinate.ext (map_X f)
  map_mul' φ ψ := FormalCoordinate.ext (map_subst ψ.hasSubst _)

@[simp]
theorem toPowerSeries_map (f : R →+* S) (φ : FormalCoordinate R) :
    (map f φ).toPowerSeries = PowerSeries.map f φ.toPowerSeries := (rfl)

/-- Base change of formal coordinates along the identity changes nothing. -/
@[simp]
theorem map_id : map (RingHom.id R) = MonoidHom.id (FormalCoordinate R) :=
  MonoidHom.ext fun _ ↦ FormalCoordinate.ext rfl

/-- Successive base changes of a formal coordinate agree with base change along the composite. -/
theorem map_comp {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) (φ : FormalCoordinate R) :
    map (g.comp f) φ = map g (map f φ) :=
  FormalCoordinate.ext rfl

/-- Substitution is natural in the coefficients: base change along `f` carries `p (φ)` to the
substitution of the base-changed coordinate into the base-changed series. -/
theorem map_substAlgEquiv (f : R →+* S) (φ : FormalCoordinate R) (p : R⟦X⟧) :
    PowerSeries.map f (φ.substAlgEquiv p) = (map f φ).substAlgEquiv (PowerSeries.map f p) := by
  rw [substAlgEquiv_apply, substAlgEquiv_apply, toPowerSeries_map]
  -- `PowerSeries.map` is by definition `MvPowerSeries.map` over `Unit`, the form in which
  -- Mathlib states `PowerSeries.map_subst`
  exact map_subst φ.hasSubst p

end map

section Strict

/-- The strict formal coordinate `X + ∑_{i ≥ 1} bᵢ X^(i + 1)` with coefficients `b`. -/
noncomputable def ofStrictCoeffs (b : ℕ+ → R) : FormalCoordinate R where
  toPowerSeries :=
    PowerSeries.mk fun n ↦ if n = 0 then 0 else if n = 1 then 1 else b (n - 1).toPNat'
  constantCoeff_toPowerSeries := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    simp
  isUnit_coeff_one := by simp

@[simp]
theorem coeff_succ_ofStrictCoeffs (b : ℕ+ → R) (i : ℕ+) :
    coeff (i + 1) (ofStrictCoeffs b).toPowerSeries = b i := by
  simp [ofStrictCoeffs, i.ne_zero]

@[simp]
theorem coeff_one_ofStrictCoeffs (b : ℕ+ → R) : coeff 1 (ofStrictCoeffs b).toPowerSeries = 1 := by
  simp [ofStrictCoeffs]

/-- The coordinates `X + ∑ bᵢ X^(i + 1)` are strict: their linear coefficient is `1`. -/
theorem ofStrictCoeffs_mem_ker_linearCoeff (b : ℕ+ → R) :
    ofStrictCoeffs b ∈ (linearCoeff (R := R)).ker :=
  MonoidHom.mem_ker.mpr <| Units.ext <| coeff_one_ofStrictCoeffs b

/-- A strict formal coordinate, one with linear coefficient `1`, is determined by the coefficients
`bᵢ` of `X^(i + 1)`, `i ≥ 1`, and every family of them occurs: strict coordinates are the series
`X + ∑ bᵢ X^(i + 1)`. -/
noncomputable def strictCoeffsEquiv : (ℕ+ → R) ≃ (linearCoeff (R := R)).ker where
  toFun b := ⟨ofStrictCoeffs b, ofStrictCoeffs_mem_ker_linearCoeff b⟩
  invFun φ i := coeff (i + 1) φ.1.toPowerSeries
  left_inv b := funext (coeff_succ_ofStrictCoeffs b)
  right_inv φ := by
    have h1 : coeff 1 φ.1.toPowerSeries = 1 := congrArg Units.val (MonoidHom.mem_ker.mp φ.2)
    refine Subtype.ext <| FormalCoordinate.ext <| PowerSeries.ext fun n ↦ ?_
    rcases n with _ | _ | n
    · simp [ofStrictCoeffs, coeff_zero_eq_constantCoeff_apply]
    · simp [ofStrictCoeffs, h1]
    · simp [ofStrictCoeffs, Nat.toPNat']

@[simp]
theorem coe_strictCoeffsEquiv_apply (b : ℕ+ → R) :
    (strictCoeffsEquiv b : FormalCoordinate R) = ofStrictCoeffs b := (rfl)

@[simp]
theorem strictCoeffsEquiv_symm_apply (φ : (linearCoeff (R := R)).ker) (i : ℕ+) :
    strictCoeffsEquiv.symm φ i = coeff (i + 1) φ.1.toPowerSeries := (rfl)

/-- Base change of `X + ∑ bᵢ X^(i + 1)` along `f` is `X + ∑ f(bᵢ) X^(i + 1)`. -/
@[simp]
theorem map_ofStrictCoeffs {S : Type*} [CommRing S] (f : R →+* S) (b : ℕ+ → R) :
    map f (ofStrictCoeffs b) = ofStrictCoeffs (f ∘ b) :=
  FormalCoordinate.ext <| PowerSeries.ext fun n ↦ by
    simp only [toPowerSeries_map, coeff_map, ofStrictCoeffs, coeff_mk, Function.comp_apply]
    split_ifs <;> simp

end Strict

section Field

variable {K : Type*} [Field K]

/-- Over a field, the formal coordinate `σ X` defined by an automorphism `σ` of `K⟦X⟧`. -/
noncomputable def ofAlgEquiv (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) : FormalCoordinate K where
  toPowerSeries := σ X
  constantCoeff_toPowerSeries := σ.toAlgHom.constantCoeff_apply_X
  -- The inverse image `σ⁻¹ X` is a compositional inverse of `σ X`.
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
