/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commutator
public import TauCeti.Algebra.DualNumber.Iterated
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
public import TauCeti.RingTheory.PowerSeries.Derivation
public import TauCeti.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Infinitesimal substitutions of power series

Let `S` be a commutative ring and `e ∈ S` with `e ^ 2 = 0`. For every power series `a`, the
substitution `X ↦ X + e a` is the automorphism `f ↦ f + e a f'` of the `S`-algebra `S⟦X⟧`: this
is the first-order Taylor formula `PowerSeries.subst_X_add_of_sq_eq_zero`. In operator notation it
is `1 + e a D`, where `D` is the formal derivative. For a fixed `e` these automorphisms compose by
adding the parameters, `(1 + e a D) (1 + e b D) = 1 + e (a + b) D`, because the cross term is a
multiple of `e ^ 2 = 0`. When `e * constantCoeff a = 0`, `X + e a` is a formal coordinate
(`TauCeti.FormalCoordinate.infinitesimal`) whose substitution automorphism is `1 + e a D`.

For two square-zero elements `e₁, e₂`, the group commutator of `σ₁ = 1 + e₁ a D` and
`σ₂ = 1 + e₂ b D` in the automorphism group, whose multiplication is operator composition, is

`σ₁ σ₂ σ₁⁻¹ σ₂⁻¹ = 1 + e₁ e₂ (a b' - b a') D`

(`TauCeti.commutatorElement_infinitesimalSubstAlgEquiv`). Because `φ ↦ σ_φ` is an
anti-homomorphism from `TauCeti.FormalCoordinate S` to the automorphism group, the commutator in the
coordinate composition group carries the opposite sign `b a' - a b'`
(`TauCeti.FormalCoordinate.commutatorElement_infinitesimal`).

Over the iterated dual numbers `R[ε][ε] = DualNumber (DualNumber R)`, identified with
`R[ε₁, ε₂] / (ε₁², ε₂²)` via `TauCeti.iteratedDualNumberMvPolynomialQuotientAlgEquiv`, the
generators `ε₁ = inl ε` and `ε₂ = ε` satisfy `ε₁ ^ 2 = ε₂ ^ 2 = 0` while their product
`ε₁ ε₂ = inl ε * ε` is part of an `R`-basis (`TauCeti.iteratedDualNumberBasis`). Specializing to
`σ₁ = 1 + ε₁ a D` and `σ₂ = 1 + ε₂ b D` for `a, b ∈ R⟦X⟧` yields
`⁅σ₁, σ₂⁆ = 1 + ε₁ ε₂ (a b' - b a') D`
(`TauCeti.iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv`), acting on `R⟦X⟧` by
`1 + ε₁ ε₂ ⁅a D, b D⁆`
(`TauCeti.iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv_apply_map`). Because
`ε₁ ε₂` is linearly independent over `R`, `a b' - b a'` is the unique series `c ∈ R⟦X⟧` with
`⁅σ₁, σ₂⁆ = 1 + ε₁ ε₂ c D`
(`TauCeti.iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv_eq_iff`), pinning the
operator-commutator sign.

Over the dual numbers `R[ε]` of a commutative ring `R`, the infinitesimal substitutions are the
`R[ε]`-algebra automorphisms of `R[ε]⟦X⟧` that reduce to the identity modulo `ε` and preserve the
ideal `(X)`. They are exactly the automorphisms `1 + ε a D` for `a ∈ X R⟦X⟧`, and `a ↦ 1 + ε a D`
is an isomorphism from the additive group `X R⟦X⟧` onto this subgroup. The `ε`-coefficient of
`1 + ε a D` on `R⟦X⟧` is the derivation `a D` of `R⟦X⟧`, so this identifies the infinitesimal
substitutions with the derivations `X R⟦X⟧ D` vanishing at the origin.

## Main definitions

* `TauCeti.infinitesimalSubstAlgEquiv e he a`: the automorphism `f ↦ f + e a f'` of `S⟦X⟧`, the
  substitution `X ↦ X + e a`.
* `TauCeti.FormalCoordinate.infinitesimal e he a ha`: the formal coordinate `X + e a` when
  `e * constantCoeff a = 0`.
* `TauCeti.infinitesimalSubstitutions R`: the subgroup of `R[ε]`-algebra automorphisms of
  `R[ε]⟦X⟧` reducing to the identity modulo `ε` and preserving `(X)`.
* `TauCeti.infinitesimalSubstitutionsEquiv R`: the isomorphism `a ↦ 1 + ε a D` from the additive
  group `X R⟦X⟧` to `TauCeti.infinitesimalSubstitutions R`.

## Main results

* `TauCeti.infinitesimalSubstAlgEquiv_apply_eq_subst`: `1 + e a D` is the substitution
  `X ↦ X + e a`.
* `TauCeti.infinitesimalSubstAlgEquiv_add`: `1 + e (a + b) D = (1 + e a D) (1 + e b D)`.
* `TauCeti.commutatorElement_infinitesimalSubstAlgEquiv`: `⁅1 + e₁ a D, 1 + e₂ b D⁆ =
  1 + e₁ e₂ (a b' - b a') D`.
* `TauCeti.FormalCoordinate.commutatorElement_infinitesimal`: in `FormalCoordinate S`,
  `⁅X + e₁ a, X + e₂ b⁆ = X + e₁ e₂ (b a' - a b')`.
* `TauCeti.iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv`: over `R[ε][ε]`,
  `⁅1 + ε₁ a D, 1 + ε₂ b D⁆ = 1 + ε₁ ε₂ (a b' - b a') D`.
* `TauCeti.iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv_eq_iff`: uniqueness of
  the commutator parameter `a b' - b a'` over `R[ε][ε]`.
* `TauCeti.infinitesimalSubstitutionsEquiv_apply_map`: the `ε`-coefficient of `1 + ε a D` on
  `R⟦X⟧` is the derivation `a D`.
-/

public section

open PowerSeries
open scoped commutatorElement

namespace TauCeti

section SquareZero

variable {S : Type*} [CommRing S] {e : S}

private theorem sq_smul_eq_zero (he : e ^ 2 = 0) (a : S⟦X⟧) : (e • a) ^ 2 = 0 := by
  rw [smul_pow, he, zero_smul]

private theorem hasSubst_X_add_smul (he : e ^ 2 = 0) (a : S⟦X⟧) : HasSubst (X + e • a) :=
  HasSubst.X'.add (.map ⟨2, sq_smul_eq_zero he a⟩ _)

/-- For a fixed square-zero `e`, the substitutions `X ↦ X + e a` compose by adding parameters. -/
private theorem substAlgHom_X_add_smul_comp (he : e ^ 2 = 0) (a b : S⟦X⟧) :
    (substAlgHom (hasSubst_X_add_smul he a)).comp (substAlgHom (hasSubst_X_add_smul he b)) =
      substAlgHom (hasSubst_X_add_smul he (a + b)) := by
  have hE : C e ^ 2 = 0 := by rw [← map_pow, he, map_zero]
  refine AlgHom.ext fun f ↦ ?_
  simp only [AlgHom.comp_apply, coe_substAlgHom, subst_X_add_of_sq_eq_zero (sq_smul_eq_zero he _),
    smul_mul_assoc, map_add, Derivation.map_smul]
  simp only [smul_eq_C_mul]
  linear_combination (a * d⁄dX (b * d⁄dX f)) * hE

private theorem substAlgHom_X_add_smul_comp_neg (he : e ^ 2 = 0) {a b : S⟦X⟧} (hab : a + b = 0) :
    (substAlgHom (hasSubst_X_add_smul he a)).comp (substAlgHom (hasSubst_X_add_smul he b)) =
      AlgHom.id S S⟦X⟧ := by
  refine (substAlgHom_X_add_smul_comp he a b).trans (AlgHom.ext fun f ↦ ?_)
  rw [coe_substAlgHom, subst_X_add_of_sq_eq_zero (sq_smul_eq_zero he _), hab]
  simp

/-- For `e` with `e ^ 2 = 0` and a power series `a`, the infinitesimal substitution
`1 + e a D : f ↦ f + e a f'` of `S⟦X⟧`, which is the substitution `X ↦ X + e a`. Its inverse is
`1 - e a D`. -/
noncomputable def infinitesimalSubstAlgEquiv (e : S) (he : e ^ 2 = 0) (a : S⟦X⟧) :
    S⟦X⟧ ≃ₐ[S] S⟦X⟧ :=
  .ofAlgHom (substAlgHom (hasSubst_X_add_smul he a)) (substAlgHom (hasSubst_X_add_smul he (-a)))
    (substAlgHom_X_add_smul_comp_neg he (add_neg_cancel a))
    (substAlgHom_X_add_smul_comp_neg he (neg_add_cancel a))

/-- `1 + e a D` acts by `f ↦ f + e a f'`. -/
@[simp]
theorem infinitesimalSubstAlgEquiv_apply (he : e ^ 2 = 0) (a f : S⟦X⟧) :
    infinitesimalSubstAlgEquiv e he a f = f + e • (a * d⁄dX f) := by
  rw [infinitesimalSubstAlgEquiv, AlgEquiv.ofAlgHom_apply, coe_substAlgHom,
    subst_X_add_of_sq_eq_zero (sq_smul_eq_zero he a), smul_mul_assoc]

/-- `1 + e a D` is the substitution `X ↦ X + e a`. -/
theorem infinitesimalSubstAlgEquiv_apply_eq_subst (he : e ^ 2 = 0) (a f : S⟦X⟧) :
    infinitesimalSubstAlgEquiv e he a f = f.subst (X + e • a) := by
  rw [infinitesimalSubstAlgEquiv_apply, subst_X_add_of_sq_eq_zero (sq_smul_eq_zero he a),
    smul_mul_assoc]

theorem infinitesimalSubstAlgEquiv_X (he : e ^ 2 = 0) (a : S⟦X⟧) :
    infinitesimalSubstAlgEquiv e he a X = X + e • a := by
  simp

/-- Multiplying by an element `e'` with `e' e = 0` kills the first-order part of `1 + e a D`, also
after differentiating. -/
private theorem smul_derivative_infinitesimalSubstAlgEquiv {e' : S} (he' : e' * e = 0)
    (he : e ^ 2 = 0) (a g : S⟦X⟧) :
    e' • d⁄dX (infinitesimalSubstAlgEquiv e he a g) = e' • d⁄dX g := by
  rw [infinitesimalSubstAlgEquiv_apply, map_add, Derivation.map_smul, smul_add, smul_smul, he',
    zero_smul, add_zero]

@[simp]
theorem infinitesimalSubstAlgEquiv_zero (he : e ^ 2 = 0) :
    infinitesimalSubstAlgEquiv e he 0 = 1 :=
  AlgEquiv.ext fun f ↦ by simp

@[simp]
theorem infinitesimalSubstAlgEquiv_zero_left (he : (0 : S) ^ 2 = 0) (a : S⟦X⟧) :
    infinitesimalSubstAlgEquiv 0 he a = 1 :=
  AlgEquiv.ext fun f ↦ by simp

/-- For a fixed square-zero `e`, infinitesimal substitutions compose by adding their parameters:
`1 + e (a + b) D = (1 + e a D) (1 + e b D)`. -/
theorem infinitesimalSubstAlgEquiv_add (he : e ^ 2 = 0) (a b : S⟦X⟧) :
    infinitesimalSubstAlgEquiv e he (a + b) =
      infinitesimalSubstAlgEquiv e he a * infinitesimalSubstAlgEquiv e he b :=
  AlgEquiv.ext fun f ↦ congr($(substAlgHom_X_add_smul_comp he a b) f).symm

@[simp]
theorem infinitesimalSubstAlgEquiv_symm (he : e ^ 2 = 0) (a : S⟦X⟧) :
    (infinitesimalSubstAlgEquiv e he a).symm = infinitesimalSubstAlgEquiv e he (-a) := by
  simp only [infinitesimalSubstAlgEquiv, AlgEquiv.ofAlgHom_symm, neg_neg]

@[simp]
theorem inv_infinitesimalSubstAlgEquiv (he : e ^ 2 = 0) (a : S⟦X⟧) :
    (infinitesimalSubstAlgEquiv e he a)⁻¹ = infinitesimalSubstAlgEquiv e he (-a) := by
  rw [AlgEquiv.aut_inv, infinitesimalSubstAlgEquiv_symm]

/-- The commutator of infinitesimal substitutions: for square-zero `e₁, e₂`, the group commutator
`⁅σ₁, σ₂⁆ = σ₁ σ₂ σ₁⁻¹ σ₂⁻¹` of `σ₁ = 1 + e₁ a D` and `σ₂ = 1 + e₂ b D`, with multiplication given
by composition, is `1 + e₁ e₂ (a b' - b a') D`. -/
@[simp]
theorem commutatorElement_infinitesimalSubstAlgEquiv {e₁ e₂ : S} (he₁ : e₁ ^ 2 = 0)
    (he₂ : e₂ ^ 2 = 0) (a b : S⟦X⟧) :
    ⁅infinitesimalSubstAlgEquiv e₁ he₁ a, infinitesimalSubstAlgEquiv e₂ he₂ b⁆ =
      infinitesimalSubstAlgEquiv (e₁ * e₂) (by rw [mul_pow, he₁, zero_mul])
        (a * d⁄dX b - b * d⁄dX a) := by
  have he : (e₁ * e₂) ^ 2 = 0 := by rw [mul_pow, he₁, zero_mul]
  have h₁ : e₁ * e₂ * e₁ = 0 := by rw [mul_right_comm, ← sq, he₁, zero_mul]
  have h₂ : e₁ * e₂ * e₂ = 0 := by rw [mul_assoc, ← sq, he₂, mul_zero]
  -- It suffices to show `σ₁ σ₂ = τ σ₂ σ₁` for `τ = 1 + e₁ e₂ (a b' - b a') D`. Applied to `f`,
  -- the first-order part of `τ` only sees `f'`, since `e₁ e₂` kills the first-order parts of
  -- `σ₁` and `σ₂`.
  have key : infinitesimalSubstAlgEquiv e₁ he₁ a * infinitesimalSubstAlgEquiv e₂ he₂ b =
      infinitesimalSubstAlgEquiv (e₁ * e₂) he (a * d⁄dX b - b * d⁄dX a) *
        infinitesimalSubstAlgEquiv e₂ he₂ b * infinitesimalSubstAlgEquiv e₁ he₁ a := by
    refine AlgEquiv.ext fun f ↦ ?_
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
      infinitesimalSubstAlgEquiv_apply he, ← mul_smul_comm,
      smul_derivative_infinitesimalSubstAlgEquiv h₂,
      smul_derivative_infinitesimalSubstAlgEquiv h₁]
    simp only [infinitesimalSubstAlgEquiv_apply, map_add, Derivation.map_smul, Derivation.leibniz,
      smul_eq_mul]
    simp only [smul_eq_C_mul, map_mul]
    ring
  rw [commutatorElement_def, key, mul_inv_cancel_right, mul_inv_cancel_right]

/-- Pointwise form of `TauCeti.commutatorElement_infinitesimalSubstAlgEquiv`. -/
theorem commutatorElement_infinitesimalSubstAlgEquiv_apply {e₁ e₂ : S} (he₁ : e₁ ^ 2 = 0)
    (he₂ : e₂ ^ 2 = 0) (a b f : S⟦X⟧) :
    ⁅infinitesimalSubstAlgEquiv e₁ he₁ a, infinitesimalSubstAlgEquiv e₂ he₂ b⁆ f =
      f + (e₁ * e₂) • ((a * d⁄dX b - b * d⁄dX a) * d⁄dX f) := by
  rw [commutatorElement_infinitesimalSubstAlgEquiv, infinitesimalSubstAlgEquiv_apply]

/-- Applying a ring homomorphism `φ : S →+* T` to coefficients intertwines
`TauCeti.infinitesimalSubstAlgEquiv`. -/
theorem map_infinitesimalSubstAlgEquiv_apply {T : Type*} [CommRing T] (φ : S →+* T)
    (he : e ^ 2 = 0) (a f : S⟦X⟧) :
    map φ (infinitesimalSubstAlgEquiv e he a f) =
      infinitesimalSubstAlgEquiv (φ e) (by rw [← map_pow, he, map_zero]) (map φ a) (map φ f) := by
  simp [smul_eq_C_mul, derivative_map]

/-- For a ring homomorphism `φ : R →+* S` and a square-zero `e : S`, the parameter `c ∈ R⟦X⟧`
of `1 + e (map φ c) D` is uniquely determined by the resulting automorphism of `S⟦X⟧` whenever
`r ↦ e * φ r` is injective. -/
theorem infinitesimalSubstAlgEquiv_map_injective {R : Type*} [CommRing R] (φ : R →+* S)
    (he : e ^ 2 = 0) (hφ : Function.Injective fun r : R ↦ e * φ r) :
    Function.Injective fun c : R⟦X⟧ ↦ infinitesimalSubstAlgEquiv e he (map φ c) := by
  intro c₁ c₂ h
  have hX : e • map φ c₁ = e • map φ c₂ := by
    have := congrArg (fun F : S⟦X⟧ ≃ₐ[S] S⟦X⟧ ↦ F X) h
    simpa only [infinitesimalSubstAlgEquiv_X, add_right_inj] using this
  ext n
  exact hφ <| by simpa only [coeff_smul, coeff_map, smul_eq_mul] using congrArg (coeff n) hX

end SquareZero

namespace FormalCoordinate

variable {S : Type*} [CommRing S]

/-- For `e` with `e ^ 2 = 0` and a power series `a` with `e * constantCoeff a = 0`, the
infinitesimal formal coordinate `X + e • a`, whose substitution automorphism is
`TauCeti.infinitesimalSubstAlgEquiv e he a`. -/
noncomputable def infinitesimal (e : S) (he : e ^ 2 = 0) (a : S⟦X⟧)
    (ha : e * constantCoeff a = 0) : FormalCoordinate S where
  toPowerSeries := X + e • a
  constantCoeff_toPowerSeries := by simp [ha]
  isUnit_coeff_one := by
    refine ⟨⟨1 + e * coeff 1 a, 1 - e * coeff 1 a, ?_, ?_⟩, by simp⟩
    · linear_combination -(coeff 1 a ^ 2) * he
    · linear_combination -(coeff 1 a ^ 2) * he

@[simp]
theorem toPowerSeries_infinitesimal {e : S} (he : e ^ 2 = 0) {a : S⟦X⟧}
    (ha : e * constantCoeff a = 0) :
    (infinitesimal e he a ha).toPowerSeries = X + e • a :=
  (rfl)

/-- The substitution automorphism of the formal coordinate `X + e • a` is
`TauCeti.infinitesimalSubstAlgEquiv e he a`. -/
@[simp]
theorem substAlgEquiv_infinitesimal {e : S} (he : e ^ 2 = 0) {a : S⟦X⟧}
    (ha : e * constantCoeff a = 0) :
    (infinitesimal e he a ha).substAlgEquiv = infinitesimalSubstAlgEquiv e he a :=
  AlgEquiv.ext fun f ↦
    (substAlgEquiv_apply _ f).trans (infinitesimalSubstAlgEquiv_apply_eq_subst he a f).symm

@[simp]
theorem infinitesimal_zero {e : S} (he : e ^ 2 = 0) :
    infinitesimal e he 0 (by simp) = 1 :=
  FormalCoordinate.ext (by simp)

@[simp]
theorem infinitesimal_zero_left (he : (0 : S) ^ 2 = 0) (a : S⟦X⟧) :
    infinitesimal 0 he a (zero_mul _) = 1 :=
  FormalCoordinate.ext (by simp)

/-- For a fixed square-zero `e`, infinitesimal formal coordinates compose by adding parameters. -/
theorem infinitesimal_add {e : S} (he : e ^ 2 = 0) {a b : S⟦X⟧}
    (ha : e * constantCoeff a = 0) (hb : e * constantCoeff b = 0) :
    infinitesimal e he (a + b) (by simp [mul_add, ha, hb]) =
      infinitesimal e he a ha * infinitesimal e he b hb :=
  substAlgEquiv_injective <| by
    rw [substAlgEquiv_mul, substAlgEquiv_infinitesimal, substAlgEquiv_infinitesimal,
      substAlgEquiv_infinitesimal, ← infinitesimalSubstAlgEquiv_add, add_comm]

@[simp]
theorem inv_infinitesimal {e : S} (he : e ^ 2 = 0) {a : S⟦X⟧} (ha : e * constantCoeff a = 0) :
    (infinitesimal e he a ha)⁻¹ = infinitesimal e he (-a) (by simp [ha]) :=
  substAlgEquiv_injective <| by
    rw [← substAlgEquiv_symm, substAlgEquiv_infinitesimal, infinitesimalSubstAlgEquiv_symm,
      substAlgEquiv_infinitesimal]

/-- In the coordinate composition group `TauCeti.FormalCoordinate S`, the commutator of `X + e₁ a`
and `X + e₂ b` carries `b a' - a b'`, the opposite sign to the operator commutator
`TauCeti.commutatorElement_infinitesimalSubstAlgEquiv`, by
`TauCeti.FormalCoordinate.substAlgEquiv_commutatorElement`. -/
@[simp]
theorem commutatorElement_infinitesimal {e₁ e₂ : S} (he₁ : e₁ ^ 2 = 0) (he₂ : e₂ ^ 2 = 0)
    {a b : S⟦X⟧} (ha : e₁ * constantCoeff a = 0) (hb : e₂ * constantCoeff b = 0) :
    ⁅infinitesimal e₁ he₁ a ha, infinitesimal e₂ he₂ b hb⁆ =
      infinitesimal (e₁ * e₂) (by rw [mul_pow, he₁, zero_mul])
        (b * d⁄dX a - a * d⁄dX b) (by
          rw [map_sub, map_mul, map_mul]
          linear_combination (e₁ * constantCoeff (d⁄dX a)) * hb -
            (e₂ * constantCoeff (d⁄dX b)) * ha) := by
  refine substAlgEquiv_injective ?_
  rw [substAlgEquiv_commutatorElement]
  simp [mul_comm e₂ e₁]

/-- The linear coefficient of `TauCeti.FormalCoordinate.infinitesimal e he a ha` is
`1 + e * coeff 1 a`. -/
theorem val_linearCoeff_infinitesimal {e : S} (he : e ^ 2 = 0) {a : S⟦X⟧}
    (ha : e * constantCoeff a = 0) :
    ((infinitesimal e he a ha).linearCoeff : S) = 1 + e * coeff 1 a := by
  simp

/-- Base change along a ring homomorphism preserves `TauCeti.FormalCoordinate.infinitesimal`. -/
@[simp]
theorem map_infinitesimal {T : Type*} [CommRing T] (φ : S →+* T) {e : S} (he : e ^ 2 = 0)
    {a : S⟦X⟧} (ha : e * constantCoeff a = 0) :
    map φ (infinitesimal e he a ha) =
      infinitesimal (φ e) (by rw [← map_pow, he, map_zero])
        (PowerSeries.map φ a)
        (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map,
              coeff_zero_eq_constantCoeff_apply, ← map_mul, ha, map_zero]) :=
  FormalCoordinate.ext (by simp [toPowerSeries_map, smul_eq_C_mul])

end FormalCoordinate

section DualNumber

open DualNumber

variable (R : Type*) [CommRing R]

private theorem snd_coeff_X_add_eps_smul (a : R⟦X⟧) (n : ℕ) :
    (coeff n (X + (ε : DualNumber R) • map (algebraMap R (DualNumber R)) a)).snd = coeff n a := by
  rw [map_add, coeff_X]
  split_ifs <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- A power series over `R[ε]` with reduction `X` modulo `ε` is `X + ε a` for the power series `a`
of its `ε`-coefficients. -/
private theorem eq_X_add_eps_smul {P : (DualNumber R)⟦X⟧}
    (hP : map (TrivSqZeroExt.fstHom R R R).toRingHom P = X) :
    P = X + (ε : DualNumber R) •
      map (algebraMap R (DualNumber R)) (mk fun n ↦ (coeff n P).snd) := by
  ext n : 1
  have hn : (coeff n P).fst = coeff n X := by simpa using congr(coeff n $hP)
  refine TrivSqZeroExt.ext ?_ ?_
  · simp only [hn, map_add, coeff_X]
    split_ifs <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · rw [snd_coeff_X_add_eps_smul, coeff_mk]

/-- An `R[ε]`-algebra automorphism of `R[ε]⟦X⟧` reducing to the identity modulo `ε` and sending
`X` to a series of zero constant coefficient is `1 + ε a D`, where `a` is the `ε`-coefficient of
the image of `X`. -/
private theorem eq_infinitesimalSubstAlgEquiv
    {σ : (DualNumber R)⟦X⟧ ≃ₐ[DualNumber R] (DualNumber R)⟦X⟧}
    (h₁ : ∀ f, map (TrivSqZeroExt.fstHom R R R).toRingHom (σ f) =
      map (TrivSqZeroExt.fstHom R R R).toRingHom f)
    (h₂ : constantCoeff (σ X) = 0) :
    σ = infinitesimalSubstAlgEquiv ε eps_pow_two
      (map (algebraMap R (DualNumber R)) (mk fun n ↦ (coeff n (σ X)).snd)) := by
  have hX := eq_X_add_eps_smul R ((h₁ X).trans (map_X _))
  have hσ := algHom_eq_substAlgHom (σ := σ.toAlgHom) (.of_constantCoeff_zero' h₂)
  refine AlgEquiv.ext fun f ↦ ?_
  rw [infinitesimalSubstAlgEquiv_apply_eq_subst, ← hX]
  simpa [coe_substAlgHom] using DFunLike.congr_fun hσ f

private theorem constantCoeff_apply_X_eq_zero
    {σ : (DualNumber R)⟦X⟧ ≃ₐ[DualNumber R] (DualNumber R)⟦X⟧}
    (h : ∀ f ∈ Ideal.span {(X : (DualNumber R)⟦X⟧)}, σ f ∈ Ideal.span {X}) :
    constantCoeff (σ X) = 0 := by
  simpa [Ideal.mem_span_singleton, X_dvd_iff] using h X (Ideal.mem_span_singleton_self X)

private theorem infinitesimalSubstAlgEquiv_map_mem {a : R⟦X⟧} (ha : constantCoeff a = 0) :
    (∀ f, map (TrivSqZeroExt.fstHom R R R).toRingHom
        (infinitesimalSubstAlgEquiv ε eps_pow_two (map (algebraMap R (DualNumber R)) a) f) =
      map (TrivSqZeroExt.fstHom R R R).toRingHom f) ∧
    ∀ f ∈ Ideal.span {(X : (DualNumber R)⟦X⟧)},
      infinitesimalSubstAlgEquiv ε eps_pow_two (map (algebraMap R (DualNumber R)) a) f ∈
        Ideal.span {X} := by
  refine ⟨fun f ↦ ?_, fun f hf ↦ ?_⟩
  · simp [smul_eq_C_mul]
  · rw [Ideal.mem_span_singleton] at hf ⊢
    have hXa : X ∣ map (algebraMap R (DualNumber R)) a := by
      rw [X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
        coeff_zero_eq_constantCoeff_apply, ha, map_zero]
    rw [infinitesimalSubstAlgEquiv_apply, smul_eq_C_mul]
    exact dvd_add hf (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hXa _) _)

/-- The infinitesimal substitutions over the dual numbers `R[ε]`: the `R[ε]`-algebra automorphisms
of `R[ε]⟦X⟧` that reduce to the identity modulo `ε` and preserve the ideal `(X)`. -/
noncomputable def infinitesimalSubstitutions :
    Subgroup ((DualNumber R)⟦X⟧ ≃ₐ[DualNumber R] (DualNumber R)⟦X⟧) where
  carrier := {σ | (∀ f, map (TrivSqZeroExt.fstHom R R R).toRingHom (σ f) =
      map (TrivSqZeroExt.fstHom R R R).toRingHom f) ∧
    ∀ f ∈ Ideal.span {(X : (DualNumber R)⟦X⟧)}, σ f ∈ Ideal.span {X}}
  mul_mem' {σ τ} hσ hτ := ⟨fun f ↦ (hσ.1 (τ f)).trans (hτ.1 f), fun f hf ↦ hσ.2 _ (hτ.2 f hf)⟩
  one_mem' := ⟨fun _ ↦ rfl, fun _ hf ↦ hf⟩
  inv_mem' {σ} hσ := by
    have h₂ := constantCoeff_apply_X_eq_zero R hσ.2
    rw [eq_infinitesimalSubstAlgEquiv R hσ.1 h₂, AlgEquiv.aut_inv,
      infinitesimalSubstAlgEquiv_symm, ← map_neg]
    exact infinitesimalSubstAlgEquiv_map_mem R (by simp [h₂])

/-- An automorphism of `R[ε]⟦X⟧` is an infinitesimal substitution exactly when it reduces to the
identity modulo `ε` and preserves the ideal `(X)`. -/
theorem mem_infinitesimalSubstitutions
    {σ : (DualNumber R)⟦X⟧ ≃ₐ[DualNumber R] (DualNumber R)⟦X⟧} :
    σ ∈ infinitesimalSubstitutions R ↔
      (∀ f, map (TrivSqZeroExt.fstHom R R R).toRingHom (σ f) =
        map (TrivSqZeroExt.fstHom R R R).toRingHom f) ∧
      ∀ f ∈ Ideal.span {(X : (DualNumber R)⟦X⟧)}, σ f ∈ Ideal.span {X} :=
  Iff.rfl

/-- An automorphism of `R[ε]⟦X⟧` is an infinitesimal substitution exactly when it is `1 + ε a D`
for some `a ∈ X R⟦X⟧`. -/
theorem mem_infinitesimalSubstitutions_iff
    {σ : (DualNumber R)⟦X⟧ ≃ₐ[DualNumber R] (DualNumber R)⟦X⟧} :
    σ ∈ infinitesimalSubstitutions R ↔ ∃ a : R⟦X⟧, constantCoeff a = 0 ∧
      σ = infinitesimalSubstAlgEquiv ε eps_pow_two (map (algebraMap R (DualNumber R)) a) := by
  refine mem_infinitesimalSubstitutions R |>.trans
    ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun ⟨a, ha, hσ⟩ ↦ hσ ▸ infinitesimalSubstAlgEquiv_map_mem R ha⟩
  have h₂ := constantCoeff_apply_X_eq_zero R h₂
  exact ⟨_, by simp [h₂], eq_infinitesimalSubstAlgEquiv R h₁ h₂⟩

/-- The infinitesimal substitutions over `R[ε]` are parametrized by the additive group
`X R⟦X⟧`, through `a ↦ 1 + ε a D`. The inverse reads off the `ε`-coefficient of the image of
`X`. -/
noncomputable def infinitesimalSubstitutionsEquiv :
    Multiplicative (Ideal.span {(X : R⟦X⟧)}) ≃* infinitesimalSubstitutions R where
  toFun a := ⟨infinitesimalSubstAlgEquiv ε eps_pow_two
      (map (algebraMap R (DualNumber R)) a.toAdd),
    (mem_infinitesimalSubstitutions_iff R).2
      ⟨_, X_dvd_iff.1 (Ideal.mem_span_singleton.1 a.toAdd.property), rfl⟩⟩
  invFun σ := .ofAdd ⟨mk fun n ↦ (coeff n (σ.val X)).snd, by
    simpa only [Ideal.mem_span_singleton, X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply,
      coeff_mk, TrivSqZeroExt.snd_zero] using
      congr(TrivSqZeroExt.snd $(constantCoeff_apply_X_eq_zero R σ.property.2))⟩
  left_inv a := by
    ext n
    simp only [toAdd_ofAdd, coeff_mk, infinitesimalSubstAlgEquiv_X, snd_coeff_X_add_eps_smul]
  right_inv σ := by
    ext1
    exact (eq_infinitesimalSubstAlgEquiv R σ.property.1
      (constantCoeff_apply_X_eq_zero R σ.property.2)).symm
  map_mul' a b := by
    ext1
    simp [infinitesimalSubstAlgEquiv_add]

@[simp]
theorem coe_infinitesimalSubstitutionsEquiv_apply (a : Multiplicative (Ideal.span {(X : R⟦X⟧)})) :
    (infinitesimalSubstitutionsEquiv R a : (DualNumber R)⟦X⟧ ≃ₐ[DualNumber R] (DualNumber R)⟦X⟧) =
      infinitesimalSubstAlgEquiv ε eps_pow_two (map (algebraMap R (DualNumber R)) a.toAdd) :=
  (rfl)

/-- The inverse of `TauCeti.infinitesimalSubstitutionsEquiv` reads off the `ε`-coefficient of the
image of `X`. -/
@[simp]
theorem coe_toAdd_infinitesimalSubstitutionsEquiv_symm_apply (σ : infinitesimalSubstitutions R) :
    (((infinitesimalSubstitutionsEquiv R).symm σ).toAdd : R⟦X⟧) =
      mk fun n ↦ (coeff n ((σ : (DualNumber R)⟦X⟧ ≃ₐ[DualNumber R] (DualNumber R)⟦X⟧) X)).snd :=
  (rfl)

/-- The `ε`-coefficient of the infinitesimal substitution `1 + ε a D` on `R⟦X⟧` is the derivation
`a D` of `R⟦X⟧`, which preserves `(X)` since `a ∈ X R⟦X⟧`. -/
theorem infinitesimalSubstitutionsEquiv_apply_map (a : Multiplicative (Ideal.span {(X : R⟦X⟧)}))
    (f : R⟦X⟧) :
    (infinitesimalSubstitutionsEquiv R a : (DualNumber R)⟦X⟧ ≃ₐ[DualNumber R] (DualNumber R)⟦X⟧)
        (map (algebraMap R (DualNumber R)) f) =
      map (algebraMap R (DualNumber R)) f +
        (ε : DualNumber R) •
          map (algebraMap R (DualNumber R)) (mkDerivation R (a.toAdd : R⟦X⟧) f) := by
  simp [derivative_map, mul_comm]

end DualNumber

section IteratedDualNumber

open DualNumber TrivSqZeroExt

variable {R : Type*} [CommRing R]

private theorem snd_snd_coeff_inl_eps_mul_eps_smul_map (g : R⟦X⟧) (n : ℕ) :
    (coeff n (((inl (ε : R[ε]) : R[ε][ε]) * ε) • map (algebraMap R R[ε][ε]) g)).snd.snd =
      coeff n g := by
  rw [map_smul, coeff_map, smul_eq_mul, ← Algebra.commutes, ← Algebra.smul_def,
    snd_snd_smul_inl_eps_mul_eps]

/-- Over `R[ε][ε]`, the parameter `c ∈ R⟦X⟧` of `1 + (inl ε * ε) c D` is uniquely determined by
the resulting automorphism of `R[ε][ε]⟦X⟧`. -/
theorem iteratedDualNumber_infinitesimalSubstAlgEquiv_inl_eps_mul_eps_injective :
    Function.Injective fun c : R⟦X⟧ ↦
      infinitesimalSubstAlgEquiv ((inl (ε : R[ε]) : R[ε][ε]) * ε) inl_eps_mul_eps_pow_two
        (map (algebraMap R R[ε][ε]) c) := by
  have h := @infinitesimalSubstAlgEquiv_map_injective R[ε][ε] _
    ((inl (ε : R[ε]) : R[ε][ε]) * ε) R _ (algebraMap R R[ε][ε]) inl_eps_mul_eps_pow_two
    fun _ _ h ↦ smul_inl_eps_mul_eps_injective <| by
      dsimp only at h
      rwa [← Algebra.commutes, ← Algebra.smul_def, ← Algebra.commutes, ← Algebra.smul_def] at h
  exact h

/-- Over the iterated dual numbers `R[ε][ε]`, the group commutator of `σ₁ = 1 + (inl ε) a D` and
`σ₂ = 1 + ε b D` in the automorphism group of `R[ε][ε]⟦X⟧` is `1 + (inl ε * ε) (a b' - b a') D`. -/
theorem iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv (a b : R⟦X⟧) :
    ⁅infinitesimalSubstAlgEquiv (inl (ε : R[ε])) inl_eps_pow_two (map (algebraMap R R[ε][ε]) a),
      infinitesimalSubstAlgEquiv (ε : R[ε][ε]) eps_pow_two (map (algebraMap R R[ε][ε]) b)⁆ =
      infinitesimalSubstAlgEquiv ((inl (ε : R[ε]) : R[ε][ε]) * ε) inl_eps_mul_eps_pow_two
        (map (algebraMap R R[ε][ε]) (a * d⁄dX b - b * d⁄dX a)) := by
  rw [commutatorElement_infinitesimalSubstAlgEquiv]
  simp [derivative_map]

/-- On power series over `R`, the commutator of `1 + (inl ε) a D` and `1 + ε b D` over `R[ε][ε]`
acts as `1 + (inl ε * ε) ⁅a D, b D⁆`. -/
theorem iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv_apply_map
    (a b f : R⟦X⟧) :
    ⁅infinitesimalSubstAlgEquiv (inl (ε : R[ε])) inl_eps_pow_two (map (algebraMap R R[ε][ε]) a),
      infinitesimalSubstAlgEquiv (ε : R[ε][ε]) eps_pow_two (map (algebraMap R R[ε][ε]) b)⁆
        (map (algebraMap R R[ε][ε]) f) =
      map (algebraMap R R[ε][ε]) f +
        ((inl (ε : R[ε]) : R[ε][ε]) * ε) •
          map (algebraMap R R[ε][ε]) (⁅mkDerivation R a, mkDerivation R b⁆ f) := by
  rw [iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv,
    infinitesimalSubstAlgEquiv_apply, lie_mkDerivation, mkDerivation_apply, smul_eq_mul,
    mul_comm (d⁄dX f)]
  simp [derivative_map]

/-- The `inl ε * ε` coordinate of the `n`-th coefficient of `⁅1 + (inl ε) a D, 1 + ε b D⁆ f` for
`f ∈ R⟦X⟧` is the `n`-th coefficient of `⁅a D, b D⁆ f`. -/
theorem snd_snd_coeff_iteratedDualNumber_commutatorElement_apply_map (a b f : R⟦X⟧) (n : ℕ) :
    (coeff n
      (⁅infinitesimalSubstAlgEquiv (inl (ε : R[ε])) inl_eps_pow_two (map (algebraMap R R[ε][ε]) a),
        infinitesimalSubstAlgEquiv (ε : R[ε][ε]) eps_pow_two (map (algebraMap R R[ε][ε]) b)⁆
          (map (algebraMap R R[ε][ε]) f))).snd.snd =
      coeff n (⁅mkDerivation R a, mkDerivation R b⁆ f) := by
  rw [iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv_apply_map, map_add,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, coeff_map,
    snd_snd_coeff_inl_eps_mul_eps_smul_map]
  simp [algebraMap_eq_inl']

/-- Because `inl ε * ε` is part of an `R`-basis of `R[ε][ε]`, `a b' - b a'` is the unique power
series `c ∈ R⟦X⟧` such that `⁅1 + (inl ε) a D, 1 + ε b D⁆ = 1 + (inl ε * ε) c D`. -/
theorem iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv_eq_iff
    (a b c : R⟦X⟧) :
    ⁅infinitesimalSubstAlgEquiv (inl (ε : R[ε])) inl_eps_pow_two (map (algebraMap R R[ε][ε]) a),
      infinitesimalSubstAlgEquiv (ε : R[ε][ε]) eps_pow_two (map (algebraMap R R[ε][ε]) b)⁆ =
      infinitesimalSubstAlgEquiv ((inl (ε : R[ε]) : R[ε][ε]) * ε) inl_eps_mul_eps_pow_two
        (map (algebraMap R R[ε][ε]) c) ↔
      c = a * d⁄dX b - b * d⁄dX a := by
  rw [iteratedDualNumber_commutatorElement_infinitesimalSubstAlgEquiv]
  exact ⟨fun h ↦
    (iteratedDualNumber_infinitesimalSubstAlgEquiv_inl_eps_mul_eps_injective h).symm,
    fun h ↦ h ▸ rfl⟩

end IteratedDualNumber

end TauCeti
