/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Group.Commutator
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
multiple of `e ^ 2 = 0`.

For two square-zero elements `e₁, e₂`, the group commutator of `σ₁ = 1 + e₁ a D` and
`σ₂ = 1 + e₂ b D` in the automorphism group, whose multiplication is composition, is

`σ₁ σ₂ σ₁⁻¹ σ₂⁻¹ = 1 + e₁ e₂ (a b' - b a') D`.

The vector field on the right is the commutator `[a D, b D] = (a b' - b a') D` of derivations, so
this fixes the sign relating composition of substitutions to the bracket of vector fields. Over
`S = DualNumber (DualNumber K) = K[ε₁, ε₂] / (ε₁², ε₂²)` this applies to `e₁ = ε₁` and `e₂ = ε₂`.

Over the dual numbers `R[ε]` of a commutative ring `R`, the infinitesimal substitutions are the
`R[ε]`-algebra automorphisms of `R[ε]⟦X⟧` that reduce to the identity modulo `ε` and preserve the
ideal `(X)`. They are exactly the automorphisms `1 + ε a D` for `a ∈ X R⟦X⟧`, and `a ↦ 1 + ε a D`
is an isomorphism from the additive group `X R⟦X⟧` onto this subgroup. The `ε`-coefficient of
`1 + ε a D` on `R⟦X⟧` is the derivation `a D` of `R⟦X⟧`, so this identifies the infinitesimal
substitutions with the derivations `X R⟦X⟧ D` vanishing at the origin.

## Main definitions

* `TauCeti.infinitesimalSubstAlgEquiv e he a`: the automorphism `f ↦ f + e a f'` of `S⟦X⟧`, the
  substitution `X ↦ X + e a`.
* `TauCeti.infinitesimalSubstitutions R`: the subgroup of `R[ε]`-algebra automorphisms of
  `R[ε]⟦X⟧` reducing to the identity modulo `ε` and preserving `(X)`.
* `TauCeti.infinitesimalSubstitutionsEquiv R`: the isomorphism `a ↦ 1 + ε a D` from the additive
  group `X R⟦X⟧` to `TauCeti.infinitesimalSubstitutions R`.

## Main results

* `TauCeti.infinitesimalSubstAlgEquiv_apply_eq_subst`: `1 + e a D` is the substitution
  `X ↦ X + e a`.
* `TauCeti.infinitesimalSubstAlgEquiv_add`: `1 + e (a + b) D = (1 + e a D) (1 + e b D)`.
* `TauCeti.infinitesimalSubstAlgEquiv_commutator_apply`: the commutator formula above.
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

/-- The commutator of infinitesimal substitutions: for square-zero `e₁, e₂`, the group commutator
`⁅σ₁, σ₂⁆ = σ₁ σ₂ σ₁⁻¹ σ₂⁻¹` of `σ₁ = 1 + e₁ a D` and `σ₂ = 1 + e₂ b D`, with multiplication given
by composition, is `1 + e₁ e₂ (a b' - b a') D`. -/
theorem infinitesimalSubstAlgEquiv_commutator_apply {e₁ e₂ : S} (he₁ : e₁ ^ 2 = 0)
    (he₂ : e₂ ^ 2 = 0) (a b f : S⟦X⟧) :
    ⁅infinitesimalSubstAlgEquiv e₁ he₁ a, infinitesimalSubstAlgEquiv e₂ he₂ b⁆ f =
      f + (e₁ * e₂) • ((a * d⁄dX b - b * d⁄dX a) * d⁄dX f) := by
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
  rw [commutatorElement_def, key, mul_inv_cancel_right, mul_inv_cancel_right,
    infinitesimalSubstAlgEquiv_apply]

end SquareZero

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
      ⟨_, X_dvd_iff.1 (Ideal.mem_span_singleton.1 a.toAdd.2), rfl⟩⟩
  invFun σ := .ofAdd ⟨mk fun n ↦ (coeff n (σ.1 X)).snd, by
    simpa only [Ideal.mem_span_singleton, X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply,
      coeff_mk, TrivSqZeroExt.snd_zero] using
      congr(TrivSqZeroExt.snd $(constantCoeff_apply_X_eq_zero R σ.2.2))⟩
  left_inv a := by
    ext n
    simp only [toAdd_ofAdd, coeff_mk, infinitesimalSubstAlgEquiv_X, snd_coeff_X_add_eps_smul]
  right_inv σ := by
    ext1
    exact (eq_infinitesimalSubstAlgEquiv R σ.2.1
      (constantCoeff_apply_X_eq_zero R σ.2.2)).symm
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

end TauCeti
