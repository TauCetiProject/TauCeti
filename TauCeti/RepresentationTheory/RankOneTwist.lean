/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LinHom.Basic

/-!
# Removing a rank-one twist

For a one-dimensional representation `V`, a linear equivalence `e : V ≃ k` identifies
`V⁺ ⊗ P` with `Hom(V, P)`. This file packages the elementary equivariance calculation used
when an isomorphism `P ≃ H` is equivariant up to the character of `V`.

## Main definitions

* `LinearEquiv.rankOneHomEquiv`: the coordinate isomorphism `P ≃ Hom(V, P)`.
* `Representation.rankOneTwistEquiv`: an isomorphism `H ≃ V⁺ ⊗ P` from an isomorphism
  `P ≃ H` equivariant up to the character of `V`.
-/

public section

open scoped TensorProduct

noncomputable section

universe u v w x

variable {k : Type u} {G : Type v}

section CommSemiring

variable [CommSemiring k]
  {V : Type w} [AddCommMonoid V] [Module k V]
  {P : Type x} [AddCommMonoid P] [Module k P]

namespace LinearEquiv

-- Adapted from the Tau Ceti lookahead branch
-- `lookahead/ClassFieldTheory/kummer-equiv-mixed-equivariant` (split 1).
/-- A choice of coordinate on a rank-one module identifies a vector with the linear map obtained
by multiplying that coordinate by the vector. -/
def rankOneHomEquiv (e : V ≃ₗ[k] k) : P ≃ₗ[k] V →ₗ[k] P :=
  (LinearMap.ringLmapEquivSelf k k P).symm.trans
    (e.symm.arrowCongr (LinearEquiv.refl k P))

/-- Evaluation of the coordinate identification `P ≃ Hom(V, P)`. -/
@[simp]
theorem rankOneHomEquiv_apply_apply (e : V ≃ₗ[k] k) (x : P) (v : V) :
    e.rankOneHomEquiv x v = e v • x :=
  by simp [rankOneHomEquiv]

/-- The inverse coordinate identification evaluates a linear map on the vector with coordinate
`1`. -/
@[simp]
theorem rankOneHomEquiv_symm_apply (e : V ≃ₗ[k] k) (f : V →ₗ[k] P) :
    e.rankOneHomEquiv.symm f = f (e.symm 1) :=
  by simp [rankOneHomEquiv]

end LinearEquiv

namespace Representation

section Monoid

variable [Monoid G]

-- Adapted from the Tau Ceti lookahead branch
-- `lookahead/ClassFieldTheory/kummer-equiv-mixed-equivariant` (split 1).
/-- The character through which a monoid acts on a representation with a chosen rank-one
coordinate: `g` acts by the coordinate of the image of the vector with coordinate `1`. -/
def rankOneCharacter (rho : Representation k G V) (e : V ≃ₗ[k] k) : G →* k where
  toFun g := e (rho g (e.symm 1))
  map_one' := by simp
  map_mul' g h := by
    have hv : rho h (e.symm 1) = e (rho h (e.symm 1)) • e.symm 1 := e.injective (by simp)
    rw [map_mul, Module.End.mul_apply]
    nth_rw 1 [hv]
    rw [map_smul, map_smul, smul_eq_mul, mul_comm]

/-- The value of the rank-one character at `g` is the coordinate of `g` applied to the vector
with coordinate `1`. -/
@[simp]
theorem rankOneCharacter_apply (rho : Representation k G V) (e : V ≃ₗ[k] k) (g : G) :
    rankOneCharacter rho e g = e (rho g (e.symm 1)) := by
  unfold rankOneCharacter
  rfl

/-- A representation on a module with a coordinate `V ≃ k` acts through its rank-one
character. -/
theorem rankOneCharacter_smul (rho : Representation k G V) (e : V ≃ₗ[k] k)
    (g : G) (v : V) :
    rho g v = rankOneCharacter rho e g • v := by
  have hv : v = e v • e.symm 1 := by
    apply e.injective
    simp
  rw [hv, map_smul, rankOneCharacter_apply]
  apply e.injective
  simp [mul_comm]

end Monoid

section Group

variable [Group G]

/-- The rank-one character of a group representation takes unit values. -/
theorem isUnit_rankOneCharacter (rho : Representation k G V) (e : V ≃ₗ[k] k) (g : G) :
    IsUnit (rankOneCharacter rho e g) :=
  (Group.isUnit g).map (rankOneCharacter rho e)

/-- The rank-one character of a representation is nonzero. -/
theorem rankOneCharacter_ne_zero [Nontrivial k]
    (rho : Representation k G V) (e : V ≃ₗ[k] k)
    (g : G) :
    rankOneCharacter rho e g ≠ 0 :=
  (isUnit_rankOneCharacter rho e g).ne_zero

variable {H : Type*} [AddCommMonoid H] [Module k H]

-- Adapted from the Tau Ceti lookahead branch
-- `lookahead/ClassFieldTheory/kummer-equiv-mixed-equivariant` (split 1).
/-- **Removal of a rank-one twist.** If `Psi : P ≃ H` satisfies
`chi(g) · g(Psi x) = Psi(gx)` for the character of the rank-one representation `rho`, then
`H` is equivariantly isomorphic to `rho⁺ ⊗ P`. -/
def rankOneTwistEquiv (rho : Representation k G V) (sigma : Representation k G P)
    (tau : Representation k G H) (e : V ≃ₗ[k] k) (Psi : P ≃ₗ[k] H)
    (hPsi : ∀ (g : G) (x : P),
      rankOneCharacter rho e g • tau g (Psi x) = Psi (sigma g x)) :
    tau.Equiv (rho.dual.tprod sigma) :=
  haveI : Module.Finite k V := Module.Finite.equiv e.symm
  haveI : Module.Projective k V := Module.Projective.of_equiv' e.symm
  (Representation.Equiv.mk (Psi.symm.trans e.rankOneHomEquiv) fun g ↦ by
    ext y v
    have htwist : rankOneCharacter rho e g • Psi.symm (tau g y) = sigma g (Psi.symm y) := by
      rw [← map_smul, ← Psi.symm_apply_apply (sigma g _), ← hPsi, Psi.apply_symm_apply]
    have hinv : e (rho g⁻¹ v) = rankOneCharacter rho e g⁻¹ * e v := by
      rw [rankOneCharacter_smul rho e g⁻¹ v, map_smul, smul_eq_mul]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      Representation.linHom_apply, LinearEquiv.rankOneHomEquiv_apply_apply, hinv, map_smul,
      ← htwist, smul_smul]
    rw [mul_right_comm, ← map_mul, inv_mul_cancel, map_one, one_mul]).trans
    (Representation.Equiv.dualTensorHomOfProjective rho sigma).symm

/-- After contraction, the twist-removal equivalence sends `y` to the coordinate map of
`Psi⁻¹ y`. -/
@[simp]
theorem dualTensorHom_rankOneTwistEquiv (rho : Representation k G V)
    (sigma : Representation k G P) (tau : Representation k G H) (e : V ≃ₗ[k] k)
    (Psi : P ≃ₗ[k] H)
    (hPsi : ∀ (g : G) (x : P),
      rankOneCharacter rho e g • tau g (Psi x) = Psi (sigma g x)) (y : H) :
    dualTensorHom k V P (rankOneTwistEquiv rho sigma tau e Psi hPsi y) =
      e.rankOneHomEquiv (Psi.symm y) := by
  have : Module.Finite k V := Module.Finite.equiv e.symm
  have : Module.Projective k V := Module.Projective.of_equiv' e.symm
  rw [← Representation.Equiv.dualTensorHomOfProjective_apply rho sigma, rankOneTwistEquiv,
    Representation.Equiv.trans_apply, Representation.Equiv.apply_symm_apply,
    Representation.Equiv.mk_apply, LinearEquiv.trans_apply]

/-- The inverse of the twist-removal equivalence evaluates the contracted tensor on the vector
with coordinate `1` and applies `Psi`. -/
@[simp]
theorem rankOneTwistEquiv_symm_apply (rho : Representation k G V)
    (sigma : Representation k G P) (tau : Representation k G H) (e : V ≃ₗ[k] k)
    (Psi : P ≃ₗ[k] H)
    (hPsi : ∀ (g : G) (x : P),
      rankOneCharacter rho e g • tau g (Psi x) = Psi (sigma g x))
    (t : Module.Dual k V ⊗[k] P) :
    (rankOneTwistEquiv rho sigma tau e Psi hPsi).symm t =
      Psi (dualTensorHom k V P t (e.symm 1)) := by
  obtain ⟨y, rfl⟩ := (rankOneTwistEquiv rho sigma tau e Psi hPsi).surjective t
  simp

end Group

end Representation

end CommSemiring
