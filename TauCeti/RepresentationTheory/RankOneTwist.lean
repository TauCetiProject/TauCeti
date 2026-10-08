/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LinHom

/-!
# Removing a rank-one twist

For a one-dimensional representation `V`, a linear equivalence `e : V ≃ k` identifies
`V⁺ ⊗ P` with `Hom(V, P)`. This file packages the elementary equivariance calculation used
when an isomorphism `P ≃ H` is equivariant up to the character of `V`.

## Main definitions

* `TauCeti.rankOneHomEquiv`: the coordinate isomorphism `P ≃ Hom(V, P)`.
* `TauCeti.rankOneTwistEquiv`: an isomorphism `H ≃ V⁺ ⊗ P` from an isomorphism
  `P ≃ H` equivariant up to the character of `V`.
-/

public section

noncomputable section

namespace TauCeti

universe u v w x

variable {k : Type u} {G : Type v}

section CommSemiring

variable [CommSemiring k] [Group G]
  {V : Type w} [AddCommMonoid V] [Module k V]
  {P : Type x} [AddCommMonoid P] [Module k P]

/-- A choice of coordinate on a rank-one module identifies a vector with the linear map obtained
by multiplying that coordinate by the vector. -/
@[expose] def rankOneHomEquiv (e : V ≃ₗ[k] k) : P ≃ₗ[k] V →ₗ[k] P :=
  (LinearMap.ringLmapEquivSelf k k P).symm.trans
    (e.symm.arrowCongr (LinearEquiv.refl k P))

/-- Evaluation of the coordinate identification `P ≃ Hom(V, P)`. -/
@[simp]
theorem rankOneHomEquiv_apply_apply (e : V ≃ₗ[k] k) (x : P) (v : V) :
    rankOneHomEquiv e x v = e v • x :=
  by simp [rankOneHomEquiv]

/-- The inverse coordinate identification evaluates a linear map on the vector with coordinate
`1`. -/
@[simp]
theorem rankOneHomEquiv_symm_apply (e : V ≃ₗ[k] k) (f : V →ₗ[k] P) :
    (rankOneHomEquiv e).symm f = f (e.symm 1) :=
  by simp [rankOneHomEquiv]

/-- The scalar through which a group element acts on a representation with a chosen rank-one
coordinate. -/
def rankOneCharacter (rho : Representation k G V) (e : V ≃ₗ[k] k) (g : G) : k :=
  e (rho g (e.symm 1))

/-- A representation on a module with a coordinate `V ≃ k` acts through its rank-one
character. -/
theorem rankOneCharacter_smul (rho : Representation k G V) (e : V ≃ₗ[k] k)
    (g : G) (v : V) :
    rho g v = rankOneCharacter rho e g • v := by
  have hv : v = e v • e.symm 1 := by
    apply e.injective
    simp
  rw [hv, map_smul, rankOneCharacter]
  apply e.injective
  simp [mul_comm]

/-- The rank-one character of a representation is nonzero. -/
theorem rankOneCharacter_ne_zero [Nontrivial k]
    (rho : Representation k G V) (e : V ≃ₗ[k] k)
    (g : G) :
    rankOneCharacter rho e g ≠ 0 := by
  intro h
  have hz : rho g (e.symm 1) = 0 := by
    rw [rankOneCharacter_smul rho e, h, zero_smul]
  have hgen : e.symm 1 ≠ 0 := by
    intro hgen
    have h : (1 : k) = 0 := by
      calc
        (1 : k) = e (e.symm 1) := (e.apply_symm_apply 1).symm
        _ = e 0 := congrArg e hgen
        _ = 0 := map_zero e
    exact one_ne_zero h
  exact hgen ((rho.apply_bijective g).1 (hz.trans (map_zero _).symm))

end CommSemiring

section Field

variable [Field k] [Group G]
  {V : Type w} [AddCommGroup V] [Module k V]
  {P : Type x} [AddCommGroup P] [Module k P]
  {H : Type*} [AddCommGroup H] [Module k H]

/-- **Removal of a rank-one twist.** If `Psi : P ≃ H` satisfies
`chi(g) · g(Psi x) = Psi(gx)` for the character of the rank-one representation `rho`, then
`H` is equivariantly isomorphic to `rho⁺ ⊗ P`. -/
def rankOneTwistEquiv (rho : Representation k G V) (sigma : Representation k G P)
    (tau : Representation k G H) (e : V ≃ₗ[k] k) (Psi : P ≃ₗ[k] H)
    (hPsi : ∀ (g : G) (x : P),
      rankOneCharacter rho e g • tau g (Psi x) = Psi (sigma g x)) :
    tau.Equiv (rho.dual.tprod sigma) := by
  letI : Module.Finite k V := Module.Finite.equiv e.symm
  letI : Module.Projective k V := Module.Projective.of_equiv' e.symm
  let homEquiv : tau.Equiv (Representation.linHom rho sigma) :=
    .mk (Psi.symm.trans (rankOneHomEquiv e)) fun g ↦ by
      ext y v
      -- Unfold the representation equivalence so the intertwining goal can be evaluated at `v`.
      change (Psi.symm.trans (rankOneHomEquiv e)) (tau g y) v =
        (Representation.linHom rho sigma g
          ((Psi.symm.trans (rankOneHomEquiv e)) y)) v
      rw [Representation.linHom_apply]
      simp only [LinearMap.comp_apply]
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
        rankOneHomEquiv_apply_apply, rankOneHomEquiv_apply_apply]
      let c := rankOneCharacter rho e g
      have hc : c ≠ 0 := rankOneCharacter_ne_zero rho e g
      let x := Psi.symm y
      have hy : y = Psi x := by simp [x]
      have hinv : v = c • rho g⁻¹ v := by
        calc
          v = rho 1 v := by simp
          _ = rho (g * g⁻¹) v := by simp
          _ = rho g (rho g⁻¹ v) := by rw [map_mul]; rfl
          _ = c • rho g⁻¹ v := rankOneCharacter_smul rho e g _
      apply ((isUnit_iff_ne_zero.mpr hc).smul_left_cancel).mp
      rw [hy]
      have htwist : c • Psi.symm (tau g (Psi x)) = sigma g x := by
        rw [← map_smul, hPsi, Psi.symm_apply_apply]
      have heinv : e v = c * e (rho g⁻¹ v) := by
        simpa using congrArg e hinv
      rw [map_smul, Psi.symm_apply_apply]
      calc
        c • (e v • Psi.symm (tau g (Psi x))) =
            e v • (c • Psi.symm (tau g (Psi x))) := by
              simp [smul_smul, mul_comm]
        _ = e v • sigma g x := by rw [htwist]
        _ = c • (e (rho g⁻¹ v) • sigma g x) := by
          rw [heinv, smul_smul]
  exact homEquiv.trans (Representation.Equiv.dualTensorHomOfProjective rho sigma).symm

end Field

end TauCeti
