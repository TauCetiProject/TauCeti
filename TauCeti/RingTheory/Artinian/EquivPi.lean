/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Components of elements of a reduced Artinian ring

A reduced Artinian ring `Q` is the finite product of its residue fields `Q ⧸ m` over its maximal
ideals `m` (`IsArtinianRing.equivPi`). This file describes the element
`(IsArtinianRing.equivPi Q).symm t` of `Q` with prescribed components `t m` in the residue fields:
its component in `Q ⧸ m` is `t m` (`IsArtinianRing.mk_equivPi_symm`), it is characterized by these
components (`IsArtinianRing.eq_equivPi_symm_iff`), it is a unit exactly when every component is
nonzero (`IsArtinianRing.isUnit_equivPi_symm_iff`), and it is `0` exactly when every component is
`0` (`IsArtinianRing.equivPi_symm_eq_zero_iff`). If the component of `x` in each residue field is
`±1` times that of `y`, then `x = ε * y` for an element `ε` of `Q` with `ε * ε = 1`
(`IsArtinianRing.exists_mul_self_eq_one_and_eq_mul`).

It also records that a ring homomorphism `g : Q →+* Q'` out of an Artinian ring induces, for each
maximal ideal `m'` of `Q'`, a homomorphism from a residue field of `Q` to `Q' ⧸ m'`
(`IsArtinianRing.exists_quotient_ringHom_mk_comp`), because every prime ideal of `Q` is maximal.

Conversely, a maximal ideal `p` of a ring `R` extends along `f : R →+* Q` to a maximal ideal of a
reduced Artinian ring `Q`, unless the extension is the unit ideal, provided distinct primes of `Q`
contract to distinct primes of `R` (`IsArtinianRing.isMaximal_map_of_injective_comap`). Then
`Q ⧸ p Q` is a single residue field of `Q`: when `Q` is finite free over `R`, the residue field
`R ⧸ p` has exactly one field component above it.
-/

public section

namespace IsArtinianRing

attribute [local instance] Ideal.Quotient.field

variable {Q : Type*} [CommRing Q] [IsArtinianRing Q]

/-- For a ring homomorphism `g : Q →+* Q'` out of an Artinian ring and a maximal ideal `m'` of
`Q'`, the preimage of `m'` is a maximal ideal `p` of `Q`, and `g` induces a homomorphism of residue
fields `ψ : Q ⧸ p →+* Q' ⧸ m'`. -/
theorem exists_quotient_ringHom_mk_comp {Q' : Type*} [CommRing Q'] (g : Q →+* Q')
    (m' : MaximalSpectrum Q') :
    ∃ (p : MaximalSpectrum Q) (ψ : Q ⧸ p.asIdeal →+* Q' ⧸ m'.asIdeal),
      ∀ x, Ideal.Quotient.mk m'.asIdeal (g x) = ψ (Ideal.Quotient.mk p.asIdeal x) :=
  -- The preimage of `m'` is prime, hence maximal in the Artinian ring `Q`.
  ⟨⟨m'.asIdeal.comap g, isMaximal_of_isPrime _⟩, Ideal.quotientMap m'.asIdeal g le_rfl,
    fun _ ↦ Ideal.quotientMap_mk.symm⟩

variable [IsReduced Q]

/-- The component in `Q ⧸ m` of the element with components `t` is `t m`. -/
@[simp]
theorem mk_equivPi_symm (t : ∀ m : MaximalSpectrum Q, Q ⧸ m.asIdeal) (m : MaximalSpectrum Q) :
    Ideal.Quotient.mk m.asIdeal ((equivPi Q).symm t) = t m := by
  rw [← equivPi_apply, AlgEquiv.apply_symm_apply]

/-- An element of `Q` is the element with components `t` exactly when its component in each
residue field `Q ⧸ m` is `t m`. -/
theorem eq_equivPi_symm_iff {t : ∀ m : MaximalSpectrum Q, Q ⧸ m.asIdeal} {x : Q} :
    x = (equivPi Q).symm t ↔ ∀ m : MaximalSpectrum Q, Ideal.Quotient.mk m.asIdeal x = t m := by
  simp_rw [AlgEquiv.eq_symm_apply, funext_iff, equivPi_apply]

/-- The element with components `t` is a unit exactly when every component is nonzero. -/
theorem isUnit_equivPi_symm_iff {t : ∀ m : MaximalSpectrum Q, Q ⧸ m.asIdeal} :
    IsUnit ((equivPi Q).symm t) ↔ ∀ m, t m ≠ 0 := by
  simp_rw [isUnit_map_iff, Pi.isUnit_iff, isUnit_iff_ne_zero]

/-- The element with components `t` is `0` exactly when every component is `0`. -/
theorem equivPi_symm_eq_zero_iff {t : ∀ m : MaximalSpectrum Q, Q ⧸ m.asIdeal} :
    (equivPi Q).symm t = 0 ↔ ∀ m, t m = 0 := by
  rw [map_eq_zero_iff _ (equivPi Q).symm.injective, funext_iff]
  simp_rw [Pi.zero_apply]

/-- If in each residue field `Q ⧸ m` the component of `x` is `(-1) ^ k m` times that of `y`, then
`x = ε * y` for some `ε : Q` with `ε * ε = 1`, namely the element with components `(-1) ^ k m`. -/
theorem exists_mul_self_eq_one_and_eq_mul {x y : Q} (k : MaximalSpectrum Q → ℕ)
    (h : ∀ m : MaximalSpectrum Q,
      Ideal.Quotient.mk m.asIdeal x = (-1) ^ k m * Ideal.Quotient.mk m.asIdeal y) :
    ∃ ε : Q, ε * ε = 1 ∧ x = ε * y :=
  ⟨(equivPi Q).symm fun m ↦ (-1) ^ k m,
    (equivPi Q).injective (funext fun m ↦ by simp [← mul_pow]),
    (equivPi Q).injective (funext fun m ↦ by simp [h])⟩

/-- **Extensions of maximal ideals to a reduced Artinian ring.** Let `f : R →+* Q` be a ring
homomorphism into a reduced Artinian ring such that distinct primes of `Q` contract to distinct
primes of `R`. Then the extension `p Q` of a maximal ideal `p` of `R` is a maximal ideal of `Q`,
unless it is the unit ideal. -/
theorem isMaximal_map_of_injective_comap {R : Type*} [CommRing R] (f : R →+* Q)
    (hf : Function.Injective (PrimeSpectrum.comap f)) {p : Ideal R} [hp : p.IsMaximal]
    (hpQ : p.map f ≠ ⊤) : (p.map f).IsMaximal := by
  obtain ⟨q, hq, hpq⟩ := Ideal.exists_le_maximal _ hpQ
  -- Every prime of `Q` containing `p Q` contracts to `p`, hence is `q`.
  have hcomap {P : Ideal Q} (hP : P.IsPrime) (hle : p.map f ≤ P) : P.comap f = p :=
    (hp.eq_of_le (hP.comap f).ne_top (Ideal.map_le_iff_le_comap.1 hle)).symm
  have hunique {P : Ideal Q} (hP : P.IsPrime) (hle : p.map f ≤ P) : P = q :=
    congrArg PrimeSpectrum.asIdeal <| hf (a₁ := ⟨P, hP⟩) (a₂ := ⟨q, hq.isPrime⟩) <|
      PrimeSpectrum.ext <| (hcomap hP hle).trans (hcomap hq.isPrime hpq).symm
  -- `Q` is semisimple, so its quotient by `p Q` is reduced and `p Q` is radical.
  have := isSemisimpleRing_of_isReduced Q
  have := (Ideal.Quotient.mk (p.map f)).isSemisimpleRing_of_surjective Ideal.Quotient.mk_surjective
  have hrad : (p.map f).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 inferInstance
  have hq' : p.map f = q := hpq.antisymm <| by
    rw [← hrad.radical, Ideal.radical_eq_sInf]
    exact le_sInf fun P ⟨hle, hP⟩ ↦ (hunique hP hle).ge
  exact hq' ▸ hq

end IsArtinianRing
