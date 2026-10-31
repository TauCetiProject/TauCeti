/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Conductor
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Weight

/-!
# Primitive ray class characters and imprimitive Euler factors

A ray class character can be presented at every multiple of its conductor, and the Dirichlet
series of a presentation depends on the presentation: the ideal weight of a character of `𝔫`
vanishes at every prime dividing the finite part `𝔫₀`. The invariants attached to the character
itself (conductor, gamma factors, Gauss sum, root number, completed L-function) are instead
functions of the primitive character underlying it. This file supplies the carrier for those
invariants and the comparison between presented and primitive series.

`TauCeti.LFunctions.PrimitiveRayClassCharacter K` bundles a modulus with a primitive ray class
character of that modulus, so that a primitive character cannot carry a second conductor.
`PrimitiveRayClassCharacter.of χ` is the bundle of the conductor and primitive character of a
presentation `χ`, and `PrimitiveRayClassCharacter.of_eq_iff` is its universal property: `of χ` is
the unique primitive character inducing `χ`. In particular `of` does not see the presentation
(`of_induced`), the trivial character has the trivial bundle (`of_one`), and the inverse of a
primitive character, primitive at the same conductor, is the bundle of the inverse
(`of_inv`). This last fact is what the functional equation `Λ(χ, s) = W(χ) Λ(χ⁻¹, 1 - s)` reflects
against.

For `𝔪 ∣ 𝔫`, `RayClassCharacter.eulerCorrection χ 𝔫 s` is the product
`∏_{𝔭 ∣ 𝔫₀, 𝔭 ∤ 𝔪₀} (1 - χ(𝔭) N(𝔭) ^ (-s))` of the Euler factors that inducing `χ` to `𝔫` deletes.
The character value is read through the total ideal weight of `χ`, so no class is assigned to a
prime dividing `𝔪₀`. On `Re s > 1` the series of the induced character is the series of `χ` times
this correction (`RayClassCharacter.LSeries_induced`), and every presented series is the primitive
series times the correction to the presentation
(`RayClassCharacter.LSeries_eq_LSeries_primitiveCharacter_mul`).
For the trivial character of the trivial modulus the correction is
`∏_{𝔭 ∣ 𝔫₀} (1 - N(𝔭) ^ (-s))`, the factor by which the series of ideals prime to `𝔫₀` differs from
the Dedekind zeta function (`TauCeti.LSeries_ofBadPrimes`).

## Main definitions

* `TauCeti.LFunctions.PrimitiveRayClassCharacter`: a primitive ray class character bundled with
  its conductor.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.of`: the primitive character underlying a ray
  class character.
* `TauCeti.GlobalNumberFields.RayClassCharacter.eulerCorrection`: the Euler factors deleted by
  inducing a character to a larger modulus.

## Main results

* `TauCeti.LFunctions.PrimitiveRayClassCharacter.eq_of_induced_eq`: two primitive characters
  inducing the same character of a common multiple of their conductors are equal.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.of_eq_iff`: `of χ` is the unique primitive
  character inducing `χ`.
* `TauCeti.LFunctions.PrimitiveRayClassCharacter.of_induced`,
  `TauCeti.LFunctions.PrimitiveRayClassCharacter.of_one`,
  `TauCeti.LFunctions.PrimitiveRayClassCharacter.of_inv`: `of` and change of modulus, the trivial
  character, and inversion.
* `TauCeti.GlobalNumberFields.RayClassCharacter.LSeries_induced`: inducing multiplies the
  `L`-series by the deleted Euler factors on `Re s > 1`.
* `TauCeti.GlobalNumberFields.RayClassCharacter.LSeries_eq_LSeries_primitiveCharacter_mul`: every
  presented `L`-series is the primitive one times the correction to the presentation.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
* The comparison of series follows Mathlib's `DirichletCharacter.LSeries_changeLevel`.
-/

public section
noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

open GlobalNumberFields

namespace LFunctions

/-- **A primitive ray class character bundled with its conductor.** One ray class character can be
presented at every multiple of its conductor; on this carrier the modulus is the conductor of the
character, so it cannot record a second conductor. -/
structure PrimitiveRayClassCharacter (K : Type*) [Field K] [NumberField K] where
  /-- The conductor of the character. -/
  conductor : Modulus K
  /-- The character, presented at its conductor. -/
  character : RayClassCharacter conductor
  /-- The character is primitive at its conductor. -/
  isPrimitive : character.IsPrimitive

namespace PrimitiveRayClassCharacter

variable {𝔪 𝔫 : Modulus K}

/-- **Primitive characters are determined by any presentation.** Two primitive characters inducing
the same character of a common multiple of their conductors are equal; in particular they have the
same conductor. -/
theorem eq_of_induced_eq {ψ ψ' : PrimitiveRayClassCharacter K} {𝔐 : Modulus K}
    (h : ψ.conductor ∣ 𝔐) (h' : ψ'.conductor ∣ 𝔐)
    (hψ : ψ.character.induced h = ψ'.character.induced h') : ψ = ψ' := by
  cases ψ with | mk 𝔣 χ hχ =>
  cases ψ' with | mk 𝔣' χ' hχ' =>
  have h𝔣 : 𝔣 = 𝔣' := by
    have := RayClassCharacter.conductor_eq_of_induced_eq h h' hψ
    rwa [(RayClassCharacter.isPrimitive_iff_conductor_eq χ).mp hχ,
      (RayClassCharacter.isPrimitive_iff_conductor_eq χ').mp hχ'] at this
  subst h𝔣
  obtain rfl := RayClassCharacter.induced_injective h hψ
  rfl

/-- **The primitive character underlying a ray class character**: its conductor, with the
primitive character of the conductor from which it is induced. -/
def of (χ : RayClassCharacter 𝔪) : PrimitiveRayClassCharacter K :=
  ⟨χ.conductor, χ.primitiveCharacter, χ.isPrimitive_primitiveCharacter⟩

@[simp]
theorem conductor_of (χ : RayClassCharacter 𝔪) : (of χ).conductor = χ.conductor :=
  (rfl)

/-- The conductor of the primitive character of a presentation divides the presentation
modulus. -/
theorem conductor_of_dvd (χ : RayClassCharacter 𝔪) : (of χ).conductor ∣ 𝔪 :=
  χ.conductor_dvd

/-- A ray class character is induced from its primitive character. -/
@[simp]
theorem induced_character_of (χ : RayClassCharacter 𝔪) :
    (of χ).character.induced (conductor_of_dvd χ) = χ :=
  χ.induced_primitiveCharacter

/-- **Universal property of the primitive character**: `of χ` is the unique primitive character
from which `χ` is induced. -/
theorem of_eq_iff {χ : RayClassCharacter 𝔪} {ψ : PrimitiveRayClassCharacter K} :
    of χ = ψ ↔ ∃ h : ψ.conductor ∣ 𝔪, ψ.character.induced h = χ := by
  refine ⟨?_, fun ⟨h, hψ⟩ ↦ eq_of_induced_eq (conductor_of_dvd χ) h ?_⟩
  · rintro rfl
    exact ⟨conductor_of_dvd χ, induced_character_of χ⟩
  · rw [induced_character_of, hψ]

/-- A primitive character is the primitive character of its own presentation. -/
@[simp]
theorem of_character (ψ : PrimitiveRayClassCharacter K) : of ψ.character = ψ :=
  of_eq_iff.mpr ⟨Modulus.dvd_refl _, RayClassCharacter.induced_refl _⟩

/-- **The primitive character does not depend on the presentation.** -/
@[simp]
theorem of_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) : of (χ.induced h) = of χ :=
  of_eq_iff.mpr ⟨Modulus.dvd_trans (conductor_of_dvd χ) h, by
    rw [← RayClassCharacter.induced_trans (conductor_of_dvd χ) h, induced_character_of]⟩

/-- The trivial character of the trivial modulus, the primitive character of the Dedekind zeta
function. -/
instance : One (PrimitiveRayClassCharacter K) :=
  ⟨⟨Modulus.one K, 1, RayClassCharacter.isPrimitive_of_modulus_one 1⟩⟩

@[simp]
theorem conductor_one : (1 : PrimitiveRayClassCharacter K).conductor = Modulus.one K :=
  (rfl)

@[simp]
theorem character_one : (1 : PrimitiveRayClassCharacter K).character = 1 :=
  (rfl)

/-- The trivial character of every modulus has the trivial primitive character. -/
@[simp]
theorem of_one : of (1 : RayClassCharacter 𝔪) = 1 :=
  of_eq_iff.mpr ⟨Modulus.one_dvd 𝔪, map_one _⟩

/-- The inverse of a primitive character is primitive at the same conductor. -/
instance : InvolutiveInv (PrimitiveRayClassCharacter K) where
  inv ψ := ⟨ψ.conductor, ψ.character⁻¹, by
    rw [RayClassCharacter.isPrimitive_iff_conductor_eq, RayClassCharacter.conductor_inv,
      ← RayClassCharacter.isPrimitive_iff_conductor_eq]
    exact ψ.isPrimitive⟩
  inv_inv ψ := eq_of_induced_eq (Modulus.dvd_refl _) (Modulus.dvd_refl _) (by
    simp only [RayClassCharacter.induced_refl]
    -- The inverse of `RayClassCharacter` is `MonoidHom.instInv`, which `simp` does not match
    -- against the `Group` inverse of `inv_inv`; the explicit term unifies the two instances.
    exact inv_inv (G := RayClassCharacter ψ.conductor) ψ.character)

@[simp]
theorem conductor_inv (ψ : PrimitiveRayClassCharacter K) : ψ⁻¹.conductor = ψ.conductor :=
  (rfl)

@[simp]
theorem character_inv (ψ : PrimitiveRayClassCharacter K) : ψ⁻¹.character = ψ.character⁻¹ :=
  (rfl)

/-- **The primitive character of the inverse is the inverse of the primitive character.** -/
@[simp]
theorem of_inv (χ : RayClassCharacter 𝔪) : of χ⁻¹ = (of χ)⁻¹ :=
  of_eq_iff.mpr ⟨conductor_of_dvd χ, by
    rw [character_inv, map_inv (RayClassCharacter.induced _) _, induced_character_of]⟩

@[simp]
theorem inv_one : (1 : PrimitiveRayClassCharacter K)⁻¹ = 1 :=
  eq_of_induced_eq (Modulus.dvd_refl _) (Modulus.dvd_refl _) (by
    simp only [RayClassCharacter.induced_refl, character_inv, character_one]
    -- As in `inv_inv` above, `MonoidHom.instInv` is unified with the `Group` inverse explicitly.
    exact _root_.inv_one (G := RayClassCharacter (Modulus.one K)))

end PrimitiveRayClassCharacter

end LFunctions

namespace GlobalNumberFields.RayClassCharacter

variable {𝔪 𝔫 : Modulus K}

open Classical in
/-- **The Euler factors deleted by inducing a character to a larger modulus**:
`∏_{𝔭 ∣ 𝔫₀, 𝔭 ∤ 𝔪₀} (1 - χ(𝔭) N(𝔭) ^ (-s))` for a character `χ` of `𝔪`. The value `χ(𝔭)` is read
through the ideal weight of `χ`, which is total and vanishes at the primes dividing `𝔪₀`. -/
def eulerCorrection (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K) (s : ℂ) : ℂ :=
  ∏ 𝔭 ∈ 𝔫.support \ 𝔪.support,
    (1 - χ.toMultiplicativeIdealWeight 𝔭.asIdeal * (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s))

/-- Since the ideal weight of `χ` vanishes at the primes dividing `𝔪₀`, the Euler correction may
be taken over all primes dividing `𝔫₀`. -/
theorem eulerCorrection_eq_prod_support (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K) (s : ℂ) :
    χ.eulerCorrection 𝔫 s = ∏ 𝔭 ∈ 𝔫.support,
      (1 - χ.toMultiplicativeIdealWeight 𝔭.asIdeal * (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) := by
  classical
  refine Finset.prod_subset Finset.sdiff_subset fun 𝔭 h𝔫 h𝔭 ↦ ?_
  have h𝔪 : 𝔭 ∈ 𝔪.support := by
    by_contra h
    exact h𝔭 (Finset.mem_sdiff.mpr ⟨h𝔫, h⟩)
  have hzero : χ.toMultiplicativeIdealWeight 𝔭.asIdeal = 0 := by
    rw [← MultiplicativeIdealWeight.mem_badPrimes, badPrimes_toMultiplicativeIdealWeight]
    exact h𝔪
  rw [hzero, zero_mul, sub_zero]

/-- Presenting a character at its own modulus deletes no Euler factor. -/
@[simp]
theorem eulerCorrection_self (χ : RayClassCharacter 𝔪) (s : ℂ) : χ.eulerCorrection 𝔪 s = 1 := by
  classical
  rw [eulerCorrection, Finset.sdiff_self, Finset.prod_empty]

/-- **The correction of the trivial character is the finite Euler correction**: for the trivial
character of the trivial modulus, inducing to `𝔫` deletes the factors `1 - N(𝔭) ^ (-s)` at every
prime dividing `𝔫₀`. -/
theorem eulerCorrection_one (𝔫 : Modulus K) (s : ℂ) :
    (1 : RayClassCharacter (Modulus.one K)).eulerCorrection 𝔫 s =
      ∏ 𝔭 ∈ 𝔫.support, (1 - (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)) := by
  rw [eulerCorrection_eq_prod_support]
  refine Finset.prod_congr rfl fun 𝔭 _ ↦ ?_
  simp [𝔭.ne_bot]

/-- The Euler correction has no zero on `Re s > 0`: each deleted factor has the form `1 - a` with
`‖a‖ ≤ N(𝔭) ^ (-Re s) < 1`. -/
theorem eulerCorrection_ne_zero (χ : RayClassCharacter 𝔪) (𝔫 : Modulus K) {s : ℂ}
    (hs : 0 < s.re) : χ.eulerCorrection 𝔫 s ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun 𝔭 _ h ↦ ?_
  have hlt : ‖(Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.cpow_neg, norm_inv]
    exact inv_lt_one_of_one_lt₀ (𝔭.one_lt_norm_absNorm_cpow hs)
  have hle : ‖χ.toMultiplicativeIdealWeight 𝔭.asIdeal‖ ≤ 1 := by
    simpa using χ.toUnitaryIdealWeight.norm_le_one 𝔭.asIdeal
  have h1 : ‖χ.toMultiplicativeIdealWeight 𝔭.asIdeal * (Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)‖ <
      1 := by
    rw [norm_mul]
    calc _ ≤ 1 * ‖(Ideal.absNorm 𝔭.asIdeal : ℂ) ^ (-s)‖ := by gcongr
      _ < 1 := by rwa [one_mul]
  rw [sub_eq_zero] at h
  simp [← h] at h1

/-- **Inducing deletes Euler factors.** On `Re s > 1`, the `L`-series of the character induced
from `χ` to a multiple `𝔫` of its modulus is the `L`-series of `χ` times the Euler factors at the
primes dividing `𝔫₀` but not `𝔪₀`. -/
theorem LSeries_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : 1 < s.re) :
    LSeries (normCoeff K (χ.induced h).toUnitaryIdealWeight.toIdealArithmeticFunction) s =
      LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s *
        χ.eulerCorrection 𝔫 s := by
  have hsum := summable_idealTerm_of_unitary_of_one_lt_re χ.toUnitaryIdealWeight hs
  -- Pass from unitary weights to the underlying multiplicative weight of `χ`.
  simp only [toUnitaryIdealWeight_induced, UnitaryIdealWeight.toIdealArithmeticFunction_eq_val,
    UnitaryIdealWeight.val_restrictAway, val_toUnitaryIdealWeight] at hsum ⊢
  rw [χ.toMultiplicativeIdealWeight.LSeries_restrictAway 𝔫.support hsum]
  simp only [eulerCorrection_eq_prod_support, div_eq_mul_inv, Complex.cpow_neg]

/-- **Presented and primitive series.** On `Re s > 1`, the `L`-series of a ray class character is
the `L`-series of its primitive character times the Euler factors at the primes dividing the
presentation modulus but not the conductor. -/
theorem LSeries_eq_LSeries_primitiveCharacter_mul (χ : RayClassCharacter 𝔪) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (normCoeff K χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s =
      LSeries (normCoeff K χ.primitiveCharacter.toUnitaryIdealWeight.toIdealArithmeticFunction) s *
        χ.primitiveCharacter.eulerCorrection 𝔪 s := by
  conv_lhs => rw [← χ.induced_primitiveCharacter]
  exact LSeries_induced χ.conductor_dvd χ.primitiveCharacter hs

end GlobalNumberFields.RayClassCharacter

end TauCeti
