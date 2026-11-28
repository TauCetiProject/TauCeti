/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.Padics.UnitsCharacter.Basic

/-!
# Coefficient-valued continuous characters of `ℚ_pˣ`

For a prime `p` and a topological monoid `Λ`, a continuous character of `ℚ_pˣ` with values in `Λ`
is a continuous homomorphism `δ : ℚ_[p]ˣ →ₜ* Λˣ` (`TauCeti.PadicUnitsCharacter p Λ`).

Using `TauCeti.padicUnitsCharacterEquiv p Λˣ`, when `Λ` is a commutative topological monoid with
continuous multiplication, `TauCeti.PadicUnitsCharacter p Λ` decomposes as
`Λˣ × (ℤ_[p]ˣ →ₜ* Λˣ)` via `δ ↦ (δ(p), δ|_{ℤ_pˣ})`.

This file also constructs additional canonical characters of `ℚ_[p]ˣ` complementing
`TauCeti.padicUnitPart` and `TauCeti.unramifiedCharacter`:

* `TauCeti.padicModPCyclotomicCharacter p`: the mod-`p` character `ω : ℚ_[p]ˣ →ₜ* (ZMod p)ˣ`,
  obtained by reducing `TauCeti.padicUnitPart p` modulo `p`.
* `TauCeti.padicAlgebraMapCharacter p R h`: the character `x ↦ algebraMap ℚ_[p] R x` into a
  topological `ℚ_[p]`-algebra `R` with continuous structure map.

## Main definitions

* `TauCeti.PadicUnitsCharacter`: the type `ℚ_[p]ˣ →ₜ* Λˣ` of continuous `Λ`-valued characters.
* `TauCeti.padicModPCyclotomicCharacter`, `TauCeti.padicAlgebraMapCharacter`: the mod-`p`
  cyclotomic character `ω` and the algebra-map character `x ↦ x`.

## References

* P. Colmez, *Représentations de GL₂(ℚ_p) et (φ, Γ)-modules*, Astérisque 330 (2010),
  Introduction §1.
* P. Colmez, *Représentations triangulines de dimension 2*, Astérisque 319 (2008), §0.1.
* P. Colmez, G. Dospinescu, V. Paškūnas, *The p-adic local Langlands correspondence for GL₂(ℚ_p)*,
  Camb. J. Math. 2 (2014), §1.1.
-/

public section

noncomputable section

namespace TauCeti

section CharacterGroup

variable (p : ℕ) [Fact p.Prime]

/-- The type `T̂(Λ)` of continuous characters `ℚ_[p]ˣ →ₜ* Λˣ` with values in a topological monoid
`Λ`. When `Λ` is commutative with continuous multiplication, Mathlib's `ContinuousMonoidHom`
instance makes `PadicUnitsCharacter p Λ` a commutative group under pointwise multiplication. -/
abbrev PadicUnitsCharacter (Λ : Type*) [Monoid Λ] [TopologicalSpace Λ] : Type _ :=
  ℚ_[p]ˣ →ₜ* Λˣ

end CharacterGroup

section CanonicalCharacters

variable (p : ℕ) [Fact p.Prime]

/-- **The mod-`p` cyclotomic character `ω : ℚ_[p]ˣ →ₜ* (ZMod p)ˣ`**, obtained by reducing
`TauCeti.padicUnitPart p` modulo `p`. -/
def padicModPCyclotomicCharacter : PadicUnitsCharacter p (ZMod p) :=
  (ContinuousMonoidHom.unitsMap
      ⟨PadicInt.toZMod.toMonoidHom, PadicInt.continuous_toZMod⟩).comp
    (padicUnitPart p)

/-- `ω(p) = 1`. -/
@[simp]
theorem padicModPCyclotomicCharacter_padicPrimeUnit :
    padicModPCyclotomicCharacter p (padicPrimeUnit p) = 1 := by
  simp [padicModPCyclotomicCharacter]

/-- The value of `ω` in `ZMod p` is the mod-`p` reduction of `padicUnitPart p`. -/
@[simp]
theorem coe_padicModPCyclotomicCharacter_apply (x : ℚ_[p]ˣ) :
    (padicModPCyclotomicCharacter p x : ZMod p) = PadicInt.toZMod (padicUnitPart p x : ℤ_[p]) := by
  simp [padicModPCyclotomicCharacter]
  rfl

/-- On `u ∈ ℤ_[p]ˣ`, `ω(u) = u mod p`. -/
theorem coe_padicModPCyclotomicCharacter_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    (padicModPCyclotomicCharacter p (padicIntUnitsInclusion p u) : ZMod p) =
      PadicInt.toZMod (u : ℤ_[p]) := by
  rw [coe_padicModPCyclotomicCharacter_apply, padicUnitPart_padicIntUnitsInclusion]

/-- The canonical character `x ↦ algebraMap ℚ_[p] R x` into a topological `ℚ_[p]`-algebra `R`
whose structure map is continuous. -/
def padicAlgebraMapCharacter (R : Type*) [Semiring R] [TopologicalSpace R] [Algebra ℚ_[p] R]
    (h : Continuous (algebraMap ℚ_[p] R)) : PadicUnitsCharacter p R :=
  ContinuousMonoidHom.unitsMap ⟨(algebraMap ℚ_[p] R).toMonoidHom, h⟩

/-- The underlying value of `padicAlgebraMapCharacter p R h x` is `algebraMap ℚ_[p] R x`. -/
@[simp]
theorem coe_padicAlgebraMapCharacter_apply {R : Type*} [Semiring R] [TopologicalSpace R]
    [Algebra ℚ_[p] R] (h : Continuous (algebraMap ℚ_[p] R)) (x : ℚ_[p]ˣ) :
    (padicAlgebraMapCharacter p R h x : R) = algebraMap ℚ_[p] R (x : ℚ_[p]) := by
  simp [padicAlgebraMapCharacter]
  rfl

/-- `padicAlgebraMapCharacter p R h` sends `p` to `(p : R)`. -/
theorem coe_padicAlgebraMapCharacter_padicPrimeUnit {R : Type*} [Semiring R] [TopologicalSpace R]
    [Algebra ℚ_[p] R] (h : Continuous (algebraMap ℚ_[p] R)) :
    (padicAlgebraMapCharacter p R h (padicPrimeUnit p) : R) = (p : R) := by
  rw [coe_padicAlgebraMapCharacter_apply]
  simp

end CanonicalCharacters

end TauCeti
