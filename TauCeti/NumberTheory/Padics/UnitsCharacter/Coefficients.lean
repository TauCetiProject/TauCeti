/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.Padics.UnitsCharacter.Basic
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic

/-!
# Coefficient-valued continuous characters of `ℚ_pˣ`

For a prime `p` and a topological monoid `Λ`, a continuous character of `ℚ_pˣ` with values in `Λ`
is a continuous homomorphism `δ : ℚ_[p]ˣ →ₜ* Λˣ` (`TauCeti.PadicUnitsCharacter p Λ`).

Using `TauCeti.padicUnitsCharacterEquiv p Λˣ`, when `Λ` is a commutative topological monoid with
continuous multiplication, `TauCeti.PadicUnitsCharacter p Λ` decomposes as
`Λˣ × TauCeti.WeightSpace p Λ` via `δ ↦ (δ(p), δ|_{ℤ_pˣ})`.

This file also constructs additional canonical characters of `ℚ_[p]ˣ` complementing
`TauCeti.padicUnitPart` and `TauCeti.unramifiedCharacter`:

* `TauCeti.padicModPCyclotomicCharacter p`: the mod-`p` character `ω : ℚ_[p]ˣ →ₜ* (ZMod p)ˣ`,
  obtained by reducing `TauCeti.padicUnitPart p` modulo `p`. After pushing forward to the residue
  field `k` of a finite extension `L / ℚ_[p]` along the induced maps `ℤ_[p] →+* k` and
  `ZMod p →+* k`, `TauCeti.padicUnitPart p` agrees with the pushforward of `ω`
  (`TauCeti.unitsMap_ringHom_comp_padicUnitPart`).
* `TauCeti.padicAlgebraMapCharacter p R h`: the character `x ↦ algebraMap ℚ_[p] R x` into a
  topological `ℚ_[p]`-algebra `R` with continuous structure map.

## Main definitions

* `TauCeti.PadicUnitsCharacter`: the type `ℚ_[p]ˣ →ₜ* Λˣ` of continuous `Λ`-valued characters.
* `TauCeti.PadicUnitsCharacter.toWeight`: restriction to `ℤ_[p]ˣ` as a weight in
  `TauCeti.WeightSpace p Λ`.
* `TauCeti.padicModPCyclotomicCharacter`, `TauCeti.padicAlgebraMapCharacter`: the mod-`p`
  cyclotomic character `ω` and the algebra-map character `x ↦ x`.

## Main results

* `TauCeti.unitsMap_ringHom_comp_padicUnitPart`: pushing `padicUnitPart p` along any
  `f : ℤ_[p] →+* k` with `[CharP k p]` agrees with pushing `padicModPCyclotomicCharacter p` along
  `ZMod.castHom`.

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

namespace PadicUnitsCharacter

variable {p}

section Monoid

variable {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ]

/-- The restriction of a continuous character of `ℚ_[p]ˣ` to `ℤ_[p]ˣ`, viewed as a weight in
`TauCeti.WeightSpace p Λ`. -/
def toWeight (δ : PadicUnitsCharacter p Λ) : WeightSpace p Λ :=
  δ.comp (padicIntUnitsInclusion p)

/-- Evaluating `δ.toWeight` at `u : ℤ_[p]ˣ` evaluates `δ` at `u` viewed in `ℚ_[p]ˣ`. -/
@[simp]
theorem toWeight_apply (δ : PadicUnitsCharacter p Λ) (u : ℤ_[p]ˣ) :
    δ.toWeight u = δ (padicIntUnitsInclusion p u) :=
  (rfl)

/-- Restriction to `ℤ_[p]ˣ` sends the trivial character to the trivial weight. -/
@[simp]
theorem toWeight_one : (1 : PadicUnitsCharacter p Λ).toWeight = 1 := by
  ext1 u
  rfl

end Monoid

section CommMonoid

variable {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ]

/-- Restriction to `ℤ_[p]ˣ` preserves products of characters. -/
@[simp]
theorem toWeight_mul (δ₁ δ₂ : PadicUnitsCharacter p Λ) :
    (δ₁ * δ₂).toWeight = δ₁.toWeight * δ₂.toWeight := by
  ext1 u
  rfl

/-- Restriction to `ℤ_[p]ˣ` preserves inverses of characters. -/
@[simp]
theorem toWeight_inv (δ : PadicUnitsCharacter p Λ) : δ⁻¹.toWeight = δ.toWeight⁻¹ := by
  ext1 u
  rfl

end CommMonoid

end PadicUnitsCharacter

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

/-- On `u ∈ ℤ_[p]ˣ`, `ω(u) = u mod p`. -/
theorem coe_padicModPCyclotomicCharacter_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    (padicModPCyclotomicCharacter p (padicIntUnitsInclusion p u) : ZMod p) =
      PadicInt.toZMod (u : ℤ_[p]) := by
  simp [padicModPCyclotomicCharacter]

/-- Pushing `x ↦ x |x|` along any ring homomorphism `f : ℤ_[p] →+* k` into a topological ring
`k` of characteristic `p` (for instance the residue field `𝓀[L]` of a finite extension `L / ℚ_[p]`)
agrees with pushing `ω` along `ZMod.castHom`. -/
theorem unitsMap_ringHom_comp_padicUnitPart {k : Type*} [Ring k] [CharP k p]
    [TopologicalSpace k] (f : ℤ_[p] →+* k) :
    (ContinuousMonoidHom.unitsMap ⟨f.toMonoidHom, f.continuous_of_padicInt_charP⟩).comp
        (padicUnitPart p) =
      (ContinuousMonoidHom.unitsMap
          ⟨(ZMod.castHom (dvd_refl p) k).toMonoidHom, continuous_of_discreteTopology⟩).comp
        (padicModPCyclotomicCharacter p) :=
  ContinuousMonoidHom.unitsMap_ringHom_comp_eq_castHom f (padicUnitPart p)

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

/-- `padicAlgebraMapCharacter p R h` sends `p` to `(p : R)`. -/
theorem coe_padicAlgebraMapCharacter_padicPrimeUnit {R : Type*} [Semiring R] [TopologicalSpace R]
    [Algebra ℚ_[p] R] (h : Continuous (algebraMap ℚ_[p] R)) :
    (padicAlgebraMapCharacter p R h (padicPrimeUnit p) : R) = (p : R) := by
  simp [padicAlgebraMapCharacter]

end CanonicalCharacters

end TauCeti
