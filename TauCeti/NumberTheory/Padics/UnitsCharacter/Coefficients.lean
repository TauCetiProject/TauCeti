/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.Padics.UnitsCharacter.Basic
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic

/-!
# Coefficient-valued continuous characters of `ℚ_pˣ`

For a prime `p` and a topological monoid `Λ`, a continuous character of `ℚ_pˣ` with values in `Λ`
is a continuous homomorphism `δ : ℚ_[p]ˣ →ₜ* Λˣ` (`TauCeti.PadicUnitsChar p Λ`).

Using `TauCeti.padicUnitsCharacterEquiv p Λˣ`, when `Λ` is a commutative topological monoid with
continuous multiplication, `TauCeti.PadicUnitsChar p Λ` decomposes as `Λˣ × TauCeti.WeightSpace p Λ`
via `δ ↦ (δ(p), δ|_{ℤ_pˣ})`.

This file also constructs additional canonical characters of `ℚ_[p]ˣ` complementing
`TauCeti.padicUnitPart` and `TauCeti.unramifiedCharacter`:

* `TauCeti.padicModPCyclotomicChar p`: the mod-`p` character `ω : ℚ_[p]ˣ →ₜ* (ZMod p)ˣ`,
  obtained by reducing `TauCeti.padicUnitPart p` modulo `p`. After pushing forward to the residue
  field `k` of a finite extension `L / ℚ_[p]` along the induced maps `ℤ_[p] →+* k` and
  `ZMod p →+* k`, `TauCeti.padicUnitPart p` agrees with the pushforward of `ω`
  (`TauCeti.mapMonoidHom_ringHom_padicUnitPart`).
* `TauCeti.padicAlgebraMapChar p R h`: the character `x ↦ algebraMap ℚ_[p] R x` into a topological
  `ℚ_[p]`-algebra `R` with continuous structure map.

## Main definitions

* `TauCeti.PadicUnitsChar`: the type `ℚ_[p]ˣ →ₜ* Λˣ` of continuous `Λ`-valued characters.
* `TauCeti.PadicUnitsChar.toWeight`: restriction to `ℤ_[p]ˣ` as a weight in
  `TauCeti.WeightSpace p Λ`.
* `TauCeti.PadicUnitsChar.mapMonoidHom`: pushforward of a character along a continuous monoid
  homomorphism.
* `TauCeti.padicModPCyclotomicChar`, `TauCeti.padicAlgebraMapChar`: the mod-`p` cyclotomic
  character `ω` and the algebra-map character `x ↦ x`.

## Main results

* `TauCeti.mapMonoidHom_ringHom_padicUnitPart`: pushing `padicUnitPart p` along any
  `f : ℤ_[p] →+* k` with `[CharP k p]` agrees with pushing `padicModPCyclotomicChar p` along
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
instance makes `PadicUnitsChar p Λ` a commutative group under pointwise multiplication. -/
abbrev PadicUnitsChar (Λ : Type*) [Monoid Λ] [TopologicalSpace Λ] : Type _ :=
  ℚ_[p]ˣ →ₜ* Λˣ

namespace PadicUnitsChar

variable {p}

section Monoid

variable {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ]

/-- The restriction of a continuous character of `ℚ_[p]ˣ` to `ℤ_[p]ˣ`, viewed as a weight in
`TauCeti.WeightSpace p Λ`. -/
def toWeight (δ : PadicUnitsChar p Λ) : WeightSpace p Λ :=
  δ.comp (padicIntUnitsInclusion p)

/-- Evaluating `δ.toWeight` at `u : ℤ_[p]ˣ` evaluates `δ` at `u` viewed in `ℚ_[p]ˣ`. -/
@[simp]
theorem toWeight_apply (δ : PadicUnitsChar p Λ) (u : ℤ_[p]ˣ) :
    δ.toWeight u = δ (padicIntUnitsInclusion p u) :=
  (rfl)

/-- Restriction to `ℤ_[p]ˣ` sends the trivial character to the trivial weight. -/
@[simp]
theorem toWeight_one : (1 : PadicUnitsChar p Λ).toWeight = 1 := by
  ext1 u
  rfl

/-- Pushforward of a character along a continuous monoid homomorphism `f : Λ →* R`. -/
def mapMonoidHom (δ : PadicUnitsChar p Λ) {R : Type*} [Monoid R] [TopologicalSpace R]
    (f : Λ →* R) (hf : Continuous f) : PadicUnitsChar p R :=
  ContinuousMonoidHom.comp ⟨Units.map f, hf.units_map f⟩ δ

/-- Pushforward along `f` evaluates pointwise via `Units.map f`. -/
@[simp]
theorem mapMonoidHom_apply (δ : PadicUnitsChar p Λ) {R : Type*} [Monoid R] [TopologicalSpace R]
    (f : Λ →* R) (hf : Continuous f) (x : ℚ_[p]ˣ) :
    δ.mapMonoidHom f hf x = Units.map f (δ x) :=
  (rfl)

/-- The underlying value of `δ.mapMonoidHom f hf x` in `R` is `f (δ x)`. -/
theorem coe_mapMonoidHom_apply (δ : PadicUnitsChar p Λ) {R : Type*} [Monoid R] [TopologicalSpace R]
    (f : Λ →* R) (hf : Continuous f) (x : ℚ_[p]ˣ) :
    (δ.mapMonoidHom f hf x : R) = f (δ x : Λ) :=
  (rfl)

/-- Pushforward sends the trivial character to the trivial character. -/
@[simp]
theorem mapMonoidHom_one {R : Type*} [Monoid R] [TopologicalSpace R]
    (f : Λ →* R) (hf : Continuous f) :
    (1 : PadicUnitsChar p Λ).mapMonoidHom f hf = 1 := by
  ext1 _
  exact map_one (Units.map f)

end Monoid

section CommMonoid

variable {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ]

/-- Restriction to `ℤ_[p]ˣ` preserves products of characters. -/
@[simp]
theorem toWeight_mul (δ₁ δ₂ : PadicUnitsChar p Λ) :
    (δ₁ * δ₂).toWeight = δ₁.toWeight * δ₂.toWeight := by
  ext1 u
  rfl

/-- Restriction to `ℤ_[p]ˣ` preserves inverses of characters. -/
@[simp]
theorem toWeight_inv (δ : PadicUnitsChar p Λ) : δ⁻¹.toWeight = δ.toWeight⁻¹ := by
  ext1 u
  rfl

/-- Pushforward along a continuous monoid homomorphism between commutative topological monoids
preserves products of characters. -/
@[simp]
theorem mapMonoidHom_mul (δ₁ δ₂ : PadicUnitsChar p Λ) {R : Type*} [CommMonoid R]
    [TopologicalSpace R] [ContinuousMul R] (f : Λ →* R) (hf : Continuous f) :
    (δ₁ * δ₂).mapMonoidHom f hf = δ₁.mapMonoidHom f hf * δ₂.mapMonoidHom f hf := by
  ext1 x
  exact map_mul (Units.map f) (δ₁ x) (δ₂ x)

/-- Pushforward along a continuous monoid homomorphism between commutative topological monoids
preserves inverses of characters. -/
@[simp]
theorem mapMonoidHom_inv (δ : PadicUnitsChar p Λ) {R : Type*} [CommMonoid R]
    [TopologicalSpace R] [ContinuousMul R] (f : Λ →* R) (hf : Continuous f) :
    δ⁻¹.mapMonoidHom f hf = (δ.mapMonoidHom f hf)⁻¹ := by
  ext1 x
  exact map_inv (Units.map f) (δ x)

end CommMonoid

end PadicUnitsChar

end CharacterGroup

section CanonicalCharacters

variable (p : ℕ) [Fact p.Prime]

/-- **The mod-`p` cyclotomic character `ω : ℚ_[p]ˣ →ₜ* (ZMod p)ˣ`**, obtained by reducing
`TauCeti.padicUnitPart p` modulo `p`. -/
def padicModPCyclotomicChar : PadicUnitsChar p (ZMod p) :=
  PadicUnitsChar.mapMonoidHom (padicUnitPart p)
    PadicInt.toZMod.toMonoidHom PadicInt.continuous_toZMod

/-- `ω(p) = 1`. -/
@[simp]
theorem padicModPCyclotomicChar_padicPrimeUnit :
    padicModPCyclotomicChar p (padicPrimeUnit p) = 1 := by
  simp [padicModPCyclotomicChar]

/-- The value of `ω` in `ZMod p` is the mod-`p` reduction of `padicUnitPart p`. -/
@[simp]
theorem coe_padicModPCyclotomicChar_apply (x : ℚ_[p]ˣ) :
    (padicModPCyclotomicChar p x : ZMod p) = PadicInt.toZMod (padicUnitPart p x : ℤ_[p]) :=
  (rfl)

/-- On `u ∈ ℤ_[p]ˣ`, `ω(u) = u mod p`. -/
theorem coe_padicModPCyclotomicChar_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    (padicModPCyclotomicChar p (padicIntUnitsInclusion p u) : ZMod p) =
      PadicInt.toZMod (u : ℤ_[p]) := by
  simp [padicModPCyclotomicChar]

/-- Pushing `x ↦ x |x|` along any ring homomorphism `f : ℤ_[p] →+* k` into a topological ring
`k` of characteristic `p` (for instance the residue field `𝓀[L]` of a finite extension `L / ℚ_[p]`)
agrees with pushing `ω` along `ZMod.castHom`. -/
theorem mapMonoidHom_ringHom_padicUnitPart {k : Type*} [Ring k] [CharP k p]
    [TopologicalSpace k] (f : ℤ_[p] →+* k) :
    PadicUnitsChar.mapMonoidHom (padicUnitPart p) f.toMonoidHom (PadicInt.continuous_of_charP f) =
      (padicModPCyclotomicChar p).mapMonoidHom
        (ZMod.castHom (dvd_refl p) k).toMonoidHom continuous_of_discreteTopology := by
  ext1 x
  apply Units.ext
  simpa using DFunLike.congr_fun (PadicInt.ringHom_eq_castHom_comp_toZMod f)
    (padicUnitPart p x : ℤ_[p])

/-- The canonical character `x ↦ algebraMap ℚ_[p] R x` into a topological `ℚ_[p]`-algebra `R`
whose structure map is continuous. -/
def padicAlgebraMapChar (R : Type*) [Semiring R] [TopologicalSpace R] [Algebra ℚ_[p] R]
    (h : Continuous (algebraMap ℚ_[p] R)) : PadicUnitsChar p R where
  toMonoidHom := Units.map (algebraMap ℚ_[p] R).toMonoidHom
  continuous_toFun := h.units_map _

/-- The underlying value of `padicAlgebraMapChar p R h x` is `algebraMap ℚ_[p] R x`. -/
@[simp]
theorem coe_padicAlgebraMapChar_apply {R : Type*} [Semiring R] [TopologicalSpace R]
    [Algebra ℚ_[p] R] (h : Continuous (algebraMap ℚ_[p] R)) (x : ℚ_[p]ˣ) :
    (padicAlgebraMapChar p R h x : R) = algebraMap ℚ_[p] R (x : ℚ_[p]) :=
  (rfl)

/-- `padicAlgebraMapChar p R h` sends `p` to `(p : R)`. -/
theorem coe_padicAlgebraMapChar_padicPrimeUnit {R : Type*} [Semiring R] [TopologicalSpace R]
    [Algebra ℚ_[p] R] (h : Continuous (algebraMap ℚ_[p] R)) :
    (padicAlgebraMapChar p R h (padicPrimeUnit p) : R) = (p : R) := by
  simp [padicAlgebraMapChar]

end CanonicalCharacters

end TauCeti
