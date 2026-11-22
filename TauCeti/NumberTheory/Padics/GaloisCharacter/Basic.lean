/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.LocalField.Unramified.Character
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.Padics.UnitsSplitting
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Continuous characters of `ℚ_pˣ`

For a prime `p` and a topological monoid `Λ`, a continuous character of `ℚ_pˣ` with values in `Λ`
is a continuous homomorphism `δ : ℚ_[p]ˣ →ₜ* Λˣ` (`TauCeti.PadicUnitsChar p Λ`).

Using `TauCeti.padicUnitsCharacterEquiv p Λˣ`, when `Λ` is a commutative topological monoid with
continuous multiplication, `TauCeti.PadicUnitsChar p Λ` decomposes as `Λˣ × TauCeti.WeightSpace p Λ`
via `δ ↦ (δ(p), δ|_{ℤ_pˣ})`. For two unramified characters `unramifiedCharacter ℚ_[p] a`,
`unramifiedCharacter ℚ_[p] b` into an arbitrary topological monoid `Λ`, the pointwise product is a
homomorphism if and only if `a` and `b` commute
(`TauCeti.exists_monoidHom_mul_unramifiedCharacter_iff`), witnessed over `M₂(𝔽₃)` by
`TauCeti.not_exists_monoidHom_mul_unramifiedCharacter_matrix`.

This file also constructs additional canonical characters of `ℚ_[p]ˣ` complementing
`TauCeti.padicUnitPart` and `TauCeti.unramifiedCharacter`:

* `TauCeti.padicModPCyclotomicChar p`: the mod-`p` character `ω : ℚ_[p]ˣ →ₜ* (ZMod p)ˣ`,
  obtained by reducing `TauCeti.padicUnitPart p` modulo `p` (and agreeing with reduction modulo the
  maximal ideal in any finite extension `L / ℚ_[p]`).
* `TauCeti.padicAlgebraMapChar p R h`: the character `x ↦ algebraMap ℚ_[p] R x` into a topological
  `ℚ_[p]`-algebra `R` with continuous structure map.

## Main definitions

* `TauCeti.PadicUnitsChar`: the type `ℚ_[p]ˣ →ₜ* Λˣ` of continuous `Λ`-valued characters.
* `TauCeti.padicModPCyclotomicChar`, `TauCeti.padicAlgebraMapChar`: the mod-`p` cyclotomic
  character `ω` and the algebra-map character `x ↦ x`.

## References

* P. Colmez, *Représentations de GL₂(ℚ_p) et (φ, Γ)-modules*, Astérisque 330 (2010),
  Introduction §1.
* P. Colmez, *Représentations triangulines de dimension 2*, Astérisque 319 (2008), §0.1.
* P. Colmez, G. Dospinescu, V. Paškūnas, *The p-adic local Langlands correspondence for GL₂(ℚ_p)*,
  Camb. J. Math. 2 (2014), §1.1.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

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

/-- Any continuous ring homomorphism `ℤ_[p] →+* k` into a discrete ring of characteristic `p`
factors through `PadicInt.toZMod` via `ZMod.castHom`. -/
theorem padicInt_ringHom_eq_castHom_comp_toZMod {k : Type*} [Ring k] [CharP k p]
    [TopologicalSpace k] [DiscreteTopology k] (f : ℤ_[p] →+* k) (hf : Continuous f) :
    f = (ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod :=
  DFunLike.coe_injective <|
    PadicInt.denseRange_natCast.equalizer hf
      ((continuous_of_discreteTopology (f := ZMod.castHom (dvd_refl p) k)).comp
        PadicInt.continuous_toZMod)
      (funext fun n ↦ by simp)

/-- Pushing `x ↦ x |x|` along any continuous ring homomorphism `ℤ_[p] →+* k` into a discrete ring
`k` of characteristic `p` (for instance the residue field `𝓀[L]` of a finite extension `L / ℚ_[p]`)
agrees with pushing `ω` along `ZMod.castHom`. -/
theorem mapMonoidHom_ringHom_padicUnitPart {k : Type*} [Ring k] [CharP k p]
    [TopologicalSpace k] [DiscreteTopology k] (f : ℤ_[p] →+* k) (hf : Continuous f) :
    PadicUnitsChar.mapMonoidHom (padicUnitPart p) f.toMonoidHom hf =
      (padicModPCyclotomicChar p).mapMonoidHom
        (ZMod.castHom (dvd_refl p) k).toMonoidHom continuous_of_discreteTopology := by
  ext1 x
  apply Units.ext
  simpa using DFunLike.congr_fun (padicInt_ringHom_eq_castHom_comp_toZMod p f hf)
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

section NoncommutativeCounterexample

/-- **Commutativity criterion for pointwise products of unramified characters.** For any
topological monoid `Λ` and units `a, b : Λˣ`, the pointwise product `x ↦ μ_a(x) * μ_b(x)` is a
group homomorphism on `ℚ_[p]ˣ` if and only if `a` and `b` commute. -/
theorem exists_monoidHom_mul_unramifiedCharacter_iff {p : ℕ} [Fact p.Prime] {Λ : Type*}
    [Monoid Λ] [TopologicalSpace Λ] (a b : Λˣ) :
    (∃ δ : ℚ_[p]ˣ →* Λˣ,
      ∀ x : ℚ_[p]ˣ, δ x = unramifiedCharacter ℚ_[p] a x * unramifiedCharacter ℚ_[p] b x) ↔
      Commute a b := by
  constructor
  · rintro ⟨δ, hδ⟩
    have hsq : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
      have ha : unramifiedCharacter ℚ_[p] a (padicPrimeUnit p) = a :=
        unramifiedCharacter_apply_of_isUniformizer a (isUniformizer_padicPrimeUnit p)
      have hb : unramifiedCharacter ℚ_[p] b (padicPrimeUnit p) = b :=
        unramifiedCharacter_apply_of_isUniformizer b (isUniformizer_padicPrimeUnit p)
      have h1 : δ (padicPrimeUnit p ^ 2) = (a * b) ^ 2 := by
        rw [map_pow, hδ, ha, hb]
      have h2 : δ (padicPrimeUnit p ^ 2) = a ^ 2 * b ^ 2 := by
        rw [hδ, map_pow, map_pow, ha, hb]
      exact h1.symm.trans h2
    rw [sq, sq, sq] at hsq
    have h1 : b * a * b = a * b * b :=
      mul_left_cancel (a := a) (by simpa [mul_assoc] using hsq)
    exact (mul_right_cancel h1).symm
  · intro hcomm
    refine ⟨(unramifiedCharacter ℚ_[p] (a * b)).toMonoidHom, fun x ↦ ?_⟩
    simp [hcomm.mul_zpow]

/-- The upper-triangular unipotent unit `A = !![1, 1; 0, 1]` in `M₂(𝔽₃)ˣ`. -/
private def matA : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ where
  val := !![(1 : ZMod 3), 1; 0, 1]
  inv := !![(1 : ZMod 3), 2; 0, 1]
  val_inv := by decide
  inv_val := by decide

/-- The lower-triangular unipotent unit `B = !![1, 0; 1, 1]` in `M₂(𝔽₃)ˣ`. -/
private def matB : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ where
  val := !![(1 : ZMod 3), 0; 1, 1]
  inv := !![(1 : ZMod 3), 0; 2, 1]
  val_inv := by decide
  inv_val := by decide

/-- **Commutativity of the coefficient ring is necessary for pointwise multiplication of
characters.** Over `M₂(𝔽₃)`, the pointwise product of the unramified characters sending `p` to
`!![1, 1; 0, 1]` and `!![1, 0; 1, 1]` is not a homomorphism on `ℚ_[p]ˣ`, because these matrices do
not commute. -/
theorem not_exists_monoidHom_mul_unramifiedCharacter_matrix (p : ℕ) [Fact p.Prime] :
    ∃ δ₁ δ₂ : PadicUnitsChar p (Matrix (Fin 2) (Fin 2) (ZMod 3)),
      ¬ ∃ δ : ℚ_[p]ˣ →* (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ,
        ∀ x : ℚ_[p]ˣ, δ x = δ₁ x * δ₂ x := by
  refine ⟨unramifiedCharacter ℚ_[p] matA, unramifiedCharacter ℚ_[p] matB, ?_⟩
  rw [exists_monoidHom_mul_unramifiedCharacter_iff]
  intro hcomm
  have h : (matA : Matrix (Fin 2) (Fin 2) (ZMod 3)) * matB =
      (matB : Matrix (Fin 2) (Fin 2) (ZMod 3)) * matA := by
    simpa [Units.val_mul] using congrArg Units.val hcomm.eq
  exact absurd h (by decide)

end NoncommutativeCounterexample

end TauCeti
