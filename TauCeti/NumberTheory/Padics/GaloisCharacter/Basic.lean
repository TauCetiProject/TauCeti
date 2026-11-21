/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.Padics.UnitsSplitting
public import TauCeti.NumberTheory.Padics.WeightSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Continuous characters of `ℚ_pˣ`

For a prime `p` and a topological monoid `Λ`, a continuous character of `ℚ_pˣ` with values in `Λ`
is a continuous homomorphism `δ : ℚ_[p]ˣ →ₜ* Λˣ` (`TauCeti.PadicUnitsChar p Λ`).

Using the canonical uniformizer `p` (`TauCeti.padicUniformizer p`), the multiplicative group
`ℚ_[p]ˣ` splits topologically as `Multiplicative ℤ × ℤ_[p]ˣ` via `x ↦ (v_p(x), x · p^{-v_p(x)})`
(`TauCeti.padicUnitsEquivIntProd p`). When `Λ` is a commutative topological monoid with continuous
multiplication, `TauCeti.PadicUnitsChar p Λ` is a commutative group under pointwise multiplication
and decomposes as `Λˣ × TauCeti.WeightSpace p Λ` via `δ ↦ (δ(p), δ|_{ℤ_pˣ})`
(`TauCeti.padicUnitsCharEquivProd p Λ`). For two unramified characters `μ_a`, `μ_b` into an
arbitrary topological monoid `Λ`, the pointwise product is a homomorphism if and only if `a` and
`b` commute (`TauCeti.exists_monoidHom_mul_padicUnramifiedChar_iff`), witnessed over `M₂(𝔽₃)` by
`TauCeti.not_exists_monoidHom_mul_padicUnramifiedChar_matrix`.

This file also constructs the canonical characters of `ℚ_[p]ˣ`:

* `TauCeti.padicNormMulChar p`: the unitary character `x ↦ x |x|_p` with values in `ℤ_[p]ˣ`,
  sending `p ↦ 1` and `u ↦ u` for `u ∈ ℤ_[p]ˣ`.
* `TauCeti.padicModPCyclotomicChar p`: the mod-`p` character `ω : ℚ_[p]ˣ →ₜ* (ZMod p)ˣ`,
  obtained by reducing `padicNormMulChar p` modulo `p` (and agreeing with reduction modulo the
  maximal ideal in any finite extension `L / ℚ_[p]`).
* `TauCeti.padicUnramifiedChar p a`: the unramified character `μ_a : ℚ_[p]ˣ →ₜ* Λˣ` sending
  `p ↦ a` and trivial on `ℤ_[p]ˣ`.
* `TauCeti.padicAlgebraMapChar p R h`: the character `x ↦ algebraMap ℚ_[p] R x` into a topological
  `ℚ_[p]`-algebra `R` with continuous structure map.

## Main definitions

* `TauCeti.PadicUnitsChar`: the type `ℚ_[p]ˣ →ₜ* Λˣ` of continuous `Λ`-valued characters.
* `TauCeti.padicUnitsCharEquivProd`: the group isomorphism
  `PadicUnitsChar p Λ ≃* Λˣ × WeightSpace p Λ` for commutative `Λ`.
* `TauCeti.padicNormMulChar`, `TauCeti.padicModPCyclotomicChar`, `TauCeti.padicUnramifiedChar`,
  `TauCeti.padicAlgebraMapChar`: the canonical characters `x |x|`, `ω`, `μ_a`, and `x ↦ x`.

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

/-- A continuous character of `ℚ_[p]ˣ` is determined by its value at `p` and its restriction to
`ℤ_[p]ˣ`. -/
theorem ext_uniformizer_units {δ₁ δ₂ : PadicUnitsChar p Λ}
    (hp : δ₁ (padicUniformizer p) = δ₂ (padicUniformizer p))
    (hu : ∀ u : ℤ_[p]ˣ, δ₁ (padicIntUnitsInclusion p u) = δ₂ (padicIntUnitsInclusion p u)) :
    δ₁ = δ₂ := by
  ext1 x
  rw [eq_padicUniformizer_zpow_mul_unitPart p x, map_mul, map_mul, map_zpow, map_zpow, hp, hu]

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

/-- **Decomposition of the character group `T̂(Λ)`.** For a commutative topological monoid `Λ`
with continuous multiplication, restricting a character to `p` and `ℤ_[p]ˣ` yields a group
isomorphism `PadicUnitsChar p Λ ≃* Λˣ × WeightSpace p Λ`. -/
def padicUnitsCharEquivProd (Λ : Type*) [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ] :
    PadicUnitsChar p Λ ≃* Λˣ × WeightSpace p Λ where
  toFun δ := (δ (padicUniformizer p), δ.toWeight)
  invFun a :=
    (ContinuousMonoidHom.coprod ⟨zpowersHom Λˣ a.1, continuous_of_discreteTopology⟩ a.2).comp
      (padicUnitsEquivIntProd p : ℚ_[p]ˣ →ₜ* Multiplicative ℤ × ℤ_[p]ˣ)
  left_inv δ := PadicUnitsChar.ext_uniformizer_units
    (by simp) (fun u ↦ by simp)
  right_inv := fun ⟨a, κ⟩ ↦ Prod.ext (by simp) (by ext1 u; simp)
  map_mul' _ _ := Prod.ext rfl rfl

/-- The first component of `padicUnitsCharEquivProd p Λ δ` is `δ(p)`. -/
@[simp]
theorem padicUnitsCharEquivProd_apply_fst {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ]
    [ContinuousMul Λ] (δ : PadicUnitsChar p Λ) :
    (padicUnitsCharEquivProd p Λ δ).1 = δ (padicUniformizer p) :=
  (rfl)

/-- The second component of `padicUnitsCharEquivProd p Λ δ` is `δ.toWeight`. -/
@[simp]
theorem padicUnitsCharEquivProd_apply_snd {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ]
    [ContinuousMul Λ] (δ : PadicUnitsChar p Λ) :
    (padicUnitsCharEquivProd p Λ δ).2 = δ.toWeight :=
  (rfl)

/-- The inverse of `padicUnitsCharEquivProd p Λ` sends `(a, κ)` to
`x ↦ a ^ v_p(x) * κ(x p^{-v_p(x)})`. -/
@[simp]
theorem padicUnitsCharEquivProd_symm_apply {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ]
    [ContinuousMul Λ] (a : Λˣ) (κ : WeightSpace p Λ) (x : ℚ_[p]ˣ) :
    (padicUnitsCharEquivProd p Λ).symm (a, κ) x =
      a ^ (x : ℚ_[p]).valuation * κ (padicUnitsEquivIntProd p x).2 := by
  -- Unfold `(padicUnitsCharEquivProd p Λ).symm` on `(a, κ)` and `x`.
  change a ^ (padicUnitsEquivIntProd p x).1.toAdd * κ (padicUnitsEquivIntProd p x).2 = _
  rw [padicUnitsEquivIntProd_apply_fst, toAdd_ofAdd]

end CharacterGroup

section CanonicalCharacters

variable (p : ℕ) [Fact p.Prime]

/-- **The unitary character `x ↦ x |x|_p`** of `ℚ_[p]ˣ` with values in `ℤ_[p]ˣ`. It sends `p ↦ 1`
and acts as the identity on `ℤ_[p]ˣ`; its underlying `p`-adic number at `x` is
`x · p ^ (-v_p(x))` (`coe_padicNormMulChar_apply`). -/
def padicNormMulChar : PadicUnitsChar p ℤ_[p] :=
  (ContinuousMonoidHom.snd (Multiplicative ℤ) ℤ_[p]ˣ).comp
    (padicUnitsEquivIntProd p : ℚ_[p]ˣ →ₜ* Multiplicative ℤ × ℤ_[p]ˣ)

/-- `(x |x|)(p) = 1`. -/
@[simp]
theorem padicNormMulChar_padicUniformizer :
    padicNormMulChar p (padicUniformizer p) = 1 := by
  simp [padicNormMulChar]

/-- `(x |x|)(u) = u` for every `u ∈ ℤ_[p]ˣ`. -/
@[simp]
theorem padicNormMulChar_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    padicNormMulChar p (padicIntUnitsInclusion p u) = u := by
  simp [padicNormMulChar]

/-- `(x |x|)(p ^ k * u) = u` for every `k : ℤ` and `u ∈ ℤ_[p]ˣ`. -/
theorem padicNormMulChar_zpow_mul (k : ℤ) (u : ℤ_[p]ˣ) :
    padicNormMulChar p (padicUniformizer p ^ k * padicIntUnitsInclusion p u) = u := by
  simp

/-- The underlying `p`-adic number of `(x |x|)(x)` is `x · p ^ (-v_p(x))`. -/
theorem coe_padicNormMulChar_apply (x : ℚ_[p]ˣ) :
    ((padicNormMulChar p x : ℤ_[p]) : ℚ_[p]) =
      (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation) :=
  coe_padicUnitsEquivIntProd_apply_snd p x

/-- Restricting `padicNormMulChar p` to `ℤ_[p]ˣ` is the identity weight. -/
@[simp]
theorem padicNormMulChar_toWeight :
    (padicNormMulChar p).toWeight = ContinuousMonoidHom.id ℤ_[p]ˣ := by
  ext1 u
  exact padicNormMulChar_padicIntUnitsInclusion p u

/-- **The mod-`p` cyclotomic character `ω : ℚ_[p]ˣ →ₜ* (ZMod p)ˣ`**, obtained by reducing
`padicNormMulChar p` modulo `p`. -/
def padicModPCyclotomicChar : PadicUnitsChar p (ZMod p) :=
  (padicNormMulChar p).mapMonoidHom PadicInt.toZMod.toMonoidHom PadicInt.continuous_toZMod

/-- `ω(p) = 1`. -/
@[simp]
theorem padicModPCyclotomicChar_padicUniformizer :
    padicModPCyclotomicChar p (padicUniformizer p) = 1 := by
  simp [padicModPCyclotomicChar]

/-- The value of `ω` in `ZMod p` is the mod-`p` reduction of `padicNormMulChar p`. -/
@[simp]
theorem coe_padicModPCyclotomicChar_apply (x : ℚ_[p]ˣ) :
    (padicModPCyclotomicChar p x : ZMod p) = PadicInt.toZMod (padicNormMulChar p x : ℤ_[p]) :=
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
theorem mapMonoidHom_ringHom_padicNormMulChar {k : Type*} [Ring k] [CharP k p]
    [TopologicalSpace k] [DiscreteTopology k] (f : ℤ_[p] →+* k) (hf : Continuous f) :
    (padicNormMulChar p).mapMonoidHom f.toMonoidHom hf =
      (padicModPCyclotomicChar p).mapMonoidHom
        (ZMod.castHom (dvd_refl p) k).toMonoidHom continuous_of_discreteTopology := by
  ext1 x
  apply Units.ext
  simpa using DFunLike.congr_fun (padicInt_ringHom_eq_castHom_comp_toZMod p f hf)
    (padicNormMulChar p x : ℤ_[p])

/-- **The unramified character `μ_a`** of `ℚ_[p]ˣ` sending `p ↦ a` and trivial on `ℤ_[p]ˣ`,
defined for any unit `a` of an arbitrary topological monoid `Λ`. -/
def padicUnramifiedChar {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ] (a : Λˣ) :
    PadicUnitsChar p Λ where
  toMonoidHom :=
    (zpowersHom Λˣ a).comp
      ((MonoidHom.fst (Multiplicative ℤ) ℤ_[p]ˣ).comp (padicUnitsEquivIntProd p).toMonoidHom)
  continuous_toFun :=
    (continuous_of_discreteTopology (f := zpowersHom Λˣ a)).comp
      (continuous_fst.comp (padicUnitsEquivIntProd p).continuous)

/-- `μ_a(x) = a ^ v_p(x)` for every `x : ℚ_[p]ˣ`. -/
@[simp]
theorem padicUnramifiedChar_apply {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ] (a : Λˣ)
    (x : ℚ_[p]ˣ) : padicUnramifiedChar p a x = a ^ (x : ℚ_[p]).valuation := by
  -- Unfold `padicUnramifiedChar` on `x` before rewriting the first projection.
  change a ^ (padicUnitsEquivIntProd p x).1.toAdd = _
  rw [padicUnitsEquivIntProd_apply_fst, toAdd_ofAdd]

/-- `μ_a(p) = a`. -/
theorem padicUnramifiedChar_padicUniformizer {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ]
    (a : Λˣ) : padicUnramifiedChar p a (padicUniformizer p) = a := by
  simp

/-- `μ_a(u) = 1` for every `u ∈ ℤ_[p]ˣ`. -/
theorem padicUnramifiedChar_padicIntUnitsInclusion {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ]
    (a : Λˣ) (u : ℤ_[p]ˣ) : padicUnramifiedChar p a (padicIntUnitsInclusion p u) = 1 := by
  rw [padicUnramifiedChar_apply, valuation_padicIntUnitsInclusion, zpow_zero]

/-- The restriction of `μ_a` to `ℤ_[p]ˣ` is the trivial weight. -/
@[simp]
theorem padicUnramifiedChar_toWeight {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ] (a : Λˣ) :
    (padicUnramifiedChar p a).toWeight = 1 := by
  ext1 u
  exact padicUnramifiedChar_padicIntUnitsInclusion p a u

/-- `μ_1 = 1`. -/
@[simp]
theorem padicUnramifiedChar_one {Λ : Type*} [Monoid Λ] [TopologicalSpace Λ] :
    padicUnramifiedChar p (1 : Λˣ) = 1 := by
  ext1 x
  simp

/-- `μ_{a * b} = μ_a * μ_b` in a commutative topological monoid with continuous multiplication. -/
@[simp]
theorem padicUnramifiedChar_mul {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ]
    (a b : Λˣ) :
    padicUnramifiedChar p (a * b) = padicUnramifiedChar p a * padicUnramifiedChar p b := by
  ext1 x
  simp [mul_zpow]

/-- `μ_{a⁻¹} = μ_a⁻¹` in a commutative topological monoid with continuous multiplication. -/
@[simp]
theorem padicUnramifiedChar_inv {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ]
    (a : Λˣ) : padicUnramifiedChar p a⁻¹ = (padicUnramifiedChar p a)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← padicUnramifiedChar_mul, inv_mul_cancel, padicUnramifiedChar_one]

/-- The group homomorphism `a ↦ μ_a` from `Λˣ` into `PadicUnitsChar p Λ`. -/
def padicUnramifiedCharHom (Λ : Type*) [CommMonoid Λ] [TopologicalSpace Λ] [ContinuousMul Λ] :
    Λˣ →* PadicUnitsChar p Λ where
  toFun := padicUnramifiedChar p
  map_one' := padicUnramifiedChar_one p
  map_mul' := padicUnramifiedChar_mul p

@[simp]
theorem padicUnramifiedCharHom_apply {Λ : Type*} [CommMonoid Λ] [TopologicalSpace Λ]
    [ContinuousMul Λ] (a : Λˣ) : padicUnramifiedCharHom p Λ a = padicUnramifiedChar p a :=
  (rfl)

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
theorem coe_padicAlgebraMapChar_padicUniformizer {R : Type*} [Semiring R] [TopologicalSpace R]
    [Algebra ℚ_[p] R] (h : Continuous (algebraMap ℚ_[p] R)) :
    (padicAlgebraMapChar p R h (padicUniformizer p) : R) = (p : R) := by
  simp [padicAlgebraMapChar]

end CanonicalCharacters

section NoncommutativeCounterexample

/-- **Commutativity criterion for pointwise products of unramified characters.** For any
topological monoid `Λ` and units `a, b : Λˣ`, the pointwise product `x ↦ μ_a(x) * μ_b(x)` is a
group homomorphism on `ℚ_[p]ˣ` if and only if `a` and `b` commute. -/
theorem exists_monoidHom_mul_padicUnramifiedChar_iff {p : ℕ} [Fact p.Prime] {Λ : Type*} [Monoid Λ]
    [TopologicalSpace Λ] (a b : Λˣ) :
    (∃ δ : ℚ_[p]ˣ →* Λˣ,
      ∀ x : ℚ_[p]ˣ, δ x = padicUnramifiedChar p a x * padicUnramifiedChar p b x) ↔
      Commute a b := by
  constructor
  · rintro ⟨δ, hδ⟩
    have hsq : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
      have h1 : δ (padicUniformizer p ^ 2) = (a * b) ^ 2 := by
        rw [map_pow, hδ, padicUnramifiedChar_padicUniformizer,
          padicUnramifiedChar_padicUniformizer]
      have h2 : δ (padicUniformizer p ^ 2) = a ^ 2 * b ^ 2 := by
        rw [hδ, map_pow, map_pow, padicUnramifiedChar_padicUniformizer,
          padicUnramifiedChar_padicUniformizer]
      exact h1.symm.trans h2
    rw [sq, sq, sq] at hsq
    have h1 : b * a * b = a * b * b :=
      mul_left_cancel (a := a) (by simpa [mul_assoc] using hsq)
    exact (mul_right_cancel h1).symm
  · intro hcomm
    refine ⟨(padicUnramifiedChar p (a * b)).toMonoidHom, fun x ↦ ?_⟩
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
theorem not_exists_monoidHom_mul_padicUnramifiedChar_matrix (p : ℕ) [Fact p.Prime] :
    ∃ δ₁ δ₂ : PadicUnitsChar p (Matrix (Fin 2) (Fin 2) (ZMod 3)),
      ¬ ∃ δ : ℚ_[p]ˣ →* (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ,
        ∀ x : ℚ_[p]ˣ, δ x = δ₁ x * δ₂ x := by
  refine ⟨padicUnramifiedChar p matA, padicUnramifiedChar p matB, ?_⟩
  rw [exists_monoidHom_mul_padicUnramifiedChar_iff]
  intro hcomm
  have h : (matA : Matrix (Fin 2) (Fin 2) (ZMod 3)) * matB =
      (matB : Matrix (Fin 2) (Fin 2) (ZMod 3)) * matA := by
    simpa [Units.val_mul] using congrArg Units.val hcomm.eq
  exact absurd h (by decide)

end NoncommutativeCounterexample

end TauCeti
