/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.NumberTheory.Padics.RingHoms
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

* `TauCeti.padicUniformizer`: the prime `p` as a unit of `ℚ_[p]`.
* `TauCeti.padicIntUnitsInclusion`: the continuous inclusion `ℤ_[p]ˣ →ₜ* ℚ_[p]ˣ`.
* `TauCeti.unitFiltrationZeroPadicEquiv`: the topological group isomorphism
  `unitFiltration ℚ_[p] 0 ≃ₜ* ℤ_[p]ˣ`.
* `TauCeti.padicUnitsEquivIntProd`: the canonical splitting
  `ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ`.
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

section Splitting

variable (p : ℕ) [Fact p.Prime]

/-- The prime `p`, viewed as a unit of `ℚ_[p]`. It is the canonical uniformizer of `ℚ_[p]`. -/
def padicUniformizer : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- The underlying `p`-adic number of `padicUniformizer p` is `p`. -/
@[simp]
theorem coe_padicUniformizer : (padicUniformizer p : ℚ_[p]) = (p : ℚ_[p]) :=
  (rfl)

/-- `padicUniformizer p` is a uniformizer of `ℚ_[p]`. -/
theorem isUniformizer_padicUniformizer : IsUniformizer ℚ_[p] (padicUniformizer p) :=
  Padic.isUniformizer_natCast_self p

/-- The normalized valuation of `padicUniformizer p` is `1`. -/
@[simp]
theorem normalizedValuation_padicUniformizer :
    normalizedValuation ℚ_[p] (padicUniformizer p) = .ofAdd 1 :=
  (isUniformizer_def _).mp (isUniformizer_padicUniformizer p)

/-- The `p`-adic valuation of `padicUniformizer p` is `1`. -/
theorem valuation_padicUniformizer : ((padicUniformizer p : ℚ_[p]).valuation) = 1 := by
  rw [coe_padicUniformizer, _root_.Padic.valuation_p]

/-- The canonical continuous inclusion `ℤ_[p]ˣ →ₜ* ℚ_[p]ˣ`. -/
def padicIntUnitsInclusion : ℤ_[p]ˣ →ₜ* ℚ_[p]ˣ where
  toMonoidHom := Units.map PadicInt.Coe.ringHom.toMonoidHom
  continuous_toFun := continuous_subtype_val.units_map _

/-- The coercion of `padicIntUnitsInclusion p u` to `ℚ_[p]` is `(u : ℤ_[p])`. -/
@[simp]
theorem coe_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    (padicIntUnitsInclusion p u : ℚ_[p]) = (u : ℤ_[p]) :=
  (rfl)

/-- `padicIntUnitsInclusion p` agrees with `Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom`. -/
theorem padicIntUnitsInclusion_eq_unitsMap_algebraMap (u : ℤ_[p]ˣ) :
    padicIntUnitsInclusion p u = Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u :=
  Units.ext rfl

/-- `padicIntUnitsInclusion p` is injective. -/
theorem padicIntUnitsInclusion_injective : Function.Injective (padicIntUnitsInclusion p) :=
  fun _ _ h ↦ Units.ext <| PadicInt.ext <| congrArg Units.val h

/-- Every unit of `ℤ_[p]` has valuation zero in `ℚ_[p]`. -/
theorem valuation_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    ((padicIntUnitsInclusion p u : ℚ_[p]).valuation) = 0 := by
  rw [coe_padicIntUnitsInclusion, PadicInt.valuation_coe,
    PadicInt.valuation_eq_zero_of_isUnit u.isUnit, Nat.cast_zero]

/-- Every unit of `ℤ_[p]` has normalized valuation `1` in `ℚ_[p]`. -/
@[simp]
theorem normalizedValuation_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    normalizedValuation ℚ_[p] (padicIntUnitsInclusion p u) = 1 :=
  Multiplicative.toAdd.injective <| by
    rw [_root_.Padic.toAdd_normalizedValuation_eq_zero_of_coe_eq (coe_padicIntUnitsInclusion p u),
      toAdd_one]

/-- Every unit of `ℤ_[p]` lies in the depth-zero unit filtration `U(ℚ_[p], 0)`. -/
theorem padicIntUnitsInclusion_mem_unitFiltration_zero (u : ℤ_[p]ˣ) :
    padicIntUnitsInclusion p u ∈ unitFiltration ℚ_[p] 0 := by
  rw [← ker_normalizedValuation, MonoidHom.mem_ker, normalizedValuation_padicIntUnitsInclusion]

/-- Underlying algebraic isomorphism `U(ℚ_[p], 0) ≃* ℤ_[p]ˣ`. -/
private def unitFiltrationZeroPadicMulEquiv : unitFiltration ℚ_[p] 0 ≃* ℤ_[p]ˣ :=
  (unitFiltrationZeroEquivIntegerUnits (K := ℚ_[p])).trans
    (Units.mapEquiv (_root_.Padic.integerRingEquiv p).toMulEquiv)

private theorem unitFiltrationZeroPadicMulEquiv_symm_apply (u : ℤ_[p]ˣ) :
    (unitFiltrationZeroPadicMulEquiv p).symm u =
      ⟨padicIntUnitsInclusion p u, padicIntUnitsInclusion_mem_unitFiltration_zero p u⟩ :=
  Subtype.ext <| Units.ext <| by
    -- Unfold the composition defining `unitFiltrationZeroPadicMulEquiv` on the inverse direction.
    change (((unitFiltrationZeroEquivIntegerUnits (K := ℚ_[p])).symm
      (Units.map (_root_.Padic.integerRingEquiv p).symm.toMonoidHom u) :
        unitFiltration ℚ_[p] 0) : ℚ_[p]ˣ) = (padicIntUnitsInclusion p u : ℚ_[p])
    rw [coe_unitFiltrationZeroEquivIntegerUnits_symm]
    exact _root_.Padic.coe_integerRingEquiv_symm_apply p (u : ℤ_[p])

/-- The depth-zero unit filtration `U(ℚ_[p], 0)` is topologically isomorphic to `ℤ_[p]ˣ`. -/
def unitFiltrationZeroPadicEquiv : unitFiltration ℚ_[p] 0 ≃ₜ* ℤ_[p]ˣ :=
  let e := unitFiltrationZeroPadicMulEquiv p
  have hinv : Continuous e.symm :=
    ((padicIntUnitsInclusion p).continuous.subtype_mk _).congr fun u ↦
      (unitFiltrationZeroPadicMulEquiv_symm_apply p u).symm
  ContinuousMulEquiv.mk e (hinv.continuous_symm_of_equiv_compact_to_t2 (f := e.symm.toEquiv)) hinv

/-- `unitFiltrationZeroPadicEquiv p` preserves the underlying `p`-adic number. -/
@[simp]
theorem coe_unitFiltrationZeroPadicEquiv_apply (u : unitFiltration ℚ_[p] 0) :
    ((unitFiltrationZeroPadicEquiv p u : ℤ_[p]) : ℚ_[p]) = ((u : ℚ_[p]ˣ) : ℚ_[p]) := by
  -- Unfold `unitFiltrationZeroPadicEquiv` into
  -- `integerRingEquiv ∘ unitFiltrationZeroEquivIntegerUnits`.
  change ((_root_.Padic.integerRingEquiv p
    (unitFiltrationZeroEquivIntegerUnits (K := ℚ_[p]) u : 𝒪[ℚ_[p]]) : ℤ_[p]) : ℚ_[p]) = _
  rw [_root_.Padic.coe_integerRingEquiv_apply, coe_unitFiltrationZeroEquivIntegerUnits]

/-- The inverse of `unitFiltrationZeroPadicEquiv p` is `padicIntUnitsInclusion p` into
`U(ℚ_[p], 0)`. -/
@[simp]
theorem coe_unitFiltrationZeroPadicEquiv_symm_apply (u : ℤ_[p]ˣ) :
    ((unitFiltrationZeroPadicEquiv p).symm u : ℚ_[p]ˣ) = padicIntUnitsInclusion p u :=
  congrArg Subtype.val (unitFiltrationZeroPadicMulEquiv_symm_apply p u)

/-- **The canonical splitting `ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ`.** It sends
`x` to `(v_p(x), x · p^{-v_p(x)})`, with inverse `(n, u) ↦ p ^ n * u`. -/
def padicUnitsEquivIntProd : ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ :=
  let e₁ := unitsEquivIntProd ℚ_[p] (padicUniformizer p) (normalizedValuation_padicUniformizer p)
  let e₂ := unitFiltrationZeroPadicEquiv p
  e₁.trans
    { toMulEquiv := MulEquiv.prodCongr (MulEquiv.refl (Multiplicative ℤ)) e₂.toMulEquiv
      continuous_toFun := continuous_fst.prodMk (e₂.continuous.comp continuous_snd)
      continuous_invFun := continuous_fst.prodMk (e₂.symm.continuous.comp continuous_snd) }

/-- The `ℤ`-component of `padicUnitsEquivIntProd p` is the `p`-adic valuation. -/
@[simp]
theorem padicUnitsEquivIntProd_apply_fst (x : ℚ_[p]ˣ) :
    (padicUnitsEquivIntProd p x).1 = .ofAdd (x : ℚ_[p]).valuation :=
  Multiplicative.toAdd.injective <| by
    -- Project onto the first factor of the composite equivalence `padicUnitsEquivIntProd`.
    change (unitsEquivIntProd ℚ_[p] (padicUniformizer p)
      (normalizedValuation_padicUniformizer p) x).1.toAdd = _
    simp

/-- The `ℤ_[p]ˣ`-component of `padicUnitsEquivIntProd p` has underlying `p`-adic number
`x · p ^ (-v_p(x))`. -/
@[simp]
theorem coe_padicUnitsEquivIntProd_apply_snd (x : ℚ_[p]ˣ) :
    (((padicUnitsEquivIntProd p x).2 : ℤ_[p]) : ℚ_[p]) =
      (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation) := by
  -- Project onto the second factor of the composite equivalence `padicUnitsEquivIntProd`.
  change ((unitFiltrationZeroPadicEquiv p (unitsEquivIntProd ℚ_[p] (padicUniformizer p)
    (normalizedValuation_padicUniformizer p) x).2 : ℤ_[p]) : ℚ_[p]) = _
  simp

/-- The inverse of `padicUnitsEquivIntProd p` sends `(n, u)` to `p ^ n * u`. -/
@[simp]
theorem padicUnitsEquivIntProd_symm_apply (z : Multiplicative ℤ × ℤ_[p]ˣ) :
    (padicUnitsEquivIntProd p).symm z =
      padicUniformizer p ^ z.1.toAdd * padicIntUnitsInclusion p z.2 := by
  -- Unfold the inverse of the composite equivalence `padicUnitsEquivIntProd`.
  change (unitsEquivIntProd ℚ_[p] (padicUniformizer p)
    (normalizedValuation_padicUniformizer p)).symm
    (z.1, (unitFiltrationZeroPadicEquiv p).symm z.2) = _
  simp

/-- `padicUnitsEquivIntProd p` sends `p` to `(1, 1)`. -/
@[simp]
theorem padicUnitsEquivIntProd_padicUniformizer :
    padicUnitsEquivIntProd p (padicUniformizer p) = (.ofAdd 1, 1) := by
  rw [← (padicUnitsEquivIntProd p).apply_symm_apply (.ofAdd 1, 1)]
  simp

/-- `padicUnitsEquivIntProd p` sends a unit `u ∈ ℤ_[p]ˣ` to `(0, u)`. -/
@[simp]
theorem padicUnitsEquivIntProd_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    padicUnitsEquivIntProd p (padicIntUnitsInclusion p u) = (1, u) := by
  rw [← (padicUnitsEquivIntProd p).apply_symm_apply (1, u)]
  simp

/-- Every `x : ℚ_[p]ˣ` factors as `p ^ v_p(x) * u` with `u ∈ ℤ_[p]ˣ` the second component of
`padicUnitsEquivIntProd p x`. -/
theorem eq_padicUniformizer_zpow_mul_unitPart (x : ℚ_[p]ˣ) :
    x = padicUniformizer p ^ (x : ℚ_[p]).valuation *
      padicIntUnitsInclusion p (padicUnitsEquivIntProd p x).2 := by
  have h := (padicUnitsEquivIntProd p).symm_apply_apply x
  rw [padicUnitsEquivIntProd_symm_apply, padicUnitsEquivIntProd_apply_fst, toAdd_ofAdd] at h
  exact h.symm

end Splitting

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
    { toMonoidHom :=
        (((zpowersHom Λˣ a.1).comp (MonoidHom.fst (Multiplicative ℤ) ℤ_[p]ˣ)) *
          (a.2.toMonoidHom.comp (MonoidHom.snd (Multiplicative ℤ) ℤ_[p]ˣ))).comp
            (padicUnitsEquivIntProd p).toMonoidHom
      continuous_toFun :=
        ((continuous_of_discreteTopology (f := zpowersHom Λˣ a.1)).comp continuous_fst |>.mul
          (a.2.continuous.comp continuous_snd)).comp (padicUnitsEquivIntProd p).continuous }
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

/-- Pushing `x ↦ x |x|` along any continuous ring homomorphism `ℤ_[p] →+* k` into a discrete ring
`k` of characteristic `p` (for instance the residue field `𝓀[L]` of a finite extension `L / ℚ_[p]`)
agrees with pushing `ω` along `ZMod.castHom`. -/
theorem mapMonoidHom_ringHom_padicNormMulChar {k : Type*} [Ring k] [CharP k p]
    [TopologicalSpace k] [DiscreteTopology k] (f : ℤ_[p] →+* k) (hf : Continuous f) :
    (padicNormMulChar p).mapMonoidHom f.toMonoidHom hf =
      (padicModPCyclotomicChar p).mapMonoidHom
        (ZMod.castHom (dvd_refl p) k).toMonoidHom continuous_of_discreteTopology := by
  -- Two continuous ring homomorphisms `ℤ_[p] →+* k` agree because `ℕ` is dense in `ℤ_[p]`.
  let f₂ : ℤ_[p] →+* k := (ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod
  have hf₂ : Continuous f₂ :=
    (continuous_of_discreteTopology (f := ZMod.castHom (dvd_refl p) k)).comp
      PadicInt.continuous_toZMod
  have heq : (f : ℤ_[p] → k) = f₂ :=
    PadicInt.denseRange_natCast.equalizer hf hf₂ (funext fun n ↦ by simp [f₂])
  ext1 x
  exact Units.ext (congrFun heq (padicNormMulChar p x : ℤ_[p]))

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
