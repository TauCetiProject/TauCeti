/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.GeometricArtinMap
public import TauCeti.NumberTheory.LocalField.Unramified.Character
public import TauCeti.NumberTheory.Padics.UnitsCharacter.Basic

/-!
# Characters of `Kˣ` as Galois characters

Local class field theory, normalized so that a uniformizer corresponds to a geometric Frobenius
(`TauCeti.ClassFieldTheory.geometricArtinMap`), lets one read a continuous character `δ` of `Kˣ`
as a character of the Galois group: a continuous character `ψ` of `G_K^ab` *corresponds* to `δ`
when `ψ(Art_geo(x)) = δ(x)` for every `x ∈ Kˣ`. Since the geometric Artin map has dense image, `ψ`
is unique when it exists (`continuousMonoidHom_ext_geometricArtinMap`).

* For a nonarchimedean local field `K`, a character `ψ` corresponds to the unramified character
  `μ_a : x ↦ a ^ v_K(x)` exactly when `ψ` is trivial on inertia and sends every geometric
  Frobenius to `a` (`comp_geometricArtinMap_eq_unramifiedCharacter_iff`).

* Over `ℚ_p`, the cyclotomic character corresponds to Colmez's character `x|x|`, the unit part
  `ℚ_pˣ → ℤ_pˣ` (`abelianizedLocalCyclotomicCharacter_geometricArtinMap_padic`): under the
  arithmetic normalization the Artin symbol of `p ^ k u` has cyclotomic character `u⁻¹`.

* Over `ℚ_p`, every continuous character `δ` of `ℚ_pˣ` with values in a profinite commutative
  group `A` has a corresponding Galois character `padicGaloisCharacter δ`. Writing
  `δ = μ_{δ(p)} · (δ|_{ℤ_pˣ} ∘ x|x|)`, it is the product of `δ|_{ℤ_pˣ}` composed with the
  cyclotomic character and of the unramified character of `G_K^ab` sending a geometric Frobenius
  to `δ(p)`, which exists because `n ↦ δ(p) ^ n` extends continuously to `ℤ̂` when `A` is profinite.
  This covers Colmez's characters with values in `k_L^×` or `𝒪_L^×`, that is unitary
  characters with values in `L^×`.

Composing a corresponding Galois character with the arithmetic Artin map gives `δ⁻¹`
(`padicGaloisCharacter_artinMap`).

## Main definitions

* `ContinuousMonoidHom.padicGaloisCharacter δ`: the continuous character of `G_{ℚ_p}^ab`
  corresponding to a continuous character `δ` of `ℚ_pˣ` with profinite values.
* `TauCeti.ClassFieldTheory.padicGaloisCharacterEquiv p A`: the correspondence
  `(ℚ_pˣ →ₜ* A) ≃* (G_{ℚ_p}^ab →ₜ* A)`, with inverse `ψ ↦ ψ ∘ Art_geo`.

## Main results

* `TauCeti.ClassFieldTheory.comp_geometricArtinMap_eq_unramifiedCharacter_iff`: a character
  corresponds to `μ_a` exactly when it is unramified and sends geometric Frobenius to `a`.
* `ContinuousMonoidHom.padicGaloisCharacter_geometricArtinMap` and
  `ContinuousMonoidHom.eq_padicGaloisCharacter`: existence and uniqueness of the Galois
  character corresponding to `δ`.
* `ContinuousMonoidHom.padicGaloisCharacter_padicUnitPart`: the Galois character of `x|x|` is
  the cyclotomic character.
* `ContinuousMonoidHom.padicGaloisCharacter_mul`, `ContinuousMonoidHom.padicGaloisCharacter_inv`
  and `ContinuousMonoidHom.padicGaloisCharacter_injective`: the correspondence is an injective
  homomorphism.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §1.
* P. Colmez, *Représentations triangulines de dimension 2*, Astérisque 319 (2008), §0.1.
* P. Colmez, G. Dospinescu, V. Paškūnas, *The p-adic local Langlands correspondence for
  `GL₂(ℚ_p)`*, Camb. J. Math. 2 (2014), §1.1.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti.ClassFieldTheory

section Unramified

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **Unramified characters as Galois characters.** A homomorphism `ψ : G_K^ab → G` corresponds,
through the geometric local Artin map, to the unramified character `μ_a : x ↦ a ^ v_K(x)` exactly
when `ψ` is trivial on the image of inertia and sends every geometric Frobenius to `a`. -/
theorem comp_geometricArtinMap_eq_unramifiedCharacter_iff
    {ψ : Field.absoluteGaloisGroupAbelianization K →* G} {a : G} :
    (∀ x : Kˣ, ψ (geometricArtinMap K x) = unramifiedCharacter K a x) ↔
      (∀ σ ∈ inertiaSubgroup K, ψ σ = 1) ∧
        ∀ σ : Field.absoluteGaloisGroup K, IsArithFrobeniusLift K σ⁻¹ → ψ σ = a := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer K
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (geometricArtinMap K π)
  have hτF : IsArithFrobeniusLift K τ⁻¹ :=
    isArithFrobeniusLift_inv_of_mk_eq_geometricArtinMap_uniformizer K hπ τ hτ
  refine ⟨fun h ↦ ?_, fun ⟨hI, hF⟩ x ↦ ?_⟩
  · -- The image of inertia consists of the Artin symbols of the units of the valuation ring.
    have hI : ∀ σ ∈ inertiaSubgroup K, ψ σ = 1 := fun σ hσ ↦ by
      obtain ⟨u, hu, hσu⟩ : (σ : Field.absoluteGaloisGroupAbelianization K) ∈
          (unitFiltration K 0).map (artinMap K) := by
        rw [map_artinMap_unitFiltration_zero]
        exact ⟨σ, hσ, rfl⟩
      have hu' : valuation K ((u⁻¹ : Kˣ) : K) = 1 := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, (mem_unitFiltration_zero u).1 hu, inv_one]
      rw [← hσu, ← inv_inv (artinMap K u), ← map_inv, ← geometricArtinMap_apply, h,
        unramifiedCharacter_apply_of_valuation_eq_one a hu']
    refine ⟨hI, fun σ hσ ↦ ?_⟩
    -- Two geometric Frobenius lifts differ by an element of inertia.
    have hστ : σ * τ⁻¹ ∈ inertiaSubgroup K := by
      simpa only [inv_inv] using (hσ.isArithFrobeniusLift_iff_inv_mul_mem).1 hτF
    have hσ' : (σ : Field.absoluteGaloisGroupAbelianization K) =
        ((σ * τ⁻¹ : Field.absoluteGaloisGroup K) : Field.absoluteGaloisGroupAbelianization K) *
          (τ : Field.absoluteGaloisGroupAbelianization K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, inv_mul_cancel_right]
    rw [hσ', map_mul, hI _ hστ, one_mul, hτ, h, unramifiedCharacter_apply_of_isUniformizer a hπ]
  · -- Both sides are trivial on units and agree at the uniformizer `π`.
    refine apply_eq_unramifiedCharacter_of_isUniformizer (δ := ψ.comp (geometricArtinMap K))
      (fun u hu ↦ ?_) hπ x |>.trans ?_
    · obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (geometricArtinMap K u)
      rw [MonoidHom.comp_apply, ← hσ]
      exact hI σ (mem_inertiaSubgroup_of_mk_eq_geometricArtinMap K u hu σ hσ)
    · rw [MonoidHom.comp_apply, ← hτ, hF τ hτF]

end Unramified

end TauCeti.ClassFieldTheory

namespace ContinuousMonoidHom

open TauCeti TauCeti.ClassFieldTheory

variable {p : ℕ} [Fact p.Prime]
variable {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [TotallyDisconnectedSpace A]

/-- **The Galois character attached to a character of `ℚ_pˣ`.** For a continuous character `δ` of
`ℚ_pˣ` with values in a profinite commutative group `A`, the continuous character of `G_{ℚ_p}^ab`
that sends the geometric Artin symbol of `x` to `δ(x)`
(`ContinuousMonoidHom.padicGaloisCharacter_geometricArtinMap`). It is the restriction
`δ|_{ℤ_pˣ}` composed with the cyclotomic character, times the unramified character of
`G_{ℚ_p}^ab` sending a geometric Frobenius to `δ(p)`. -/
def padicGaloisCharacter (δ : ℚ_[p]ˣ →ₜ* A) :
    Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* A :=
  (δ.comp (padicIntUnitsInclusion p)).comp (abelianizedLocalCyclotomicCharacter p ℚ_[p]) *
    (zHat.lift (δ (padicPrimeUnit p))⁻¹).comp (unramifiedCoordinate ℚ_[p])

/-- The Galois character of `δ` evaluated at `σ`: `δ` of the cyclotomic character of `σ`, times
`δ(p)` raised to minus the unramified coordinate of `σ`. -/
theorem padicGaloisCharacter_apply (δ : ℚ_[p]ˣ →ₜ* A)
    (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) :
    padicGaloisCharacter δ σ =
      δ (padicIntUnitsInclusion p (abelianizedLocalCyclotomicCharacter p ℚ_[p] σ)) *
        zHat.lift (δ (padicPrimeUnit p))⁻¹ (unramifiedCoordinate ℚ_[p] σ) :=
  (rfl)

/-- **The Galois character of `δ` corresponds to `δ`**: it sends the geometric Artin symbol of `x`
to `δ(x)`. -/
theorem padicGaloisCharacter_geometricArtinMap (δ : ℚ_[p]ˣ →ₜ* A) (x : ℚ_[p]ˣ) :
    padicGaloisCharacter δ (geometricArtinMap ℚ_[p] x) = δ x := by
  -- The cyclotomic factor gives `δ(x|x|)` and the unramified factor gives `δ(p) ^ v(x)`.
  conv_rhs => rw [DFunLike.congr_fun δ.eq_unramifiedCharacter_mul_comp_padicUnitPart x]
  simp [padicGaloisCharacter_apply, mul_comm]

/-- **Uniqueness of the corresponding Galois character.** A continuous character of `G_{ℚ_p}^ab`
that sends the geometric Artin symbol of every `x` to `δ(x)` is `padicGaloisCharacter δ`. -/
theorem eq_padicGaloisCharacter {δ : ℚ_[p]ˣ →ₜ* A}
    {ψ : Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* A}
    (h : ∀ x : ℚ_[p]ˣ, ψ (geometricArtinMap ℚ_[p] x) = δ x) : ψ = padicGaloisCharacter δ :=
  continuousMonoidHom_ext_geometricArtinMap fun x ↦ by
    rw [h, padicGaloisCharacter_geometricArtinMap]

/-- Through the arithmetic local Artin map, the Galois character of `δ` is `δ⁻¹`. -/
@[simp]
theorem padicGaloisCharacter_artinMap (δ : ℚ_[p]ˣ →ₜ* A) (x : ℚ_[p]ˣ) :
    padicGaloisCharacter δ (artinMap ℚ_[p] x) = (δ x)⁻¹ := by
  rw [← inv_inv (artinMap ℚ_[p] x), ← geometricArtinMap_apply, map_inv,
    padicGaloisCharacter_geometricArtinMap]

/-- **The correspondence is multiplicative.** -/
@[simp]
theorem padicGaloisCharacter_mul (δ δ' : ℚ_[p]ˣ →ₜ* A) :
    padicGaloisCharacter (δ * δ') = padicGaloisCharacter δ * padicGaloisCharacter δ' :=
  (eq_padicGaloisCharacter fun x ↦ by simp).symm

/-- The trivial character corresponds to the trivial Galois character. -/
@[simp]
theorem padicGaloisCharacter_one : padicGaloisCharacter (1 : ℚ_[p]ˣ →ₜ* A) = 1 :=
  (eq_padicGaloisCharacter fun x ↦ by simp).symm

variable (p) in
/-- **The Galois character of `x|x|` is the cyclotomic character.** -/
@[simp]
theorem padicGaloisCharacter_padicUnitPart :
    padicGaloisCharacter (padicUnitPart p) = abelianizedLocalCyclotomicCharacter p ℚ_[p] :=
  (eq_padicGaloisCharacter (abelianizedLocalCyclotomicCharacter_geometricArtinMap_padic p)).symm

/-- **The Galois character of an unramified character** `μ_a` is trivial on inertia. -/
theorem padicGaloisCharacter_unramifiedCharacter_apply_of_mem_inertiaSubgroup (a : A)
    {σ : Field.absoluteGaloisGroup ℚ_[p]} (hσ : σ ∈ inertiaSubgroup ℚ_[p]) :
    padicGaloisCharacter (unramifiedCharacter ℚ_[p] a) σ = 1 :=
  (comp_geometricArtinMap_eq_unramifiedCharacter_iff
    (ψ := (unramifiedCharacter ℚ_[p] a).padicGaloisCharacter.toMonoidHom) |>.1
    (padicGaloisCharacter_geometricArtinMap _)).1 σ hσ

/-- **The Galois character of an unramified character** `μ_a` sends every geometric Frobenius
to `a`. -/
theorem padicGaloisCharacter_unramifiedCharacter_apply_of_isArithFrobeniusLift_inv (a : A)
    {σ : Field.absoluteGaloisGroup ℚ_[p]} (hσ : IsArithFrobeniusLift ℚ_[p] σ⁻¹) :
    padicGaloisCharacter (unramifiedCharacter ℚ_[p] a) σ = a :=
  (comp_geometricArtinMap_eq_unramifiedCharacter_iff
    (ψ := (unramifiedCharacter ℚ_[p] a).padicGaloisCharacter.toMonoidHom) |>.1
    (padicGaloisCharacter_geometricArtinMap _)).2 σ hσ

end ContinuousMonoidHom

namespace TauCeti.ClassFieldTheory

open _root_.ContinuousMonoidHom

variable (p : ℕ) [Fact p.Prime]
variable (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [TotallyDisconnectedSpace A]

/-- **Characters of `ℚ_pˣ` are Galois characters.** For a profinite commutative group `A`, the
correspondence `δ ↦ padicGaloisCharacter δ` between continuous characters of `ℚ_pˣ` and of
`G_{ℚ_p}^ab` is a multiplicative bijection; its inverse composes a Galois character with the
geometric local Artin map. -/
def padicGaloisCharacterEquiv :
    (ℚ_[p]ˣ →ₜ* A) ≃* (Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* A) where
  toFun := padicGaloisCharacter
  invFun ψ := ψ.comp ⟨geometricArtinMap ℚ_[p], continuous_geometricArtinMap ℚ_[p]⟩
  left_inv δ := ContinuousMonoidHom.ext (padicGaloisCharacter_geometricArtinMap δ)
  right_inv _ := (eq_padicGaloisCharacter fun _ ↦ rfl).symm
  map_mul' := padicGaloisCharacter_mul

variable {p A}

/-- `TauCeti.ClassFieldTheory.padicGaloisCharacterEquiv` sends `δ` to its Galois character. -/
@[simp]
theorem padicGaloisCharacterEquiv_apply (δ : ℚ_[p]ˣ →ₜ* A) :
    padicGaloisCharacterEquiv p A δ = padicGaloisCharacter δ :=
  (rfl)

/-- The inverse of `TauCeti.ClassFieldTheory.padicGaloisCharacterEquiv` evaluates a Galois
character on geometric Artin symbols. -/
@[simp]
theorem padicGaloisCharacterEquiv_symm_apply_apply
    (ψ : Field.absoluteGaloisGroupAbelianization ℚ_[p] →ₜ* A) (x : ℚ_[p]ˣ) :
    (padicGaloisCharacterEquiv p A).symm ψ x = ψ (geometricArtinMap ℚ_[p] x) :=
  (rfl)

end TauCeti.ClassFieldTheory

namespace ContinuousMonoidHom

open TauCeti.ClassFieldTheory

variable {p : ℕ} [Fact p.Prime]
variable {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [TotallyDisconnectedSpace A]

/-- **The correspondence is injective**: a character of `ℚ_pˣ` is determined by its Galois
character. -/
theorem padicGaloisCharacter_injective :
    Function.Injective (padicGaloisCharacter : (ℚ_[p]ˣ →ₜ* A) → _) :=
  (padicGaloisCharacterEquiv p A).injective

/-- **The correspondence commutes with inverses.** -/
@[simp]
theorem padicGaloisCharacter_inv (δ : ℚ_[p]ˣ →ₜ* A) :
    padicGaloisCharacter δ⁻¹ = (padicGaloisCharacter δ)⁻¹ :=
  map_inv (padicGaloisCharacterEquiv p A) δ

end ContinuousMonoidHom
