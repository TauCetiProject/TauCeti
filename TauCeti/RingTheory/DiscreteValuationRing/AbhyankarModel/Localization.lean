/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Local rings containing a root in Abhyankar's lemma

Let `B` be a discrete valuation ring with uniformizer `ϖ`, let `u` be a unit and `e` invertible in
`B`, and let `d ≠ 0`. Let `S` be an integrally closed local domain dominating `B` and containing an
`e d`-th root `β` of `u ϖ ^ e`, such that every element of `S` becomes a polynomial in `β` with
coefficients in `B` after multiplication by a nonzero element of `B`. Then `S` is the local ring of
the Abhyankar model `(B[y]/(y ^ e − u))[x]/(x ^ d − ϖ y)` at a maximal ideal, with `x` sent to `β`
(`TauCeti.exists_algEquiv_localization_abhyankarModel`). The map sends `y` to the unit
`β ^ d / ϖ` of `S`, which lies in `S` because `S` is integrally closed.

Consequently `S` is a discrete valuation ring, `β` is a uniformizer of `S`, and the residue field of
`S` is separable over that of `B`. This applies to the local rings at maximal ideals of the
integral closure of `B` in a field `L(β)`, where `L` is the fraction field of `B`.

In Abhyankar's lemma for discrete valuation rings, `A → B` is an extension of discrete valuation
rings with uniformizer `π` of `A` and ramification index `e` invertible in `B`, so that
`π = u ϖ ^ e`, and `β` is a root of `X ^ (e d) − π`. The root `β` is also a uniformizer of the
integral closure `A[β]` of `A` in `K(β)`
(`TauCeti.IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible`). So the results here
say that each such local ring `S` has ramification index one over `A[β]`, and that its residue
field is separable over that of `A[β]`, which is the residue field of `A`, whenever the residue
field extension of `B` over `A` is separable.

## Main results

* `TauCeti.exists_algEquiv_localization_abhyankarModel`: `S` is the local ring of the Abhyankar
  model at a maximal ideal, by an isomorphism sending `x` to `β`.
* `TauCeti.isDiscreteValuationRing_of_pow_eq_unit_mul_pow`: `S` is a discrete valuation ring.
* `TauCeti.irreducible_of_pow_eq_unit_mul_pow`: `β` is a uniformizer of `S`.
* `TauCeti.isSeparable_residueField_of_pow_eq_unit_mul_pow`: the residue field of `S` is
  separable over the residue field of `B`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Lemme 3.6.
* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
-/

public section

open Polynomial IsLocalRing

namespace TauCeti

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S] {ϖ u : B} {e d : ℕ} {β : S}

/-- An `e`-th root `γ` of `u` and a `d`-th root `β` of `ϖ γ` define a map from the Abhyankar model
sending `y` to `γ` and `x` to `β`. -/
private theorem exists_algHom_abhyankarModel {γ : S} (hγ : γ ^ e = algebraMap B S u)
    (hβ : β ^ d = algebraMap B S ϖ * γ) :
    ∃ φ : abhyankarModel ϖ u e d →ₐ[B] S, φ (abhyankarModelRoot ϖ u e d) = β ∧
      φ (algebraMap (standardTameCover B u e) _ (AdjoinRoot.root (X ^ e - C u))) = γ :=
  ⟨AdjoinRoot.liftAlgHom _ (AdjoinRoot.liftAlgHom (X ^ e - C u) (Algebra.ofId B S) γ (by
      simp [hγ])) β (by simp [hβ]),
    AdjoinRoot.liftAlgHom_root _ _ _ _,
    (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (AdjoinRoot.liftAlgHom_root _ _ _ _)⟩

variable [IsDomain B] [IsDiscreteValuationRing B]

/-- The local ring of the Abhyankar model at a maximal ideal is a discrete valuation ring with
uniformizer `x`. -/
private theorem isDiscreteValuationRing_localization_abhyankarModel (hϖ : Irreducible ϖ)
    (hu : IsUnit u) (he : IsUnit (e : B)) (hd : d ≠ 0) (M : Ideal (abhyankarModel ϖ u e d))
    [M.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime M), IsDiscreteValuationRing (Localization.AtPrime M) ∧
      Irreducible (algebraMap _ (Localization.AtPrime M) (abhyankarModelRoot ϖ u e d)) := by
  have := isRegularLocalRing_abhyankarModel (Localization.AtPrime M) M hϖ hu he hd
  have := isDiscreteValuationRing_abhyankarModel (Localization.AtPrime M) M hϖ hu he hd
  exact ⟨inferInstance, inferInstance, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (maximalIdeal_eq_span_abhyankarModelRoot _ M hϖ hu he hd)⟩

variable [IsDomain S]

/-- Let `φ` be a `B`-algebra map from the Abhyankar model to a domain `S`, sending `x` to a nonzero
nonunit `β` and `y` to `γ` with `ϖ γ = β ^ d`, and let `ψ` be its extension to the local ring at a
prime `M`, assumed to be a discrete valuation ring with uniformizer `x`. If every element of `S`
times some nonzero element of `B` is a polynomial in `β` over `B`, then `ψ` is surjective. -/
private theorem surjective_localization_abhyankarModel (hϖ : Irreducible ϖ) {γ : S}
    (hγ : algebraMap B S ϖ * γ = β ^ d) (hβ₀ : β ≠ 0) (hβ : ¬IsUnit β)
    (hgen : ∀ c : S, ∃ s : B, s ≠ 0 ∧ algebraMap B S s * c ∈ Algebra.adjoin B {β})
    (φ : abhyankarModel ϖ u e d →ₐ[B] S) (hφx : φ (abhyankarModelRoot ϖ u e d) = β)
    (hφy : φ (algebraMap (standardTameCover B u e) _ (AdjoinRoot.root (X ^ e - C u))) = γ)
    {M : Ideal (abhyankarModel ϖ u e d)} [M.IsPrime] [IsDomain (Localization.AtPrime M)]
    [IsDiscreteValuationRing (Localization.AtPrime M)]
    (hx : Irreducible (algebraMap _ (Localization.AtPrime M) (abhyankarModelRoot ϖ u e d)))
    (ψ : Localization.AtPrime M →ₐ[B] S) (hψ : ∀ z, ψ (algebraMap _ _ z) = φ z) :
    Function.Surjective ψ := by
  have hψx : ψ (algebraMap _ _ (abhyankarModelRoot ϖ u e d)) = β := by
    rw [hψ, hφx]
  intro c
  -- Write `s c = φ t` with `s = v ϖ ^ k`. Since `ϖ ^ k γ ^ k = β ^ (d k)`, the element
  -- `v⁻¹ t y ^ k` maps to `β ^ (d k) c`, and `ψ` reflects divisibility by `β ^ (d k)`.
  obtain ⟨s, hs, hsc⟩ := hgen c
  obtain ⟨t, ht⟩ := (AlgHom.mem_range φ).mp (Algebra.adjoin_le (Set.singleton_subset_iff.mpr
    ((AlgHom.mem_range φ).mpr ⟨_, hφx⟩)) hsc)
  obtain ⟨k, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs hϖ
  have hv : algebraMap B S ↑v⁻¹ * algebraMap B S ↑v = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have key : φ (algebraMap B (abhyankarModel ϖ u e d) ↑v⁻¹ * t *
      algebraMap (standardTameCover B u e) _ (AdjoinRoot.root (X ^ e - C u)) ^ k) =
        β ^ (d * k) * c := by
    simp only [map_mul, map_pow, ht, AlgHom.commutes, hφy]
    linear_combination (algebraMap B S ϖ ^ k * c * γ ^ k) * hv + c * congrArg (· ^ k) hγ
  rw [← hψ, ← hψx, ← map_pow ψ] at key
  obtain ⟨r, hr⟩ := (IsDiscreteValuationRing.map_dvd_iff ψ hx (hψx ▸ hβ) (hψx ▸ hβ₀)).mp
    ⟨c, key⟩
  rw [hr, map_mul, map_pow, hψx] at key
  exact ⟨r, mul_left_cancel₀ (pow_ne_zero (d * k) hβ₀) key⟩

variable [IsLocalRing S] [IsLocalHom (algebraMap B S)] [IsIntegrallyClosed S] [FaithfulSMul B S]

/-- **Local rings containing a root in Abhyankar's lemma.** Let `B` be a discrete valuation ring
with uniformizer `ϖ`, let `u` be a unit and `e` invertible in `B`, and let `d ≠ 0`. Let `S` be an
integrally closed local domain dominating `B`, with `B → S` injective, containing an `e d`-th root
`β` of `u ϖ ^ e`, such that every element of `S` times some nonzero element of `B` is a polynomial
in `β` over `B`. Then `S` is the local ring of the Abhyankar model
`(B[y]/(y ^ e − u))[x]/(x ^ d − ϖ y)` at a maximal ideal over the maximal ideal of `B`, by a
`B`-algebra isomorphism sending `x` to `β`. -/
theorem exists_algEquiv_localization_abhyankarModel (hϖ : Irreducible ϖ) (hu : IsUnit u)
    (he : IsUnit (e : B)) (hd : d ≠ 0) (hβ : β ^ (e * d) = algebraMap B S (u * ϖ ^ e))
    (hgen : ∀ c : S, ∃ s : B, s ≠ 0 ∧ algebraMap B S s * c ∈ Algebra.adjoin B {β}) :
    ∃ (M : Ideal (abhyankarModel ϖ u e d)) (_ : M.IsMaximal) (_ : M.LiesOver (maximalIdeal B))
      (σ : Localization.AtPrime M ≃ₐ[B] S),
      σ (algebraMap _ _ (abhyankarModelRoot ϖ u e d)) = β := by
  have he₀ : e ≠ 0 := he.neZero_natCast.out
  have hϖS : algebraMap B S ϖ ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective B S)).mpr hϖ.ne_zero
  have hβ₀ : β ≠ 0 := by
    rintro rfl
    rw [zero_pow (mul_ne_zero he₀ hd), eq_comm, map_mul, map_pow] at hβ
    exact mul_ne_zero (hu.map (algebraMap B S)).ne_zero (pow_ne_zero e hϖS) hβ
  have hβm : ¬IsUnit β := fun h ↦ by
    have := h.pow (e * d)
    rw [hβ, isUnit_map_iff, IsUnit.mul_iff, isUnit_pow_iff he₀] at this
    exact hϖ.not_isUnit this.2
  -- `(β ^ d) ^ e` and `ϖ ^ e` are associated, so `γ = β ^ d / ϖ` lies in the integrally closed
  -- ring `S`, and `γ ^ e = u`.
  have hβ' : (β ^ d) ^ e = algebraMap B S u * algebraMap B S ϖ ^ e := by
    rw [← map_pow, ← map_mul, ← hβ]
    ring
  have hassoc : Associated (algebraMap B S ϖ ^ e) ((β ^ d) ^ e) :=
    ⟨(hu.map (algebraMap B S)).unit, by
      rw [IsUnit.unit_spec]
      linear_combination -hβ'⟩
  obtain ⟨γ, hγ'⟩ := (Associated.pow_iff he₀).mp hassoc
  have hγ : (γ : S) ^ e = algebraMap B S u := by
    apply mul_left_cancel₀ (pow_ne_zero e hϖS)
    linear_combination congrArg (· ^ e) hγ' + hβ'
  obtain ⟨φ, hφx, hφy⟩ := exists_algHom_abhyankarModel (d := d) hγ hγ'.symm
  set M := (maximalIdeal S).comap φ
  have : NeZero e := ⟨he₀⟩
  have : NeZero d := ⟨hd⟩
  have : Module.Finite B (abhyankarModel ϖ u e d) := .trans (standardTameCover B u e) _
  have : M.IsMaximal := .of_liesOver_isMaximal M (maximalIdeal B)
  -- `φ` inverts the complement of `M`, so it factors through the localization `ψ` at `M`, a
  -- discrete valuation ring with uniformizer `x`. Then `ψ` is injective as `β ≠ 0`.
  have hunit (y : M.primeCompl) : IsUnit (φ y) := by
    by_contra h
    exact y.2 ((mem_maximalIdeal _).mpr h)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Localization.AtPrime M →ₐ[B] S, ∀ z, ψ (algebraMap _ _ z) = φ z :=
    ⟨IsLocalization.liftAlgHom hunit, fun _ ↦ IsLocalization.lift_eq _ _⟩
  have hψx : ψ (algebraMap _ _ (abhyankarModelRoot ϖ u e d)) = β := by
    rw [hψ, hφx]
  obtain ⟨_, _, hx⟩ := isDiscreteValuationRing_localization_abhyankarModel hϖ hu he hd M
  exact ⟨M, inferInstance, inferInstance, .ofBijective ψ
    ⟨IsDiscreteValuationRing.injective_of_map_ne_zero ψ hx (hψx ▸ hβ₀),
      surjective_localization_abhyankarModel hϖ hγ' hβ₀ hβm hgen φ hφx hφy hx ψ hψ⟩, hψx⟩

/-- Under the hypotheses of `TauCeti.exists_algEquiv_localization_abhyankarModel`, the integrally
closed local domain `S` is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_pow_eq_unit_mul_pow (hϖ : Irreducible ϖ) (hu : IsUnit u)
    (he : IsUnit (e : B)) (hd : d ≠ 0) (hβ : β ^ (e * d) = algebraMap B S (u * ϖ ^ e))
    (hgen : ∀ c : S, ∃ s : B, s ≠ 0 ∧ algebraMap B S s * c ∈ Algebra.adjoin B {β}) :
    IsDiscreteValuationRing S := by
  obtain ⟨M, _, _, σ, -⟩ := exists_algEquiv_localization_abhyankarModel hϖ hu he hd hβ hgen
  obtain ⟨_, _, -⟩ := isDiscreteValuationRing_localization_abhyankarModel hϖ hu he hd M
  exact _root_.IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing σ

/-- **The root is a uniformizer.** Under the hypotheses of
`TauCeti.exists_algEquiv_localization_abhyankarModel`, the `e d`-th root `β` of `u ϖ ^ e` is a
uniformizer of the discrete valuation ring `S`. -/
theorem irreducible_of_pow_eq_unit_mul_pow (hϖ : Irreducible ϖ) (hu : IsUnit u)
    (he : IsUnit (e : B)) (hd : d ≠ 0) (hβ : β ^ (e * d) = algebraMap B S (u * ϖ ^ e))
    (hgen : ∀ c : S, ∃ s : B, s ≠ 0 ∧ algebraMap B S s * c ∈ Algebra.adjoin B {β}) :
    Irreducible β := by
  obtain ⟨M, _, _, σ, hσ⟩ := exists_algEquiv_localization_abhyankarModel hϖ hu he hd hβ hgen
  obtain ⟨_, _, hx⟩ := isDiscreteValuationRing_localization_abhyankarModel hϖ hu he hd M
  rw [← hσ]
  exact hx.map σ

/-- **The residue field extension is separable.** Under the hypotheses of
`TauCeti.exists_algEquiv_localization_abhyankarModel`, the residue field of `S` is separable over
the residue field of `B`. -/
theorem isSeparable_residueField_of_pow_eq_unit_mul_pow (hϖ : Irreducible ϖ) (hu : IsUnit u)
    (he : IsUnit (e : B)) (hd : d ≠ 0) (hβ : β ^ (e * d) = algebraMap B S (u * ϖ ^ e))
    (hgen : ∀ c : S, ∃ s : B, s ≠ 0 ∧ algebraMap B S s * c ∈ Algebra.adjoin B {β}) :
    Algebra.IsSeparable (ResidueField B) (ResidueField S) := by
  obtain ⟨M, _, _, σ, -⟩ := exists_algEquiv_localization_abhyankarModel hϖ hu he hd hβ hgen
  -- `σ` identifies the residue field of the localization at `M` with the residue field of `S`.
  have : IsLocalHom (algebraMap B (Localization.AtPrime M)) :=
    ⟨fun b hb ↦ (isUnit_map_iff (algebraMap B S) b).mp (σ.commutes b ▸ hb.map σ)⟩
  have := isSeparable_residueField_localization_abhyankarModel M
    ((mem_maximalIdeal ϖ).mpr hϖ.not_isUnit) hu he hd
  exact (AlgEquiv.Algebra.isSeparable_iff (ResidueField.mapAlgEquiv' σ)).mp this

end TauCeti
