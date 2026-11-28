/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Module
public import TauCeti.RingTheory.Derivation.DerivationIdeal
import TauCeti.RingTheory.Derivation.Ideal

/-!
# Derivations of a localization

Let `T` be a localization of a commutative ring `A` at a submonoid `S`, and let `N` be a
`T`-module. Every `R`-derivation `A → N` extends uniquely to an `R`-derivation `T → N`, by the
quotient rule `D (a / s) = (s • D a - a • D s) / s ^ 2`.

Uniqueness is elementary: if `t * s = a` in `T` with `s ∈ S`, the Leibniz rule gives
`s • D t = D a - t • D s`, and `s` acts invertibly on `N`. The uniqueness statement only
needs commutative semirings, left cancellative addition in `N`, and a multiplicative action of `T`.
Existence goes through Kähler differentials: `Ω[T⁄R]` is the localization of `Ω[A⁄R]` at `S`
(`KaehlerDifferential.isLocalizedModule_map`), so the `A`-linear map `Ω[A⁄R] → N` classifying a
derivation of `A` extends to a `T`-linear map `Ω[T⁄R] → N`.

Extending global derivations unconditionally shows that the pushforward of a derivative ideal into
a localization is contained in the derivative ideal of the pushforward
(`Ideal.map_derivativeIdeal_le`), with no finiteness hypothesis.

Conversely, when `Ω[R⁄k]` is finitely presented over `R`, for any `k`-derivation `D` of a
localization `A` of `R` at `S` there exist `s ∈ S` and a global `k`-derivation `δ` of `R` such that
the extension of `δ` to `A` equals `algebraMap R A s • D`: lifting `Ω[R⁄k] →ₗ[R] A` via
`Module.FinitePresentation.exists_lift_of_isLocalizedModule` produces an `R`-linear map
`Ω[R⁄k] →ₗ[R] R` matching `s • D` on `R`, and uniqueness on localizations
(`IsLocalization.eq_of_leibniz`) identifies the extension of `δ` with `algebraMap R A s • D` on
`A`. Under the same finite-presentation hypothesis on `Ω[R⁄k]`, taking derivative ideals therefore
commutes with localization (`Ideal.map_derivativeIdeal`).

## Main declarations

* `IsLocalization.eq_of_leibniz`: two maps `T → N` satisfying the Leibniz rule and agreeing on
  the image of `A` are equal;
* `Derivation.extendOfIsLocalization`: the extension of a derivation of `A` to `T`, with
  `Derivation.extendOfIsLocalization_algebraMap` stating that it extends;
* `Derivation.exists_extendOfIsLocalization_eq_smul`: when `Ω[R⁄k]` is finitely presented over
  `R`, for every derivation `D` of a localization `A` of `R`, there exist `s ∈ S` and a global
  derivation `δ` of `R` whose extension to `A` equals `algebraMap R A s • D`;
* `Ideal.map_derivativeIdeal_le`, `Ideal.map_derivativeIdeal`: unconditional inclusion and
  (under `[Module.FinitePresentation R Ω[R⁄k]]`) equality for derivative ideals under localization;
* `Derivation.algebraMap_notMem_maximalIdeal_sq`: if `D f ∉ Q` for a prime `Q` of `A`, then the
  image of `f` in `A_Q` does not lie in the square of its maximal ideal.
-/

public section

open scoped KaehlerDifferential

/-- Two maps from a localization `T` of a commutative semiring `A` to a type with left
cancellative addition and a multiplicative `T`-action that satisfy the Leibniz rule are equal
once they agree on the image of `A`. In particular a derivation of `T` is determined by its
values on `A`. -/
theorem IsLocalization.eq_of_leibniz {A T N : Type*} [CommSemiring A] [CommSemiring T]
    [Algebra A T] [Add N] [IsLeftCancelAdd N] [MulAction T N]
    (S : Submonoid A) [IsLocalization S T]
    {δ₁ δ₂ : T → N} (h₁ : ∀ x y, δ₁ (x * y) = x • δ₁ y + y • δ₁ x)
    (h₂ : ∀ x y, δ₂ (x * y) = x • δ₂ y + y • δ₂ x)
    (h : ∀ a : A, δ₁ (algebraMap A T a) = δ₂ (algebraMap A T a)) : δ₁ = δ₂ := by
  funext t
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj S t
  apply (IsLocalization.map_units T s).smul_left_cancel.mp
  have hm : t • δ₁ (algebraMap A T s) + algebraMap A T s • δ₁ t =
      t • δ₂ (algebraMap A T s) + algebraMap A T s • δ₂ t := by
    rw [← h₁, ← h₂, hs, h]
  exact add_left_cancel (by simpa only [h] using hm)

namespace Derivation

section Extend

variable {R A T N : Type*} [CommRing R] [CommRing A] [CommRing T] [Algebra R T] [Algebra A T]
  [AddCommGroup N] [Module T N] [Module R N] [Algebra R A] [IsScalarTower R A T] [Module A N]
  [IsScalarTower A T N] [IsScalarTower R A N]

/-- The extension of an `R`-derivation `D : A → N` to an `R`-derivation of the localization `T`
of `A` at `S`, for `N` a `T`-module. By `IsLocalization.eq_of_leibniz` it is the only derivation
of `T` agreeing with `D` on `A`. -/
noncomputable def extendOfIsLocalization (S : Submonoid A) [IsLocalization S T]
    (D : Derivation R A N) : Derivation R T N :=
  haveI := IsScalarTower.to₁₃₄ R A T N
  letI := isLocalizedModule_id S N T
  let f := IsLocalizedModule.lift S (KaehlerDifferential.map R R A T) D.liftKaehlerDifferential
    (IsLocalizedModule.map_units (LinearMap.id : N →ₗ[A] N))
  (f.extendScalarsOfIsLocalization S T).compDer (KaehlerDifferential.D R T)

/-- The extension of `D` to the localization `T` agrees with `D` on the image of `A`. -/
@[simp]
theorem extendOfIsLocalization_algebraMap (S : Submonoid A) [IsLocalization S T]
    (D : Derivation R A N) (a : A) :
    D.extendOfIsLocalization S (algebraMap A T a) = D a := by
  simp only [extendOfIsLocalization, coe_comp, LinearMap.comp_apply, coeFn_coe]
  rw [← KaehlerDifferential.map_D R R A T]
  -- Keep the differential in the image of `map` so the localization lift simplifies.
  simp [-KaehlerDifferential.map_D]

/-- If a derivation `D` of `A` maps `f` outside the prime ideal `Q`, then the image of `f` in the
local ring `A_Q` does not lie in the square of its maximal ideal. -/
theorem algebraMap_notMem_maximalIdeal_sq (D : Derivation R A A) {Q : Ideal A} [Q.IsPrime]
    {f : A} (hf : D f ∉ Q) :
    algebraMap A (Localization.AtPrime Q) f ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ 2 := by
  -- the extension of `D` to `A_Q` maps the square of the maximal ideal into the maximal ideal
  intro h
  have h' := (((Algebra.linearMap A (Localization.AtPrime Q)).compDer D).extendOfIsLocalization
    Q.primeCompl).apply_mem_smul_top_of_mem_sq h
  rw [extendOfIsLocalization_algebraMap, smul_eq_mul, Ideal.mul_top] at h'
  exact hf ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q _).mp h')

end Extend

/-- On a localization `A` of a `k`-algebra `R` with finitely presented Kähler differentials
`Ω[R⁄k]`, for every `k`-derivation `D` of `A` there exist `s ∈ S` and a global `k`-derivation `δ`
of `R` such that the extension of `δ` to `A` equals `algebraMap R A s • D`. -/
theorem exists_extendOfIsLocalization_eq_smul {k R A : Type*} [CommRing k] [CommRing R]
    [CommRing A] [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    [Module.FinitePresentation R Ω[R⁄k]]
    (S : Submonoid R) [IsLocalization S A] (D : Derivation k A A) :
    ∃ (s : S) (δ : Derivation k R R),
      ((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S = algebraMap R A s • D := by
  let f : Ω[R⁄k] →ₗ[R] A :=
    D.liftKaehlerDifferential.restrictScalars R ∘ₗ KaehlerDifferential.map k k R A
  obtain ⟨g, s, hg⟩ :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule S (Algebra.linearMap R A) f
  let δ : Derivation k R R := g.compDer (KaehlerDifferential.D k R)
  have hf (r : R) : f (KaehlerDifferential.D k R r) = D (algebraMap R A r) := by
    simp only [f, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      KaehlerDifferential.map_D, Derivation.liftKaehlerDifferential_comp_D]
  have hδ (r : R) :
      ((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S (algebraMap R A r) =
        (Algebra.linearMap R A ∘ₗ g) (KaehlerDifferential.D k R r) := by
    simp only [extendOfIsLocalization_algebraMap, δ, coe_comp, LinearMap.comp_apply, coeFn_coe,
      LinearMap.coe_restrictScalars]
  refine ⟨s, δ, Derivation.ext fun a ↦ congrFun (IsLocalization.eq_of_leibniz S
    (δ₁ := ((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S)
    (δ₂ := algebraMap R A s • D)
    (fun x y ↦ (((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S).leibniz x y)
    (fun x y ↦ (algebraMap R A s • D).leibniz x y)
    fun r ↦ ?_) a⟩
  have hg_r := LinearMap.congr_fun hg (KaehlerDifferential.D k R r)
  rw [LinearMap.smul_apply, hf, Submonoid.smul_def, Algebra.smul_def] at hg_r
  exact (hδ r).trans hg_r

end Derivation

namespace Ideal

/-- Extending global derivations shows that the pushforward of a derivative ideal into a
localization is contained in the derivative ideal of the pushforward. -/
theorem map_derivativeIdeal_le (k : Type*) {R A : Type*} [CommRing k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    (S : Submonoid R) [IsLocalization S A] (I : Ideal R) :
    (I.derivativeIdeal k).map (algebraMap R A) ≤ (I.map (algebraMap R A)).derivativeIdeal k := by
  rw [Ideal.map_le_iff_le_comap, Ideal.derivativeIdeal_le_iff]
  refine ⟨Ideal.map_le_iff_le_comap.mp (Ideal.le_derivativeIdeal k _), fun δ f hf ↦ ?_⟩
  rw [Ideal.mem_comap]
  have hmem := Ideal.apply_mem_derivativeIdeal k
    (((Algebra.linearMap R A).compDer δ).extendOfIsLocalization S)
    (Ideal.mem_map_of_mem (algebraMap R A) hf)
  rw [Derivation.extendOfIsLocalization_algebraMap] at hmem
  exact hmem

/-- When `Ω[R⁄k]` is finitely presented over `R`, taking derivative ideals commutes with
localization. -/
theorem map_derivativeIdeal (k : Type*) {R A : Type*} [CommRing k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    [Module.FinitePresentation R Ω[R⁄k]]
    (S : Submonoid R) [IsLocalization S A] (I : Ideal R) :
    (I.derivativeIdeal k).map (algebraMap R A) = (I.map (algebraMap R A)).derivativeIdeal k := by
  refine le_antisymm (map_derivativeIdeal_le k S I) ?_
  conv_lhs => rw [← Ideal.span_eq I, Ideal.map_span, Ideal.derivativeIdeal_span]
  refine Ideal.span_le.mpr (Set.union_subset ?_ ?_)
  · exact Set.image_subset_iff.mpr fun r hr ↦
      Ideal.mem_map_of_mem _ (Ideal.le_derivativeIdeal k I hr)
  · rintro _ ⟨_, ⟨D, rfl⟩, _, ⟨r, hr, rfl⟩, rfl⟩
    obtain ⟨s, δ, hδ⟩ := Derivation.exists_extendOfIsLocalization_eq_smul S D
    have hD : algebraMap R A s * D (algebraMap R A r) = algebraMap R A (δ r) := by
      simpa [Submonoid.smul_def, Algebra.smul_def] using
        (congrArg (fun d : Derivation k A A ↦ d (algebraMap R A r)) hδ).symm
    refine (Ideal.mul_unit_mem_iff_mem _ (IsLocalization.map_units A s)).mp ?_
    rw [mul_comm, hD]
    exact Ideal.mem_map_of_mem _ (Ideal.apply_mem_derivativeIdeal k δ hr)

end Ideal
