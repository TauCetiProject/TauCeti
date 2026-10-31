/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Unramified.Field
import TauCeti.RingTheory.Etale.IntegralClosure

/-!
# Base change of unramified extensions of a discrete valuation ring

Let `A → A'` be an extension of discrete valuation rings with fraction fields `K ⊆ K'`, and let
`L / K` be a finite separable extension. The algebra `K' ⊗[K] L` is a finite product of fields, and
its factors are the fields `L'` receiving a surjective `K'`-algebra map from it. If `L` is
unramified with respect to `A`, then every such factor `L'` is unramified with respect to `A'`
(Stacks, Lemma 15.116.9 (0EXY), the unramified half).

The proof follows Stacks. The integral closure `B` of `A` in `L` is finite étale over `A`
(`TauCeti.Algebra.isUnramifiedWRT_iff_etale`), so `B' = A' ⊗[A] B` is finite étale over `A'`, and
`K' ⊗[A'] B'` maps onto `L'` because every element of `L` is an element of `B` divided by an
element of `A`. The integral closure of `A'` in a field quotient of the generic fibre of a finite
étale `A'`-algebra is étale over `A'` (`AlgHom.etale_integralClosure_of_surjective`), so
`L'` is unramified with respect to `A'`.

The extension `A → A'` need not be local here: only the compatibility of the fraction fields is
used.

## Main results

* `AlgHom.isUnramifiedWRT_of_surjective`: over a discrete valuation ring `R`, every field
  quotient of the generic fibre of a finite étale `R`-algebra is unramified with respect to `R`.
* `TauCeti.Algebra.IsUnramifiedWRT.baseChange`: every factor of `K' ⊗[K] L` is unramified with
  respect to `A'` when `L` is unramified with respect to `A`.

## References

* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

open scoped TensorProduct

namespace AlgHom

open TauCeti.Algebra

variable {R K S L : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [CommRing S] [Algebra R S] [Algebra.Etale R S]
  [Module.Finite R S] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- Let `S` be a finite étale algebra over a discrete valuation ring `R` with fraction field `K`.
Every field quotient `L` of the generic fibre `K ⊗[R] S` is unramified with respect to `R`. -/
theorem isUnramifiedWRT_of_surjective (χ : K ⊗[R] S →ₐ[K] L) (hχ : Function.Surjective χ) :
    IsUnramifiedWRT R L := by
  have : IsIntegrallyClosedIn R K :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp inferInstance
  have : Algebra.Etale R (integralClosure R L) := etale_integralClosure_of_surjective χ hχ
  have : FiniteDimensional K L := Module.Finite.of_surjective χ.toLinearMap hχ
  have : Algebra.FormallyUnramified K L := .of_surjective χ hχ
  have : Algebra.IsSeparable K L := (Algebra.FormallyUnramified.iff_isSeparable K L).mp ‹_›
  exact (isUnramifiedWRT_iff_etale R K L).mpr ‹_›

end AlgHom

namespace TauCeti.Algebra

section BaseChange

variable {A K L A' K' L' : Type*}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
  [IsFractionRing A' K'] [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K'] [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']

/-- Unramified extensions of a discrete valuation ring are stable under base change: if `L` is
unramified with respect to `A`, then every factor `L'` of `K' ⊗[K] L`, given by a surjective
`K'`-algebra map `φ : K' ⊗[K] L → L'`, is unramified with respect to `A'`. -/
@[stacks 0EXY "unramified case"]
theorem IsUnramifiedWRT.baseChange (h : IsUnramifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L')
    (hφ : Function.Surjective φ) : IsUnramifiedWRT A' L' := by
  let B := integralClosure A L
  have : Algebra.Etale A B := (isUnramifiedWRT_iff_etale A K L).mp h
  have : Module.Finite A B := IsIntegralClosure.finite A K L _
  let B' := A' ⊗[A] B
  let : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' L' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K' L' := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A A' K',
      ← IsScalarTower.algebraMap_apply A' K' L']
  -- The map `B → L'` through `L` and `K' ⊗[K] L`.
  let g₀ : B →+* L' := φ.toRingHom.comp
    ((Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L).toRingHom.comp
      (integralClosure A L).val.toRingHom)
  -- In `K' ⊗[K] L`, the scalar `1 ⊗ a` from `L` is the scalar `a ⊗ 1` from `K'`.
  have htmul (a : A) : (1 : K') ⊗ₜ[K] algebraMap A L a =
      algebraMap K' (K' ⊗[K] L) (algebraMap A K' a) := by
    simp [IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A K K',
      Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have hg₀ (a : A) : g₀ (algebraMap A B a) = algebraMap A L' a := by
    simp only [g₀, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Subalgebra.coe_val, Subalgebra.coe_algebraMap, Algebra.TensorProduct.includeRight_apply]
    rw [htmul, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  let g : B →ₐ[A] L' := { g₀ with commutes' := hg₀ }
  have hg (b : B) : g b = φ ((1 : K') ⊗ₜ[K] (b : L)) := by
    simp [g, g₀]
  let ψ : B' →ₐ[A'] L' := Algebra.TensorProduct.lift (Algebra.ofId A' L') g fun _ _ ↦ .all _ _
  have hψ (b : B) : ψ (1 ⊗ₜ b) = φ ((1 : K') ⊗ₜ[K] (b : L)) := by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, hg]
  let χ : K' ⊗[A'] B' →ₐ[K'] L' :=
    Algebra.TensorProduct.lift (Algebra.ofId K' L') ψ fun _ _ ↦ .all _ _
  -- `χ` is surjective: every element of `L` is an element of `B` divided by an element of `A`.
  have hχ : Function.Surjective χ := by
    intro y
    obtain ⟨t, rfl⟩ := hφ y
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨x₁, hx₁⟩ := h₁
      obtain ⟨x₂, hx₂⟩ := h₂
      exact ⟨x₁ + x₂, by rw [map_add, map_add, hx₁, hx₂]⟩
    | tmul k l =>
      have hl : IsAlgebraic A l :=
        (IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic l)
      obtain ⟨a, ha, hint⟩ := hl.exists_integral_multiple
      have ha' : algebraMap A K' a ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply A K K']
        exact (_root_.map_ne_zero _).mpr
          ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha)
      let b : B := ⟨a • l, hint⟩
      have hbl : (b : L) = algebraMap A K a • l := (algebraMap_smul K a l).symm
      have hb : (1 : K') ⊗ₜ[K] (b : L) = algebraMap A K' a • ((1 : K') ⊗ₜ[K] l) := by
        rw [hbl, TensorProduct.tmul_smul, TensorProduct.smul_tmul', IsScalarTower.algebraMap_smul]
        simp [Algebra.smul_def, IsScalarTower.algebraMap_apply A K K']
      have hφb : φ (1 ⊗ₜ b) = algebraMap K' L' (algebraMap A K' a) * φ (1 ⊗ₜ l) := by
        rw [hb, map_smul, Algebra.smul_def]
      have hφk : φ (k ⊗ₜ l) = algebraMap K' L' k * φ (1 ⊗ₜ l) := by
        rw [← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      refine ⟨(k * (algebraMap A K' a)⁻¹) ⊗ₜ (1 ⊗ₜ b), ?_⟩
      simp only [χ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, hψ, hφb, hφk, map_mul,
        map_inv₀]
      have := (map_ne_zero (algebraMap K' L')).mpr ha'
      field_simp
  exact χ.isUnramifiedWRT_of_surjective hχ

end BaseChange

end TauCeti.Algebra
