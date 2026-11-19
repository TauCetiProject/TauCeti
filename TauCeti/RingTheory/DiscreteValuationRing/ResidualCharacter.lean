/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.GoingUp
import TauCeti.RingTheory.DedekindDomain.IntegralClosure

/-!
# Lifting residual characters of finite algebras over a DVR

Let `O` be a discrete valuation ring with fraction field `K` and residue field `κ`, and let `H`
be a finite commutative `O`-algebra with going down, for instance a finite free one. An
`O`-algebra map `χ : H → κ` is a residual character of `H`, such as the system of eigenvalues
of a commuting family of operators on a residual eigenvector. This file lifts `χ` to
characteristic zero: after a finite extension `L` of `K` and the choice of a DVR `V` of `L`
dominating `O`, there is an `O`-algebra map `ψ : H → V` whose reduction is `χ` followed by an
embedding of residue fields `κ → κ_V`.

The proof follows Deligne–Serre. The kernel of `χ` lies over the maximal ideal of `O`, and
going down gives a prime of `H` below it meeting `O` only in zero. The quotient by that prime
embeds in an algebraic closure of `K`, inside a finite extension `L`. The integral closure of `O`
in `L` is a Dedekind domain, with no separability hypothesis on `L / K`; lying over gives a
nonzero prime of it pulling back to the kernel of `χ`, and the localization there is the DVR
`V`. The extension `L / K` may be inseparable, and `V` need not be finite over `O`.

## Main results

* `AlgHom.under_ker_eq_maximalIdeal`: the kernel of a residual character lies over the maximal
  ideal.
* `AlgHom.exists_isPrime_le_ker_under_eq_bot`: under going down, a prime below the kernel of a
  residual character meets the base only in zero.
* `AlgHom.exists_algHom_algebraicClosure_ker_le`: an integral algebra with going down has an
  `O`-algebra map to an algebraic closure of `K` whose kernel lies in the kernel of a given
  residual character.
* `AlgHom.exists_valuationSubring_lift`: a residual character of a finite algebra with going
  down over a DVR lifts to a character valued in a DVR dominating `O` in a finite extension of
  `K`.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, Lemme 6.11 and its proof.
-/

public section

open IsLocalRing IsDedekindDomain

namespace AlgHom

section LocalRing

variable {O H : Type*} [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H]

/-- The kernel of an `O`-algebra map to the residue field of `O` lies over the maximal ideal. -/
@[simp]
theorem under_ker_eq_maximalIdeal (χ : H →ₐ[O] ResidueField O) :
    (RingHom.ker χ).under O = maximalIdeal O := by
  ext x
  simp [Ideal.under, RingHom.mem_ker, ResidueField.algebraMap_eq, residue_eq_zero_iff]

/-- The kernel of a residual character, as a prime lying over the maximal ideal. -/
instance liesOver_ker (χ : H →ₐ[O] ResidueField O) :
    (RingHom.ker χ).LiesOver (maximalIdeal O) :=
  ⟨χ.under_ker_eq_maximalIdeal.symm⟩

/-- Under going down over a local domain `O`, some prime below the kernel of a residual character
meets `O` only in zero. -/
theorem exists_isPrime_le_ker_under_eq_bot [IsDomain O] [Algebra.HasGoingDown O H]
    (χ : H →ₐ[O] ResidueField O) :
    ∃ P ≤ RingHom.ker χ, P.IsPrime ∧ P.under O = ⊥ := by
  have := RingHom.ker_isPrime χ
  obtain ⟨P, hPQ, hP, hlies⟩ :=
    (RingHom.ker χ).exists_ideal_le_liesOver_of_le (p := ⊥) (q := maximalIdeal O) bot_le
  exact ⟨P, hPQ, hP, hlies.over.symm⟩

/-- An integral algebra `H` with going down over a local domain `O` has an `O`-algebra map to an
algebraic closure of the fraction field `K` of `O` whose kernel lies in the kernel of a given
residual character. -/
theorem exists_algHom_algebraicClosure_ker_le [IsDomain O] [Algebra.HasGoingDown O H]
    [Algebra.IsIntegral O H] (χ : H →ₐ[O] ResidueField O) (K : Type*) [Field K] [Algebra O K]
    [IsFractionRing O K] :
    ∃ φ : H →ₐ[O] AlgebraicClosure K, RingHom.ker φ ≤ RingHom.ker χ := by
  obtain ⟨P, hPQ, hP, hbot⟩ := χ.exists_isPrime_le_ker_under_eq_bot
  have hinj : Function.Injective (algebraMap O (H ⧸ P)) := by
    rw [RingHom.injective_iff_ker_eq_bot, ← hbot]
    ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.under, Ideal.mem_comap]
  have hΩ : Function.Injective (algebraMap O (AlgebraicClosure K)) := by
    rw [IsScalarTower.algebraMap_eq O K (AlgebraicClosure K)]
    exact (algebraMap K _).injective.comp (IsFractionRing.injective O K)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hΩ
  have : Algebra.IsAlgebraic O (H ⧸ P) := Algebra.IsIntegral.isAlgebraic
  let ι : H ⧸ P →ₐ[O] AlgebraicClosure K := IsAlgClosed.lift
  -- `ι` is injective: its kernel meets `O` only in zero, and `H ⧸ P` is integral over `O`.
  have hι : RingHom.ker ι = ⊥ := Ideal.eq_bot_of_under_eq_bot (R := O) <| by
    ext x
    simp [map_eq_zero_iff _ hΩ]
  refine ⟨ι.comp (Ideal.Quotient.mkₐ O P), fun x hx ↦ hPQ ?_⟩
  rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← RingHom.mem_ker, hι,
    Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact hx

end LocalRing

section ValuationSubring

variable {O H : Type*} [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H]
  {L B : Type*} [Field L] [CommRing B] [IsDedekindDomain B] [Algebra O B] [Algebra B L]
  [Algebra O L] [IsScalarTower O B L]

/-- Lifting a residual character through the localization `V` of a Dedekind domain `B` at a
nonzero prime `𝔓`, given an `O`-algebra map `H → B` along which `𝔓` pulls back to the kernel of
the character. -/
private theorem exists_lift_of_isLocalization (χ : H →ₐ[O] ResidueField O) (ψB : H →ₐ[O] B)
    {𝔓 : Ideal B} [𝔓.IsPrime] (hne : 𝔓 ≠ ⊥) (h𝔓 : 𝔓.comap ψB = RingHom.ker χ)
    (V : ValuationSubring L) [Algebra B V] [IsScalarTower B V L] [IsLocalization.AtPrime V 𝔓] :
    ∃ (_ : Algebra O V) (j : ResidueField O →+* ResidueField V) (ψ : H →ₐ[O] V),
      IsDiscreteValuationRing V ∧ (∀ x : O, (algebraMap O V x : L) = algebraMap O L x) ∧
      (residue V).comp (algebraMap O V) = j.comp (residue O) ∧
      (maximalIdeal V).under O = maximalIdeal O ∧ ∀ h, residue V (ψ h) = j (χ h) := by
  let : Algebra O V := ((algebraMap B V).comp (algebraMap O B)).toAlgebra
  let ψ : H →ₐ[O] V :=
    { (algebraMap B V).comp ψB.toRingHom with
      commutes' x := by simp [RingHom.algebraMap_toAlgebra] }
  -- An element of `H` maps into the maximal ideal of `V` exactly when it lies in `ker χ`.
  have hψ (h : H) : ψ h ∈ maximalIdeal V ↔ h ∈ RingHom.ker χ := by
    rw [← h𝔓, Ideal.mem_comap, ← IsLocalization.AtPrime.under_maximalIdeal V 𝔓, Ideal.under,
      Ideal.mem_comap]
    -- `ψ h` is `algebraMap B V (ψB h)` by construction.
    exact Iff.rfl
  have hunder : (maximalIdeal V).under O = maximalIdeal O := by
    ext x
    rw [← χ.under_ker_eq_maximalIdeal]
    simp only [Ideal.under, Ideal.mem_comap, ← ψ.commutes, hψ]
  have : IsLocalHom (algebraMap O V) := ((local_hom_tfae (algebraMap O V)).out 1 5).mpr hunder
  refine ⟨_, ResidueField.map (algebraMap O V), ψ,
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hne V, fun x ↦ ?_,
    (ResidueField.map_comp_residue _).symm, hunder, fun h ↦ ?_⟩
  · rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, IsScalarTower.algebraMap_apply O B L]
    exact (IsScalarTower.algebraMap_apply B V L _).symm
  · obtain ⟨o, ho⟩ := residue_surjective (χ h)
    have : h - algebraMap O H o ∈ RingHom.ker χ := by
      rw [RingHom.mem_ker, map_sub, χ.commutes, ResidueField.algebraMap_eq, ho, sub_self]
    rw [← hψ, map_sub, ψ.commutes, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at this
    rw [this, ← ho, ResidueField.map_residue]

end ValuationSubring

section IntegralClosure

variable {O H : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing H]
  [Algebra O H] {L B : Type*} [Field L] [CommRing B] [Algebra O B] [Algebra B L] [Algebra O L]
  [IsScalarTower O B L] (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]
  [Algebra K L] [IsScalarTower O K L] [Module.Finite K L] [IsIntegralClosure B O L]

include K in
/-- Lifting a residual character through an integral closure `B` of `O` in a finite extension `L`
of `K`, given an `O`-algebra map `H → B` whose kernel lies in the kernel of the character. -/
private theorem exists_lift_of_isIntegralClosure (χ : H →ₐ[O] ResidueField O) (ψB : H →ₐ[O] B)
    (hker : RingHom.ker ψB ≤ RingHom.ker χ) :
    ∃ (V : ValuationSubring L) (_ : Algebra O V) (j : ResidueField O →+* ResidueField V)
      (ψ : H →ₐ[O] V),
      IsDiscreteValuationRing V ∧ (∀ x : O, (algebraMap O V x : L) = algebraMap O L x) ∧
      (residue V).comp (algebraMap O V) = j.comp (residue O) ∧
      (maximalIdeal V).under O = maximalIdeal O ∧ ∀ h, residue V (ψ h) = j (χ h) := by
  have : IsDedekindDomain B := TauCeti.IsIntegralClosure.isDedekindDomain O K L B
  have : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension O K L B
  have hOB : Function.Injective (algebraMap O B) := by
    refine Function.Injective.of_comp (f := algebraMap B L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  -- `B` is integral over `H` through `ψB`, so `ker χ` lies under a prime `𝔓` of `B`.
  let : Algebra H B := ψB.toRingHom.toAlgebra
  have : IsScalarTower O H B := IsScalarTower.of_algebraMap_eq fun x ↦ (ψB.commutes x).symm
  have : Algebra.IsIntegral O B := IsIntegralClosure.isIntegral_algebra O L
  have : Algebra.IsIntegral H B := Algebra.IsIntegral.tower_top O
  have := RingHom.ker_isPrime χ
  obtain ⟨𝔓, -, h𝔓, hunder⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker χ) (⊥ : Ideal B) fun x hx ↦ hker <| by
      rw [Ideal.under, Ideal.mem_comap, Ideal.mem_bot, RingHom.algebraMap_toAlgebra] at hx
      exact RingHom.mem_ker.mpr hx
  -- `𝔓` is nonzero: it contains the image of a uniformizer of `O`.
  have hne : 𝔓 ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    intro h
    have : algebraMap O H ϖ ∈ RingHom.ker χ := by
      rw [RingHom.mem_ker, χ.commutes, ResidueField.algebraMap_eq, residue_eq_zero_iff]
      exact (mem_maximalIdeal _).mpr hϖ.not_isUnit
    rw [← hunder, h, Ideal.under, Ideal.mem_comap, Ideal.mem_bot] at this
    exact hϖ.ne_zero (hOB ((ψB.commutes ϖ).symm.trans (this.trans (map_zero _).symm)))
  obtain ⟨v, rfl⟩ : ∃ v : HeightOneSpectrum B, v.asIdeal = 𝔓 := ⟨⟨𝔓, h𝔓, hne⟩, rfl⟩
  exact ⟨_, exists_lift_of_isLocalization χ ψB v.ne_bot hunder (v.valuationSubringAtPrime L)⟩

end IntegralClosure

section Lift

variable {O H : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing H]
  [Algebra O H] [Module.Finite O H]

/-- **Lifting a residual character to a dominating DVR** (Deligne–Serre). Let `O` be a DVR with
fraction field `K`, and `H` a finite `O`-algebra with going down, for instance a finite free one.
Every `O`-algebra map `χ : H → κ` to the residue field of `O` lifts: there are a finite extension
`L` of `K` inside an algebraic closure, a DVR `V` of `L` dominating `O` (its `O`-algebra
structure being the inclusion `O → K → L`), an embedding `j` of the residue field of `O` into
that of `V`, compatible with the residue maps, and an `O`-algebra map `ψ : H → V` whose
reduction is `j ∘ χ`. The extension `L / K` need not be separable. -/
theorem exists_valuationSubring_lift [Algebra.HasGoingDown O H] (χ : H →ₐ[O] ResidueField O)
    (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (V : ValuationSubring L)
      (_ : Algebra O V) (j : ResidueField O →+* ResidueField V) (ψ : H →ₐ[O] V),
      Module.Finite K L ∧ IsDiscreteValuationRing V ∧
      Function.Injective (algebraMap O V) ∧ Function.Injective j ∧
      (∀ x : O, (algebraMap O V x : L) = algebraMap K L (algebraMap O K x)) ∧
      (residue V).comp (algebraMap O V) = j.comp (residue O) ∧
      (maximalIdeal V).under O = maximalIdeal O ∧
      ∀ h, residue V (ψ h) = j (χ h) := by
  obtain ⟨φ, hφ⟩ := χ.exists_algHom_algebraicClosure_ker_le K
  -- The image of `φ` lies in the field `L` generated over `K` by the images of finitely many
  -- `O`-module generators of `H`; `L` is finite over `K`.
  obtain ⟨L, hL, hmem⟩ : ∃ L : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K L ∧ ∀ h, φ h ∈ L := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := H)
    refine ⟨IntermediateField.adjoin K (φ '' s), ?_, fun h ↦ ?_⟩
    · refine IntermediateField.finiteDimensional_adjoin fun x hx ↦ ?_
      obtain ⟨h, -, rfl⟩ := hx
      exact ((Algebra.IsIntegral.isIntegral (R := O) h).map φ).tower_top
    · have : Submodule.span O (s : Set H) ≤
          ((IntermediateField.adjoin K (φ '' s)).toSubalgebra.restrictScalars O).toSubmodule.comap
            φ.toLinearMap :=
        Submodule.span_le.mpr fun x hx ↦ IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩
      exact this (hs ▸ Submodule.mem_top)
  let φL : H →ₐ[O] L :=
    { toFun h := ⟨φ h, hmem h⟩
      map_one' := by ext; simp
      map_mul' _ _ := by ext; simp
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp
      commutes' x := by
        ext
        rw [IsScalarTower.algebraMap_apply O K L, IntermediateField.coe_algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
        exact φ.commutes x }
  let ψB : H →ₐ[O] integralClosure O L :=
    φL.codRestrict _ fun h ↦ (Algebra.IsIntegral.isIntegral (R := O) h).map φL
  -- `ψB` is `φ` with its codomain restricted to the integral closure of `O` in `L`.
  have hψB (x : H) : ((ψB x : L) : AlgebraicClosure K) = φ x := rfl
  obtain ⟨V, _, j, ψ, hV, hcompat, hres, hmax, hψ⟩ :=
    exists_lift_of_isIntegralClosure (L := L) K χ ψB fun x hx ↦ hφ <| by
      rw [RingHom.mem_ker] at hx ⊢
      rw [← hψB, hx, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
  have hOL : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective O K)
  refine ⟨L, V, _, j, ψ, hL, hV, fun x y hxy ↦ hOL ?_, j.injective, fun x ↦ ?_, hres, hmax, hψ⟩
  · rw [← hcompat, ← hcompat, hxy]
  · rw [hcompat, IsScalarTower.algebraMap_apply O K L]

end Lift

end AlgHom
