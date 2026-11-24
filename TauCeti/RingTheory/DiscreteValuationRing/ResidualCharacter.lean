/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.RingTheory.LocalRing.ResidueField.Character
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
import Mathlib.RingTheory.DedekindDomain.Dvr
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.Ideal.GoingUp

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

The steps over a general local ring, up to the embedding in an algebraic closure, are in
`TauCeti/RingTheory/LocalRing/ResidueField/Character.lean`.

## Main results

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
      simp [ResidueField.algebraMap_eq, ho]
    rw [← hψ, ← residue_eq_zero_iff] at this
    simpa [sub_eq_zero, ← ho] using this

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
  have hOB := algebraMap_injective_of_field_isFractionRing O B K L
  -- `B` is integral over `H` through `ψB`, so `ker χ` is the pullback of a prime `𝔓` of `B`.
  have : Algebra.IsIntegral O B := IsIntegralClosure.isIntegral_algebra O L
  have hψB : (ψB : H →+* B).IsIntegral := RingHom.IsIntegral.tower_top (algebraMap O H) _ <| by
    rw [ψB.comp_algebraMap]
    exact Algebra.IsIntegral.isIntegral
  have := RingHom.ker_isPrime χ
  obtain ⟨𝔓, h𝔓, hunder⟩ := (RingHom.ker χ).exists_comap_eq_of_isIntegral (ψB : H →+* B) hψB hker
  -- `𝔓` is nonzero: it contains the image of a uniformizer of `O`.
  have hne : 𝔓 ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    intro h
    have : algebraMap O H ϖ ∈ RingHom.ker χ := by
      simpa [ResidueField.algebraMap_eq] using hϖ.not_isUnit
    rw [← hunder, h] at this
    simp [map_eq_zero_iff _ hOB, hϖ.ne_zero] at this
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
  refine ⟨L, V, _, j, ψ, hL, hV, fun x y hxy ↦
    algebraMap_injective_of_field_isFractionRing O L K L ?_,
    j.injective, fun x ↦ ?_, hres, hmax, hψ⟩
  · rw [← hcompat, ← hcompat, hxy]
  · rw [hcompat, IsScalarTower.algebraMap_apply O K L]

end Lift

end AlgHom
