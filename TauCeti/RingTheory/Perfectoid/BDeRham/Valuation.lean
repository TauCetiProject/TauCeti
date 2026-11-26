/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.BDeRham
public import TauCeti.RingTheory.AdicCompletion.DiscreteValuationRing
public import TauCeti.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.RingTheory.IntegralClosure.AbsolutelyIntegrallyClosed
public import Mathlib.RingTheory.Valuation.LocalSubring
public import TauCeti.RingTheory.Valuation.AdicSeparated
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.Field.Equiv

/-!
# The native de Rham valuation ring

For a `p`-adically complete valuation ring of an algebraically closed characteristic-zero field,
Mathlib's `BDeRhamPlus` is a discrete valuation domain and `BDeRham` is a field. In particular,
this applies to the valuation ring of any complete algebraically closed field over `ℚ_p`.
The residue
map is obtained by extending the localized Fontaine map through its kernel-adic completion.
The argument uses a regular generator of the integral Fontaine kernel; no choice of
cyclotomic roots is needed.

These are algebraic statements. The canonical period topologies, Galois actions and the
logarithmic uniformizer are separate constructions.

## Provenance

The valuation argument adapts `New.Period.BdRPlus.isUnit_iff`,
`New.Period.BdRPlus.exists_associated_xi_pow`, `New.Period.BdRPlus.prime_xi` and the domain/DVR
instances from `src/Lib/PadicHodge/PeriodRings/CrystallineRings.lean` in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
Here the principal-completion argument is generalized and applied to Mathlib's native
completion of `A_inf[1/p]`, for any `p`-adically complete valuation ring with algebraically
closed characteristic-zero fraction field.
The field statement uses Mathlib's native localization at all kernel generators.

## References

* J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994),
  §§1.5.1–1.5.2 and §1.5.5, pp. 71–73.
-/

public section

open Ideal WittVector
open scoped nonZeroDivisors

namespace TauCeti

section General

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime]
  [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

/-- The native plus carrier has the algebra structure of its defining completion. -/
noncomputable instance bDeRhamPlusAlgebra :
    Algebra (Localization.Away (p : WittVector p (PreTilt R p))) (BDeRhamPlus R p) :=
  inferInstanceAs (Algebra _ (AdicCompletion _ _))

/-- The native de Rham localization is a commutative ring. -/
noncomputable instance bDeRhamCommRing : CommRing (BDeRham R p) := by
  unfold BDeRham
  infer_instance

/-- The native de Rham localization is an algebra over the plus carrier. -/
noncomputable instance bDeRhamAlgebra : Algebra (BDeRhamPlus R p) (BDeRham R p) := by
  unfold BDeRham
  infer_instance

local instance : IsLocalization.Away ((fontaineTheta R p) p) (Localization.Away (p : R)) := by
  simpa only [map_natCast] using
    (inferInstance : IsLocalization.Away (p : R) (Localization.Away (p : R)))

private theorem fontaineThetaInvertP_eq_map :
    fontaineThetaInvertP R p =
      IsLocalization.Away.map (Localization.Away (p : WittVector p (PreTilt R p)))
        (Localization.Away (p : R)) (fontaineTheta R p) p := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext x
  simp [fontaineThetaInvertP, IsLocalization.Away.map, Localization.awayLift]

/-- Inverting `p` localizes Fontaine's kernel. -/
theorem ker_fontaineThetaInvertP : RingHom.ker (fontaineThetaInvertP R p) =
    (RingHom.ker (fontaineTheta R p)).map
      (algebraMap _ (Localization.Away (p : WittVector p (PreTilt R p)))) := by
  rw [fontaineThetaInvertP_eq_map]
  exact IsLocalization.ker_map _ _ (by simp)

/-- Surjectivity of Fontaine's map survives inversion of `p`. -/
theorem surjective_fontaineThetaInvertP (h : Function.Surjective (fontaineTheta R p)) :
    Function.Surjective (fontaineThetaInvertP R p) := by
  rw [fontaineThetaInvertP_eq_map]
  apply (IsLocalization.Away.map_surjective_iff _ _ _ _).mpr
  intro a
  obtain ⟨b, hb⟩ := h a
  exact ⟨b, 0, by simpa using hb⟩

/-- Fontaine's map on the native de Rham plus carrier, with values in `R[1/p]`. -/
noncomputable def fontaineThetaBDeRhamPlus :
    BDeRhamPlus R p →+* Localization.Away (p : R) :=
  (fontaineThetaInvertP R p).kerLift.comp
    (AdicCompletion.evalOneₐ (RingHom.ker (fontaineThetaInvertP R p))).toRingHom

/-- The extended Fontaine map agrees with the original map on `A_inf[1/p]`. -/
@[simp]
theorem fontaineThetaBDeRhamPlus_of
    (x : Localization.Away (p : WittVector p (PreTilt R p))) :
    fontaineThetaBDeRhamPlus R p
      (AdicCompletion.of (RingHom.ker (fontaineThetaInvertP R p)) _ x) =
        fontaineThetaInvertP R p x := (rfl)

/-- The extended Fontaine map is surjective whenever the integral Fontaine map is. -/
theorem surjective_fontaineThetaBDeRhamPlus
    (h : Function.Surjective (fontaineTheta R p)) :
    Function.Surjective (fontaineThetaBDeRhamPlus R p) := by
  intro x
  obtain ⟨y, rfl⟩ := surjective_fontaineThetaInvertP R p h x
  exact ⟨AdicCompletion.of _ _ y, rfl⟩

/-- The extended Fontaine kernel is the kernel of the first completion projection. -/
theorem ker_fontaineThetaBDeRhamPlus :
    RingHom.ker (fontaineThetaBDeRhamPlus R p) =
      RingHom.ker (AdicCompletion.evalOneₐ
        (RingHom.ker (fontaineThetaInvertP R p))).toRingHom := by
  exact RingHom.ker_comp_of_injective _ (RingHom.kerLift_injective _)

end General

section AlgebraicallyClosed

variable (p : ℕ) [Fact p.Prime]
    (C : Type*) [Field C] [CharZero C] (R : ValuationSubring C)
    [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

local instance : IsLocalization.Away (p : R) C := by
  apply PreValuationRing.isLocalization_away_of_isFractionRing
  intro h
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    (congrArg Subtype.val h : (p : C) = 0)

/-- The canonical residue map from the native plus carrier to the ambient valued field. -/
noncomputable def bDeRhamPlusResidue : BDeRhamPlus R p →+* C :=
  (IsLocalization.algEquiv (Submonoid.powers (p : R))
    (Localization.Away (p : R)) C).toRingHom.comp (fontaineThetaBDeRhamPlus R p)

/-- On Witt vectors, the native residue map is Fontaine's integral map followed by inclusion
into the ambient field. -/
@[simp]
theorem bDeRhamPlusResidue_of (x : WittVector p (PreTilt R p)) :
    bDeRhamPlusResidue p C R
      (AdicCompletion.of (RingHom.ker (fontaineThetaInvertP R p)) _
        (algebraMap _ (Localization.Away (p : WittVector p (PreTilt R p))) x)) =
          algebraMap R C (fontaineTheta R p x) := by
  exact (congrArg (IsLocalization.algEquiv (Submonoid.powers (p : R))
    (Localization.Away (p : R)) C) (fontaineThetaBDeRhamPlus_of R p _)).trans
      (by simp [fontaineThetaInvertP, Localization.awayLift])

/-- Passing from `R[1/p]` to the ambient field does not change the native Fontaine kernel. -/
theorem ker_bDeRhamPlusResidue :
    RingHom.ker (bDeRhamPlusResidue p C R) = RingHom.ker (fontaineThetaBDeRhamPlus R p) := by
  unfold bDeRhamPlusResidue
  exact RingHom.ker_comp_of_injective _ (AlgEquiv.injective _)

variable [IsAlgClosed C]

private theorem deRham_data :
    Function.Surjective (fontaineThetaInvertP R p) ∧
    ∃ ξ : Localization.Away (p : WittVector p (PreTilt R p)), IsRegular ξ ∧
      RingHom.ker (fontaineThetaInvertP R p) = span {ξ} ∧
      (RingHom.ker (fontaineThetaInvertP R p)).IsMaximal := by
  have : IsAbsolutelyIntegrallyClosed R :=
    IsAbsolutelyIntegrallyClosed.of_isIntegrallyClosed_of_isAlgClosed C
  obtain ⟨π, hπ⟩ := IsAbsolutelyIntegrallyClosed.exists_pow_nat_eq (p : R)
    (Fact.out : p.Prime).pos
  have hc : IsAdicComplete (span {π}) R := by
    apply IsAdicComplete.of_pow_le_of_pow_le (I := span {(p : R)}) (k := p) (l := 1)
    · rw [span_singleton_pow, hπ]
    · rw [pow_one, span_singleton_le_span_singleton, ← hπ]
      exact dvd_pow_self _ (Fact.out : p.Prime).ne_zero
  have hp0 : (p : R) ≠ 0 := by
    intro h
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      (congrArg Subtype.val h : (p : C) = 0)
  have hreg : π ∈ R⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr fun h ↦ hp0 (by
    rw [← hπ, h, zero_pow (Fact.out : p.Prime).ne_zero])
  have hdvd : π ^ p ∣ (p : R) := hπ ▸ dvd_rfl
  have hbij : Function.Bijective (TauCeti.frobeniusModPow p hdvd) := by
    refine ⟨(TauCeti.frobeniusModPow_injective_iff hdvd).mpr fun y hy ↦
      (IsIntegrallyClosed.pow_dvd_pow_iff (Fact.out : p.Prime).ne_zero).mp hy,
      (TauCeti.frobeniusModPow_surjective_iff hdvd).mpr fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := IsAbsolutelyIntegrallyClosed.exists_pow_nat_eq x (Fact.out : p.Prime).pos
    exact ⟨y, by rw [hy, sub_self]; exact dvd_zero _⟩
  obtain ⟨ξ, -, hξ, hker⟩ :=
    WittVector.exists_isDistinguished_mem_nonZeroDivisors_ker_fontaineTheta hreg hbij
  have hs := surjective_fontaineThetaInvertP R p
    (WittVector.surjective_fontaineTheta_of_frobeniusModPow_surjective hbij.2)
  have hker' := ker_fontaineThetaInvertP R p
  rw [hker, map_span, Set.image_singleton] at hker'
  have hfield := (IsLocalization.algEquiv (Submonoid.powers (p : R))
    (Localization.Away (p : R)) C).toRingEquiv.toMulEquiv.isField (Field.toIsField C)
  let := hfield.toField
  exact ⟨hs, _, isRegular_iff_mem_nonZeroDivisors.mpr
    (IsLocalization.nonZeroDivisors_le_comap
      (Submonoid.powers (p : WittVector p (PreTilt R p)))
      (Localization.Away (p : WittVector p (PreTilt R p))) hξ), hker',
    RingHom.ker_isMaximal_of_surjective _ hs⟩

/-- The native de Rham plus carrier of an algebraically closed characteristic-zero field
with `p`-adically complete valuation ring is a discrete valuation domain. -/
theorem bDeRhamPlus_isDiscreteValuationRing :
    ∃ h : IsDomain (BDeRhamPlus R p),
      @IsDiscreteValuationRing (BDeRhamPlus R p) _ h := by
  obtain ⟨-, ξ, hreg, hker, hm⟩ := deRham_data p C R
  -- Express both the carrier and its derived ring structure as the defining completion.
  change ∃ h : IsDomain (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p))
      (Localization.Away (p : WittVector p (PreTilt R p)))),
    @IsDiscreteValuationRing (AdicCompletion (RingHom.ker (fontaineThetaInvertP R p))
      (Localization.Away (p : WittVector p (PreTilt R p)))) _ h
  rw [hker]
  have : (span {ξ}).IsMaximal := hker ▸ hm
  exact ⟨AdicCompletion.isDomain_of_isMaximal_span hreg,
    AdicCompletion.isDiscreteValuationRing_of_isMaximal_span hreg⟩

/-- The native de Rham localization of an algebraically closed characteristic-zero field
with `p`-adically complete valuation ring is a field. Inverting the kernel generators inverts a
uniformizer of the plus carrier. -/
theorem bDeRham_isField : IsField (BDeRham R p) := by
  obtain ⟨hD, hV⟩ := bDeRhamPlus_isDiscreteValuationRing p C R
  have := hD
  have := hV
  obtain ⟨-, ξ, -, hker, hm⟩ := deRham_data p C R
  let I := RingHom.ker (fontaineThetaInvertP R p)
  let A := BDeRhamPlus R p
  let t : A := AdicCompletion.of I _ ξ
  let M : Submonoid A := Submonoid.closure (AdicCompletion.of I _ '' {a | I = span {a}})
  have hker : I = span {ξ} := hker
  have hmap : I.map (algebraMap _ A) = span {t} := by
    have h := congrArg (Ideal.map (algebraMap _ A)) hker
    rw [map_span, Set.image_singleton] at h
    exact h
  have : I.IsMaximal := hm
  have hfg : I.FG := by
    rw [hker]
    exact Submodule.fg_span_singleton ξ
  have hmax : (span {t}).IsMaximal := by
    rw [← hmap]
    exact AdicCompletion.isMaximal_map_of_le I I le_rfl hfg
  have ht0 : t ≠ 0 := fun ht ↦ IsDiscreteValuationRing.not_a_field A
    ((IsLocalRing.eq_maximalIdeal hmax).symm.trans (span_singleton_eq_bot.mpr ht))
  have ht : Irreducible t := ((span_singleton_prime ht0).mp hmax.isPrime).irreducible
  have htM : t ∈ M := Submonoid.subset_closure ⟨ξ, hker, rfl⟩
  have hM : M ≤ nonZeroDivisors A := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    have hassoc : Associated t (AdicCompletion.of I _ a : A) := by
      have h := congrArg (Ideal.map (algebraMap _ A)) ha
      rw [map_span, Set.image_singleton] at h
      exact span_singleton_eq_span_singleton.mp (hmap.symm.trans h)
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (hassoc.ne_zero_iff.mp ht0)
  have : IsLocalization M (BDeRham R p) := inferInstanceAs (IsLocalization M (Localization M))
  have : IsFractionRing A (BDeRham R p) :=
    (IsLocalization.iff_of_le_of_exists_dvd M (nonZeroDivisors A) hM fun a ha ↦ by
      obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
        (nonZeroDivisors.ne_zero ha) ht
      exact ⟨t ^ n, pow_mem htM n, hn.dvd⟩).mp inferInstance
  exact (IsFractionRing.toField A).toIsField _

/-- The native residue map onto the algebraically closed ambient field is surjective. -/
theorem surjective_bDeRhamPlusResidue : Function.Surjective (bDeRhamPlusResidue p C R) := by
  obtain ⟨hs, -⟩ := deRham_data p C R
  have hs' : Function.Surjective (fontaineThetaBDeRhamPlus R p) := by
    intro x
    obtain ⟨y, rfl⟩ := hs x
    exact ⟨AdicCompletion.of _ _ y, rfl⟩
  exact (IsLocalization.algEquiv (Submonoid.powers (p : R))
    (Localization.Away (p : R)) C).surjective.comp hs'

end AlgebraicallyClosed

end TauCeti
