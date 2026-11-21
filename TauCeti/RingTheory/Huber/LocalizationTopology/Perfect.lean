/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Perfect
public import TauCeti.RingTheory.Huber.LocalizationTopology.RatLoc
import TauCeti.RingTheory.Huber.LocalizationTopology.Restriction

/-!
# Perfectness of completed rational localizations

A continuous inverse Frobenius on the base extends across the completed rational localization.
The denominator remains invertible after taking its `p`-th root, and the roots of the distinguished
fractions are power-bounded since their `p`-th powers are. This is the universal-property argument
in Scholze–Weinstein, *Berkeley Lectures on p-adic Geometry*, Theorem 2.5.3, and does not need the
base to be complete or Tate.
-/

public section

namespace TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (P : PairOfDefinition A) (T : Finset A) (s : A)
  (hden : P.HasDenominatorPower T s (Localization.Away s))

/-- A completed rational localization of a perfect characteristic-`p` Huber ring with continuous
inverse Frobenius is perfect, including when the localization is the zero ring. -/
theorem perfectRing_ratLoc (p : ℕ) [Fact p.Prime] [CharP A p] [PerfectRing A p]
    (hc : Continuous (frobeniusEquiv A p).symm) : PerfectRing (ratLoc P T s hden) p := by
  let B := ratLoc P T s hden
  let ρ : A →+* B := algebraMap A B
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact ⟨Function.bijective_of_subsingleton _⟩
  have hprime : p.Prime := Fact.out
  have : CharP B p := (CharP.charP_iff_prime_eq_zero hprime).2 (by
    rw [← map_natCast ρ, CharP.cast_eq_zero, map_zero])
  let φ := ρ.comp (↑(frobeniusEquiv A p).symm : A →+* A)
  have hφ (a : A) : φ a ^ p = ρ a := by
    simpa only [φ, RingHom.comp_apply, RingEquiv.coe_toRingHom, map_pow] using
      congrArg ρ (frobeniusEquiv_symm_pow_p A p a)
  have hs : IsUnit (φ s) := (isUnit_pow_iff hprime.ne_zero).mp (hφ s ▸
    isUnit_algebraMap_ratLoc P T s hden)
  have hρ : ρ = P.toCompletionLoc T s (Localization.Away s) hden :=
    algebraMap_ratLoc P T s hden
  have hu : IsUnit (P.toCompletionLoc T s (Localization.Away s) hden s) :=
    hρ ▸ isUnit_algebraMap_ratLoc P T s hden
  obtain ⟨g, ⟨hg, hge⟩, -⟩ := P.existsUnique_continuous_ringHom_completion_locTopology
    T s (Localization.Away s) hden ((continuous_algebraMap_ratLoc P T s hden).comp hc).continuousAt
    hs (fun t ht ↦ by
      apply IsPowerBounded.of_pow hprime.ne_zero
      have hfrac := P.isPowerBounded_toCompletionLoc_mul_unit_inv T s (Localization.Away s) hden
        (mul_one s).symm hu (t := t) (by simpa only [mul_one, Finset.mem_coe] using ht)
      convert hfrac using 1
      apply hu.unit.mul_left_inj.mp
      calc
        (φ t * ↑hs.unit⁻¹) ^ p * (hu.unit : B) = (φ t * ↑hs.unit⁻¹ * φ s) ^ p := by
          rw [hu.unit_spec, ← hρ, mul_pow (φ t * ↑hs.unit⁻¹) (φ s), hφ]
        _ = ρ t := by rw [mul_assoc, hs.val_inv_mul, mul_one, hφ]
        _ = _ := by
          rw [mul_assoc, Units.inv_mul, mul_one]
          exact RingHom.congr_fun hρ t)
  have hgc : g.comp ρ = φ := hρ ▸ hge
  have hf : Continuous (frobenius B p) := continuous_id.pow p
  have hfg : (frobenius B p).comp g = RingHom.id B := by
    refine P.eq_id_of_comp_toCompletionLoc_eq_self T s (Localization.Away s) hden _ (hf.comp hg) ?_
    rw [← hρ, RingHom.comp_assoc, hgc]
    exact RingHom.ext hφ
  have hgf : g.comp (frobenius B p) = RingHom.id B :=
    (RingHom.ext (g.map_frobenius p)).trans hfg
  have hl : Function.LeftInverse g (frobenius B p) := RingHom.congr_fun hgf
  have hr : Function.RightInverse g (frobenius B p) := RingHom.congr_fun hfg
  exact ⟨⟨hl.injective, hr.surjective⟩⟩

end TauCeti.Huber.PairOfDefinition
