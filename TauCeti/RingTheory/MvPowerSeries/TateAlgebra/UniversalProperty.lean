/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.GaussNorm
public import TauCeti.RingTheory.Huber.WeightedEval.UniversalProperty

/-!
# The universal property of Gauss-normed Tate algebras at power-bounded arguments

Let `R` and `S` be ultrametric normed commutative rings with `S` complete, let `φ : R →+* S` be
continuous, and let `b₁, …, bₖ ∈ S` be power-bounded. Then there is exactly one continuous ring
homomorphism `ψ : R⟨X₁, …, Xₖ⟩ → S` on the Gauss-normed ring of unit-radius restricted series
with `ψ (C r) = φ r` and `ψ (Xᵢ) = bᵢ`.

This is Wedhorn's Proposition 5.50,
`TauCeti.Huber.existsUnique_continuous_ringHom_weightedRestrictedSubring`, carried along the
identity comparison `TauCeti.Huber.restrictedMvPowerSeriesGaussEquiv` between the Huber model and
the Gauss-normed model, which is continuous in both directions. Unlike
`MvPowerSeries.restrictedEval₂`, neither `‖φ r‖ ≤ ‖r‖` nor `‖bᵢ‖ ≤ 1` is assumed. Power-boundedness
is `TauCeti.Huber.IsPowerBounded` for the norm topology: the powers of `bᵢ` stay bounded, while
`bᵢ` itself may have norm larger than one.

## Main results

* `MvPowerSeries.existsUnique_continuous_ringHom_isRestricted_subring`: the universal property.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Proposition 5.50.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.4.
-/

public section

namespace MvPowerSeries

open TauCeti.Huber

variable {k : ℕ} {R S : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormedCommRing S]
  [IsUltrametricDist S] [CompleteSpace S]

/-- **The universal property of `R⟨X₁, …, Xₖ⟩` at power-bounded arguments.** For a continuous
ring homomorphism `φ : R →+* S` into a complete ultrametric normed ring and power-bounded
`b₁, …, bₖ ∈ S`, there is exactly one continuous ring homomorphism out of the Gauss-normed
unit-radius restricted series that extends `φ` on constants and sends each `Xᵢ` to `bᵢ`. -/
theorem existsUnique_continuous_ringHom_isRestricted_subring {φ : R →+* S} (hφ : Continuous φ)
    {b : Fin k → S} (hb : ∀ i, IsPowerBounded (b i)) :
    ∃! ψ : IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+* S,
      Continuous ψ ∧ (∀ r, ψ (algebraMap R _ r) = φ r) ∧
        ∀ i, ψ ⟨X i, isRestricted_X _ i⟩ = b i := by
  -- the ultrametric norms make both rings nonarchimedean, as the Huber model requires
  have : NonarchimedeanRing R :=
    { toIsTopologicalRing := inferInstance
      is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
  have : NonarchimedeanRing S :=
    { toIsTopologicalRing := inferInstance
      is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
  let e := restrictedMvPowerSeriesGaussEquiv (n := k) (R := R)
  have hC (r : R) : e (weightedC _ isWeightFamily_one_weight r) = algebraMap R _ r :=
    Subtype.ext (by simp [e])
  have hX (i : Fin k) : e (weightedX _ isWeightFamily_one_weight i) = ⟨X i, isRestricted_X _ i⟩ :=
    Subtype.ext (by simp [e])
  obtain ⟨ψ, ⟨hψ, hψC, hψX⟩, huniq⟩ := existsUnique_continuous_ringHom_weightedRestrictedSubring
    isWeightFamily_one_weight hφ.continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded φ b).mpr hb)
  refine ⟨ψ.comp e.symm.toRingHom, ⟨hψ.comp continuous_restrictedMvPowerSeriesGaussEquiv_symm,
    fun r ↦ ?_, fun i ↦ ?_⟩, fun ψ' ⟨hψ', hψ'C, hψ'X⟩ ↦ ?_⟩
  · simp [← hC, hψC]
  · simp [← hX, hψX]
  · have h := huniq (ψ'.comp e.toRingHom)
      ⟨hψ'.comp continuous_restrictedMvPowerSeriesGaussEquiv, fun r ↦ by simp [hC, hψ'C],
        fun i ↦ by simp [hX, hψ'X]⟩
    ext f
    simpa using congr($h (e.symm f))

end MvPowerSeries
