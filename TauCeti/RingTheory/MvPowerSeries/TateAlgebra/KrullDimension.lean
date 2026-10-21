/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
import Mathlib.RingTheory.KrullDimension.Field
import TauCeti.RingTheory.KrullDimension.Basic
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.PowerSeries.TateAlgebra
import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient

/-!
# Krull dimension of Tate algebras

Over a complete nonarchimedean field `K`, the Tate algebra `K⟨X₁, …, Xₙ⟩` has Krull dimension
`n`. Consequently every ring that is integral over an injectively embedded Tate algebra
`K⟨X₁, …, X_d⟩` has Krull dimension `d`. Applied to the finite injective maps given by
Noether normalisation, this identifies the number of variables of a normalisation of an
affinoid algebra with its Krull dimension.

The proof is by induction on the number of variables, writing `K⟨X, Y⟩` as the univariate Tate
algebra `K⟨X⟩⟨Y⟩`.

* *Lower bound.* Setting `Y = 0` is a surjection `K⟨X⟩⟨Y⟩ → K⟨X⟩` killing the non-zero-divisor
  `Y`, so `dim K⟨X⟩ + 1 ≤ dim K⟨X, Y⟩`.
* *Upper bound.* For a nonzero `f`, an automorphism makes `f` distinguished in `Y`, and Weierstrass
  division makes `K⟨X, Y⟩ ⧸ (f)` finite over `K⟨X⟩`, so `dim K⟨X, Y⟩ ⧸ (f) ≤ dim K⟨X⟩`. A chain
  of primes of length `k + 1` gives a chain of length `k` above a nonzero element, so
  `dim K⟨X, Y⟩ ≤ dim K⟨X⟩ + 1`.

## Main results

* `TauCeti.MvPowerSeries.ringKrullDim_isRestricted_subring`: the Tate algebra in the variables
  `σ`, for finite `σ`, has Krull dimension `Nat.card σ`.
* `TauCeti.MvPowerSeries.ringKrullDim_eq_natCard_of_isIntegral`: a ring that is integral over an
  injectively embedded Tate algebra in the variables `σ` has Krull dimension `Nat.card σ`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§5.2.2 and
  6.1.2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- Without variables, the Tate algebra is the coefficient field, of Krull dimension zero. -/
private theorem ringKrullDim_isRestricted_subring_pEmpty : ringKrullDim (Tate PEmpty) = 0 := by
  rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.ofBijective _
    ⟨(algebraMap K (Tate PEmpty)).injective, algebraMap_isRestrictedSubring_surjective⟩)]
  exact ringKrullDim_eq_zero_of_field K

variable [CompleteSpace K]

/-- Quotients of `K⟨X, Y⟩` by nonzero principal ideals are integral over `K⟨X⟩`, so their Krull
dimension is at most that of `K⟨X⟩`. -/
private theorem ringKrullDim_quotient_span_le_option {σ : Type*} [Finite σ] (f : Tate (Option σ))
    (hf : f ≠ 0) : ringKrullDim (Tate (Option σ) ⧸ Ideal.span {f}) ≤ ringKrullDim (Tate σ) := by
  let R := Tate σ
  let S := PowerSeries.IsRestricted.subring (R := R) 1
  let Φ : Tate (Option σ) ≃+* S := Huber.restrictedOptionEquiv
  obtain ⟨e, s, hd, hu⟩ := exists_algEquiv_isDistinguished_isUnit f hf
  have := hd.finite_quotient zero_lt_one hu
  have : Algebra.IsIntegral R (S ⧸ Ideal.span {Φ (e f)}) := Algebra.IsIntegral.of_finite R _
  let E : Tate (Option σ) ≃+* S := (e : Tate (Option σ) ≃+* Tate (Option σ)).trans Φ
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv (Ideal.span {f})
    (Ideal.span {Φ (e f)}) E (by simp [Ideal.map_span, E]))]
  exact ringKrullDim_le_of_isIntegral

/-- **Krull dimension of Tate algebras.** Over a complete nonarchimedean field `K`, the Tate
algebra `K⟨X₁, …, Xₙ⟩` in finitely many variables has Krull dimension `n`. -/
theorem ringKrullDim_isRestricted_subring {σ : Type*} [Finite σ] :
    ringKrullDim (Tate σ) = Nat.card σ := by
  refine Finite.induction_empty_option (P := fun σ ↦ ringKrullDim (Tate σ) = Nat.card σ)
    (fun {α β} e h ↦ ?_) ?_ (fun {σ} _ h ↦ ?_) σ
  · -- Renaming the variables along `e : α ≃ β` is a ring isomorphism of Tate algebras.
    rw [← Nat.card_congr e, ← h]
    exact (ringKrullDim_eq_of_ringEquiv
      (IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1).toRingEquiv).symm
  · simpa using ringKrullDim_isRestricted_subring_pEmpty
  · rw [Finite.card_option, Nat.cast_add, Nat.cast_one]
    refine le_antisymm ?_ ?_
    · have hle (f : Tate (Option σ)) (hf : f ≠ 0) :
          ringKrullDim (Tate (Option σ) ⧸ Ideal.span {f}) ≤ ((Nat.card σ : ℕ∞) : WithBot ℕ∞) :=
        (ringKrullDim_quotient_span_le_option f hf).trans_eq (h.trans (WithBot.coe_natCast _).symm)
      exact ringKrullDim_le_add_one_of_forall_ringKrullDim_quotient_le hle
    · rw [← h, ringKrullDim_eq_of_ringEquiv (Huber.restrictedOptionEquiv (σ := σ) (R := K))]
      exact PowerSeries.ringKrullDim_succ_le_ringKrullDim_isRestricted_subring 1

/-- The Tate algebra in finitely many variables has finite Krull dimension. -/
instance finiteRingKrullDim {σ : Type*} [Finite σ] : FiniteRingKrullDim (Tate σ) :=
  .of_ringKrullDim_eq_natCast ringKrullDim_isRestricted_subring

/-- **The degree of a normalisation is the Krull dimension.** A ring that is integral over an
injectively embedded Tate algebra `K⟨X₁, …, X_d⟩` has Krull dimension `d`. This applies to the
finite injective maps from Tate algebras supplied by Noether normalisation,
`TauCeti.IsAffinoidAlgebra.exists_finite_injective`. -/
theorem ringKrullDim_eq_natCard_of_isIntegral {σ : Type*} [Finite σ] {A : Type*} [CommRing A]
    [Algebra (Tate σ) A] [Algebra.IsIntegral (Tate σ) A] [FaithfulSMul (Tate σ) A] :
    ringKrullDim A = Nat.card σ := by
  rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := Tate σ),
    ringKrullDim_isRestricted_subring]

end TauCeti.MvPowerSeries
