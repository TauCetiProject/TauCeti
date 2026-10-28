/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Noetherian
public import TauCeti.RingTheory.KrullDimension.Basic
public import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.KrullDimension.Quotient
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Krull dimension of Monsky–Washnitzer algebras

Over a complete ultrametric normed field, the algebra of overconvergent power series in
`n` variables has Krull dimension `n`. Thus an injective integral extension of this algebra
also has dimension `n`; in particular, the number of variables in a Noether normalisation
is the dimension of the algebra being normalised.

The dimension calculation uses overconvergent Weierstrass division. After a triangular
change of variables, a nonzero principal quotient is finite over the algebra in one fewer
variable. This bounds its dimension from above. Setting one variable to zero gives the
reverse bound, since that variable is a non-zero-divisor.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), Proposition 1.5.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §6.1.2.

The induction follows `TauCeti.MvPowerSeries.ringKrullDim_isRestricted_subring` for Tate
algebras. Here both the change of variables and division take place in the overconvergent
algebra itself.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W " σ:max => washnitzerAlgebra σ K

/-- A nonzero principal quotient has dimension at most that of the overconvergent algebra
in one fewer variable. -/
private theorem ringKrullDim_quotient_span_le_option {σ : Type*} [Finite σ]
    (f : W (Option σ)) (hf : f ≠ 0) :
    ringKrullDim (W (Option σ) ⧸ Ideal.span {f}) ≤ ringKrullDim (W σ) := by
  obtain ⟨α, hα, s, hd, hu⟩ := exists_triangularEquiv_isDistinguished_isUnit f hf
  let e := triangularEquiv (R := K) α hα
  let J : Ideal (W (Option σ)) := Ideal.span {e f}
  let π : W (Option σ) →ₐ[K] W (Option σ) ⧸ J := Ideal.Quotient.mkₐ K J
  have hz : π (e f) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hfin := finite_comp_optionC_of_isDistinguished (A := W (Option σ) ⧸ J) (π := π)
    hd hu (RingHom.Finite.of_surjective _ (Ideal.Quotient.mkₐ_surjective K J)) hz
  let ψ := (π.comp (washnitzerAlgebra.optionC (R := K))).toRingHom
  let : Algebra (W σ) (W (Option σ) ⧸ J) :=
    RingHom.toAlgebra (R := W σ) (S := W (Option σ) ⧸ J) ψ
  have : Module.Finite (W σ) (W (Option σ) ⧸ J) := hfin
  have : Algebra.IsIntegral (W σ) (W (Option σ) ⧸ J) := Algebra.IsIntegral.of_finite _ _
  have hdim : ringKrullDim (W (Option σ) ⧸ J) ≤ ringKrullDim (W σ) :=
    ringKrullDim_le_of_isIntegral (R := W σ) (S := W (Option σ) ⧸ J)
  let E : (W (Option σ) ⧸ Ideal.span {f}) ≃+* (W (Option σ) ⧸ J) :=
    Ideal.quotientEquiv (Ideal.span {f}) J e.toRingEquiv (by simp [J, Ideal.map_span])
  rw [ringKrullDim_eq_of_ringEquiv (S := W (Option σ) ⧸ J) E]
  exact hdim

/-- The Monsky–Washnitzer algebra in finitely many variables has Krull dimension equal to
the number of variables. Completeness of the ultrametric coefficient field suffices; its
norm may be trivial, and its characteristic is arbitrary. -/
@[simp]
theorem ringKrullDim_eq_natCard {σ : Type*} [Finite σ] :
    ringKrullDim (W σ) = Nat.card σ := by
  refine Finite.induction_empty_option (P := fun σ ↦ ringKrullDim (W σ) = Nat.card σ)
    (fun {α β} e h ↦ ?_) ?_ (fun {σ} _ h ↦ ?_) σ
  · rw [← Nat.card_congr e, ← h]
    exact (ringKrullDim_eq_of_ringEquiv (renameAlgEquiv (R := K) e).toRingEquiv).symm
  · rw [ringKrullDim_eq_of_ringEquiv (isEmptyAlgEquiv PEmpty K).toRingEquiv]
    simp
  · rw [Finite.card_option, Nat.cast_add, Nat.cast_one]
    refine le_antisymm ?_ ?_
    · have hle (f : W (Option σ)) (hf : f ≠ 0) :
          ringKrullDim (W (Option σ) ⧸ Ideal.span {f}) ≤ ((Nat.card σ : ℕ∞) : WithBot ℕ∞) :=
        (ringKrullDim_quotient_span_le_option f hf).trans_eq
          (h.trans (WithBot.coe_natCast _).symm)
      exact ringKrullDim_le_add_one_of_forall_ringKrullDim_quotient_le hle
    · rw [← h]
      exact ringKrullDim_succ_le_of_surjective
        (PowerSeries.constantCoeff.comp (optionSeries (σ := σ) (R := K)).toRingHom)
        (fun f ↦ ⟨optionC f, by simp⟩)
        (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := K) none)) (by simp)

/-- Monsky–Washnitzer algebras in finitely many variables have finite Krull dimension. -/
instance finiteRingKrullDim {σ : Type*} [Finite σ] : FiniteRingKrullDim (W σ) :=
  .of_ringKrullDim_eq_natCast ringKrullDim_eq_natCard

/-- An algebra integral over an injectively embedded Monsky–Washnitzer algebra has dimension
equal to its number of variables. Applied to a finite Noether normalisation, this identifies
the normalisation dimension intrinsically. -/
theorem ringKrullDim_eq_natCard_of_isIntegral {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra (W σ) A] [Algebra.IsIntegral (W σ) A]
    [FaithfulSMul (W σ) A] : ringKrullDim A = Nat.card σ := by
  rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := W σ), ringKrullDim_eq_natCard]

end TauCeti.Dagger.washnitzerAlgebra
