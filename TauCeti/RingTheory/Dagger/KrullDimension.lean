/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra
public import TauCeti.RingTheory.Dagger.NoetherNormalization
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import TauCeti.RingTheory.KrullDimension.Basic
public import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.KrullDimension.Quotient

/-!
# Krull dimension of overconvergent algebras

The Monsky–Washnitzer algebra `K⟨X₁, …, Xₙ⟩†` over a complete ultrametric normed field has
Krull dimension `n`. Consequently the number of variables in a finite injective Noether
normalisation of a nonzero dagger algebra is its Krull dimension. In particular nonzero
dagger algebras have finite Krull dimension. Presentation dimension is only an upper bound:
it counts variables in a surjective presentation, rather than in a normalisation.

For the dimension calculation, setting one variable to zero gives the lower bound. A change
of variables and Weierstrass division make every quotient by a nonzero principal ideal finite
over an overconvergent algebra in one fewer variable, giving the upper bound.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.4(2) and Proposition 1.5.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §6.1.2.

The dimension induction follows `TauCeti.MvPowerSeries.ringKrullDim_isRestricted_subring`
in `TauCeti.RingTheory.MvPowerSeries.TateAlgebra.KrullDimension`, using overconvergent
Weierstrass division in place of division in a complete Tate algebra.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "W " σ:max => washnitzerAlgebra σ K

namespace washnitzerAlgebra

/-- A nonzero principal quotient in one more variable has dimension at most that of the
overconvergent algebra in the remaining variables. -/
private theorem ringKrullDim_quotient_span_le_option {σ : Type*} [Finite σ]
    (f : W (Option σ)) (hf : f ≠ 0) :
    ringKrullDim (W (Option σ) ⧸ Ideal.span {f}) ≤ ringKrullDim (W σ) := by
  -- Pin the inherited ring structures so quotient and finite-map APIs share their projections.
  let : CommRing (W (Option σ)) := inferInstance
  let : CommRing (W σ) := inferInstance
  obtain ⟨α, hα, s, hd, hu⟩ := exists_triangularEquiv_isDistinguished_isUnit f hf
  let e := triangularEquiv (R := K) α hα
  let J : Ideal (W (Option σ)) := Ideal.span {e f}
  let π : W (Option σ) →ₐ[K] W (Option σ) ⧸ J := Ideal.Quotient.mkₐ K J
  have hz : π (e f) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hfin := finite_comp_optionC_of_isDistinguished
    (A := W (Option σ) ⧸ J) (π := π) hd hu
    (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hz
  let : Algebra (W σ) (W (Option σ) ⧸ J) :=
    (π.comp optionC).toRingHom.toAlgebra
  have : Module.Finite (W σ) (W (Option σ) ⧸ J) := RingHom.finite_algebraMap.mp hfin
  have : Algebra.IsIntegral (W σ) (W (Option σ) ⧸ J) := Algebra.IsIntegral.of_finite _ _
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ J e.toRingEquiv
    (by simp [J, Ideal.map_span]))]
  exact ringKrullDim_le_of_isIntegral (R := W σ)

/-- **Krull dimension of the Monsky–Washnitzer algebra.** The overconvergent algebra over a
complete ultrametric normed field has dimension equal to its number of variables. -/
@[simp]
theorem ringKrullDim_eq_natCard {σ : Type*} [Finite σ] :
    ringKrullDim (W σ) = Nat.card σ := by
  refine Finite.induction_empty_option (P := fun σ ↦ ringKrullDim (W σ) = Nat.card σ)
    (fun {α β} e h ↦ ?_) ?_ (fun {σ} _ h ↦ ?_) σ
  · rw [← Nat.card_congr e, ← h]
    exact (ringKrullDim_eq_of_ringEquiv (renameAlgEquiv (R := K) e).toRingEquiv).symm
  · rw [ringKrullDim_eq_of_ringEquiv (isEmptyAlgEquiv PEmpty K).toRingEquiv]
    simp [ringKrullDim_eq_zero_of_field]
  · rw [Finite.card_option, Nat.cast_add, Nat.cast_one]
    refine le_antisymm ?_ ?_
    · apply ringKrullDim_le_add_one_of_forall_ringKrullDim_quotient_le
      intro f hf
      exact (ringKrullDim_quotient_span_le_option f hf).trans_eq
        (h.trans (WithBot.coe_natCast _).symm)
    · rw [← h]
      let ev : W (Option σ) →+* W σ := PowerSeries.constantCoeff.comp optionSeries.toRingHom
      have hsur : Function.Surjective ev := fun f ↦ ⟨optionC f, by simp [ev]⟩
      exact ringKrullDim_succ_le_of_surjective ev hsur
        (mem_nonZeroDivisors_of_ne_zero (X_ne_zero (R := K) none)) (by simp [ev])

/-- The overconvergent algebra in finitely many variables has finite Krull dimension. -/
instance finiteRingKrullDim {σ : Type*} [Finite σ] : FiniteRingKrullDim (W σ) :=
  .of_ringKrullDim_eq_natCast ringKrullDim_eq_natCard

/-- An algebra integral over an injectively embedded Monsky–Washnitzer algebra has dimension
equal to its number of variables. Applied to a finite Noether normalisation, this identifies
the normalisation dimension intrinsically. -/
theorem ringKrullDim_eq_natCard_of_isIntegral {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra (W σ) A] [Algebra.IsIntegral (W σ) A]
    [FaithfulSMul (W σ) A] : ringKrullDim A = Nat.card σ := by
  rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := W σ), ringKrullDim_eq_natCard]

end washnitzerAlgebra

namespace IsDaggerAlgebra

variable {A : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]

/-- **Noether normalisation in the dimension of the algebra.** A nonzero dagger algebra is
finite over an injectively embedded overconvergent algebra in `dim A` variables. -/
theorem exists_ringKrullDim_eq_finite_injective [Nontrivial A] :
    ∃ n : ℕ, ringKrullDim A = n ∧ ∃ g : W (Fin n) →ₐ[K] A,
      Function.Injective g ∧ g.Finite := by
  obtain ⟨n, π, hπ⟩ := exists_surjective (K := K) (A := A)
  obtain ⟨d, g, -, hg, hfin⟩ := washnitzerAlgebra.exists_finite_injective
    (AlgHom.Finite.of_surjective π hπ)
  let := g.toRingHom.toAlgebra
  have : Module.Finite (W (Fin d)) A := hfin
  have : Algebra.IsIntegral (W (Fin d)) A := Algebra.IsIntegral.of_finite _ _
  have : FaithfulSMul (W (Fin d)) A :=
    (faithfulSMul_iff_algebraMap_injective (W (Fin d)) A).mpr hg
  refine ⟨d, ?_, g, hg, hfin⟩
  simpa using (ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := W (Fin d)) (S := A))

include K in
/-- A nonzero dagger algebra has finite Krull dimension. The zero algebra instead has
dimension `⊥`. -/
theorem finiteRingKrullDim [Nontrivial A] : FiniteRingKrullDim A := by
  obtain ⟨n, hn, -⟩ := exists_ringKrullDim_eq_finite_injective (K := K) (A := A)
  exact .of_ringKrullDim_eq_natCast hn

/-- Krull dimension is at most the least number of variables in a surjective presentation.
The bound also includes the zero algebra. -/
theorem ringKrullDim_le_presentationDim : ringKrullDim A ≤ presentationDim K A := by
  exact (ringKrullDim_le_of_surjective (presentation K A).toRingHom
    (presentation_surjective K A)).trans_eq (by simp)

end IsDaggerAlgebra

end TauCeti.Dagger
