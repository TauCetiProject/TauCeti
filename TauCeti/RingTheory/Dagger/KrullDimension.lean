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
import TauCeti.RingTheory.Dagger.Preparation
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

Every maximal ideal of `K⟨X₁, …, Xₙ⟩†` moreover has height `n`, so the algebra is
equidimensional. Writing `K⟨X, Y⟩†` for the algebra in one more variable `Y`, a nonzero maximal
ideal `M` of `K⟨X, Y⟩†` contains, after a change of variables, the evaluation at `Y` of a
Weierstrass polynomial `ω ∈ K⟨X⟩†[Y]`. Then `K⟨X, Y⟩† ⧸ (ω) ≅ K⟨X⟩†[Y] ⧸ (ω)` is finite free over
`K⟨X⟩†`, so going down bounds the height of the image of `M` below by that of a maximal ideal of
`K⟨X⟩†`, and quotienting by the non-zero-divisor `ω` lowers heights by one.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.ringKrullDim_eq_natCard`: `K⟨X⟩†` in the variables `σ` has
  Krull dimension `Nat.card σ`.
* `Ideal.height_eq_natCard_of_isMaximal_washnitzerAlgebra`: every maximal ideal of `K⟨X⟩†` in the
  variables `σ` has height `Nat.card σ`.
* `Ideal.ringKrullDim_localization_atPrime_of_isMaximal_washnitzerAlgebra`: the localization of
  `K⟨X⟩†` at a maximal ideal has Krull dimension `Nat.card σ`.
* `TauCeti.Dagger.IsDaggerAlgebra.exists_ringKrullDim_eq_finite_injective`: a nonzero dagger
  algebra is finite over an overconvergent algebra in `dim A` variables.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.4(2) and Proposition 1.5.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §6.1.2.

The dimension and height inductions follow `TauCeti.MvPowerSeries.ringKrullDim_isRestricted_subring`
and `Ideal.height_eq_natCard_of_isMaximal_isRestricted_subring` in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.KrullDimension`, using overconvergent Weierstrass
preparation and division in place of division in a complete Tate algebra.
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

open scoped nonZeroDivisors in
/-- The inductive step for heights: if every maximal ideal of `K⟨X⟩†` has height at least the
number `n` of variables, then every maximal ideal of `K⟨X, Y⟩†` has height at least `n + 1`. -/
private theorem natCard_add_one_le_height_option {σ : Type*} [Finite σ]
    (IH : ∀ (p : Ideal (W σ)) [p.IsMaximal], Nat.card σ ≤ p.height)
    (M : Ideal (W (Option σ))) [M.IsMaximal] : Nat.card (Option σ) ≤ M.height := by
  -- `M ≠ 0`, since `K⟨X, Y⟩†` has positive dimension and so is not a field.
  have hM : M ≠ ⊥ := by
    rintro rfl
    have := ringKrullDim_eq_zero_of_isField (Ring.isField_iff_maximal_bot.mpr ‹_›)
    rw [ringKrullDim_eq_natCard, Finite.card_option] at this
    exact Nat.succ_ne_zero (Nat.card σ) (by exact_mod_cast this)
  obtain ⟨f, hfM, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  obtain ⟨E, s, ω, hd, hm, v, hv⟩ := exists_associated_polynomialToOption f hf
  let N : Ideal (W (Option σ)) := M.comap E
  have : N.IsMaximal := Ideal.comap_isMaximal_of_surjective E E.surjective
  -- `K⟨X, Y⟩† ⧸ (ω) ≅ K⟨X⟩†[Y] ⧸ (ω)` is finite free over `K⟨X⟩†`, so it is integral with going
  -- down; as `ω` is a non-zero-divisor, `N` has height at least one more than some maximal ideal
  -- of `K⟨X⟩†`.
  have : Module.Free (W σ) (AdjoinRoot ω) := hm.monic.free_adjoinRoot
  have : Module.Finite (W σ) (AdjoinRoot ω) := hm.monic.finite_adjoinRoot
  have : Algebra.IsIntegral (W σ) (AdjoinRoot ω) := Algebra.IsIntegral.of_finite _ _
  have hg : polynomialToOption ω ∈ (W (Option σ))⁰ :=
    mem_nonZeroDivisors_of_ne_zero fun h ↦ hm.ne_zero (polynomialToOption_injective (by simpa))
  obtain ⟨p, _, hp⟩ := N.exists_isMaximal_height_add_one_le_of_ringEquiv_quotient (R := W σ)
    (Ideal.mem_comap.mpr (hv ▸ M.mul_mem_right _ hfM)) hg
    (polynomialQuotientEquiv hd hm).toRingEquiv
  rw [← RingEquiv.height_comap E M, Finite.card_option, Nat.cast_add, Nat.cast_one]
  exact le_trans (by gcongr; exact IH p) hp

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
  have : Module.Finite (W (Fin d)) A := RingHom.finite_algebraMap.mp hfin
  have : Algebra.IsIntegral (W (Fin d)) A := Algebra.IsIntegral.of_finite _ _
  have : FaithfulSMul (W (Fin d)) A :=
    (faithfulSMul_iff_algebraMap_injective (W (Fin d)) A).mpr hg
  refine ⟨d, ?_, g, hg, hfin⟩
  simpa using washnitzerAlgebra.ringKrullDim_eq_natCard_of_isIntegral (K := K) (σ := Fin d) (A := A)

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

namespace Ideal

open TauCeti.Dagger

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Heights of maximal ideals of Monsky–Washnitzer algebras.** Over a complete ultrametric
normed field, every maximal ideal of `K⟨X₁, …, Xₙ⟩†` has height `n`, its Krull dimension. -/
@[simp]
theorem height_eq_natCard_of_isMaximal_washnitzerAlgebra {σ : Type*} [Finite σ]
    (M : Ideal (washnitzerAlgebra σ K)) [M.IsMaximal] : M.height = Nat.card σ := by
  refine le_antisymm ?_ ?_
  · have := Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top' (I := M))
    rw [washnitzerAlgebra.ringKrullDim_eq_natCard] at this
    exact_mod_cast this
  revert M
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    intro M _
    let e' : washnitzerAlgebra _ K ≃+* washnitzerAlgebra _ K :=
      (washnitzerAlgebra.renameAlgEquiv (R := K) e).toRingEquiv
    have := H (M.comap e')
    rwa [RingEquiv.height_comap, Nat.card_congr e] at this
  | h_empty => simp
  | h_option IH => exact washnitzerAlgebra.natCard_add_one_le_height_option IH

/-- **Monsky–Washnitzer algebras are equidimensional.** The localization of `K⟨X₁, …, Xₙ⟩†` at
any maximal ideal has Krull dimension `n`. -/
@[simp]
theorem ringKrullDim_localization_atPrime_of_isMaximal_washnitzerAlgebra {σ : Type*} [Finite σ]
    (M : Ideal (washnitzerAlgebra σ K)) [M.IsMaximal] :
    ringKrullDim (Localization.AtPrime M) = Nat.card σ := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height M (Localization.AtPrime M),
    height_eq_natCard_of_isMaximal_washnitzerAlgebra]
  norm_cast

end Ideal
