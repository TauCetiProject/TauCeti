/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.RingTheory.MvPowerSeries.Ideal

/-!
# The cotangent module at the origin of a formal power series ring

The degree-one coefficients give the coordinates on the cotangent module of a formal
power series ring at the origin. In finitely many variables `cotangentCoeffEquiv`
identifies that module with the corresponding finite product of the coefficient ring.
Consequently `finrank_cotangent_ker_constantCoeff` recovers the number of variables
over any nontrivial commutative ring.

This is the cotangent dimension calculation for a formal Lie group in coordinates
(Stix, *A course on finite flat group schemes and p-divisible groups*, §10.2.2).
The construction uses `Ideal.Cotangent.lift` and the injectivity calculation uses
`MvPowerSeries.mem_pow_span_range_X_iff_le_order`.
-/

public section

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*} [CommRing R]

local notation "I" => RingHom.ker (constantCoeff (σ := σ) (R := R))

/-- The map from the cotangent module at the origin to the tuple of linear coefficients. -/
noncomputable def cotangentCoeff : (I).Cotangent →ₗ[R] (σ → R) :=
  Ideal.Cotangent.lift
    (LinearMap.pi fun i ↦ (coeff (single i 1)).comp
      ((I).subtype.restrictScalars R))
    (by
      intro f g
      have hf : 1 ≤ (f : MvPowerSeries σ R).order :=
        one_le_order_iff_constCoeff_eq_zero.mpr (RingHom.mem_ker.mp f.prop)
      have hg : 1 ≤ (g : MvPowerSeries σ R).order :=
        one_le_order_iff_constCoeff_eq_zero.mpr (RingHom.mem_ker.mp g.prop)
      have hfg : 1 + 1 ≤ ((f * g : I) : MvPowerSeries σ R).order :=
        (add_le_add hf hg).trans le_order_mul
      funext i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply, Pi.zero_apply]
      apply coeff_of_lt_order
      have hsmall : (1 : ℕ∞) < 1 + 1 := (by decide)
      simpa only [degree_single, Nat.cast_one] using lt_of_lt_of_le hsmall hfg)

/-- On a representative of a cotangent class, the coordinates are the degree-one coefficients. -/
@[simp]
theorem cotangentCoeff_toCotangent (f : I) (i : σ) :
    cotangentCoeff ((I).toCotangent f) i =
      coeff (single i 1) (f : MvPowerSeries σ R) :=
  congrFun (Ideal.Cotangent.lift_toCotangent _ _ f) i

/-- Every tuple occurs as the linear coefficients of a series vanishing at the origin. -/
theorem cotangentCoeff_surjective : Function.Surjective (cotangentCoeff (σ := σ) (R := R)) := by
  classical
  intro a
  let f : MvPowerSeries σ R := Function.extend (fun i ↦ single i 1) a 0
  have hf : f ∈ I := by
    rw [RingHom.mem_ker, ← coeff_zero_eq_constantCoeff_apply, coeff_apply]
    exact Function.extend_apply' _ _ _ (by simp)
  refine ⟨(I).toCotangent ⟨f, hf⟩, ?_⟩
  funext i
  rw [cotangentCoeff_toCotangent, coeff_apply]
  exact (single_left_injective one_ne_zero).extend_apply a 0 i

/-- In finitely many variables a cotangent class is determined by its linear coefficients. -/
theorem cotangentCoeff_injective [Finite σ] :
    Function.Injective (cotangentCoeff (σ := σ) (R := R)) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨f, rfl⟩ := (I).toCotangent_surjective z
  have hI : I = Ideal.span (Set.range X) :=
    Ideal.ext fun _ ↦ RingHom.mem_ker.trans mem_span_range_X_iff.symm
  rw [Ideal.toCotangent_eq_zero, congrArg (· ^ 2) hI, mem_pow_span_range_X_iff_le_order]
  apply nat_le_order
  intro d hd
  rcases (by lia : d.degree = 0 ∨ d.degree = 1) with h₀ | h₁
  · rw [(degree_eq_zero_iff _).mp h₀, coeff_zero_eq_constantCoeff_apply]
    exact RingHom.mem_ker.mp f.prop
  · have hmem : d ∈ Set.range (fun i : σ ↦ single i 1) :=
      range_single_one.symm ▸ h₁
    obtain ⟨i, rfl⟩ := hmem
    simpa only [cotangentCoeff_toCotangent, Pi.zero_apply] using congrFun hz i

/-- The cotangent module of a formal power series ring in finitely many variables is freely
coordinatized by the degree-one coefficients. -/
noncomputable def cotangentCoeffEquiv [Finite σ] : (I).Cotangent ≃ₗ[R] (σ → R) :=
  LinearEquiv.ofBijective cotangentCoeff ⟨cotangentCoeff_injective, cotangentCoeff_surjective⟩

/-- The equivalence sends a cotangent class to the degree-one coefficients of any representative. -/
@[simp]
theorem cotangentCoeffEquiv_toCotangent [Finite σ] (f : I) (i : σ) :
    cotangentCoeffEquiv ((I).toCotangent f) i =
      coeff (single i 1) (f : MvPowerSeries σ R) :=
  (congrFun (LinearEquiv.ofBijective_apply _ _) i).trans (cotangentCoeff_toCotangent f i)

/-- The coordinate unit vector at `i` corresponds to the class of `X i`. -/
@[simp]
theorem cotangentCoeffEquiv_symm_single [Finite σ] [DecidableEq σ] (i : σ) :
    (cotangentCoeffEquiv (R := R)).symm (Pi.single i 1) =
      (I).toCotangent ⟨X i, RingHom.mem_ker.mpr (constantCoeff_X i)⟩ := by
  apply (cotangentCoeffEquiv (σ := σ) (R := R)).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  simp only [cotangentCoeffEquiv_toCotangent, coeff_index_single_X, Pi.single_apply,
    eq_comm]

/-- Over a nontrivial commutative ring, the rank of the cotangent module at the origin is the
number of variables. -/
theorem finrank_cotangent_ker_constantCoeff [Finite σ] [Nontrivial R] :
    Module.finrank R (I).Cotangent = Nat.card σ := by
  let := Fintype.ofFinite σ
  rw [(cotangentCoeffEquiv (σ := σ) (R := R)).finrank_eq, Module.finrank_pi,
    Nat.card_eq_fintype_card]

end MvPowerSeries
