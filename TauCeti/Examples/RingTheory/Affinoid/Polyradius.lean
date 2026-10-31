/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Polyradius
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber

/-!
# Strict and non-strict radii over the p-adic numbers

The radius `p^(-1/2)` gives a strict affinoid algebra, and its Gauss norm is the supremum
norm. In contrast, the square of the Liouville number is a positive radius outside the
divisible hull of the value group of every `ℚ_p`: all p-adic norms are rational, whereas
every positive power of this radius is transcendental. Its restricted-series algebra
is therefore not strictly affinoid.

The examples use the Liouville number and its transcendence theorem from Mathlib.
-/

public section

open MvPowerSeries TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

local instance : Fact (0 < (√(p : ℝ))⁻¹) :=
  ⟨inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.out.pos))⟩

-- The square root of the norm of p gives a strict algebra and the expected supremum norm.
example : supSeminorm ℚ_[p]
    (⟨X (), isRestricted_X (fun _ : Unit ↦ (√(p : ℝ))⁻¹) ()⟩ :
      IsRestricted.subring (R := ℚ_[p]) (fun _ : Unit ↦ (√(p : ℝ))⁻¹)) =
        (√(p : ℝ))⁻¹ := by
  have hA : IsAffinoidAlgebra ℚ_[p]
      (IsRestricted.subring (R := ℚ_[p]) (fun _ : Unit ↦ (√(p : ℝ))⁻¹)) := by
    apply isAffinoidAlgebra_isRestricted_of_pow_eq_norm
    intro _
    refine ⟨2, by decide, Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr hp.out.ne_zero), ?_⟩
    simp [inv_pow, Real.sq_sqrt (Nat.cast_nonneg p), Padic.norm_p]
  rw [hA.supSeminorm_eq_norm_of_normMulClass, MvPowerSeries.norm_X]

local instance : Fact (0 < liouvilleNumber 2 ^ 2) :=
  ⟨sq_pos_of_ne_zero (transcendental_liouvilleNumber (by decide : 2 ≤ 2)).ne_zero⟩

-- A concrete positive radius outside p^ℚ, for every prime p.
example : ¬ IsAffinoidAlgebra ℚ_[p]
    (IsRestricted.subring (R := ℚ_[p]) (fun _ : Unit ↦ liouvilleNumber 2 ^ 2)) := by
  intro hA
  obtain ⟨n, hn, c, hc⟩ :=
    isAffinoidAlgebra_isRestricted_iff_pow_eq_norm.mp hA ()
  have ht : Transcendental ℚ (liouvilleNumber 2 ^ 2) := by
    rw [Transcendental, ← IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ]
    exact (transcendental_liouvilleNumber (by decide : 2 ≤ 2)).pow (by decide)
  apply ht.pow hn
  rw [hc, ← Padic.padicNormE.is_norm]
  exact isAlgebraic_ratCast ℚ _

-- The formal geometric series ∑ Tⁿ is not restricted on the closed unit boundary.
example : ¬ PowerSeries.IsRestricted 1
    (PowerSeries.mk fun _ ↦ (1 : ℚ_[p])) := by
  simp [PowerSeries.isRestricted_iff', tendsto_const_nhds_iff]

-- No variables: both sides of the criterion hold, with no conditions on radii.
example {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (r : Fin 0 → ℝ) : IsAffinoidAlgebra K (IsRestricted.subring (R := K) r) := by
  let : ∀ i, Fact (0 < r i) := fun i ↦ Fin.elim0 i
  exact isAffinoidAlgebra_isRestricted_iff_pow_eq_norm.mpr fun i ↦ Fin.elim0 i
