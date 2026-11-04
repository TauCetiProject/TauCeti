/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UnitBall
public import TauCeti.RingTheory.PowerSeries.Geometric
public import TauCeti.RingTheory.PowerSeries.OpenDisc.Basic
public import TauCeti.RingTheory.PowerSeries.TateAlgebra

/-!
# Examples of restricted power series

These examples test the definitions of restricted power series, their Gauss norms, their units
and their reduction against the standard examples over `ℚ_p` and over general coefficient rings.

* The geometric series `∑ pⁿ Xⁿ` is restricted at radius one but not at radius `p`.
* The powers `Xⁿ` tend to zero coefficientwise but not for the unit Gauss norm, where each has
  norm one.
* At the radius `√p` the variable has norm `√p`, although `√p` is not the norm of any element
  of `ℚ_p`: the construction needs no scalar of norm equal to the radius.
* Each row of the diagonal array `aᵢⱼ = δᵢⱼ` is a restricted family in one variable, but the array
  is not restricted in two variables at unit radii.
* `1 - p X` is a unit of `ℚ_p⟨X⟩`, with inverse `∑ pⁿ Xⁿ`, while `1 - X` is not a unit of the
  unit-radius restricted series over any nontrivial ultrametric normed commutative ring: its
  formal inverse `∑ Xⁿ` is not restricted there.
* The reduction of `∑ pⁿ Xⁿ` to a polynomial over the residue field of `ℚ_p` is the constant
  polynomial one.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§5.1.1–5.1.3.
-/

public section

open Filter Topology PowerSeries

namespace TauCeti

section Ring

variable {R : Type*} [NormedRing R]

-- The powers `Xⁿ` tend to zero coefficientwise.
example (k : ℕ) : Tendsto (fun n ↦ coeff k (X ^ n : PowerSeries R)) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' <| (eventually_gt_atTop k).mono fun n hn ↦ by
    simp [coeff_X_pow, hn.ne]

-- Row `i` of the diagonal array `aᵢⱼ = δᵢⱼ` is the restricted series `Xⁱ`.
example (i : ℕ) : (mk fun j ↦ if i = j then (1 : R) else 0).IsRestricted 1 := by
  convert isRestricted_monomial 1 i (1 : R) using 1
  ext j
  simp [coeff_monomial, eq_comm]

-- The diagonal array is not restricted in two variables at unit radii: its coefficients at the
-- infinitely many exponents `(n, n)` all have norm `‖1‖ ≠ 0`.
example [Nontrivial R] (f : MvPowerSeries (Fin 2) R)
    (hf : ∀ t, MvPowerSeries.coeff t f = if t 0 = t 1 then 1 else 0) :
    ¬MvPowerSeries.IsRestricted (fun _ ↦ 1) f := by
  intro h
  have hfin := eventually_cofinite.mp
    (h.eventually (gt_mem_nhds (norm_pos_iff.mpr (one_ne_zero (α := R)))))
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ Finsupp.single 0 n + Finsupp.single 1 n)
    (fun m n hmn ↦ by simpa using DFunLike.congr_fun hmn 0) (fun n ↦ ?_) hfin
  simp [hf]

end Ring

section CommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [Nontrivial R]

-- `1 - X` is not a unit at the unit radius: in `R⟦X⟧` its inverse is `∑ Xⁿ`, which is not
-- restricted there.
example : ¬IsUnit (⟨1 - X, (isRestricted_one 1).sub (isRestricted_monomial 1 1 1)⟩ :
    IsRestricted.subring (R := R) 1) := by
  rintro ⟨u, hu⟩
  have h1 : (mk 1 : PowerSeries R) * (1 - X) = 1 := by
    rw [Pi.one_def]
    simpa using powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one (1 : R)
  have hinv : ((u⁻¹ : (IsRestricted.subring (R := R) 1)ˣ) : PowerSeries R) * (1 - X) = 1 := by
    simpa [hu] using congrArg Subtype.val u.inv_mul
  have h2 : ((u⁻¹ : (IsRestricted.subring (R := R) 1)ˣ) : PowerSeries R) = mk 1 :=
    calc _ = ((u⁻¹ : (IsRestricted.subring (R := R) 1)ˣ) : PowerSeries R) * ((1 - X) * mk 1) := by
          rw [mul_comm (1 - X), h1, mul_one]
      _ = mk 1 := by rw [← mul_assoc, hinv, one_mul]
  exact PowerSeries.not_isRestricted_mk_one (h2 ▸ (u⁻¹ : _).1.2)

end CommRing

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

-- At the unit radius every power `Xⁿ` has Gauss norm one, so the powers do not tend to zero.
example : ¬Tendsto (fun n ↦ (⟨X, isRestricted_monomial 1 1 1⟩ :
    IsRestricted.subring (R := K) 1) ^ n) atTop (𝓝 0) := by
  intro h
  have := (continuous_norm.tendsto 0).comp h
  simp only [Function.comp_def, norm_pow, PowerSeries.norm_X, one_pow, norm_zero] at this
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

end Field

section Padic

variable (p : ℕ) [hp : Fact p.Prime]

-- `∑ pⁿ Xⁿ` is restricted at radius one, inside its open disc of convergence of radius `p`.
example : (mk fun n ↦ (p : ℚ_[p]) ^ n).IsRestricted 1 :=
  (onOpenDisc_mk_pow _).isRestricted (by simpa [Padic.norm_p] using hp.out.one_lt)

-- `∑ pⁿ Xⁿ` is not restricted at radius `p`, where all its weighted coefficient norms are one.
example : ¬(mk fun n ↦ (p : ℚ_[p]) ^ n).IsRestricted p := by
  simpa [Padic.norm_p] using
    PowerSeries.not_isRestricted_mk_pow (R := ℚ_[p]) (a := p) (Nat.cast_ne_zero.mpr hp.out.ne_zero)

/-- The radius `√p` is positive. -/
local instance : Fact (0 < √p) :=
  ⟨Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.out.pos)⟩

-- At the radius `√p` the variable has Gauss norm `√p`.
example : ‖(⟨X, isRestricted_monomial _ 1 1⟩ : IsRestricted.subring (R := ℚ_[p]) √p)‖ = √p :=
  PowerSeries.norm_X

-- The radius `√p` is not the norm of an element of `ℚ_p`: nonzero norms are integer powers of `p`.
example (x : ℚ_[p]) : ‖x‖ ≠ √p := by
  intro hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hx
    exact (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.out.pos)).ne hx
  rw [Padic.norm_eq_zpow_neg_valuation hx0] at hx
  have h : (p : ℝ) ^ (1 : ℤ) = (p : ℝ) ^ (2 * -x.valuation) := by
    rw [zpow_one, zpow_mul', hx, zpow_ofNat, Real.sq_sqrt (Nat.cast_nonneg p)]
  have := zpow_right_injective₀ (Nat.cast_pos.mpr hp.out.pos) (Nat.cast_ne_one.mpr hp.out.ne_one) h
  omega

-- `1 - p X` is a unit of `ℚ_p⟨X⟩`, with inverse `∑ pⁿ Xⁿ`.
example : IsUnit (⟨1 - C (p : ℚ_[p]) * X,
    (isRestricted_one 1).sub ((isRestricted_C 1 _).mul (isRestricted_monomial 1 1 1))⟩ :
      IsRestricted.subring (R := ℚ_[p]) 1) :=
  IsUnit.of_mul_eq_one
    ⟨_, (onOpenDisc_mk_pow _).isRestricted (by simpa [Padic.norm_p] using hp.out.one_lt)⟩ <|
    Subtype.ext <|
    (mul_comm _ _).trans (powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one _)

-- The reduction of `∑ pⁿ Xⁿ` modulo the maximal ideal of `ℤ_p` is the constant polynomial one:
-- its constant coefficient is one and all its other coefficients have norm less than one.
example : MvPowerSeries.restrictedReduction (⟨⟨mk fun n ↦ (p : ℚ_[p]) ^ n,
      (onOpenDisc_mk_pow _).isRestricted (by simpa [Padic.norm_p] using hp.out.one_lt)⟩,
    MvPowerSeries.mem_unitClosedBall_iff.mpr fun t ↦ by
      rw [← coeff_def rfl, coeff_mk, norm_pow, Padic.norm_p]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (mod_cast hp.out.one_le))⟩ :
      Subring.unitClosedBall (_root_.MvPowerSeries.IsRestricted.subring (R := ℚ_[p])
        fun _ : Unit ↦ 1)) = 1 := by
  ext t
  rw [MvPolynomial.coeff_one]
  split_ifs with ht
  · subst ht
    rw [MvPowerSeries.coeff_restrictedReduction, ← map_one (IsLocalRing.residue _)]
    exact congrArg _ (Subtype.ext (by simp [← coeff_def rfl]))
  · rw [MvPowerSeries.coeff_restrictedReduction_eq_zero_iff, ← coeff_def rfl, coeff_mk, norm_pow,
      Padic.norm_p]
    refine pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ (mod_cast hp.out.one_lt)) ?_
    exact fun h ↦ ht (Finsupp.ext fun _ ↦ h.symm)

end Padic

end TauCeti
