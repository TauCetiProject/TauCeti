/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Restricted power series as a normed ring

Let `R` be a nonarchimedean normed ring and `c` a positive real number. The ring
`PowerSeries.IsRestricted.subring c` of power series `∑ aₙ Xⁿ` over `R` with `‖aₙ‖ cⁿ → 0` carries
the Gauss norm `‖∑ aₙ Xⁿ‖ = sup ‖aₙ‖ cⁿ`. This file makes it a normed ring for that norm, and shows
that the norm inherits the properties of the norm on `R` that the theory of Tate algebras uses:

* it is ultrametric;
* it is multiplicative when the norm on `R` is;
* it is complete when `R` is complete.

At the unit radius over a complete nonarchimedean field `K`, the result is the Tate algebra
`K⟨X⟩` with its Gauss norm. Iterating the construction, the ring of series in one more variable
restricted over `K⟨X₁, …, Xₙ₋₁⟩` is again complete, ultrametric and multiplicatively normed. This
is the setting in which Bosch–Güntzer–Remmert apply Weierstrass division in `n` variables, and it
is exactly the hypothesis set of
`TauCeti.PowerSeries.IsDistinguished.existsUnique_mul_add_eq_subring`.

The radius is supplied as an instance argument `[Fact (0 < c)]`; at the unit radius it is found
automatically.

## Main results

* `TauCeti.PowerSeries.norm_eq_gaussNorm`: the norm of a restricted series is its Gauss norm.
* `TauCeti.PowerSeries.norm_le_iff`: the norm is bounded by `r ≥ 0` exactly when every weighted
  coefficient norm `‖aₙ‖ cⁿ` is.
* `TauCeti.PowerSeries.norm_C`, `TauCeti.PowerSeries.norm_X`: constants keep their norm, and the
  variable has norm `c`.
* `TauCeti.PowerSeries.nnnorm_eq_gaussValuation`: the norm is the Gauss valuation
  `TauCeti.PowerSeries.gaussValuation`.
* Instances: `NormedRing`, `NormedCommRing`, `IsUltrametricDist`, `NormOneClass`,
  `NormMulClass` and `CompleteSpace` on `PowerSeries.IsRestricted.subring c`.

Apply the norm lemmas by qualified name, for example `TauCeti.PowerSeries.norm_eq_gaussNorm f`.
The normed and completeness instances are supplied by the multivariate construction in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic`. Elements of the restricted subring have type
`Subtype`, rather than a new Tate algebra type.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1 and §5.2.1.
-/

public section

namespace TauCeti.PowerSeries

open Filter
open scoped Topology

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ) [hc : Fact (0 < c)]

/-- The multivariate Gauss norm, specialized to the constant polyradius on `Unit`.
Mathlib's univariate subring is a semireducible wrapper for instance matching, so this
specialization supplies the same normed-ring data explicitly. -/
noncomputable instance instNormedRingIsRestrictedSubring :
    NormedRing (PowerSeries.IsRestricted.subring (R := R) c) :=
  inferInstanceAs (NormedRing
    (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Unit ↦ c)))

variable {c}

/-- The norm of a restricted power series is its Gauss norm. -/
theorem norm_eq_gaussNorm (f : PowerSeries.IsRestricted.subring (R := R) c) :
    ‖f‖ = (f : PowerSeries R).gaussNorm norm c := (rfl)

/-- Each weighted coefficient norm `‖aₙ‖ cⁿ` of a restricted series is bounded by its norm. -/
theorem norm_coeff_mul_pow_le (f : PowerSeries.IsRestricted.subring (R := R) c) (n : ℕ) :
    ‖(f : PowerSeries R).coeff n‖ * c ^ n ≤ ‖f‖ :=
  PowerSeries.le_gaussNorm norm c _ (hasGaussNorm_of_isRestricted f.2) n

/-- The norm of a restricted series is bounded by a nonnegative `r` exactly when every weighted
coefficient norm `‖aₙ‖ cⁿ` is. -/
theorem norm_le_iff {f : PowerSeries.IsRestricted.subring (R := R) c} {r : ℝ} (hr : 0 ≤ r) :
    ‖f‖ ≤ r ↔ ∀ n, ‖(f : PowerSeries R).coeff n‖ * c ^ n ≤ r := by
  refine ⟨fun h n ↦ (norm_coeff_mul_pow_le f n).trans h, fun h ↦ ?_⟩
  rw [norm_eq_gaussNorm, PowerSeries.gaussNorm_eq]
  exact Real.iSup_le h hr

/-- A constant series has the norm of its coefficient. -/
@[simp]
theorem norm_C (a : R) :
    ‖(⟨PowerSeries.C a, PowerSeries.isRestricted_C c a⟩ :
      PowerSeries.IsRestricted.subring (R := R) c)‖ = ‖a‖ := by
  rw [norm_eq_gaussNorm, gaussNorm_eq_of_forall_le (s := 0) fun m ↦ ?_]
  · simp
  · rcases eq_or_ne m 0 with rfl | hm
    · rfl
    · simp [PowerSeries.coeff_C, hm]

/-- The variable has norm `c`. -/
@[simp]
theorem norm_X [NormOneClass R] :
    ‖(⟨PowerSeries.X, by
        rw [PowerSeries.X_eq]
        exact PowerSeries.isRestricted_monomial c 1 (1 : R)⟩ :
      PowerSeries.IsRestricted.subring (R := R) c)‖ = c := by
  rw [norm_eq_gaussNorm, gaussNorm_eq_of_forall_le (s := 1) fun m ↦ ?_]
  · simp
  · rcases eq_or_ne m 1 with rfl | hm
    · rfl
    · simp [PowerSeries.coeff_X, hm, hc.out.le]

/-- The norm of a restricted series is its Gauss valuation. -/
theorem nnnorm_eq_gaussValuation [NormMulClass R] [NormOneClass R]
    (f : PowerSeries.IsRestricted.subring (R := R) c) :
    ‖f‖₊ = gaussValuation hc.out f :=
  NNReal.eq <| by rw [coe_nnnorm, coe_gaussValuation, norm_eq_gaussNorm]

variable (c)

instance : IsUltrametricDist (PowerSeries.IsRestricted.subring (R := R) c) :=
  inferInstanceAs (IsUltrametricDist
    (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Unit ↦ c)))

instance [NormOneClass R] : NormOneClass (PowerSeries.IsRestricted.subring (R := R) c) :=
  inferInstanceAs (NormOneClass
    (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Unit ↦ c)))

/-- The multiplicative multivariate Gauss norm specialized to one variable. -/
instance [NormMulClass R] : NormMulClass (PowerSeries.IsRestricted.subring (R := R) c) :=
  inferInstanceAs (NormMulClass
    (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Unit ↦ c)))

/-- Completeness of the multivariate Gauss norm specialized to one variable. -/
instance [CompleteSpace R] : CompleteSpace (PowerSeries.IsRestricted.subring (R := R) c) :=
  inferInstanceAs (CompleteSpace
    (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Unit ↦ c)))

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] (c : ℝ) [Fact (0 < c)]

/-- The normed commutative multivariate restricted-series ring specialized to one variable. -/
noncomputable instance instNormedCommRingIsRestrictedSubring :
    NormedCommRing (PowerSeries.IsRestricted.subring (R := R) c) :=
  inferInstanceAs (NormedCommRing
    (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Unit ↦ c)))

end NormedCommRing

end TauCeti.PowerSeries
