/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import TauCeti.RingTheory.PowerSeries.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius

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
is the setting in which Bosch–Güntzer–Remmert apply Weierstrass division in `n` variables.
It satisfies the hypotheses of
`TauCeti.PowerSeries.IsMulDistinguished.existsUnique_mul_add_eq_subring`: with a multiplicative
coefficient norm, every unit coefficient is a multiplicative unit.

The radius is supplied as an instance argument `[Fact (0 < c)]`; at the unit radius it is found
automatically.

Setting the variable to zero is a surjection onto `R` killing the non-zero-divisor `X`, so at any
radius the Krull dimension of the restricted series ring is at least `dim R + 1`.

## Main results

* `TauCeti.PowerSeries.norm_eq_gaussNorm`: the norm of a restricted series is its Gauss norm.
* `TauCeti.PowerSeries.norm_le_iff`: the norm is bounded by `r` exactly when every weighted
  coefficient norm `‖aₙ‖ cⁿ` is.
* `TauCeti.PowerSeries.tendsto_trunc_atTop`: polynomial truncations converge in the Gauss norm.
* `TauCeti.PowerSeries.norm_C`, `TauCeti.PowerSeries.norm_X`: constants keep their norm, and the
  variable has norm `c`.
* `TauCeti.PowerSeries.nnnorm_eq_gaussValuation`: the norm is the Gauss valuation
  `TauCeti.PowerSeries.gaussValuation`.
* `TauCeti.PowerSeries.ringKrullDim_succ_le_ringKrullDim_isRestricted_subring`: adjoining a
  restricted variable, at any radius, raises the Krull dimension by at least one.
* `PowerSeries.isRestricted_map_of_abs_lt_one` and `TauCeti.PowerSeries.isUnit_mk_map`: series
  with coefficients mapped into the closed unit ball are restricted inside the unit disc, and
  units of `O⟦X⟧` map to units of every ring of series restricted there.
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

/-- The norm of a restricted series is bounded by `r` exactly when every weighted coefficient norm
`‖aₙ‖ cⁿ` is. -/
theorem norm_le_iff {f : PowerSeries.IsRestricted.subring (R := R) c} {r : ℝ} :
    ‖f‖ ≤ r ↔ ∀ n, ‖(f : PowerSeries R).coeff n‖ * c ^ n ≤ r := by
  refine ⟨fun h n ↦ (norm_coeff_mul_pow_le f n).trans h, fun h ↦ ?_⟩
  rw [norm_eq_gaussNorm, PowerSeries.gaussNorm_eq]
  exact Real.iSup_le h <| (norm_nonneg _).trans (by simpa using h 0)

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

/-- Each coefficient is uniformly continuous for the positive-radius Gauss norm.
This specializes the multivariate coefficient map at `Finsupp.single () n`, using
`PowerSeries R = MvPowerSeries Unit R` and the corresponding restricted subrings. -/
theorem uniformContinuous_coeff (n : ℕ) :
    UniformContinuous fun f : PowerSeries.IsRestricted.subring (R := R) c ↦
      PowerSeries.coeff n (f : PowerSeries R) :=
  _root_.MvPowerSeries.uniformContinuous_coeff_isRestrictedSubring
    (c := fun _ : Unit ↦ c) (Finsupp.single () n)

/-- Polynomial truncations converge to a restricted series in its positive-radius Gauss norm. -/
theorem tendsto_trunc_atTop (f : PowerSeries.IsRestricted.subring (R := R) c) :
    Tendsto (fun n ↦ (⟨((f : PowerSeries R).trunc n : PowerSeries R),
      isRestricted_polynomial _⟩ : PowerSeries.IsRestricted.subring (R := R) c)) atTop (𝓝 f) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((PowerSeries.isRestricted_iff' c _).mp f.2).eventually
      (gt_mem_nhds (half_pos hε)))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_le_iff.mpr fun m ↦ ?_) (half_lt_self hε)
  simp only [AddSubgroupClass.coe_sub, map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hm
  · simp only [sub_self, norm_zero, zero_mul]
    exact (half_pos hε).le
  · simpa using (hN m (hn.trans (Nat.le_of_not_gt hm))).le

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

section Radius

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s)

/-- Restrict a univariate series to a smaller nonnegative radius. This specializes the
multivariate restriction to constant polyradii on `Unit`. -/
noncomputable def restrictedRadiusHom :
    PowerSeries.IsRestricted.subring (R := R) s →+* PowerSeries.IsRestricted.subring (R := R) r :=
  TauCeti.MvPowerSeries.restrictedRadiusHom (R := R)
    (r := fun _ : Unit ↦ r) (s := fun _ : Unit ↦ s) (fun _ ↦ hr) (fun _ ↦ hrs)

/-- Radius restriction leaves the underlying univariate formal series unchanged. -/
@[simp]
theorem coe_restrictedRadiusHom (f : PowerSeries.IsRestricted.subring (R := R) s) :
    (restrictedRadiusHom hr hrs f : PowerSeries R) = f :=
  TauCeti.MvPowerSeries.coe_restrictedRadiusHom (fun _ : Unit ↦ hr) (fun _ ↦ hrs) f

/-- Radius restriction is continuous for the positive-radius Gauss norms. -/
@[continuity]
theorem continuous_restrictedRadiusHom [Fact (0 < r)] [Fact (0 < s)] :
    Continuous (restrictedRadiusHom (R := R) hr hrs) :=
  TauCeti.MvPowerSeries.continuous_restrictedRadiusHom
    (r := fun _ : Unit ↦ r) (s := fun _ : Unit ↦ s) (fun _ ↦ hr) (fun _ ↦ hrs)

end Radius

section Map

variable {O R : Type*} [Semiring O] [NormedRing R] {φ : O →+* R}

/-- A series whose coefficients map into the closed unit ball of a normed ring is restricted at
every radius of absolute value less than one. -/
theorem _root_.PowerSeries.isRestricted_map_of_abs_lt_one (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (g : PowerSeries O) {r : ℝ} (hr : |r| < 1) :
    (g.map φ).IsRestricted r :=
  _root_.PowerSeries.HasGaussNorm.isRestricted_of_abs_lt
    ⟨1, Set.forall_mem_range.mpr fun n ↦ by simpa using hφ (g.coeff n)⟩ hr

/-- **A formal unit is a unit of every ring of series restricted inside the unit disc.** If `φ`
maps into the closed unit ball, the image of a unit `u` of `O⟦X⟧` is a unit of the ring of series
restricted at any radius of absolute value less than one, with inverse the image of `u⁻¹`. -/
theorem isUnit_mk_map [IsUltrametricDist R] (hφ : ∀ x, ‖φ x‖ ≤ 1) {u : _root_.PowerSeries O}
    (hu : IsUnit u) {r : ℝ} (hr : |r| < 1) :
    IsUnit (⟨u.map φ, u.isRestricted_map_of_abs_lt_one hφ hr⟩ :
      _root_.PowerSeries.IsRestricted.subring (R := R) r) := by
  obtain ⟨u, rfl⟩ := hu
  exact ⟨⟨⟨_, _root_.PowerSeries.isRestricted_map_of_abs_lt_one hφ _ hr⟩,
    ⟨_, _root_.PowerSeries.isRestricted_map_of_abs_lt_one hφ (↑u⁻¹ : _root_.PowerSeries O) hr⟩,
    Subtype.ext (by simp [← map_mul]), Subtype.ext (by simp [← map_mul])⟩, rfl⟩

end Map

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] (c : ℝ) [Fact (0 < c)]

/-- The normed commutative multivariate restricted-series ring specialized to one variable. -/
noncomputable instance instNormedCommRingIsRestrictedSubring :
    NormedCommRing (PowerSeries.IsRestricted.subring (R := R) c) :=
  inferInstanceAs (NormedCommRing
    (MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Unit ↦ c)))

/-- Coefficients act boundedly on the restricted algebra with its Gauss norm. -/
instance : IsBoundedSMul R (PowerSeries.IsRestricted.subring (R := R) c) :=
  IsBoundedSMul.of_norm_smul_le fun a f ↦ by
    have ha : algebraMap R (PowerSeries.IsRestricted.subring (R := R) c) a =
        ⟨PowerSeries.C a, PowerSeries.isRestricted_C c a⟩ :=
      Subtype.ext (MvPowerSeries.coe_algebraMap_isRestrictedSubring a)
    simpa only [Algebra.smul_def, ha, norm_C] using
      norm_mul_le (algebraMap R (PowerSeries.IsRestricted.subring (R := R) c) a) f

variable {c} in
/-- In the Gauss norm at a radius `c > 0`, the linear polynomial `a + d X` has weighted norm at
most `M` once both `‖a‖` and `‖d‖ c` do. -/
theorem norm_polynomialToRestricted_C_add_X_mul_C_mul_le {a d : R} {w M : ℝ}
    (ha : ‖a‖ * w ≤ M) (hd : ‖d‖ * c * w ≤ M) :
    ‖polynomialToRestricted c (Polynomial.C a + Polynomial.X * Polynomial.C d)‖ * w ≤ M := by
  rcases le_or_gt w 0 with hw | hw
  · have h0 := norm_coeff_mul_pow_le
      (polynomialToRestricted c (Polynomial.C a + Polynomial.X * Polynomial.C d)) 0
    simp only [coe_polynomialToRestricted, Polynomial.coeff_coe, pow_zero, mul_one,
      Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero, add_zero] at h0
    exact (mul_le_mul_of_nonpos_right h0 hw).trans ha
  have hM : 0 ≤ M := (mul_nonneg (norm_nonneg _) hw.le).trans ha
  rw [← le_div_iff₀ hw, norm_le_iff]
  intro i
  rw [le_div_iff₀ hw]
  rcases i with _ | _ | i
  · simpa using ha
  · simpa [mul_right_comm] using hd
  · simpa [Polynomial.coeff_C, Polynomial.coeff_X_mul] using hM

end NormedCommRing

section KrullDimension

/-- Setting the variable to zero shows `dim R + 1 ≤ dim R⟨X⟩` for the ring of restricted power
series of any radius over an ultrametric normed commutative ring `R`. -/
theorem ringKrullDim_succ_le_ringKrullDim_isRestricted_subring {R : Type*} [NormedCommRing R]
    [IsUltrametricDist R] (c : ℝ) :
    ringKrullDim R + 1 ≤ ringKrullDim (PowerSeries.IsRestricted.subring (R := R) c) := by
  let S := PowerSeries.IsRestricted.subring (R := R) c
  let X : S := ⟨PowerSeries.X, PowerSeries.X_eq (R := R) ▸ PowerSeries.isRestricted_monomial c 1 1⟩
  have hX : X ∈ nonZeroDivisors S := mem_nonZeroDivisors_iff_right.mpr fun x hx ↦
    Subtype.ext <| PowerSeries.mul_X_cancel (ψ := 0) (by simpa [X] using congrArg Subtype.val hx)
  exact ringKrullDim_succ_le_of_surjective (PowerSeries.constantCoeff.comp S.subtype)
    (fun r ↦ ⟨⟨PowerSeries.C r, PowerSeries.isRestricted_C c r⟩, by simp⟩) hX (by simp [X])

end KrullDimension

end TauCeti.PowerSeries
