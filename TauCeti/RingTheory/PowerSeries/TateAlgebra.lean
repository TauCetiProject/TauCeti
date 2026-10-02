/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
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

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1 and §5.2.1.
-/

public section

namespace TauCeti.PowerSeries

open Filter
open scoped Topology

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] (c : ℝ) [hc : Fact (0 < c)]

/-- **The Gauss norm on restricted power series.** At a positive radius `c`, the ring of power
series restricted at `c` over a nonarchimedean normed ring is a normed ring for the Gauss norm
`‖∑ aₙ Xⁿ‖ = sup ‖aₙ‖ cⁿ`. -/
noncomputable instance instNormedRingIsRestrictedSubring :
    NormedRing (PowerSeries.IsRestricted.subring (R := R) c) :=
  RingNorm.toNormedRing
    { toFun f := (f : PowerSeries R).gaussNorm norm c
      map_zero' := PowerSeries.gaussNorm_zero norm c norm_zero
      add_le' f g :=
        (PowerSeries.gaussNorm_add_le_max norm c _ _ hc.out.le norm_nonneg
          IsUltrametricDist.norm_add_le_max (hasGaussNorm_of_isRestricted f.2)
          (hasGaussNorm_of_isRestricted g.2)).trans
          (max_le_add_of_nonneg (PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg)
            (PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg))
      neg' f := by simp [PowerSeries.gaussNorm_eq]
      mul_le' f g :=
        MvPowerSeries.gaussNorm_mul_le norm (fun _ : Unit ↦ c) _ _ (fun _ ↦ hc.out.le)
          norm_nonneg norm_mul_le IsUltrametricDist.isNonarchimedean_norm norm_zero
          (hasGaussNorm_of_isRestricted f.2).hasMvGaussNorm
          (hasGaussNorm_of_isRestricted g.2).hasMvGaussNorm
      eq_zero_of_map_eq_zero' f h := by
        rwa [PowerSeries.gaussNorm_eq_zero_iff norm c _ norm_zero norm_nonneg
          (fun _ ↦ norm_eq_zero.mp) hc.out (hasGaussNorm_of_isRestricted f.2),
          ZeroMemClass.coe_eq_zero] at h }

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
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g ↦
    PowerSeries.gaussNorm_add_le_max norm c _ _ hc.out.le norm_nonneg
      IsUltrametricDist.norm_add_le_max (hasGaussNorm_of_isRestricted f.2)
      (hasGaussNorm_of_isRestricted g.2)

instance [NormOneClass R] : NormOneClass (PowerSeries.IsRestricted.subring (R := R) c) where
  norm_one := by
    have h1 : (1 : PowerSeries.IsRestricted.subring (R := R) c) =
        ⟨PowerSeries.C 1, PowerSeries.isRestricted_C c 1⟩ :=
      Subtype.ext (map_one PowerSeries.C).symm
    rw [h1, norm_C, norm_one]

/-- The Gauss norm on restricted series is multiplicative when the norm on the coefficients is. -/
instance [NormMulClass R] : NormMulClass (PowerSeries.IsRestricted.subring (R := R) c) where
  norm_mul f g := gaussNorm_mul_of_isRestricted hc.out f.2 g.2

/-- **The Tate algebra is complete.** Over a complete nonarchimedean normed ring, the ring of
series restricted at a positive radius is complete for the Gauss norm. A Cauchy sequence converges
coefficientwise, uniformly in the weighted coefficient norms, and its coefficientwise limit is
again restricted. -/
instance [CompleteSpace R] : CompleteSpace (PowerSeries.IsRestricted.subring (R := R) c) := by
  refine Metric.complete_of_cauchySeq_tendsto fun F hF ↦ ?_
  -- Each coefficient map is a bounded additive map, so the coefficients of `F` are Cauchy.
  have hcoeff (n : ℕ) : CauchySeq fun k ↦ (F k : PowerSeries R).coeff n := by
    let coeffHom : PowerSeries.IsRestricted.subring (R := R) c →+ R :=
      (PowerSeries.coeff n).toAddMonoidHom.comp
        (PowerSeries.IsRestricted.subring (R := R) c).subtype.toAddMonoidHom
    refine (AddMonoidHomClass.uniformContinuous_of_bound coeffHom (c ^ n)⁻¹
      fun f ↦ ?_).comp_cauchySeq hF
    rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos hc.out n)]
    exact norm_coeff_mul_pow_le f n
  choose a ha using fun n ↦ cauchySeq_tendsto_of_complete (hcoeff n)
  -- The coefficients converge uniformly in the weighted norms.
  have hunif : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ n,
      ‖(F k : PowerSeries R).coeff n - a n‖ * c ^ n ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF ε hε
    refine ⟨N, fun k hk n ↦ le_of_tendsto
      (((tendsto_const_nhds.sub (ha n)).norm).mul_const (c ^ n))
      (eventually_atTop.mpr ⟨N, fun l hl ↦ ?_⟩)⟩
    have h := norm_coeff_mul_pow_le (F k - F l) n
    rw [AddSubgroupClass.coe_sub, map_sub] at h
    exact h.trans ((dist_eq_norm _ _).symm.trans_le (hN k hk l hl).le)
  have hg : (PowerSeries.mk a).IsRestricted c := by
    rw [PowerSeries.isRestricted_iff']
    refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun n ↦
      hb.trans_le (mul_nonneg (norm_nonneg _) (pow_nonneg hc.out.le n)), fun ε hε ↦ ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    filter_upwards [((PowerSeries.isRestricted_iff' c _).mp (F N).2).eventually
      (gt_mem_nhds (half_pos hε))] with n hn
    calc ‖(PowerSeries.mk a).coeff n‖ * c ^ n
        ≤ ‖(F N : PowerSeries R).coeff n‖ * c ^ n
          + ‖(F N : PowerSeries R).coeff n - a n‖ * c ^ n := by
          rw [PowerSeries.coeff_mk, ← add_mul]
          exact mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub _ _)
            (pow_nonneg hc.out.le n)
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le hn (hN N le_rfl n)
      _ = ε := add_halves ε
  refine ⟨⟨PowerSeries.mk a, hg⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ (?_ : _ ≤ ε / 2).trans_lt (half_lt_self hε)⟩
  rw [dist_eq_norm, norm_le_iff (half_pos hε).le]
  intro n
  simpa using hN k hk n

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] (c : ℝ) [Fact (0 < c)]

/-- Over a commutative base, the restricted series form a normed commutative ring. -/
noncomputable instance instNormedCommRingIsRestrictedSubring :
    NormedCommRing (PowerSeries.IsRestricted.subring (R := R) c) :=
  { instNormedRingIsRestrictedSubring c with mul_comm := mul_comm }

end NormedCommRing

end TauCeti.PowerSeries
