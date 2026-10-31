/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.OpenDisc.Eval
public import TauCeti.RingTheory.PowerSeries.TateAlgebra

/-!
# Power series with bounded weighted coefficients

For an ultrametric normed ring `R` and a radius `R₀ > 0`, the power series `f = ∑ aₙ Xⁿ` whose
weighted coefficient norms `‖aₙ‖ R₀ⁿ` are bounded form a subring
`PowerSeries.HasGaussNorm.subring R R₀` of `R⟦X⟧`. The Gauss norm `‖f‖ = supₙ ‖aₙ‖ R₀ⁿ` makes it
an ultrametric normed ring, complete when `R` is complete. At the radius `1` these are the series
with bounded coefficients (`PowerSeries.HasGaussNorm.mem_subring_one_iff`), for instance every
series with coefficients in the closed unit ball of `R`.

The bounded series sit between the two neighbouring coefficient algebras:

`IsRestricted.subring R₀ ≤ HasGaussNorm.subring R R₀ ≤ OnOpenDisc.subring R R₀`.

The first inclusion is an isometry for the Gauss norms at `R₀`. The second is uniformly
continuous for the topology of the Gauss norms at all radii below `R₀`, each of which is bounded
by the Gauss norm at `R₀`. Composing with evaluation of series on the open disc, a bounded series
is evaluated continuously at every point `b` with `‖b‖ < R₀` of a complete normed algebra, and in
an ultrametric algebra with `‖1‖ = 1` its value is bounded by its Gauss norm. Neither inclusion is
onto in general: the series `∑ Xⁿ` has bounded coefficients but is not restricted at the radius `1`
(`TauCeti.PowerSeries.not_isRestricted_mk_one`), and over `ℚ_p` the series `log (1 + X)` lies on
the open unit disc (`PowerSeries.onOpenDisc_log`) but has unbounded coefficients
(`TauCeti.not_bddAbove_norm_coeff_log`).

## Main definitions

* `PowerSeries.HasGaussNorm.subring R R₀`: the subring of series with bounded weighted
  coefficient norms at the radius `R₀`.

## Main results

* `PowerSeries.IsRestricted.subring_le_hasGaussNormSubring` and
  `PowerSeries.HasGaussNorm.subring_le_onOpenDiscSubring`: the two inclusions.
* `TauCeti.PowerSeries.HasGaussNorm.norm_eq_gaussNorm` and
  `TauCeti.PowerSeries.HasGaussNorm.norm_le_iff`: the norm is the supremum of the weighted
  coefficient norms.
* `TauCeti.PowerSeries.HasGaussNorm.isometry_inclusion_isRestrictedSubring`: restricted series
  keep their Gauss norm.
* `TauCeti.PowerSeries.HasGaussNorm.uniformContinuous_inclusion_onOpenDiscSubring`: the inclusion
  into series on the open disc is uniformly continuous.
* `TauCeti.PowerSeries.HasGaussNorm.norm_evalAt_le` and
  `TauCeti.PowerSeries.HasGaussNorm.continuous_evalAtHom_comp_inclusion`: evaluation at a point of
  the open disc is bounded by the Gauss norm in an ultrametric algebra, and continuous in any
  complete normed algebra.
* Instances: `NormedRing`, `NormedCommRing`, `IsUltrametricDist`, `NormOneClass` and
  `CompleteSpace` on `PowerSeries.HasGaussNorm.subring R R₀`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter
open scoped Topology

namespace PowerSeries

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {R₀ : ℝ} [hR₀ : Fact (0 < R₀)]
  {f : R⟦X⟧}

variable (R R₀) in
/-- The power series over an ultrametric normed ring whose weighted coefficient norms
`‖aₙ‖ R₀ⁿ` are bounded, at a positive radius `R₀`, form a subring. -/
protected noncomputable def HasGaussNorm.subring : Subring R⟦X⟧ where
  carrier := {f | f.HasGaussNorm norm R₀}
  zero_mem' := ⟨0, by simp [upperBounds]⟩
  one_mem' := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
    (by simpa using isRestricted_C R₀ (1 : R))
  add_mem' hf hg := TauCeti.PowerSeries.hasGaussNorm_add hR₀.out.le hf hg
  mul_mem' hf hg := TauCeti.PowerSeries.hasGaussNorm_mul hR₀.out.le hf hg
  neg_mem' {f} hf := by
    simp only [Set.mem_ofPred_eq, HasGaussNorm, map_neg, norm_neg] at hf ⊢
    exact hf

/-- Membership in the subring of bounded series is boundedness of the weighted coefficient
norms. -/
@[simp]
theorem HasGaussNorm.mem_subring : f ∈ HasGaussNorm.subring R R₀ ↔ f.HasGaussNorm norm R₀ :=
  Iff.rfl

/-- At the radius `1`, the bounded series are the series with bounded coefficients. -/
theorem HasGaussNorm.mem_subring_one_iff :
    f ∈ HasGaussNorm.subring R 1 ↔ BddAbove (Set.range fun n ↦ ‖coeff n f‖) := by
  simp [HasGaussNorm]

/-- Over an ultrametric ring, a series restricted at the radius `R₀` has bounded weighted
coefficient norms there. -/
theorem IsRestricted.subring_le_hasGaussNormSubring :
    IsRestricted.subring R₀ ≤ HasGaussNorm.subring R R₀ :=
  fun _ hf ↦ TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf

/-- A series with bounded weighted coefficient norms at the radius `R₀` lies on the open disc of
radius `R₀`. -/
theorem HasGaussNorm.subring_le_onOpenDiscSubring :
    HasGaussNorm.subring R R₀ ≤ OnOpenDisc.subring R R₀ :=
  fun _ hf ↦ OnOpenDisc.mem_subring.mpr (HasGaussNorm.mem_subring.mp hf).onOpenDisc

end PowerSeries

namespace TauCeti.PowerSeries.HasGaussNorm

open _root_.PowerSeries

section NormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] (R₀ : ℝ) [hR₀ : Fact (0 < R₀)]

/-- The bounded series at a positive radius `R₀` carry their Gauss norm `supₙ ‖aₙ‖ R₀ⁿ`. -/
noncomputable instance instNormedRingSubring : NormedRing (HasGaussNorm.subring R R₀) :=
  RingNorm.toNormedRing
    { toFun f := (f : R⟦X⟧).gaussNorm norm R₀
      map_zero' := gaussNorm_zero norm R₀ norm_zero
      add_le' f g :=
        (gaussNorm_add_le_max norm R₀ (f : R⟦X⟧) (g : R⟦X⟧) hR₀.out.le norm_nonneg
          IsUltrametricDist.isNonarchimedean_norm (HasGaussNorm.mem_subring.mp f.2)
          (HasGaussNorm.mem_subring.mp g.2)).trans
          (max_le_add_of_nonneg (gaussNorm_nonneg norm _ _ norm_nonneg)
            (gaussNorm_nonneg norm _ _ norm_nonneg))
      neg' f := MvPowerSeries.gaussNorm_neg (fun x : R ↦ ‖x‖) _ (fun x ↦ norm_neg x)
        (f : R⟦X⟧)
      mul_le' f g := TauCeti.PowerSeries.gaussNorm_mul_le hR₀.out.le
        (HasGaussNorm.mem_subring.mp f.2) (HasGaussNorm.mem_subring.mp g.2)
      eq_zero_of_map_eq_zero' f h := by
        rwa [gaussNorm_eq_zero_iff norm R₀ _ norm_zero norm_nonneg
          (fun _ ↦ norm_eq_zero.mp) hR₀.out (HasGaussNorm.mem_subring.mp f.2),
          ZeroMemClass.coe_eq_zero] at h }

variable {R₀}

/-- The norm of a bounded series is its Gauss norm. -/
theorem norm_eq_gaussNorm (f : HasGaussNorm.subring R R₀) :
    ‖f‖ = (f : R⟦X⟧).gaussNorm norm R₀ := (rfl)

/-- Each weighted coefficient norm `‖aₙ‖ R₀ⁿ` of a bounded series is bounded by its norm. -/
theorem norm_coeff_mul_pow_le (f : HasGaussNorm.subring R R₀) (n : ℕ) :
    ‖coeff n (f : R⟦X⟧)‖ * R₀ ^ n ≤ ‖f‖ :=
  le_gaussNorm norm R₀ _ (HasGaussNorm.mem_subring.mp f.2) n

/-- The norm of a bounded series is bounded by a nonnegative `r` exactly when every weighted
coefficient norm `‖aₙ‖ R₀ⁿ` is. -/
theorem norm_le_iff {f : HasGaussNorm.subring R R₀} {r : ℝ} (hr : 0 ≤ r) :
    ‖f‖ ≤ r ↔ ∀ n, ‖coeff n (f : R⟦X⟧)‖ * R₀ ^ n ≤ r := by
  refine ⟨fun h n ↦ (norm_coeff_mul_pow_le f n).trans h, fun h ↦ ?_⟩
  rw [norm_eq_gaussNorm, gaussNorm_eq]
  exact Real.iSup_le h hr

/-- Each coefficient is uniformly continuous for the Gauss norm, with bound `(R₀ⁿ)⁻¹`. -/
theorem uniformContinuous_coeff (n : ℕ) :
    UniformContinuous fun f : HasGaussNorm.subring R R₀ ↦ coeff n (f : R⟦X⟧) :=
  AddMonoidHomClass.uniformContinuous_of_bound
    ((coeff n).toAddMonoidHom.comp (HasGaussNorm.subring R R₀).subtype.toAddMonoidHom)
    (R₀ ^ n)⁻¹ fun f ↦ by
      rw [inv_mul_eq_div, le_div_iff₀ (pow_pos hR₀.out n)]
      exact norm_coeff_mul_pow_le f n

variable (R₀)

/-- The Gauss norm on bounded series is ultrametric. -/
instance : IsUltrametricDist (HasGaussNorm.subring R R₀) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g ↦
    gaussNorm_add_le_max norm R₀ (f : R⟦X⟧) (g : R⟦X⟧) hR₀.out.le norm_nonneg
      IsUltrametricDist.isNonarchimedean_norm (HasGaussNorm.mem_subring.mp f.2)
      (HasGaussNorm.mem_subring.mp g.2)

/-- The Gauss norm on bounded series preserves the norm of `1`. -/
instance [NormOneClass R] : NormOneClass (HasGaussNorm.subring R R₀) where
  norm_one := by
    rw [norm_eq_gaussNorm, OneMemClass.coe_one,
      TauCeti.PowerSeries.gaussNorm_eq_of_forall_le (s := 0) fun m ↦ ?_]
    · simp
    · rcases eq_or_ne m 0 with rfl | hm
      · rfl
      · simp [coeff_one, hm]

/-- The Gauss norm on bounded series is complete over a complete coefficient ring. -/
instance [CompleteSpace R] : CompleteSpace (HasGaussNorm.subring R R₀) := by
  refine Metric.complete_of_cauchySeq_tendsto fun F hF ↦ ?_
  choose a ha using fun n ↦ cauchySeq_tendsto_of_complete
    ((uniformContinuous_coeff n).comp_cauchySeq hF)
  -- The Cauchy estimates pass to the coefficientwise limit uniformly in the degree.
  have hunif : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ n, ‖coeff n (F k : R⟦X⟧) - a n‖ * R₀ ^ n ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF ε hε
    refine ⟨N, fun k hk n ↦ le_of_tendsto
      (((tendsto_const_nhds.sub (ha n)).norm).mul_const (R₀ ^ n))
      (eventually_atTop.mpr ⟨N, fun l hl ↦ ?_⟩)⟩
    have h := norm_coeff_mul_pow_le (F k - F l) n
    rw [AddSubgroupClass.coe_sub, map_sub] at h
    exact h.trans ((dist_eq_norm _ _).symm.trans_lt (hN k hk l hl)).le
  -- The limit has bounded weighted coefficient norms.
  have hg : (mk a).HasGaussNorm norm R₀ := by
    obtain ⟨N, hN⟩ := hunif 1 one_pos
    refine ⟨‖F N‖ + 1, Set.forall_mem_range.mpr fun n ↦ ?_⟩
    rw [coeff_mk]
    calc ‖a n‖ * R₀ ^ n
        ≤ ‖coeff n (F N : R⟦X⟧)‖ * R₀ ^ n + ‖coeff n (F N : R⟦X⟧) - a n‖ * R₀ ^ n := by
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub _ _)
            (pow_nonneg hR₀.out.le n)
      _ ≤ ‖F N‖ + 1 := add_le_add (norm_coeff_mul_pow_le (F N) n) (hN N le_rfl n)
  refine ⟨⟨mk a, HasGaussNorm.mem_subring.mpr hg⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [dist_eq_norm]
  refine ((norm_le_iff (half_pos hε).le).mpr fun n ↦ ?_).trans_lt (half_lt_self hε)
  rw [AddSubgroupClass.coe_sub, map_sub, coeff_mk]
  exact hN k hk n

variable {R₀}

/-- Restricted series keep their Gauss norm as bounded series. -/
@[simp]
theorem norm_inclusion_isRestrictedSubring (f : IsRestricted.subring (R := R) R₀) :
    ‖Subring.inclusion IsRestricted.subring_le_hasGaussNormSubring f‖ = ‖f‖ :=
  (rfl)

/-- The inclusion of restricted series into bounded series is an isometry. -/
theorem isometry_inclusion_isRestrictedSubring :
    Isometry (Subring.inclusion
      (IsRestricted.subring_le_hasGaussNormSubring (R := R) (R₀ := R₀))) :=
  AddMonoidHomClass.isometry_of_norm _ norm_inclusion_isRestrictedSubring

-- Supply the positivity witness used by the Gauss-norm instances on each smaller closed disc.
attribute [local instance] TauCeti.PowerSeries.OnOpenDisc.radius_pos

/-- The inclusion of bounded series into series on the open disc of the same radius is uniformly
continuous: the Gauss norm at each smaller radius is bounded by the Gauss norm at `R₀`. -/
theorem uniformContinuous_inclusion_onOpenDiscSubring :
    UniformContinuous (Subring.inclusion
      (HasGaussNorm.subring_le_onOpenDiscSubring (R := R) (R₀ := R₀))) := by
  refine OnOpenDisc.uniformContinuous_iff.mpr fun r ↦ ?_
  refine AddMonoidHomClass.uniformContinuous_of_bound ((OnOpenDisc.restrict r).toAddMonoidHom.comp
    (Subring.inclusion HasGaussNorm.subring_le_onOpenDiscSubring).toAddMonoidHom) 1 fun f ↦ ?_
  rw [one_mul, TauCeti.PowerSeries.norm_eq_gaussNorm, norm_eq_gaussNorm]
  simpa using TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _)
    r.2.1.le r.2.2.le (HasGaussNorm.mem_subring.mp f.2)

/-- The inclusion of bounded series into series on the open disc of the same radius is
continuous. -/
theorem continuous_inclusion_onOpenDiscSubring :
    Continuous (Subring.inclusion
      (HasGaussNorm.subring_le_onOpenDiscSubring (R := R) (R₀ := R₀))) :=
  uniformContinuous_inclusion_onOpenDiscSubring.continuous

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] (R₀ : ℝ) [Fact (0 < R₀)]

/-- Over a commutative coefficient ring, the Gauss norm gives a normed commutative ring. -/
noncomputable instance instNormedCommRingSubring :
    NormedCommRing (HasGaussNorm.subring R R₀) :=
  { instNormedRingSubring R₀ with mul_comm := mul_comm }

variable {R₀} {A : Type*} [NormedRing A] [Algebra R A] [IsBoundedSMul R A] {b : A}

/-- In an ultrametric normed algebra with `‖1‖ = 1`, the value of a bounded series at a point `b`
with `‖b‖ ≤ R₀` is bounded by its Gauss norm. -/
theorem norm_evalAt_le [IsUltrametricDist A] [NormOneClass A] (f : HasGaussNorm.subring R R₀)
    (hb : ‖b‖ ≤ R₀) : ‖(f : R⟦X⟧).evalAt b‖ ≤ ‖f‖ :=
  norm_evalAt_le_gaussNorm (HasGaussNorm.mem_subring.mp f.2) hb

/-- Evaluation of bounded series at a point `b` with `‖b‖ < R₀` of a complete normed algebra,
through the series on the open disc of radius `R₀`, is continuous for the Gauss norm. -/
theorem continuous_evalAtHom_comp_inclusion [CompleteSpace A] (hb : ‖b‖ < R₀) :
    Continuous ((OnOpenDisc.evalAtHom R hb).comp
      (Subring.inclusion HasGaussNorm.subring_le_onOpenDiscSubring)) :=
  (TauCeti.PowerSeries.OnOpenDisc.continuous_evalAtHom hb).comp
    continuous_inclusion_onOpenDiscSubring

end NormedCommRing

end TauCeti.PowerSeries.HasGaussNorm
