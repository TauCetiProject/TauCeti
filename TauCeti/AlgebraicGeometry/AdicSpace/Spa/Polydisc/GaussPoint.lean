/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.PowerSeries.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.OneVariable

import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic
import TauCeti.RingTheory.Huber.Continuous.PowerBounded
import Mathlib.RingTheory.Valuation.RankOne
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Gauss points of the closed unit disc

Let `K` be a nontrivially normed nonarchimedean field and `K⟨T⟩` the one-variable restricted
power series ring, the coordinate ring of the closed unit disc `closedPolydisc 1 K`. For a radius
`0 < r ≤ 1` the *Gauss norm*

```text
|f|_r = sup_n ‖aₙ‖ rⁿ,    f = ∑ aₙ Tⁿ,
```

is a multiplicative ultrametric norm on `K⟨T⟩`, hence a valuation. It is continuous and at most
one on the power-bounded elements, so it defines a point `η_r` of the closed unit disc. At `r = 1`
this is the Gauss point of the disc; for `r < 1` it is the Gauss norm of the disc of radius `r`
about the origin, one of the points of Wedhorn's Example 7.57. The valuation and its
continuity need only a normed commutative ring with multiplicative ultrametric norm in place of
`K`; the bound on power-bounded elements uses nonzero constants of small norm.

When `K` is complete, these points are not classical: the support of `η_r` is trivial, while the
classical point at `a` kills `T - a`. Distinct radii give distinct points by comparing
powers of `T` with constants. The file does not treat Wedhorn's classification of all points of
the disc, nor discs about centres other than the origin.

## Main definitions

* `TauCeti.ValuationSpectrum.closedDiscGaussValuation`: the Gauss norm at radius `r` as a valuation
  on `R⟨T⟩` with values in `ℝ≥0`, for a normed commutative ring `R` with multiplicative ultrametric
  norm.
* `TauCeti.ValuationSpectrum.gaussPoint`: the point `η_r` of the closed unit disc.

## Main results

* `TauCeti.ValuationSpectrum.coe_closedDiscGaussValuation`: the valuation is `sup_n ‖aₙ‖ rⁿ`;
  it takes the value `‖a‖` on the constant `a` and `r` on the variable.
* `TauCeti.ValuationSpectrum.isContinuous_closedDiscGaussValuation` and
  `TauCeti.ValuationSpectrum.closedDiscGaussValuation_le_one_of_isPowerBounded`: the two
  conditions for membership in the closed unit disc.
* `TauCeti.ValuationSpectrum.gaussPoint_vle_iff`: `η_r` compares elements by their Gauss norms.
* `TauCeti.ValuationSpectrum.supp_gaussPoint`: the support of `η_r` is trivial.
* `TauCeti.ValuationSpectrum.gaussPoint_ne_classicalPoint`: for complete `K`, `η_r` is not a
  classical point.
* `TauCeti.ValuationSpectrum.gaussPoint_inj`: distinct radii give distinct points.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1, for the Gauss norm on
  restricted power series.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NNReal

section NormedRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NonarchimedeanRing R] {r : ℝ}

/-- `R⟨T⟩` sits inside the ring of power series restricted at any radius `r` with `|r| ≤ 1`, after
renaming its variable from `Fin 1` to `Unit`. -/
private noncomputable def toRestrictedSubring (hr : |r| ≤ 1) :
    weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight →+*
      PowerSeries.IsRestricted.subring (R := R) r :=
  (Subring.inclusion
    (TauCeti.PowerSeries.isRestrictedSubring_le_of_abs_le (by simpa using hr))).comp
    (restrictedMvPowerSeriesSubringOneEquiv.toRingHom.comp
      (RingEquiv.subringCongr weightedRestrictedSubring_one_weight).toRingHom)

private theorem coe_toRestrictedSubring (hr : |r| ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    (toRestrictedSubring hr f : PowerSeries R) =
      MvPowerSeries.rename finOneEquiv (f : MvPowerSeries (Fin 1) R) := by
  rw [toRestrictedSubring, RingHom.comp_apply, Subring.coe_inclusion]
  simp

private theorem toRestrictedSubring_injective (hr : |r| ≤ 1) :
    Function.Injective (toRestrictedSubring (R := R) hr) := fun f g h ↦ by
  have h' := congrArg Subtype.val h
  rw [coe_toRestrictedSubring, coe_toRestrictedSubring] at h'
  exact Subtype.ext (MvPowerSeries.rename_injective (finOneEquiv : Fin 1 ↪ Unit) h')

private theorem toRestrictedSubring_weightedC (hr : |r| ≤ 1) (a : R) :
    toRestrictedSubring hr
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight a) =
      (⟨PowerSeries.C a, PowerSeries.isRestricted_C r a⟩ :
        PowerSeries.IsRestricted.subring (R := R) r) := by
  apply Subtype.ext
  simpa only [coe_toRestrictedSubring, coe_weightedC, MvPowerSeries.rename_C] using
    (show MvPowerSeries.C a = (PowerSeries.C a : PowerSeries R) from rfl)

private theorem toRestrictedSubring_weightedX (hr : |r| ≤ 1) :
    toRestrictedSubring hr
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0) =
      (⟨(PowerSeries.X : PowerSeries R), by
          rw [PowerSeries.X_eq]
          exact PowerSeries.isRestricted_monomial r 1 (1 : R)⟩ :
        PowerSeries.IsRestricted.subring (R := R) r) := by
  apply Subtype.ext
  simpa only [coe_toRestrictedSubring, coe_weightedX, MvPowerSeries.rename_X] using
    (show MvPowerSeries.X (finOneEquiv (0 : Fin 1)) =
      (PowerSeries.X : PowerSeries R) from rfl)

variable [NormMulClass R] [NormOneClass R]

/-- **The Gauss valuation of radius `r` on `R⟨T⟩`**, for `0 < r ≤ 1`: the valuation
`f ↦ sup_n ‖aₙ‖ rⁿ` with values in `ℝ≥0`, where `aₙ` is the coefficient of `Tⁿ` in `f`. -/
noncomputable def closedDiscGaussValuation (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    Valuation (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R))
      isWeightFamily_one_weight) ℝ≥0 :=
  (TauCeti.PowerSeries.gaussValuation hr₀).comap
    (toRestrictedSubring ((abs_of_pos hr₀).trans_le hr₁))

/-- The Gauss valuation of radius `r` is the supremum of the weighted coefficient norms. -/
theorem coe_closedDiscGaussValuation (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    (closedDiscGaussValuation hr₀ hr₁ f : ℝ) =
      ⨆ n : ℕ,
        ‖MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) R)‖ * r ^ n := by
  simp only [closedDiscGaussValuation, Valuation.comap_apply,
    TauCeti.PowerSeries.coe_gaussValuation, coe_toRestrictedSubring, PowerSeries.gaussNorm_eq,
    PowerSeries.coeff_rename, Subsingleton.elim (finOneEquiv.symm ()) 0]

/-- Every weighted coefficient norm `‖aₙ‖ rⁿ` of `f` is bounded by its Gauss valuation. -/
theorem norm_coeff_mul_pow_le_closedDiscGaussValuation (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight)
    (n : ℕ) :
    ‖MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) R)‖ * r ^ n ≤
      closedDiscGaussValuation hr₀ hr₁ f := by
  simpa only [closedDiscGaussValuation, Valuation.comap_apply,
    TauCeti.PowerSeries.coe_gaussValuation, coe_toRestrictedSubring,
    PowerSeries.coeff_rename, Subsingleton.elim (finOneEquiv.symm ()) 0] using
    (PowerSeries.le_gaussNorm norm r _
      (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
        (toRestrictedSubring ((abs_of_pos hr₀).trans_le hr₁) f).2) n)

/-- A common bound on the coefficient norms of `f` bounds its Gauss valuation, since `r ≤ 1`. -/
theorem closedDiscGaussValuation_le_of_forall_norm_coeff_le (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight}
    {ε : ℝ} (h : ∀ ν, ‖MvPowerSeries.coeff ν (f : MvPowerSeries (Fin 1) R)‖ ≤ ε) :
    (closedDiscGaussValuation hr₀ hr₁ f : ℝ) ≤ ε := by
  rw [coe_closedDiscGaussValuation]
  exact ciSup_le fun n ↦
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hr₀.le hr₁)).trans (h _)

/-- The Gauss valuation of a constant is its norm. -/
@[simp]
theorem closedDiscGaussValuation_weightedC (hr₀ : 0 < r) (hr₁ : r ≤ 1) (a : R) :
    closedDiscGaussValuation hr₀ hr₁
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight a) = ‖a‖₊ := by
  simp [closedDiscGaussValuation, toRestrictedSubring_weightedC]

/-- The Gauss valuation of radius `r` takes the value `r` on the variable. -/
@[simp]
theorem coe_closedDiscGaussValuation_weightedX (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (closedDiscGaussValuation hr₀ hr₁
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0) : ℝ) = r := by
  simp [closedDiscGaussValuation, toRestrictedSubring_weightedX,
    TauCeti.PowerSeries.gaussValuation_X]
  rfl

/-- The Gauss valuation vanishes only at zero. -/
@[simp]
theorem closedDiscGaussValuation_eq_zero_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight} :
    closedDiscGaussValuation hr₀ hr₁ f = 0 ↔ f = 0 := by
  rw [closedDiscGaussValuation, Valuation.comap_apply,
    TauCeti.PowerSeries.gaussValuation_eq_zero_iff, map_eq_zero_iff _
      (toRestrictedSubring_injective _)]

/-- **The Gauss valuation is continuous** for `0 < r ≤ 1`. -/
theorem isContinuous_closedDiscGaussValuation (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (closedDiscGaussValuation (R := R) hr₀ hr₁).IsContinuous := by
  refine Valuation.isContinuous_of_forall_isOpen_lt fun γ ↦ ?_
  rcases eq_or_ne γ 0 with rfl | hγ
  · simp
  have hγ₀ : (0 : ℝ) < γ := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _
    (Metric.ball_mem_nhds (0 : R) (half_pos hγ₀))
  refine AddSubgroup.isOpen_mono (H₂ := (closedDiscGaussValuation hr₀ hr₁).ltAddSubgroup
    (Units.mk0 γ hγ)) (fun f hf ↦ ?_) (isOpen_weightedNhd isWeightFamily_one_weight U.isOpen)
  have hle := closedDiscGaussValuation_le_of_forall_norm_coeff_le hr₀ hr₁ (f := f) fun ν ↦
    (mem_ball_zero_iff.mp (hU (by simpa using mem_weightedNhd.mp hf ν))).le
  exact NNReal.coe_lt_coe.mp (hle.trans_lt (half_lt_self hγ₀))

end NormedRing

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]
  {r : ℝ}

/-- **The Gauss valuation is at most one on power-bounded elements** of `K⟨T⟩`. -/
theorem closedDiscGaussValuation_le_one_of_isPowerBounded (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : IsPowerBounded f) : closedDiscGaussValuation hr₀ hr₁ f ≤ 1 := by
  let v := closedDiscGaussValuation (R := K) hr₀ hr₁
  obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt K one_pos
  let _ : MulArchimedean v.ValueGroup₀ :=
    MulArchimedean.comap MonoidWithZeroHom.ValueGroup₀.embedding.toMonoidHom
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  have hcNil : IsTopologicallyNilpotent c :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₁
  have hnil : IsTopologicallyNilpotent
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight c) :=
    hcNil.map (continuous_weightedC isWeightFamily_one_weight)
  exact (isContinuous_closedDiscGaussValuation hr₀ hr₁ : v.IsContinuous).le_one_of_isPowerBounded
    hnil
    (by rw [closedDiscGaussValuation_weightedC]
        exact nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp hc₀)) hf

/-- **The Gauss point `η_r` of the closed unit disc**, for `0 < r ≤ 1`: the point of
`Spa (K⟨T⟩, K⟨T⟩°)` given by the Gauss valuation `f ↦ sup_n ‖aₙ‖ rⁿ`. At `r = 1` it is the Gauss
point of the disc. -/
noncomputable def gaussPoint (hr₀ : 0 < r) (hr₁ : r ≤ 1) : closedPolydisc 1 K :=
  ⟨ofValuation (closedDiscGaussValuation hr₀ hr₁), (mem_closedPolydisc_iff _ _ _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr (isContinuous_closedDiscGaussValuation hr₀ hr₁),
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact closedDiscGaussValuation_le_one_of_isPowerBounded hr₀ hr₁
          (mem_powerBoundedSubring.mp hf)⟩⟩

/-- The underlying point in `Spv K⟨T⟩` is defined by the Gauss valuation. -/
theorem gaussPoint_val (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (gaussPoint (K := K) hr₀ hr₁).1 = ofValuation (closedDiscGaussValuation hr₀ hr₁) :=
  (rfl)

/-- The Gauss point `η_r` compares two series by their Gauss valuations of radius `r`. -/
@[simp]
theorem gaussPoint_vle_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (gaussPoint hr₀ hr₁).1.toValuativeRel.vle f g ↔
      closedDiscGaussValuation hr₀ hr₁ f ≤ closedDiscGaussValuation hr₀ hr₁ g := by
  rw [gaussPoint_val, vle_ofValuation]

/-- A Gauss point `η_r` kills only the zero series. -/
theorem gaussPoint_vle_zero_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight} :
    (gaussPoint hr₀ hr₁).1.toValuativeRel.vle f 0 ↔ f = 0 := by
  rw [gaussPoint_vle_iff, map_zero, nonpos_iff_eq_zero, closedDiscGaussValuation_eq_zero_iff]

/-- **The support of a Gauss point is trivial.** -/
@[simp]
theorem supp_gaussPoint (hr₀ : 0 < r) (hr₁ : r ≤ 1) : (gaussPoint (K := K) hr₀ hr₁).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by rw [mem_supp_iff, gaussPoint_vle_zero_iff, Ideal.mem_bot]

/-- **Gauss points over a complete field are not classical points.** -/
theorem gaussPoint_ne_classicalPoint [CompleteSpace K] (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (x : spa (powerBoundedSubring K)) (a : Fin 1 → K) (ha : ∀ i, IsPowerBounded (a i)) :
    gaussPoint hr₀ hr₁ ≠ classicalPoint x a ha := by
  intro h
  have hvle := (classicalPoint_vle x a ha
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 -
      weightedC _ isWeightFamily_one_weight (a 0)) 0).mpr (by simp)
  rw [← h, gaussPoint_vle_zero_iff, sub_eq_zero] at hvle
  -- the variable and a constant differ in their coefficient of `T`
  have hcoeff := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) (congrArg Subtype.val hvle)
  simp [MvPowerSeries.coeff_X, MvPowerSeries.coeff_C] at hcoeff

/-- **Distinct radii `0 < r, s ≤ 1` give distinct Gauss points.** -/
theorem gaussPoint_inj {s : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    gaussPoint (K := K) hr₀ hr₁ = gaussPoint hs₀ hs₁ ↔ r = s := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  by_contra hne
  wlog hlt : r < s generalizing r s
  · exact this hs₀ hs₁ hr₀ hr₁ h.symm (Ne.symm hne) ((not_lt.mp hlt).lt_of_ne (Ne.symm hne))
  -- choose `m` with `‖k‖ ≤ (s / r)ᵐ` and `c` in the shell `sᵐ / ‖k‖ ≤ ‖c‖ < sᵐ`
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm K
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖k‖ ((one_lt_div hr₀).mpr hlt)
  obtain ⟨c, -, hcs, hcr, -⟩ := rescale_to_shell hk (pow_pos hs₀ m) (one_ne_zero' K)
  rw [smul_eq_mul, mul_one] at hcs hcr
  have hrm : r ^ m ≤ ‖c‖ := by
    refine le_trans ?_ hcr
    rw [le_div_iff₀ (one_pos.trans hk), ← le_div_iff₀' (pow_pos hr₀ m), ← div_pow]
    exact hm.le
  have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 ^ m)
    (weightedC _ isWeightFamily_one_weight c)) h
  simp only [gaussPoint_vle_iff, map_pow, closedDiscGaussValuation_weightedC, eq_iff_iff,
    ← NNReal.coe_le_coe, NNReal.coe_pow, coe_closedDiscGaussValuation_weightedX,
    coe_nnnorm] at key
  exact (key.mp hrm).not_gt hcs

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
