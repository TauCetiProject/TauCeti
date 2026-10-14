/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.PowerSeries.GaussNorm
public import TauCeti.RingTheory.Huber.Restricted.OneVariable

import TauCeti.Analysis.Normed.Field.Basic
import TauCeti.AlgebraicGeometry.AdicSpace.Cont.Basic
import TauCeti.RingTheory.Huber.Continuous.PowerBounded
import Mathlib.RingTheory.Valuation.RankOne
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
the disc; the Gauss points of discs about other centres are `TauCeti.ValuationSpectrum.discPoint`.

Next to each Gauss point `η_r` sit the refined points `η_{r⁻}` and `η_{r⁺}`, the Gauss norms at a
radius infinitesimally below and above `r`. They are defined by the valuations
`f ↦ (|f|_r, -s)` and `f ↦ (|f|_r, s)` with values in `ℝ≥0ˣ ×ₗ ℤ`, where `s` is the first,
respectively the last, degree in which `f` attains `|f|_r`
(`TauCeti.PowerSeries.gaussValuationBelow` and `TauCeti.PowerSeries.gaussValuationAbove`). They
are continuous because they refine `η_r`, and `η_{r⁻}` lies in the closed disc for `0 < r ≤ 1`,
`η_{r⁺}` for `0 < r < 1`; at `r = 1` the valuation just above `r` gives `T` a value larger than
`1`. When `r` is the norm of an element of `K`, the three points `η_r`, `η_{r⁻}` and `η_{r⁺}` are
pairwise distinct, and both `η_{r⁻}` and `η_{r⁺}` are specializations of `η_r`. When `K` is
algebraically closed and `r ∈ |K^×|`, these are the points of type (5) centred at the origin in
the description of the disc in Wedhorn's Example 7.57; for radii outside `|K^×|` the refined
valuations need not differ from `η_r`.

## Main definitions

* `TauCeti.ValuationSpectrum.closedDiscGaussValuation`: the Gauss norm at radius `r` as a valuation
  on `R⟨T⟩` with values in `ℝ≥0`, for a normed commutative ring `R` with multiplicative ultrametric
  norm.
* `TauCeti.ValuationSpectrum.gaussPoint`: the point `η_r` of the closed unit disc.
* `TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove` and
  `TauCeti.ValuationSpectrum.closedDiscGaussValuationBelow`: the Gauss valuations just above and
  just below `r` on `R⟨T⟩`, with values in `ℝ≥0ˣ ×ₗ ℤ`.
* `TauCeti.ValuationSpectrum.gaussPointAbove` and `TauCeti.ValuationSpectrum.gaussPointBelow`:
  the points `η_{r⁺}` and `η_{r⁻}` of the closed unit disc.

## Main results

* `TauCeti.ValuationSpectrum.coe_closedDiscGaussValuation`: the valuation is `sup_n ‖aₙ‖ rⁿ`;
  it takes the value `‖a‖` on the constant `a`, `r` on the variable, and `max r ‖a‖` on `T - a`
  (`TauCeti.ValuationSpectrum.coe_closedDiscGaussValuation_weightedX_sub_weightedC`).
* `TauCeti.ValuationSpectrum.closedDiscGaussValuation_le_closedDiscGaussValuation_of_le` and
  `TauCeti.ValuationSpectrum.tendsto_closedDiscGaussValuation`: the valuation is monotone and right
  continuous in the radius.
* `TauCeti.ValuationSpectrum.isContinuous_closedDiscGaussValuation` and
  `TauCeti.ValuationSpectrum.closedDiscGaussValuation_le_one_of_isPowerBounded`: the two
  conditions for membership in the closed unit disc.
* `TauCeti.ValuationSpectrum.gaussPoint_vle_iff`: `η_r` compares elements by their Gauss norms.
* `TauCeti.ValuationSpectrum.supp_gaussPoint`: the support of `η_r` is trivial.
* `TauCeti.ValuationSpectrum.gaussPoint_ne_classicalPoint`: for complete `K`, `η_r` is not a
  classical point.
* `TauCeti.ValuationSpectrum.gaussPoint_inj`: distinct radii give distinct points.
* `TauCeti.ValuationSpectrum.isContinuous_closedDiscGaussValuationAbove`,
  `TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove_le_one_of_isPowerBounded` and their
  `Below` analogues: the conditions for membership in the closed unit disc.
* `TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove_weightedX_le_iff` and
  `TauCeti.ValuationSpectrum.closedDiscGaussValuationBelow_weightedC_le_iff`: just above `r` the
  variable `T` is at most a constant `c` exactly when `r < ‖c‖`, and just below `r` a constant `c`
  is at most `T` exactly when `‖c‖ < r`. The complementary comparisons are
  `TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove_weightedC_le_iff` (`c ≤ T` exactly when
  `‖c‖ ≤ r`) and `TauCeti.ValuationSpectrum.closedDiscGaussValuationBelow_weightedX_le_iff`
  (`T ≤ c` exactly when `r ≤ ‖c‖`). Just above `r`, constants compare by their norms
  (`TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove_weightedC_le_weightedC_iff`).
* `TauCeti.ValuationSpectrum.gaussPointAbove_ne_gaussPoint`,
  `TauCeti.ValuationSpectrum.gaussPointBelow_ne_gaussPoint` and
  `TauCeti.ValuationSpectrum.gaussPointBelow_ne_gaussPointAbove`: for `r` the norm of an element
  of `K`, the three points at radius `r` are pairwise distinct.
* `TauCeti.ValuationSpectrum.gaussPointAbove_inj` and
  `TauCeti.ValuationSpectrum.gaussPointBelow_inj`: distinct radii give distinct points `η_{r⁺}`,
  respectively `η_{r⁻}`.
* `TauCeti.ValuationSpectrum.gaussPoint_specializes_of_lt`: a point of `Spv K⟨T⟩` whose valuation
  refines the Gauss norm of radius `r` lies in the closure of `η_r`.
* `TauCeti.ValuationSpectrum.gaussPoint_specializes_gaussPointAbove` and
  `TauCeti.ValuationSpectrum.gaussPoint_specializes_gaussPointBelow`: `η_{r⁺}` and `η_{r⁻}` lie in
  the closure of `η_r`.
* `TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove_weightedC_mul_weightedX_pow_le` and
  its `Below` analogue: every monomial `aₙ Tⁿ` of a series is at most the series, just above and
  just below `r`.
* `TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove_weightedX_add_weightedC` and
  `TauCeti.ValuationSpectrum.closedDiscGaussValuationBelow_weightedX_add_weightedC`: the shifted
  variable `T + c` has the value of `T` just above `r` when `‖c‖ ≤ r`, and just below `r` when
  `‖c‖ < r`. With the monomial bounds these make the two valuations invariant under translation
  (`TauCeti.ValuationSpectrum.closedDiscGaussValuationAbove_taylorHom`).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), Example 2.20, for the points of
  type (5).
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
    weightedRestrictedSubringOneEquiv.toRingHom

private theorem coe_toRestrictedSubring (hr : |r| ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    (toRestrictedSubring hr f : PowerSeries R) =
      MvPowerSeries.rename finOneEquiv (f : MvPowerSeries (Fin 1) R) := by
  rw [toRestrictedSubring, RingHom.comp_apply, Subring.coe_inclusion]
  simp [coe_weightedRestrictedSubringOneEquiv]

private theorem toRestrictedSubring_injective (hr : |r| ≤ 1) :
    Function.Injective (toRestrictedSubring (R := R) hr) := by
  rw [toRestrictedSubring, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (Subring.inclusion_injective _).comp weightedRestrictedSubringOneEquiv.injective

private theorem toRestrictedSubring_weightedC (hr : |r| ≤ 1) (a : R) :
    toRestrictedSubring hr
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight a) =
      (⟨PowerSeries.C a, PowerSeries.isRestricted_C r a⟩ :
        PowerSeries.IsRestricted.subring (R := R) r) := by
  apply Subtype.ext
  rw [toRestrictedSubring, RingHom.comp_apply, Subring.coe_inclusion]
  exact coe_weightedRestrictedSubringOneEquiv_weightedC a

private theorem toRestrictedSubring_weightedX (hr : |r| ≤ 1) :
    toRestrictedSubring hr
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0) =
      (⟨(PowerSeries.X : PowerSeries R), by
          rw [PowerSeries.X_eq]
          exact PowerSeries.isRestricted_monomial r 1 (1 : R)⟩ :
        PowerSeries.IsRestricted.subring (R := R) r) := by
  apply Subtype.ext
  rw [toRestrictedSubring, RingHom.comp_apply, Subring.coe_inclusion]
  exact coe_weightedRestrictedSubringOneEquiv_weightedX

/-- The weighted coefficients of `f ∈ R⟨T⟩` are its coefficients as a restricted series. -/
private theorem coeff_toRestrictedSubring (hr : |r| ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight)
    (n : ℕ) :
    (toRestrictedSubring hr f : PowerSeries R).coeff n =
      MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) R) := by
  simp only [coe_toRestrictedSubring, PowerSeries.coeff_rename,
    Subsingleton.elim (finOneEquiv.symm ()) 0]

private theorem coe_toRestrictedSubring_ne_zero (hr : |r| ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight}
    (hf : f ≠ 0) : (toRestrictedSubring hr f : PowerSeries R) ≠ 0 := by
  rw [Ne, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ (toRestrictedSubring_injective hr)]
  exact hf

private theorem coe_toRestrictedSubring_one (hr : |r| ≤ 1) :
    ((toRestrictedSubring hr 1 :
      PowerSeries.IsRestricted.subring (R := R) r) : PowerSeries R) = PowerSeries.monomial 0 1 := by
  rw [map_one, OneMemClass.coe_one, PowerSeries.monomial_zero_eq_C_apply, map_one]

private theorem coe_toRestrictedSubring_weightedX (hr : |r| ≤ 1) :
    ((toRestrictedSubring hr
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0) :
      PowerSeries.IsRestricted.subring (R := R) r) : PowerSeries R) =
      PowerSeries.monomial 1 1 := by
  rw [toRestrictedSubring_weightedX]
  exact PowerSeries.X_eq

private theorem coe_toRestrictedSubring_weightedC (hr : |r| ≤ 1) (a : R) :
    ((toRestrictedSubring hr (weightedC (fun _ : Fin 1 ↦ ({1} : Set R))
      isWeightFamily_one_weight a) : PowerSeries.IsRestricted.subring (R := R) r) :
      PowerSeries R) = PowerSeries.monomial 0 a := by
  rw [toRestrictedSubring_weightedC]
  exact (PowerSeries.monomial_zero_eq_C_apply a).symm

private theorem coe_toRestrictedSubring_weightedC_mul_weightedX_pow (hr : |r| ≤ 1) (a : R)
    (n : ℕ) :
    ((toRestrictedSubring hr
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight a *
        weightedX _ isWeightFamily_one_weight 0 ^ n) :
      PowerSeries.IsRestricted.subring (R := R) r) : PowerSeries R) =
      PowerSeries.monomial n a := by
  rw [map_mul, map_pow, Subring.coe_mul, Subring.coe_pow, coe_toRestrictedSubring_weightedC,
    coe_toRestrictedSubring_weightedX, PowerSeries.monomial_pow, PowerSeries.monomial_mul_monomial]
  simp

private theorem coe_toRestrictedSubring_weightedX_add_weightedC (hr : |r| ≤ 1) (c : R) :
    ((toRestrictedSubring hr
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0 +
        weightedC _ isWeightFamily_one_weight c) :
      PowerSeries.IsRestricted.subring (R := R) r) : PowerSeries R) =
      PowerSeries.X - PowerSeries.C (-c) := by
  rw [map_add, Subring.coe_add, toRestrictedSubring_weightedX, toRestrictedSubring_weightedC,
    map_neg, sub_neg_eq_add]

private theorem coe_toRestrictedSubring_weightedX' (hr : |r| ≤ 1) :
    ((toRestrictedSubring hr
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0) :
      PowerSeries.IsRestricted.subring (R := R) r) : PowerSeries R) =
      PowerSeries.X - PowerSeries.C 0 := by
  rw [toRestrictedSubring_weightedX, map_zero, sub_zero]

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

/-- **The Gauss valuation is monotone in the radius**: for `0 < r ≤ s ≤ 1`, the Gauss norm of
radius `r` is at most the Gauss norm of radius `s`. -/
theorem closedDiscGaussValuation_le_closedDiscGaussValuation_of_le {s : ℝ} (hr₀ : 0 < r)
    (hr₁ : r ≤ 1) (hs₁ : s ≤ 1) (hrs : r ≤ s)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    closedDiscGaussValuation hr₀ hr₁ f ≤ closedDiscGaussValuation (hr₀.trans_le hrs) hs₁ f := by
  have h := TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _) hr₀.le hrs
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
      (toRestrictedSubring ((abs_of_pos (hr₀.trans_le hrs)).trans_le hs₁) f).2)
  rw [← NNReal.coe_le_coe]
  simpa only [closedDiscGaussValuation, Valuation.comap_apply,
    TauCeti.PowerSeries.coe_gaussValuation, coe_toRestrictedSubring] using h

/-- **The Gauss valuation is right continuous in the radius**: if radii `tₙ ∈ [r, 1]` tend to
`r > 0`, the Gauss norms of radius `tₙ` tend to the Gauss norm of radius `r`. -/
theorem tendsto_closedDiscGaussValuation {t : ℕ → ℝ} (hr₀ : 0 < r) (hrt : ∀ n, r ≤ t n)
    (ht₁ : ∀ n, t n ≤ 1) (ht : Filter.Tendsto t Filter.atTop (nhds r))
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight) :
    Filter.Tendsto (fun n ↦ closedDiscGaussValuation (hr₀.trans_le (hrt n)) (ht₁ n) f)
      Filter.atTop (nhds (closedDiscGaussValuation hr₀ ((hrt 0).trans (ht₁ 0)) f)) := by
  have h := TauCeti.PowerSeries.tendsto_gaussNorm_of_isRestricted hr₀ hrt ht₁ ht
    (toRestrictedSubring (r := 1) (by simp) f).2
  rw [← NNReal.tendsto_coe]
  simpa only [closedDiscGaussValuation, Valuation.comap_apply,
    TauCeti.PowerSeries.coe_gaussValuation, coe_toRestrictedSubring] using h

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

/-- The Gauss valuation of radius `r` takes the value `max r ‖a‖` on `T - a`: the coefficients
`-a` and `1` of `T - a` give the lower bounds `‖a‖` and `r`, and the ultrametric inequality the
upper bound. -/
@[simp]
theorem coe_closedDiscGaussValuation_weightedX_sub_weightedC (hr₀ : 0 < r) (hr₁ : r ≤ 1) (a : R) :
    (closedDiscGaussValuation hr₀ hr₁
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0 -
        weightedC _ isWeightFamily_one_weight a) : ℝ) = max r ‖a‖ := by
  have h n := norm_coeff_mul_pow_le_closedDiscGaussValuation hr₀ hr₁
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0 -
      weightedC _ isWeightFamily_one_weight a) n
  simp only [AddSubgroupClass.coe_sub, coe_weightedX, coe_weightedC] at h
  refine le_antisymm ?_ (max_le ?_ ?_)
  · refine (NNReal.coe_le_coe.mpr (Valuation.map_sub _ _ _)).trans ?_
    rw [NNReal.coe_max, coe_closedDiscGaussValuation_weightedX, closedDiscGaussValuation_weightedC,
      coe_nnnorm]
  · simpa [MvPowerSeries.coeff_X, MvPowerSeries.coeff_C] using h 1
  · simpa using h 0

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

/-! ### The Gauss valuations just above and just below a radius -/

/-- **The Gauss valuation just above the radius `r` on `R⟨T⟩`**, for `0 < r ≤ 1`: the valuation
`f ↦ (|f|_r, s)` with values in `ℝ≥0ˣ ×ₗ ℤ`, where `s` is the last degree in which `f` attains its
Gauss norm `|f|_r` (`TauCeti.PowerSeries.gaussValuationAbove`). -/
noncomputable def closedDiscGaussValuationAbove (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    Valuation (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R))
      isWeightFamily_one_weight) (WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ)) :=
  (TauCeti.PowerSeries.gaussValuationAbove hr₀).comap
    (toRestrictedSubring ((abs_of_pos hr₀).trans_le hr₁))

/-- **The Gauss valuation just below the radius `r` on `R⟨T⟩`**, for `0 < r ≤ 1`: the valuation
`f ↦ (|f|_r, -s)` with values in `ℝ≥0ˣ ×ₗ ℤ`, where `s` is the first degree in which `f` attains
its Gauss norm `|f|_r` (`TauCeti.PowerSeries.gaussValuationBelow`). -/
noncomputable def closedDiscGaussValuationBelow (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    Valuation (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R))
      isWeightFamily_one_weight) (WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ)) :=
  (TauCeti.PowerSeries.gaussValuationBelow hr₀).comap
    (toRestrictedSubring ((abs_of_pos hr₀).trans_le hr₁))

/-- The Gauss valuation just above `r` vanishes only at zero. -/
@[simp]
theorem closedDiscGaussValuationAbove_eq_zero_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight} :
    closedDiscGaussValuationAbove hr₀ hr₁ f = 0 ↔ f = 0 := by
  rw [closedDiscGaussValuationAbove, Valuation.comap_apply,
    TauCeti.PowerSeries.gaussValuationAbove_eq_zero_iff, map_eq_zero_iff _
      (toRestrictedSubring_injective _)]

/-- The Gauss valuation just below `r` vanishes only at zero. -/
@[simp]
theorem closedDiscGaussValuationBelow_eq_zero_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight} :
    closedDiscGaussValuationBelow hr₀ hr₁ f = 0 ↔ f = 0 := by
  rw [closedDiscGaussValuationBelow, Valuation.comap_apply,
    TauCeti.PowerSeries.gaussValuationBelow_eq_zero_iff, map_eq_zero_iff _
      (toRestrictedSubring_injective _)]

/-- A strictly smaller Gauss norm of radius `r` gives a strictly smaller value just above `r`. -/
theorem closedDiscGaussValuationAbove_lt_of_lt (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight}
    (h : closedDiscGaussValuation hr₀ hr₁ f < closedDiscGaussValuation hr₀ hr₁ g) :
    closedDiscGaussValuationAbove hr₀ hr₁ f < closedDiscGaussValuationAbove hr₀ hr₁ g :=
  TauCeti.PowerSeries.gaussValuationAbove_lt_of_lt hr₀ h

/-- A strictly smaller Gauss norm of radius `r` gives a strictly smaller value just below `r`. -/
theorem closedDiscGaussValuationBelow_lt_of_lt (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight}
    (h : closedDiscGaussValuation hr₀ hr₁ f < closedDiscGaussValuation hr₀ hr₁ g) :
    closedDiscGaussValuationBelow hr₀ hr₁ f < closedDiscGaussValuationBelow hr₀ hr₁ g :=
  TauCeti.PowerSeries.gaussValuationBelow_lt_of_lt hr₀ h

/-- **The Gauss valuation just above `r` is continuous**, since it refines the Gauss valuation of
radius `r`. -/
theorem isContinuous_closedDiscGaussValuationAbove (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (closedDiscGaussValuationAbove (R := R) hr₀ hr₁).IsContinuous :=
  (isContinuous_closedDiscGaussValuation hr₀ hr₁).of_lt_imp_lt
    (fun _ hb ↦ by simpa using hb) fun _ _ ↦ closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁

/-- **The Gauss valuation just below `r` is continuous**, since it refines the Gauss valuation of
radius `r`. -/
theorem isContinuous_closedDiscGaussValuationBelow (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (closedDiscGaussValuationBelow (R := R) hr₀ hr₁).IsContinuous :=
  (isContinuous_closedDiscGaussValuation hr₀ hr₁).of_lt_imp_lt
    (fun _ hb ↦ by simpa using hb) fun _ _ ↦ closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁

/-! ### Monomials and the shifted variable -/

/-- **Every monomial of `f` is at most `f` just above `r`.** A monomial `aₙ Tⁿ` of `f` has Gauss
norm at most that of `f`, and if the two agree then `n` is at most the distinguished degree of
`f`, the last degree in which `f` attains its Gauss norm. -/
theorem closedDiscGaussValuationAbove_weightedC_mul_weightedX_pow_le (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight)
    (n : ℕ) :
    closedDiscGaussValuationAbove hr₀ hr₁
        (weightedC _ isWeightFamily_one_weight
            (MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) R)) *
          weightedX _ isWeightFamily_one_weight 0 ^ n) ≤
      closedDiscGaussValuationAbove hr₀ hr₁ f := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁
  -- the monomial `aₙ Tⁿ` of `f` is the monomial of degree `n` of the restricted series `f`
  rw [closedDiscGaussValuationAbove, Valuation.comap_apply, Valuation.comap_apply]
  refine (congrArg (TauCeti.PowerSeries.gaussValuationAbove hr₀) (Subtype.ext ?_)).trans_le
    (TauCeti.PowerSeries.gaussValuationAbove_monomial_coeff_le hr₀
      (f := toRestrictedSubring hr f) n)
  rw [coe_toRestrictedSubring_weightedC_mul_weightedX_pow, coeff_toRestrictedSubring]

/-- **Every monomial of `f` is at most `f` just below `r`.** A monomial `aₙ Tⁿ` of `f` has Gauss
norm at most that of `f`, and if the two agree then `n` is at least the lowest dominant degree of
`f`, the first degree in which `f` attains its Gauss norm. -/
theorem closedDiscGaussValuationBelow_weightedC_mul_weightedX_pow_le (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight)
    (n : ℕ) :
    closedDiscGaussValuationBelow hr₀ hr₁
        (weightedC _ isWeightFamily_one_weight
            (MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) R)) *
          weightedX _ isWeightFamily_one_weight 0 ^ n) ≤
      closedDiscGaussValuationBelow hr₀ hr₁ f := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁
  -- the monomial `aₙ Tⁿ` of `f` is the monomial of degree `n` of the restricted series `f`
  rw [closedDiscGaussValuationBelow, Valuation.comap_apply, Valuation.comap_apply]
  refine (congrArg (TauCeti.PowerSeries.gaussValuationBelow hr₀) (Subtype.ext ?_)).trans_le
    (TauCeti.PowerSeries.gaussValuationBelow_monomial_coeff_le hr₀
      (f := toRestrictedSubring hr f) n)
  rw [coe_toRestrictedSubring_weightedC_mul_weightedX_pow, coeff_toRestrictedSubring]

/-- **Just above `r`, the shifted variable `T + c` with `‖c‖ ≤ r` has the value of `T`**: both
have Gauss norm `r`, attained last in degree `1`. -/
theorem closedDiscGaussValuationAbove_weightedX_add_weightedC (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {c : R} (hc : ‖c‖ ≤ r) :
    closedDiscGaussValuationAbove hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0 +
          weightedC _ isWeightFamily_one_weight c) =
      closedDiscGaussValuationAbove hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0) := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁
  have h₁ := TauCeti.PowerSeries.isDistinguished_X_sub_C hr₀ (b := -c) (by rwa [norm_neg])
  have h₂ := TauCeti.PowerSeries.isDistinguished_X_sub_C hr₀ (b := (0 : R)) (by simpa using hr₀.le)
  rw [← coe_toRestrictedSubring_weightedX_add_weightedC hr] at h₁
  rw [← coe_toRestrictedSubring_weightedX' hr] at h₂
  -- both Gauss norms are the norm `r` of the leading coefficient in degree `1`
  have heq : TauCeti.PowerSeries.gaussValuation hr₀ (toRestrictedSubring hr
      (weightedX _ isWeightFamily_one_weight 0 + weightedC _ isWeightFamily_one_weight c)) =
      TauCeti.PowerSeries.gaussValuation hr₀ (toRestrictedSubring hr
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0)) := by
    rw [← NNReal.coe_inj, TauCeti.PowerSeries.coe_gaussValuation,
      TauCeti.PowerSeries.coe_gaussValuation, ← h₁.norm_coeff_mul_pow_eq,
      ← h₂.norm_coeff_mul_pow_eq, coe_toRestrictedSubring_weightedX_add_weightedC,
      coe_toRestrictedSubring_weightedX']
    simp
  simp only [closedDiscGaussValuationAbove, Valuation.comap_apply]
  exact le_antisymm
    ((TauCeti.PowerSeries.gaussValuationAbove_le_iff hr₀ h₁ h₂).mpr (Or.inr ⟨heq, le_rfl⟩))
    ((TauCeti.PowerSeries.gaussValuationAbove_le_iff hr₀ h₂ h₁).mpr (Or.inr ⟨heq.symm, le_rfl⟩))

/-- **Just below `r`, the shifted variable `T + c` with `‖c‖ < r` has the value of `T`**: both
have Gauss norm `r`, attained first in degree `1`. -/
theorem closedDiscGaussValuationBelow_weightedX_add_weightedC (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {c : R} (hc : ‖c‖ < r) :
    closedDiscGaussValuationBelow hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0 +
          weightedC _ isWeightFamily_one_weight c) =
      closedDiscGaussValuationBelow hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0) := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁
  have h₁ := TauCeti.PowerSeries.isLowestDominant_X_sub_C hr₀ (b := -c) (by rwa [norm_neg])
  have h₂ := TauCeti.PowerSeries.isLowestDominant_X_sub_C hr₀ (b := (0 : R)) (by simpa using hr₀)
  rw [← coe_toRestrictedSubring_weightedX_add_weightedC hr] at h₁
  rw [← coe_toRestrictedSubring_weightedX' hr] at h₂
  -- both Gauss norms are the norm `r` of the leading coefficient in degree `1`
  have heq : TauCeti.PowerSeries.gaussValuation hr₀ (toRestrictedSubring hr
      (weightedX _ isWeightFamily_one_weight 0 + weightedC _ isWeightFamily_one_weight c)) =
      TauCeti.PowerSeries.gaussValuation hr₀ (toRestrictedSubring hr
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set R)) isWeightFamily_one_weight 0)) := by
    rw [← NNReal.coe_inj, TauCeti.PowerSeries.coe_gaussValuation,
      TauCeti.PowerSeries.coe_gaussValuation, ← h₁.norm_coeff_mul_pow_eq,
      ← h₂.norm_coeff_mul_pow_eq, coe_toRestrictedSubring_weightedX_add_weightedC,
      coe_toRestrictedSubring_weightedX']
    simp
  simp only [closedDiscGaussValuationBelow, Valuation.comap_apply]
  exact le_antisymm
    ((TauCeti.PowerSeries.gaussValuationBelow_le_iff hr₀ h₁ h₂).mpr (Or.inr ⟨heq, le_rfl⟩))
    ((TauCeti.PowerSeries.gaussValuationBelow_le_iff hr₀ h₂ h₁).mpr (Or.inr ⟨heq.symm, le_rfl⟩))

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
    gaussPoint hr₀ hr₁ ≠ classicalPoint x a ha :=
  ne_classicalPoint_of_supp_eq_bot _ (supp_gaussPoint hr₀ hr₁) x a ha

/-- **Distinct radii `0 < r, s ≤ 1` give distinct Gauss points.** -/
theorem gaussPoint_inj {s : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    gaussPoint (K := K) hr₀ hr₁ = gaussPoint hs₀ hs₁ ↔ r = s := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  by_contra hne
  wlog hlt : r < s generalizing r s
  · exact this hs₀ hs₁ hr₀ hr₁ h.symm (Ne.symm hne) ((not_lt.mp hlt).lt_of_ne (Ne.symm hne))
  obtain ⟨m, c, hrm, hcs⟩ := NormedField.exists_pow_lt_norm_lt_pow K hr₀ hlt
  have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 ^ m)
    (weightedC _ isWeightFamily_one_weight c)) h
  simp only [gaussPoint_vle_iff, map_pow, closedDiscGaussValuation_weightedC, eq_iff_iff,
    ← NNReal.coe_le_coe, NNReal.coe_pow, coe_closedDiscGaussValuation_weightedX,
    coe_nnnorm] at key
  exact (key.mp hrm.le).not_gt hcs

/-! ### The points just above and just below a Gauss point -/

/-- **The Gauss valuation just above `r < 1` is at most one on power-bounded elements** of
`K⟨T⟩`: a power-bounded series of Gauss norm `1` at radius `r < 1` attains that norm only in
degree `0`. -/
theorem closedDiscGaussValuationAbove_le_one_of_isPowerBounded (hr₀ : 0 < r) (hr₁ : r < 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : IsPowerBounded f) : closedDiscGaussValuationAbove hr₀ hr₁.le f ≤ 1 := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁.le
  have h1 : TauCeti.PowerSeries.IsDistinguished r 0
      ((toRestrictedSubring hr 1 : PowerSeries.IsRestricted.subring (R := K) r) :
        PowerSeries K) := by
    rw [coe_toRestrictedSubring_one]
    exact TauCeti.PowerSeries.isDistinguished_monomial hr₀ one_ne_zero 0
  rcases (closedDiscGaussValuation_le_one_of_isPowerBounded hr₀ hr₁.le hf).lt_or_eq
    with hlt | heq
  · rw [← map_one (closedDiscGaussValuationAbove (R := K) hr₀ hr₁.le)]
    exact (closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁.le (by rwa [map_one])).le
  have hF : (toRestrictedSubring hr f : PowerSeries K) ≠ 0 :=
    coe_toRestrictedSubring_ne_zero hr fun h ↦ by simp [h] at heq
  obtain ⟨s, hs⟩ := TauCeti.PowerSeries.exists_isDistinguished hr₀ (toRestrictedSubring hr f).2 hF
  have hs0 : s = 0 := by
    by_contra hne
    have hnorm : ‖MvPowerSeries.coeff (Finsupp.single 0 s) (f : MvPowerSeries (Fin 1) K)‖ ≤ 1 := by
      have h1 := closedDiscGaussValuation_le_one_of_isPowerBounded one_pos le_rfl hf
      simpa using (norm_coeff_mul_pow_le_closedDiscGaussValuation one_pos le_rfl f s).trans
        (NNReal.coe_le_one.mpr h1)
    have heq' := hs.norm_coeff_mul_pow_eq
    rw [← TauCeti.PowerSeries.coe_gaussValuation hr₀, coeff_toRestrictedSubring] at heq'
    have : (TauCeti.PowerSeries.gaussValuation hr₀ (toRestrictedSubring hr f) : ℝ) = 1 :=
      congrArg NNReal.toReal heq
    rw [this] at heq'
    exact (mul_le_of_le_one_left (pow_nonneg hr₀.le s) hnorm).not_gt
      (heq' ▸ pow_lt_one₀ hr₀.le hr₁ hne)
  rw [← map_one (closedDiscGaussValuationAbove (R := K) hr₀ hr₁.le), closedDiscGaussValuationAbove,
    Valuation.comap_apply, Valuation.comap_apply,
    TauCeti.PowerSeries.gaussValuationAbove_le_iff hr₀ hs h1, hs0]
  exact Or.inr ⟨heq.trans (by rw [map_one, map_one]), le_rfl⟩

/-- **The Gauss valuation just below `r` is at most one on power-bounded elements** of `K⟨T⟩`. -/
theorem closedDiscGaussValuationBelow_le_one_of_isPowerBounded (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : IsPowerBounded f) : closedDiscGaussValuationBelow hr₀ hr₁ f ≤ 1 := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁
  rcases (closedDiscGaussValuation_le_one_of_isPowerBounded hr₀ hr₁ hf).lt_or_eq with hlt | heq
  · rw [← map_one (closedDiscGaussValuationBelow (R := K) hr₀ hr₁)]
    exact (closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ (by rwa [map_one])).le
  have hF : (toRestrictedSubring hr f : PowerSeries K) ≠ 0 :=
    coe_toRestrictedSubring_ne_zero hr fun h ↦ by simp [h] at heq
  obtain ⟨s, hs⟩ := TauCeti.PowerSeries.exists_isLowestDominant hr₀ (toRestrictedSubring hr f).2 hF
  have h1 : TauCeti.PowerSeries.IsLowestDominant r 0
      ((toRestrictedSubring hr 1 : PowerSeries.IsRestricted.subring (R := K) r) :
        PowerSeries K) := by
    rw [coe_toRestrictedSubring_one]
    exact TauCeti.PowerSeries.isLowestDominant_monomial hr₀ one_ne_zero 0
  rw [← map_one (closedDiscGaussValuationBelow (R := K) hr₀ hr₁), closedDiscGaussValuationBelow,
    Valuation.comap_apply, Valuation.comap_apply,
    TauCeti.PowerSeries.gaussValuationBelow_le_iff hr₀ hs h1]
  exact Or.inr ⟨heq.trans (by rw [map_one, map_one]), Nat.zero_le s⟩

/-- **The point `η_{r⁺}` just above the Gauss point `η_r`**, for `0 < r < 1`: the point of
`Spa (K⟨T⟩, K⟨T⟩°)` given by the Gauss valuation just above `r`,
`f ↦ (|f|_r, last degree attaining |f|_r)` in `ℝ≥0ˣ ×ₗ ℤ`. -/
noncomputable def gaussPointAbove (hr₀ : 0 < r) (hr₁ : r < 1) : closedPolydisc 1 K :=
  ⟨ofValuation (Γ₀ := WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ))
      (closedDiscGaussValuationAbove (R := K) hr₀ hr₁.le),
    (mem_closedPolydisc_iff _ _ _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr (isContinuous_closedDiscGaussValuationAbove hr₀ hr₁.le),
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact closedDiscGaussValuationAbove_le_one_of_isPowerBounded hr₀ hr₁
          (mem_powerBoundedSubring.mp hf)⟩⟩

/-- **The point `η_{r⁻}` just below the Gauss point `η_r`**, for `0 < r ≤ 1`: the point of
`Spa (K⟨T⟩, K⟨T⟩°)` given by the Gauss valuation just below `r`,
`f ↦ (|f|_r, -(first degree attaining |f|_r))` in `ℝ≥0ˣ ×ₗ ℤ`. -/
noncomputable def gaussPointBelow (hr₀ : 0 < r) (hr₁ : r ≤ 1) : closedPolydisc 1 K :=
  ⟨ofValuation (Γ₀ := WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ))
      (closedDiscGaussValuationBelow (R := K) hr₀ hr₁),
    (mem_closedPolydisc_iff _ _ _).mpr
    ⟨(isContinuous_ofValuation_iff _).mpr (isContinuous_closedDiscGaussValuationBelow hr₀ hr₁),
      fun _ hf ↦ (vle_ofValuation _ _ _).mpr <| by
        rw [map_one]
        exact closedDiscGaussValuationBelow_le_one_of_isPowerBounded hr₀ hr₁
          (mem_powerBoundedSubring.mp hf)⟩⟩

/-- The underlying point of `η_{r⁺}` in `Spv K⟨T⟩` is defined by the Gauss valuation just above
`r`. -/
theorem gaussPointAbove_val (hr₀ : 0 < r) (hr₁ : r < 1) :
    (gaussPointAbove (K := K) hr₀ hr₁).1 = ofValuation (Γ₀ := WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ))
      (closedDiscGaussValuationAbove hr₀ hr₁.le) :=
  (rfl)

/-- The underlying point of `η_{r⁻}` in `Spv K⟨T⟩` is defined by the Gauss valuation just below
`r`. -/
theorem gaussPointBelow_val (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (gaussPointBelow (K := K) hr₀ hr₁).1 = ofValuation (Γ₀ := WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ))
      (closedDiscGaussValuationBelow hr₀ hr₁) :=
  (rfl)

/-- The point `η_{r⁺}` compares two series by their Gauss valuations just above `r`. -/
@[simp]
theorem gaussPointAbove_vle_iff (hr₀ : 0 < r) (hr₁ : r < 1)
    (f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (gaussPointAbove hr₀ hr₁).1.toValuativeRel.vle f g ↔
      closedDiscGaussValuationAbove hr₀ hr₁.le f ≤ closedDiscGaussValuationAbove hr₀ hr₁.le g := by
  rw [gaussPointAbove_val, vle_ofValuation]

/-- The point `η_{r⁻}` compares two series by their Gauss valuations just below `r`. -/
@[simp]
theorem gaussPointBelow_vle_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (f g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight) :
    (gaussPointBelow hr₀ hr₁).1.toValuativeRel.vle f g ↔
      closedDiscGaussValuationBelow hr₀ hr₁ f ≤ closedDiscGaussValuationBelow hr₀ hr₁ g := by
  rw [gaussPointBelow_val, vle_ofValuation]

/-- **The support of `η_{r⁺}` is trivial.** -/
@[simp]
theorem supp_gaussPointAbove (hr₀ : 0 < r) (hr₁ : r < 1) :
    (gaussPointAbove (K := K) hr₀ hr₁).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by
    rw [mem_supp_iff, gaussPointAbove_vle_iff, map_zero, le_zero_iff,
      closedDiscGaussValuationAbove_eq_zero_iff, Ideal.mem_bot]

/-- **The support of `η_{r⁻}` is trivial.** -/
@[simp]
theorem supp_gaussPointBelow (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    (gaussPointBelow (K := K) hr₀ hr₁).1.supp = ⊥ :=
  Ideal.ext fun _ ↦ by
    rw [mem_supp_iff, gaussPointBelow_vle_iff, map_zero, le_zero_iff,
      closedDiscGaussValuationBelow_eq_zero_iff, Ideal.mem_bot]

/-- The variable `T` and a constant `c` of norm `r` have the same Gauss norm at radius `r`. -/
private theorem closedDiscGaussValuation_weightedX_eq_weightedC (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {c : K} (hc : ‖c‖ = r) :
    closedDiscGaussValuation hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) =
      closedDiscGaussValuation hr₀ hr₁ (weightedC _ isWeightFamily_one_weight c) :=
  NNReal.eq <| by rw [coe_closedDiscGaussValuation_weightedX, closedDiscGaussValuation_weightedC,
    coe_nnnorm, hc]

/-- Just above `r`, the variable `T` is strictly larger than a constant `c` of norm `r`: the
Gauss norms agree and `T` attains its norm in the later degree. -/
theorem not_closedDiscGaussValuationAbove_weightedX_le (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {c : K} (hc : ‖c‖ = r) :
    ¬ closedDiscGaussValuationAbove hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) ≤
      closedDiscGaussValuationAbove hr₀ hr₁ (weightedC _ isWeightFamily_one_weight c) := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁
  have hc0 : c ≠ 0 := norm_pos_iff.mp (hc ▸ hr₀)
  have hX : TauCeti.PowerSeries.IsDistinguished r 1 (toRestrictedSubring hr
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) : PowerSeries K) := by
    rw [coe_toRestrictedSubring_weightedX]
    exact TauCeti.PowerSeries.isDistinguished_monomial hr₀ one_ne_zero 1
  have hC : TauCeti.PowerSeries.IsDistinguished r 0 (toRestrictedSubring hr
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight c) : PowerSeries K) := by
    rw [coe_toRestrictedSubring_weightedC]
    exact TauCeti.PowerSeries.isDistinguished_monomial hr₀ hc0 0
  rw [closedDiscGaussValuationAbove, Valuation.comap_apply, Valuation.comap_apply,
    TauCeti.PowerSeries.gaussValuationAbove_le_iff hr₀ hX hC]
  have heq := closedDiscGaussValuation_weightedX_eq_weightedC hr₀ hr₁ hc
  rintro (h | ⟨-, h⟩)
  · exact h.ne heq
  · exact absurd h (by norm_num)

/-- Just below `r`, a constant `c` of norm `r` is strictly larger than the variable `T`: the Gauss
norms agree and `c` attains its norm in the earlier degree. -/
theorem not_closedDiscGaussValuationBelow_weightedC_le (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    {c : K} (hc : ‖c‖ = r) :
    ¬ closedDiscGaussValuationBelow hr₀ hr₁ (weightedC _ isWeightFamily_one_weight c) ≤
      closedDiscGaussValuationBelow hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁
  have hc0 : c ≠ 0 := norm_pos_iff.mp (hc ▸ hr₀)
  have hX : TauCeti.PowerSeries.IsLowestDominant r 1 (toRestrictedSubring hr
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) : PowerSeries K) := by
    rw [coe_toRestrictedSubring_weightedX]
    exact TauCeti.PowerSeries.isLowestDominant_monomial hr₀ one_ne_zero 1
  have hC : TauCeti.PowerSeries.IsLowestDominant r 0 (toRestrictedSubring hr
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight c) : PowerSeries K) := by
    rw [coe_toRestrictedSubring_weightedC]
    exact TauCeti.PowerSeries.isLowestDominant_monomial hr₀ hc0 0
  rw [closedDiscGaussValuationBelow, Valuation.comap_apply, Valuation.comap_apply,
    TauCeti.PowerSeries.gaussValuationBelow_le_iff hr₀ hC hX]
  have heq := closedDiscGaussValuation_weightedX_eq_weightedC hr₀ hr₁ hc
  rintro (h | ⟨-, h⟩)
  · exact h.ne heq.symm
  · exact absurd h (by norm_num)

/-- **Just above `r`, the variable `T` is at most a constant `c` exactly when `r < ‖c‖`**: the
Gauss norms decide unless `‖c‖ = r`, and then `T` is strictly larger. -/
@[simp]
theorem closedDiscGaussValuationAbove_weightedX_le_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1) (c : K) :
    closedDiscGaussValuationAbove hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) ≤
      closedDiscGaussValuationAbove hr₀ hr₁ (weightedC _ isWeightFamily_one_weight c) ↔
      r < ‖c‖ := by
  rcases lt_trichotomy ‖c‖ r with h | h | h
  · refine iff_of_false (not_le.mpr (closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁ ?_))
      (lt_asymm h)
    rwa [← NNReal.coe_lt_coe, coe_closedDiscGaussValuation_weightedX,
      closedDiscGaussValuation_weightedC, coe_nnnorm]
  · exact iff_of_false (not_closedDiscGaussValuationAbove_weightedX_le hr₀ hr₁ h)
      fun h' ↦ h'.ne' h
  · refine iff_of_true (closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁ ?_).le h
    rwa [← NNReal.coe_lt_coe, coe_closedDiscGaussValuation_weightedX,
      closedDiscGaussValuation_weightedC, coe_nnnorm]

/-- **Just below `r`, a constant `c` is at most the variable `T` exactly when `‖c‖ < r`**: the
Gauss norms decide unless `‖c‖ = r`, and then `c` is strictly larger. -/
@[simp]
theorem closedDiscGaussValuationBelow_weightedC_le_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1) (c : K) :
    closedDiscGaussValuationBelow hr₀ hr₁ (weightedC _ isWeightFamily_one_weight c) ≤
      closedDiscGaussValuationBelow hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) ↔
      ‖c‖ < r := by
  rcases lt_trichotomy ‖c‖ r with h | h | h
  · refine iff_of_true (closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ ?_).le h
    rwa [← NNReal.coe_lt_coe, coe_closedDiscGaussValuation_weightedX,
      closedDiscGaussValuation_weightedC, coe_nnnorm]
  · exact iff_of_false (not_closedDiscGaussValuationBelow_weightedC_le hr₀ hr₁ h) fun h' ↦ h'.ne h
  · refine iff_of_false (not_le.mpr (closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ ?_))
      (lt_asymm h)
    rwa [← NNReal.coe_lt_coe, coe_closedDiscGaussValuation_weightedX,
      closedDiscGaussValuation_weightedC, coe_nnnorm]

/-- **Just above `r`, a constant `c` is at most the variable `T` exactly when `‖c‖ ≤ r`**: this
is the complement of `closedDiscGaussValuationAbove_weightedX_le_iff`. -/
@[simp]
theorem closedDiscGaussValuationAbove_weightedC_le_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1) (c : K) :
    closedDiscGaussValuationAbove hr₀ hr₁ (weightedC _ isWeightFamily_one_weight c) ≤
      closedDiscGaussValuationAbove hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) ↔
      ‖c‖ ≤ r := by
  rcases lt_or_ge r ‖c‖ with h | h
  · refine iff_of_false (not_le.mpr (closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁ ?_))
      h.not_ge
    rwa [← NNReal.coe_lt_coe, coe_closedDiscGaussValuation_weightedX,
      closedDiscGaussValuation_weightedC, coe_nnnorm]
  · exact iff_of_true (not_le.mp
      ((closedDiscGaussValuationAbove_weightedX_le_iff hr₀ hr₁ c).not.mpr h.not_gt)).le h

/-- **Just below `r`, the variable `T` is at most a constant `c` exactly when `r ≤ ‖c‖`**: this
is the complement of `closedDiscGaussValuationBelow_weightedC_le_iff`. -/
@[simp]
theorem closedDiscGaussValuationBelow_weightedX_le_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1) (c : K) :
    closedDiscGaussValuationBelow hr₀ hr₁
        (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) ≤
      closedDiscGaussValuationBelow hr₀ hr₁ (weightedC _ isWeightFamily_one_weight c) ↔
      r ≤ ‖c‖ := by
  rcases lt_or_ge ‖c‖ r with h | h
  · refine iff_of_false (not_le.mpr (closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ ?_))
      h.not_ge
    rwa [← NNReal.coe_lt_coe, coe_closedDiscGaussValuation_weightedX,
      closedDiscGaussValuation_weightedC, coe_nnnorm]
  · exact iff_of_true (not_le.mp
      ((closedDiscGaussValuationBelow_weightedC_le_iff hr₀ hr₁ c).not.mpr h.not_gt)).le h

/-- **Just above `r`, constants are compared by their norms**: a nonzero constant attains its
Gauss norm only in degree `0`. -/
@[simp]
theorem closedDiscGaussValuationAbove_weightedC_le_weightedC_iff (hr₀ : 0 < r) (hr₁ : r ≤ 1)
    (a b : K) :
    closedDiscGaussValuationAbove hr₀ hr₁
        (weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight a) ≤
      closedDiscGaussValuationAbove hr₀ hr₁ (weightedC _ isWeightFamily_one_weight b) ↔
      ‖a‖ ≤ ‖b‖ := by
  have hr : |r| ≤ 1 := (abs_of_pos hr₀).trans_le hr₁
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp [ha]
  have hdist {c : K} (hc : c ≠ 0) : TauCeti.PowerSeries.IsDistinguished r 0 (toRestrictedSubring hr
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight c) : PowerSeries K) := by
    rw [coe_toRestrictedSubring_weightedC]
    exact TauCeti.PowerSeries.isDistinguished_monomial hr₀ hc 0
  rw [closedDiscGaussValuationAbove, Valuation.comap_apply, Valuation.comap_apply,
    TauCeti.PowerSeries.gaussValuationAbove_le_iff hr₀ (hdist ha) (hdist hb)]
  have hG (c : K) : TauCeti.PowerSeries.gaussValuation hr₀ (toRestrictedSubring hr
      (weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight c)) = ‖c‖₊ :=
    closedDiscGaussValuation_weightedC hr₀ hr₁ c
  rw [hG, hG]
  simp [← le_iff_lt_or_eq, ← NNReal.coe_le_coe]

/-- **`η_{r⁺}` is not the Gauss point `η_r`** when `r` is the norm of an element of `K`: the two
points compare `T` with a constant of norm `r` differently. -/
theorem gaussPointAbove_ne_gaussPoint (hr₀ : 0 < r) (hr₁ : r < 1) (hr : ∃ c : K, ‖c‖ = r) :
    gaussPointAbove (K := K) hr₀ hr₁ ≠ gaussPoint hr₀ hr₁.le := fun h ↦ by
  obtain ⟨c, hc⟩ := hr
  have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0)
    (weightedC _ isWeightFamily_one_weight c)) h
  simp only [gaussPointAbove_vle_iff, gaussPoint_vle_iff, eq_iff_iff] at key
  exact not_closedDiscGaussValuationAbove_weightedX_le hr₀ hr₁.le hc
    (key.mpr (closedDiscGaussValuation_weightedX_eq_weightedC hr₀ hr₁.le hc).le)

/-- **`η_{r⁻}` is not the Gauss point `η_r`** when `r` is the norm of an element of `K`: the two
points compare `T` with a constant of norm `r` differently. -/
theorem gaussPointBelow_ne_gaussPoint (hr₀ : 0 < r) (hr₁ : r ≤ 1) (hr : ∃ c : K, ‖c‖ = r) :
    gaussPointBelow (K := K) hr₀ hr₁ ≠ gaussPoint hr₀ hr₁ := fun h ↦ by
  obtain ⟨c, hc⟩ := hr
  have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
    (weightedC _ isWeightFamily_one_weight c)
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0)) h
  simp only [gaussPointBelow_vle_iff, gaussPoint_vle_iff, eq_iff_iff] at key
  exact not_closedDiscGaussValuationBelow_weightedC_le hr₀ hr₁ hc
    (key.mpr (closedDiscGaussValuation_weightedX_eq_weightedC hr₀ hr₁ hc).ge)

/-- **`η_{r⁻}` and `η_{r⁺}` are distinct** when `r` is the norm of an element of `K`: just below
`r` the variable `T` is smaller than a constant of norm `r`, just above it is larger. -/
theorem gaussPointBelow_ne_gaussPointAbove (hr₀ : 0 < r) (hr₁ : r < 1) (hr : ∃ c : K, ‖c‖ = r) :
    gaussPointBelow (K := K) hr₀ hr₁.le ≠ gaussPointAbove hr₀ hr₁ := fun h ↦ by
  obtain ⟨c, hc⟩ := hr
  have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0)
    (weightedC _ isWeightFamily_one_weight c)) h
  simp only [gaussPointBelow_vle_iff, gaussPointAbove_vle_iff, eq_iff_iff] at key
  exact not_closedDiscGaussValuationAbove_weightedX_le hr₀ hr₁.le hc
    (key.mp (le_of_not_ge (not_closedDiscGaussValuationBelow_weightedC_le hr₀ hr₁.le hc)))

/-- **Distinct radii `0 < r, s < 1` give distinct points `η_{r⁺}`**: they refine the distinct
Gauss points `η_r` and `η_s`. -/
theorem gaussPointAbove_inj {s : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) (hs₀ : 0 < s) (hs₁ : s < 1) :
    gaussPointAbove (K := K) hr₀ hr₁ = gaussPointAbove hs₀ hs₁ ↔ r = s := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  by_contra hne
  wlog hlt : r < s generalizing r s
  · exact this hs₀ hs₁ hr₀ hr₁ h.symm (Ne.symm hne) ((not_lt.mp hlt).lt_of_ne (Ne.symm hne))
  obtain ⟨m, c, hrm, hcs⟩ := NormedField.exists_pow_lt_norm_lt_pow K hr₀ hlt
  have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 ^ m)
    (weightedC _ isWeightFamily_one_weight c)) h
  simp only [gaussPointAbove_vle_iff, eq_iff_iff] at key
  -- `Tᵐ` is strictly below `c` at radius `r` and strictly above it at radius `s`
  refine (closedDiscGaussValuationAbove_lt_of_lt hs₀ hs₁.le ?_).not_ge
    (key.mp (closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁.le ?_).le) <;>
  simpa only [← NNReal.coe_lt_coe, map_pow, NNReal.coe_pow, closedDiscGaussValuation_weightedC,
    coe_closedDiscGaussValuation_weightedX, coe_nnnorm]

/-- **Distinct radii `0 < r, s ≤ 1` give distinct points `η_{r⁻}`**: they refine the distinct
Gauss points `η_r` and `η_s`. -/
theorem gaussPointBelow_inj {s : ℝ} (hr₀ : 0 < r) (hr₁ : r ≤ 1) (hs₀ : 0 < s) (hs₁ : s ≤ 1) :
    gaussPointBelow (K := K) hr₀ hr₁ = gaussPointBelow hs₀ hs₁ ↔ r = s := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  by_contra hne
  wlog hlt : r < s generalizing r s
  · exact this hs₀ hs₁ hr₀ hr₁ h.symm (Ne.symm hne) ((not_lt.mp hlt).lt_of_ne (Ne.symm hne))
  obtain ⟨m, c, hrm, hcs⟩ := NormedField.exists_pow_lt_norm_lt_pow K hr₀ hlt
  have key := congrArg (fun p : closedPolydisc 1 K ↦ p.1.toValuativeRel.vle
    (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0 ^ m)
    (weightedC _ isWeightFamily_one_weight c)) h
  simp only [gaussPointBelow_vle_iff, eq_iff_iff] at key
  -- `Tᵐ` is strictly below `c` at radius `r` and strictly above it at radius `s`
  refine (closedDiscGaussValuationBelow_lt_of_lt hs₀ hs₁ ?_).not_ge
    (key.mp (closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ ?_).le) <;>
  simpa only [← NNReal.coe_lt_coe, map_pow, NNReal.coe_pow, closedDiscGaussValuation_weightedC,
    coe_closedDiscGaussValuation_weightedX, coe_nnnorm]

/-- **A point refining the Gauss point `η_r` is a specialization of it.** If a strictly smaller
Gauss norm of radius `r` gives a strictly smaller value at `x ∈ Spv K⟨T⟩`, then `x` lies in the
closure of `η_r`. The point `x` need not lie in the closed unit disc. -/
theorem gaussPoint_specializes_of_lt {hr₀ : 0 < r} {hr₁ : r ≤ 1}
    {x : Spv (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
      isWeightFamily_one_weight)}
    (hlt : ∀ f g, closedDiscGaussValuation hr₀ hr₁ f < closedDiscGaussValuation hr₀ hr₁ g →
      ¬ x.toValuativeRel.vle g f) :
    (gaussPoint hr₀ hr₁).1 ⤳ x := by
  refine specializes_of_forall_mem_basicOpen fun f g hx ↦ ?_
  obtain ⟨hfg, hg⟩ := (mem_basicOpen_iff _ _ _).mp hx
  refine (mem_basicOpen_iff _ _ _).mpr ⟨?_, ?_⟩
  · rw [gaussPoint_vle_iff]
    exact not_lt.mp fun h ↦ hlt g f h hfg
  · rw [gaussPoint_vle_zero_iff]
    exact fun h ↦ hg (h ▸ x.toValuativeRel.vle_refl 0)

/-- **`η_{r⁺}` is a specialization of the Gauss point `η_r`**: it lies in the closure of `η_r`,
since its valuation refines the Gauss norm of radius `r`. -/
theorem gaussPoint_specializes_gaussPointAbove (hr₀ : 0 < r) (hr₁ : r < 1) :
    gaussPoint (K := K) hr₀ hr₁.le ⤳ gaussPointAbove hr₀ hr₁ :=
  Topology.IsInducing.subtypeVal.specializes_iff.mp <| gaussPoint_specializes_of_lt
    (fun _ _ h ↦ by
      rw [gaussPointAbove_vle_iff, not_le]
      exact closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁.le h)

/-- **`η_{r⁻}` is a specialization of the Gauss point `η_r`**: it lies in the closure of `η_r`,
since its valuation refines the Gauss norm of radius `r`. -/
theorem gaussPoint_specializes_gaussPointBelow (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    gaussPoint (K := K) hr₀ hr₁ ⤳ gaussPointBelow hr₀ hr₁ :=
  Topology.IsInducing.subtypeVal.specializes_iff.mp <| gaussPoint_specializes_of_lt
    (fun _ _ h ↦ by
      rw [gaussPointBelow_vle_iff, not_le]
      exact closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ h)

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
