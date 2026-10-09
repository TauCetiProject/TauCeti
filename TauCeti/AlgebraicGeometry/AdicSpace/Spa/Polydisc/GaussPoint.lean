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
  it takes the value `‖a‖` on the constant `a` and `r` on the variable.
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
* `TauCeti.ValuationSpectrum.gaussPointAbove_ne_gaussPoint`,
  `TauCeti.ValuationSpectrum.gaussPointBelow_ne_gaussPoint` and
  `TauCeti.ValuationSpectrum.gaussPointBelow_ne_gaussPointAbove`: for `r` the norm of an element
  of `K`, the three points at radius `r` are pairwise distinct.
* `TauCeti.ValuationSpectrum.gaussPoint_specializes_gaussPointAbove` and
  `TauCeti.ValuationSpectrum.gaussPoint_specializes_gaussPointBelow`: `η_{r⁺}` and `η_{r⁻}` lie in
  the closure of `η_r`.

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
    -- `PowerSeries R` is `MvPowerSeries Unit R`; the constant series are definitionally equal.
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
    -- Renaming sends the sole `Fin 1` variable to `Unit`; both series use that same variable.
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

/-! ### The points just above and just below a Gauss point -/

/-- The weighted coefficients of `f ∈ K⟨T⟩` are its coefficients as a restricted series. -/
private theorem coeff_toRestrictedSubring (hr : |r| ≤ 1)
    (f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight)
    (n : ℕ) :
    (toRestrictedSubring hr f : PowerSeries K).coeff n =
      MvPowerSeries.coeff (Finsupp.single 0 n) (f : MvPowerSeries (Fin 1) K) := by
  simp only [coe_toRestrictedSubring, PowerSeries.coeff_rename,
    Subsingleton.elim (finOneEquiv.symm ()) 0]

private theorem coe_toRestrictedSubring_ne_zero (hr : |r| ≤ 1)
    {f : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight}
    (hf : f ≠ 0) : (toRestrictedSubring hr f : PowerSeries K) ≠ 0 := by
  rw [Ne, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ (toRestrictedSubring_injective hr)]
  exact hf

private theorem coe_toRestrictedSubring_one (hr : |r| ≤ 1) :
    ((toRestrictedSubring hr 1 :
      PowerSeries.IsRestricted.subring (R := K) r) : PowerSeries K) = PowerSeries.monomial 0 1 := by
  rw [map_one, OneMemClass.coe_one, PowerSeries.monomial_zero_eq_C_apply, map_one]

private theorem coe_toRestrictedSubring_weightedX (hr : |r| ≤ 1) :
    ((toRestrictedSubring hr
      (weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0) :
      PowerSeries.IsRestricted.subring (R := K) r) : PowerSeries K) =
      PowerSeries.monomial 1 1 := by
  rw [toRestrictedSubring_weightedX]
  exact PowerSeries.X_eq

private theorem coe_toRestrictedSubring_weightedC (hr : |r| ≤ 1) (a : K) :
    ((toRestrictedSubring hr (weightedC (fun _ : Fin 1 ↦ ({1} : Set K))
      isWeightFamily_one_weight a) : PowerSeries.IsRestricted.subring (R := K) r) :
      PowerSeries K) = PowerSeries.monomial 0 a := by
  rw [toRestrictedSubring_weightedC]
  exact (PowerSeries.monomial_zero_eq_C_apply a).symm

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
private theorem not_closedDiscGaussValuationAbove_weightedX_le (hr₀ : 0 < r) (hr₁ : r ≤ 1)
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
private theorem not_closedDiscGaussValuationBelow_weightedC_le (hr₀ : 0 < r) (hr₁ : r ≤ 1)
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

/-- A point refining the Gauss point `η_r`, in the sense that a strictly smaller Gauss norm gives
a strictly smaller value and only zero vanishes, lies in the closure of `η_r`. -/
private theorem gaussPoint_specializes_of_lt {hr₀ : 0 < r} {hr₁ : r ≤ 1}
    {x : closedPolydisc 1 K}
    (hlt : ∀ f g, closedDiscGaussValuation hr₀ hr₁ f < closedDiscGaussValuation hr₀ hr₁ g →
      ¬ x.1.toValuativeRel.vle g f)
    (h0 : ∀ g, ¬ x.1.toValuativeRel.vle g 0 → g ≠ 0) :
    gaussPoint hr₀ hr₁ ⤳ x := by
  rw [← Topology.IsInducing.subtypeVal.specializes_iff]
  refine specializes_of_forall_mem_basicOpen fun f g hx ↦ ?_
  obtain ⟨hfg, hg⟩ := (mem_basicOpen_iff _ _ _).mp hx
  refine (mem_basicOpen_iff _ _ _).mpr ⟨?_, ?_⟩
  · rw [gaussPoint_vle_iff]
    exact not_lt.mp fun h ↦ hlt g f h hfg
  · rw [gaussPoint_vle_zero_iff]
    exact h0 g hg

/-- **`η_{r⁺}` is a specialization of the Gauss point `η_r`**: it lies in the closure of `η_r`,
since its valuation refines the Gauss norm of radius `r`. -/
theorem gaussPoint_specializes_gaussPointAbove (hr₀ : 0 < r) (hr₁ : r < 1) :
    gaussPoint (K := K) hr₀ hr₁.le ⤳ gaussPointAbove hr₀ hr₁ :=
  gaussPoint_specializes_of_lt
    (fun _ _ h ↦ by
      rw [gaussPointAbove_vle_iff, not_le]
      exact closedDiscGaussValuationAbove_lt_of_lt hr₀ hr₁.le h)
    fun g hg h ↦ hg (by rw [h]; exact (gaussPointAbove hr₀ hr₁).1.toValuativeRel.vle_refl 0)

/-- **`η_{r⁻}` is a specialization of the Gauss point `η_r`**: it lies in the closure of `η_r`,
since its valuation refines the Gauss norm of radius `r`. -/
theorem gaussPoint_specializes_gaussPointBelow (hr₀ : 0 < r) (hr₁ : r ≤ 1) :
    gaussPoint (K := K) hr₀ hr₁ ⤳ gaussPointBelow hr₀ hr₁ :=
  gaussPoint_specializes_of_lt
    (fun _ _ h ↦ by
      rw [gaussPointBelow_vle_iff, not_le]
      exact closedDiscGaussValuationBelow_lt_of_lt hr₀ hr₁ h)
    fun g hg h ↦ hg (by rw [h]; exact (gaussPointBelow hr₀ hr₁).1.toValuativeRel.vle_refl 0)

end NontriviallyNormedField

end TauCeti.ValuationSpectrum
