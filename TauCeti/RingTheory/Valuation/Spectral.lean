/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.RingTheory.Valuation.Continuous.Basic

import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.Valuation.Integral
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The spectral valuation of an algebraic extension

Let `K` be a complete nontrivially normed field with an ultrametric norm and `L` an algebraic
field extension of `K`. Mathlib's spectral norm `spectralNorm K L` is then the unique
power-multiplicative `K`-algebra norm on `L` extending the norm of `K` (`spectralNorm_unique`),
and it is multiplicative and nonarchimedean. So it is a rank-one valuation on `L`, the
*spectral valuation* `TauCeti.spectralValuation K L`: Mathlib's `NormedField.valuation` for the
normed field structure `spectralNorm.normedField K L`.

That normed field structure is not installed as an instance, because `L` often carries a
topology of its own. The typical case is a residue field `A ⧸ 𝔪` of a topological `K`-algebra,
with the quotient topology. When `L` is finite over `K` and that topology makes it a Hausdorff
topological `K`-vector space, the spectral valuation is continuous for it
(`TauCeti.isContinuous_spectralValuation`). This is how a maximal ideal with finite residue field
gives a point of an adic spectrum.

Up to equivalence the spectral valuation is the only valuation on `L` extending the norm of `K`
(`Valuation.isEquiv_spectralValuation_iff`). An element of spectral norm at most one is integral
over the closed unit ball of `K`, so every such valuation is at most one on it. An element of
spectral norm below one has a power dominated by a scalar of norm below one, so its value is below
one. This makes the point of an adic spectrum attached to a maximal ideal the only one with that
support.

## Main definitions

* `TauCeti.spectralValuation`: the spectral norm of an algebraic extension, as a valuation with
  values in `ℝ≥0`.

## Main results

* `TauCeti.coe_spectralValuation`: the spectral valuation is the spectral norm.
* `TauCeti.spectralValuation_algebraMap` and `TauCeti.comap_spectralValuation`: it extends the
  norm of `K`.
* `Valuation.isEquiv_spectralValuation_iff`: a valuation on `L` is equivalent to the spectral
  valuation exactly when it compares elements of `K` by their norms.
* `TauCeti.isContinuous_spectralValuation`: on a finite extension it is continuous for every
  Hausdorff topological `K`-vector space structure.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti

variable (K L : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Field L] [Algebra K L]

section IsAlgebraic

variable [Algebra.IsAlgebraic K L]

/-- **The spectral valuation** of an algebraic extension `L` of a complete ultrametric field `K`:
the spectral norm `spectralNorm K L`, which is multiplicative and nonarchimedean, as a valuation
with values in `ℝ≥0`. -/
def spectralValuation : Valuation L ℝ≥0 :=
  letI := spectralNorm.normedField K L
  haveI : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  NormedField.valuation

variable {K L}

/-- The spectral valuation is the spectral norm. -/
@[simp]
theorem coe_spectralValuation (x : L) : (spectralValuation K L x : ℝ) = spectralNorm K L x :=
  (rfl)

/-- The spectral valuation extends the norm of `K`. -/
@[simp]
theorem spectralValuation_algebraMap (c : K) :
    spectralValuation K L (algebraMap K L c) = ‖c‖₊ :=
  NNReal.eq <| by rw [coe_spectralValuation, spectralNorm_extends, coe_nnnorm]

/-- The spectral valuation pulled back to `K` is the norm valuation of `K`. -/
@[simp]
theorem comap_spectralValuation :
    (spectralValuation K L).comap (algebraMap K L) = NormedField.valuation :=
  Valuation.ext fun c ↦ by simp [NormedField.valuation_apply]

/-- An element of spectral norm at most one has value at most one for every valuation that is at
most one on the image of the closed unit ball of `K`: the coefficients of its minimal polynomial
have norm at most one, so it is integral over the ring of integers of the valuation. -/
private theorem le_one_of_spectralValuation_le_one {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {w : Valuation L Γ₀}
    (hw : ∀ c : K, ‖c‖ ≤ 1 → w (algebraMap K L c) ≤ 1) {a : L}
    (ha : spectralValuation K L a ≤ 1) : w a ≤ 1 := by
  have hP : (minpoly K a).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
  have hcoeff := (spectralValue_le_one_iff hP).mp (by
    rwa [← NNReal.coe_le_coe, coe_spectralValuation, NNReal.coe_one] at ha)
  -- the minimal polynomial of `a` has coefficients in the ring of integers of `w`
  have hsub : (((minpoly K a).map (algebraMap K L)).coeffs : Set L) ⊆ w.integer := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    rw [Polynomial.coeff_map]
    exact hw _ (hcoeff n)
  refine (Valuation.integer.integers w).mem_of_integral
    ⟨_, (Polynomial.monic_toSubring _ _ hsub).mpr (hP.map _), ?_⟩
  have := congrArg (Polynomial.eval a) (Polynomial.map_toSubring _ _ hsub)
  rwa [Polynomial.eval_map, Polynomial.eval_map_algebraMap, minpoly.aeval] at this

/-- **Uniqueness of the extension of the norm.** A valuation on an algebraic extension `L` of a
complete ultrametric field `K` is equivalent to the spectral valuation exactly when it compares
elements of `K` by their norms. In particular every such valuation has rank at most one. -/
theorem _root_.Valuation.isEquiv_spectralValuation_iff {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation L Γ₀) :
    w.IsEquiv (spectralValuation K L) ↔
      ∀ c d : K, w (algebraMap K L c) ≤ w (algebraMap K L d) ↔ ‖c‖ ≤ ‖d‖ := by
  refine ⟨fun h c d ↦ ?_, fun hK ↦ ?_⟩
  · rw [h, spectralValuation_algebraMap, spectralValuation_algebraMap, ← NNReal.coe_le_coe,
      coe_nnnorm, coe_nnnorm]
  have hle (c : K) (hc : ‖c‖ ≤ 1) : w (algebraMap K L c) ≤ 1 := by
    simpa using (hK c 1).mpr (by simpa using hc)
  -- an element of spectral norm below one has value below one: compare a power of it with a
  -- scalar of norm strictly between zero and one
  have hlt {a : L} (ha : spectralValuation K L a < 1) : w a < 1 := by
    obtain ⟨c, hc₀, hc₁⟩ := NormedField.exists_norm_lt_one K
    have hwc : w (algebraMap K L c) < 1 := lt_of_not_ge fun h ↦
      hc₁.not_ge (by simpa using (hK 1 c).mp (by simpa using h))
    have hwc₀ : w (algebraMap K L c) ≠ 0 := by simpa using norm_pos_iff.mp hc₀
    obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one (nnnorm_pos.mpr (norm_pos_iff.mp hc₀)) ha
    have hdiv : w (a ^ n / algebraMap K L c) ≤ 1 := le_one_of_spectralValuation_le_one hle <| by
      rw [map_div₀, map_pow, spectralValuation_algebraMap]
      exact div_le_one_of_le₀ hn.le zero_le
    rw [map_div₀, map_pow, div_le_one₀ (zero_lt_iff.mpr hwc₀)] at hdiv
    by_contra! h1
    exact (one_le_pow₀ h1).trans hdiv |>.not_gt hwc
  refine Valuation.isEquiv_of_val_le_one fun a ↦ ⟨fun ha ↦ ?_,
    le_one_of_spectralValuation_le_one hle⟩
  by_contra! h
  have ha₀ : a ≠ 0 := by rintro rfl; simp at h
  have := hlt (a := a⁻¹) (by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h)
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff w).mpr ha₀))] at this
  exact this.not_ge ha

end IsAlgebraic

/-- **The spectral valuation is continuous** on a finite extension `L` of `K`, for every topology
making `L` a Hausdorff topological `K`-vector space. The spectral norm is a `K`-seminorm on `L`,
and every seminorm on a finite-dimensional Hausdorff topological vector space is continuous. -/
theorem isContinuous_spectralValuation [FiniteDimensional K L] [TopologicalSpace L]
    [IsTopologicalAddGroup L] [ContinuousSMul K L] [T2Space L] :
    (spectralValuation K L).IsContinuous := by
  have hcont : Continuous (spectralNorm K L) :=
    (spectralAlgNorm K L).toSeminorm.continuous_of_finiteDimensional
  refine Valuation.isContinuous_of_forall_isOpen_lt fun γ ↦ ?_
  simpa [← NNReal.coe_lt_coe] using isOpen_lt hcont continuous_const

end TauCeti
