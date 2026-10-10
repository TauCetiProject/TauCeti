/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite means and centered scatter operators

For a finite family `z : Fin n → E` in an inner-product space, the centered scatter operator
is `∑ i, (zᵢ - mean z) ⊗ (zᵢ - mean z)`.  The primary theorem is the exact add-one update

`S(Fin.snoc z y) = S(z) + n/(n+1) • ((y - mean z) ⊗ (y - mean z))`,

from which Löwner monotonicity and quadratic-form growth are short corollaries.

## Main results

* `TauCeti.centeredScatter_append`: the exact operator-level add-one identity;
* `TauCeti.centeredScatter_le_append`: appending a point grows the scatter in Löwner order;
* `TauCeti.re_inner_centeredScatter_append`: the quadratic-form version of the update;
* `TauCeti.re_inner_centeredScatter_self`: the scatter quadratic form is the sum of
  squared centered inner products.

## Implementation notes

`centeredScatter` is a `ContinuousLinearMap`. Its summands `rankOne 𝕜 a a` are continuous
already, so taking the bundled linear map would discard continuity for nothing; the
`IsPositive` and Löwner-order API used below exists at both levels and needs no
completeness assumption.

`finiteMean` is *not* an instance of an existing Mathlib average.

* `Finset.expect`, the canonical finite average, requires `Module ℚ≥0 E`. That instance does
  not resolve for a general `𝕜`-inner-product space: `NormedSpace ℝ E` is reachable only
  through `InnerProductSpace.rclikeToReal` / `NormedSpace.restrictScalars`, which are
  deliberately definitions rather than instances.
* `Finset.centroid` does typecheck here, but `Finset.affineCombination` is defined against
  `Classical.arbitrary`, so the centroid of the empty family is nonconstructive junk.
  `finiteMean` instead returns `0` there, by Mathlib's total-inverse convention, and
  `finiteMean_append` is deliberately stated to hold *at* `n = 0`.

See backlog §8.1.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/InnerProductSpace/CenteredScatter.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declarations: `centeredScatter`, `finiteMean`, `appendFin` and the
  add-one / Löwner / quadratic-form API (namespace renamed here
  `ForMathlib` → `TauCeti`).
* Original authors / copyright: Jon Crall, GPT-5.6 High, Claude Fable 5;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system, then polished
  against the reuse rubric (backlog §8.1): `appendFin` was deleted in favour of
  `Fin.snoc`, and `centeredScatter` moved from `E →ₗ[𝕜] E` to `E →L[𝕜] E`.
* Spectra influence: **none** (imports only Mathlib).

Moved from
`ForTauCeti/Analysis/InnerProductSpace/CenteredScatter.lean` to
`ForTauCeti/Probability/Moments/CenteredScatter.lean`, beside `SampleMean`,
`SampleSecondMoment`, `Variance` and `MatrixConcentration`.  Finite means and
centered scatter operators are the content of roadmap topic T20, where this
module was already assigned; only its path disagreed.  Path change and
repointing of one import in `DkpsQuench2026/Spectral/GramSpectrum.lean` — no
statement, signature, proof, attribute, declaration name or namespace changed.
-/

public section

namespace TauCeti

open Module InnerProductSpace
open scoped BigOperators

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Arithmetic mean of a `Fin n` family. At `n = 0`, Mathlib's total inverse convention makes
this zero. -/
noncomputable def finiteMean {n : ℕ} (z : Fin n → E) : E :=
  ((n : 𝕜)⁻¹) • ∑ i, z i

/-- Unnormalized centered scatter operator `∑ i, (zᵢ - mean z) ⊗ (zᵢ - mean z)`.

The rank-one convention is chosen so its quadratic form is
`∑ i, ‖⟪zᵢ - mean z, x⟫‖²`. -/
noncomputable def centeredScatter {n : ℕ} (z : Fin n → E) : E →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (z i - finiteMean 𝕜 z) (z i - finiteMean 𝕜 z)

/-- The centered residuals sum to zero. -/
theorem sum_sub_finiteMean_eq_zero {n : ℕ} (z : Fin n → E) :
    ∑ i, (z i - finiteMean 𝕜 z) = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      sub_eq_zero, finiteMean]
    rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, mul_inv_cancel₀ hn0, one_smul]

/-- Mean after appending one point: the mean moves toward the new point by the fraction
`1/(n+1)` of the deviation `y - mean z`.  The formula also holds at `n = 0`, where the old
mean is the junk value `0` and the new mean is `y`. -/
theorem finiteMean_append {n : ℕ} (z : Fin n → E) (y : E) :
    finiteMean 𝕜 (Fin.snoc z y) =
      finiteMean 𝕜 z + ((n : 𝕜) + 1)⁻¹ • (y - finiteMean 𝕜 z) := by
  have hsum : ∑ i, Fin.snoc z y i = (∑ i, z i) + y := by
    rw [Fin.sum_univ_castSucc]
    simp
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    -- The old mean is the junk value `0` and the new family sums to `y`.
    unfold finiteMean
    rw [hsum]
    simp
  · have hn0 : (n : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hn1 : (n : 𝕜) + 1 ≠ 0 := by
      have : ((n + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      push_cast at this
      exact this
    unfold finiteMean
    rw [hsum]
    push_cast
    match_scalars
    all_goals field_simp
    all_goals ring

/-- **Exact add-one centered-scatter identity**:
`S(z ++ [y]) = S(z) + n/(n+1) • ((y - mean z) ⊗ (y - mean z))`. -/
theorem centeredScatter_append {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter 𝕜 (Fin.snoc z y) = centeredScatter 𝕜 z +
      ((n : 𝕜) / ((n : 𝕜) + 1)) •
        rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z) := by
  have hn1 : (n : 𝕜) + 1 ≠ 0 := by
    have : ((n + 1 : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    push_cast at this
    exact this
  set m := finiteMean 𝕜 z with hm
  set δ := y - m with hδ
  set c : 𝕜 := ((n : 𝕜) + 1)⁻¹ with hc
  have hconjc : (starRingEnd 𝕜) c = c := by
    simp [hc]
  have hmean' : finiteMean 𝕜 (Fin.snoc z y) = m + c • δ := finiteMean_append 𝕜 z y
  have hzero : ∑ i, (z i - m) = 0 := by
    rw [hm]; exact sum_sub_finiteMean_eq_zero 𝕜 z
  apply ContinuousLinearMap.ext
  intro x
  have hterm : ∀ a : E,
      inner 𝕜 (a - c • δ) x • (a - c • δ) =
        inner 𝕜 a x • a - inner 𝕜 a x • (c • δ) - (c * inner 𝕜 δ x) • a +
          (c * (c * inner 𝕜 δ x)) • δ := by
    intro a
    rw [inner_sub_left, inner_smul_left, hconjc]
    module
  have hzero' : ∑ i, inner 𝕜 (z i - m) x = 0 := by
    rw [← sum_inner, hzero, inner_zero_left]
  simp only [centeredScatter, sum_apply, add_apply,
    smul_apply, rankOne_apply]
  rw [hmean', Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hres : ∀ i : Fin n, z i - (m + c • δ) = (z i - m) - c • δ := fun i => by
    rw [sub_add_eq_sub_sub]
  have hlast : y - (m + c • δ) = δ - c • δ := by
    rw [sub_add_eq_sub_sub, ← hδ]
  calc (∑ i, inner 𝕜 (z i - (m + c • δ)) x • (z i - (m + c • δ))) +
        inner 𝕜 (y - (m + c • δ)) x • (y - (m + c • δ))
      = (∑ i, (inner 𝕜 (z i - m) x • (z i - m) - inner 𝕜 (z i - m) x • (c • δ) -
            (c * inner 𝕜 δ x) • (z i - m) + (c * (c * inner 𝕜 δ x)) • δ)) +
          (inner 𝕜 δ x • δ - inner 𝕜 δ x • (c • δ) - (c * inner 𝕜 δ x) • δ +
            (c * (c * inner 𝕜 δ x)) • δ) := by
        rw [hlast, hterm δ]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by rw [hres i, hterm (z i - m)]
    _ = ((∑ i, inner 𝕜 (z i - m) x • (z i - m)) -
          (∑ i, inner 𝕜 (z i - m) x) • (c • δ) -
          (c * inner 𝕜 δ x) • (∑ i, (z i - m)) + (n : 𝕜) • ((c * (c * inner 𝕜 δ x)) • δ)) +
          (inner 𝕜 δ x • δ - inner 𝕜 δ x • (c • δ) - (c * inner 𝕜 δ x) • δ +
            (c * (c * inner 𝕜 δ x)) • δ) := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_smul, ← Finset.smul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Nat.cast_smul_eq_nsmul 𝕜]
    _ = (∑ i, inner 𝕜 (z i - m) x • (z i - m)) +
          ((n : 𝕜) / ((n : 𝕜) + 1)) • (inner 𝕜 δ x • δ) := by
        rw [hzero', hzero, zero_smul, smul_zero, sub_zero, sub_zero]
        match_scalars
        all_goals simp only [hc]
        all_goals field_simp
        all_goals ring

/-- The scatter quadratic form is the sum of squared centered inner products. -/
theorem re_inner_centeredScatter_self {n : ℕ} (z : Fin n → E) (x : E) :
    RCLike.re (inner 𝕜 (centeredScatter 𝕜 z x) x) =
      ∑ i, ‖inner 𝕜 (z i - finiteMean 𝕜 z) x‖ ^ 2 := by
  have h1 : inner 𝕜 (centeredScatter 𝕜 z x) x =
      ((∑ i, ‖inner 𝕜 (z i - finiteMean 𝕜 z) x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [centeredScatter, sum_apply, sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rankOne_apply, inner_smul_left, RCLike.conj_mul]
  rw [h1, RCLike.ofReal_re]

/-- The centered scatter operator is positive. -/
theorem centeredScatter_isPositive {n : ℕ} (z : Fin n → E) :
    (centeredScatter 𝕜 z).IsPositive := by
  constructor
  · intro u v
    simp only [centeredScatter, ContinuousLinearMap.toLinearMap_sum, LinearMap.sum_apply,
      ContinuousLinearMap.coe_coe, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rankOne_apply, rankOne_apply, inner_smul_left,
      inner_smul_right, inner_conj_symm]
    ring
  · intro u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, re_inner_centeredScatter_self]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- Appending a point can only increase the centered scatter in Löwner order. -/
theorem centeredScatter_le_append {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter 𝕜 z ≤ centeredScatter 𝕜 (Fin.snoc z y) := by
  rw [ContinuousLinearMap.le_def, centeredScatter_append, add_sub_cancel_left]
  set δ := y - finiteMean 𝕜 z with hδ
  have hcoef : (starRingEnd 𝕜) ((n : 𝕜) / ((n : 𝕜) + 1)) = (n : 𝕜) / ((n : 𝕜) + 1) := by
    simp
  have hre : ∀ u : E, RCLike.re (inner 𝕜
      ((((n : 𝕜) / ((n : 𝕜) + 1)) • rankOne 𝕜 δ δ) u) u) =
      ((n : ℝ) / ((n : ℝ) + 1)) * ‖inner 𝕜 δ u‖ ^ 2 := by
    intro u
    rw [smul_apply, inner_smul_left, hcoef,
      rankOne_apply, inner_smul_left, RCLike.conj_mul]
    have hcast : ((n : 𝕜) / ((n : 𝕜) + 1)) = (((n : ℝ) / ((n : ℝ) + 1) : ℝ) : 𝕜) := by
      push_cast
      rfl
    rw [hcast, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  constructor
  · intro u v
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_coe,
      inner_smul_left, inner_smul_right, hcoef, rankOne_apply]
    rw [inner_conj_symm]
    ring
  · intro u
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, hre u]
    positivity

/-- Quadratic-form version of the add-one identity: adding one point adds the exact
nonnegative correction `n/(n+1) ⟪y - mean z, x⟫²` to the scatter quadratic form. -/
theorem re_inner_centeredScatter_append {n : ℕ} (z : Fin n → E) (y x : E) :
    RCLike.re (inner 𝕜 (centeredScatter 𝕜 (Fin.snoc z y) x) x) =
      RCLike.re (inner 𝕜 (centeredScatter 𝕜 z x) x) +
        (n : ℝ) / ((n : ℝ) + 1) * ‖inner 𝕜 (y - finiteMean 𝕜 z) x‖ ^ 2 := by
  rw [centeredScatter_append, add_apply, inner_add_left, map_add]
  congr 1
  set δ := y - finiteMean 𝕜 z with hδ
  have hcoef : (starRingEnd 𝕜) ((n : 𝕜) / ((n : 𝕜) + 1)) = (n : 𝕜) / ((n : 𝕜) + 1) := by
    simp
  rw [smul_apply, inner_smul_left, hcoef,
    rankOne_apply, inner_smul_left, RCLike.conj_mul]
  have hcast : ((n : 𝕜) / ((n : 𝕜) + 1)) = (((n : ℝ) / ((n : ℝ) + 1) : ℝ) : 𝕜) := by
    push_cast
    rfl
  rw [hcast, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

end TauCeti
