/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.FiniteMean
public import TauCeti.Analysis.InnerProductSpace.Frame

/-!
# The centered scatter operator of a finite family

Let `z : ι → E` be a finite family of points in an inner product space over `ℝ` or `ℂ`, with
mean `m = TauCeti.finiteMean 𝕜 z`. Its (unnormalized) *centered scatter operator* is

`S(z) = ∑ᵢ (zᵢ - m) ⊗ (zᵢ - m)`, that is `S(z) x = ∑ᵢ ⟪zᵢ - m, x⟫ (zᵢ - m)`.

Divided by the number of points it is the empirical covariance operator of the sample `z`. It is
the frame operator of the centered family `zᵢ - m`, so it is positive with quadratic form
`Re ⟪S(z) x, x⟫ = ∑ᵢ ‖⟪zᵢ - m, x⟫‖²`.

The main identity is the exact rank-one update when a point `y` is appended to a family `z` of
`n` points: writing `(z, y)` for the extended family `Fin.snoc z y`,

`S(z, y) = S(z) + n / (n + 1) · (y - m) ⊗ (y - m)`,

so the scatter operator only grows, in the Loewner order, as points are added. It comes from the
decomposition of the scatter about an arbitrary centre `p`,
`∑ᵢ (zᵢ - p) ⊗ (zᵢ - p) = S(z) + card ι · (m - p) ⊗ (m - p)` (the König–Huygens identity),
together with the update `m + (n + 1)⁻¹ (y - m)` of the mean (`TauCeti.finiteMean_snoc`).

## Main declarations

* `TauCeti.centeredScatter`: the centered scatter operator `S(z)`.
* `TauCeti.toLinearMap_centeredScatter`: `S(z)` is the frame operator of the centered family.
* `TauCeti.sum_rankOne_sub_eq_centeredScatter_add`: the scatter about an arbitrary centre.
* `TauCeti.re_inner_centeredScatter_apply_self`, `TauCeti.isPositive_centeredScatter`: the
  quadratic form of `S(z)`, and its positivity.
* `TauCeti.centeredScatter_snoc`: the rank-one update when a point is appended.
* `TauCeti.re_inner_centeredScatter_snoc_apply_self`: the corresponding update of the quadratic
  form.
* `TauCeti.centeredScatter_le_centeredScatter_snoc`: appending a point increases `S(z)` in the
  Loewner order.

## References

* K. V. Mardia, J. T. Kent, J. M. Bibby, *Multivariate Analysis*, Academic Press (1979), §1.4
  (the sample covariance matrix).
-/

public section

open Finset InnerProductSpace
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

variable (𝕜) in
/-- The centered scatter operator `∑ᵢ (zᵢ - m) ⊗ (zᵢ - m)` of a finite family `z`, where
`m = finiteMean 𝕜 z` is its mean: it sends `x` to `∑ᵢ ⟪zᵢ - m, x⟫ (zᵢ - m)`. -/
noncomputable def centeredScatter (z : ι → E) : E →L[𝕜] E :=
  ∑ i, rankOne 𝕜 (z i - finiteMean 𝕜 z) (z i - finiteMean 𝕜 z)

theorem centeredScatter_def (z : ι → E) :
    centeredScatter 𝕜 z = ∑ i, rankOne 𝕜 (z i - finiteMean 𝕜 z) (z i - finiteMean 𝕜 z) :=
  (rfl)

@[simp]
theorem centeredScatter_apply (z : ι → E) (x : E) :
    centeredScatter 𝕜 z x = ∑ i, ⟪z i - finiteMean 𝕜 z, x⟫_𝕜 • (z i - finiteMean 𝕜 z) := by
  simp only [centeredScatter_def, _root_.sum_apply, rankOne_apply]

/-- The centered scatter operator is the frame operator of the centered family `zᵢ - m`,
where `m` is the mean of `z`. -/
theorem toLinearMap_centeredScatter (z : ι → E) :
    (centeredScatter 𝕜 z : E →ₗ[𝕜] E) = frameOperator 𝕜 fun i ↦ z i - finiteMean 𝕜 z := by
  ext x
  simp

/-- **The scatter about an arbitrary centre** (König–Huygens). Measured from a point `p`, the
scatter of a finite family exceeds the centered scatter by `card ι` times the rank-one operator
of the displacement `m - p` of the mean. -/
theorem sum_rankOne_sub_eq_centeredScatter_add (z : ι → E) (p : E) :
    ∑ i, rankOne 𝕜 (z i - p) (z i - p) =
      centeredScatter 𝕜 z +
        (Fintype.card ι : 𝕜) • rankOne 𝕜 (finiteMean 𝕜 z - p) (finiteMean 𝕜 z - p) := by
  rw [centeredScatter_def]
  set m := finiteMean 𝕜 z
  have hsum : ∑ i, (z i - m) = 0 := sum_sub_finiteMean z
  have hz : ∀ i, z i - p = (z i - m) + (m - p) := fun i ↦ by abel
  -- Expand `zᵢ - p = (zᵢ - m) + (m - p)` bilinearly: each cross term sums to a rank-one operator
  -- with `∑ᵢ (zᵢ - m) = 0` in one slot, so it vanishes.
  simp_rw [hz, map_add, add_apply, sum_add_distrib, ← _root_.sum_apply, ← map_sum, hsum]
  simp [← Nat.cast_smul_eq_nsmul 𝕜]

/-- **The quadratic form of the centered scatter operator.**
`Re ⟪S(z) x, x⟫ = ∑ᵢ ‖⟪zᵢ - m, x⟫‖²`, where `m` is the mean of `z`. -/
theorem re_inner_centeredScatter_apply_self (z : ι → E) (x : E) :
    RCLike.re ⟪centeredScatter 𝕜 z x, x⟫_𝕜 = ∑ i, ‖⟪z i - finiteMean 𝕜 z, x⟫_𝕜‖ ^ 2 := by
  rw [← ContinuousLinearMap.coe_coe, toLinearMap_centeredScatter,
    re_inner_frameOperator_apply_self]

/-- The centered scatter operator is positive. -/
theorem isPositive_centeredScatter (z : ι → E) : (centeredScatter 𝕜 z).IsPositive := by
  rw [← ContinuousLinearMap.isPositive_toLinearMap_iff, toLinearMap_centeredScatter]
  exact isPositive_frameOperator _

/-- The weight `n / (n + 1)` of the rank-one update is real. -/
private theorem natCast_div_natCast_add_one_eq_ofReal (n : ℕ) :
    (n : 𝕜) / ((n : 𝕜) + 1) = ((n / (n + 1) : ℝ) : 𝕜) := by
  simp only [RCLike.ofReal_div, RCLike.ofReal_add, RCLike.ofReal_natCast, RCLike.ofReal_one]

/-- **Appending a point to a family.** If `y` is appended to a family `z` of `n` points with
mean `m`, the centered scatter operator grows by the rank-one operator
`n / (n + 1) · (y - m) ⊗ (y - m)`. -/
theorem centeredScatter_snoc {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter 𝕜 (Fin.snoc z y : Fin (n + 1) → E) =
      centeredScatter 𝕜 z +
        ((n : 𝕜) / ((n : 𝕜) + 1)) • rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z) := by
  set m := finiteMean 𝕜 z
  set d := y - m with hd
  have hn : (n : 𝕜) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  -- The new mean is `m + c • d` with `c = (n + 1)⁻¹`; measured from it, the old points are
  -- displaced by `(-c) • d` and the new point by `(1 - c) • d`.
  have hmean : finiteMean 𝕜 (Fin.snoc z y : Fin (n + 1) → E) = m + ((n : 𝕜) + 1)⁻¹ • d :=
    finiteMean_snoc z y
  have hold : m - (m + ((n : 𝕜) + 1)⁻¹ • d) = (-((n : 𝕜) + 1)⁻¹) • d := by
    rw [neg_smul]; abel
  have hnew : y - (m + ((n : 𝕜) + 1)⁻¹ • d) = (1 - ((n : 𝕜) + 1)⁻¹) • d := by
    rw [sub_smul, one_smul, hd]; abel
  rw [centeredScatter_def, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [hmean, sum_rankOne_sub_eq_centeredScatter_add, Fintype.card_fin, hold, hnew, add_assoc]
  simp only [map_smul, map_smulₛₗ, smul_apply, smul_smul, ← add_smul, map_neg, map_sub, map_one,
    map_inv₀, map_add, map_natCast]
  congr 2
  field_simp
  ring

/-- **The quadratic form after appending a point.** Appending `y` to a family `z` of `n` points
with mean `m` adds `n / (n + 1) · ‖⟪y - m, x⟫‖²` to the quadratic form of the centered scatter
operator. -/
theorem re_inner_centeredScatter_snoc_apply_self {n : ℕ} (z : Fin n → E) (y x : E) :
    RCLike.re ⟪centeredScatter 𝕜 (Fin.snoc z y : Fin (n + 1) → E) x, x⟫_𝕜 =
      RCLike.re ⟪centeredScatter 𝕜 z x, x⟫_𝕜 +
        n / (n + 1) * ‖⟪y - finiteMean 𝕜 z, x⟫_𝕜‖ ^ 2 := by
  rw [centeredScatter_snoc, natCast_div_natCast_add_one_eq_ofReal]
  simp only [add_apply, smul_apply, rankOne_apply, inner_add_left, inner_smul_left,
    RCLike.conj_ofReal, RCLike.conj_mul, map_add]
  norm_cast

/-- **Monotonicity of the scatter.** Appending a point to a family increases its centered scatter
operator in the Loewner order. -/
theorem centeredScatter_le_centeredScatter_snoc {n : ℕ} (z : Fin n → E) (y : E) :
    centeredScatter 𝕜 z ≤ centeredScatter 𝕜 (Fin.snoc z y : Fin (n + 1) → E) := by
  rw [ContinuousLinearMap.le_def, centeredScatter_snoc, add_sub_cancel_left]
  refine (isPositive_rankOne_self _).smul_of_nonneg ?_
  rw [natCast_div_natCast_add_one_eq_ofReal]
  exact RCLike.ofReal_nonneg.mpr (by positivity)

end TauCeti
