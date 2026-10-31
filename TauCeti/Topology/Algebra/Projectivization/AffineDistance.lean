/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Reciprocal affine distance on projective space

Fix a standard affine open `U_i = {[v] | v i ≠ 0}` of `ℙ 𝕜 (Fin (n + 1) → 𝕜)`, over `ℝ` or `ℂ`,
and a centre `a` in the Euclidean space `𝕜ⁿ`. On `U_i` the squared Euclidean distance
`ρ(x) = dist (z(x), a)²` from the centre, read in the affine chart `z = affineChart i`, is a
proper exhaustion of `U_i`. Its reciprocal transform `F = (1 + ρ)⁻¹`, extended by `0` on the
hyperplane `H_i = {v i = 0}`, is `Projectivization.affineChartInvOneAddDistSq i a`.

The main point is that `F` is continuous on the whole projective space: as a point approaches the
hyperplane its affine coordinates leave every bounded set, so `ρ` tends to infinity and `F` to `0`.
Concretely, in homogeneous coordinates
`F [v] = ‖v i‖² / (‖v i‖² + ‖v' - v i • a‖²)`, where `v'` lists the other coordinates of `v`
(`Projectivization.affineChartInvOneAddDistSq_mk`). The denominator vanishes only at `v = 0` and
the expression is invariant under scaling, so it descends to a continuous function.

Consequently `F` takes values in `[0, 1]`, vanishes exactly on the hyperplane, equals `1` exactly at
the centre, and for every `ε > 0` the superlevel set `{ε ≤ F}` is a compact subset of `U_i`: it is
the image under the inverse chart of the closed ball of radius `√(ε⁻¹ - 1)` about `a`. For a closed
subset `X` of projective space, `F` therefore restricts to a continuous function on `X` which
vanishes exactly on `X ∩ H_i` and whose positive superlevel sets are compact subsets of `X \ H_i`.
This is how Morse theory of a squared-distance exhaustion of the affine part `X \ H_i` is turned
into a statement about the compact pair `(X, X ∩ H_i)`: the regular bands `{ε ≤ F ≤ c}` are the
compact bands `{1/c - 1 ≤ ρ ≤ 1/ε - 1}` of the exhaustion, traversed in the opposite direction.

## Main declarations

* `Projectivization.affineChartInvOneAddDistSq i a`: the function `F`.
* `Projectivization.affineChartInvOneAddDistSq_mk`: its formula in homogeneous coordinates.
* `Projectivization.continuous_affineChartInvOneAddDistSq`: `F` is continuous.
* `Projectivization.affineChartInvOneAddDistSq_eq_zero_iff`: `F` vanishes exactly on the
  hyperplane.
* `Projectivization.setOf_le_affineChartInvOneAddDistSq`: superlevel sets are images of closed
  balls under the inverse chart.
* `Projectivization.isCompact_setOf_le_affineChartInvOneAddDistSq` and
  `Projectivization.setOf_le_affineChartInvOneAddDistSq_subset_affineOpen`: positive superlevel
  sets are compact subsets of the affine open.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7.
-/

public section

open Metric Set
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1)) (a : EuclideanSpace 𝕜 (Fin n))

/-- The reciprocal transform `(1 + ρ)⁻¹` of the squared Euclidean distance `ρ` from a centre `a`,
read in the standard affine chart at `i`, extended by `0` on the hyperplane where the `i`-th
homogeneous coordinate vanishes. -/
noncomputable def affineChartInvOneAddDistSq : ℙ 𝕜 (Fin (n + 1) → 𝕜) → ℝ :=
  (affineOpen i).indicator fun x ↦ (1 + dist (WithLp.toLp 2 (affineChart i x)) a ^ 2)⁻¹

variable {i a}

/-- On the affine open, the function is the reciprocal transform of the squared distance in the
affine chart. -/
theorem affineChartInvOneAddDistSq_of_mem {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} (hx : x ∈ affineOpen i) :
    affineChartInvOneAddDistSq i a x = (1 + dist (WithLp.toLp 2 (affineChart i x)) a ^ 2)⁻¹ :=
  indicator_of_mem hx _

/-- On the hyperplane where the `i`-th homogeneous coordinate vanishes, the function is `0`. -/
theorem affineChartInvOneAddDistSq_of_notMem {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)}
    (hx : x ∉ affineOpen i) : affineChartInvOneAddDistSq i a x = 0 :=
  indicator_of_notMem hx _

variable (i a)

/-- The function read in the affine chart is `z ↦ (1 + dist (z, a)²)⁻¹`. -/
theorem affineChartInvOneAddDistSq_affineChart_symm (z : Fin n → 𝕜) :
    affineChartInvOneAddDistSq i a ((affineChart i).symm z) =
      (1 + dist (WithLp.toLp 2 z) a ^ 2)⁻¹ := by
  rw [affineChartInvOneAddDistSq_of_mem (by simp), (affineChart i).right_inv (by simp)]

/-- **The function in homogeneous coordinates.** For a nonzero vector `v`, with `v'` its
coordinates other than the `i`-th one,
`F [v] = ‖v i‖² / (‖v i‖² + ‖v' - v i • a‖²)`. Both sides vanish when `v i = 0`. -/
@[simp]
theorem affineChartInvOneAddDistSq_mk (v : Fin (n + 1) → 𝕜) (hv : v ≠ 0) :
    affineChartInvOneAddDistSq i a (mk 𝕜 v hv) = ‖v i‖ ^ 2 /
      (‖v i‖ ^ 2 + ‖WithLp.toLp 2 (fun j ↦ v (i.succAbove j)) - v i • a‖ ^ 2) := by
  by_cases h : v i = 0
  · rw [affineChartInvOneAddDistSq_of_notMem (by simpa using h), h]
    simp
  rw [affineChartInvOneAddDistSq_of_mem (by simpa using h), affineChart_mk, dist_eq_norm]
  -- The chart coordinates minus the centre are `(v i)⁻¹ • (v' - v i • a)`.
  have hsub : WithLp.toLp 2 (fun j ↦ v (i.succAbove j) / v i) - a =
      (v i)⁻¹ • (WithLp.toLp 2 (fun j ↦ v (i.succAbove j)) - v i • a) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ h, one_smul, ← WithLp.toLp_smul]
    congr 2
    ext j
    simp [div_eq_inv_mul]
  have hn : 0 < ‖v i‖ := norm_pos_iff.2 h
  rw [hsub, norm_smul, norm_inv]
  field_simp

/-- The denominator of the homogeneous formula vanishes only at the zero vector. -/
private theorem norm_sq_add_norm_sq_sub_smul_ne_zero (v : Fin (n + 1) → 𝕜) (hv : v ≠ 0) :
    ‖v i‖ ^ 2 + ‖WithLp.toLp 2 (fun j ↦ v (i.succAbove j)) - v i • a‖ ^ 2 ≠ 0 := by
  intro h0
  have hi : v i = 0 := by
    simpa using (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).1 h0 |>.1
  have hrest : ∀ j, v (i.succAbove j) = 0 := by
    have h := (add_eq_zero_iff_of_nonneg (by positivity) (by positivity)).1 h0 |>.2
    rw [hi, zero_smul, sub_zero, sq_eq_zero_iff, norm_eq_zero, WithLp.toLp_eq_zero] at h
    exact congr_fun h
  refine hv (funext fun k ↦ ?_)
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i k
  exacts [hi, hrest j]

/-- **The reciprocal affine distance is continuous on projective space**, including at the
hyperplane where it is extended by `0`. -/
theorem continuous_affineChartInvOneAddDistSq :
    Continuous (affineChartInvOneAddDistSq i a) := by
  rw [continuous_iff]
  have hF : affineChartInvOneAddDistSq i a ∘ mk' 𝕜 = fun v : {v : Fin (n + 1) → 𝕜 // v ≠ 0} ↦
      ‖v.1 i‖ ^ 2 /
        (‖v.1 i‖ ^ 2 + ‖WithLp.toLp 2 (fun j ↦ v.1 (i.succAbove j)) - v.1 i • a‖ ^ 2) :=
    funext fun v ↦ by simp only [Function.comp_apply, mk'_eq_mk, affineChartInvOneAddDistSq_mk]
  rw [hF]
  have hi : Continuous fun v : {v : Fin (n + 1) → 𝕜 // v ≠ 0} ↦ v.1 i :=
    (continuous_apply i).comp continuous_subtype_val
  have hrest : Continuous fun v : {v : Fin (n + 1) → 𝕜 // v ≠ 0} ↦
      WithLp.toLp 2 (fun j ↦ v.1 (i.succAbove j)) - v.1 i • a :=
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦
      (continuous_apply _).comp continuous_subtype_val)).sub (hi.smul continuous_const)
  exact (hi.norm.pow 2).div ((hi.norm.pow 2).add (hrest.norm.pow 2)) fun v ↦
    norm_sq_add_norm_sq_sub_smul_ne_zero i a v.1 v.2

/-- The reciprocal affine distance is nonnegative. -/
theorem affineChartInvOneAddDistSq_nonneg (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    0 ≤ affineChartInvOneAddDistSq i a x :=
  indicator_nonneg (fun _ _ ↦ by positivity) x

/-- The reciprocal affine distance is at most `1`. -/
theorem affineChartInvOneAddDistSq_le_one (x : ℙ 𝕜 (Fin (n + 1) → 𝕜)) :
    affineChartInvOneAddDistSq i a x ≤ 1 :=
  indicator_apply_le' (fun _ ↦ inv_le_one_of_one_le₀ (le_add_of_nonneg_right (sq_nonneg _)))
    fun _ ↦ zero_le_one

/-- The reciprocal affine distance is positive exactly on the affine open. -/
@[simp]
theorem affineChartInvOneAddDistSq_pos_iff {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} :
    0 < affineChartInvOneAddDistSq i a x ↔ x ∈ affineOpen i := by
  refine ⟨fun h ↦ by_contra fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [affineChartInvOneAddDistSq_of_notMem hx] at h
    exact h.false
  · rw [affineChartInvOneAddDistSq_of_mem hx]
    positivity

/-- **The reciprocal affine distance vanishes exactly on the hyperplane** where the `i`-th
homogeneous coordinate vanishes. -/
@[simp]
theorem affineChartInvOneAddDistSq_eq_zero_iff {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} :
    affineChartInvOneAddDistSq i a x = 0 ↔ x ∉ affineOpen i := by
  rw [← affineChartInvOneAddDistSq_pos_iff i a, not_lt]
  exact ⟨le_of_eq, fun h ↦ h.antisymm (affineChartInvOneAddDistSq_nonneg i a x)⟩

/-- The reciprocal affine distance attains its maximum `1` exactly at the centre. -/
@[simp]
theorem affineChartInvOneAddDistSq_eq_one_iff {x : ℙ 𝕜 (Fin (n + 1) → 𝕜)} :
    affineChartInvOneAddDistSq i a x = 1 ↔ x = (affineChart i).symm (WithLp.ofLp a) := by
  constructor
  · intro h
    have hx : x ∈ affineOpen i := by
      rw [← affineChartInvOneAddDistSq_pos_iff i a, h]
      exact one_pos
    rw [affineChartInvOneAddDistSq_of_mem hx, inv_eq_one, add_eq_left] at h
    have hz : affineChart i x = WithLp.ofLp a := by
      rw [← (WithLp.toLp_injective 2).eq_iff, WithLp.toLp_ofLp]
      simpa using h
    rw [← hz, (affineChart i).left_inv (by simpa using hx)]
  · rintro rfl
    rw [affineChartInvOneAddDistSq_affineChart_symm]
    simp

/-- **Superlevel sets of the reciprocal affine distance.** For `ε > 0`, the set `{ε ≤ F}` is the
image under the inverse affine chart of the closed Euclidean ball about the centre of squared
radius `ε⁻¹ - 1`. -/
theorem setOf_le_affineChartInvOneAddDistSq {ε : ℝ} (hε : 0 < ε) :
    {x | ε ≤ affineChartInvOneAddDistSq i a x} =
      (affineChart i).symm '' {z | dist (WithLp.toLp 2 z) a ^ 2 ≤ ε⁻¹ - 1} := by
  ext x
  constructor
  · intro hx
    have hmem : x ∈ affineOpen i :=
      (affineChartInvOneAddDistSq_pos_iff i a).1 (hε.trans_le hx)
    refine ⟨affineChart i x, ?_, (affineChart i).left_inv (by simpa using hmem)⟩
    rw [mem_ofPred_eq, affineChartInvOneAddDistSq_of_mem hmem,
      le_inv_comm₀ hε (by positivity)] at hx
    simp only [mem_ofPred_eq]
    linarith
  · rintro ⟨z, hz, rfl⟩
    rw [mem_ofPred_eq, affineChartInvOneAddDistSq_affineChart_symm,
      le_inv_comm₀ hε (by positivity)]
    simp only [mem_ofPred_eq] at hz
    linarith

/-- For `ε > 0`, the superlevel set `{ε ≤ F}` lies in the affine open. -/
theorem setOf_le_affineChartInvOneAddDistSq_subset_affineOpen {ε : ℝ} (hε : 0 < ε) :
    {x | ε ≤ affineChartInvOneAddDistSq i a x} ⊆ affineOpen i := fun _ hx ↦
  (affineChartInvOneAddDistSq_pos_iff i a).1 (hε.trans_le hx)

/-- Every superlevel set `{ε ≤ F}` is compact; for `ε > 0` it lies in the affine open by
`Projectivization.setOf_le_affineChartInvOneAddDistSq_subset_affineOpen`. -/
theorem isCompact_setOf_le_affineChartInvOneAddDistSq (ε : ℝ) :
    IsCompact {x | ε ≤ affineChartInvOneAddDistSq i a x} :=
  (isClosed_le continuous_const (continuous_affineChartInvOneAddDistSq i a)).isCompact

end Projectivization
