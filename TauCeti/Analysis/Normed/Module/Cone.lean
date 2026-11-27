/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Topology.Algebra.Module.Cone
import TauCeti.Topology.MetricSpace.CoboundedImage

/-!
# Rapid decay in conic neighbourhoods

Let `Γ` be an open subset of a real normed space which is closed under multiplication by positive
reals, such as an open cone of frequencies in microlocal analysis. Every `ξ ∈ Γ` lies in a smaller
open cone `Γ'` which stays inside `Γ` after perturbations proportional to the size of the
frequency: for some `c > 0`, the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in `Γ`.
Take `Γ'` to be the cone over a small ball about `ξ`. Such a `Γ'` can also be chosen inside a
closed cone `F` whose nonzero elements lie in `Γ`: the cones over a small open and the
concentric closed ball of directions.

This is the geometric input to the localization of rapid decay in cones. If `F` grows at most
polynomially and decays rapidly on `Γ`, and the coefficients `a i` decay rapidly in `‖v i‖`, then
the superposition `∑ i, a i • F (η - v i)` decays rapidly on `Γ'`: the shifts with
`‖v i‖ ≤ c ‖η‖` evaluate `F` at points of `Γ` of size comparable to `‖η‖`, and the remaining
shifts have `‖v i‖` comparable to `‖η‖`, where the decay of the coefficients wins. Applied to the
Fourier coefficients of a smooth function, this shows that rapid decay of a localized Fourier
transform in a cone survives multiplication of the cutoff by a smooth function.

Rapid decay in a cone also survives multiplication by a function of polynomial growth in other
variables: if `g` decays rapidly on a cone around `a ζ₀ ≠ 0`, then `g (a ζ) h (b ζ)` decays rapidly
on the cone of those `ζ` with `a ζ` in that cone and `‖b ζ‖ < c ‖a ζ‖`. This is how the localized
Fourier transform of a tensor product inherits the decay of one of its factors.

In a proper space, if every unit vector of a closed cone lies in an open cone, finitely many of
these cones cover the nonzero vectors of the closed cone, by compactness of the unit sphere. This
is how conditions imposed direction by direction combine into one condition on a whole closed
cone of frequencies. By the same compactness, a continuous linear map `L` with no zeros on the
nonzero vectors of a closed cone `V` is bounded below there, `‖η‖ ≤ c ‖L η‖`, and maps `V` to a
closed cone. This is how a closed cone of frequencies is transported along the transpose of a
linear map.

Applying a linear automorphism `B`, the image of a smaller cone also separates: there are an open
cone `Γ'` around `B η₀` and `c > 0` such that `B ζ` is at distance at least `c (‖ξ‖ + ‖ζ‖)` from
every `ξ ∈ Γ'` whenever `ζ ∉ Γ` or `‖ζ‖ < c ‖ξ‖`. This is how a cone in which a localized Fourier
transform decays is transported along the transposed derivative of a change of variables.

Similarly, for a continuous linear map `p` on a proper space and an open cone `Γ` containing the
nonzero vectors that `p` maps to the ray through `ξ₀ ≠ 0`, the image `p ζ` of every `ζ ∉ Γ` stays at
distance at least `c (‖ξ‖ + ‖ζ‖)` from every `ξ` in an open cone `Γ'` around `ξ₀`. Then if `F`
decays rapidly on `Γ` and `g` decays rapidly everywhere, `g (ξ - p ζ) F ζ` decays rapidly in
`ξ ∈ Γ'` and `ζ` jointly. This is how a cone in which a localized Fourier transform decays is
transported along the transpose of an injective linear map, such as the inclusion `x ↦ (x, 0)`.

Conversely, decay forbids constancy: a function with `(1 + ‖η‖) ‖g η‖` bounded on an open cone
around `ξ ≠ 0` vanishes wherever it is constant along a line `t ↦ t • ξ + w`, since the line
eventually lies in the cone. This is how lower bounds on wave front sets are proved.

## Main results

* `IsOpen.exists_cone_exists_smul_mem`: the open cone over an open set containing `ξ`.
* `IsOpen.exists_cone_closedBall_subset`: an open cone `Γ` containing `ξ` contains a smaller open
  cone `Γ'` containing `ξ` such that `closedBall η (c * ‖η‖) ⊆ Γ` for every `η ∈ Γ'`.
* `IsOpen.exists_isOpen_cone_subset_isClosed_cone`: an open cone `Γ` containing `ξ` contains the
  nonzero elements of a closed cone `F` which contains an open cone `Γ'` containing `ξ`.
* `IsOpen.eq_zero_of_forall_smul_add_eq`: a function with `(1 + ‖η‖) ‖g η‖` bounded on an open
  cone around `ξ ≠ 0` vanishes wherever it is constant along a line `t ↦ t • ξ + w`.
* `IsOpen.exists_pos_setOf_norm_fst_lt_subset`: an open cone of `E × D` containing the nonzero
  vectors of `{0} × D` contains a cone `‖ζ.1‖ < c ‖ζ.2‖` around them.
* `IsOpen.exists_cone_mul_add_le_norm_sub`: for a linear automorphism `B`, an open cone `Γ'`
  around `B η₀` with `c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖` for `ξ ∈ Γ'` and `ζ ∉ Γ` or `‖ζ‖ < c ‖ξ‖`.
* `IsOpen.exists_pos_forall_mul_norm_le_norm_apply_sub_smul`,
  `IsOpen.exists_cone_mul_add_le_norm_apply_sub`: for an open cone `Γ` containing the nonzero
  vectors that `p` maps to the ray through `ξ₀`, `p ζ` stays at distance at least `ε ‖ζ‖` from the
  ray for `ζ ∉ Γ`, and at distance at least `c (‖ξ‖ + ‖ζ‖)` from an open cone `Γ'` around `ξ₀`.
* `TauCeti.exists_one_add_norm_pow_mul_one_add_norm_pow_mul_norm_mul_le`: the joint rapid decay
  of `g (ξ - p ζ) F ζ` in `ξ ∈ Γ'` and `ζ`.
* `TauCeti.mem_of_mem_closure_of_forall_closedBall_subset`: the nonzero points of the closure of
  such a `Γ'` still lie in `Γ`.
* `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum`: decay of order `N` on `Γ'` of a
  superposition of translates of a function decaying at order `N` on `Γ`, with rapidly decreasing
  coefficients, bounded by a weighted `ℓ¹` norm of the coefficients.
* `TauCeti.one_add_norm_pow_mul_norm_le_of_hasSum`: the same decay at a single `η`, for
  coefficients that may depend on `η`, from bounds on the coefficients at large shifts.
* `TauCeti.one_add_norm_pow_mul_norm_apply_sub_le_of_norm_le`,
  `TauCeti.one_add_norm_pow_mul_norm_apply_sub_le_of_lt_norm`: the bounds on a single translate
  `F (η - v)` with a small or a large shift `v`.
* `TauCeti.exists_one_add_norm_pow_mul_norm_apply_sub_le`: the pointwise bound behind
  `TauCeti.exists_one_add_norm_pow_mul_norm_le_of_hasSum` and its integral form: for `η ∈ Γ'`
  and every shift `θ`, `(1 + ‖η‖) ^ N (1 + ‖η - θ‖) ^ M ‖F (η - θ)‖` is at most a constant times a
  power of `1 + ‖θ‖`.
* `TauCeti.exists_cone_decay_mul`: if `g` decays rapidly on an open cone around `a ζ₀ ≠ 0` and `h`
  grows at most polynomially, then `ζ ↦ g (a ζ) * h (b ζ)` decays rapidly on an open cone around
  `ζ₀`, provided `‖ζ‖ ≤ ‖a ζ‖ + ‖b ζ‖`.
* `TauCeti.exists_finset_diff_singleton_subset_biUnion`: if every unit vector of a closed cone `V`
  lies in an open cone, finitely many of these cones cover the nonzero vectors of `V`;
  `TauCeti.exists_finset_compl_singleton_subset_biUnion` is the case `V = E`.
* `ContinuousLinearMap.exists_norm_le_mul_norm_apply_of_isClosed_cone_of_apply_eq_zero_imp`,
  `ContinuousLinearMap.isClosed_image_of_isClosed_cone_of_apply_eq_zero_imp`: a continuous linear
  map without zeros on the nonzero vectors of a closed cone is bounded below on it and maps it to
  a closed set.
* `TauCeti.exists_forall_le_of_diff_singleton_subset_biUnion`: bounds on finitely many sets
  covering the nonzero elements of `V` combine into one bound on `V`.
* `TauCeti.exists_finset_subset_biUnion_interior_and_isOpen_cone`: finitely many of given
  neighbourhoods of the points of a compact set cover it, and the corresponding open cones
  intersect in an open cone.
* `IsClosed.zero_mem_of_smul_mem`: a nonempty closed set closed under multiplication by positive
  reals contains `0`.
* `TauCeti.forall_smul_mem_neg`, `TauCeti.forall_smul_mem_compl`, `TauCeti.forall_smul_mem_add`,
  `TauCeti.forall_smul_mem_insert_zero`: the negative and the complement of a set closed under
  multiplication by positive reals, the sum of two such sets, and such a set with `0` adjoined, are
  closed under multiplication by positive reals.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, proof of Lemma 8.1.1.
-/

public section

open Metric Set

namespace IsOpen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cone over an open set: if `V` is open and contains `ξ`, there is an open set `Γ`
containing `ξ` and closed under multiplication by positive reals, every element of which is
rescaled by some `t > 0` into `V`. -/
theorem exists_cone_exists_smul_mem {V : Set E} (hV : IsOpen V) {ξ : E} (hξ : ξ ∈ V) :
    ∃ Γ : Set E, IsOpen Γ ∧ ξ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∀ η ∈ Γ, ∃ t : ℝ, 0 < t ∧ t • η ∈ V := by
  set Γ : Set E := ⋃ t ∈ Ioi (0 : ℝ), (t • ·) ⁻¹' V
  have hmem {η : E} : η ∈ Γ ↔ ∃ t : ℝ, 0 < t ∧ t • η ∈ V := by simp [Γ]
  refine ⟨Γ, isOpen_biUnion fun t _ ↦ hV.preimage (continuous_const_smul t),
    hmem.2 ⟨1, one_pos, by simpa using hξ⟩, fun s hs η hη ↦ ?_, fun η ↦ hmem.1⟩
  obtain ⟨t, ht, htη⟩ := hmem.1 hη
  exact hmem.2 ⟨t / s, div_pos ht hs, by rwa [smul_smul, div_mul_cancel₀ _ hs.ne']⟩

/-- An open set `Γ` closed under multiplication by positive reals contains, around each of its
points `ξ`, a smaller open set `Γ'` closed under multiplication by positive reals such that, for
some `c > 0`, the closed ball of radius `c ‖η‖` about every `η ∈ Γ'` lies in `Γ`. -/
theorem exists_cone_closedBall_subset {Γ : Set E} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {ξ : E} (hξ : ξ ∈ Γ) :
    ∃ Γ' : Set E, IsOpen Γ' ∧ ξ ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') ∧
      ∃ c > 0, ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ := by
  obtain ⟨r, hr, hball⟩ := isOpen_iff.1 hΓ ξ hξ
  -- `Γ'` is the cone over the ball of radius `r / 2` about `ξ`.
  obtain ⟨Γ', hΓ'o, hξ', hcone', hmem⟩ :=
    exists_cone_exists_smul_mem (isOpen_ball (x := ξ)) (mem_ball_self (half_pos hr))
  refine ⟨Γ', hΓ'o, hξ', hcone', r / (2 * ‖ξ‖ + r), by positivity, fun η hη ζ hζ ↦ ?_⟩
  obtain ⟨t, ht, htη⟩ := hmem η hη
  rw [mem_ball] at htη
  -- Rescaled by `t`, the point `ζ` is within `r` of `ξ`, since `t ‖η‖ < ‖ξ‖ + r / 2`.
  have hnorm : t * ‖η‖ < ‖ξ‖ + r / 2 := by
    have h := norm_le_norm_add_norm_sub' (t • η) ξ
    rw [norm_smul, Real.norm_of_nonneg ht.le, ← dist_eq_norm] at h
    linarith
  have hζη : t * dist ζ η ≤ r / (2 * ‖ξ‖ + r) * (t * ‖η‖) := by
    rw [mem_closedBall] at hζ
    nlinarith
  have hr' : r / (2 * ‖ξ‖ + r) * (‖ξ‖ + r / 2) = r / 2 := by
    field_simp
  have htζ : t • ζ ∈ Γ := by
    refine hball (mem_ball.2 ?_)
    calc dist (t • ζ) ξ ≤ dist (t • ζ) (t • η) + dist (t • η) ξ := dist_triangle _ _ _
      _ = t * dist ζ η + dist (t • η) ξ := by
        rw [dist_smul₀, Real.norm_of_nonneg ht.le]
      _ < r / 2 + r / 2 := by
        refine add_lt_add_of_le_of_lt ?_ htη
        calc t * dist ζ η ≤ r / (2 * ‖ξ‖ + r) * (t * ‖η‖) := hζη
          _ ≤ r / (2 * ‖ξ‖ + r) * (‖ξ‖ + r / 2) := by gcongr
          _ = r / 2 := hr'
      _ = r := add_halves r
  simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using hcone t⁻¹ (inv_pos.2 ht) _ htζ

/-- **A closed cone between two open cones.** If `Γ` is open, closed under multiplication by
positive reals and contains `ξ`, there are a closed cone `F`, whose nonzero elements lie in `Γ`,
and an open cone `Γ' ⊆ F` containing `ξ`. For `ξ ≠ 0` these are the cones over the closed and the
open ball of directions of a small radius about the direction of `ξ`. -/
theorem exists_isOpen_cone_subset_isClosed_cone {Γ : Set E} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {ξ : E} (hξ : ξ ∈ Γ) :
    ∃ F Γ' : Set E, IsClosed F ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ F, t • η ∈ F) ∧
      (∀ η ∈ F, η ≠ 0 → η ∈ Γ) ∧ IsOpen Γ' ∧ ξ ∈ Γ' ∧
        (∀ t : ℝ, 0 < t → ∀ η ∈ Γ', t • η ∈ Γ') ∧ Γ' ⊆ F := by
  have hdir (η : E) (hη : η ≠ 0) (h : NormedSpace.normalize η ∈ Γ) : η ∈ Γ := by
    simpa [NormedSpace.norm_smul_normalize] using hcone ‖η‖ (norm_pos_iff.2 hη) _ h
  by_cases hξ0 : ξ = 0
  · -- An open cone containing `0` contains every vector.
    subst hξ0
    obtain ⟨r, hr, hball⟩ := isOpen_iff.1 hΓ 0 hξ
    refine ⟨univ, univ, isClosed_univ, fun _ _ _ _ ↦ mem_univ _, fun η _ hη ↦ hdir η hη ?_,
      isOpen_univ, mem_univ _, fun _ _ _ _ ↦ mem_univ _, subset_rfl⟩
    simpa [smul_smul, hr.ne'] using hcone (2 / r) (by positivity) _
      (hball (mem_ball_zero_iff.2 (show ‖(r / 2) • NormedSpace.normalize η‖ < r by
        rw [norm_smul, NormedSpace.norm_normalize_eq_one_iff.2 hη,
          Real.norm_of_nonneg (half_pos hr).le]
        linarith)))
  obtain ⟨ε, hε, hεΓ⟩ := isOpen_iff.1 hΓ (NormedSpace.normalize ξ)
    (hcone _ (inv_pos.2 (norm_pos_iff.2 hξ0)) ξ hξ)
  refine ⟨{η | η = 0 ∨ NormedSpace.normalize η ∈ closedBall (NormedSpace.normalize ξ) (ε / 2)},
    {η | η ≠ 0} ∩ NormedSpace.normalize ⁻¹' ball (NormedSpace.normalize ξ) (ε / 2),
    NormedSpace.isClosed_setOf_eq_zero_or_normalize_mem isClosed_closedBall,
    fun t ht η hη ↦ hη.imp (fun h ↦ by simp [h]) fun h ↦ ?_,
    fun η hη hη0 ↦ hdir η hη0
      (hεΓ (closedBall_subset_ball (half_lt_self hε) (hη.resolve_left hη0))),
    ContinuousOn.isOpen_inter_preimage
      (fun x hx ↦ ContinuousAt.continuousWithinAt (Filter.tendsto_id.normalize hx)) isOpen_ne
      isOpen_ball,
    ⟨hξ0, mem_ball_self (half_pos hε)⟩, fun t ht η hη ↦ ⟨smul_ne_zero ht.ne' hη.1, ?_⟩,
    fun η hη ↦ Or.inr (ball_subset_closedBall hη.2)⟩
  · rwa [mem_ofPred_eq, NormedSpace.normalize_smul_of_pos ht]
  · rw [mem_preimage, NormedSpace.normalize_smul_of_pos ht]
    exact hη.2

/-- If `ζ` is at distance more than `c₂ ‖ν‖` from `ν`, with `0 < c₂ ≤ 1`, then `B ζ` is at
distance at least a fixed multiple of `‖B ν‖ + ‖ζ‖` from `B ν`. -/
private theorem mul_add_le_norm_sub_of_mul_lt_norm_sub (B : E ≃L[ℝ] E) {c₂ : ℝ} (hc₂ : 0 < c₂)
    (hc₂1 : c₂ ≤ 1) {ν ζ : E} (hfar : c₂ * ‖ν‖ < ‖ζ - ν‖) :
    c₂ / (3 * (1 + ‖(B : E →L[ℝ] E)‖) * (1 + ‖(B.symm : E →L[ℝ] E)‖)) * (‖B ν‖ + ‖ζ‖) ≤
      ‖B ζ - B ν‖ := by
  set M := ‖(B : E →L[ℝ] E)‖
  set M' := ‖(B.symm : E →L[ℝ] E)‖
  have hM : 0 ≤ M := norm_nonneg _
  have hM' : 0 ≤ M' := norm_nonneg _
  have hξν : ‖B ν‖ ≤ M * ‖ν‖ := (B : E →L[ℝ] E).le_opNorm ν
  have hζν : ‖ζ - ν‖ ≤ M' * ‖B ζ - B ν‖ := by
    have h : B.symm (B ζ - B ν) = ζ - ν := by simp
    rw [← h]
    exact (B.symm : E →L[ℝ] E).le_opNorm _
  have hζ' : ‖ζ‖ ≤ ‖ζ - ν‖ + ‖ν‖ := by simpa using norm_add_le (ζ - ν) ν
  have h1 : c₂ * ‖B ν‖ ≤ M * ‖ζ - ν‖ :=
    calc c₂ * ‖B ν‖ ≤ c₂ * (M * ‖ν‖) := mul_le_mul_of_nonneg_left hξν hc₂.le
      _ = M * (c₂ * ‖ν‖) := by ring
      _ ≤ M * ‖ζ - ν‖ := mul_le_mul_of_nonneg_left hfar.le hM
  have h2 : c₂ * ‖ζ‖ ≤ 2 * ‖ζ - ν‖ := by nlinarith [norm_nonneg (ζ - ν)]
  have hsum : c₂ * (‖B ν‖ + ‖ζ‖) ≤ 3 * (1 + M) * ‖ζ - ν‖ := by
    nlinarith [h1, h2, norm_nonneg (ζ - ν)]
  calc c₂ / (3 * (1 + M) * (1 + M')) * (‖B ν‖ + ‖ζ‖)
      ≤ 3 * (1 + M) * ‖ζ - ν‖ / (3 * (1 + M) * (1 + M')) := by
        rw [div_mul_eq_mul_div]
        gcongr
    _ = ‖ζ - ν‖ / (1 + M') := by field_simp
    _ ≤ ‖B ζ - B ν‖ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg (B ζ - B ν)]

/-- If `ζ` is small compared with `ξ`, `‖ζ‖ < c ‖ξ‖` with `4 c (1 + ‖B‖) ≤ 1`, then
`c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖`. -/
private theorem mul_add_le_norm_sub_of_norm_lt (B : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hcB : c * (4 * (1 + ‖B‖)) ≤ 1) {ξ ζ : E} (hζ : ‖ζ‖ < c * ‖ξ‖) :
    c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖ := by
  have hM : 0 ≤ ‖B‖ := norm_nonneg _
  have hBζ : ‖B ζ‖ ≤ ‖B‖ * ‖ζ‖ := B.le_opNorm ζ
  have htri : ‖ξ‖ ≤ ‖B ζ - ξ‖ + ‖B ζ‖ := by
    have h := norm_le_norm_add_norm_sub' ξ (B ζ)
    rw [norm_sub_rev] at h
    linarith
  have h1 : ‖B‖ * ‖ζ‖ ≤ ‖B‖ * (c * ‖ξ‖) := mul_le_mul_of_nonneg_left hζ.le hM
  have h2 : c * ‖ζ‖ ≤ c * (c * ‖ξ‖) := mul_le_mul_of_nonneg_left hζ.le hc.le
  have hcoef : c + c * c + ‖B‖ * c ≤ 1 := by nlinarith
  have hX : (c + c * c + ‖B‖ * c) * ‖ξ‖ ≤ ‖ξ‖ := by
    simpa using mul_le_mul_of_nonneg_right hcoef (norm_nonneg ξ)
  nlinarith [h1, h2, hX, htri, hBζ]

/-- **Separation from a cone.** Let `Γ` be an open set closed under multiplication by positive
reals, `η₀ ∈ Γ`, and `B` a continuous linear automorphism. There are an open set `Γ'` closed under
multiplication by positive reals with `B η₀ ∈ Γ'` and `c > 0` such that for every `ξ ∈ Γ'` and
every `ζ` which lies outside `Γ`, or is small compared with `ξ`, the vector `B ζ` is far from `ξ`:
`c (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖` whenever `ζ ∉ Γ` or `‖ζ‖ < c ‖ξ‖`. -/
theorem exists_cone_mul_add_le_norm_sub {Γ : Set E} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {η₀ : E} (hη₀ : η₀ ∈ Γ) (B : E ≃L[ℝ] E) :
    ∃ Γ' : Set E, IsOpen Γ' ∧ B η₀ ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ', t • ξ ∈ Γ') ∧
      ∃ c > 0, ∀ ξ ∈ Γ', ∀ ζ, (ζ ∉ Γ ∨ ‖ζ‖ < c * ‖ξ‖) → c * (‖ξ‖ + ‖ζ‖) ≤ ‖B ζ - ξ‖ := by
  obtain ⟨Γ'', hΓ'', hη₀'', hcone'', c₁, hc₁, hball⟩ := hΓ.exists_cone_closedBall_subset hcone hη₀
  set M := ‖(B : E →L[ℝ] E)‖
  set c₂ := min c₁ 1
  have hc₂ : 0 < c₂ := lt_min hc₁ one_pos
  set c := min (c₂ / (3 * (1 + M) * (1 + ‖(B.symm : E →L[ℝ] E)‖))) (1 / (4 * (1 + M)))
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨B.symm ⁻¹' Γ'', hΓ''.preimage B.symm.continuous, by simpa using hη₀'',
    fun t ht ξ hξ ↦ by simpa using hcone'' t ht _ hξ, c, hc, fun ξ hξ ζ hζ ↦ ?_⟩
  rcases hζ with hζ | hζ
  · -- `ζ` lies outside the ball of radius `c₁ ‖B⁻¹ ξ‖ ≥ c₂ ‖B⁻¹ ξ‖` about `B⁻¹ ξ`.
    have hfar : c₂ * ‖B.symm ξ‖ < ‖ζ - B.symm ξ‖ := by
      by_contra h
      refine hζ (hball _ hξ (mem_closedBall.2 ?_))
      rw [dist_eq_norm]
      exact (not_lt.1 h).trans (by gcongr; exact min_le_left _ _)
    have h := mul_add_le_norm_sub_of_mul_lt_norm_sub B hc₂ (min_le_right _ _) hfar
    rw [B.apply_symm_apply] at h
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans h
  · have hcB : c ≤ 1 / (4 * (1 + M)) := min_le_right _ _
    exact mul_add_le_norm_sub_of_norm_lt _ hc ((le_div_iff₀ (by positivity)).1 hcB) hζ

/-- An open cone of `E × D` containing the nonzero vectors of `{0} × D` contains a cone
`‖ζ.1‖ < c ‖ζ.2‖` around them, by compactness of the unit sphere of `D`. -/
theorem exists_pos_setOf_norm_fst_lt_subset {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [ProperSpace D] {Γ : Set (E × D)} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ, t • ζ ∈ Γ) (hD : ∀ b : D, b ≠ 0 → ((0 : E), b) ∈ Γ) :
    ∃ c > 0, {ζ : E × D | ‖ζ.1‖ < c * ‖ζ.2‖} ⊆ Γ := by
  have hι : Continuous fun b : D ↦ ((0 : E), b) := continuous_const.prodMk continuous_id
  obtain ⟨c, hc, hcΓ⟩ := ((isCompact_sphere (0 : D) 1).image hι).exists_cthickening_subset_open
    hΓ (image_subset_iff.2 fun b hb ↦ hD b (ne_zero_of_mem_unit_sphere ⟨b, hb⟩))
  refine ⟨c, hc, fun ζ hζ ↦ ?_⟩
  -- Rescaled to a unit second component, `ζ` lies within `c` of a conormal direction.
  have hs : 0 < ‖ζ.2‖ := pos_of_mul_pos_right ((norm_nonneg _).trans_lt hζ) hc.le
  set s := ‖ζ.2‖
  have hmem : s⁻¹ • ζ ∈ Γ := by
    refine hcΓ (mem_cthickening_of_dist_le _ ((0 : E), s⁻¹ • ζ.2) _ _
      (mem_image_of_mem _ ?_) ?_)
    · simp [norm_smul, inv_mul_cancel₀ hs.ne', s]
    · simp only [Prod.dist_eq, Prod.smul_fst, Prod.smul_snd, dist_self, dist_zero_right,
        norm_smul, norm_inv, Real.norm_of_nonneg hs.le]
      refine max_le ?_ hc.le
      rw [inv_mul_le_iff₀ hs, mul_comm]
      exact le_of_lt hζ
  simpa [smul_smul, mul_inv_cancel₀ hs.ne'] using hcone s hs _ hmem

/-- **Distance from a ray outside a cone.** Let `p` be a continuous linear map from a proper real
normed space `X`, and let `Γ` be an open subset of `X` closed under multiplication by positive
reals containing every nonzero `ζ` with `p ζ` on the ray `{s • ξ₀ | s ≥ 0}`. Then `p ζ` is at
distance at least `ε ‖ζ‖` from the ray for every `ζ ∉ Γ`, for some `ε > 0`. -/
theorem exists_pos_forall_mul_norm_le_norm_apply_sub_smul {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [ProperSpace X] {Γ : Set X} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ, t • ζ ∈ Γ) (p : X →L[ℝ] E) {ξ₀ : E}
    (hray : ∀ ζ : X, ζ ≠ 0 → ∀ s : ℝ, 0 ≤ s → p ζ = s • ξ₀ → ζ ∈ Γ) :
    ∃ ε > 0, ∀ ζ ∉ Γ, ∀ s : ℝ, 0 ≤ s → ε * ‖ζ‖ ≤ ‖p ζ - s • ξ₀‖ := by
  -- The unit vectors outside `Γ` form a compact set, which `p` maps away from the closed ray.
  set R : Set E := (fun s : ℝ ↦ s • ξ₀) '' Ici 0
  have hR : IsClosed R := isClosedMap_smul_left ξ₀ _ isClosed_Ici
  have hRne : R.Nonempty := ⟨_, mem_image_of_mem _ (self_mem_Ici (a := (0 : ℝ)))⟩
  obtain ⟨ε, hε, hεS⟩ :=
    ((isCompact_sphere (0 : X) 1).inter_right hΓ.isClosed_compl).exists_forall_le'
    (f := fun ζ ↦ infDist (p ζ) R) ((continuous_infDist_pt R).comp p.continuous).continuousOn
    (a := 0) fun ζ ⟨hζ, hζΓ⟩ ↦ by
      refine (infDist_pos_iff_notMem_closure hRne).1 ?_
      rw [hR.closure_eq]
      rintro ⟨s, hs, hsζ⟩
      exact hζΓ (hray ζ (ne_zero_of_mem_unit_sphere ⟨ζ, hζ⟩) s hs hsζ.symm)
  -- Rescale `ζ` to a unit vector.
  refine ⟨ε, hε, fun ζ hζ s hs ↦ ?_⟩
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · simp
  have hpos : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
  have hu : ‖ζ‖⁻¹ • ζ ∈ sphere (0 : X) 1 ∩ Γᶜ := by
    refine ⟨by simp [norm_smul, hpos.ne'], fun hmem ↦ hζ ?_⟩
    simpa [smul_smul, mul_inv_cancel₀ hpos.ne'] using hcone ‖ζ‖ hpos _ hmem
  have hdist : infDist (p (‖ζ‖⁻¹ • ζ)) R ≤ ‖ζ‖⁻¹ * ‖p ζ - s • ξ₀‖ := by
    refine (infDist_le_dist_of_mem (mem_image_of_mem (fun s : ℝ ↦ s • ξ₀)
      (show ‖ζ‖⁻¹ * s ∈ Ici 0 from mul_nonneg (inv_nonneg.2 hpos.le) hs))).trans (le_of_eq ?_)
    rw [dist_eq_norm, map_smul, ← smul_smul, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
  have h := (hεS _ hu).trans hdist
  rwa [inv_mul_eq_div, le_div_iff₀ hpos] at h

/-- **Separation from a cone around the preimage of a ray.** Let `p` be a continuous linear map
from a proper real normed space `X`, let `ξ₀ ≠ 0`, and let `Γ` be an open subset of `X` closed
under multiplication by positive reals containing every nonzero `ζ` with `p ζ` on the ray
`{s • ξ₀ | s ≥ 0}`. There are an open set `Γ'` closed under multiplication by positive reals with
`ξ₀ ∈ Γ'` and `c > 0` such that `p ζ` is at distance at least `c (‖ξ‖ + ‖ζ‖)` from every
`ξ ∈ Γ'` whenever `ζ ∉ Γ`. -/
theorem exists_cone_mul_add_le_norm_apply_sub {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [ProperSpace X] {Γ : Set X} (hΓ : IsOpen Γ)
    (hcone : ∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ, t • ζ ∈ Γ) (p : X →L[ℝ] E) {ξ₀ : E} (hξ₀ : ξ₀ ≠ 0)
    (hray : ∀ ζ : X, ζ ≠ 0 → ∀ s : ℝ, 0 ≤ s → p ζ = s • ξ₀ → ζ ∈ Γ) :
    ∃ Γ' : Set E, IsOpen Γ' ∧ ξ₀ ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ', t • ξ ∈ Γ') ∧
      ∃ c > 0, ∀ ξ ∈ Γ', ∀ ζ ∉ Γ, c * (‖ξ‖ + ‖ζ‖) ≤ ‖p ζ - ξ‖ := by
  obtain ⟨ε, hε, hfar⟩ := hΓ.exists_pos_forall_mul_norm_le_norm_apply_sub_smul hcone p hray
  -- `Γ'` is the cone of the `ξ` close to the ray, relative to `‖ξ‖`.
  set M := ‖p‖
  have hM : 0 ≤ M := norm_nonneg _
  set δ := ε / (2 * (M + 1))
  have hδ : 0 < δ := by positivity
  have hδM : (M + 1) * δ = ε / 2 := by
    simp only [δ]
    field_simp
  refine ⟨⋃ s ∈ Ioi (0 : ℝ), {ξ | ‖ξ - s • ξ₀‖ < δ * ‖ξ‖},
    isOpen_biUnion fun s _ ↦ isOpen_lt (by fun_prop) (by fun_prop),
    mem_iUnion₂.2 ⟨1, one_pos, by simpa using mul_pos hδ (norm_pos_iff.2 hξ₀)⟩,
    fun t ht ξ hξ ↦ ?_, ε / (1 + 3 * (ε + M)), by positivity, fun ξ hξ ζ hζ ↦ ?_⟩
  · obtain ⟨s, hs, hξs⟩ := mem_iUnion₂.1 hξ
    refine mem_iUnion₂.2 ⟨t * s, mul_pos ht hs, ?_⟩
    simp only [mem_ofPred_eq] at hξs ⊢
    rw [← smul_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm]
    exact mul_lt_mul_of_pos_left hξs ht
  · obtain ⟨s, hs, hξs⟩ := mem_iUnion₂.1 hξ
    simp only [mem_ofPred_eq] at hξs
    have h1 : ‖p ζ - s • ξ₀‖ ≤ ‖p ζ - ξ‖ + ‖ξ - s • ξ₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : ‖ξ‖ ≤ ‖p ζ - ξ‖ + M * ‖ζ‖ := by
      calc ‖ξ‖ ≤ ‖p ζ - ξ‖ + ‖p ζ‖ := by
            simpa [norm_sub_rev, add_comm] using norm_le_norm_add_norm_sub' ξ (p ζ)
        _ ≤ _ := by gcongr; exact p.le_opNorm ζ
    have hA : ε * ‖ζ‖ ≤ ‖p ζ - ξ‖ + δ * ‖ξ‖ := by linarith [hfar ζ hζ s hs.le]
    have hC := mul_le_mul_of_nonneg_left h2 hε.le
    have hD := mul_le_mul_of_nonneg_left hA hM
    have hMδ : M * (δ * ‖ξ‖) ≤ ε / 2 * ‖ξ‖ := by
      rw [← mul_assoc, ← hδM]
      gcongr
      linarith
    have hδ2 : δ * ‖ξ‖ ≤ ε / 2 * ‖ξ‖ := by
      rw [← hδM]
      gcongr
      exact le_mul_of_one_le_left hδ.le (by linarith)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith


open Filter in
/-- **Decay in a cone forces vanishing along lines.** Let `Γ` be an open cone containing a nonzero
`ξ`, and let `(1 + ‖η‖) ‖g η‖` be bounded on `Γ`. If `g` is constant along the line
`t ↦ t • ξ + w`, then the constant is zero: the line eventually lies in `Γ`, where
`‖g (t • ξ + w)‖ ≤ C / (1 + ‖t • ξ + w‖)` tends to `0`. Applied to a localized Fourier transform,
this shows that a distribution is not microlocally smooth. -/
theorem eq_zero_of_forall_smul_add_eq {F : Type*} [NormedAddCommGroup F] {g : E → F} {Γ : Set E}
    (hΓ : IsOpen Γ) {ξ : E} (hξΓ : ξ ∈ Γ) (hξ : ξ ≠ 0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) {C : ℝ}
    (hC : ∀ η ∈ Γ, (1 + ‖η‖) * ‖g η‖ ≤ C) {w : E} {c : F} (hc : ∀ t : ℝ, g (t • ξ + w) = c) :
    c = 0 := by
  have hξpos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hgrow : Tendsto (fun t : ℝ => 1 + ‖t • ξ + w‖) atTop atTop := by
    refine tendsto_atTop_mono (fun t => ?_)
      (tendsto_atTop_add_const_right _ (-‖w‖) (tendsto_id.atTop_mul_const hξpos))
    have h := norm_sub_le (t • ξ + w) w
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs] at h
    have := mul_le_mul_of_nonneg_right (le_abs_self t) (norm_nonneg ξ)
    simp only [id]
    linarith
  refine norm_le_zero_iff.1 (ge_of_tendsto ((tendsto_const_nhds (x := C)).div_atTop hgrow) ?_)
  filter_upwards [hΓ.eventually_smul_add_mem hξΓ hcone w] with t ht
  have hbound := hC _ ht
  rw [hc] at hbound
  exact (le_div_iff₀' (by positivity)).2 hbound

end IsOpen

namespace IsClosed

/-- A closed set closed under multiplication by positive reals contains `0` as soon as it is
nonempty. -/
theorem zero_mem_of_smul_mem {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousSMul ℝ E] {V : Set E} (hV : IsClosed V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V) {ξ : E} (hξ : ξ ∈ V) : (0 : E) ∈ V := by
  have h : Filter.Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1)) • ξ) Filter.atTop (nhds 0) := by
    have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const ξ
    rwa [zero_smul] at h0
  exact hV.mem_of_tendsto h (Filter.Eventually.of_forall fun n ↦ hVcone _ (by positivity) ξ hξ)

end IsClosed

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- If the closed ball of radius `c ‖η‖` about every point `η` of `Γ'` lies in `Γ`, then so does
every nonzero point of the closure of `Γ'`. For an open cone `Γ'` as in
`IsOpen.exists_cone_closedBall_subset`, the closure of `Γ'` is a closed cone whose nonzero points
lie in `Γ`. -/
theorem mem_of_mem_closure_of_forall_closedBall_subset {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {ξ : E} (hξ : ξ ∈ closure Γ') (hξ0 : ξ ≠ 0) :
    ξ ∈ Γ := by
  obtain ⟨η, hη, hξη⟩ := Metric.mem_closure_iff.1 hξ (c * ‖ξ‖ / (1 + c)) (by positivity)
  refine hΓ' η hη (mem_closedBall.2 ?_)
  -- `dist ξ η (1 + c) < c ‖ξ‖ ≤ c (‖η‖ + dist ξ η)`.
  have hnorm : ‖ξ‖ ≤ ‖η‖ + dist ξ η := by
    rw [dist_eq_norm]
    exact norm_le_norm_add_norm_sub' ξ η
  rw [lt_div_iff₀ (by positivity)] at hξη
  nlinarith

/-- **A translate by a small shift.** If `‖v‖ ≤ c ‖η‖` with `c ≤ 1 / 2` and the closed ball of
radius `c ‖η‖` about `η` lies in a set `Γ` on which `(1 + ‖ζ‖) ^ n ‖F ζ‖ ≤ C₁`, then
`(1 + ‖η‖) ^ n ‖F (η - v)‖ ≤ 2 ^ n C₁`, since `‖η - v‖ ≥ ‖η‖ / 2`. -/
theorem one_add_norm_pow_mul_norm_apply_sub_le_of_norm_le {G : Type*} [NormedAddCommGroup G]
    {F : E → G} {Γ : Set E} {n : ℕ} {C₁ : ℝ} (hdecay : ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ n * ‖F ζ‖ ≤ C₁) {c : ℝ}
    (hc1 : c ≤ 1 / 2) {η v : E} (hη : closedBall η (c * ‖η‖) ⊆ Γ) (hv : ‖v‖ ≤ c * ‖η‖) :
    (1 + ‖η‖) ^ n * ‖F (η - v)‖ ≤ 2 ^ n * C₁ := by
  have hmem : η - v ∈ Γ := hη (by
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hv)
  have hle : 1 + ‖η‖ ≤ 2 * (1 + ‖η - v‖) := by
    have := norm_sub_norm_le η v
    nlinarith [norm_nonneg η]
  calc (1 + ‖η‖) ^ n * ‖F (η - v)‖ ≤ (2 * (1 + ‖η - v‖)) ^ n * ‖F (η - v)‖ := by gcongr
    _ = 2 ^ n * ((1 + ‖η - v‖) ^ n * ‖F (η - v)‖) := by rw [mul_pow]; ring
    _ ≤ 2 ^ n * C₁ := by gcongr; exact hdecay _ hmem

/-- **A translate by a large shift.** If `F` grows at most like `(1 + ‖ζ‖) ^ k` and
`c ‖η‖ < ‖v‖` with `0 < c ≤ 1`, then `(1 + ‖η‖) ^ N ‖F (η - v)‖` is bounded by
`C₀ c⁻¹ ^ (N + k) (1 + ‖v‖) ^ (N + 2 k)`, since `1 + ‖η‖ ≤ c⁻¹ (1 + ‖v‖)`. -/
theorem one_add_norm_pow_mul_norm_apply_sub_le_of_lt_norm {G : Type*} [NormedAddCommGroup G]
    {F : E → G} {C₀ : ℝ} {k : ℕ} (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) (N : ℕ) {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1) {η v : E} (hv : c * ‖η‖ < ‖v‖) :
    (1 + ‖η‖) ^ N * ‖F (η - v)‖ ≤ C₀ * c⁻¹ ^ (N + k) * (1 + ‖v‖) ^ (N + 2 * k) := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  have hle : 1 + ‖η‖ ≤ c⁻¹ * (1 + ‖v‖) := by
    rw [le_inv_mul_iff₀ hc]
    nlinarith [norm_nonneg η]
  have hFle : ‖F (η - v)‖ ≤ C₀ * ((1 + ‖η‖) ^ k * (1 + ‖v‖) ^ k) := by
    refine (hF _).trans ?_
    rw [← mul_pow]
    gcongr
    nlinarith [norm_sub_le η v, norm_nonneg η, norm_nonneg v]
  calc (1 + ‖η‖) ^ N * ‖F (η - v)‖
      ≤ (1 + ‖η‖) ^ N * (C₀ * ((1 + ‖η‖) ^ k * (1 + ‖v‖) ^ k)) := by gcongr
    _ = C₀ * ((1 + ‖η‖) ^ (N + k) * (1 + ‖v‖) ^ k) := by ring
    _ ≤ C₀ * ((c⁻¹ * (1 + ‖v‖)) ^ (N + k) * (1 + ‖v‖) ^ k) := by gcongr
    _ = C₀ * c⁻¹ ^ (N + k) * (1 + ‖v‖) ^ (N + 2 * k) := by rw [mul_pow]; ring

/-- **The pointwise bound behind rapid decay on a smaller cone.** Let `F` grow at most polynomially
and let `(1 + ‖η‖) ^ (N + M) ‖F η‖` be bounded on a set `Γ`. If the closed ball of radius `c ‖η‖`
about every `η ∈ Γ'` lies in `Γ`, then `(1 + ‖η‖) ^ N (1 + ‖η - θ‖) ^ M ‖F (η - θ)‖` is at most a
constant times `(1 + ‖θ‖) ^ (N + 2 (M + k))`, for `η ∈ Γ'` and every shift `θ`. Shifts with
`‖θ‖ ≤ c ‖η‖` evaluate `F` at points of `Γ` of size comparable to `‖η‖`, and the remaining shifts
have `1 + ‖η‖` and `1 + ‖η - θ‖` controlled by powers of `1 + ‖θ‖`. -/
theorem exists_one_add_norm_pow_mul_norm_apply_sub_le {G : Type*} [SeminormedAddGroup G]
    {F : E → G} {C₀ : ℝ} {k : ℕ} (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E} {c : ℝ}
    (hc : 0 < c) (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ) {N M : ℕ}
    (hdecay : ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ (N + M) * ‖F η‖ ≤ C) :
    ∃ D, 0 ≤ D ∧ ∀ η ∈ Γ', ∀ θ,
      (1 + ‖η‖) ^ N * ((1 + ‖η - θ‖) ^ M * ‖F (η - θ)‖) ≤ D * (1 + ‖θ‖) ^ (N + 2 * (M + k)) := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  set c' := min c (1 / 2)
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'1 : c' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C₁, hC₁⟩ := hdecay
  set D := max (2 ^ N * C₁) (C₀ * c'⁻¹ ^ (N + M + k))
  have hD : 0 ≤ D := le_max_of_le_right (by positivity)
  refine ⟨D, hD, fun η hη θ ↦ ?_⟩
  by_cases hθ : ‖θ‖ ≤ c' * ‖η‖
  · -- Small shifts stay in `Γ`, where `F` decays rapidly, and `‖η - θ‖ ≥ ‖η‖ / 2`.
    have hmem : η - θ ∈ Γ := by
      refine hΓ' η hη (mem_closedBall.2 ?_)
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
      exact hθ.trans (by gcongr; exact min_le_left _ _)
    have hle : 1 + ‖η‖ ≤ 2 * (1 + ‖η - θ‖) := by
      have := norm_sub_norm_le η θ
      nlinarith [norm_nonneg η]
    calc (1 + ‖η‖) ^ N * ((1 + ‖η - θ‖) ^ M * ‖F (η - θ)‖)
        ≤ (2 * (1 + ‖η - θ‖)) ^ N * ((1 + ‖η - θ‖) ^ M * ‖F (η - θ)‖) := by gcongr
      _ = 2 ^ N * ((1 + ‖η - θ‖) ^ (N + M) * ‖F (η - θ)‖) := by rw [mul_pow, pow_add]; ring
      _ ≤ 2 ^ N * C₁ := by gcongr; exact hC₁ _ hmem
      _ ≤ D := le_max_left _ _
      _ ≤ D * (1 + ‖θ‖) ^ (N + 2 * (M + k)) :=
        le_mul_of_one_le_right hD (one_le_pow₀ (by linarith [norm_nonneg θ]))
  · -- Large shifts have `1 + ‖η‖ ≤ c'⁻¹ (1 + ‖θ‖)`; use the polynomial growth of `F`.
    push Not at hθ
    have hle : 1 + ‖η‖ ≤ c'⁻¹ * (1 + ‖θ‖) := by
      rw [le_inv_mul_iff₀ hc']
      nlinarith [norm_nonneg η]
    have hle' : 1 + ‖η - θ‖ ≤ c'⁻¹ * (1 + ‖θ‖) ^ 2 :=
      calc 1 + ‖η - θ‖ ≤ (1 + ‖η‖) * (1 + ‖θ‖) := by
            simpa only [sub_eq_add_neg, norm_neg] using one_add_norm_add_le η (-θ)
        _ ≤ c'⁻¹ * (1 + ‖θ‖) * (1 + ‖θ‖) := by gcongr
        _ = c'⁻¹ * (1 + ‖θ‖) ^ 2 := by ring
    calc (1 + ‖η‖) ^ N * ((1 + ‖η - θ‖) ^ M * ‖F (η - θ)‖)
        ≤ (1 + ‖η‖) ^ N * ((1 + ‖η - θ‖) ^ M * (C₀ * (1 + ‖η - θ‖) ^ k)) := by
          gcongr; exact hF _
      _ = C₀ * ((1 + ‖η‖) ^ N * (1 + ‖η - θ‖) ^ (M + k)) := by ring
      _ ≤ C₀ * ((c'⁻¹ * (1 + ‖θ‖)) ^ N * (c'⁻¹ * (1 + ‖θ‖) ^ 2) ^ (M + k)) := by gcongr
      _ = C₀ * c'⁻¹ ^ (N + M + k) * (1 + ‖θ‖) ^ (N + 2 * (M + k)) := by
          rw [mul_pow, mul_pow, ← pow_mul]; ring
      _ ≤ D * (1 + ‖θ‖) ^ (N + 2 * (M + k)) := by gcongr; exact le_max_right _ _

/-- **Rapid decay of a discrete convolution on a smaller cone.** A superposition
`∑ i, a i • F (η - v i)` of translates of a function `F` of polynomial growth, with coefficients
`a i` rapidly decreasing in `‖v i‖`, decays on every set `Γ'` whose conic neighbourhoods
`closedBall η (c ‖η‖)`, `c > 0`, lie in a set `Γ`, at every order `N` at which `F` decays on `Γ`:
if `F` grows at most like `(1 + ‖ζ‖) ^ k` and `(1 + ‖η‖) ^ N ‖F η‖` is bounded on `Γ`, then
`(1 + ‖η‖) ^ N ‖∑ i, a i • F (η - v i)‖` is bounded on `Γ'` by
`D ∑ i, (1 + ‖v i‖) ^ (N + 2 k) ‖a i‖`, with a constant `D ≥ 0` independent of the coefficients. -/
theorem exists_one_add_norm_pow_mul_norm_le_of_hasSum {ι 𝕜 G : Type*} [NormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (v : ι → E) {F : E → G} {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ η ∈ Γ', closedBall η (c * ‖η‖) ⊆ Γ)
    {N : ℕ} (hdecay : ∃ C, ∀ η ∈ Γ, (1 + ‖η‖) ^ N * ‖F η‖ ≤ C) :
    ∃ D, 0 ≤ D ∧ ∀ a : ι → 𝕜, Summable (fun i ↦ (1 + ‖v i‖) ^ (N + 2 * k) * ‖a i‖) →
      ∀ η ∈ Γ', ∀ s, HasSum (fun i ↦ a i • F (η - v i)) s →
        (1 + ‖η‖) ^ N * ‖s‖ ≤ D * ∑' i, (1 + ‖v i‖) ^ (N + 2 * k) * ‖a i‖ := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  set c' := min c (1 / 2)
  have hc' : 0 < c' := lt_min hc (by norm_num)
  have hc'1 : c' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨C₁, hC₁⟩ := hdecay
  set D := max (2 ^ N * C₁) (C₀ * c'⁻¹ ^ (N + k))
  have hD : 0 ≤ D := le_max_of_le_right (by positivity)
  refine ⟨D, hD, fun a ha η hη s hs ↦ ?_⟩
  -- Each translate is bounded by `D (1 + ‖v i‖) ^ (N + 2 k) (1 + ‖η‖) ^ (-N)`.
  have hterm (i : ι) : (1 + ‖η‖) ^ N * ‖F (η - v i)‖ ≤ D * (1 + ‖v i‖) ^ (N + 2 * k) := by
    have h1 : 1 ≤ (1 + ‖v i‖) ^ (N + 2 * k) := one_le_pow₀ (by linarith [norm_nonneg (v i)])
    by_cases hv : ‖v i‖ ≤ c' * ‖η‖
    · -- Small shifts stay in `Γ`, where `F` decays rapidly.
      calc (1 + ‖η‖) ^ N * ‖F (η - v i)‖ ≤ 2 ^ N * C₁ :=
            one_add_norm_pow_mul_norm_apply_sub_le_of_norm_le hC₁ hc'1
              ((closedBall_subset_closedBall (by gcongr; exact min_le_left _ _)).trans
                (hΓ' η hη)) hv
        _ ≤ D := le_max_left _ _
        _ ≤ D * (1 + ‖v i‖) ^ (N + 2 * k) := le_mul_of_one_le_right hD h1
    · -- Large shifts have `‖v i‖` comparable to `‖η‖`; use the polynomial growth of `F`.
      push Not at hv
      refine (one_add_norm_pow_mul_norm_apply_sub_le_of_lt_norm hF N hc' (by linarith) hv).trans ?_
      gcongr
      exact le_max_right _ _
  have hp : 0 < (1 + ‖η‖) ^ N := by positivity
  have hbound := hs.norm_le_of_bounded ((ha.hasSum.mul_left D).div_const _) fun i ↦ by
    rw [norm_smul, le_div_iff₀ hp]
    nlinarith [hterm i, norm_nonneg (a i)]
  rw [le_div_iff₀ hp] at hbound
  linarith

/-- **Decay of a discrete convolution with frequency-dependent coefficients.** Let `F` grow at
most like `(1 + ‖ζ‖) ^ k` and satisfy `(1 + ‖ζ‖) ^ (N + q) ‖F ζ‖ ≤ C₁` on a set `Γ` containing the
closed ball of radius `c ‖η‖` about `η`, with `0 < c ≤ 1 / 2`. If the coefficients `a i`, which may
depend on `η`, are bounded by `A₀`, and those with `‖v i‖ > c ‖η‖` satisfy
`‖v i‖ ^ (N + 2 k + q) ‖a i‖ ≤ A₁`, then the sum `s = ∑ i, a i • F (η - v i)` has
`(1 + ‖η‖) ^ N ‖s‖` bounded by a constant depending only on these data, times
`∑ i, (1 + ‖v i‖) ^ (-q)`. -/
theorem one_add_norm_pow_mul_norm_le_of_hasSum {ι 𝕜 G : Type*} [NormedField 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (v : ι → E) {q : ℕ}
    (hv : Summable fun i ↦ ((1 + ‖v i‖) ^ q)⁻¹) {F : E → G} {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) {Γ : Set E} {N : ℕ} {C₁ : ℝ}
    (hdecay : ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ (N + q) * ‖F ζ‖ ≤ C₁) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    {η : E} (hη : closedBall η (c * ‖η‖) ⊆ Γ) {a : ι → 𝕜} {A₀ A₁ : ℝ} (hA₀ : 0 ≤ A₀)
    (hA₁ : 0 ≤ A₁) (ha₀ : ∀ i, ‖a i‖ ≤ A₀)
    (ha₁ : ∀ i, c * ‖η‖ < ‖v i‖ → ‖v i‖ ^ (N + 2 * k + q) * ‖a i‖ ≤ A₁) {s : G}
    (hs : HasSum (fun i ↦ a i • F (η - v i)) s) :
    (1 + ‖η‖) ^ N * ‖s‖ ≤ (A₀ * 2 ^ (N + q) * C₁ +
      C₀ * c⁻¹ ^ (N + k) * (2 ^ (N + 2 * k + q) * (A₀ + A₁))) * ∑' i, ((1 + ‖v i‖) ^ q)⁻¹ := by
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (F 0)).trans (by simpa using hF 0)
  have hC₁ : 0 ≤ C₁ := (by positivity : 0 ≤ (1 + ‖η‖) ^ (N + q) * ‖F η‖).trans
    (hdecay η (hη (mem_closedBall_self (by positivity))))
  have hp : 0 < (1 + ‖η‖) ^ N := by positivity
  -- Each term is bounded by the constant times `(1 + ‖v i‖) ^ (-q) / (1 + ‖η‖) ^ N`.
  have hterm (i : ι) : ‖a i • F (η - v i)‖ ≤ (A₀ * 2 ^ (N + q) * C₁ +
      C₀ * c⁻¹ ^ (N + k) * (2 ^ (N + 2 * k + q) * (A₀ + A₁))) * ((1 + ‖v i‖) ^ q)⁻¹ /
        (1 + ‖η‖) ^ N := by
    rw [le_div_iff₀ hp, norm_smul, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    by_cases hvi : ‖v i‖ ≤ c * ‖η‖
    · -- Small shifts: `1 + ‖v i‖ ≤ 1 + ‖η‖`, and `F` decays at order `N + q` near `η`.
      have hvη : 1 + ‖v i‖ ≤ 1 + ‖η‖ := by nlinarith [norm_nonneg η]
      calc ‖a i‖ * ‖F (η - v i)‖ * (1 + ‖η‖) ^ N * (1 + ‖v i‖) ^ q
          ≤ A₀ * ‖F (η - v i)‖ * (1 + ‖η‖) ^ N * (1 + ‖η‖) ^ q := by gcongr; exact ha₀ i
        _ = A₀ * ((1 + ‖η‖) ^ (N + q) * ‖F (η - v i)‖) := by rw [pow_add]; ring
        _ ≤ A₀ * (2 ^ (N + q) * C₁) := by
            gcongr A₀ * ?_
            exact one_add_norm_pow_mul_norm_apply_sub_le_of_norm_le hdecay hc1 hη hvi
        _ ≤ _ := le_add_of_le_of_nonneg (by rw [mul_assoc]) (by positivity)
    · -- Large shifts: the coefficient decays at order `N + 2 k + q` in `‖v i‖`.
      push Not at hvi
      have hav : (1 + ‖v i‖) ^ (N + 2 * k + q) * ‖a i‖ ≤ 2 ^ (N + 2 * k + q) * (A₀ + A₁) :=
        calc (1 + ‖v i‖) ^ (N + 2 * k + q) * ‖a i‖
            ≤ 2 ^ (N + 2 * k + q - 1) * (1 ^ (N + 2 * k + q) + ‖v i‖ ^ (N + 2 * k + q)) *
                ‖a i‖ := by
              gcongr; exact add_pow_le zero_le_one (norm_nonneg _) _
          _ = 2 ^ (N + 2 * k + q - 1) * (‖a i‖ + ‖v i‖ ^ (N + 2 * k + q) * ‖a i‖) := by ring
          _ ≤ 2 ^ (N + 2 * k + q) * (A₀ + A₁) := mul_le_mul
              (pow_le_pow_right₀ one_le_two (by omega)) (add_le_add (ha₀ i) (ha₁ i hvi))
              (by positivity) (by positivity)
      calc ‖a i‖ * ‖F (η - v i)‖ * (1 + ‖η‖) ^ N * (1 + ‖v i‖) ^ q
          = ‖a i‖ * ((1 + ‖η‖) ^ N * ‖F (η - v i)‖) * (1 + ‖v i‖) ^ q := by ring
        _ ≤ ‖a i‖ * (C₀ * c⁻¹ ^ (N + k) * (1 + ‖v i‖) ^ (N + 2 * k)) * (1 + ‖v i‖) ^ q := by
            gcongr ‖a i‖ * ?_ * _
            exact one_add_norm_pow_mul_norm_apply_sub_le_of_lt_norm hF N hc (by linarith) hvi
        _ = C₀ * c⁻¹ ^ (N + k) * ((1 + ‖v i‖) ^ (N + 2 * k + q) * ‖a i‖) := by
            rw [pow_add _ (N + 2 * k) q]; ring
        _ ≤ C₀ * c⁻¹ ^ (N + k) * (2 ^ (N + 2 * k + q) * (A₀ + A₁)) := by gcongr
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have hbound := hs.norm_le_of_bounded ((hv.hasSum.mul_left _).div_const _) hterm
  rw [le_div_iff₀ hp] at hbound
  linarith

/-- **Rapid decay of a product on a cone.** If `g` decays rapidly on an open cone `Γ` containing
`a ζ₀ ≠ 0` and `h` grows at most polynomially, then `ζ ↦ g (a ζ) * h (b ζ)` decays rapidly on an
open cone containing `ζ₀`, provided `‖ζ‖ ≤ ‖a ζ‖ + ‖b ζ‖`. The cone is that of the `ζ` with
`a ζ ∈ Γ` and `‖b ζ‖ < c ‖a ζ‖`, on which `‖ζ‖` and `‖b ζ‖` are at most `(1 + c) ‖a ζ‖`. -/
theorem exists_cone_decay_mul {X A B 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B]
    (a : X →L[ℝ] A) (b : X →L[ℝ] B) (hab : ∀ ζ, ‖ζ‖ ≤ ‖a ζ‖ + ‖b ζ‖) {Γ : Set A}
    (hΓ : IsOpen Γ) (hcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ, t • ξ ∈ Γ) {ζ₀ : X} (hζ₀ : a ζ₀ ∈ Γ)
    (ha₀ : a ζ₀ ≠ 0) {g : A → 𝕜} {h : B → 𝕜}
    (hg : ∀ N : ℕ, ∃ C, ∀ ξ ∈ Γ, (1 + ‖ξ‖) ^ N * ‖g ξ‖ ≤ C)
    (hh : ∃ (C : ℝ) (k : ℕ), ∀ η, ‖h η‖ ≤ C * (1 + ‖η‖) ^ k) :
    ∃ Γ' : Set X, IsOpen Γ' ∧ ζ₀ ∈ Γ' ∧ (∀ t : ℝ, 0 < t → ∀ ζ ∈ Γ', t • ζ ∈ Γ') ∧
      ∀ N : ℕ, ∃ C, ∀ ζ ∈ Γ', (1 + ‖ζ‖) ^ N * ‖g (a ζ) * h (b ζ)‖ ≤ C := by
  obtain ⟨C₀, k, hC₀⟩ := hh
  have hC₀' : 0 ≤ C₀ := by simpa using (norm_nonneg _).trans (hC₀ 0)
  have ha₀' : 0 < ‖a ζ₀‖ := norm_pos_iff.2 ha₀
  set c := ‖b ζ₀‖ / ‖a ζ₀‖ + 1 with hc_def
  have hc : 0 < c := by positivity
  refine ⟨a ⁻¹' Γ ∩ {ζ | ‖b ζ‖ < c * ‖a ζ‖},
    (hΓ.preimage a.continuous).inter (isOpen_lt (by fun_prop) (by fun_prop)), ⟨hζ₀, ?_⟩, ?_,
    fun N ↦ ?_⟩
  · have : c * ‖a ζ₀‖ = ‖b ζ₀‖ + ‖a ζ₀‖ := by
      rw [hc_def, add_mul, div_mul_cancel₀ _ ha₀'.ne', one_mul]
    simp only [mem_ofPred_eq, this]
    linarith
  · rintro t ht ζ ⟨h₁, h₂⟩
    refine ⟨by simpa using hcone t ht _ h₁, ?_⟩
    simp only [mem_ofPred_eq, map_smul, norm_smul, Real.norm_of_nonneg ht.le]
    rw [mul_left_comm]
    exact mul_lt_mul_of_pos_left h₂ ht
  · obtain ⟨C, hC⟩ := hg (N + k)
    refine ⟨(1 + c) ^ (N + k) * C₀ * C, fun ζ ⟨h₁, h₂⟩ ↦ ?_⟩
    have h₂' : ‖b ζ‖ ≤ c * ‖a ζ‖ := h₂.le
    have hr : 0 ≤ ‖a ζ‖ := norm_nonneg _
    have hζ : 1 + ‖ζ‖ ≤ (1 + c) * (1 + ‖a ζ‖) := by nlinarith [hab ζ]
    have hb : 1 + ‖b ζ‖ ≤ (1 + c) * (1 + ‖a ζ‖) := by nlinarith
    have hh' : ‖h (b ζ)‖ ≤ C₀ * ((1 + c) * (1 + ‖a ζ‖)) ^ k :=
      (hC₀ _).trans (by gcongr)
    calc (1 + ‖ζ‖) ^ N * ‖g (a ζ) * h (b ζ)‖
        = (1 + ‖ζ‖) ^ N * ‖h (b ζ)‖ * ‖g (a ζ)‖ := by rw [norm_mul]; ring
      _ ≤ ((1 + c) * (1 + ‖a ζ‖)) ^ N * (C₀ * ((1 + c) * (1 + ‖a ζ‖)) ^ k) * ‖g (a ζ)‖ := by
          gcongr
      _ = (1 + c) ^ (N + k) * C₀ * ((1 + ‖a ζ‖) ^ (N + k) * ‖g (a ζ)‖) := by
          rw [mul_pow, mul_pow, pow_add, pow_add]
          ring
      _ ≤ (1 + c) ^ (N + k) * C₀ * C := by gcongr; exact hC _ h₁

/-- **Joint rapid decay of a product separated by a cone.** Let `p : X →L[ℝ] E` and suppose that
`p ζ` is at distance at least `c (‖ξ‖ + ‖ζ‖)` from every `ξ ∈ Γ'` whenever `ζ ∉ Γ`, as in
`IsOpen.exists_cone_mul_add_le_norm_apply_sub`. If `F` grows at most polynomially and decays
rapidly on `Γ`, and `g` decays rapidly, then `g (ξ - p ζ) F ζ` decays rapidly in `ξ ∈ Γ'` and in
`ζ` jointly: for `ζ ∈ Γ` both factors contribute, and for `ζ ∉ Γ` the argument of `g` is
comparable to `‖ξ‖ + ‖ζ‖`. -/
theorem exists_one_add_norm_pow_mul_one_add_norm_pow_mul_norm_mul_le {X 𝕜 : Type*}
    [NormedSpace ℝ E] [NormedField 𝕜] [NormedAddCommGroup X] [NormedSpace ℝ X] (p : X →L[ℝ] E)
    {Γ : Set X} {Γ' : Set E} {c : ℝ} (hc : 0 < c)
    (hsep : ∀ ξ ∈ Γ', ∀ ζ ∉ Γ, c * (‖ξ‖ + ‖ζ‖) ≤ ‖p ζ - ξ‖) {g : E → 𝕜} {F : X → 𝕜}
    (hg : ∀ N : ℕ, ∃ C, ∀ v, (1 + ‖v‖) ^ N * ‖g v‖ ≤ C)
    (hF : ∃ (C : ℝ) (k : ℕ), ∀ ζ, ‖F ζ‖ ≤ C * (1 + ‖ζ‖) ^ k)
    (hFΓ : ∀ N : ℕ, ∃ C, ∀ ζ ∈ Γ, (1 + ‖ζ‖) ^ N * ‖F ζ‖ ≤ C) (N : ℕ) :
    ∃ C, ∀ ξ ∈ Γ', ∀ ζ, (1 + ‖ξ‖) ^ N * ((1 + ‖ζ‖) ^ N * ‖g (ξ - p ζ) * F ζ‖) ≤ C := by
  obtain ⟨C₀, k, hC₀⟩ := hF
  have hC₀' : 0 ≤ C₀ := by simpa using (norm_nonneg _).trans (hC₀ 0)
  obtain ⟨C₁, hC₁⟩ := hg N
  obtain ⟨C₂, hC₂⟩ := hFΓ (2 * N)
  obtain ⟨C₃, hC₃⟩ := hg (2 * N + k)
  have hC₁' : 0 ≤ C₁ := (by positivity : (0 : ℝ) ≤ (1 + ‖(0 : E)‖) ^ N * ‖g 0‖).trans (hC₁ 0)
  set M := ‖p‖
  set A := 1 + c⁻¹
  refine ⟨max ((1 + M) ^ N * (C₁ * C₂)) (C₀ * A ^ (2 * N + k) * C₃), fun ξ hξ ζ ↦ ?_⟩
  have hd : 0 ≤ ‖ξ - p ζ‖ := norm_nonneg _
  rw [norm_mul]
  by_cases hζ : ζ ∈ Γ
  · -- `1 + ‖ξ‖ ≤ (1 + M) (1 + ‖ξ - p ζ‖) (1 + ‖ζ‖)`, and `F` decays at `ζ`.
    have hξ' : ‖ξ‖ ≤ ‖ξ - p ζ‖ + M * ‖ζ‖ :=
      (norm_le_norm_sub_add ξ (p ζ)).trans (by gcongr; exact p.le_opNorm ζ)
    have hle : 1 + ‖ξ‖ ≤ (1 + M) * ((1 + ‖ξ - p ζ‖) * (1 + ‖ζ‖)) := by
      have hM : 0 ≤ M := norm_nonneg _
      nlinarith [norm_nonneg ζ, mul_nonneg hd (norm_nonneg ζ), mul_nonneg hM hd,
        mul_nonneg hM (mul_nonneg hd (norm_nonneg ζ))]
    calc (1 + ‖ξ‖) ^ N * ((1 + ‖ζ‖) ^ N * (‖g (ξ - p ζ)‖ * ‖F ζ‖))
        ≤ ((1 + M) * ((1 + ‖ξ - p ζ‖) * (1 + ‖ζ‖))) ^ N *
            ((1 + ‖ζ‖) ^ N * (‖g (ξ - p ζ)‖ * ‖F ζ‖)) := by gcongr
      _ = (1 + M) ^ N * (((1 + ‖ξ - p ζ‖) ^ N * ‖g (ξ - p ζ)‖) *
            ((1 + ‖ζ‖) ^ (2 * N) * ‖F ζ‖)) := by rw [mul_pow, mul_pow, two_mul, pow_add]; ring
      _ ≤ (1 + M) ^ N * (C₁ * C₂) := by gcongr; exacts [hC₁ _, hC₂ ζ hζ]
      _ ≤ _ := le_max_left _ _
  · -- Both `1 + ‖ξ‖` and `1 + ‖ζ‖` are at most `A (1 + ‖ξ - p ζ‖)`.
    have hs := hsep ξ hξ ζ hζ
    rw [norm_sub_rev] at hs
    have hsum : ‖ξ‖ + ‖ζ‖ ≤ c⁻¹ * ‖ξ - p ζ‖ := by rwa [le_inv_mul_iff₀ hc]
    have hcinv : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    have hξ' : 1 + ‖ξ‖ ≤ A * (1 + ‖ξ - p ζ‖) := by
      nlinarith [norm_nonneg ζ, mul_nonneg hcinv hd]
    have hζ' : 1 + ‖ζ‖ ≤ A * (1 + ‖ξ - p ζ‖) := by
      nlinarith [norm_nonneg ξ, mul_nonneg hcinv hd]
    calc (1 + ‖ξ‖) ^ N * ((1 + ‖ζ‖) ^ N * (‖g (ξ - p ζ)‖ * ‖F ζ‖))
        ≤ (A * (1 + ‖ξ - p ζ‖)) ^ N * ((A * (1 + ‖ξ - p ζ‖)) ^ N *
            (‖g (ξ - p ζ)‖ * (C₀ * (A * (1 + ‖ξ - p ζ‖)) ^ k))) := by
          gcongr
          exact (hC₀ ζ).trans (by gcongr)
      _ = C₀ * A ^ (2 * N + k) * ((1 + ‖ξ - p ζ‖) ^ (2 * N + k) * ‖g (ξ - p ζ)‖) := by
          rw [mul_pow, mul_pow, two_mul, pow_add, pow_add, pow_add, pow_add]; ring
      _ ≤ C₀ * A ^ (2 * N + k) * C₃ := by gcongr; exact hC₃ _
      _ ≤ _ := le_max_right _ _


/-- **Finitely many open cones cover a closed cone.** Let `V` be a closed subset of a proper real
normed space closed under multiplication by positive reals. If every unit vector `ξ` of `V` lies
in an open set `Γ ξ` closed under multiplication by positive reals, then finitely many of these
cones cover every nonzero vector of `V`: the unit vectors of `V` form a compact set. -/
theorem exists_finset_diff_singleton_subset_biUnion [NormedSpace ℝ E] [ProperSpace E] {V : Set E}
    (hV : IsClosed V) (hVcone : ∀ t : ℝ, 0 < t → ∀ η ∈ V, t • η ∈ V)
    {Γ : sphere (0 : E) 1 → Set E} (hΓ : ∀ ξ, IsOpen (Γ ξ))
    (hξΓ : ∀ ξ : sphere (0 : E) 1, (ξ : E) ∈ V → (ξ : E) ∈ Γ ξ)
    (hcone : ∀ ξ, ∀ t : ℝ, 0 < t → ∀ η ∈ Γ ξ, t • η ∈ Γ ξ) :
    ∃ t : Finset (sphere (0 : E) 1), V \ {0} ⊆ ⋃ ξ ∈ t, Γ ξ := by
  obtain ⟨t, ht⟩ := ((isCompact_sphere (0 : E) 1).inter_left hV).elim_finite_subcover Γ hΓ
    fun ζ hζ ↦ mem_iUnion.2 ⟨⟨ζ, hζ.2⟩, hξΓ _ hζ.1⟩
  refine ⟨t, fun η hη ↦ ?_⟩
  -- The direction of `η` lies in one of the finitely many cones, hence so does `η`.
  have hη' : 0 < ‖η‖ := norm_pos_iff.2 hη.2
  obtain ⟨ξ, hξt, hηξ⟩ := mem_iUnion₂.1 (ht (show ‖η‖⁻¹ • η ∈ V ∩ sphere (0 : E) 1 from
    ⟨hVcone _ (inv_pos.2 hη') η hη.1, by simp [norm_smul, inv_mul_cancel₀ hη'.ne']⟩))
  exact mem_iUnion₂.2 ⟨ξ, hξt, by
    simpa [smul_smul, mul_inv_cancel₀ hη'.ne'] using hcone ξ ‖η‖ hη' _ hηξ⟩

/-- **Finitely many open cones cover the nonzero vectors.** If every unit vector `ξ` of a proper
real normed space lies in an open set `Γ ξ` closed under multiplication by positive reals, then
finitely many of these cones cover every nonzero vector: the unit sphere is compact. -/
theorem exists_finset_compl_singleton_subset_biUnion [NormedSpace ℝ E] [ProperSpace E]
    {Γ : sphere (0 : E) 1 → Set E} (hΓ : ∀ ξ, IsOpen (Γ ξ)) (hξΓ : ∀ ξ, (ξ : E) ∈ Γ ξ)
    (hcone : ∀ ξ, ∀ t : ℝ, 0 < t → ∀ η ∈ Γ ξ, t • η ∈ Γ ξ) :
    ∃ t : Finset (sphere (0 : E) 1), {0}ᶜ ⊆ ⋃ ξ ∈ t, Γ ξ := by
  simpa [compl_eq_univ_sdiff] using exists_finset_diff_singleton_subset_biUnion isClosed_univ
    (fun _ _ _ _ ↦ mem_univ _) hΓ (fun ξ _ ↦ hξΓ ξ) hcone

/-- **A uniform bound from a finite cover.** If finitely many sets `Γ ξ` cover the nonzero
elements of `V` and `f` is bounded by `C ξ` on each `Γ ξ`, then `f` is bounded on all of `V` by a
nonnegative constant. Combined with `TauCeti.exists_finset_diff_singleton_subset_biUnion`, this
turns estimates on open cones around each direction into one estimate on a closed cone. -/
theorem exists_forall_le_of_diff_singleton_subset_biUnion {X ι : Type*} [Zero X] {V : Set X}
    {t : Finset ι} {Γ : ι → Set X} (ht : V \ {0} ⊆ ⋃ ξ ∈ t, Γ ξ) {f : X → ℝ} {C : ι → ℝ}
    (hC : ∀ ξ ∈ t, ∀ η ∈ Γ ξ, f η ≤ C ξ) : ∃ C, 0 ≤ C ∧ ∀ η ∈ V, f η ≤ C := by
  have hsum : 0 ≤ ∑ ξ ∈ t, |C ξ| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  refine ⟨|f 0| + ∑ ξ ∈ t, |C ξ|, add_nonneg (abs_nonneg _) hsum, fun η hη ↦ ?_⟩
  rcases eq_or_ne η 0 with rfl | hη0
  · exact (le_abs_self _).trans (le_add_of_nonneg_right hsum)
  obtain ⟨ξ, hξt, hηΓ⟩ := mem_iUnion₂.1 (ht ⟨hη, hη0⟩)
  calc f η ≤ C ξ := hC ξ hξt η hηΓ
    _ ≤ |C ξ| := le_abs_self _
    _ ≤ ∑ ξ ∈ t, |C ξ| := Finset.single_le_sum (f := fun ξ ↦ |C ξ|) (fun _ _ ↦ abs_nonneg _) hξt
    _ ≤ |f 0| + ∑ ξ ∈ t, |C ξ| := le_add_of_nonneg_left (abs_nonneg _)

/-- **Finitely many neighbourhoods and cones over a compact set.** Given at each point `x` of a
compact set `K` a neighbourhood `U x` and an open set `Γ x`, in a possibly different space,
containing `ξ` and closed under multiplication by positive reals, finitely many of the interiors
of the `U x` cover `K`, and the intersection of the corresponding sets `Γ x` is again open,
contains `ξ` and is closed under multiplication by positive reals. -/
theorem exists_finset_subset_biUnion_interior_and_isOpen_cone {X F : Type*}
    [TopologicalSpace X] [TopologicalSpace F] [SMul ℝ F] {K : Set X} {ξ : F} (hK : IsCompact K)
    {U : K → Set X} {Γ : K → Set F} (hU : ∀ x : K, U x ∈ nhds (x : X))
    (hΓ : ∀ x, IsOpen (Γ x)) (hξΓ : ∀ x, ξ ∈ Γ x)
    (hcone : ∀ x, ∀ t : ℝ, 0 < t → ∀ η ∈ Γ x, t • η ∈ Γ x) :
    ∃ t : Finset K, K ⊆ ⋃ x ∈ t, interior (U x) ∧ IsOpen (⋂ x ∈ t, Γ x) ∧ ξ ∈ ⋂ x ∈ t, Γ x ∧
      ∀ c : ℝ, 0 < c → ∀ η ∈ ⋂ x ∈ t, Γ x, c • η ∈ ⋂ x ∈ t, Γ x := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K ↦ interior (U x))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hU ⟨x, hx⟩)⟩
  exact ⟨t, ht, isOpen_biInter_finset fun x _ ↦ hΓ x, mem_iInter₂.2 fun x _ ↦ hξΓ x,
    fun c hc η hη ↦ mem_iInter₂.2 fun x hx ↦ hcone x c hc η (mem_iInter₂.1 hη x hx)⟩

open Pointwise in
/-- The negative `-Γ` of a set closed under multiplication by positive reals is again closed under
multiplication by positive reals. -/
theorem forall_smul_mem_neg [Module ℝ E] {Γ : Set E}
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) :
    ∀ t : ℝ, 0 < t → ∀ η ∈ -Γ, t • η ∈ -Γ := fun t ht η hη ↦ by
  rw [Set.mem_neg, ← smul_neg]
  exact hcone t ht _ (Set.mem_neg.1 hη)

/-- The complement of a set closed under multiplication by positive reals is again closed under
multiplication by positive reals. -/
theorem forall_smul_mem_compl [Module ℝ E] {Γ : Set E}
    (hcone : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) :
    ∀ t : ℝ, 0 < t → ∀ η ∈ Γᶜ, t • η ∈ Γᶜ := fun t ht η hη htη ↦
  hη (by simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using hcone t⁻¹ (inv_pos.2 ht) _ htη)

open Pointwise in
/-- The sum `Γ₁ + Γ₂` of two sets closed under multiplication by positive reals is again closed
under multiplication by positive reals. -/
theorem forall_smul_mem_add [Module ℝ E] {Γ₁ Γ₂ : Set E}
    (hc₁ : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ₁, t • η ∈ Γ₁) (hc₂ : ∀ t : ℝ, 0 < t → ∀ η ∈ Γ₂, t • η ∈ Γ₂) :
    ∀ t : ℝ, 0 < t → ∀ η ∈ Γ₁ + Γ₂, t • η ∈ Γ₁ + Γ₂ := by
  rintro t ht _ ⟨a, ha, b, hb, rfl⟩
  exact ⟨t • a, hc₁ t ht a ha, t • b, hc₂ t ht b hb, (smul_add t a b).symm⟩

/-- Adjoining `0` to a set closed under multiplication by positive reals keeps it closed under
multiplication by positive reals. -/
theorem forall_smul_mem_insert_zero [Module ℝ E] {Γ : Set E}
    (hc : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ, t • ξ ∈ Γ) :
    ∀ t : ℝ, 0 < t → ∀ ξ ∈ insert 0 Γ, t • ξ ∈ insert 0 Γ := by
  rintro t ht ξ (rfl | hξ)
  · simp
  · exact Set.mem_insert_of_mem _ (hc t ht ξ hξ)

end TauCeti

namespace ContinuousLinearMap

open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {V : Set E}

/-- **A linear map is bounded below on a closed cone where it has no zeros.** Let `V` be a closed
subset of a proper real normed space closed under multiplication by positive reals. If a
continuous linear map `L` vanishes on no nonzero vector of `V`, then `‖η‖ ≤ c ‖L η‖` on `V` for
some `c ≥ 0`: the norm of `L` has a positive minimum on the compact set of unit vectors of `V`. -/
theorem exists_norm_le_mul_norm_apply_of_isClosed_cone_of_apply_eq_zero_imp (L : E →L[ℝ] F)
    (hV : IsClosed V) (hVcone : ∀ t : ℝ, 0 < t → ∀ η ∈ V, t • η ∈ V)
    (hL : ∀ η ∈ V, L η = 0 → η = 0) : ∃ c, 0 ≤ c ∧ ∀ η ∈ V, ‖η‖ ≤ c * ‖L η‖ := by
  set S := V ∩ sphere (0 : E) 1
  -- The direction of a nonzero vector of `V` is a unit vector of `V`.
  have hdir {η : E} (hη : η ∈ V) (hη0 : η ≠ 0) : ‖η‖⁻¹ • η ∈ S :=
    ⟨hVcone _ (inv_pos.2 (norm_pos_iff.2 hη0)) η hη,
      by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hη0)]⟩
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- Here `V ⊆ {0}`.
    refine ⟨0, le_rfl, fun η hη ↦ ?_⟩
    by_contra h
    have hη0 : η ≠ 0 := fun h0 ↦ h (by simp [h0])
    exact (hS ▸ hdir hη hη0 : _ ∈ (∅ : Set E))
  obtain ⟨ξ₀, hξ₀, hmin⟩ := ((isCompact_sphere (0 : E) 1).inter_left hV).exists_isMinOn hS
    (continuous_norm.comp L.continuous).continuousOn
  have hm : 0 < ‖L ξ₀‖ := norm_pos_iff.2 fun h ↦ by
    simpa [hL ξ₀ hξ₀.1 h] using hξ₀.2
  refine ⟨‖L ξ₀‖⁻¹, inv_nonneg.2 hm.le, fun η hη ↦ ?_⟩
  rcases eq_or_ne η 0 with rfl | hη0
  · simp
  have h := hmin (hdir hη hη0)
  simp only [mem_ofPred_eq, Function.comp_apply, map_smul, norm_smul, norm_inv, norm_norm] at h
  rw [inv_mul_eq_div, le_div_iff₀ (norm_pos_iff.2 hη0)] at h
  rw [inv_mul_eq_div, le_div_iff₀ hm, mul_comm]
  exact h

/-- **The image of a closed cone under a linear map without zeros on it is closed.** If a
continuous linear map `L` on a proper real normed space vanishes on no nonzero vector of a closed
cone `V`, then `L '' V` is closed: `L` is bounded below on `V`
(`ContinuousLinearMap.exists_norm_le_mul_norm_apply_of_isClosed_cone_of_apply_eq_zero_imp`), so
it tends to infinity along `V` (`TauCeti.isClosed_image_of_tendsto_cobounded`). -/
theorem isClosed_image_of_isClosed_cone_of_apply_eq_zero_imp (L : E →L[ℝ] F) (hV : IsClosed V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ η ∈ V, t • η ∈ V) (hL : ∀ η ∈ V, L η = 0 → η = 0) :
    IsClosed (L '' V) := by
  obtain ⟨c, hc, hle⟩ :=
    L.exists_norm_le_mul_norm_apply_of_isClosed_cone_of_apply_eq_zero_imp hV hVcone hL
  refine TauCeti.isClosed_image_of_tendsto_cobounded hV L.continuous.continuousOn ?_
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  refine tendsto_atTop_mono' _ ?_
    ((tendsto_norm_cobounded_atTop.mono_left inf_le_left).atTop_div_const (by positivity :
      (0 : ℝ) < c + 1))
  filter_upwards [mem_inf_of_right (mem_principal_self V)] with η hη
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hle η hη, norm_nonneg η, norm_nonneg (L η)]

end ContinuousLinearMap
