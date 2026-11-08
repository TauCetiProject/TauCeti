/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Pi

/-!
# Basic facts about bounded operators

A semilinear map into a normed space with bounded values vanishes
(`LinearMap.eq_zero_of_forall_norm_apply_le`). For continuous semilinear maps from a seminormed
space to a normed space, zero operator norm forces the map to vanish. The corresponding normed
group structure is available as an explicit construction, including for strong duals of
seminormed spaces.

This file also records a shared uniform-bound lemma for continuous linear maps between seminormed
spaces. It lets an evaluation `T i (g i)` pass to the limit when the operators `T i` are eventually
uniformly bounded, their values at the limiting argument converge, and the arguments `g i` converge.
In particular, it supplies the common continuity step for
`StronglyContinuousSemigroup.tendsto_realOperator_apply` and
`StronglyContinuousGroup.tendsto_apply`.

A left inverse `S` of `T` modulo an error term gives the estimate
`‖x‖ ≤ ‖S‖ ‖T x‖ + ‖(S ∘ T - 1) x‖`
(`ContinuousLinearMap.norm_le_opNorm_mul_norm_add_norm_comp_sub_one`).

Finally, an operator bounded below is injective
(`ContinuousLinearMap.injective_of_forall_norm_le`) and stays nonzero under a sufficiently small
perturbation (`ContinuousLinearMap.apply_add_ne_zero_of_forall_norm_le`), and is invertible if it
is also surjective
(`ContinuousLinearMap.isInvertible_of_surjective_of_forall_norm_le`), with inverse bounded by the
same constant (`ContinuousLinearMap.norm_inverse_apply_le_of_forall_norm_le`); an invertible
operator `A` on a normed space cancels against its inverse
(`ContinuousLinearMap.ringInverse_apply_apply`, `ContinuousLinearMap.apply_ringInverse_apply`)
and is bounded below by `‖A⁻¹‖⁻¹` (`ContinuousLinearMap.norm_le_norm_ringInverse_mul_norm_apply`),
and conversely a lower bound `‖x‖ ≤ M ‖A x‖` bounds the norm of the inverse by `M`
(`ContinuousLinearMap.norm_ringInverse_le_of_forall_norm_le`). An operator bounded below
is invertible if a sufficiently nearby operator is invertible
(`ContinuousLinearMap.isUnit_of_forall_mul_norm_le_of_norm_sub_lt`).

The diagonal sum `∑ i ∈ s, A (v i) (v i)` of a continuous bilinear map along vectors of norm at
most one, such as the trace of `A` along an orthonormal basis, is bounded by `#s * ‖A‖`
(`ContinuousLinearMap.norm_sum_apply_apply_le`).

Over `ℝ` or `ℂ`, two-sided norm bounds `1 - δ < ‖T v‖ < 1 + δ` on a `δ`-net of the unit sphere
extend to bounds `(1 - 3 δ) ‖v‖ ≤ ‖T v‖ ≤ (1 + 3 δ) ‖v‖` on the whole space
(`ContinuousLinearMap.norm_apply_bounds_of_net`).

A continuous bilinear map satisfies a Young-type bound
`‖B u v‖ ≤ ‖B‖ * ((c⁻¹ * ‖u‖ ^ 2 + c * ‖v‖ ^ 2) / 2)` for every `c > 0`
(`ContinuousLinearMap.norm_apply_apply_le_mul_add_sq`).

A **metric quotient map**, an operator `q` with `‖q‖ ≤ 1` lifting every vector of norm less than
`r` to a vector of norm less than `r`, maps each open ball about `0` onto the open ball of the same
radius (`ContinuousLinearMap.image_ball_eq_ball`).

Finite real products also admit coordinate-basis estimates and continuous linear equivalences
obtained by replacing one coordinate. The coordinate arguments are adapted from
[KLS](https://github.com/human-ai-mathematics/kls-lean), commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`,
`formalization/FunctionalInequalities/Analysis/`, files `PiCoordinates.lean` and
`Sard/CoordinateChange.lean`; the coordinate bound comes from `Sard/Disk.lean`.
-/

public section

open scoped Topology
open Filter

namespace LinearMap

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NormedField 𝕜₂] [AddCommGroup E]
  [Module 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]

/-- A semilinear map with bounded values is zero: scaling a vector with nonzero image by a scalar
of large norm makes its image arbitrarily large. -/
theorem eq_zero_of_forall_norm_apply_le {f : E →ₛₗ[σ] F} {C : ℝ} (h : ∀ x, ‖f x‖ ≤ C) :
    f = 0 := by
  ext x
  by_contra hx
  have hpos : 0 < ‖f x‖ := norm_pos_iff.2 hx
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 (C / ‖f x‖)
  have := h (c • x)
  rw [map_smulₛₗ, norm_smul, RingHomIsometric.norm_map] at this
  exact ((le_div_iff₀ hpos).2 this).not_gt hc

end LinearMap

namespace ContinuousLinearMap

section Semilinear

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]

/-- An operator from a seminormed space to a normed space has zero norm exactly when it is zero.
This generalizes `opNorm_zero_iff` to seminormed sources. -/
@[simp]
theorem opNorm_zero_iff' (f : E →SL[σ] F) : ‖f‖ = 0 ↔ f = 0 := by
  constructor
  · intro hf
    ext x
    exact norm_le_zero_iff.mp (by simpa only [hf, zero_mul] using f.le_opNorm x)
  · rintro rfl
    exact norm_zero

/-- The nonnegative operator norm vanishes exactly at zero, even for a seminormed source. -/
@[simp]
theorem opNNNorm_eq_zero_iff (f : E →SL[σ] F) : ‖f‖₊ = 0 ↔ f = 0 := by
  simpa only [← NNReal.coe_eq_zero, coe_nnnorm] using f.opNorm_zero_iff'

/-- The extended operator norm vanishes exactly at zero, even for a seminormed source. -/
@[simp]
theorem opENorm_eq_zero_iff (f : E →SL[σ] F) : ‖f‖ₑ = 0 ↔ f = 0 := by
  simpa only [enorm_eq_nnnorm, ENNReal.coe_eq_zero] using f.opNNNorm_eq_zero_iff

/-- Continuous semilinear maps from a seminormed space to a normed space form a normed group
for the operator norm. Use this construction locally when the source is only seminormed. -/
noncomputable abbrev normedAddCommGroup : NormedAddCommGroup (E →SL[σ] F) :=
  .ofSeparation fun f ↦ f.opNorm_zero_iff'.mp

end Semilinear

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- If `T i` is eventually uniformly bounded, `T i z` tends to `w`, and `g i` tends to `z`, then
the moving evaluations `T i (g i)` tend to `w`. -/
theorem tendsto_apply_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {T : ι → X →L[𝕜] Y} {C : ℝ} {g : ι → X} {z : X} {w : Y}
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) (hz : Tendsto (fun i => T i z) l (𝓝 w))
    (hg : Tendsto g l (𝓝 z)) : Tendsto (fun i => T i (g i)) l (𝓝 w) := by
  have hmove : Tendsto (fun i => T i (g i - z)) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => C * ‖g i - z‖) ?_ ?_
    · filter_upwards [hT] with i hi
      exact (T i).le_of_opNorm_le hi _
    · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hg).const_mul C
  simpa only [map_sub, sub_add_cancel, zero_add] using hmove.add hz

/-- The a priori estimate attached to a left inverse modulo an error term: since
`x = S (T x) - (S ∘ T - 1) x`, the norm of `x` is controlled by `‖T x‖` and the error
`(S ∘ T - 1) x`. When `S ∘ T - 1` is compact this is the compact-error estimate behind the
semi-Fredholm property. -/
theorem norm_le_opNorm_mul_norm_add_norm_comp_sub_one (T : X →L[𝕜] Y) (S : Y →L[𝕜] X) (x : X) :
    ‖x‖ ≤ ‖S‖ * ‖T x‖ + ‖(S.comp T - 1 : X →L[𝕜] X) x‖ := by
  have hx : x = S (T x) - (S.comp T - 1 : X →L[𝕜] X) x := by simp
  calc ‖x‖ = ‖S (T x) - (S.comp T - 1 : X →L[𝕜] X) x‖ := congrArg _ hx
    _ ≤ ‖S (T x)‖ + ‖(S.comp T - 1 : X →L[𝕜] X) x‖ := norm_sub_le _ _
    _ ≤ ‖S‖ * ‖T x‖ + ‖(S.comp T - 1 : X →L[𝕜] X) x‖ := by gcongr; exact S.le_opNorm _

section Inverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An operator bounded below, `‖x‖ ≤ M ‖f x‖`, is injective. -/
theorem injective_of_forall_norm_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →L[𝕜] F} {M : ℝ} (h : ∀ x, ‖x‖ ≤ M * ‖f x‖) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).mpr fun x hx ↦ norm_le_zero_iff.mp ?_
  simpa [hx] using h x

/-- An operator bounded below, `‖x‖ ≤ M ‖f x‖`, stays nonzero at `x ≠ 0` under a perturbation `w`
with `‖w‖ ≤ ε ‖x‖`, provided `M ε < 1`. -/
theorem apply_add_ne_zero_of_forall_norm_le {F : Type*} [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : E →L[𝕜] F} {M ε : ℝ} (h : ∀ x, ‖x‖ ≤ M * ‖f x‖) (hMε : M * ε < 1)
    {x : E} (hx : x ≠ 0) {w : F} (hw : ‖w‖ ≤ ε * ‖x‖) : f x + w ≠ 0 := by
  intro hsum
  have hfx : ‖f x‖ ≤ ε * ‖x‖ := by rwa [eq_neg_of_add_eq_zero_left hsum, norm_neg]
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hM : 0 < M := pos_of_mul_pos_left (hpos.trans_le (h x)) (norm_nonneg _)
  nlinarith [h x, mul_le_mul_of_nonneg_left hfx hM.le]

/-- A surjective continuous linear map that is bounded below, `‖x‖ ≤ C * ‖L x‖`, is invertible.
Neither space needs to be complete. -/
theorem isInvertible_of_surjective_of_forall_norm_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {L : E →L[𝕜] F} {C : ℝ}
    (hL : Function.Surjective L) (hC : ∀ x, ‖x‖ ≤ C * ‖L x‖) : L.IsInvertible := by
  let e := LinearEquiv.ofBijective (L : E →ₗ[𝕜] F) ⟨injective_of_forall_norm_le hC, hL⟩
  have he : ∀ x, e x = L x := fun x ↦ LinearEquiv.ofBijective_apply _ x
  -- `toContinuousLinearEquivOfBounds` has no coercion lemma; it applies as `e` by definition.
  refine ⟨e.toContinuousLinearEquivOfBounds ‖L‖ C L.le_opNorm fun y ↦ ?_, ext he⟩
  calc ‖e.symm y‖ ≤ C * ‖e (e.symm y)‖ := hC (e.symm y)
    _ = C * ‖y‖ := by rw [e.apply_symm_apply]

/-- The inverse of a surjective continuous linear map with `‖x‖ ≤ C * ‖L x‖` satisfies
`‖L⁻¹ y‖ ≤ C * ‖y‖`. -/
theorem norm_inverse_apply_le_of_forall_norm_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {L : E →L[𝕜] F} {C : ℝ}
    (hL : Function.Surjective L) (hC : ∀ x, ‖x‖ ≤ C * ‖L x‖) (y : F) :
    ‖L.inverse y‖ ≤ C * ‖y‖ := by
  simpa [(isInvertible_of_surjective_of_forall_norm_le hL hC).self_apply_inverse]
    using hC (L.inverse y)

/-- The inverse of an invertible operator undoes the operator. -/
@[simp]
theorem ringInverse_apply_apply {A : E →L[𝕜] E} (hA : IsUnit A) (x : E) :
    Ring.inverse A (A x) = x := by
  rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel A hA, one_apply_eq_self]

/-- An invertible operator undoes its inverse. -/
@[simp]
theorem apply_ringInverse_apply {A : E →L[𝕜] E} (hA : IsUnit A) (y : E) :
    A (Ring.inverse A y) = y := by
  rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel A hA, one_apply_eq_self]

/-- An invertible operator is bounded below by the reciprocal of the norm of its inverse. -/
theorem norm_le_norm_ringInverse_mul_norm_apply {A : E →L[𝕜] E} (hA : IsUnit A) (x : E) :
    ‖x‖ ≤ ‖Ring.inverse A‖ * ‖A x‖ := by
  calc
    ‖x‖ = ‖Ring.inverse A (A x)‖ := by rw [ringInverse_apply_apply hA]
    _ ≤ ‖Ring.inverse A‖ * ‖A x‖ := le_opNorm _ _

/-- An invertible operator bounded below by `M⁻¹` has an inverse of norm at most `M`. -/
theorem norm_ringInverse_le_of_forall_norm_le {A : E →L[𝕜] E} (hA : IsUnit A) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ x, ‖x‖ ≤ M * ‖A x‖) : ‖Ring.inverse A‖ ≤ M := by
  refine opNorm_le_bound _ hM fun y ↦ ?_
  simpa only [apply_ringInverse_apply hA] using h (Ring.inverse A y)

/-- An operator bounded below by `c > 0` is invertible if its distance from an invertible
operator is less than `c / 2`. -/
theorem isUnit_of_forall_mul_norm_le_of_norm_sub_lt [CompleteSpace E]
    {A B : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x : E, c * ‖x‖ ≤ ‖A x‖) (hB : IsUnit B) (hAB : ‖A - B‖ < c / 2) :
    IsUnit A := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hA : A = 1 := Subsingleton.elim _ _
    rw [hA]
    exact isUnit_one
  obtain ⟨u, rfl⟩ := hB
  -- The nearby invertible operator retains at least half the lower bound.
  have hlow (x : E) : c / 2 * ‖x‖ ≤ ‖(u : E →L[𝕜] E) x‖ := by
    have h := norm_add_le ((A - (u : E →L[𝕜] E)) x) ((u : E →L[𝕜] E) x)
    simp only [sub_apply, sub_add_cancel] at h
    have hdist := mul_le_mul_of_nonneg_right hAB.le (norm_nonneg x)
    have hn := (A - (u : E →L[𝕜] E)).le_opNorm x
    rw [sub_apply] at hn
    have hb := hbound x
    nlinarith
  have hinv : ‖(↑u⁻¹ : E →L[𝕜] E)‖ ≤ 2 / c := by
    rw [← Ring.inverse_unit]
    apply norm_ringInverse_le_of_forall_norm_le u.isUnit (by positivity)
    intro x
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have h := hlow x
    nlinarith
  -- The inverse bound places `A` within Mathlib's nearby-unit radius.
  have hnear : ‖A - (u : E →L[𝕜] E)‖ < ‖(↑u⁻¹ : E →L[𝕜] E)‖⁻¹ := by
    rw [← one_div, lt_div_iff₀ (Units.norm_pos u⁻¹)]
    calc ‖A - (u : E →L[𝕜] E)‖ * ‖(↑u⁻¹ : E →L[𝕜] E)‖ ≤
          ‖A - (u : E →L[𝕜] E)‖ * (2 / c) :=
            mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ < 1 := by
        have hpos : 0 < 2 / c := by positivity
        have h := mul_lt_mul_of_pos_right hAB hpos
        have heq : (c / 2) * (2 / c) = 1 := by field_simp
        rwa [heq] at h
  exact (u.ofNearby A hnear).isUnit

end Inverse

/-- The diagonal sum `∑ i ∈ s, A (v i) (v i)` of a continuous bilinear map along vectors of norm
at most one is bounded by `#s * ‖A‖`. Along an orthonormal basis this bounds the trace of `A` by
the dimension times its norm. -/
theorem norm_sum_apply_apply_le {ι : Type*} (s : Finset ι) (A : X →L[𝕜] X →L[𝕜] Y)
    {v : ι → X} (hv : ∀ i ∈ s, ‖v i‖ ≤ 1) : ‖∑ i ∈ s, A (v i) (v i)‖ ≤ s.card * ‖A‖ := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (g := fun _ ↦ ‖A‖) fun i hi ↦ ?_).trans_eq
    (by simp))
  calc ‖A (v i) (v i)‖ ≤ ‖A‖ * ‖v i‖ * ‖v i‖ := ((A (v i)).le_opNorm _).trans <|
        mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖A‖ * 1 * 1 := by gcongr <;> exact hv i hi
    _ = ‖A‖ := by ring

section Young

variable {𝕜 X Y Z : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup X]
  [NormedSpace 𝕜 X] [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y] [SeminormedAddCommGroup Z]
  [NormedSpace 𝕜 Z]

/-- A Young-type bound for a continuous bilinear map: for every `c > 0`,
`‖B u v‖ ≤ ‖B‖ * ((c⁻¹ * ‖u‖ ^ 2 + c * ‖v‖ ^ 2) / 2)`. -/
theorem norm_apply_apply_le_mul_add_sq (B : X →L[𝕜] Y →L[𝕜] Z) {c : ℝ} (hc : 0 < c) (u : X)
    (v : Y) : ‖B u v‖ ≤ ‖B‖ * ((c⁻¹ * ‖u‖ ^ 2 + c * ‖v‖ ^ 2) / 2) := by
  refine (B.le_opNorm₂ _ _).trans ?_
  rw [mul_assoc]
  gcongr
  have h := two_mul_le_add_mul_sq (a := ‖u‖) (b := ‖v‖) (inv_pos.2 hc)
  rw [inv_inv] at h
  linarith

end Young

section Net

variable {𝕜 V F : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Two-sided bounds `1 - δ < ‖T v‖ < 1 + δ` on a `δ`-net of the unit sphere, for `δ ≤ 1 / 6`,
give `(1 - 3 δ) ‖v‖ ≤ ‖T v‖ ≤ (1 + 3 δ) ‖v‖` everywhere. -/
theorem norm_apply_bounds_of_net (T : V →L[𝕜] F) {t : Set V} {δ : ℝ}
    (hnear : ∀ w : V, ‖w‖ = 1 → ∃ v ∈ t, ‖w - v‖ < δ)
    (hlow : ∀ v ∈ t, 1 - δ < ‖T v‖) (hup : ∀ v ∈ t, ‖T v‖ < 1 + δ) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 6) :
    (∀ v, (1 - 3 * δ) * ‖v‖ ≤ ‖T v‖) ∧ ∀ v, ‖T v‖ ≤ (1 + 3 * δ) * ‖v‖ := by
  -- Propagate the upper bound to the unit sphere, and then bound `‖T‖`.
  have hTnorm : ‖T‖ ≤ 1 + 3 * δ := by
    have hbound : ‖T‖ ≤ 1 + δ + ‖T‖ * δ := by
      refine T.opNorm_le_of_unit_norm (by positivity) fun w hw ↦ ?_
      obtain ⟨v, hv, hwv⟩ := hnear w hw
      calc ‖T w‖ = ‖T v + T (w - v)‖ := by rw [map_sub, add_sub_cancel]
        _ ≤ ‖T v‖ + ‖T (w - v)‖ := norm_add_le _ _
        _ ≤ (1 + δ) + ‖T‖ * δ := by
          gcongr
          · exact (hup v hv).le
          · exact (T.le_opNorm _).trans (by gcongr)
    nlinarith [norm_nonneg T]
  -- The lower bound on the unit sphere.
  have hsphere : ∀ w : V, ‖w‖ = 1 → 1 - 3 * δ ≤ ‖T w‖ := by
    intro w hw
    obtain ⟨v, hv, hwv⟩ := hnear w hw
    have hTwv : ‖T (w - v)‖ ≤ (1 + 3 * δ) * δ :=
      (T.le_opNorm _).trans (mul_le_mul hTnorm hwv.le (norm_nonneg _) (by positivity))
    have : ‖T v‖ ≤ ‖T w‖ + ‖T (w - v)‖ := by
      calc ‖T v‖ = ‖T w - T (w - v)‖ := by rw [map_sub, sub_sub_cancel]
        _ ≤ ‖T w‖ + ‖T (w - v)‖ := norm_sub_le _ _
    nlinarith [hlow v hv]
  refine ⟨fun v ↦ ?_, fun v ↦ (T.le_opNorm v).trans (by gcongr)⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hTv : ‖T v‖ = ‖v‖ * ‖T ((‖v‖⁻¹ : 𝕜) • v)‖ := by
    simp [norm_smul, hv]
  rw [hTv, mul_comm]
  exact mul_le_mul_of_nonneg_left (hsphere _ (norm_smul_inv_norm hv)) (norm_nonneg v)

end Net

section MetricQuotient

variable {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]

/-- A **metric quotient map** maps each open ball onto the open ball of the same radius: if
`‖q‖ ≤ 1` and `q` lifts every vector of norm less than `r` to a vector of norm less than `r`,
then `q` maps each open ball about `0` onto the open ball of the same radius. -/
theorem image_ball_eq_ball {q : E →SL[σ₁₂] F} (h₁ : ‖q‖ ≤ 1)
    (h : ∀ r, Metric.ball (0 : F) r ⊆ q '' Metric.ball 0 r) (r : ℝ) :
    q '' Metric.ball 0 r = Metric.ball 0 r := by
  refine subset_antisymm ?_ (h r)
  have h' : ‖q‖₊ ≤ 1 := by rwa [← NNReal.coe_le_one, coe_nnnorm]
  simpa using ((q.lipschitzWith.weaken h').mapsTo_ball one_ne_zero 0 r).image_subset

end MetricQuotient

end ContinuousLinearMap

end

public section

/-- A nonzero functional on a finite real product is nonzero on some coordinate vector. -/
theorem ContinuousLinearMap.exists_apply_single_ne_zero {ι : Type*} [Finite ι] [DecidableEq ι]
    (α : (ι → ℝ) →L[ℝ] ℝ) (hα : α ≠ 0) : ∃ i : ι, α (Pi.single i (1 : ℝ)) ≠ 0 := by
  let := Fintype.ofFinite ι
  by_contra h
  push Not at h
  refine hα (ContinuousLinearMap.ext fun v => ?_)
  have hv : v = ∑ i : ι, v i • Pi.single i (1 : ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  simp [map_sum, h]

/-- A coordinate bound for a functional on a finite real product bounds its value on every
vector, using the cardinality of the index set and the product norm. -/
theorem ContinuousLinearMap.abs_apply_le_card_mul_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) {M : ℝ}
    (h : ∀ j, |L (Pi.single j (1 : ℝ))| ≤ M) :
    |L v| ≤ Fintype.card ι * ‖v‖ * M := by
  have hv : v = ∑ j : ι, v j • Pi.single j (1 : ℝ) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  calc |L v| = |∑ j : ι, v j * L (Pi.single j (1 : ℝ))| := by
        conv_lhs => rw [hv]
        simp [map_sum, smul_eq_mul]
    _ ≤ ∑ j : ι, |v j * L (Pi.single j (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, ‖v‖ * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v j) (h j)
          (abs_nonneg _) (norm_nonneg _)
    _ = Fintype.card ι * ‖v‖ * M := by simp [Finset.sum_const, mul_assoc]

/-- Replacing one coordinate by a linear functional is injective when its coefficient at
that coordinate is nonzero. -/
theorem ContinuousLinearMap.pi_update_injective {ι : Type*} [DecidableEq ι]
    (α : (ι → ℝ) →L[ℝ] ℝ) (i : ι) (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    Function.Injective (ContinuousLinearMap.pi fun m : ι ↦
      if m = i then α else ContinuousLinearMap.proj m) := by
  intro v₁ v₂ hv
  rw [← sub_eq_zero]
  set v : ι → ℝ := v₁ - v₂ with hvdef
  have h0 : (ContinuousLinearMap.pi fun m : ι =>
      if m = i then α else ContinuousLinearMap.proj m) v = 0 := by
    rw [hvdef, map_sub, hv, sub_self]
  have hoff : ∀ m, m ≠ i → v m = 0 := by
    intro m hm
    have := congrFun h0 m
    simpa [ContinuousLinearMap.pi_apply, hm] using this
  have hsingle : v = v i • Pi.single i (1 : ℝ) := by
    funext m
    rcases eq_or_ne m i with rfl | hm
    · simp
    · simp [hoff m hm, hm]
  have hαv : α v = 0 := by
    have := congrFun h0 i
    simpa [ContinuousLinearMap.pi_apply] using this
  rw [hsingle, map_smul, smul_eq_mul] at hαv
  have hvi : v i = 0 := by
    rcases mul_eq_zero.mp hαv with h | h
    · exact h
    · exact absurd h hα
  rw [hsingle, hvi, zero_smul]

/-- Replacing one coordinate by a functional with a nonzero coefficient at that coordinate
is a continuous linear equivalence. -/
theorem ContinuousLinearMap.exists_pi_update_equiv {ι : Type*} [Finite ι] [DecidableEq ι]
    (α : (ι → ℝ) →L[ℝ] ℝ) (i : ι) (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    ∃ e : (ι → ℝ) ≃L[ℝ] (ι → ℝ),
      (e : (ι → ℝ) →L[ℝ] (ι → ℝ)) =
        ContinuousLinearMap.pi fun m : ι ↦ if m = i then α else ContinuousLinearMap.proj m := by
  refine ⟨(LinearEquiv.ofInjectiveEndo _ (α.pi_update_injective i hα)).toContinuousLinearEquiv, ?_⟩
  ext v m
  rfl

end
