/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sylvester.Bound
public import Mathlib.Algebra.Group.Semiconj.Units
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach

/-! # Coercive bounded operators are units

For a bounded operator `N` on a Hilbert space over `𝕜 = ℝ, ℂ` whose quadratic
form is uniformly coercive, `c * ‖z‖ ^ 2 ≤ re ⟪N z, z⟫` with `c > 0`, the
operator `N` is invertible in `E →L[𝕜] E`.  This is the operator-level
Lax–Milgram lemma; the inverse is then available through `Ring.inverse` or
through `IsUnit.unit`.

## Staging note

Staged for Tau Ceti, roadmap topic T16.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/CoerciveUnit.lean`
(new file).
Formalized by Claude Fable 5 (claude-fable-5[1m]) while closing the graph
projection formula of the Davis–Kahan graph-subspace correspondence.  This is
the operator form of the Lax–Milgram lemma on a Hilbert space: a uniformly
coercive bounded operator is invertible in the algebra of bounded operators.
No self-adjointness is required — coercivity alone forces injectivity, a
closed range, and a trivial orthogonal complement of the range.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `00ca5e1`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Intended Mathlib home: additions to `Mathlib/Analysis/InnerProductSpace/CoerciveUnit.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- A uniformly coercive bounded operator on a Hilbert space is bounded
below. -/
theorem norm_smul_le_norm_apply_of_coercive {N : E →L[𝕜] E} {c : ℝ}
    (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) (z : E) :
    c * ‖z‖ ≤ ‖N z‖ := by
  rcases eq_or_ne z 0 with hz | hz
  · simp [hz]
  · have h1 : c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜 := hcoer z
    have h2 : RCLike.re ⟪N z, z⟫_𝕜 ≤ ‖N z‖ * ‖z‖ :=
      calc RCLike.re ⟪N z, z⟫_𝕜 ≤ ‖⟪N z, z⟫_𝕜‖ := RCLike.re_le_norm _
        _ ≤ ‖N z‖ * ‖z‖ := norm_inner_le_norm _ _
    have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have h3 : c * ‖z‖ * ‖z‖ ≤ ‖N z‖ * ‖z‖ := by nlinarith
    exact le_of_mul_le_mul_right h3 hzpos

/-- Operator Lax–Milgram: a uniformly coercive bounded operator on a Hilbert
space is a unit of the algebra of bounded operators. -/
theorem isUnit_of_coercive {N : E →L[𝕜] E} {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) : IsUnit N := by
  have hlow := norm_smul_le_norm_apply_of_coercive hcoer
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro a b hab
    have h1 : N (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 := hlow (a - b)
    rw [h1, norm_zero] at h2
    have h3 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
    rw [← sub_eq_zero]
    exact norm_le_zero_iff.mp h3
  · have hanti : AntilipschitzWith (Real.toNNReal c)⁻¹ N := by
      refine ContinuousLinearMap.antilipschitz_of_bound N ?_
      intro x
      have hcoe : (((Real.toNNReal c)⁻¹ : NNReal) : ℝ) = c⁻¹ := by
        rw [NNReal.coe_inv, Real.coe_toNNReal c hc.le]
      rw [hcoe, le_inv_mul_iff₀ hc]
      exact hlow x
    have hclosed :
        IsClosed ((LinearMap.range (N : E →ₗ[𝕜] E) : Submodule 𝕜 E) : Set E) := by
      rw [LinearMap.coe_range]
      exact hanti.isClosed_range N.uniformContinuous
    have : CompleteSpace (LinearMap.range (N : E →ₗ[𝕜] E)) :=
      hclosed.completeSpace_coe
    have : (LinearMap.range (N : E →ₗ[𝕜] E)).HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    have hrange : LinearMap.range (N : E →ₗ[𝕜] E) = ⊤ := by
      rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
      intro z hz
      have h0 : ⟪N z, z⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal _ z).mp hz (N z)
          (LinearMap.mem_range.mpr ⟨z, rfl⟩)
      have h1 := hcoer z
      rw [h0, map_zero] at h1
      have h2 : ‖z‖ ^ 2 ≤ 0 := by nlinarith
      have h3 : ‖z‖ = 0 :=
        (pow_eq_zero_iff two_ne_zero).mp (le_antisymm h2 (sq_nonneg _))
      exact norm_eq_zero.mp h3
    exact LinearMap.range_eq_top.mp hrange

/-- `1 + W⋆ W` is invertible for every bounded Hilbert-space operator `W`:
its quadratic form dominates `‖z‖ ^ 2`, so the operator Lax–Milgram lemma
applies. -/
theorem isUnit_one_add_star_mul_self (W : E →L[𝕜] E) :
    IsUnit (1 + star W * W) := by
  refine isUnit_of_coercive one_pos fun z => ?_
  have h : (1 + star W * W) z = z + star W (W z) := rfl
  rw [h]
  simp only [inner_add_left, map_add, inner_self_eq_norm_sq,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  nlinarith [sq_nonneg ‖W z‖]

omit [CompleteSpace E] in
/-- Cauchy–Schwarz for the semi-inner product induced by a positive symmetric
operator, in operator-norm form: `‖B y‖ ^ 2 ≤ ‖B‖ * re ⟪B y, y⟫`.  The proof
evaluates the nonnegative quadratic form at `y - ‖B‖⁻¹ • B y`; no square
roots or functional calculus are involved. -/
theorem norm_apply_sq_le_of_positive {B : E →L[𝕜] E}
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    (hBpos : ∀ z, 0 ≤ RCLike.re ⟪B z, z⟫_𝕜) (y : E) :
    ‖B y‖ ^ 2 ≤ ‖B‖ * RCLike.re ⟪B y, y⟫_𝕜 := by
  rcases eq_or_lt_of_le (norm_nonneg B) with hs | hs
  · have hB0 : B = 0 := norm_eq_zero.mp hs.symm
    simp [hB0]
  · set t : ℝ := ‖B‖⁻¹ with htdef
    have ht : 0 < t := inv_pos.mpr hs
    have hts : t * ‖B‖ = 1 := inv_mul_cancel₀ hs.ne'
    have hsym : ⟪B (B y), y⟫_𝕜 = ⟪B y, B y⟫_𝕜 := hB (B y) y
    have h1 : ⟪B (y - (t : 𝕜) • B y), y - (t : 𝕜) • B y⟫_𝕜
        = ⟪B y, y⟫_𝕜 - (t : 𝕜) * ⟪B y, B y⟫_𝕜 - (t : 𝕜) * ⟪B y, B y⟫_𝕜
          + (t : 𝕜) * ((t : 𝕜) * ⟪B (B y), B y⟫_𝕜) := by
      rw [map_sub, map_smul]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left,
        inner_smul_right, RCLike.conj_ofReal]
      rw [hsym]
      ring
    have h2 : (0 : ℝ) ≤ RCLike.re ⟪B y, y⟫_𝕜 - t * ‖B y‖ ^ 2 - t * ‖B y‖ ^ 2
        + t * (t * RCLike.re ⟪B (B y), B y⟫_𝕜) := by
      have h0 := hBpos (y - (t : 𝕜) • B y)
      rw [h1] at h0
      simpa [map_sub, map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
        using h0
    have h3 : RCLike.re ⟪B (B y), B y⟫_𝕜 ≤ ‖B‖ * ‖B y‖ ^ 2 := by
      calc RCLike.re ⟪B (B y), B y⟫_𝕜 ≤ ‖⟪B (B y), B y⟫_𝕜‖ := RCLike.re_le_norm _
        _ ≤ ‖B (B y)‖ * ‖B y‖ := norm_inner_le_norm _ _
        _ ≤ (‖B‖ * ‖B y‖) * ‖B y‖ :=
            mul_le_mul_of_nonneg_right (B.le_opNorm (B y)) (norm_nonneg _)
        _ = ‖B‖ * ‖B y‖ ^ 2 := by ring
    have key : t * (t * RCLike.re ⟪B (B y), B y⟫_𝕜) ≤ t * ‖B y‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ ht.le
      calc t * RCLike.re ⟪B (B y), B y⟫_𝕜 ≤ t * (‖B‖ * ‖B y‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h3 ht.le
        _ = ‖B y‖ ^ 2 := by rw [← mul_assoc, hts, one_mul]
    have h7 : t * ‖B y‖ ^ 2 ≤ RCLike.re ⟪B y, y⟫_𝕜 := by linarith
    calc ‖B y‖ ^ 2 = ‖B‖ * (t * ‖B y‖ ^ 2) := by
          rw [← mul_assoc, mul_comm ‖B‖ t, hts, one_mul]
      _ ≤ ‖B‖ * RCLike.re ⟪B y, y⟫_𝕜 :=
          mul_le_mul_of_nonneg_left h7 (norm_nonneg B)

/-- The arithmetic core of the lower bound: if the "energy" `c` and the
"square" `d` of a positive operator at a unit vector satisfy `c² ≤ d` and the
Cauchy–Schwarz consequence `c + d ≤ K (1 + 2c + d)`, then `K` already dominates
`c / (1 + c)`.

Stated over plain reals because that is all it is; in the application
`c = re ⟪B u, u⟫`, `d = ‖B u‖²` and `K = ‖1 - (1 + B)⁻¹‖`. -/
private lemma div_one_add_le_of_sq_le {c d K : ℝ} (hc : 0 ≤ c)
    (hcd : c ^ 2 ≤ d) (h : c + d ≤ K * (1 + 2 * c + d)) :
    c / (1 + c) ≤ K := by
  have hd : 0 ≤ d := le_trans (sq_nonneg c) hcd
  have hD : (0 : ℝ) < 1 + 2 * c + d := by linarith
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + c)]
  have h9 : c * (1 + 2 * c + d) ≤ (c + d) * (1 + c) := by nlinarith [hcd]
  have h10 : c * (1 + 2 * c + d) ≤ (K * (1 + c)) * (1 + 2 * c + d) := by
    calc c * (1 + 2 * c + d) ≤ (c + d) * (1 + c) := h9
      _ ≤ (K * (1 + 2 * c + d)) * (1 + c) :=
          mul_le_mul_of_nonneg_right h (by linarith)
      _ = (K * (1 + c)) * (1 + 2 * c + d) := by ring
  exact le_of_mul_le_mul_right h10 hD

/-- The limit that turns the family of near-maximizer bounds into the sharp
constant: `(b - ε)² / (b + (b - ε)²) → b / (1 + b)` as `ε ↓ 0` inside `Ioo 0 b`.

Pure real analysis; `b = ‖B‖` at the use site. -/
private lemma tendsto_sub_sq_div_add_sub_sq {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto (fun ε : ℝ => (b - ε) ^ 2 / (b + (b - ε) ^ 2))
      (nhdsWithin 0 (Set.Ioo 0 b)) (nhds (b / (1 + b))) := by
  have hden : b + (b - 0) ^ 2 ≠ 0 := by nlinarith
  have h1 : Filter.Tendsto (fun ε : ℝ => (b - ε) ^ 2 / (b + (b - ε) ^ 2))
      (nhds 0) (nhds ((b - 0) ^ 2 / (b + (b - 0) ^ 2))) := by
    refine Filter.Tendsto.div ?_ ?_ hden
    · exact (((continuous_const.sub continuous_id).pow 2).tendsto 0)
    · exact ((continuous_const.add
        ((continuous_const.sub continuous_id).pow 2)).tendsto 0)
  have h2 : (b - 0) ^ 2 / (b + (b - 0) ^ 2) = b / (1 + b) := by
    rw [sub_zero, div_eq_div_iff (by nlinarith) (by linarith)]
    ring
  rw [← h2]
  exact h1.mono_left nhdsWithin_le_nhds

/-- **Passing to the limit in the lower bound.**  If `b/(1+b)` is approached from below by the
family `(b-ε)²/(b + (b-ε)²)` and every member is `≤ K`, then so is the limit.

Pure real analysis, stated separately because it is the only place in
`norm_one_sub_inverse_one_add` where anything topological happens: the rest of the lower bound is
Cauchy--Schwarz and algebra. -/
private theorem div_one_add_le_of_forall_sub_sq_le {b K : ℝ} (hb : 0 < b)
    (h : ∀ ε ∈ Set.Ioo (0 : ℝ) b, (b - ε) ^ 2 / (b + (b - ε) ^ 2) ≤ K) :
    b / (1 + b) ≤ K := by
  have hcont := tendsto_sub_sq_div_add_sub_sq (b := b) hb
  have : (nhdsWithin (0 : ℝ) (Set.Ioo 0 b)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo hb.ne]
    exact ⟨le_refl 0, hb.le⟩
  exact le_of_tendsto hcont
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using h ε hε)

omit [CompleteSpace E] in
/-- Cauchy--Schwarz bound on the quadratic form of a bounded operator. -/
private theorem re_inner_apply_self_le_norm_mul_sq (B : E →L[𝕜] E) (y : E) :
    RCLike.re ⟪B y, y⟫_𝕜 ≤ ‖B‖ * ‖y‖ ^ 2 := by
  calc RCLike.re ⟪B y, y⟫_𝕜 ≤ ‖⟪B y, y⟫_𝕜‖ := RCLike.re_le_norm _
    _ ≤ ‖B y‖ * ‖y‖ := norm_inner_le_norm _ _
    _ ≤ (‖B‖ * ‖y‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right (B.le_opNorm y) (norm_nonneg _)
    _ = ‖B‖ * ‖y‖ ^ 2 := by ring

omit [CompleteSpace E] in
/-- Expansion of `‖(1 + B) y‖²`.  The two cross terms are conjugate, so they add to twice the real
part — no self-adjointness of `B` is needed, only conjugate symmetry of the inner product. -/
private theorem norm_one_add_apply_sq (B : E →L[𝕜] E) (y : E) :
    ‖(1 + B) y‖ ^ 2 = ‖y‖ ^ 2 + 2 * RCLike.re ⟪B y, y⟫_𝕜 + ‖B y‖ ^ 2 := by
  have hNy : (1 + B) y = y + B y := rfl
  have hswap : RCLike.re ⟪y, B y⟫_𝕜 = RCLike.re ⟪B y, y⟫_𝕜 := by
    rw [← inner_conj_symm, RCLike.conj_re]
  rw [hNy, norm_add_sq (𝕜 := 𝕜), hswap]

/-- Exact operator norm of `1 - (1 + B)⁻¹` for a positive operator `B`:
the value is `‖B‖ / (1 + ‖B‖)`.  The inverse is interpreted through
`Ring.inverse`; the operator `1 + B` is coercive, so this is a genuine
inverse.  The upper bound is the quadratic-form estimate along the
substitution `z = (1 + B) y`; the lower bound follows from near-maximizers
of `‖B‖` transported through the positive-operator Cauchy–Schwarz
inequality, with a limit along small `ε`. -/
theorem norm_one_sub_inverse_one_add {B : E →L[𝕜] E} (hB : IsSelfAdjoint B)
    (hBpos : ∀ z, 0 ≤ RCLike.re ⟪B z, z⟫_𝕜) :
    ‖1 - Ring.inverse (1 + B)‖ = ‖B‖ / (1 + ‖B‖) := by
  rcases eq_or_lt_of_le (norm_nonneg B) with hs | hs
  · have hB0 : B = 0 := norm_eq_zero.mp hs.symm
    rw [hB0, add_zero, Ring.inverse_one, sub_self, norm_zero]
    norm_num
  set N : E →L[𝕜] E := 1 + B with hNdef
  have hNcoer : ∀ z, (1 : ℝ) * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜 := by
    intro z
    have hNz : N z = z + B z := rfl
    rw [hNz, inner_add_left, map_add, inner_self_eq_norm_sq]
    have := hBpos z
    linarith
  have hNunit : IsUnit N := isUnit_of_coercive one_pos hNcoer
  set R : E →L[𝕜] E := Ring.inverse N with hRdef
  have hNR : N * R = 1 := Ring.mul_inverse_cancel N hNunit
  have hRN : R * N = 1 := Ring.inverse_mul_cancel N hNunit
  have hCB : (1 - R) * N = B := by
    calc (1 - R) * N = N - R * N := by rw [sub_mul, one_mul]
      _ = N - 1 := by rw [hRN]
      _ = B := by rw [hNdef, add_sub_cancel_left]
  have hNsa : star N = N := by rw [hNdef, star_add, star_one, hB.star_eq]
  have hRsa : star R = R := by
    have h1 : N * star R = 1 := by
      have h := congrArg star hRN
      rwa [star_mul, star_one, hNsa] at h
    calc star R = (R * N) * star R := by rw [hRN, one_mul]
      _ = R * (N * star R) := by rw [mul_assoc]
      _ = R := by rw [h1, mul_one]
  have hCsa : IsSelfAdjoint (1 - R) := by
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change star (1 - R) = 1 - R
    rw [star_sub, star_one, hRsa]
  have hbs : ∀ y, RCLike.re ⟪B y, y⟫_𝕜 ≤ ‖B‖ * ‖y‖ ^ 2 :=
    re_inner_apply_self_le_norm_mul_sq B
  have hNsq : ∀ y, ‖N y‖ ^ 2
      = ‖y‖ ^ 2 + 2 * RCLike.re ⟪B y, y⟫_𝕜 + ‖B y‖ ^ 2 :=
    norm_one_add_apply_sq B
  have hval : ∀ y, RCLike.re ⟪(1 - R) (N y), N y⟫_𝕜
      = RCLike.re ⟪B y, y⟫_𝕜 + ‖B y‖ ^ 2 := by
    intro y
    have hCNy : (1 - R) (N y) = B y := DFunLike.congr_fun hCB y
    have hNy : N y = y + B y := rfl
    rw [hCNy, hNy, inner_add_right, map_add, inner_self_eq_norm_sq]
  have hupper : ‖1 - R‖ ≤ ‖B‖ / (1 + ‖B‖) := by
    have hkey : ∀ y,
        |RCLike.re ⟪(1 - R) (N y), N y⟫_𝕜| ≤ (‖B‖ / (1 + ‖B‖)) * ‖N y‖ ^ 2 := by
      intro y
      have hb0 := hBpos y
      have hb := hbs y
      have hc := norm_apply_sq_le_of_positive hB.isSymmetric hBpos y
      rw [hval y, hNsq y, abs_of_nonneg (by positivity)]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0 : ℝ) < 1 + ‖B‖)]
      nlinarith [hb, hc]
    refine norm_le_of_abs_re_inner_map_self_le hCsa.isSymmetric
      (div_nonneg hs.le (by linarith)) ?_
    intro z
    have h := hkey (R z)
    have hNRz : N (R z) = z := DFunLike.congr_fun hNR z
    rwa [hNRz] at h
  have hlower : ‖B‖ / (1 + ‖B‖) ≤ ‖1 - R‖ := by
    have hstep : ∀ u : E, ‖u‖ ≤ 1 →
        RCLike.re ⟪B u, u⟫_𝕜 / (1 + RCLike.re ⟪B u, u⟫_𝕜) ≤ ‖1 - R‖ := by
      intro u hu
      have hb0 := hBpos u
      have hc2 : RCLike.re ⟪B u, u⟫_𝕜 ^ 2 ≤ ‖B u‖ ^ 2 := by
        have h1 : RCLike.re ⟪B u, u⟫_𝕜 ≤ ‖B u‖ := by
          calc RCLike.re ⟪B u, u⟫_𝕜 ≤ ‖⟪B u, u⟫_𝕜‖ := RCLike.re_le_norm _
            _ ≤ ‖B u‖ * ‖u‖ := norm_inner_le_norm _ _
            _ ≤ ‖B u‖ * 1 := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
            _ = ‖B u‖ := mul_one _
        nlinarith [norm_nonneg (B u)]
      have hCS : RCLike.re ⟪(1 - R) (N u), N u⟫_𝕜 ≤ ‖1 - R‖ * ‖N u‖ ^ 2 := by
        calc RCLike.re ⟪(1 - R) (N u), N u⟫_𝕜
            ≤ ‖⟪(1 - R) (N u), N u⟫_𝕜‖ := RCLike.re_le_norm _
          _ ≤ ‖(1 - R) (N u)‖ * ‖N u‖ := norm_inner_le_norm _ _
          _ ≤ (‖1 - R‖ * ‖N u‖) * ‖N u‖ :=
              mul_le_mul_of_nonneg_right ((1 - R).le_opNorm _) (norm_nonneg _)
          _ = ‖1 - R‖ * ‖N u‖ ^ 2 := by ring
      rw [hval u, hNsq u] at hCS
      have husq : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
      have hK0 : (0 : ℝ) ≤ ‖1 - R‖ := norm_nonneg _
      have h8 : RCLike.re ⟪B u, u⟫_𝕜 + ‖B u‖ ^ 2
          ≤ ‖1 - R‖ * (1 + 2 * RCLike.re ⟪B u, u⟫_𝕜 + ‖B u‖ ^ 2) := by
        nlinarith [hCS]
      exact div_one_add_le_of_sq_le hb0 hc2 h8
    have hstep2 : ∀ ε ∈ Set.Ioo (0 : ℝ) ‖B‖,
        (‖B‖ - ε) ^ 2 / (‖B‖ + (‖B‖ - ε) ^ 2) ≤ ‖1 - R‖ := by
      intro ε hε
      obtain ⟨u, hu1, hu2⟩ :=
        B.exists_lt_apply_of_lt_opNorm (r := ‖B‖ - ε) (by linarith [hε.1])
      have hb0 := hBpos u
      have hcs := norm_apply_sq_le_of_positive hB.isSymmetric hBpos u
      have hbge : (‖B‖ - ε) ^ 2 / ‖B‖ ≤ RCLike.re ⟪B u, u⟫_𝕜 := by
        rw [div_le_iff₀ hs]
        have hsq : (‖B‖ - ε) * (‖B‖ - ε) ≤ ‖B u‖ * ‖B u‖ :=
          mul_self_le_mul_self (by linarith [hε.2]) hu2.le
        nlinarith [hcs, hsq]
      have hmono := hstep u hu1.le
      have hmono2 : (‖B‖ - ε) ^ 2 / (‖B‖ + (‖B‖ - ε) ^ 2)
          ≤ RCLike.re ⟪B u, u⟫_𝕜 / (1 + RCLike.re ⟪B u, u⟫_𝕜) := by
        have hr2 : (‖B‖ - ε) ^ 2 ≤ RCLike.re ⟪B u, u⟫_𝕜 * ‖B‖ := by
          rw [div_le_iff₀ hs] at hbge
          linarith
        rw [div_le_div_iff₀ (by nlinarith [sq_nonneg (‖B‖ - ε)]) (by linarith)]
        nlinarith [hr2, sq_nonneg (‖B‖ - ε)]
      linarith
    exact div_one_add_le_of_forall_sub_sq_le hs hstep2
  exact le_antisymm hupper hlower

/-! ## `Ring.inverse` and semiconjugation

This module's own summary says the inverse of a coercive operator "is then
available through `Ring.inverse` or through `IsUnit.unit`".  These two lemmas are
about that choice.  **Mathlib states the semiconjugation-respects-inverses fact
only in the `Units` spelling** (`SemiconjBy.units_inv_right`), and every
operator-algebra argument here gets its invertibility as `IsUnit` and its inverse
through `Ring.inverse`, so using the Mathlib lemma means unfolding by hand at
every site.  That unfolding was written out as the same six-line `calc` in
**three** theorems of `DavisKahan/SpectralTheory/GraphSubspace.lean`, which is
the file this module was written to support.

They are stated for a `MonoidWithZero` and mention no inner product; they live
here because this is where the `IsUnit`-to-`Ring.inverse` seam is already
documented, and because `ForTauCeti`'s module-to-topic partition is total, so a
general-algebra subtree would need a new roadmap topic.  See
`{lane:ALG-PROMOTE-SEMICONJ}`. -/

end ContinuousLinearMap

namespace TauCeti

/-- **`Ring.inverse` respects semiconjugation.**

If `a` semiconjugates a unit `n` to a unit `m` — that is, `a * n = m * a` — then
it semiconjugates their inverses.  This is `SemiconjBy.units_inv_right` in the
`Ring.inverse` spelling. -/
theorem ringInverse_semiconj {M : Type*} [MonoidWithZero M] {a n m : M}
    (hn : IsUnit n) (hm : IsUnit m) (h : a * n = m * a) :
    a * Ring.inverse n = Ring.inverse m * a := by
  obtain ⟨un, rfl⟩ := hn
  obtain ⟨um, rfl⟩ := hm
  rw [Ring.inverse_unit, Ring.inverse_unit]
  exact SemiconjBy.units_inv_right h

/-- The commuting case, which is the one that actually appears: if `a` commutes
with a unit `n`, it commutes with `Ring.inverse n`. -/
theorem commute_ringInverse {M : Type*} [MonoidWithZero M] {a n : M}
    (hn : IsUnit n) (h : Commute a n) : Commute a (Ring.inverse n) :=
  ringInverse_semiconj hn hn h

/-- `Ring.inverse` commutes with `star` on units. -/
theorem star_ringInverse {A : Type*} [Ring A] [StarRing A] {a : A} (ha : IsUnit a) :
    star (Ring.inverse a) = Ring.inverse (star a) := by
  have hstar : IsUnit (star a) := ha.star
  have h1 : star a * Ring.inverse (star a) = 1 := Ring.mul_inverse_cancel _ hstar
  have h2 : star (Ring.inverse a) * star a = 1 := by
    rw [← star_mul, Ring.mul_inverse_cancel a ha, star_one]
  calc
    star (Ring.inverse a)
        = star (Ring.inverse a) * (star a * Ring.inverse (star a)) := by
            rw [h1, mul_one]
    _ = (star (Ring.inverse a) * star a) * Ring.inverse (star a) := by
          rw [mul_assoc]
    _ = Ring.inverse (star a) := by rw [h2, one_mul]

end TauCeti
