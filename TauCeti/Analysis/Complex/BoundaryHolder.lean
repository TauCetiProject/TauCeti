/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import TauCeti.Analysis.Calculus.DiffContOnCl
public import TauCeti.Analysis.Complex.AbsMax
public import TauCeti.Analysis.Complex.Basic
public import TauCeti.Analysis.SpecialFunctions.Pow.Sector
public import TauCeti.Topology.MetricSpace.Holder
import TauCeti.Analysis.Complex.CircleRotation

/-!
# Hölder boundary values of holomorphic functions on a disc

Let `f` be complex differentiable on a disc `ball c R` and continuous on its closure, with values
in a complex normed space, and let `0 ≤ α < 1`. If the boundary values of `f` are `α`-Hölder
continuous on the circle `sphere c R` with constant `C`, then `f` is `α`-Hölder continuous on the
whole closed disc, with constant `C / cos (α π / 2)`
(`DiffContOnCl.holderOnWith_closedBall`). This is the theorem of Privalov and of Hardy and
Littlewood on the boundary regularity of holomorphic functions: Hölder regularity on the boundary
costs nothing in the interior. It is the boundary estimate behind the Hölder theory of the
Cauchy–Riemann operator on the disc with totally real boundary conditions, where a holomorphic
correction with prescribed Hölder boundary data has to be Hölder continuous up to the boundary.

The exponent `1` is excluded, and the constant blows up as `α → 1`: Lipschitz boundary values do
not make a holomorphic function Lipschitz on the closed disc.

The same holds one derivative higher, which is the form used for `C^{1,α}` regularity up to the
boundary. Let `f` be holomorphic on the open unit disc and continuous on the closed one, with
values in a complex Banach space, and let `0 < α < 1`. Suppose that at each point `w` of the unit
circle the boundary values have a derivative `v w` along the rotations, that is of
`t ↦ f (e^{it} w)` at `t = 0`, and that `v` is `α`-Hölder on the circle. Then the tangential
derivative `(I z) • f' z` extends to an `α`-Hölder function on the closed disc equal to `v` on the
circle (`DiffContOnCl.exists_holderOnWith_closedBall_smul_deriv`), and so does `f'` itself, with
boundary values `(I w)⁻¹ • v w` (`DiffContOnCl.exists_holderOnWith_closedBall_deriv`). Indeed, the
difference quotients `(f (e^{it} z) - f z) / t` are holomorphic, within `C |t| ^ α` of `v` on the
circle by the mean value inequality, and hence uniformly Cauchy on the closed disc by the maximum
modulus principle; their limit is continuous on the closed disc and is the tangential derivative
inside, so the first part of the file applies to it. Dividing by `I z` away from the centre, and
using the boundedness of `f''` near the centre, gives the statement for `f'`.

The proof uses no integral representation. Write `k = cos (α π / 2)`, which is positive for
`α < 1`.

* **A harmonic majorant at a boundary point.** For `w₀` on the unit circle and `z` in the closed
  unit disc, `1 - conj w₀ * z` has nonnegative real part and norm `‖z - w₀‖`, so the holomorphic
  function `(1 - conj w₀ * z) ^ α` has real part between `k ‖z - w₀‖ ^ α` and `‖z - w₀‖ ^ α`. If
  `‖f w - f w₀‖ ≤ C ‖w - w₀‖ ^ α` on the circle, then `‖f - f w₀‖` is bounded on the circle by the
  real part of `(C / k) (1 - conj w₀ * z) ^ α`, hence on the closed disc, by
  `Complex.norm_le_re_of_forall_mem_frontier_norm_le_re`. This gives
  `k ‖f z - f w₀‖ ≤ C ‖z - w₀‖ ^ α` between interior points and boundary points.
* **Rotations.** For `‖u‖ = 1`, the function `z ↦ f (u z) - f z` vanishes at `0` and is bounded
  by `C ‖u - 1‖ ^ α` on the circle, so by Schwarz's lemma it is bounded by `C ‖u - 1‖ ^ α ‖z‖` on
  the closed disc.
* **Rescaling.** For `0 < r ≤ 1`, the rotation bound shows that `ξ ↦ f (r ξ)` has `α`-Hölder
  boundary values with constant `C r ^ α`, using `r ≤ r ^ α`. Applying the boundary-point
  estimate to it, with `r = ‖z‖` and the boundary point `z / r`, compares `f z` with `f z'` for
  every `z'` with `‖z'‖ ≤ ‖z‖`.

## Main results

* `DiffContOnCl.holderOnWith_closedBall`: Hölder boundary values give a Hölder function on the
  closed disc.
* `DiffContOnCl.exists_holderOnWith_closedBall_smul_deriv`: a Hölder tangential derivative on the
  circle gives a Hölder tangential derivative on the closed unit disc.
* `DiffContOnCl.exists_holderOnWith_closedBall_deriv`: a Hölder tangential derivative on the circle
  gives a derivative that extends to a Hölder function on the closed unit disc.

## References

* G. H. Hardy and J. E. Littlewood, *Some properties of fractional integrals. II*, Math. Z. 34
  (1932), 403–439.
* P. L. Duren, *Theory of Hᵖ Spaces*, Academic Press, 1970, Chapter 5 (mean growth and
  smoothness: Hölder boundary values of holomorphic functions on the disc).
-/

public section

open Metric Set Complex Filter Topology
open scoped NNReal Real ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E}

namespace DiffContOnCl

/-- The comparison function `(C / k) (1 - conj w₀ * z) ^ α` is differentiable on the open unit
disc and continuous on the closed one. -/
private theorem diffContOnCl_cpow (w₀ : ℂ) (hw₀ : ‖w₀‖ = 1) {α : ℝ} (hα0 : 0 ≤ α) (a : ℂ) :
    DiffContOnCl ℂ (fun z ↦ a * (1 - conj w₀ * z) ^ (α : ℂ)) (ball (0 : ℂ) 1) := by
  rcases hα0.eq_or_lt with rfl | hα
  · simpa using diffContOnCl_const
  refine DiffContOnCl.mk_ball (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · have hre := re_one_sub_conj_mul_pos hw₀ (mem_ball_zero_iff.mp hz)
    exact (((differentiableAt_const _).sub ((differentiableAt_const _).mul
      differentiableAt_id)).cpow_const (mem_slitPlane_iff.mpr (Or.inl hre))).const_mul _
      |>.differentiableWithinAt
  · have hcont : ContinuousAt (fun z : ℂ ↦ (1 - conj w₀ * z) ^ (α : ℂ)) z :=
      (continuousAt_cpow_const_of_re_pos
        (Or.inl (re_one_sub_conj_mul_nonneg hw₀ (mem_closedBall_zero_iff.mp hz)))
        (show 0 < (α : ℂ).re by simpa using hα)).comp
        (f := fun z : ℂ ↦ 1 - conj w₀ * z) (by fun_prop)
    exact (continuousAt_const.mul hcont).continuousWithinAt

/-- **The boundary-point estimate.** If `f` is differentiable on the open unit disc and continuous
on the closed one, and `‖f w - f w₀‖ ≤ C ‖w - w₀‖ ^ α` for `w` on the unit circle, where `w₀` is
on the unit circle and `0 ≤ α < 1`, then `cos (α π / 2) ‖f z - f w₀‖ ≤ C ‖z - w₀‖ ^ α` on the
closed unit disc. -/
private theorem cos_mul_norm_sub_le_of_mem_sphere (hf : DiffContOnCl ℂ f (ball 0 1)) {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) {C : ℝ≥0} {w₀ : ℂ} (hw₀ : ‖w₀‖ = 1)
    (h : ∀ w ∈ sphere (0 : ℂ) 1, ‖f w - f w₀‖ ≤ C * ‖w - w₀‖ ^ α) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) :
    Real.cos (α * π / 2) * ‖f z - f w₀‖ ≤ C * ‖z - w₀‖ ^ α := by
  set k := Real.cos (α * π / 2)
  have hk : 0 < k := TauCeti.cos_mul_pi_div_two_pos hα0 hα1
  -- The real part of `G` is a harmonic majorant of `‖f - f w₀‖` on the circle.
  set G : ℂ → ℂ := fun z ↦ ((C / k : ℝ) : ℂ) * (1 - conj w₀ * z) ^ (α : ℂ)
  have hre (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) :
      C * ‖z - w₀‖ ^ α ≤ (G z).re ∧ (G z).re ≤ C / k * ‖z - w₀‖ ^ α := by
    have hcos := TauCeti.cos_mul_norm_le_re_cpow hα0 (by linarith)
      (re_one_sub_conj_mul_nonneg hw₀ (mem_closedBall_zero_iff.mp hz))
    have hnorm := (re_le_norm ((1 - conj w₀ * z) ^ (α : ℂ))).trans_eq (norm_cpow_real _ _)
    rw [norm_cpow_real, norm_one_sub_conj_mul hw₀] at hcos
    rw [norm_one_sub_conj_mul hw₀] at hnorm
    simp only [G, re_ofReal_mul]
    constructor
    · calc (C : ℝ) * ‖z - w₀‖ ^ α = C / k * (k * ‖z - w₀‖ ^ α) := by field_simp
        _ ≤ C / k * ((1 - conj w₀ * z) ^ (α : ℂ)).re := by gcongr
    · gcongr
  have hmaj := Complex.norm_le_re_of_forall_mem_frontier_norm_le_re isBounded_ball
    (hf.sub_const (f w₀)) (diffContOnCl_cpow w₀ hw₀ hα0 _)
    (by
      rw [frontier_ball (0 : ℂ) one_ne_zero]
      exact fun w hw ↦ (h w hw).trans (hre w (sphere_subset_closedBall hw)).1)
    (z := z) (by rwa [closure_ball (0 : ℂ) one_ne_zero])
  calc k * ‖f z - f w₀‖ ≤ k * (C / k * ‖z - w₀‖ ^ α) :=
        mul_le_mul_of_nonneg_left (hmaj.trans (hre z hz).2) hk.le
    _ = C * ‖z - w₀‖ ^ α := by field_simp

/-- **Rotations.** If `f` is differentiable on the open unit disc and continuous on the closed
one, `‖u‖ = 1`, and `‖f (u w) - f w‖ ≤ M` for `w` on the unit circle, then
`‖f (u z) - f z‖ ≤ M ‖z‖` on the closed unit disc, by Schwarz's lemma. -/
private theorem norm_sub_le_mul_norm_of_mem_sphere (hf : DiffContOnCl ℂ f (ball 0 1)) {u : ℂ}
    (hu : ‖u‖ = 1) {M : ℝ} (h : ∀ w ∈ sphere (0 : ℂ) 1, ‖f (u * w) - f w‖ ≤ M) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) : ‖f (u * z) - f z‖ ≤ M * ‖z‖ := by
  have hg : DiffContOnCl ℂ (fun w ↦ f (u * w) - f w) (ball 0 1) :=
    (hf.comp_const_mul hu.le).sub hf
  rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with hz1 | hz1
  · have hbound : MapsTo (fun w ↦ f (u * w) - f w) (ball (0 : ℂ) 1)
        (closedBall (f (u * 0) - f 0) M) := fun w hw ↦ by
      simp only [mul_zero, sub_self, mem_closedBall_zero_iff]
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg ?_
        (subset_closure hw)
      rwa [frontier_ball (0 : ℂ) one_ne_zero]
    have := dist_le_div_mul_dist_of_mapsTo_ball hg.differentiableOn hbound
      (mem_ball_zero_iff.mpr hz1)
    simpa using this
  · simpa [hz1] using h z (mem_sphere_zero_iff_norm.mpr hz1)

/-- **Rescaling.** If `f` has `α`-Hölder boundary values on the unit circle with constant `C`, for
`α ≤ 1`, then for `0 < r ≤ 1` the boundary values of `ξ ↦ f (r ξ)` are `α`-Hölder with constant
`C r ^ α`. -/
private theorem norm_sub_le_of_mem_sphere_mul (hf : DiffContOnCl ℂ f (ball 0 1)) {α : ℝ}
    (hα1 : α ≤ 1) {C : ℝ≥0}
    (h : ∀ w ∈ sphere (0 : ℂ) 1, ∀ w' ∈ sphere (0 : ℂ) 1, ‖f w - f w'‖ ≤ C * ‖w - w'‖ ^ α)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {w w₀ : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) (hw₀ : ‖w₀‖ = 1) :
    ‖f (r * w) - f (r * w₀)‖ ≤ (C * r.toNNReal ^ α : ℝ≥0) * ‖w - w₀‖ ^ α := by
  have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw1]; exact one_ne_zero)
  -- `r w₀` is the rotation of `r w` by `u = w₀ / w`.
  set u := w₀ / w
  have hu : ‖u‖ = 1 := by rw [norm_div, hw₀, hw1, div_one]
  have hu1 : ‖u - 1‖ = ‖w - w₀‖ := by
    have : u - 1 = (w₀ - w) / w := by rw [sub_div, div_self hw0]
    simp [this, hw1, norm_sub_rev]
  have hrot := norm_sub_le_mul_norm_of_mem_sphere hf hu (M := C * ‖w - w₀‖ ^ α)
    (fun v hv ↦ by
      have hv1 : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
      have huv : u * v ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_mul, hu, hv1, one_mul]
      have := h _ huv v hv
      rwa [← sub_one_mul, norm_mul, hv1, mul_one, hu1] at this)
    (z := r * w) (by
      rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_of_nonneg hr.le, hw1, mul_one]
      exact hr1)
  have huw : u * (r * w) = r * w₀ := by
    rw [mul_left_comm, div_mul_cancel₀ w₀ hw0]
  rw [huw, norm_sub_rev, norm_mul, Complex.norm_of_nonneg hr.le, hw1, mul_one] at hrot
  push_cast
  rw [Real.coe_toNNReal _ hr.le]
  calc ‖f (r * w) - f (r * w₀)‖ ≤ C * ‖w - w₀‖ ^ α * r := hrot
    _ ≤ C * ‖w - w₀‖ ^ α * r ^ α := by
      gcongr
      exact Real.self_le_rpow_of_le_one hr.le hr1 hα1
    _ = C * r ^ α * ‖w - w₀‖ ^ α := by ring

/-- The unit disc case of `DiffContOnCl.holderOnWith_closedBall`, stated with norms. -/
private theorem cos_mul_norm_sub_le (hf : DiffContOnCl ℂ f (ball 0 1)) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {C : ℝ≥0}
    (h : ∀ w ∈ sphere (0 : ℂ) 1, ∀ w' ∈ sphere (0 : ℂ) 1, ‖f w - f w'‖ ≤ C * ‖w - w'‖ ^ α)
    {z z' : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (hz' : z' ∈ closedBall (0 : ℂ) 1) :
    Real.cos (α * π / 2) * ‖f z - f z'‖ ≤ C * ‖z - z'‖ ^ α := by
  wlog hle : ‖z'‖ ≤ ‖z‖ generalizing z z'
  · rw [norm_sub_rev (f z), norm_sub_rev z]
    exact this hz' hz (le_of_not_ge hle)
  rcases (norm_nonneg z).eq_or_lt with hr | hr
  · have hz0 : z = 0 := norm_eq_zero.mp hr.symm
    have hz'0 : z' = 0 := norm_eq_zero.mp (le_antisymm (hle.trans hr.symm.le) (norm_nonneg _))
    simp only [hz0, hz'0, sub_self, norm_zero, mul_zero]
    positivity
  -- Rescale by `r = ‖z‖`, so that `z` becomes the boundary point `w₀ = z / r`.
  set r := ‖z‖
  have hr1 : r ≤ 1 := mem_closedBall_zero_iff.mp hz
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  set w₀ : ℂ := z / r
  have hw₀ : ‖w₀‖ = 1 := by
    rw [norm_div, Complex.norm_of_nonneg hr.le, div_self hr.ne']
  have hrw₀ : (r : ℂ) * w₀ = z := mul_div_cancel₀ z hr0
  have hfr : DiffContOnCl ℂ (fun ξ ↦ f (r * ξ)) (ball 0 1) :=
    hf.comp_const_mul (by rwa [Complex.norm_of_nonneg hr.le])
  -- The rescaled function has `α`-Hölder boundary values with constant `C r ^ α`.
  have hbd (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 1) :=
    norm_sub_le_of_mem_sphere_mul hf hα1.le h hr hr1 hw hw₀
  have hz'r : z' / r ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall_zero_iff, norm_div, Complex.norm_of_nonneg hr.le]
    exact div_le_one_of_le₀ hle hr.le
  have key := cos_mul_norm_sub_le_of_mem_sphere hfr hα0 hα1 hw₀ hbd hz'r
  have hrz' : (r : ℂ) * (z' / r) = z' := mul_div_cancel₀ z' hr0
  rw [hrz', hrw₀, norm_sub_rev (f z')] at key
  have hdist : r * ‖z' / r - w₀‖ = ‖z - z'‖ := by
    calc r * ‖z' / r - w₀‖ = ‖(r : ℂ)‖ * ‖z' / r - w₀‖ := by
          rw [Complex.norm_of_nonneg hr.le]
      _ = ‖z - z'‖ := by rw [← norm_mul, mul_sub, hrz', hrw₀, norm_sub_rev]
  refine key.trans_eq ?_
  push_cast
  rw [Real.coe_toNNReal _ hr.le, mul_assoc, ← Real.mul_rpow hr.le (norm_nonneg _), hdist]

/-- **Privalov's theorem on a disc.** Let `f` be complex differentiable on `ball c R` and
continuous on its closure, with values in a complex normed space, and let `0 ≤ α < 1`. If `f` is
`α`-Hölder continuous on the circle `sphere c R` with constant `C`, then `f` is `α`-Hölder
continuous on the closed disc `closedBall c R`, with constant `C / cos (α π / 2)`. -/
theorem holderOnWith_closedBall {c : ℂ} {R : ℝ} {C α : ℝ≥0} (hf : DiffContOnCl ℂ f (ball c R))
    (hα : α < 1) (h : HolderOnWith C α f (sphere c R)) :
    HolderOnWith (C / (Real.cos (α * π / 2)).toNNReal) α f (closedBall c R) := by
  rcases le_or_gt R 0 with hR | hR
  · exact (subsingleton_closedBall c hR).holderOnWith _ _ _
  have hα1 : (α : ℝ) < 1 := by exact_mod_cast hα
  have hk : 0 < Real.cos (α * π / 2) := TauCeti.cos_mul_pi_div_two_pos α.coe_nonneg hα1
  -- Transport `f` to the unit disc by the affine map `ξ ↦ c + R ξ`.
  have hR0 : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  set A : ℂ → ℂ := fun ξ ↦ c + R * ξ
  have hA (ξ ξ' : ℂ) : ‖A ξ - A ξ'‖ = R * ‖ξ - ξ'‖ := by
    simp only [A, add_sub_add_left_eq_sub, ← mul_sub, norm_mul, Complex.norm_of_nonneg hR.le]
  have hAc (ξ : ℂ) : ‖A ξ - c‖ = R * ‖ξ‖ := by simpa [A] using hA ξ 0
  have hmaps : MapsTo A (ball (0 : ℂ) 1) (ball c R) := fun ξ hξ ↦ by
    rw [mem_ball_zero_iff] at hξ
    rw [mem_ball, dist_eq_norm, hAc]
    nlinarith
  have hg : DiffContOnCl ℂ (f ∘ A) (ball 0 1) :=
    hf.comp ((differentiable_const c).add (differentiable_id.const_mul (R : ℂ))).diffContOnCl
      hmaps
  have hsphere {ξ : ℂ} (hξ : ξ ∈ sphere (0 : ℂ) 1) : A ξ ∈ sphere c R := by
    rw [mem_sphere_zero_iff_norm] at hξ
    rw [mem_sphere, dist_eq_norm, hAc, hξ, mul_one]
  have hgbd (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 1) (w' : ℂ) (hw' : w' ∈ sphere (0 : ℂ) 1) :
      ‖(f ∘ A) w - (f ∘ A) w'‖ ≤ (C * R.toNNReal ^ (α : ℝ) : ℝ≥0) * ‖w - w'‖ ^ (α : ℝ) := by
    have := h.dist_le (hsphere hw) (hsphere hw')
    rw [dist_eq_norm, dist_eq_norm, hA, Real.mul_rpow hR.le (norm_nonneg _), ← mul_assoc] at this
    push_cast
    rwa [Real.coe_toNNReal _ hR.le]
  refine HolderOnWith.of_dist_le fun z hz z' hz' ↦ ?_
  -- Pull `z` and `z'` back to the unit disc.
  have hpull {x : ℂ} (hx : x ∈ closedBall c R) :
      (x - c) / R ∈ closedBall (0 : ℂ) 1 ∧ A ((x - c) / R) = x := by
    refine ⟨?_, by simp only [A]; rw [mul_div_cancel₀ _ hR0, add_sub_cancel]⟩
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall_zero_iff, norm_div, Complex.norm_of_nonneg hR.le]
    exact div_le_one_of_le₀ hx hR.le
  obtain ⟨hξ, hAξ⟩ := hpull hz
  obtain ⟨hξ', hAξ'⟩ := hpull hz'
  have key := cos_mul_norm_sub_le hg α.coe_nonneg hα1 hgbd hξ hξ'
  have hpow : (R.toNNReal : ℝ) ^ (α : ℝ) * ‖(z - c) / R - (z' - c) / R‖ ^ (α : ℝ) =
      ‖z - z'‖ ^ (α : ℝ) := by
    rw [Real.coe_toNNReal _ hR.le, ← Real.mul_rpow hR.le (norm_nonneg _), ← hA, hAξ, hAξ']
  simp only [Function.comp_apply, hAξ, hAξ', NNReal.coe_mul, NNReal.coe_rpow, mul_assoc,
    hpow] at key
  calc dist (f z) (f z') = ‖f z - f z'‖ := dist_eq_norm _ _
    _ ≤ C * ‖z - z'‖ ^ (α : ℝ) / Real.cos (α * π / 2) := by rw [le_div_iff₀ hk]; linarith
    _ = _ := by rw [dist_eq_norm, NNReal.coe_div, Real.coe_toNNReal _ hk.le]; ring

/-! ### Hölder derivatives up to the boundary -/

section Deriv

variable {v : ℂ → E} {C α : ℝ≥0}

/-- Along the rotations of a boundary point `w`, `f (e^{it} w) - f w` differs from `t v(w)` by at
most `C |t| ^ α |t|`, when `v` is the derivative of `f` along the rotations and is `α`-Hölder on
the circle with constant `C`. -/
private theorem norm_sub_sub_smul_le
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ f (exp (I * t) * w)) (v w) 0)
    (h : HolderOnWith C α v (sphere 0 1)) {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) (t : ℝ) :
    ‖f (exp (I * t) * w) - f w - t • v w‖ ≤ C * |t| ^ (α : ℝ) * |t| := by
  have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
  have hrot (s : ℝ) : exp (I * s) * w ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_mul, norm_exp_I_mul_ofReal, hw1, one_mul]
  -- `u ↦ f (e^{iu} w) - u v(w)` has derivative `v (e^{is} w) - v w` at `s`.
  have hψ (s : ℝ) : HasDerivAt (fun u : ℝ ↦ f (exp (I * u) * w) - u • v w)
      (v (exp (I * s) * w) - v w) s := by
    have hlin : HasDerivAt (fun u : ℝ ↦ u • v w) (v w) s := by
      simpa using (hasDerivAt_id s).smul_const (v w)
    exact (TauCeti.hasDerivAt_comp_exp_I_mul_mul hv hw s).sub hlin
  have hbound : ∀ s ∈ uIcc 0 t, ‖v (exp (I * s) * w) - v w‖ ≤ C * |t| ^ (α : ℝ) := by
    intro s hs
    have hst : |s| ≤ |t| := by simpa using abs_sub_left_of_mem_uIcc hs
    calc ‖v (exp (I * s) * w) - v w‖ ≤ C * ‖exp (I * s) * w - w‖ ^ (α : ℝ) := by
          simpa [dist_eq_norm] using h.dist_le (hrot s) hw
      _ ≤ C * |t| ^ (α : ℝ) := by
          gcongr
          rw [← sub_one_mul, norm_mul, hw1, mul_one]
          exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (by rwa [Real.norm_eq_abs])
  have := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ ↦ (hψ s).hasDerivWithinAt) hbound left_mem_uIcc right_mem_uIcc
  calc ‖f (exp (I * t) * w) - f w - t • v w‖ =
        ‖(f (exp (I * t) * w) - t • v w) - (f (exp (I * (0 : ℝ)) * w) - (0 : ℝ) • v w)‖ := by
        congr 1; simp only [ofReal_zero, mul_zero, exp_zero, one_mul, zero_smul]; abel
    _ ≤ C * |t| ^ (α : ℝ) * ‖t - 0‖ := this
    _ = C * |t| ^ (α : ℝ) * |t| := by rw [sub_zero, Real.norm_eq_abs]

/-- The difference quotients of `f` along the rotation by the angle `t` are differentiable on the
open unit disc and continuous on the closed one. -/
private theorem diffContOnCl_slope (hf : DiffContOnCl ℂ f (ball 0 1)) (t : ℝ) :
    DiffContOnCl ℂ (fun z ↦ (t : ℂ)⁻¹ • (f (exp (I * t) * z) - f z)) (ball 0 1) := by
  exact ((hf.comp_const_mul (norm_exp_I_mul_ofReal t).le).sub hf).const_smul _

/-- On the circle, the difference quotients along the rotations are within `C |t| ^ α` of `v`. -/
private theorem norm_slope_sub_le
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ f (exp (I * t) * w)) (v w) 0)
    (h : HolderOnWith C α v (sphere 0 1)) {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) {t : ℝ}
    (ht : t ≠ 0) : ‖(t : ℂ)⁻¹ • (f (exp (I * t) * w) - f w) - v w‖ ≤ C * |t| ^ (α : ℝ) := by
  have hts : (t : ℂ)⁻¹ • (f (exp (I * t) * w) - f w) - v w =
      (t : ℂ)⁻¹ • (f (exp (I * t) * w) - f w - t • v w) := by
    rw [smul_sub (t : ℂ)⁻¹ _ (t • v w), ← Complex.coe_smul, smul_smul,
      inv_mul_cancel₀ (ofReal_ne_zero.mpr ht), one_smul]
  rw [hts, norm_smul, norm_inv, norm_real, Real.norm_eq_abs]
  calc |t|⁻¹ * ‖f (exp (I * t) * w) - f w - t • v w‖ ≤ |t|⁻¹ * (C * |t| ^ (α : ℝ) * |t|) := by
        gcongr; exact norm_sub_sub_smul_le hv h hw t
    _ = C * |t| ^ (α : ℝ) := by field_simp

/-- Inside the disc, the difference quotients along the rotations tend to `(I z) • f' z`. -/
private theorem tendsto_slope (hf : DiffContOnCl ℂ f (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    Tendsto (fun s : ℝ ↦ (s : ℂ)⁻¹ • (f (exp (I * s) * z) - f z)) (𝓝[≠] 0)
      (𝓝 ((I * z) • deriv f z)) := by
  have hrot : HasDerivAt (fun s : ℝ ↦ exp (I * s) * z) (I * z) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul I).cexp).mul_const z
  have hd := (hf.differentiableAt isOpen_ball hz).hasDerivAt.scomp_of_eq 0 hrot (by simp)
  refine hd.tendsto_slope.congr' (Filter.Eventually.of_forall fun s ↦ ?_)
  simp [slope_def_module, ← Complex.coe_smul]

/-- Inside the disc, the difference quotients along the rotations are within `C |t| ^ α` of
`(I z) • f' z`: two difference quotients differ on the circle, hence on the disc, by at most
`C (|t| ^ α + |s| ^ α)`, and the second one tends to `(I z) • f' z` as `s → 0`, while
`C |s| ^ α` tends to `0`. -/
private theorem norm_slope_sub_smul_deriv_le (hf : DiffContOnCl ℂ f (ball 0 1))
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ f (exp (I * t) * w)) (v w) 0)
    (h : HolderOnWith C α v (sphere 0 1))
    (hpow : Tendsto (fun s : ℝ ↦ (C : ℝ) * |s| ^ (α : ℝ)) (𝓝[≠] 0) (𝓝 0)) {t : ℝ} (ht : t ≠ 0)
    {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    ‖(t : ℂ)⁻¹ • (f (exp (I * t) * z) - f z) - (I * z) • deriv f z‖ ≤ C * |t| ^ (α : ℝ) := by
  set S : ℝ → ℂ → E := fun s z ↦ (s : ℂ)⁻¹ • (f (exp (I * s) * z) - f z)
  have hcomp (s : ℝ) (hs : s ≠ 0) :
      ‖S t z - S s z‖ ≤ C * |t| ^ (α : ℝ) + C * |s| ^ (α : ℝ) := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      ((diffContOnCl_slope hf t).sub (diffContOnCl_slope hf s)) (fun w hw ↦ ?_)
      (subset_closure hz)
    rw [frontier_ball (0 : ℂ) one_ne_zero] at hw
    calc ‖S t w - S s w‖ = ‖(S t w - v w) - (S s w - v w)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖S t w - v w‖ + ‖S s w - v w‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_slope_sub_le hv h hw ht) (norm_slope_sub_le hv h hw hs)
  have hlim : Tendsto (fun s : ℝ ↦ ‖S t z - S s z‖) (𝓝[≠] 0)
      (𝓝 ‖S t z - (I * z) • deriv f z‖) :=
    ((tendsto_slope hf hz).const_sub (S t z)).norm
  have hlim' : Tendsto (fun s : ℝ ↦ C * |t| ^ (α : ℝ) + C * |s| ^ (α : ℝ)) (𝓝[≠] 0)
      (𝓝 (C * |t| ^ (α : ℝ))) := by
    simpa using tendsto_const_nhds.add hpow
  exact le_of_tendsto_of_tendsto hlim hlim' (eventually_nhdsWithin_of_forall hcomp)

/-- A function equal to `(I z) • f' z` on the open disc and to `v` on the circle is
differentiable on the open disc and continuous on the closed one: it is the uniform limit on the
closed disc of the difference quotients along the rotations. -/
private theorem diffContOnCl_of_eqOn [CompleteSpace E] (hf : DiffContOnCl ℂ f (ball 0 1))
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ f (exp (I * t) * w)) (v w) 0)
    (h : HolderOnWith C α v (sphere 0 1)) (hα0 : 0 < α) {g : ℂ → E}
    (hgb : ∀ z ∈ ball (0 : ℂ) 1, g z = (I * z) • deriv f z)
    (hgs : ∀ w ∈ sphere (0 : ℂ) 1, g w = v w) : DiffContOnCl ℂ g (ball 0 1) := by
  refine ⟨((differentiableOn_id.const_mul I).smul
    (hf.differentiableOn.deriv isOpen_ball)).congr hgb, ?_⟩
  rw [closure_ball (0 : ℂ) one_ne_zero]
  have hpow : Tendsto (fun s : ℝ ↦ (C : ℝ) * |s| ^ (α : ℝ)) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (((continuous_abs.tendsto' 0 0 abs_zero).rpow_const_nhds_zero
      (NNReal.coe_pos.mpr hα0)).const_mul (C : ℝ)).mono_left nhdsWithin_le_nhds
  have hunif : TendstoUniformlyOn (fun s : ℝ ↦ fun z ↦ (s : ℂ)⁻¹ • (f (exp (I * s) * z) - f z))
      g (𝓝[≠] 0) (closedBall 0 1) := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε ↦ ?_
    filter_upwards [hpow.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with s hs hs0
    intro z hz
    rw [dist_eq_norm, norm_sub_rev]
    refine lt_of_le_of_lt ?_ hs
    rcases (mem_closedBall_zero_iff.mp hz).lt_or_eq with hz1 | hz1
    · rw [hgb z (mem_ball_zero_iff.mpr hz1)]
      exact norm_slope_sub_smul_deriv_le hf hv h hpow hs0 (mem_ball_zero_iff.mpr hz1)
    · have hzs : z ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hz1
      rw [hgs z hzs]
      exact norm_slope_sub_le hv h hzs hs0
  refine hunif.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall fun s ↦ ?_))
  simpa [closure_ball (0 : ℂ) one_ne_zero] using (diffContOnCl_slope hf s).continuousOn

/-- **Privalov's theorem for the tangential derivative.** Let `f` be complex differentiable on the
open unit disc and continuous on the closed one, with values in a complex Banach space, and let
`0 < α < 1`. Suppose that at every point `w` of the unit circle the boundary values of `f` have the
derivative `v w` along the rotations, `t ↦ f (e^{it} w)` at `t = 0`, and that `v` is `α`-Hölder
on the circle with constant `C`. Then the tangential derivative `(I z) • f' z` extends from the
open disc to a function on the closed disc that equals `v` on the circle and is `α`-Hölder with
constant `C / cos (α π / 2)`. -/
theorem exists_holderOnWith_closedBall_smul_deriv [CompleteSpace E]
    (hf : DiffContOnCl ℂ f (ball 0 1))
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ f (exp (I * t) * w)) (v w) 0)
    (hα0 : 0 < α) (hα1 : α < 1) (h : HolderOnWith C α v (sphere 0 1)) :
    ∃ g : ℂ → E, HolderOnWith (C / (Real.cos (α * π / 2)).toNNReal) α g (closedBall 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, g z = (I * z) • deriv f z) ∧ ∀ w ∈ sphere (0 : ℂ) 1, g w = v w := by
  classical
  set g : ℂ → E := fun z ↦ if z ∈ ball (0 : ℂ) 1 then (I * z) • deriv f z else v z
  have hgb (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : g z = (I * z) • deriv f z := by
    simp only [g, hz, ↓reduceIte]
  have hgs (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 1) : g w = v w := by
    have hwb : w ∉ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hw]
      exact lt_irrefl _
    simp only [g, hwb, ↓reduceIte]
  refine ⟨g, holderOnWith_closedBall (diffContOnCl_of_eqOn hf hv h hα0 hgb hgs) hα1 ?_, hgb,
    hgs⟩
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  rw [hgs x hx, hgs y hy]
  exact h.dist_le hx hy

/-- On the closed disc of radius `3 / 4`, the derivative of a function holomorphic on the unit
disc is bounded and Lipschitz, with a common constant. -/
private theorem exists_norm_deriv_sub_le [CompleteSpace E] (hf : DiffContOnCl ℂ f (ball 0 1)) :
    ∃ M : ℝ, (∀ x ∈ closedBall (0 : ℂ) (3 / 4), ∀ y ∈ closedBall (0 : ℂ) (3 / 4),
      ‖deriv f x - deriv f y‖ ≤ M * ‖x - y‖) ∧
      ∀ x ∈ closedBall (0 : ℂ) (3 / 4), ‖deriv f x‖ ≤ M := by
  have hsub : closedBall (0 : ℂ) (3 / 4) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have hd := hf.differentiableOn.deriv isOpen_ball
  have hdd := hd.deriv isOpen_ball
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) (3 / 4)).exists_bound_of_continuousOn
    (hd.continuousOn.mono hsub)
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (0 : ℂ) (3 / 4)).exists_bound_of_continuousOn
    (hdd.continuousOn.mono hsub)
  refine ⟨max M₀ M₁, fun x hx y hy ↦ ?_, fun x hx ↦ (hM₀ x hx).trans (le_max_left _ _)⟩
  exact (convex_closedBall (0 : ℂ) (3 / 4)).norm_image_sub_le_of_norm_deriv_le
    (C := max M₀ M₁) (fun z hz ↦ hd.differentiableAt (isOpen_ball.mem_nhds (hsub hz)))
    (fun z hz ↦ (hM₁ z hz).trans (le_max_right _ _)) hy hx

/-- On the annulus `1 / 2 ≤ ‖z‖ ≤ 1`, dividing a bounded `α`-Hölder function by `I z` keeps it
`α`-Hölder between points at distance at most `1`. -/
private theorem norm_inv_smul_sub_inv_smul_le {g : ℂ → E} {K : ℝ≥0}
    (hg : HolderOnWith K α g (closedBall 0 1)) (hgbd : ∀ z ∈ closedBall (0 : ℂ) 1, ‖g z‖ ≤ K)
    (hα1 : α ≤ 1) {x y : ℂ} (hx : x ∈ closedBall (0 : ℂ) 1) (hy : y ∈ closedBall (0 : ℂ) 1)
    (hx2 : 1 / 2 ≤ ‖x‖) (hy2 : 1 / 2 ≤ ‖y‖) (hxy : ‖x - y‖ ≤ 1) :
    ‖(I * x)⁻¹ • g x - (I * y)⁻¹ • g y‖ ≤ 6 * K * ‖x - y‖ ^ (α : ℝ) := by
  have hx0 : I * x ≠ 0 := mul_ne_zero I_ne_zero (norm_pos_iff.mp (by linarith))
  have hy0 : I * y ≠ 0 := mul_ne_zero I_ne_zero (norm_pos_iff.mp (by linarith))
  have hnx : ‖(I * x)⁻¹‖ ≤ 2 := by
    rw [norm_inv, norm_mul, norm_I, one_mul]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hinv : ‖(I * x)⁻¹ - (I * y)⁻¹‖ ≤ 4 * ‖x - y‖ := by
    have hxy4 : 1 / 2 * (1 / 2) ≤ ‖x‖ * ‖y‖ := mul_le_mul hx2 hy2 (by norm_num) (norm_nonneg _)
    calc ‖(I * x)⁻¹ - (I * y)⁻¹‖ = ‖x - y‖ / (‖x‖ * ‖y‖) := by
          rw [inv_sub_inv hx0 hy0, ← mul_sub]
          simp [norm_sub_rev]
      _ ≤ ‖x - y‖ / (1 / 2 * (1 / 2)) := by gcongr
      _ = 4 * ‖x - y‖ := by ring
  have hd : ‖x - y‖ ≤ ‖x - y‖ ^ (α : ℝ) :=
    Real.self_le_rpow_of_le_one (norm_nonneg _) hxy (by exact_mod_cast hα1)
  have hgxy : ‖g x - g y‖ ≤ K * ‖x - y‖ ^ (α : ℝ) := by
    simpa [dist_eq_norm] using hg.dist_le hx hy
  calc ‖(I * x)⁻¹ • g x - (I * y)⁻¹ • g y‖
        = ‖(I * x)⁻¹ • (g x - g y) + ((I * x)⁻¹ - (I * y)⁻¹) • g y‖ := by
          rw [smul_sub, sub_smul]; abel_nf
    _ ≤ ‖(I * x)⁻¹‖ * ‖g x - g y‖ + ‖(I * x)⁻¹ - (I * y)⁻¹‖ * ‖g y‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
    _ ≤ 2 * (K * ‖x - y‖ ^ (α : ℝ)) + 4 * ‖x - y‖ ^ (α : ℝ) * K := by
          gcongr
          · exact hinv.trans (by gcongr)
          · exact hgbd y hy
    _ = 6 * K * ‖x - y‖ ^ (α : ℝ) := by ring

/-- **Gluing.** A function on the closed unit disc that is bounded and Lipschitz on the disc of
radius `3 / 4`, and equals `(I z)⁻¹ • g z` on the annulus `1 / 2 ≤ ‖z‖ ≤ 1` for a bounded
`α`-Hölder function `g`, is `α`-Hölder on the closed unit disc. -/
private theorem exists_holderOnWith_of_eq_inv_smul {F φ g : ℂ → E} {K : ℝ≥0} {M : ℝ}
    (hα1 : α ≤ 1) (hg : HolderOnWith K α g (closedBall 0 1))
    (hgbd : ∀ z ∈ closedBall (0 : ℂ) 1, ‖g z‖ ≤ K)
    (hlip : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), ∀ y ∈ closedBall (0 : ℂ) (3 / 4),
      ‖φ x - φ y‖ ≤ M * ‖x - y‖) (hbd : ∀ x ∈ closedBall (0 : ℂ) (3 / 4), ‖φ x‖ ≤ M)
    (hFφ : ∀ z : ℂ, ‖z‖ < 3 / 4 → F z = φ z)
    (hFg : ∀ z ∈ closedBall (0 : ℂ) 1, 1 / 2 ≤ ‖z‖ → F z = (I * z)⁻¹ • g z) :
    ∃ K' : ℝ≥0, HolderOnWith K' α F (closedBall 0 1) := by
  have hMr : M ≤ M.toNNReal := Real.le_coe_toNNReal M
  have hFbd (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : ‖F z‖ ≤ M.toNNReal + 2 * K := by
    by_cases hz2 : ‖z‖ < 1 / 2
    · rw [hFφ z (by linarith)]
      linarith [hbd z (mem_closedBall_zero_iff.mpr (by linarith)), K.coe_nonneg]
    · rw [hFg z hz (not_lt.mp hz2), norm_smul, norm_inv, norm_mul, norm_I, one_mul]
      have : ‖z‖⁻¹ ≤ 2 := inv_le_of_inv_le₀ (by norm_num) (by linarith)
      nlinarith [hgbd z hz, norm_nonneg (g z), inv_nonneg.mpr (norm_nonneg z),
        (M.toNNReal : ℝ≥0).coe_nonneg]
  refine ⟨_, HolderOnWith.of_dist_lt_of_dist_le (K := M.toNNReal + 6 * K)
    (D := 2 * (M.toNNReal + 2 * K)) (δ := 1 / 4) (by norm_num) (fun x hx y hy hxy ↦ ?_)
    (fun x hx y hy ↦ ?_)⟩
  · rw [dist_eq_norm, dist_eq_norm] at *
    push_cast at hxy ⊢
    have hpow : ‖x - y‖ ≤ ‖x - y‖ ^ (α : ℝ) := Real.self_le_rpow_of_le_one (norm_nonneg _)
      (by linarith) (by exact_mod_cast hα1)
    by_cases hxy2 : ‖x‖ < 1 / 2 ∨ ‖y‖ < 1 / 2
    · -- Both points lie in the disc of radius `3 / 4`.
      have hx' : ‖x‖ < 3 / 4 := by
        rcases hxy2 with h2 | h2
        · linarith
        · linarith [norm_le_norm_add_norm_sub' x y, norm_sub_rev x y]
      have hy' : ‖y‖ < 3 / 4 := by
        rcases hxy2 with h2 | h2
        · linarith [norm_le_norm_add_norm_sub' y x, norm_sub_rev x y]
        · linarith
      rw [hFφ x hx', hFφ y hy']
      calc ‖φ x - φ y‖ ≤ M * ‖x - y‖ :=
            hlip x (mem_closedBall_zero_iff.mpr hx'.le) y (mem_closedBall_zero_iff.mpr hy'.le)
        _ ≤ (M.toNNReal + 6 * K) * ‖x - y‖ ^ (α : ℝ) := by
            gcongr
            linarith [K.coe_nonneg]
    · -- Both points lie in the annulus.
      simp only [not_or, not_lt] at hxy2
      rw [hFg x hx hxy2.1, hFg y hy hxy2.2]
      refine (norm_inv_smul_sub_inv_smul_le hg hgbd hα1 hx hy hxy2.1 hxy2.2
        (by linarith)).trans ?_
      gcongr
      linarith [(M.toNNReal : ℝ≥0).coe_nonneg]
  · rw [dist_eq_norm]
    push_cast
    linarith [norm_sub_le (F x) (F y), hFbd x hx, hFbd y hy]

/-- **Privalov's theorem for the derivative.** Let `f` be complex differentiable on the open unit
disc and continuous on the closed one, with values in a complex Banach space, and let
`0 < α < 1`. Suppose that at every point `w` of the unit circle the boundary values of `f` have the
derivative `v w` along the rotations, `t ↦ f (e^{it} w)` at `t = 0`, and that `v` is `α`-Hölder
on the circle. Then the derivative `f'` of `f` extends from the open disc to an `α`-Hölder
function on the closed disc, whose boundary values satisfy `(I w) • f' w = v w`. -/
theorem exists_holderOnWith_closedBall_deriv [CompleteSpace E] (hf : DiffContOnCl ℂ f (ball 0 1))
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ f (exp (I * t) * w)) (v w) 0)
    (hα0 : 0 < α) (hα1 : α < 1) (h : HolderOnWith C α v (sphere 0 1)) :
    ∃ (f' : ℂ → E) (K : ℝ≥0), HolderOnWith K α f' (closedBall 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, f' z = deriv f z) ∧ ∀ w ∈ sphere (0 : ℂ) 1, (I * w) • f' w = v w := by
  obtain ⟨g, hg, hgb, hgs⟩ := exists_holderOnWith_closedBall_smul_deriv hf hv hα0 hα1 h
  set K₁ := C / (Real.cos (α * π / 2)).toNNReal
  -- `g` vanishes at `0`, so it is bounded by its Hölder constant.
  have hgbd (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : ‖g z‖ ≤ K₁ := by
    have := hg.dist_le hz (mem_closedBall_self zero_le_one)
    rw [hgb 0 (mem_ball_self one_pos), mul_zero, zero_smul, dist_zero_right,
      dist_zero_right] at this
    exact this.trans (mul_le_of_le_one_right K₁.coe_nonneg
      (Real.rpow_le_one (norm_nonneg _) (mem_closedBall_zero_iff.mp hz) α.coe_nonneg))
  obtain ⟨M, hMlip, hMbd⟩ := exists_norm_deriv_sub_le hf
  classical
  -- Extend `f'` to the circle by `(I w)⁻¹ • v w`.
  set f' : ℂ → E := fun z ↦ if z ∈ ball (0 : ℂ) 1 then deriv f z else (I * z)⁻¹ • v z
  have hf'b (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : f' z = deriv f z := by
    simp only [f', hz, ↓reduceIte]
  have hf'g (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) (hz2 : 1 / 2 ≤ ‖z‖) :
      f' z = (I * z)⁻¹ • g z := by
    have hIz : I * z ≠ 0 := mul_ne_zero I_ne_zero (norm_pos_iff.mp (by linarith))
    by_cases hzb : z ∈ ball (0 : ℂ) 1
    · rw [hf'b z hzb, hgb z hzb, inv_smul_smul₀ hIz]
    · have hzs : z ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact le_antisymm (mem_closedBall_zero_iff.mp hz) (not_lt.mp (by simpa using hzb))
      simp only [f', hzb, ↓reduceIte, hgs z hzs]
  obtain ⟨K, hK⟩ := exists_holderOnWith_of_eq_inv_smul hα1.le hg hgbd hMlip hMbd
    (fun z hz ↦ hf'b z (mem_ball_zero_iff.mpr (by linarith))) hf'g
  refine ⟨f', K, hK, hf'b, fun w hw ↦ ?_⟩
  have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
  rw [hf'g w (sphere_subset_closedBall hw) (by rw [hw1]; norm_num), ← hgs w hw,
    smul_inv_smul₀ (mul_ne_zero I_ne_zero (norm_pos_iff.mp (by rw [hw1]; norm_num)))]

end Deriv

end DiffContOnCl
