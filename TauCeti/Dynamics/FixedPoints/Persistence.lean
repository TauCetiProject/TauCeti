/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Basic.Sign.Defs
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Instances.Sign
import TauCeti.Analysis.Calculus.ApproximatesLinearOn
import TauCeti.Analysis.Normed.Operator.CompactFamily
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Persistence of nondegenerate fixed points under small `C¹` perturbations

Let `f` be a self-map of a real Banach space `E` with a fixed point `x` at which the derivative of
`f` is continuous and `1 - Df(x)` is invertible. Then `x` survives every sufficiently small `C¹`
perturbation: on each sufficiently small closed ball around `x` there is a threshold `δ > 0` such
that every map `g`, differentiable on the ball, with `‖g x - f x‖ ≤ δ` and whose derivative stays
within `δ` of that of `f` on the ball, has exactly one fixed point `y` in the ball. At `y` the
operator `1 - Dg(y)` is again invertible, and `y` lies within a constant times `‖g x - f x‖` of
`x` (`Function.IsFixedPt.exists_isFixedPt_perturbation`). In finite dimensions `y` is a
nondegenerate fixed point in the sense of `TauCeti.IsNondegenerateFixedPt`, and the sign of
`det (1 - Dg(y))`, the local contribution of `y` to the Lefschetz fixed-point formula, is that of
`det (1 - Df(x))` (`TauCeti.IsNondegenerateFixedPt.exists_isNondegenerateFixedPt_perturbation`).

The perturbation is an arbitrary map, not a member of a parametrized family as in
`TauCeti.IsNondegenerateFixedPt.exists_contMDiffAt_fixedPt_continuation`, and the size of the
admissible perturbation is uniform on the ball. The fixed points of `g` are the zeros of
`y ↦ y - g y`, whose derivative `1 - Dg` approximates the invertible operator `1 - Df(x)` on a
small ball. Its unique zero there comes from the quantitative inverse function theorem
`ApproximatesLinearOn.exists_eq_zero_of_two_mul_norm_le`.

On a compact set `K` the local statements combine.

* If every fixed point of `f` in `K` has `1 - Df` invertible, the same holds for every map that
  is `C⁰`- and `C¹`-close to `f` on `K`
  (`IsCompact.exists_pos_forall_isInvertible_id_sub_fderiv`), and in finite dimensions
  nondegeneracy of all fixed points in `K` is preserved
  (`IsCompact.exists_pos_forall_isNondegenerateFixedPt`). At a point of `K`, either `f` moves it
  by a definite amount, and then so does `g`, or `1 - Df` is far from the closed set of
  non-invertible operators, and then `1 - Dg` is invertible; compactness makes the alternatives
  uniform.
* In finite dimensions, if `f` is continuous on `K`, with derivative continuous at its fixed points
  in `K`, which are nondegenerate and lie in the interior of `K`, then the fixed points in `K` of a
  map `g` that is `C¹`-close to `f` on `K` correspond bijectively to those of `f`, each within a
  prescribed distance of its partner and with the same sign of `det (1 - D)`
  (`IsCompact.exists_pos_forall_exists_bijOn_fixedPoints_inter`). So the number of fixed points
  in `K` and their signed count `∑ sign det (1 - D)` do not change
  (`IsCompact.exists_pos_forall_ncard_fixedPoints_inter_eq`,
  `IsCompact.exists_pos_forall_finsum_sign_det_eq`).

These are the openness statements behind the genericity of nondegenerate fixed points: the maps
whose fixed points in `K` are all nondegenerate form a `C¹`-open set. Once a localized
perturbation, such as the Hamiltonian translations of
`TauCeti.SymplecticForm.exists_hamiltonianFlow_isNondegenerateFixedPt_iterate`, has made the fixed
points of a surface map in a chart nondegenerate, every further perturbation that is small in `C¹`
on that chart keeps them nondegenerate, with the same number and the same signs.

## References

* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3 (openness of transversality).
* R. C. Robinson, *Generic properties of conservative systems*, Amer. J. Math. 92 (1970),
  562–603, for the genericity of nondegenerate periodic points of conservative maps.
* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 3, §4
  (local Lefschetz numbers). That reference uses the sign of `det (df_x - I)`; this file uses the
  sign of `det (1 - Df)`, which differs from it by `(-1) ^ dim E`.
-/

public section

open Filter Function Metric Set
open scoped Manifold NNReal Topology

namespace Function.IsFixedPt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {x : E}

/-- If `1 - Dg` stays within `κ` of an invertible operator `L` on a closed ball, with
`2 ‖L⁻¹‖ κ ≤ 1`, and `g` moves the centre `x` little enough, then `g` has a unique fixed point in
the ball, within `2 C ‖x - g x‖` of `x`, for any bound `C` on `‖L⁻¹‖`. -/
private theorem exists_isFixedPt_of_norm_id_sub_fderiv_sub_le [CompleteSpace E] {g : E → E}
    {L : E ≃L[ℝ] E} {C κ r : ℝ} (hκ : 0 ≤ κ) (hLsymm : ‖(L.symm : E →L[ℝ] E)‖ ≤ C)
    (hκC : 2 * C * κ ≤ 1) (hg : ∀ y ∈ closedBall x r, DifferentiableAt ℝ g y)
    (hclose : ∀ y ∈ closedBall x r, ‖(ContinuousLinearMap.id ℝ E - fderiv ℝ g y) - L‖ ≤ κ)
    (hr : 2 * C * ‖x - g x‖ ≤ r) :
    ∃ y ∈ closedBall x (2 * C * ‖x - g x‖), IsFixedPt g y ∧
      ∀ z ∈ closedBall x r, IsFixedPt g z → z = y := by
  -- The fixed points of `g` are the zeros of the displacement `y ↦ y - g y`, whose derivative
  -- `1 - Dg` approximates `L` on the ball.
  have happrox : ApproximatesLinearOn (fun z ↦ z - g z) (L : E →L[ℝ] E) (closedBall x r)
      ⟨κ, hκ⟩ :=
    (convex_closedBall x r).approximatesLinearOn_of_nnnorm_fderiv_sub_le
      (fun y hy ↦ differentiableAt_id.sub (hg y hy)) fun y hy ↦ by
        rw [fderiv_fun_sub differentiableAt_fun_id (hg y hy), fderiv_fun_id]
        exact_mod_cast hclose y hy
  obtain ⟨y, hy, hy0, huniq⟩ := happrox.exists_eq_zero_of_two_mul_norm_le hLsymm hκC hr
  exact ⟨y, hy, (sub_eq_zero.1 hy0).symm, fun z hz hgz ↦ huniq z hz (sub_eq_zero.2 hgz.symm)⟩

/-- **Persistence of a fixed point under small `C¹` perturbations.**

Let `x` be a fixed point of `f`, a map of a Banach space whose derivative is continuous at `x`,
such that `1 - Df(x)` is invertible. For every sufficiently small radius `r` there is `δ > 0` with
the following property. If `g` is differentiable at every point of the closed ball of radius `r`
around `x`, its derivative stays within `δ` of that of `f` on the ball, and `‖g x - f x‖ ≤ δ`,
then `g` has a fixed point `y` in the ball, and it is the only one there. At `y` the operator
`1 - Dg(y)` is invertible, and `y` lies within `K * ‖g x - f x‖` of `x`, for a constant `K`
depending only on `f` and `x`. -/
theorem exists_isFixedPt_perturbation [CompleteSpace E] (hx : IsFixedPt f x)
    (hf : ContinuousAt (fderiv ℝ f) x)
    (hinv : (ContinuousLinearMap.id ℝ E - fderiv ℝ f x).IsInvertible) :
    ∃ K : ℝ, ∀ᶠ r in 𝓝[>] 0, ∃ δ > 0, ∀ g : E → E,
      (∀ y ∈ closedBall x r, DifferentiableAt ℝ g y) →
      (∀ y ∈ closedBall x r, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      ‖g x - f x‖ ≤ δ →
      ∃ y ∈ closedBall x r, IsFixedPt g y ∧
        (ContinuousLinearMap.id ℝ E - fderiv ℝ g y).IsInvertible ∧
        dist y x ≤ K * ‖g x - f x‖ ∧ ∀ z ∈ closedBall x r, IsFixedPt g z → z = y := by
  -- On a small ball `1 - Dg` stays close to the invertible operator `L = 1 - Df(x)`.
  obtain ⟨L, hL⟩ := hinv
  -- `C` bounds the inverse of `L` and is positive even on the zero space.
  set C : ℝ := ‖(L.symm : E →L[ℝ] E)‖ + 1
  have hLsymm : ‖(L.symm : E →L[ℝ] E)‖ ≤ C := le_add_of_nonneg_right zero_le_one
  obtain ⟨ε₀, hε₀, hinv'⟩ :=
    Metric.eventually_nhds_iff.1 (ContinuousLinearMap.IsInvertible.eventually_nhds ⟨L, hL⟩)
  -- `κ` is the admissible distance from `L` on the ball.
  set κ : ℝ := min (2 * C)⁻¹ (ε₀ / 2)
  have hκ : 0 < κ := by positivity
  have hκC : 2 * C * κ ≤ 1 :=
    calc 2 * C * κ ≤ 2 * C * (2 * C)⁻¹ := by gcongr; exact min_le_left _ _
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hκε₀ : κ < ε₀ := (min_le_right _ _).trans_lt (half_lt_self hε₀)
  obtain ⟨ρ, hρ, hρf⟩ := Metric.eventually_nhds_iff.1
    (hf.eventually (Metric.ball_mem_nhds _ (half_pos hκ)))
  refine ⟨2 * C, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
  refine ⟨min (κ / 2) (r / (2 * C)), by have := hr.1; positivity, fun g hg hgf hgx ↦ ?_⟩
  -- On the ball, `1 - Dg` is within `κ` of `L`.
  have hclose (y : E) (hy : y ∈ closedBall x r) :
      ‖(ContinuousLinearMap.id ℝ E - fderiv ℝ g y) - L‖ ≤ κ :=
    calc ‖(ContinuousLinearMap.id ℝ E - fderiv ℝ g y) - L‖
        = ‖(fderiv ℝ f y - fderiv ℝ g y) + (fderiv ℝ f x - fderiv ℝ f y)‖ := by
          rw [hL]; congr 1; abel
      _ ≤ ‖fderiv ℝ f y - fderiv ℝ g y‖ + ‖fderiv ℝ f x - fderiv ℝ f y‖ := norm_add_le _ _
      _ = ‖fderiv ℝ g y - fderiv ℝ f y‖ + ‖fderiv ℝ f y - fderiv ℝ f x‖ := by
          rw [norm_sub_rev (fderiv ℝ f y), norm_sub_rev (fderiv ℝ f x)]
      _ ≤ κ / 2 + κ / 2 := by
          gcongr
          · exact (hgf y hy).trans (min_le_left _ _)
          · have := hρf (lt_of_le_of_lt (mem_closedBall.1 hy) hr.2)
            rw [dist_eq_norm] at this
            exact this.le
      _ = κ := add_halves κ
  have hn : ‖x - g x‖ = ‖g x - f x‖ := by rw [norm_sub_rev, hx.eq]
  have hεr : 2 * C * ‖x - g x‖ ≤ r := by
    have : ‖g x - f x‖ ≤ r / (2 * C) := hgx.trans (min_le_right _ _)
    rw [hn]
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  obtain ⟨y, hyε, hgy, huniq⟩ :=
    exists_isFixedPt_of_norm_id_sub_fderiv_sub_le hκ.le hLsymm hκC hg hclose hεr
  have hsub : closedBall x (2 * C * ‖x - g x‖) ⊆ closedBall x r := closedBall_subset_closedBall hεr
  refine ⟨y, hsub hyε, hgy, hinv' ?_, ?_, huniq⟩
  · rw [dist_eq_norm, ← hL]
    exact (hclose y (hsub hyε)).trans_lt hκε₀
  · rw [← hn]
    exact mem_closedBall.1 hyε

end Function.IsFixedPt

namespace TauCeti.IsNondegenerateFixedPt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → E} {x : E}

/-- **Persistence of a nondegenerate fixed point under small `C¹` perturbations.**

Let `x` be a nondegenerate fixed point of a map `f` of a finite-dimensional real normed space,
with derivative continuous at `x`. For every sufficiently small radius `r` there is `δ > 0` with
the following property.
If `g` is differentiable at every point of the closed ball of radius `r` around `x`, its derivative
stays within `δ` of that of `f` on the ball, and `‖g x - f x‖ ≤ δ`, then `g` has a fixed point `y`
in the ball, and it is the only one there. It is nondegenerate, the sign of `det (1 - Dg(y))` is
that of `det (1 - Df(x))`, and `y` lies within `K * ‖g x - f x‖` of `x`, for a constant `K`
depending only on `f` and `x`. -/
theorem exists_isNondegenerateFixedPt_perturbation (h : IsNondegenerateFixedPt 𝓘(ℝ, E) f x)
    (hf : ContinuousAt (fderiv ℝ f) x) :
    ∃ K : ℝ, ∀ᶠ r in 𝓝[>] 0, ∃ δ > 0, ∀ g : E → E,
      (∀ y ∈ closedBall x r, DifferentiableAt ℝ g y) →
      (∀ y ∈ closedBall x r, ‖fderiv ℝ g y - fderiv ℝ f y‖ ≤ δ) →
      ‖g x - f x‖ ≤ δ →
      ∃ y ∈ closedBall x r, IsNondegenerateFixedPt 𝓘(ℝ, E) g y ∧
        SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ g y : E →ₗ[ℝ] E))) =
          SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ f x : E →ₗ[ℝ] E))) ∧
        dist y x ≤ K * ‖g x - f x‖ ∧ ∀ z ∈ closedBall x r, IsFixedPt g z → z = y := by
  have hinv := h.isInvertible_id_sub_fderiv
  have hdet : LinearMap.det (LinearMap.id - (fderiv ℝ f x : E →ₗ[ℝ] E)) ≠ 0 := by
    have := (isNondegenerateFixedPt_iff_det_id_sub_ne_zero ⟨x, h.isFixedPt⟩ h.mdifferentiableAt).1 h
    rwa [det_id_sub_fixedPointDerivative_modelSpace] at this
  obtain ⟨K, hK⟩ := h.isFixedPt.exists_isFixedPt_perturbation hf hinv
  -- `ε` is a distance from `Df(x)` within which the sign of `det (1 - T)` is unchanged.
  have hcont : Continuous fun T : E →L[ℝ] E ↦ LinearMap.det (LinearMap.id - (T : E →ₗ[ℝ] E)) := by
    refine (ContinuousLinearMap.continuous_det.comp
      ((continuous_const (y := ContinuousLinearMap.id ℝ E)).sub continuous_id)).congr fun T ↦ ?_
    simp [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_sub]
  have hsgn : ContinuousAt (fun T : E →L[ℝ] E ↦
      SignType.sign (LinearMap.det (LinearMap.id - (T : E →ₗ[ℝ] E)))) (fderiv ℝ f x) :=
    (continuousAt_sign_of_ne_zero hdet).comp
      (f := fun T : E →L[ℝ] E ↦ LinearMap.det (LinearMap.id - (T : E →ₗ[ℝ] E))) hcont.continuousAt
  obtain ⟨ε, hε, hsign⟩ := Metric.eventually_nhds_iff.1
    (hsgn.eventually_mem ((isOpen_discrete ({_} : Set SignType)).mem_nhds (mem_singleton _)))
  obtain ⟨ρ, hρ, hρf⟩ := Metric.eventually_nhds_iff.1
    (hf.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  refine ⟨K, ?_⟩
  filter_upwards [hK, Ioo_mem_nhdsGT hρ] with r ⟨δ, hδ, hr⟩ hrρ
  refine ⟨min δ (ε / 2), by positivity, fun g hg hgf hgx ↦ ?_⟩
  obtain ⟨y, hy, hgy, hinvy, hdist, huniq⟩ := hr g hg
    (fun y hy ↦ (hgf y hy).trans (min_le_left _ _)) (hgx.trans (min_le_left _ _))
  refine ⟨y, hy,
    (HasFDerivAt.isNondegenerateFixedPt_iff_isInvertible_id_sub (hg y hy).hasFDerivAt hgy).2 hinvy,
    mem_singleton_iff.1 (hsign ?_), hdist, huniq⟩
  -- `Dg(y)` is within `ε / 2` of `Df(y)`, which is within `ε / 2` of `Df(x)`.
  calc dist (fderiv ℝ g y) (fderiv ℝ f x)
      ≤ dist (fderiv ℝ g y) (fderiv ℝ f y) + dist (fderiv ℝ f y) (fderiv ℝ f x) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [dist_eq_norm]
        exact add_lt_add_of_le_of_lt ((hgf y hy).trans (min_le_right _ _))
          (hρf (lt_of_le_of_lt (mem_closedBall.1 hy) hrρ.2))
    _ = ε := add_halves ε

end TauCeti.IsNondegenerateFixedPt

namespace IsCompact

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → E} {K : Set E}

/-- **Invertibility at the fixed points in a compact set persists under small `C¹`
perturbations.**

Let `f` be a self-map of a Banach space, continuous on a compact set `K` with derivative continuous
on `K`, such that `1 - Df(x)` is invertible at every fixed point `x` of `f` in `K`. Then there is
`δ > 0` such that every map `g` within `δ` of `f` on `K`, whose derivative is within `δ` of that of
`f` on `K`, again has `1 - Dg(x)` invertible at every fixed point `x` in `K`. -/
theorem exists_pos_forall_isInvertible_id_sub_fderiv [CompleteSpace E] (hK : IsCompact K)
    (hf₀ : ContinuousOn f K) (hf₁ : ContinuousOn (fderiv ℝ f) K)
    (hf : ∀ x ∈ K, IsFixedPt f x → (ContinuousLinearMap.id ℝ E - fderiv ℝ f x).IsInvertible) :
    ∃ δ > 0, ∀ g : E → E, (∀ x ∈ K, ‖g x - f x‖ ≤ δ) →
      (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ δ) →
      ∀ x ∈ K, IsFixedPt g x → (ContinuousLinearMap.id ℝ E - fderiv ℝ g x).IsInvertible := by
  -- Apply the compactness lemma to the displacement `x - f x` and the operators `1 - Df(x)`.
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_isInvertible_of_norm_le (d := fun x ↦ x - f x)
    (A := fun x ↦ ContinuousLinearMap.id ℝ E - fderiv ℝ f x) (continuousOn_id.sub hf₀)
    (continuousOn_const.sub hf₁) fun x hx hx₀ ↦ hf x hx (sub_eq_zero.1 hx₀).symm
  refine ⟨δ, hδ, fun g hg₀ hg₁ x hx hgx ↦ h x hx _ (by simpa [hgx.eq] using hg₀ x hx) ?_⟩
  rw [sub_sub_sub_cancel_left, norm_sub_rev]
  exact hg₁ x hx

/-- **Nondegeneracy of the fixed points in a compact set persists under small `C¹`
perturbations.**

Let `f` be a self-map of a finite-dimensional real normed space, continuous on a compact set `K`
with derivative continuous on `K`, all of whose fixed points in `K` are nondegenerate. Then there is
`δ > 0` such that every map `g` differentiable on `K`, within `δ` of `f` on `K` and whose
derivative is within `δ` of that of `f` on `K`, again has only nondegenerate fixed points in `K`. -/
theorem exists_pos_forall_isNondegenerateFixedPt [FiniteDimensional ℝ E] (hK : IsCompact K)
    (hf₀ : ContinuousOn f K) (hf₁ : ContinuousOn (fderiv ℝ f) K)
    (hf : ∀ x ∈ K, IsFixedPt f x → IsNondegenerateFixedPt 𝓘(ℝ, E) f x) :
    ∃ δ > 0, ∀ g : E → E, (∀ x ∈ K, DifferentiableAt ℝ g x) → (∀ x ∈ K, ‖g x - f x‖ ≤ δ) →
      (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ δ) →
      ∀ x ∈ K, IsFixedPt g x → IsNondegenerateFixedPt 𝓘(ℝ, E) g x := by
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_isInvertible_id_sub_fderiv hf₀ hf₁ fun x hx hfx ↦
    (hf x hx hfx).isInvertible_id_sub_fderiv
  exact ⟨δ, hδ, fun g hg hg₀ hg₁ x hx hgx ↦
    (HasFDerivAt.isNondegenerateFixedPt_iff_isInvertible_id_sub (hg x hx).hasFDerivAt hgx).2
      (h g hg₀ hg₁ x hx hgx)⟩

omit [NormedSpace ℝ E] in
/-- Away from the open balls of radius `r` around its fixed points in a compact set `K`, a map
continuous on `K` moves the points of `K` by at least a positive amount. -/
private theorem exists_pos_forall_le_norm_sub (hK : IsCompact K) (hf₀ : ContinuousOn f K)
    {r : ℝ} (hr : 0 < r) :
    ∃ m > 0, ∀ y ∈ K, (∀ x ∈ fixedPoints f ∩ K, y ∉ ball x r) → m ≤ ‖y - f y‖ := by
  set K' := K ∩ ⋂ x ∈ fixedPoints f ∩ K, (ball x r)ᶜ
  have hK' : IsCompact K' := hK.inter_right (isClosed_biInter fun x _ ↦ isOpen_ball.isClosed_compl)
  -- `‖y - f y‖` is positive on `K'`, since a fixed point of `f` in `K` lies in its own ball.
  obtain ⟨m, hm, hmK'⟩ := hK'.exists_forall_le'
    ((continuousOn_id.sub hf₀).norm.mono inter_subset_left) fun y hy ↦ norm_pos_iff.2 fun h ↦
      mem_iInter₂.1 hy.2 y ⟨(sub_eq_zero.1 h).symm, hy.1⟩ (mem_ball_self hr)
  exact ⟨m, hm, fun y hy hball ↦ hmK' y ⟨hy, mem_iInter₂.2 hball⟩⟩

/-- **The fixed points in a compact set persist under small `C¹` perturbations, with their
signs.**

Let `f` be a self-map of a finite-dimensional real normed space, continuous on a compact set `K`
with derivative continuous at its fixed points in `K`, which are all nondegenerate and lie in the
interior of `K`.
For every `ε > 0` there is `δ > 0` with the following property. If `g` is differentiable on `K`,
within `δ` of `f` on `K`, and its derivative is within `δ` of that of `f` on `K`, then some map `φ`
is a bijection from the fixed points of `f` in `K` to those of `g` in `K`. It moves each point by at
most `ε`, its values are nondegenerate fixed points of `g`, and it preserves the sign of
`det (1 - D)`. -/
theorem exists_pos_forall_exists_bijOn_fixedPoints_inter [FiniteDimensional ℝ E]
    (hK : IsCompact K) (hf₀ : ContinuousOn f K)
    (hf : ∀ x ∈ K, IsFixedPt f x → ContinuousAt (fderiv ℝ f) x)
    (hnd : ∀ x ∈ K, IsFixedPt f x → IsNondegenerateFixedPt 𝓘(ℝ, E) f x)
    (hint : ∀ x ∈ K, IsFixedPt f x → x ∈ interior K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : E → E, (∀ x ∈ K, DifferentiableAt ℝ g x) →
      (∀ x ∈ K, ‖g x - f x‖ ≤ δ) → (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ δ) →
      ∃ φ : E → E, BijOn φ (fixedPoints f ∩ K) (fixedPoints g ∩ K) ∧
        ∀ x ∈ fixedPoints f ∩ K, dist (φ x) x ≤ ε ∧ IsNondegenerateFixedPt 𝓘(ℝ, E) g (φ x) ∧
          SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ g (φ x) : E →ₗ[ℝ] E))) =
            SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ f x : E →ₗ[ℝ] E))) := by
  set F := fixedPoints f ∩ K
  -- The fixed points of `f` in `K` form a compact set of nondegenerate fixed points, so finitely
  -- many.
  have hFc : IsCompact F := by
    have hFeq : F = {y ∈ K | f y = y} := Set.ext fun _ ↦ and_comm
    rw [hFeq]
    exact hK.of_isClosed_subset (hK.isClosed.isClosed_eq hf₀ continuousOn_id) fun y hy ↦ hy.1
  have hFfin : F.Finite := hFc.finite_of_isNondegenerateFixedPt fun x hx ↦ hnd x hx.2 hx.1
  -- The local persistence theorem at each point of `F`, for a common radius `r` and thresholds
  -- `δx x`, and a common threshold `δ < m` below them.
  choose! C hC using fun x (hx : x ∈ F) ↦
    (hnd x hx.2 hx.1).exists_isNondegenerateFixedPt_perturbation (hf x hx.2 hx.1)
  obtain ⟨r, hr0, hr, hrε, hrK, hsep⟩ := (eventually_mem_nhdsWithin.and <|
    ((eventually_all_finite hFfin).2 hC).and <| nhdsWithin_le_nhds <| (eventually_le_nhds hε).and <|
    eventually_closedBall_subset_and_lt_dist hFfin fun x hx ↦
      mem_interior_iff_mem_nhds.1 (hint x hx.2 hx.1)).exists
  obtain ⟨m, hm, hmK⟩ := hK.exists_pos_forall_le_norm_sub hf₀ hr0
  choose! δx hδx hQ using hr
  obtain ⟨δ, hδ, hδm, hδF⟩ := (eventually_mem_nhdsWithin.and <| nhdsWithin_le_nhds <|
    (eventually_lt_nhds hm).and <| (eventually_all_finite hFfin).2 fun x hx ↦
      eventually_le_nhds (hδx x hx)).exists (f := 𝓝[>] 0)
  refine ⟨δ, hδ, fun g hg hg₀ hg₁ ↦ ?_⟩
  -- At each point `x` of `F`, the unique fixed point of `g` in the ball of radius `r`.
  have hloc (x : E) (hx : x ∈ F) := hQ x hx g (fun y hy ↦ hg y (hrK x hx hy))
    (fun y hy ↦ (hg₁ y (hrK x hx hy)).trans (hδF x hx))
    ((hg₀ x hx.2).trans (hδF x hx))
  choose! φ hφr hφnd hφsign _ hφuniq using hloc
  refine ⟨φ, ⟨fun x hx ↦ ⟨(hφnd x hx).isFixedPt, hrK x hx (hφr x hx)⟩, ?_, ?_⟩,
    fun x hx ↦ ⟨(mem_closedBall.1 (hφr x hx)).trans hrε, hφnd x hx, hφsign x hx⟩⟩
  · -- Distinct points of `F` have disjoint balls.
    intro x₁ hx₁ x₂ hx₂ h
    by_contra hne
    have := hsep x₁ hx₁ x₂ hx₂ hne
    have h₁ := mem_closedBall.1 (hφr x₁ hx₁)
    have h₂ := mem_closedBall.1 (hφr x₂ hx₂)
    rw [h] at h₁
    linarith [dist_triangle_left x₁ x₂ (φ x₂)]
  · -- A fixed point of `g` in `K` outside every ball would be moved by `f` by at least `m`.
    intro y ⟨hgy, hyK⟩
    by_cases hball : ∃ x ∈ F, y ∈ ball x r
    · obtain ⟨x, hx, hyx⟩ := hball
      exact ⟨x, hx, (hφuniq x hx y (ball_subset_closedBall hyx) hgy).symm⟩
    · have h₁ := hmK y hyK fun x hx hyx ↦ hball ⟨x, hx, hyx⟩
      have h₂ := hg₀ y hyK
      rw [mem_fixedPoints.1 hgy] at h₂
      linarith

/-- **The number of fixed points in a compact set is stable under small `C¹` perturbations.**

Under the hypotheses of `IsCompact.exists_pos_forall_exists_bijOn_fixedPoints_inter`, every map
`g` that is `C¹`-close to `f` on `K` has as many fixed points in `K` as `f`. -/
theorem exists_pos_forall_ncard_fixedPoints_inter_eq [FiniteDimensional ℝ E]
    (hK : IsCompact K) (hf₀ : ContinuousOn f K)
    (hf : ∀ x ∈ K, IsFixedPt f x → ContinuousAt (fderiv ℝ f) x)
    (hnd : ∀ x ∈ K, IsFixedPt f x → IsNondegenerateFixedPt 𝓘(ℝ, E) f x)
    (hint : ∀ x ∈ K, IsFixedPt f x → x ∈ interior K) :
    ∃ δ > 0, ∀ g : E → E, (∀ x ∈ K, DifferentiableAt ℝ g x) →
      (∀ x ∈ K, ‖g x - f x‖ ≤ δ) → (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ δ) →
      (fixedPoints g ∩ K).ncard = (fixedPoints f ∩ K).ncard := by
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_exists_bijOn_fixedPoints_inter hf₀ hf hnd hint one_pos
  refine ⟨δ, hδ, fun g hg hg₀ hg₁ ↦ ?_⟩
  obtain ⟨φ, hφ, -⟩ := h g hg hg₀ hg₁
  exact hφ.ncard_eq.symm

/-- **The signed count of the fixed points in a compact set is stable under small `C¹`
perturbations.**

Under the hypotheses of `IsCompact.exists_pos_forall_exists_bijOn_fixedPoints_inter`, every map
`g` that is `C¹`-close to `f` on `K` has the same sum of the local Lefschetz signs
`sign det (1 - Dg(y))` over its fixed points `y` in `K` as `f`. -/
theorem exists_pos_forall_finsum_sign_det_eq [FiniteDimensional ℝ E]
    (hK : IsCompact K) (hf₀ : ContinuousOn f K)
    (hf : ∀ x ∈ K, IsFixedPt f x → ContinuousAt (fderiv ℝ f) x)
    (hnd : ∀ x ∈ K, IsFixedPt f x → IsNondegenerateFixedPt 𝓘(ℝ, E) f x)
    (hint : ∀ x ∈ K, IsFixedPt f x → x ∈ interior K) :
    ∃ δ > 0, ∀ g : E → E, (∀ x ∈ K, DifferentiableAt ℝ g x) →
      (∀ x ∈ K, ‖g x - f x‖ ≤ δ) → (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ δ) →
      ∑ᶠ y ∈ fixedPoints g ∩ K,
          (SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ g y : E →ₗ[ℝ] E))) : ℤ) =
        ∑ᶠ x ∈ fixedPoints f ∩ K,
          (SignType.sign (LinearMap.det (LinearMap.id - (fderiv ℝ f x : E →ₗ[ℝ] E))) : ℤ) := by
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_exists_bijOn_fixedPoints_inter hf₀ hf hnd hint one_pos
  refine ⟨δ, hδ, fun g hg hg₀ hg₁ ↦ ?_⟩
  obtain ⟨φ, hφ, hφx⟩ := h g hg hg₀ hg₁
  exact (finsum_mem_eq_of_bijOn φ hφ fun x hx ↦ by rw [(hφx x hx).2.2]).symm

end IsCompact
