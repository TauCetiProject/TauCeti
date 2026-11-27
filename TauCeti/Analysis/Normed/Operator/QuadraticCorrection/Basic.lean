/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Solving a nonlinear equation with a bounded right inverse and a quadratic remainder

Let `D : E → F` have a right inverse `Q`, an additive map with `‖Q y‖ ≤ C ‖y‖`, and consider the
equation

`e + D x + N x = 0`

for an unknown `x : E`, where `e : F` is a small residual and the nonlinear remainder `N`
vanishes at `0` and is quadratic on the ball of radius `δ`:

`‖N x - N y‖ ≤ (L / 2) (‖x‖ + ‖y‖) ‖x - y‖`  for `‖x‖, ‖y‖ ≤ δ`.

This is the form taken by an elliptic equation `S(x) = 0` expanded around an approximate solution,
`S(x) = S(0) + dS(0) x + N x`, once a right inverse `Q` of the linearization `D = dS(0)` with an
operator-norm bound `C` has been constructed. The quadratic estimate holds, for instance, for a
remainder `N x = B x x` built from a bounded bilinear map `B` with `‖B‖ ≤ L / 2`
(`ContinuousLinearMap.norm_apply_apply_sub_apply_apply_le`), such as the quadratic terms of the
Seiberg–Witten and vortex equations. This file gives the quantitative fixed-point argument used in
gluing constructions, with explicit radii.

* The solutions in the range of `Q` are the fixed points of `x ↦ -Q (e + N x)`
  (`TauCeti.mem_range_and_add_add_eq_zero_iff`).
* **A priori estimate.** A solution `x` in the range of `Q` satisfies a weighted comparison
  estimate with every other point `y` of the range:
  `(1 - C L (‖x‖ + ‖y‖) / 2) ‖x - y‖ ≤ C ‖e + D y + N y‖`
  (`TauCeti.one_sub_mul_norm_sub_le_mul_norm_add_add`). The analogous weighted estimate compares
  solutions for two residuals `e` and `e'` (`TauCeti.one_sub_mul_norm_sub_le_mul_norm_sub`). The
  weight only controls the distance when it is positive: if `x` and `y` lie in a common ball of
  radius `r ≤ δ` with `C L r < 1`, then `‖x - y‖ ≤ C / (1 - C L r)` times the residual of `y`, resp.
  `‖e - e'‖`, so on such a ball solutions depend Lipschitz-continuously on the residual. More
  generally, a solution is compared with an arbitrary point `y` through its defect
  `y + Q (e + N y)` as a fixed point of `z ↦ -Q (e + N z)`
  (`TauCeti.one_sub_mul_norm_sub_le_norm_add_apply`), and
  solutions of two different equations through the difference of the maps `z ↦ Q (e + N z)` and
  `z ↦ Q' (e' + N' z)` (`TauCeti.one_sub_mul_norm_sub_le_norm_apply_sub_apply`).
  On a common ball of radius `r ≤ δ` with `C L r ≤ 1 / 2` the weight is at least `1 / 2`, so a
  point `y` of the range lies within `2 C ‖e + D y + N y‖` of the solution
  (`TauCeti.norm_sub_le_two_mul_mul_norm_add_add`), and solutions of two equations lie within
  `2 ‖Q (e + N y) - Q' (e' + N' y)‖` of each other
  (`TauCeti.norm_sub_le_two_mul_norm_apply_sub_apply`). These are the fast stability and graph
  Lipschitz constants of a fast–slow recovery estimate
  (`TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Recovery`).
* **Uniqueness.** Two solutions in the range of `Q` of norm at most `r ≤ δ` coincide as soon as
  `C L r < 1` (`TauCeti.eq_of_add_add_eq_zero`). The radius `r` may be much larger than the
  radius `2 C ‖e‖` where the solution is constructed.
* **Existence.** On the closed ball of radius `R ≤ δ`, the map `z ↦ Q (e + N z)` is Lipschitz with
  constant `C L R` (`TauCeti.lipschitzOnWith_apply_add_apply`). If `E` is complete,
  `2 C ‖e‖ ≤ δ` and `2 C² L ‖e‖ < 1`, it follows that the map
  `x ↦ -Q (e + N x)` contracts the closed ball of radius `2 C ‖e‖`, and its fixed point is a
  solution `x` in the range of `Q` with `‖x‖ ≤ 2 C ‖e‖`
  (`TauCeti.exists_mem_range_norm_le_add_add_eq_zero`).
* **Dependence on a parameter.** For a family of equations `e p + D p x + N p x = 0` with
  constants `C` and `L` uniform in `p`, and targets `F p` that may depend on `p`, solutions `x p`
  in the range of `Q p` of norm at most `r ≤ δ`, with `C L r < 1`, depend continuously on `p` as
  soon as each map `p ↦ Q p (e p + N p z)` with `‖z‖ ≤ r` does
  (`TauCeti.continuousAt_of_eventually_add_add_eq_zero`, which only needs the hypotheses near the
  base point, and `TauCeti.continuous_of_forall_add_add_eq_zero`). In particular, when moreover
  `E` is complete, `N p 0 = 0` and `2 C ‖e p‖ ≤ r` for all `p`, the solutions constructed above
  form a continuous family (`TauCeti.exists_continuous_forall_add_add_eq_zero`). Smooth
  dependence is in `TauCeti.Analysis.Calculus.QuadraticCorrection`.
* **Forcing.** On a common ball of radius `r ≤ δ` with `C L r ≤ 1 / 2`, solutions depend on the
  residual with Lipschitz constant `2 C` (`TauCeti.norm_sub_le_two_mul_mul_norm_sub`). So if an
  obstruction map `Φ₀` is `K`-Lipschitz along the solutions and is changed to `Φ₁` by at most `β`,
  the reduced values move by at most `β + 2 C K ‖e - e'‖`
  (`TauCeti.norm_sub_le_add_two_mul_mul_mul_norm_sub`), and stay away from zero when they started
  with a larger margin (`TauCeti.sub_le_norm_of_add_add_eq_zero`). Suppose
  the residuals satisfy `‖e p‖ ≤ ε`, and add a forcing term `g p ρ` of size at most `β`,
  depending on a second parameter `ρ`, such that `2 C (ε + β) < δ / 2` and
  `4 C² L (ε + β) < 1`. If moreover `E` is complete and `N p 0 = 0`, the forced equations
  `e p + g p ρ + D p x + N p x = 0` have solutions `x p ρ` in the range of `Q p`. They are
  `2 C`-Lipschitz in the forcing, unique in the range of `Q p` among solutions of norm less than
  `min (δ / 2) (2 C L)⁻¹`, and continuous in `(p, ρ)` as soon as each map
  `(p, ρ) ↦ Q p (e p + g p ρ + N p z)` with `‖z‖ ≤ 2 C (ε + β)` is
  (`TauCeti.exists_continuousOn_forall_add_add_add_eq_zero`). For residuals with
  `2 C² L ε < 1 / 4` and `2 C ε < δ / 4`, the tolerance `16 C² L β ≤ 1` and `8 C β ≤ δ` on the
  forcing implies both conditions and, when `C` and `L` are positive, puts the radius
  `2 C (ε + β)` below `min (δ / 2) (2 C L)⁻¹` (`TauCeti.two_mul_mul_add_lt_min`). This is how a
  small curvature perturbation `ρ`, added after the unforced correction has been constructed, is
  absorbed: its admissible size is fixed by the constants of the unforced problem alone.

No linearity of `D` and no completeness of `F` is needed; the fixed-point characterization needs
no norms at all, and the estimates only need seminorms on `E` and `F`. The right inverse `Q` is
only assumed additive, so that it applies to bounded linear maps over any normed field.

Mathlib's `ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` gives existence of
some zero in a ball, and `ApproximatesLinearOn.exists_eq_zero_of_two_mul_norm_le` (in
`TauCeti.Analysis.Calculus.ApproximatesLinearOn.Basic`) a unique zero when the linearization is an
equivalence. Here the linearization only has a right inverse, and the
solution is singled out by lying in the range of `Q`; for linear `D` this range is a complement of
the kernel of `D`, chosen by the construction. The a priori estimate compares the solution with
arbitrary approximate solutions in that range.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52 (2012), Proposition A.3.4.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

namespace TauCeti

variable {E F G : Type*} [FunLike G F E] {Q : G} {D N : E → F} {e : F} {C L : ℝ≥0} {δ : ℝ}

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [AddMonoidHomClass G F E]

/-- A point of the range of a right inverse `Q` of `D` solves `e + D x + N x = 0` exactly when it
is a fixed point of `x ↦ -Q (e + N x)`. -/
theorem mem_range_and_add_add_eq_zero_iff (hDQ : ∀ y, D (Q y) = y) {x : E} :
    (x ∈ range Q ∧ e + D x + N x = 0) ↔ x = -Q (e + N x) := by
  constructor
  · rintro ⟨⟨y, rfl⟩, h⟩
    rw [hDQ] at h
    have hy : y = -(e + N (Q y)) := eq_neg_of_add_eq_zero_left (by rw [← h]; abel)
    calc Q y = Q (-(e + N (Q y))) := by rw [← hy]
      _ = -Q (e + N (Q y)) := map_neg Q _
  · intro hx
    have hDx : D x = -(e + N x) := by
      conv_lhs => rw [hx]
      rw [← map_neg, hDQ]
    refine ⟨⟨-(e + N x), by rw [map_neg, ← hx]⟩, ?_⟩
    rw [hDx]
    abel

end AddCommGroup

/-- On a ball of radius `r` with `C L r ≤ 1 / 2`, the weight `1 - C L (a + b) / 2` of the
comparison estimates below is at least `1 / 2`. -/
private lemma one_half_le_one_sub_mul {r : ℝ} (hr : C * L * r ≤ 1 / 2) {a b : ℝ} (ha : a ≤ r)
    (hb : b ≤ r) : 1 / 2 ≤ 1 - C * (L / 2 * (a + b)) := by
  have hCL : (0 : ℝ) ≤ C * L := mul_nonneg C.property L.property
  have := mul_le_mul_of_nonneg_left (add_le_add ha hb) hCL
  nlinarith

section Seminormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [AddMonoidHomClass G F E]
  (hDQ : ∀ y, D (Q y) = y) (hQ : ∀ y, ‖Q y‖ ≤ C * ‖y‖)
  (hN : ∀ x ∈ closedBall (0 : E) δ, ∀ y ∈ closedBall (0 : E) δ,
    ‖N x - N y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
include hDQ hQ hN

/-- **Defect estimate.** A solution `x` of `e + D x + N x = 0` in the range of `Q` is compared with
an arbitrary point `y` of the closed ball of radius `δ` through the defect `y + Q (e + N y)` of `y`
as a fixed point of `z ↦ -Q (e + N z)`: the distance, weighted by `1 - C L (‖x‖ + ‖y‖) / 2`, is at
most the norm of the defect. -/
theorem one_sub_mul_norm_sub_le_norm_add_apply {x y : E} (hx : x ∈ closedBall 0 δ)
    (hy : y ∈ closedBall 0 δ) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0) :
    (1 - C * (L / 2 * (‖x‖ + ‖y‖))) * ‖x - y‖ ≤ ‖y + Q (e + N y)‖ := by
  have hx' : x = -Q (e + N x) := (mem_range_and_add_add_eq_zero_iff hDQ).1 ⟨hxQ, hxe⟩
  -- The difference splits into `-Q` of the difference of the remainders and the defect of `y`.
  have hsub : x - y = -Q (N x - N y) - (y + Q (e + N y)) := by
    calc x - y = -Q (e + N x) - y := by rw [← hx']
      _ = _ := by simp only [map_add, map_sub]; abel
  have hle : ‖x - y‖ ≤ C * (L / 2 * (‖x‖ + ‖y‖)) * ‖x - y‖ + ‖y + Q (e + N y)‖ := by
    calc ‖x - y‖ ≤ ‖Q (N x - N y)‖ + ‖y + Q (e + N y)‖ := by
          rw [hsub]
          exact (norm_sub_le _ _).trans_eq (by rw [norm_neg])
      _ ≤ C * (L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖) + ‖y + Q (e + N y)‖ := by
          gcongr
          exact (hQ _).trans (by gcongr; exact hN x hx y hy)
      _ = _ := by ring
  linarith

/-- **A priori estimate.** A solution `x` of `e + D x + N x = 0` in the range of the right inverse
`Q` satisfies a weighted comparison estimate with every point `y` of the range: the distance,
weighted by `1 - C L (‖x‖ + ‖y‖) / 2`, is at most `C` times the residual of `y`. When the weight is
positive, this bounds the distance by a multiple of the residual. -/
theorem one_sub_mul_norm_sub_le_mul_norm_add_add {x y : E} (hx : x ∈ closedBall 0 δ)
    (hy : y ∈ closedBall 0 δ) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) :
    (1 - C * (L / 2 * (‖x‖ + ‖y‖))) * ‖x - y‖ ≤ C * ‖e + D y + N y‖ := by
  refine (one_sub_mul_norm_sub_le_norm_add_apply hDQ hQ hN hx hy hxQ hxe).trans ?_
  obtain ⟨z, rfl⟩ := hyQ
  -- Since `Q z = Q (D (Q z))`, the defect of `Q z` is `Q` of its residual.
  calc ‖Q z + Q (e + N (Q z))‖ = ‖Q (e + D (Q z) + N (Q z))‖ := by
        rw [hDQ]; simp only [map_add]; abel_nf
    _ ≤ C * ‖e + D (Q z) + N (Q z)‖ := hQ _

/-- **Comparison of two equations.** Let `x` solve `e + D x + N x = 0` in the range of `Q`, and let
`y` solve a second equation `e' + D' y + N' y = 0` in the range of an additive right inverse `Q'` of
`D'`, whose target `F'` may differ from `F`. If `x` and `y` lie in the closed ball of radius `δ`,
the distance, weighted by `1 - C L (‖x‖ + ‖y‖) / 2`, is at most the norm
`‖Q (e + N y) - Q' (e' + N' y)‖` of the difference of the maps `z ↦ Q (e + N z)` and
`z ↦ Q' (e' + N' z)` at `y`. Only the first equation needs the bound on `Q` and the quadratic
estimate on `N`. -/
theorem one_sub_mul_norm_sub_le_norm_apply_sub_apply {F' G' : Type*} [AddCommGroup F']
    [FunLike G' F' E] [AddMonoidHomClass G' F' E] {Q' : G'} {D' N' : E → F'} {e' : F'}
    (hDQ' : ∀ y, D' (Q' y) = y) {x y : E} (hx : x ∈ closedBall 0 δ) (hy : y ∈ closedBall 0 δ)
    (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0) (hyQ : y ∈ range Q')
    (hye : e' + D' y + N' y = 0) :
    (1 - C * (L / 2 * (‖x‖ + ‖y‖))) * ‖x - y‖ ≤ ‖Q (e + N y) - Q' (e' + N' y)‖ := by
  have hy' : y = -Q' (e' + N' y) := (mem_range_and_add_add_eq_zero_iff hDQ').1 ⟨hyQ, hye⟩
  refine (one_sub_mul_norm_sub_le_norm_add_apply hDQ hQ hN hx hy hxQ hxe).trans_eq ?_
  rw [sub_eq_add_neg, ← hy', add_comm y]

/-- Solutions `x` of `e + D x + N x = 0` and `y` of `e' + D y + N y = 0` in the range of `Q`
satisfy a weighted comparison estimate: the distance, weighted by `1 - C L (‖x‖ + ‖y‖) / 2`, is at
most `C ‖e - e'‖`. On a common ball of radius `r ≤ δ` with `C L r < 1`, solutions thus depend
Lipschitz-continuously on the residual, with constant `C / (1 - C L r)`. -/
theorem one_sub_mul_norm_sub_le_mul_norm_sub {e' : F} {x y : E} (hx : x ∈ closedBall 0 δ)
    (hy : y ∈ closedBall 0 δ) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) (hye : e' + D y + N y = 0) :
    (1 - C * (L / 2 * (‖x‖ + ‖y‖))) * ‖x - y‖ ≤ C * ‖e - e'‖ := by
  refine (one_sub_mul_norm_sub_le_norm_apply_sub_apply hDQ hQ hN hDQ hx hy hxQ hxe hyQ hye).trans ?_
  rw [← map_sub, add_sub_add_right_eq_sub]
  exact hQ _

/-- **Lipschitz dependence on the residual.** Solutions `x` of `e + D x + N x = 0` and `y` of
`e' + D y + N y = 0` in the range of `Q`, both of norm at most `r ≤ δ` with `C L r ≤ 1 / 2`, satisfy
`‖x - y‖ ≤ 2 C ‖e - e'‖`. -/
theorem norm_sub_le_two_mul_mul_norm_sub {e' : F} {r : ℝ} (hrδ : r ≤ δ) (hr : C * L * r ≤ 1 / 2)
    {x y : E} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) (hye : e' + D y + N y = 0) : ‖x - y‖ ≤ 2 * C * ‖e - e'‖ := by
  have h := one_sub_mul_norm_sub_le_mul_norm_sub hDQ hQ hN
    (mem_closedBall_zero_iff.2 (hx.trans hrδ)) (mem_closedBall_zero_iff.2 (hy.trans hrδ)) hxQ hxe
    hyQ hye
  nlinarith [mul_le_mul_of_nonneg_right (one_half_le_one_sub_mul hr hx hy) (norm_nonneg (x - y))]

/-- **The forcing budget of a reduced section.** Let `x` solve the unforced equation
`e + D x + N x = 0` and `y` the forced equation `e' + D y + N y = 0`, both in the range of `Q` and
of norm at most `r ≤ δ` with `C L r ≤ 1 / 2`. If the forced obstruction map `Φ₁` differs from the
unforced one `Φ₀` by at most `β` at `y`, and `Φ₀` is `K`-Lipschitz between `x` and `y`, then the
reduced sections satisfy `‖Φ₁ y - Φ₀ x‖ ≤ β + 2 C K ‖e - e'‖`. -/
theorem norm_sub_le_add_two_mul_mul_mul_norm_sub {H : Type*} [SeminormedAddCommGroup H]
    {Φ₀ Φ₁ : E → H} {e' : F} {r β K : ℝ} (hrδ : r ≤ δ) (hr : C * L * r ≤ 1 / 2) (hK : 0 ≤ K)
    {x y : E} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) (hye : e' + D y + N y = 0) (hΦ : ‖Φ₁ y - Φ₀ y‖ ≤ β)
    (hΦ₀ : ‖Φ₀ y - Φ₀ x‖ ≤ K * ‖y - x‖) :
    ‖Φ₁ y - Φ₀ x‖ ≤ β + 2 * C * K * ‖e - e'‖ := by
  -- The forced correction moves by at most `2 C ‖e - e'‖`.
  have hxy : ‖y - x‖ ≤ 2 * C * ‖e - e'‖ := by
    rw [norm_sub_rev]
    exact norm_sub_le_two_mul_mul_norm_sub hDQ hQ hN hrδ hr hx hy hxQ hxe hyQ hye
  calc ‖Φ₁ y - Φ₀ x‖ ≤ ‖Φ₁ y - Φ₀ y‖ + ‖Φ₀ y - Φ₀ x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ β + K * (2 * C * ‖e - e'‖) :=
        add_le_add hΦ (hΦ₀.trans (mul_le_mul_of_nonneg_left hxy hK))
    _ = β + 2 * C * K * ‖e - e'‖ := by ring

/-- **Boundary separation.** In the situation of
`TauCeti.norm_sub_le_add_two_mul_mul_mul_norm_sub`, if the unforced reduced section has norm at
least `b` at `x`, then the forced reduced section has norm at least `b - (β + 2 C K ‖e - e'‖)` at
`y`. In particular it does not vanish when `β + 2 C K ‖e - e'‖ < b`. -/
theorem sub_le_norm_of_add_add_eq_zero {H : Type*} [SeminormedAddCommGroup H]
    {Φ₀ Φ₁ : E → H} {e' : F} {r b β K : ℝ} (hrδ : r ≤ δ) (hr : C * L * r ≤ 1 / 2) (hK : 0 ≤ K)
    {x y : E} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) (hye : e' + D y + N y = 0) (hΦ : ‖Φ₁ y - Φ₀ y‖ ≤ β)
    (hΦ₀ : ‖Φ₀ y - Φ₀ x‖ ≤ K * ‖y - x‖) (hb : b ≤ ‖Φ₀ x‖) :
    b - (β + 2 * C * K * ‖e - e'‖) ≤ ‖Φ₁ y‖ := by
  have h := norm_sub_le_add_two_mul_mul_mul_norm_sub hDQ hQ hN hrδ hr hK hx hy hxQ hxe hyQ hye hΦ
    hΦ₀
  have h' := norm_sub_norm_le (Φ₀ x) (Φ₁ y)
  rw [norm_sub_rev] at h'
  linarith

/-- **Stability on a small ball.** A solution `x` of `e + D x + N x = 0` in the range of `Q` and a
point `y` of the range, both of norm at most `r ≤ δ` with `C L r ≤ 1 / 2`, satisfy
`‖x - y‖ ≤ 2 C ‖e + D y + N y‖`: the distance of `y` to the solution is controlled by its
residual. -/
theorem norm_sub_le_two_mul_mul_norm_add_add {r : ℝ} (hrδ : r ≤ δ) (hr : C * L * r ≤ 1 / 2)
    {x y : E} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) : ‖x - y‖ ≤ 2 * C * ‖e + D y + N y‖ := by
  have h := one_sub_mul_norm_sub_le_mul_norm_add_add hDQ hQ hN
    (mem_closedBall_zero_iff.2 (hx.trans hrδ)) (mem_closedBall_zero_iff.2 (hy.trans hrδ)) hxQ hxe
    hyQ
  nlinarith [mul_le_mul_of_nonneg_right (one_half_le_one_sub_mul hr hx hy) (norm_nonneg (x - y))]

/-- **Comparison of two equations on a small ball.** Let `x` solve `e + D x + N x = 0` in the range
of `Q`, and `y` solve `e' + D' y + N' y = 0` in the range of an additive right inverse `Q'` of
`D'`. If both have norm at most `r ≤ δ` with `C L r ≤ 1 / 2`, then
`‖x - y‖ ≤ 2 ‖Q (e + N y) - Q' (e' + N' y)‖`. For a family of equations whose maps
`z ↦ Q (e + N z)` depend Lipschitz-continuously on a parameter, uniformly on the ball, the
solutions therefore do too, with twice the constant. -/
theorem norm_sub_le_two_mul_norm_apply_sub_apply {F' G' : Type*} [AddCommGroup F']
    [FunLike G' F' E] [AddMonoidHomClass G' F' E] {Q' : G'} {D' N' : E → F'} {e' : F'}
    (hDQ' : ∀ y, D' (Q' y) = y) {r : ℝ} (hrδ : r ≤ δ) (hr : C * L * r ≤ 1 / 2) {x y : E}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q') (hye : e' + D' y + N' y = 0) :
    ‖x - y‖ ≤ 2 * ‖Q (e + N y) - Q' (e' + N' y)‖ := by
  have h := one_sub_mul_norm_sub_le_norm_apply_sub_apply hDQ hQ hN hDQ'
    (mem_closedBall_zero_iff.2 (hx.trans hrδ)) (mem_closedBall_zero_iff.2 (hy.trans hrδ)) hxQ hxe
    hyQ hye
  nlinarith [mul_le_mul_of_nonneg_right (one_half_le_one_sub_mul hr hx hy) (norm_nonneg (x - y))]

omit hDQ in
/-- On the closed ball of radius `R ≤ δ`, the map `z ↦ Q (e + N z)` is Lipschitz with
constant `C L R`. -/
theorem lipschitzOnWith_apply_add_apply {R : ℝ} (hRδ : R ≤ δ) :
    LipschitzOnWith (C * L * R).toNNReal (fun z ↦ Q (e + N z)) (closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz w hw ↦ ?_
  have hz' := mem_closedBall_zero_iff.1 hz
  have hw' := mem_closedBall_zero_iff.1 hw
  have hR : 0 ≤ R := (norm_nonneg _).trans hz'
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  calc ‖Q (e + N z) - Q (e + N w)‖ = ‖Q (N z - N w)‖ := by
        rw [← map_sub, add_sub_add_left_eq_sub]
    _ ≤ C * (L / 2 * (‖z‖ + ‖w‖) * ‖z - w‖) := by
        grw [hQ, hN z (closedBall_subset_closedBall hRδ hz) w (closedBall_subset_closedBall hRδ hw)]
    _ ≤ C * (L / 2 * (R + R) * ‖z - w‖) := by gcongr
    _ = C * L * R * ‖z - w‖ := by ring

end Seminormed

section Normed

variable [NormedAddCommGroup E] [SeminormedAddCommGroup F] [AddMonoidHomClass G F E]
  (hDQ : ∀ y, D (Q y) = y) (hQ : ∀ y, ‖Q y‖ ≤ C * ‖y‖)
  (hN : ∀ x ∈ closedBall (0 : E) δ, ∀ y ∈ closedBall (0 : E) δ,
    ‖N x - N y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
include hDQ hQ hN

/-- **Uniqueness.** Two solutions of `e + D x + N x = 0` in the range of `Q`, both of norm at most
`r ≤ δ`, coincide when `C L r < 1`. -/
theorem eq_of_add_add_eq_zero {r : ℝ} (hrδ : r ≤ δ) (hr : C * L * r < 1) {x y : E}
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) (hye : e + D y + N y = 0) : x = y := by
  have h := one_sub_mul_norm_sub_le_mul_norm_add_add hDQ hQ hN
    (mem_closedBall_zero_iff.2 (hx.trans hrδ)) (mem_closedBall_zero_iff.2 (hy.trans hrδ)) hxQ hxe
    hyQ
  rw [hye, norm_zero, mul_zero] at h
  have hk : (L : ℝ) / 2 * (‖x‖ + ‖y‖) ≤ L * r := by
    have := add_le_add hx hy
    have hL : (0 : ℝ) ≤ L := L.property
    nlinarith
  have hpos : 0 < 1 - C * (L / 2 * (‖x‖ + ‖y‖)) := by
    have hC : (0 : ℝ) ≤ C := C.property
    nlinarith [mul_le_mul_of_nonneg_left hk hC]
  have hxy : ‖x - y‖ ≤ 0 := by
    by_contra hxy
    linarith [mul_pos hpos (not_le.1 hxy)]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hxy)

/-- **Uniqueness in the ball of radius `min (δ / 2) (2 C L)⁻¹`.** Two solutions of
`e + D x + N x = 0` in the range of `Q`, both of norm less than `min (δ / 2) (2 C L)⁻¹`, coincide:
on this ball `C L ‖x‖ < 1 / 2`. When `C L = 0` the ball is empty. -/
theorem eq_of_add_add_eq_zero_of_lt_min {x y : E} (hx : ‖x‖ < min (δ / 2) (2 * C * L)⁻¹)
    (hy : ‖y‖ < min (δ / 2) (2 * C * L)⁻¹) (hxQ : x ∈ range Q) (hxe : e + D x + N x = 0)
    (hyQ : y ∈ range Q) (hye : e + D y + N y = 0) : x = y := by
  set r := max ‖x‖ ‖y‖
  have hrγ : r < min (δ / 2) (2 * C * L)⁻¹ := max_lt hx hy
  rw [lt_min_iff] at hrγ
  have hr0 : 0 ≤ r := (norm_nonneg x).trans (le_max_left _ _)
  have hCL : C * L * r < 1 := by
    rcases eq_or_lt_of_le (mul_nonneg C.coe_nonneg L.coe_nonneg) with hCL | hCL
    · rw [← hCL, zero_mul]
      exact one_pos
    · have h := hrγ.2
      rw [← one_div, lt_div_iff₀ (by linarith)] at h
      linarith
  exact eq_of_add_add_eq_zero hDQ hQ hN (by linarith) hCL (le_max_left _ _) (le_max_right _ _) hxQ
    hxe hyQ hye

/-- **Existence.** If `E` is complete, `2 C ‖e‖ ≤ δ` and `2 C² L ‖e‖ < 1`, the equation
`e + D x + N x = 0` has a solution `x` in the range of `Q` with `‖x‖ ≤ 2 C ‖e‖`. It is the fixed
point of the contraction `x ↦ -Q (e + N x)` of the closed ball of radius `2 C ‖e‖`, and by
`TauCeti.eq_of_add_add_eq_zero` the only solution in the range of `Q` of norm at most `r`, for every
`r` with `2 C ‖e‖ ≤ r ≤ δ` and `C L r < 1`. -/
theorem exists_mem_range_norm_le_add_add_eq_zero [CompleteSpace E] (hN0 : N 0 = 0)
    (hδ : 2 * C * ‖e‖ ≤ δ) (he : 2 * C ^ 2 * L * ‖e‖ < 1) :
    ∃ x ∈ range Q, ‖x‖ ≤ 2 * C * ‖e‖ ∧ e + D x + N x = 0 := by
  set R : ℝ := 2 * C * ‖e‖ with hR
  have hR0 : 0 ≤ R := by positivity
  have hball : closedBall (0 : E) R ⊆ closedBall 0 δ := closedBall_subset_closedBall hδ
  set T : E → E := fun x ↦ -Q (e + N x) with hT
  -- On the ball of radius `R`, the remainder is bounded by `L ‖x‖² / 2`.
  have hsq (x : E) (hx : ‖x‖ ≤ R) : ‖N x‖ ≤ L / 2 * (‖x‖ * ‖x‖) := by
    have := hN x (hball (mem_closedBall_zero_iff.2 hx)) 0 (hball (mem_closedBall_self hR0))
    simpa [hN0, mul_assoc] using this
  have hmaps : MapsTo T (closedBall 0 R) (closedBall 0 R) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    calc ‖T x‖ ≤ C * ‖e + N x‖ := by rw [hT, norm_neg]; exact hQ _
      _ ≤ C * (‖e‖ + L / 2 * (R * R)) := by
          gcongr
          refine (norm_add_le e (N x)).trans ?_
          gcongr
          exact (hsq x hx).trans (by gcongr)
      _ = C * ‖e‖ * (1 + 2 * C ^ 2 * L * ‖e‖) := by rw [hR]; ring
      _ ≤ C * ‖e‖ * 2 := by gcongr; linarith
      _ = R := by rw [hR]; ring
  have hlip : LipschitzOnWith (Real.toNNReal (C * L * R)) T (closedBall 0 R) :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ by
      have h := (lipschitzOnWith_apply_add_apply (e := e) hQ hN hδ).dist_le_mul x hx y hy
      rw [dist_comm, dist_eq_norm] at h
      simpa only [hT, dist_eq_norm, neg_sub_neg] using h
  have hK : ContractingWith (Real.toNNReal (C * L * R)) (hmaps.restrict T _ _) :=
    ⟨Real.toNNReal_lt_one.2 (by rw [hR]; linarith), hlip.mapsToRestrict hmaps⟩
  obtain ⟨x, hxs, hfix, -⟩ := hK.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    (mem_closedBall_self hR0) (edist_ne_top _ _)
  obtain ⟨hxQ, hxe⟩ := (mem_range_and_add_add_eq_zero_iff hDQ).2 hfix.symm
  exact ⟨x, hxQ, mem_closedBall_zero_iff.1 hxs, hxe⟩

end Normed

/-- **The forcing tolerance.** If the residual `ε` satisfies the contraction and radius conditions
`2 C² L ε < 1 / 4` and `2 C ε < δ / 4`, and a forcing of size `β` stays within the tolerance
`16 C² L β ≤ 1` and `8 C β ≤ δ`, then the radius `2 C (ε + β)` of the forced solution lies in the
uniqueness ball: `2 C (ε + β) < min (δ / 2) (2 C L)⁻¹`. -/
theorem two_mul_mul_add_lt_min {C L δ ε β : ℝ} (hC : 0 < C) (hL : 0 < L)
    (hε : 2 * C ^ 2 * L * ε < 1 / 4) (hεδ : 2 * C * ε < δ / 4) (hβ : 16 * C ^ 2 * L * β ≤ 1)
    (hβδ : 8 * C * β ≤ δ) : 2 * C * (ε + β) < min (δ / 2) (2 * C * L)⁻¹ := by
  have hCL : 0 < 2 * C * L := by positivity
  rw [lt_min_iff, ← one_div, lt_div_iff₀ hCL]
  constructor <;> nlinarith

section Parametric

/-! ### Dependence on a parameter -/

variable {P : Type*} [TopologicalSpace P] {F G : P → Type*} [∀ p, FunLike (G p) (F p) E]
  {Q : ∀ p, G p} {D N : ∀ p, E → F p} {e : ∀ p, F p}

section Seminormed

variable [SeminormedAddCommGroup E] [∀ p, SeminormedAddCommGroup (F p)]
  [∀ p, AddMonoidHomClass (G p) (F p) E]

/-- **Continuous dependence on a parameter.** Let `e p + D p x + N p x = 0` be a family of
equations, with right inverses `Q p` of `D p` and remainders `N p` satisfying the bounds with
constants `C` and `L` uniform in `p` near `p₀`; the target `F p` of `D p` may depend on `p`. A
family of solutions `x p` in the range of `Q p`, of norm at most `r ≤ δ` with `C L r < 1` for `p`
near `p₀`, is continuous at `p₀` as soon as the map `p ↦ Q p (e p + N p z)` is continuous at `p₀`
for the single point `z = x p₀`. -/
theorem continuousAt_of_eventually_add_add_eq_zero {p₀ : P}
    (hDQ : ∀ᶠ p in 𝓝 p₀, ∀ y, D p (Q p y) = y) (hQ : ∀ᶠ p in 𝓝 p₀, ∀ y, ‖Q p y‖ ≤ C * ‖y‖)
    (hN : ∀ᶠ p in 𝓝 p₀, ∀ x ∈ closedBall (0 : E) δ, ∀ y ∈ closedBall (0 : E) δ,
      ‖N p x - N p y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
    {x : P → E} {r : ℝ} (hrδ : r ≤ δ) (hr : C * L * r < 1) (hx : ∀ᶠ p in 𝓝 p₀, ‖x p‖ ≤ r)
    (hxQ : ∀ᶠ p in 𝓝 p₀, x p ∈ range (Q p))
    (hxe : ∀ᶠ p in 𝓝 p₀, e p + D p (x p) + N p (x p) = 0)
    (hT : ContinuousAt (fun p ↦ Q p (e p + N p (x p₀))) p₀) : ContinuousAt x p₀ := by
  have hC : (0 : ℝ) ≤ C := C.property
  have hL : (0 : ℝ) ≤ L := L.property
  have hk : 0 < 1 - C * L * r := by linarith
  have hx₀ := hx.self_of_nhds
  rw [Metric.continuousAt_iff'] at hT ⊢
  intro ε hε
  filter_upwards [hT ((1 - C * L * r) * ε) (mul_pos hk hε), hDQ, hQ, hN, hx, hxQ, hxe]
    with p hp hDQp hQp hNp hxp hxQp hxep
  rw [dist_eq_norm] at hp ⊢
  have h := one_sub_mul_norm_sub_le_norm_apply_sub_apply hDQp hQp hNp hDQ.self_of_nhds
    (mem_closedBall_zero_iff.2 (hxp.trans hrδ)) (mem_closedBall_zero_iff.2 (hx₀.trans hrδ)) hxQp
    hxep hxQ.self_of_nhds hxe.self_of_nhds
  -- The weight in the comparison estimate is at least `1 - C L r`.
  have hw : 1 - C * L * r ≤ 1 - C * (L / 2 * (‖x p‖ + ‖x p₀‖)) := by
    have := add_le_add hxp hx₀
    nlinarith [mul_nonneg hC hL]
  refine lt_of_mul_lt_mul_left ?_ hk.le
  exact ((mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans h).trans_lt hp

variable (hDQ : ∀ p y, D p (Q p y) = y) (hQ : ∀ p y, ‖Q p y‖ ≤ C * ‖y‖)
  (hN : ∀ p, ∀ x ∈ closedBall (0 : E) δ, ∀ y ∈ closedBall (0 : E) δ,
    ‖N p x - N p y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
include hDQ hQ hN

/-- **Continuous dependence on a parameter**, global form: a family of solutions `x p` in the
range of `Q p`, of norm at most `r ≤ δ` with `C L r < 1`, is continuous when the map
`p ↦ Q p (e p + N p z)` is continuous for every `z` in the closed ball of radius `r`. -/
theorem continuous_of_forall_add_add_eq_zero {x : P → E} {r : ℝ} (hrδ : r ≤ δ)
    (hr : C * L * r < 1) (hx : ∀ p, ‖x p‖ ≤ r) (hxQ : ∀ p, x p ∈ range (Q p))
    (hxe : ∀ p, e p + D p (x p) + N p (x p) = 0)
    (hT : ∀ z ∈ closedBall (0 : E) r, Continuous fun p ↦ Q p (e p + N p z)) : Continuous x :=
  continuous_iff_continuousAt.2 fun p ↦
    continuousAt_of_eventually_add_add_eq_zero (.of_forall hDQ) (.of_forall hQ) (.of_forall hN)
      hrδ hr (.of_forall hx) (.of_forall hxQ) (.of_forall hxe)
      (hT _ (mem_closedBall_zero_iff.2 (hx p))).continuousAt

end Seminormed

variable [NormedAddCommGroup E] [∀ p, SeminormedAddCommGroup (F p)]
  [∀ p, AddMonoidHomClass (G p) (F p) E]
  (hDQ : ∀ p y, D p (Q p y) = y) (hQ : ∀ p y, ‖Q p y‖ ≤ C * ‖y‖)
  (hN : ∀ p, ∀ x ∈ closedBall (0 : E) δ, ∀ y ∈ closedBall (0 : E) δ,
    ‖N p x - N p y‖ ≤ L / 2 * (‖x‖ + ‖y‖) * ‖x - y‖)
include hDQ hQ hN

/-- **Existence of a continuous family of solutions.** If `E` is complete, the remainders vanish
at the origin, `N p 0 = 0`, and the residuals satisfy `2 C ‖e p‖ ≤ r` for one `r ≤ δ` with
`C L r < 1`, the solutions `x p` of
`e p + D p x + N p x = 0` constructed by `TauCeti.exists_mem_range_norm_le_add_add_eq_zero` depend
continuously on `p`, provided the map `p ↦ Q p (e p + N p z)` is continuous for every `z` in the
closed ball of radius `r`. By
`TauCeti.eq_of_add_add_eq_zero`, `x p` is the only solution in the range of `Q p` of norm at
most `r`. -/
theorem exists_continuous_forall_add_add_eq_zero [CompleteSpace E] (hN0 : ∀ p, N p 0 = 0)
    {r : ℝ} (hrδ : r ≤ δ) (hr : C * L * r < 1) (he : ∀ p, 2 * C * ‖e p‖ ≤ r)
    (hT : ∀ z ∈ closedBall (0 : E) r, Continuous fun p ↦ Q p (e p + N p z)) :
    ∃ x : P → E, Continuous x ∧
      ∀ p, x p ∈ range (Q p) ∧ ‖x p‖ ≤ 2 * C * ‖e p‖ ∧ e p + D p (x p) + N p (x p) = 0 := by
  have hC : (0 : ℝ) ≤ C := C.property
  have hL : (0 : ℝ) ≤ L := L.property
  have hsol (p : P) : ∃ x ∈ range (Q p), ‖x‖ ≤ 2 * C * ‖e p‖ ∧ e p + D p x + N p x = 0 := by
    refine exists_mem_range_norm_le_add_add_eq_zero (hDQ p) (hQ p) (hN p) (hN0 p)
      ((he p).trans hrδ) ?_
    have : 2 * C ^ 2 * L * ‖e p‖ = C * L * (2 * C * ‖e p‖) := by ring
    rw [this]
    exact (mul_le_mul_of_nonneg_left (he p) (mul_nonneg hC hL)).trans_lt hr
  choose x hxQ hxn hxe using hsol
  exact ⟨x, continuous_of_forall_add_add_eq_zero hDQ hQ hN hrδ hr (fun p ↦ (hxn p).trans (he p))
    hxQ hxe hT, fun p ↦ ⟨hxQ p, hxn p, hxe p⟩⟩

/-- **The forced correction.** Let the residuals satisfy `‖e p‖ ≤ ε`, and add a forcing term
`g p ρ`, depending on a second parameter `ρ ∈ s`, of size `‖g p ρ‖ ≤ β`, such that
`2 C (ε + β) < δ / 2` and `4 C² L (ε + β) < 1`. If `E` is complete and `N p 0 = 0`, the forced
equations

`e p + g p ρ + D p x + N p x = 0`

have solutions `x p ρ` in the range of `Q p` with `‖x p ρ‖ ≤ 2 C ‖e p + g p ρ‖`, depending
continuously on `(p, ρ)` as soon as the maps `(p, ρ) ↦ Q p (e p + g p ρ + N p z)` do for `z` in the
closed ball of radius `2 C (ε + β)`, and depending on the forcing with Lipschitz constant `2 C`:
`‖x p ρ - x p ρ'‖ ≤ 2 C ‖g p ρ - g p ρ'‖`. Moreover `x p ρ` is the only solution in the range
of `Q p` of norm less than `min (δ / 2) (2 C L)⁻¹`.

Both conditions hold when the unforced residuals satisfy `2 C² L ε < 1 / 4` and
`2 C ε < δ / 4` and the forcing stays within the tolerance `16 C² L β ≤ 1` and `8 C β ≤ δ`: then
`2 C² L (ε + β) < 3 / 8` and `2 C (ε + β) < δ / 2`, see also `TauCeti.two_mul_mul_add_lt_min`.
For a forcing `‖g p ρ‖ ≤ B ‖ρ‖` over the ball `‖ρ‖ ≤ τ`, take `β = B τ`: the tolerance holds as
soon as `τ ≤ (16 C² L (1 + B))⁻¹` and `τ ≤ δ / (8 C (1 + B))`. -/
theorem exists_continuousOn_forall_add_add_add_eq_zero [CompleteSpace E] (hN0 : ∀ p, N p 0 = 0)
    {V : Type*} [TopologicalSpace V] {s : Set V} {g : ∀ p, V → F p} {ε β : ℝ}
    (he : ∀ p, ‖e p‖ ≤ ε) (hg : ∀ p, ∀ ρ ∈ s, ‖g p ρ‖ ≤ β) (hRδ : 2 * C * (ε + β) < δ / 2)
    (hRL : 4 * C ^ 2 * L * (ε + β) < 1)
    (hT : ∀ z ∈ closedBall (0 : E) (2 * C * (ε + β)),
      ContinuousOn (fun q : P × V ↦ Q q.1 (e q.1 + g q.1 q.2 + N q.1 z)) (univ ×ˢ s)) :
    ∃ x : P → V → E, ContinuousOn (Function.uncurry x) (univ ×ˢ s) ∧
      (∀ p, ∀ ρ ∈ s, x p ρ ∈ range (Q p) ∧ ‖x p ρ‖ ≤ 2 * C * ‖e p + g p ρ‖ ∧
        e p + g p ρ + D p (x p ρ) + N p (x p ρ) = 0) ∧
      (∀ p, ∀ ρ ∈ s, ∀ y ∈ range (Q p), ‖y‖ < min (δ / 2) (2 * C * L)⁻¹ →
        e p + g p ρ + D p y + N p y = 0 → y = x p ρ) ∧
      ∀ p, ∀ ρ ∈ s, ∀ ρ' ∈ s, ‖x p ρ - x p ρ'‖ ≤ 2 * C * ‖g p ρ - g p ρ'‖ := by
  classical
  have hC : (0 : ℝ) ≤ C := C.property
  have hL : (0 : ℝ) ≤ L := L.property
  -- The solutions are constructed in the ball of radius `r = min (2 C (ε + β)) δ`, on which the
  -- contraction constant `C L r` is below `1 / 2`.
  set R : ℝ := 2 * C * (ε + β)
  have hCLR : C * L * R < 1 / 2 := by linarith
  set r : ℝ := min R δ
  have hCLr : C * L * r ≤ 1 / 2 := by
    linarith [hCLR, mul_le_mul_of_nonneg_left (min_le_left R δ) (mul_nonneg hC hL)]
  have hbound (p : P) (ρ : V) (hρ : ρ ∈ s) : 2 * C * ‖e p + g p ρ‖ ≤ r := by
    have h₁ : 2 * C * ‖e p + g p ρ‖ ≤ R :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (he p) (hg p ρ hρ)))
        (by positivity)
    exact le_min h₁
      (by linarith [mul_nonneg (mul_nonneg zero_le_two hC) (norm_nonneg (e p + g p ρ))])
  -- Solve over the parameter space `P × s`, viewed as a subtype of `P × V`.
  obtain ⟨x, hxc, hx⟩ := exists_continuous_forall_add_add_eq_zero (P := ↥(univ ×ˢ s))
    (F := fun q ↦ F q.val.1) (G := fun q ↦ G q.val.1) (Q := fun q ↦ Q q.val.1)
    (D := fun q ↦ D q.val.1) (N := fun q ↦ N q.val.1) (e := fun q ↦ e q.val.1 + g q.val.1 q.val.2)
    (fun q ↦ hDQ q.val.1) (fun q ↦ hQ q.val.1) (fun q ↦ hN q.val.1) (fun q ↦ hN0 q.val.1)
    (min_le_right R δ) (by linarith) (fun q ↦ hbound q.val.1 q.val.2 q.property.2)
    fun z hz ↦ (hT z (closedBall_subset_closedBall (min_le_left R δ) hz)).domRestrict
  set y : P → V → E := fun p ρ ↦ if h : ρ ∈ s then x ⟨(p, ρ), mem_univ p, h⟩ else 0
  have hyx (p : P) (ρ : V) (hρ : ρ ∈ s) : y p ρ = x ⟨(p, ρ), mem_univ p, hρ⟩ := dite_eq_left hρ
  have hys (p : P) (ρ : V) (hρ : ρ ∈ s) :
      y p ρ ∈ range (Q p) ∧ ‖y p ρ‖ ≤ 2 * C * ‖e p + g p ρ‖ ∧
        e p + g p ρ + D p (y p ρ) + N p (y p ρ) = 0 := by
    rw [hyx p ρ hρ]
    exact hx ⟨(p, ρ), mem_univ p, hρ⟩
  refine ⟨y, ?_, hys, fun p ρ hρ z hzQ hz hze ↦ ?_, fun p ρ hρ ρ' hρ' ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hxc using 1
    ext ⟨⟨p, ρ⟩, hq⟩
    exact hyx p ρ hq.2
  · -- The constructed solution has norm at most `2 C (ε + β)`, inside the uniqueness ball.
    obtain ⟨hQρ, hnρ, heρ⟩ := hys p ρ hρ
    have hyR : ‖y p ρ‖ ≤ R := hnρ.trans ((hbound p ρ hρ).trans (min_le_left R δ))
    -- The uniqueness ball is nonempty, so `C L > 0`.
    have hCL : 0 < 2 * (C : ℝ) * L := inv_pos.1 ((norm_nonneg z).trans_lt (lt_min_iff.1 hz).2)
    have hRγ : R < min (δ / 2) (2 * C * L)⁻¹ := by
      rw [lt_min_iff, ← one_div, lt_div_iff₀ hCL]
      exact ⟨hRδ, by linarith⟩
    exact eq_of_add_add_eq_zero_of_lt_min (hDQ p) (hQ p) (hN p) hz (hyR.trans_lt hRγ) hzQ hze
      hQρ heρ
  · obtain ⟨hQρ, hnρ, heρ⟩ := hys p ρ hρ
    obtain ⟨hQρ', hnρ', heρ'⟩ := hys p ρ' hρ'
    have h := norm_sub_le_two_mul_mul_norm_sub (hDQ p) (hQ p) (hN p) (min_le_right R δ) hCLr
      (hnρ.trans (hbound p ρ hρ)) (hnρ'.trans (hbound p ρ' hρ')) hQρ heρ hQρ' heρ'
    rwa [add_sub_add_left_eq_sub] at h

end Parametric

end TauCeti
