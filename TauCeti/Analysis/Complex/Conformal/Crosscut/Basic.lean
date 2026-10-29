/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Analysis.Normed.Module.Ball.Cut
public import TauCeti.Topology.ClusterSet
import TauCeti.Topology.Circle.Metric

/-!
# The circular crosscut of a disc at a boundary point

Fix a disc `ball c r` and a point `ζ` of its boundary circle. For `0 < ρ < 2 * r` the circle
`sphere ζ ρ` meets the disc in an arc, the **circular crosscut** of `ball c r` at `ζ` of radius
`ρ`, and that arc cuts the disc in two: the *crosscut neighbourhood* `ball c r ∩ ball ζ ρ` of `ζ`,
and the rest, `ball c r \ closedBall ζ ρ`. This file proves that decomposition, and then uses the
crosscut neighbourhoods as the approach regions along which the boundary behaviour of a holomorphic
function is read off: an estimate on the crosscut arcs and on a collar of the boundary circle,
propagated inside by the maximum modulus principle, yields a boundary limit and a continuous
extension to the closed disc, as in Carathéodory's boundary correspondence.

## The decomposition

That `ball c r ∩ ball ζ ρ` is connected is immediate — it is an intersection of two balls, hence
convex — and is proved in a seminormed real vector space, together with the rest of what the
crosscut neighbourhood is, in `TauCeti/Analysis/Normed/Module/Ball/Cut.lean`. The other piece is
not convex, and it is handled by a **Möbius reduction**: the inversion `z ↦ (z - ζ)⁻¹` at the
boundary point `ζ` carries the disc to a half-plane, because a circle through the centre of an
inversion goes to a line. Concretely, writing `a = c - ζ`, a point `z ≠ ζ` lies in `ball c r`
exactly when `1 < 2 * (a * (z - ζ)⁻¹).re` (`TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv`): the
disc becomes the open half-plane `{w | 1 < 2 * (a * w).re}`. The inversion simultaneously turns the
*complement* of `closedBall ζ ρ` into the ball `ball 0 ρ⁻¹`, since `‖(z - ζ)⁻¹‖ = ‖z - ζ‖⁻¹`. So
`ball c r \ closedBall ζ ρ` is carried onto an intersection of a half-plane with a ball — convex,
and nonempty exactly when `ρ < 2 * r` — and is therefore connected, being the image of a connected
set under the continuous inverse inversion `w ↦ ζ + w⁻¹`.

The two pieces are open, disjoint and cover `ball c r \ sphere ζ ρ`, so they *are* its connected
components: a circular crosscut separates the disc into exactly two parts. That the crosscut
neighbourhood is one of the two components is
`TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_inter_ball` of
`TauCeti/Analysis/Normed/Module/Ball/Cut.lean`, which needs no complex structure; that the other
piece is the other component is
`TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_diff_closedBall` below.

## The angular description

Which *angles* the crosscut occupies is settled in `TauCeti/Topology/Circle/Metric.lean`, where
nothing ties the cutting circle to the disc: writing `α = arg (c - ζ)` for the direction from `ζ`
to the centre and `d = dist ζ c`, the point of `sphere ζ ρ` at angle `θ` lies in `ball c r` exactly
when `ρ ^ 2 + d ^ 2 - r ^ 2 < 2 * ρ * d * cos (θ - α)` (`TauCeti.circleMap_mem_ball_iff_sq`). This
file adds the *boundary-point* case `d = r`, where the condition becomes `ρ < 2 * r * cos (θ - α)`
(`TauCeti.circleMap_mem_ball_iff`, with the `simp`-normal form `TauCeti.dist_circleMap_lt_iff`
beside it): for `0 < ρ < 2 * r` the crosscut consists of the angles *strictly* within
`arccos (ρ / (2 * r))` of `α`, while for `2 * r ≤ ρ` the circle `sphere ζ ρ` misses the disc.

## The boundary criterion

The frontier of the crosscut neighbourhood is contained in the arc `closedBall c r ∩ sphere ζ ρ`
together with the cap `sphere c r ∩ closedBall ζ ρ` (`TauCeti.frontier_ball_inter_ball_subset`), so
the maximum modulus principle bounds `f` on the closed crosscut neighbourhood by its values on
those two pieces (`TauCeti.norm_sub_le_of_mem_ball_inter_ball`).

Reading `f` on the cap presupposes continuity up to the boundary, which is the conclusion one is
after. So `TauCeti.norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn` assumes only holomorphy
on the open disc, asks for the arc bound on `ball c r ∩ sphere ζ ρ`, and replaces the cap bound by
a bound on a *collar* `r₀ ≤ dist w c` of the boundary inside the crosscut neighbourhood — all of it
data about `f` inside the disc. Those oscillation bounds, one for each tolerance `ε`, give:

> a holomorphic function on a disc, with values in a complex Banach space, has a limit at a
> boundary point `ζ` as soon as, for every `ε > 0`, there is *some* radius `ρ > 0` at which `f` is
> within `ε` of a single value on the part `ball c r ∩ sphere ζ ρ` of the circle around `ζ` inside
> the disc and on a collar of the boundary.

The radius `ρ`, the collar and the value approximated may all depend on `ε`, and `ρ` is not asked
to stay below `2 * r`. This is `TauCeti.exists_tendsto_nhdsWithin_ball`, and
`TauCeti.exists_continuousOn_closedBall_eqOn` is its global form, a continuous extension to the
closed disc. No boundedness of `f` is assumed: the estimate makes `f` Cauchy along the disc at `ζ`,
and completeness of the codomain supplies the limit. Neither injectivity of `f` nor any hypothesis
on the image is used.

## Generality

The domain is the complex plane throughout: the decomposition of the far side is performed by the
complex inversion `z ↦ (z - ζ)⁻¹`. The analytic half allows values in any complex normed space,
complete for the two theorems that produce a limit. The set lemmas that split a set by a sphere live
in `TauCeti/Topology/MetricSpace/Cut.lean`, and the near side of the crosscut, including the bound
on its frontier, in `TauCeti/Analysis/Normed/Module/Ball/Cut.lean`.

## Main results

* `TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv` — the inversion at a boundary point carries a
  disc to a half-plane.
* `TauCeti.circleMap_mem_ball_iff` — the angular description of a circular crosscut.
* `TauCeti.isConnected_ball_diff_closedBall` — the part of a disc outside a circular crosscut is
  connected.
* `TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_diff_closedBall` — together with its
  companion `TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_inter_ball`, a circular crosscut
  separates the disc into exactly two connected components.
* `TauCeti.norm_sub_le_of_mem_ball_inter_ball` and
  `TauCeti.norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn` — the maximum modulus principle
  on a crosscut neighbourhood, and its form assuming only holomorphy on the open disc, with the cap
  replaced by a collar of the boundary.
* `TauCeti.exists_tendsto_nhdsWithin_ball` and `TauCeti.exists_continuousOn_closedBall_eqOn` — the
  crosscut criterion for a boundary limit, and for a continuous extension to the closed disc.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (crosscuts).
-/

public section

namespace TauCeti

open Complex Filter Metric Set Topology
open scoped Real

variable {c ζ z : ℂ} {r ρ : ℝ}

/-! ## The inversion at a boundary point -/

/-- **The inversion at a boundary point carries a disc to a half-plane.** If `ζ` lies on the circle
`sphere c r`, then a point `z ≠ ζ` lies in `ball c r` exactly when its image `(z - ζ)⁻¹` under the
inversion centred at `ζ` lies in the open half-plane `{w | 1 < 2 * ((c - ζ) * w).re}`.

This is the classical fact that a Möbius map sends a circle through the centre of the inversion to
a line, in the form the crosscut decomposition needs: which *side* of that line the disc goes to.
Multiplied by `normSq (z - ζ)`, the half-plane condition becomes
`normSq (z - c) < normSq (c - ζ) = r ^ 2`. -/
theorem mem_ball_iff_one_lt_two_mul_re_mul_inv (hζ : dist ζ c = r) (hz : z ≠ ζ) :
    z ∈ ball c r ↔ 1 < 2 * ((c - ζ) * (z - ζ)⁻¹).re := by
  have hns : 0 < normSq (z - ζ) := normSq_pos.mpr (sub_ne_zero.mpr hz)
  -- the half-plane condition, cleared of the denominator `normSq (z - ζ)`
  have key : (2 * ((c - ζ) * (z - ζ)⁻¹).re - 1) * normSq (z - ζ) =
      normSq (c - ζ) - normSq (z - c) := by
    rw [mul_re, inv_re, inv_im]
    field_simp
    simp only [normSq_apply, sub_re, sub_im]
    ring
  -- membership in the disc, compared through squared distances
  have hball : z ∈ ball c r ↔ normSq (z - c) < normSq (c - ζ) := by
    rw [mem_ball, ← hζ, dist_comm ζ, dist_eq, dist_eq, normSq_eq_norm_sq, normSq_eq_norm_sq,
      sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [hball]
  constructor <;> intro h <;> nlinarith

/-! ## The angular description of a circular crosscut -/

/-- **A circular crosscut is an arc of angles around the direction of the centre.** For `ζ` on the
circle `sphere c r` and `ρ > 0`, the point of `sphere ζ ρ` at angle `θ` lies in `ball c r` exactly
when `ρ < 2 * r * cos (θ - arg (c - ζ))`.

This is the boundary-point case `dist ζ c = r` of `TauCeti.circleMap_mem_ball_iff_sq`. For `r = 0`
both sides are false.

This is not a `simp` lemma, since `Metric.mem_ball` rewrites its left-hand side; the `simp`-normal
companion is `TauCeti.dist_circleMap_lt_iff`. -/
theorem circleMap_mem_ball_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    circleMap ζ ρ θ ∈ ball c r ↔ ρ < 2 * r * Real.cos (θ - (c - ζ).arg) := by
  rw [circleMap_mem_ball_iff_sq (hζ ▸ dist_nonneg) ρ θ, hζ]
  constructor <;> intro h <;> nlinarith

/-- **A circular crosscut is an arc of angles around the direction of the centre**, stated in
`simp` normal form: `TauCeti.circleMap_mem_ball_iff` with the membership in `ball c r` unfolded by
`Metric.mem_ball`. -/
@[simp]
theorem dist_circleMap_lt_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    dist (circleMap ζ ρ θ) c < r ↔ ρ < 2 * r * Real.cos (θ - (c - ζ).arg) :=
  circleMap_mem_ball_iff hζ hρ θ

/-- Every point of a circle has an angular representative in the period of length `2 * π` centred
at any prescribed angle. This also covers radius zero; a negative-radius sphere is empty. -/
theorem exists_mem_Icc_circleMap_eq (α : ℝ) {z : ℂ} (hz : z ∈ sphere ζ ρ) :
    ∃ t ∈ Icc (-π) π, circleMap ζ ρ (α + t) = z := by
  obtain ⟨θ, hθ, rfl⟩ : z ∈ circleMap ζ ρ '' Icc (α - π) (α - π + 2 * π) := by
    rwa [(periodic_circleMap ζ ρ).image_Icc Real.two_pi_pos, range_circleMap,
      abs_of_nonneg (nonneg_of_mem_sphere hz)]
  exact ⟨θ - α, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, by rw [add_sub_cancel]⟩

/-! ## The far side of a circular crosscut

The *near* side `ball c r ∩ ball ζ ρ` is convex, and is treated without any complex structure in
`TauCeti/Analysis/Normed/Module/Ball/Cut.lean`. The far side is not convex, and is where the Möbius
reduction is needed. -/

/-- The inversion model of a disc punctured by a crosscut: the intersection of the open half-plane
`{w | 1 < 2 * (a * w).re}` with `ball 0 R` is convex, being an intersection of a half-space with a
ball. -/
private lemma convex_halfPlane_inter_ball (a : ℂ) (R : ℝ) :
    Convex ℝ ({w : ℂ | 1 < 2 * (a * w).re} ∩ ball 0 R) := by
  have hlin : IsLinearMap ℝ fun w : ℂ => 2 * (a * w).re :=
    { map_add := by intro x y; simp [mul_add, Complex.mul_re]
      map_smul := by intro s x; simp [Complex.real_smul, Complex.mul_re]; ring }
  exact (convex_halfSpace_gt hlin 1).inter (convex_ball _ _)

/-- A point of the half-plane `{w | 1 < 2 * (a * w).re}` is nonzero, since at `w = 0` the defining
quantity is `0`. -/
private lemma ne_zero_of_one_lt_two_mul_re_mul {a w : ℂ} (hw : 1 < 2 * (a * w).re) : w ≠ 0 := by
  rintro rfl
  rw [mul_zero, Complex.zero_re] at hw
  linarith

/-- The inversion model region is nonempty when the crosscut radius is less than the diameter,
`ρ < 2 * ‖a‖`; a witness is a real multiple `s / a` with `1 / 2 < s < ‖a‖ / ρ`. -/
private lemma nonempty_halfPlane_inter_ball {a : ℂ} (hρ : 0 < ρ) (hρ' : ρ < 2 * ‖a‖) :
    ({w : ℂ | 1 < 2 * (a * w).re} ∩ ball 0 ρ⁻¹).Nonempty := by
  have hr : 0 < ‖a‖ := by linarith
  obtain ⟨s, hs1, hs2⟩ := exists_between (show (1 : ℝ) / 2 < ‖a‖ / ρ by
    rw [lt_div_iff₀ hρ]; linarith)
  refine ⟨(s : ℂ) / a, ?_, ?_⟩
  · rw [mem_ofPred_eq, mul_div_cancel₀ _ (norm_pos_iff.mp hr), ofReal_re]
    linarith
  · rwa [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg (by linarith),
      div_lt_iff₀ hr, inv_mul_eq_div]

/-- The inversion `w ↦ ζ + w⁻¹` carries the model region onto the disc-minus-crosscut region: the
half-plane factor becomes `ball c r` by `TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv`, and the
ball factor becomes the complement of `closedBall ζ ρ`. -/
private lemma image_add_inv_halfPlane_inter_ball (hζ : dist ζ c = r) (hρ : 0 < ρ) :
    (fun w : ℂ => ζ + w⁻¹) '' ({w : ℂ | 1 < 2 * ((c - ζ) * w).re} ∩ ball 0 ρ⁻¹)
      = ball c r \ closedBall ζ ρ := by
  ext y
  constructor
  · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
    have hw0 : w ≠ 0 := ne_zero_of_one_lt_two_mul_re_mul hw1
    have hne : ζ + w⁻¹ ≠ ζ := by simpa using hw0
    refine ⟨by rwa [mem_ball_iff_one_lt_two_mul_re_mul_inv hζ hne, add_sub_cancel_left, inv_inv],
      ?_⟩
    rw [mem_ball_zero_iff, lt_inv_comm₀ (norm_pos_iff.mpr hw0) hρ, ← norm_inv] at hw2
    simpa [dist_eq_norm] using hw2
  · rintro ⟨hy1, hy2⟩
    have hyne : y ≠ ζ := by rintro rfl; exact hy2 (mem_closedBall_self hρ.le)
    refine ⟨(y - ζ)⁻¹, ⟨(mem_ball_iff_one_lt_two_mul_re_mul_inv hζ hyne).mp hy1, ?_⟩, by simp⟩
    rw [mem_closedBall, not_le, dist_eq_norm] at hy2
    rwa [mem_ball_zero_iff, norm_inv, inv_lt_inv₀ (hρ.trans hy2) hρ]

/-- **The part of a disc outside a circular crosscut is connected.** For `ζ` on the circle
`sphere c r` and `0 < ρ < 2 * r`, the set `ball c r \ closedBall ζ ρ` is connected, and in
particular nonempty.

The set is not convex; it is the image of a convex set under the inversion `w ↦ ζ + w⁻¹`, as
explained in the module docstring. -/
theorem isConnected_ball_diff_closedBall (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρ' : ρ < 2 * r) : IsConnected (ball c r \ closedBall ζ ρ) := by
  have hac : ‖c - ζ‖ = r := by rw [← dist_eq_norm, dist_comm, hζ]
  rw [← image_add_inv_halfPlane_inter_ball hζ hρ]
  refine ((convex_halfPlane_inter_ball _ _).isConnected
    (nonempty_halfPlane_inter_ball hρ (by rw [hac]; exact hρ'))).image _ fun w hw => ?_
  exact (continuousAt_const.add
    (continuousAt_inv₀ (ne_zero_of_one_lt_two_mul_re_mul hw.1))).continuousWithinAt

/-- **The far side of a circular crosscut is a connected component of the cut disc.** The companion
of `TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_inter_ball` of
`TauCeti/Analysis/Normed/Module/Ball/Cut.lean`; here the connectedness of the piece is
`TauCeti.isConnected_ball_diff_closedBall` rather than convexity, which is why this half is stated
in the plane. -/
theorem connectedComponentIn_ball_diff_sphere_eq_ball_diff_closedBall
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρ' : ρ < 2 * r) (hz : z ∈ ball c r \ closedBall ζ ρ) :
    connectedComponentIn (ball c r \ sphere ζ ρ) z = ball c r \ closedBall ζ ρ := by
  have hsub : ball c r \ closedBall ζ ρ ⊆ ball c r \ sphere ζ ρ :=
    sdiff_sphere_eq_inter_ball_union_sdiff_closedBall (x := ζ) (s := ball c r) ▸ subset_union_right
  refine Subset.antisymm ?_ ((isConnected_ball_diff_closedBall hζ hρ hρ').isPreconnected
    |>.subset_connectedComponentIn hz hsub)
  rcases subset_inter_ball_or_subset_sdiff_closedBall (x := ζ) (s := ball c r) isOpen_ball
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) with h | h
  · exact absurd hz (Set.disjoint_left.mp disjoint_inter_ball_sdiff_closedBall
      (h (mem_connectedComponentIn (hsub hz))))
  · exact h

/-! ## The maximum modulus principle on a crosscut neighbourhood -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a : E} {C r₀ : ℝ}

/-- **The maximum modulus principle on a crosscut neighbourhood.** A function holomorphic on the
crosscut neighbourhood `ball c r ∩ ball ζ ρ` and continuous up to its closure that stays within `C`
of a value `a` on the closed crosscut arc and on the boundary cap stays within `C` of `a` on the
closure of the crosscut neighbourhood.

The frontier of the crosscut neighbourhood is covered by those two pieces
(`TauCeti.frontier_ball_inter_ball_subset`). A caller holding `DiffContOnCl ℂ f (ball c r)`
supplies the regularity hypothesis by `DiffContOnCl.mono inter_subset_left`. -/
theorem norm_sub_le_of_mem_ball_inter_ball (hf : DiffContOnCl ℂ f (ball c r ∩ ball ζ ρ))
    (harc : ∀ w ∈ closedBall c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ C)
    (hcap : ∀ w ∈ sphere c r ∩ closedBall ζ ρ, ‖f w - a‖ ≤ C)
    (hz : z ∈ closure (ball c r ∩ ball ζ ρ)) : ‖f z - a‖ ≤ C := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball.subset inter_subset_left) (hf.sub_const a) (fun w hw => ?_) hz
  rcases frontier_ball_inter_ball_subset hw with h | h
  · exact hcap w h
  · exact harc w h

/-- **The maximum modulus principle on a crosscut neighbourhood, from interior values alone.** A
function holomorphic on `ball c r`, with *no* regularity assumed at the boundary circle, that stays
within `C` of a value `a` on the part `ball c r ∩ sphere ζ ρ` of the crosscut circle inside the disc
and on the collar `r₀ ≤ dist w c` of the crosscut neighbourhood, stays within `C` of `a` throughout
that neighbourhood.

The hypotheses constrain only the values `f` takes *inside* the disc, so that in the boundary
criteria below a boundary limit is a conclusion rather than a restatement of an assumed continuity
up to the boundary. -/
theorem norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn
    (hd : DifferentiableOn ℂ f (ball c r)) (hr₀ : r₀ < r)
    (harc : ∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ C)
    (hcap : ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ C)
    (hz : z ∈ ball c r ∩ ball ζ ρ) : ‖f z - a‖ ≤ C := by
  -- run the maximum modulus principle on a concentric disc `ball c s` with
  -- `max r₀ (dist z c) < s < r`, on whose closure `f` is continuous
  have hzr : dist z c < r := mem_ball.mp hz.1
  obtain ⟨s, hzs, hr₀s, hsr⟩ : ∃ s, dist z c < s ∧ r₀ ≤ s ∧ s < r :=
    ⟨(max r₀ (dist z c) + r) / 2, by
      have h₁ := le_max_left r₀ (dist z c)
      have h₂ := le_max_right r₀ (dist z c)
      have h₃ := max_lt hr₀ hzr
      exact ⟨by linarith, by linarith, by linarith⟩⟩
  have hsub : closedBall c s ⊆ ball c r := closedBall_subset_ball hsr
  refine norm_sub_le_of_mem_ball_inter_ball (r := s)
    ((hd.diffContOnCl_ball hsub).mono inter_subset_left)
    (fun w hw => harc w ⟨hsub hw.1, hw.2⟩) (fun w hw => ?_)
    (subset_closure ⟨mem_ball.mpr hzs, hz.2⟩)
  have hwc : dist w c = s := mem_sphere.mp hw.1
  exact hcap w ⟨hsub (mem_closedBall.mpr hwc.le), hw.2⟩ (hwc ▸ hr₀s)

/-- **The oscillation of a holomorphic function on a crosscut neighbourhood** is at most twice a
bound holding, around a common value, on the crosscut arc and on the collar of the boundary. -/
theorem dist_le_of_mem_ball_inter_ball (hd : DifferentiableOn ℂ f (ball c r)) (hr₀ : r₀ < r)
    (harc : ∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ C)
    (hcap : ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ C)
    {x y : ℂ} (hx : x ∈ ball c r ∩ ball ζ ρ) (hy : y ∈ ball c r ∩ ball ζ ρ) :
    dist (f x) (f y) ≤ 2 * C := by
  have hx' := norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn hd hr₀ harc hcap hx
  have hy' := norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn hd hr₀ harc hcap hy
  rw [← dist_eq_norm] at hx' hy'
  linarith [dist_triangle_right (f x) (f y) a]

/-! ## The crosscut criterion for boundary behaviour -/

/-- The crosscut estimate as an oscillation bound: on the trace on the disc of a small enough ball
around `ζ`, the values of `f` are within `ε` of one another. -/
private lemma forall_exists_dist_le_of_crosscut (hd : DifferentiableOn ℂ f (ball c r))
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ r₀ < r, ∃ a : E, (∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ ε) ∧
      ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ ε) :
    ∀ ε > 0, ∃ ρ > 0, ∀ x ∈ ball c r ∩ ball ζ ρ, ∀ y ∈ ball c r ∩ ball ζ ρ,
      dist (f x) (f y) ≤ ε := fun ε hε => by
  obtain ⟨ρ, hρ, r₀, hr₀, a, harc, hcap⟩ := h (ε / 2) (by positivity)
  refine ⟨ρ, hρ, fun x hx y hy => ?_⟩
  linarith [dist_le_of_mem_ball_inter_ball hd hr₀ harc hcap hx hy]

/-- **The crosscut criterion, cluster-set form.** If for every `ε > 0` there is *some* radius
`ρ > 0` at which the function `f` is within `ε` of a single value on the part
`ball c r ∩ sphere ζ ρ` of the circle around `ζ` inside the disc and on a collar of the boundary,
then `f` has at most one cluster value at `ζ` along the disc.

Only the values of `f` on the *open* disc are constrained, and only holomorphy there is assumed.
The point `ζ` need not lie on the boundary circle, `ρ`, `r₀` and `a` may all depend on `ε`, and `ρ`
is not bounded above by `2 * r`, so a witness need not cut a circular crosscut. -/
theorem subsingleton_clusterSetOn_ball (hd : DifferentiableOn ℂ f (ball c r))
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ r₀ < r, ∃ a : E, (∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ ε) ∧
      ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ ε) :
    (clusterSetOn f (ball c r) ζ).Subsingleton :=
  subsingleton_clusterSetOn_of_forall_exists (forall_exists_dist_le_of_crosscut hd h)

/-- **The crosscut criterion for a boundary limit.** A holomorphic function on a disc, with values
in a complex Banach space, has a limit at `ζ` along the disc as soon as for every `ε > 0` there is
some radius `ρ > 0` at which it is within `ε` of a single value on the part `ball c r ∩ sphere ζ ρ`
of the circle around `ζ` inside the disc and on a collar of the boundary.

The content is at a boundary point `ζ`, but none is required: inside the disc the limit exists by
continuity, and away from its closure the filter `𝓝[ball c r] ζ` is trivial. Nothing is assumed at
the boundary circle itself, and no boundedness of `f`: the estimate makes `f` Cauchy along the disc
at `ζ`. As in `TauCeti.subsingleton_clusterSetOn_ball`, no upper bound on `ρ` is imposed. -/
theorem exists_tendsto_nhdsWithin_ball [CompleteSpace E] (hd : DifferentiableOn ℂ f (ball c r))
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ r₀ < r, ∃ a : E, (∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ ε) ∧
      ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ ε) :
    ∃ v, Tendsto f (𝓝[ball c r] ζ) (𝓝 v) :=
  exists_tendsto_of_forall_exists (forall_exists_dist_le_of_crosscut hd h)

/-- **The crosscut criterion for a continuous extension to the closed disc.** If the hypothesis of
`TauCeti.exists_tendsto_nhdsWithin_ball` holds at *every* point of the boundary circle, the
holomorphic function `f`, with values in a complex Banach space, extends continuously to
`closedBall c r`.

Only holomorphy on the *open* disc is assumed, so the extension is produced rather than assumed.
Nothing here asserts that the extension is injective. -/
theorem exists_continuousOn_closedBall_eqOn [CompleteSpace E] (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r))
    (h : ∀ ζ ∈ sphere c r, ∀ ε > 0, ∃ ρ > 0, ∃ r₀ < r, ∃ a : E,
      (∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ ε) ∧
        ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ ε) :
    ∃ F : ℂ → E, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) :=
  closure_ball c hr.ne' ▸ exists_continuousOn_closure_eqOn_of_forall_exists hd.continuousOn
    fun ζ hζ => forall_exists_dist_le_of_crosscut hd (h ζ (frontier_ball c hr.ne' ▸ hζ))

end TauCeti
