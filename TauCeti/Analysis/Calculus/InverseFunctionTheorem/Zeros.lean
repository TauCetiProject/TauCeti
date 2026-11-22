/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.UniformSpace.HeineCantor
public import TauCeti.Analysis.Calculus.ApproximatesLinearOn
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Family
public import TauCeti.Topology.Compactness.Compact
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Persistence and count of nondegenerate zeros

This file proves the stability of nondegenerate zeros, and of their number in a compact set, in
two settings: under a single `C¹`-small perturbation, quantitatively, and along families of maps
converging in `C¹` along a filter.

## `C¹`-small perturbations

Let `f : E → F` be a map between Banach spaces and `K ⊆ E` compact. Call a zero `x` of `f` in `K`
*nondegenerate* if `x` is an interior point of `K` and the derivative of `f` at `x` is invertible.
If every zero of a map continuous on `K` has invertible derivative, there are only finitely many
zeros in `K` (`IsCompact.finite_inter_preimage_of_isInvertible_fderiv`). If `f` is continuous on
`K`, all its zeros in `K` are nondegenerate and its derivative is continuous at each of them, then
these zeros persist under perturbations that are small in `C¹` on `K`: every such perturbation `g`
again has only nondegenerate zeros in `K`, and they correspond bijectively to those of `f`, each
moving by an arbitrarily small distance. In particular the number of zeros in `K` does not change.

This is how a count of transverse intersection points is shown to be locally constant along a
family of maps. For instance, near an intersection point of a map `u` with a codimension-two
submanifold `D` cut out near that point as `{φ = 0}` by a submersion `φ`, the nearby intersection
points of `u` with `D` are the zeros of `φ ∘ u`, and transversality of `u` to `D` makes them
nondegenerate. For a continuous family of maps whose derivatives also vary continuously, the
number of nondegenerate zeros in `K` is locally constant in the parameter, hence constant over a
connected parameter space, as long as every member of the family has only nondegenerate zeros in
`K`.

The local step is a quantitative inverse function theorem (`TauCeti.exists_zero_perturbation`):
near a point where the derivative of `f` is continuous and invertible, a map whose derivative
stays close to that of `f` on a small closed ball, and which is small at the centre, has exactly
one zero in the ball, and that zero is nondegenerate, at distance from the centre linearly
controlled by the value there. It rests on Mathlib's local surjectivity and injectivity of maps
approximating a linear equivalence, through
`ApproximatesLinearOn.exists_eq_zero_of_two_mul_norm_le`. The persistence of a nondegenerate
critical point, `TauCeti.IsNondegenerateCriticalPoint.exists_criticalPoint_perturbation`, is its
case `f := fderiv ℝ h`. Away from the zeros of `f`, the norm of `f` is bounded below on the compact
remainder of `K`, so a uniformly close `g` has no zeros there.

## Converging families

A solution `x₀` of `Φ₀ x = y` for a `C¹` map `Φ₀ : E → F` is *nondegenerate* when the derivative
`D Φ₀ (x₀)` is invertible; the main case is a nondegenerate zero, `y = 0`. Nondegenerate solutions
are stable: if `Φ i → Φ₀` in `C¹` along a filter `l`, every map `Φ i` close enough to the limit
has exactly one solution of `Φ i x = y` near `x₀`, this solution is again nondegenerate, and it
converges to `x₀` along `l`
(`TauCeti.exists_tendsto_inter_preimage_singleton_eq_singleton_of_tendstoContDiffAt`). This is the
inverse function theorem for converging families
(`TauCeti.exists_openPartialHomeomorph_tendstoContDiffAt_symm`) applied at the value `y`: the maps
`Φ i` restrict to partial homeomorphisms with one common source around `x₀` whose targets all
contain one neighbourhood of `y`, and their inverses converge.

On a compact set `K` whose solutions of `Φ₀ x = y` are all nondegenerate and lie in the interior of
`K`, these solutions are moreover isolated, hence finitely many
(`IsCompact.finite_inter_preimage_of_isInvertible_fderiv`), and they persist as a
whole: eventually along `l` the solutions of `Φ i x = y` in `K` are in bijection with those of
`Φ₀ x = y`, through a bijection under which each perturbed solution converges along `l` to the
solution of `Φ₀ x = y` it comes from, and they are all nondegenerate
(`TauCeti.exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt`). Away from the
solutions for `Φ₀`, the maps `Φ i` do not take the value `y` on `K` for `i` close to the limit, by
compactness of `K` and continuous convergence of the values
(`IsCompact.eventually_forall_mem_of_tendsto_prod_nhds`). In particular the number of solutions in
`K` is eventually constant
(`TauCeti.eventually_ncard_inter_preimage_singleton_eq_of_tendstoContDiffAt`). The hypothesis that
the solutions for `Φ₀` lie in the interior of `K` cannot be dropped: solutions for nearby maps may
leave `K` through its boundary.

A typical application is local, to the transverse preimage `u⁻¹(D)` of a codimension-two
submanifold `D` under a map `u` of a surface. In a chart where `D = g⁻¹(0)`, the points of `u⁻¹(D)`
are the zeros of `g ∘ u`, and transverse intersection points are nondegenerate zeros. So in a
compact set of the chart whose zeros are interior, along a `C¹`-converging family of maps the
number of these points is eventually constant and they converge to the original intersection
points. This local count is one ingredient of a stabilization of unstable sphere components by the
full preimage of a transverse cut; the results here are stated only for maps between Banach spaces
on a single compact set.

## Main results

* `TauCeti.exists_zero_perturbation`: a map `C¹`-close to `f` on a small ball around a point
  where `fderiv f` is continuous and invertible, and small at its centre, has a unique zero in the
  ball, it is nondegenerate, and its distance to the centre is linearly controlled.
* `IsCompact.exists_pos_forall_exists_equiv_sep_eq_zero`: a `C¹`-small perturbation of `f` on `K`
  has only nondegenerate zeros in `K`, in a bijection with those of `f` moving each by at most
  any prescribed `ε > 0`.
* `IsCompact.exists_pos_forall_ncard_sep_eq_zero_eq`: hence it has as many zeros in `K` as `f`.
* `IsCompact.eventually_ncard_sep_eq_zero_eq`: along a family of maps continuous together with
  their derivatives, the number of zeros in `K` is locally constant near a member with only
  nondegenerate zeros in `K`.
* `IsCompact.ncard_sep_eq_zero_eq_of_isPreconnected`: it is constant over a preconnected set of
  parameters at which all zeros in `K` are nondegenerate.
* `TauCeti.exists_tendsto_inter_preimage_singleton_eq_singleton_of_tendstoContDiffAt`: a
  nondegenerate solution persists, uniquely near the original solution, and converges to it
  along `l`.
* `TauCeti.exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt`: the solutions in a
  compact set persist as a whole.
* `TauCeti.eventually_ncard_inter_preimage_singleton_eq_of_tendstoContDiffAt`: the number of
  solutions in a compact set is eventually constant.

## References

* V. Guillemin and A. Pollack, *Differential topology*, Prentice-Hall, 1974, Chapter 1, §6
  (stability of transversality) and Chapter 2, §4 (intersection numbers mod 2 are invariant under
  homotopy).
* J. Milnor, *Topology from the differentiable viewpoint*, University Press of Virginia, 1965,
  §1 (the number of preimages of a regular value is locally constant).
* K. Cieliebak and K. Mohnke, *Symplectic hypersurfaces and transversality in Gromov–Witten
  theory*, J. Symplectic Geom. 5 (2007), 281–356, Section 6 (stabilization of domains by
  transverse preimages of a hypersurface).
-/

public section

section SmallPerturbations

open Filter Metric Set
open scoped NNReal Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {K : Set E}

namespace TauCeti

/-- **Persistence of a nondegenerate zero under `C¹`-small perturbations.**

Let `fderiv 𝕜 f` be continuous and invertible at `z`. For every sufficiently small radius `r`
there is `δ > 0` with the following property. If `g` is differentiable on the closed ball of
radius `r` around `z`, `‖g z‖ ≤ δ`, and the derivatives of `g` and `f` differ by at most `δ` on
that ball, then `g` has a zero `a` in the ball, it is the only one there, the derivative of
`g` at `a` is invertible, and `a` lies within `C * ‖g z‖` of `z`, for a constant `C` depending only
on `f` and `z`. The map `f` need not vanish at `z`.

For `f := fderiv ℝ h` this gives the persistence of nondegenerate critical points,
`TauCeti.IsNondegenerateCriticalPoint.exists_criticalPoint_perturbation`. -/
theorem exists_zero_perturbation {z : E} (hc : ContinuousAt (fderiv 𝕜 f) z)
    (hz : (fderiv 𝕜 f z).IsInvertible) :
    ∃ C : ℝ, ∀ᶠ r in 𝓝[>] 0, ∃ δ > 0, ∀ g : E → F,
      (∀ y ∈ closedBall z r, DifferentiableAt 𝕜 g y) →
      ‖g z‖ ≤ δ → (∀ y ∈ closedBall z r, ‖fderiv 𝕜 g y - fderiv 𝕜 f y‖ ≤ δ) →
      ∃ a ∈ closedBall z r, g a = 0 ∧ (fderiv 𝕜 g a).IsInvertible ∧ dist a z ≤ C * ‖g z‖ ∧
        ∀ y ∈ closedBall z r, g y = 0 → y = a := by
  -- On a small ball, `g` approximates the invertible derivative `L` of `f` at `z`, so it has a
  -- unique zero there by `ApproximatesLinearOn.exists_eq_zero_of_two_mul_norm_le`.
  -- The mean value inequality on the ball uses the underlying real structure of `E`.
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  obtain ⟨L, hL⟩ := hz
  -- `C` bounds the inverse of `L` and is positive even on the zero space.
  let C : ℝ := ‖(L.symm : F →L[𝕜] E)‖ + 1
  have hC : 0 < C := by positivity
  have hLsymm : ‖(L.symm : F →L[𝕜] E)‖ ≤ C := le_add_of_nonneg_right zero_le_one
  -- `κ` is the admissible distance from `L` on the ball.
  let κ : ℝ := (2 * C)⁻¹
  have hκ : 0 < κ := by positivity
  have hκC : 2 * C * κ ≤ 1 := (mul_inv_cancel₀ (by positivity)).le
  obtain ⟨ρ, hρ, hρf⟩ := Metric.eventually_nhds_iff.1
    (hc.eventually_mem (Metric.ball_mem_nhds (fderiv 𝕜 f z) (half_pos hκ)))
  refine ⟨2 * C, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hρ] with r hr
  refine ⟨min (κ / 2) (r / (2 * C)), by have := hr.1; positivity, fun g hg hgz hgf ↦ ?_⟩
  have hclose : ∀ y ∈ closedBall z r, ‖fderiv 𝕜 g y - (L : E →L[𝕜] F)‖ ≤ κ := fun y hy ↦ by
    have hfy : ‖fderiv 𝕜 f y - (L : E →L[𝕜] F)‖ < κ / 2 := by
      rw [hL]
      exact mem_ball_iff_norm.1 (hρf (lt_of_le_of_lt (mem_closedBall.1 hy) hr.2))
    calc ‖fderiv 𝕜 g y - (L : E →L[𝕜] F)‖
        ≤ ‖fderiv 𝕜 g y - fderiv 𝕜 f y‖ + ‖fderiv 𝕜 f y - (L : E →L[𝕜] F)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ κ / 2 + κ / 2 := add_le_add ((hgf y hy).trans (min_le_left _ _)) hfy.le
      _ = κ := add_halves _
  have happrox : ApproximatesLinearOn g (L : E →L[𝕜] F) (closedBall z r) ⟨κ, hκ.le⟩ :=
    (convex_closedBall z r).approximatesLinearOn_of_nnnorm_fderiv_sub_le hg fun y hy ↦
      NNReal.coe_le_coe.1 (hclose y hy)
  have hεr : 2 * C * ‖g z‖ ≤ r := by
    have : ‖g z‖ ≤ r / (2 * C) := hgz.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity), mul_comm] at this
  obtain ⟨a, ha, ha0, huniq⟩ := happrox.exists_eq_zero_of_two_mul_norm_le hLsymm hκC hεr
  have haz : a ∈ closedBall z r := closedBall_subset_closedBall hεr ha
  refine ⟨a, haz, ha0, ?_, mem_closedBall.1 ha, huniq⟩
  -- The derivative of `g` at `a` is within `κ = (2 C)⁻¹` of `L`, and `‖L⁻¹‖ ≤ C`.
  have hinv : ‖(L : E →L[𝕜] F).inverse‖ ≤ C := by
    rw [ContinuousLinearMap.inverse_equiv]
    exact hLsymm
  refine ContinuousLinearMap.isInvertible_equiv.of_mul_norm_sub_lt hinv ?_
  calc C * ‖fderiv 𝕜 g a - (L : E →L[𝕜] F)‖ ≤ C * κ := by gcongr; exact hclose a haz
    _ = 1 / 2 := by simp only [κ]; field_simp
    _ < 1 := by norm_num

/-- Around an interior point `z` of `K` at which `fderiv 𝕜 f` is continuous and invertible, small
closed balls lie in the interior of `K` and carry the conclusion of
`TauCeti.exists_zero_perturbation`. -/
private theorem eventually_closedBall_subset_interior_and_zero_perturbation {z : E}
    (hzK : z ∈ interior K) (hc : ContinuousAt (fderiv 𝕜 f) z)
    (hz : (fderiv 𝕜 f z).IsInvertible) :
    ∀ᶠ r in 𝓝[>] 0, closedBall z r ⊆ interior K ∧ ∃ δ > 0, ∀ g : E → F,
      (∀ y ∈ closedBall z r, DifferentiableAt 𝕜 g y) → ‖g z‖ ≤ δ →
      (∀ y ∈ closedBall z r, ‖fderiv 𝕜 g y - fderiv 𝕜 f y‖ ≤ δ) →
      ∃ a ∈ closedBall z r, g a = 0 ∧ (fderiv 𝕜 g a).IsInvertible ∧
        ∀ y ∈ closedBall z r, g y = 0 → y = a := by
  obtain ⟨_, h⟩ := exists_zero_perturbation hc hz
  filter_upwards [(eventually_closedBall_subset (isOpen_interior.mem_nhds hzK)).filter_mono
    nhdsWithin_le_nhds, h] with r hr hpert
  obtain ⟨δ, hδ, hpert⟩ := hpert
  exact ⟨hr, δ, hδ, fun g hg hgz hgf ↦ (hpert g hg hgz hgf).imp fun _ ⟨ha, ha0, hinv, _, hu⟩ ↦
    ⟨ha, ha0, hinv, hu⟩⟩

end TauCeti

namespace IsCompact

omit [IsRCLikeNormedField 𝕜] [CompleteSpace E] in
/-- The zeros of `g` in `K` once each zero `z` of `f` in `K` has a unique zero `a z` of `g` in the
ball of radius `r` around it, these balls lie in the interior of `K` and are pairwise disjoint,
and every zero of `g` in `K` lies in one of them. -/
private theorem nondegenerate_and_exists_equiv_of_closedBall {g : E → F} {r : ℝ}
    (hsep : ∀ z ∈ {x ∈ K | f x = 0}, ∀ z' ∈ {x ∈ K | f x = 0}, z ≠ z' → r + r < dist z z')
    (hball : ∀ z ∈ {x ∈ K | f x = 0}, closedBall z r ⊆ interior K)
    (hloc : ∀ z ∈ {x ∈ K | f x = 0}, ∃ a ∈ closedBall z r, g a = 0 ∧
      (fderiv 𝕜 g a).IsInvertible ∧ ∀ y ∈ closedBall z r, g y = 0 → y = a)
    (hcover : ∀ y ∈ K, g y = 0 → ∃ z ∈ {x ∈ K | f x = 0}, y ∈ closedBall z r) :
    (∀ x ∈ K, g x = 0 → x ∈ interior K ∧ (fderiv 𝕜 g x).IsInvertible) ∧
      ∃ e : {x ∈ K | f x = 0} ≃ {x ∈ K | g x = 0}, ∀ x, dist (e x : E) x ≤ r := by
  choose! a ha ha0 hainv huniq using hloc
  refine ⟨fun y hy hy0 ↦ ?_, ?_⟩
  · obtain ⟨z, hz, hyz⟩ := hcover y hy hy0
    rw [huniq z hz y hyz hy0]
    exact ⟨hball z hz (ha z hz), hainv z hz⟩
  -- The balls are disjoint, so `z ↦ a z` is injective; it is onto by `hcover`.
  have hmem (z : {x ∈ K | f x = 0}) : a z ∈ {x ∈ K | g x = 0} :=
    ⟨interior_subset (hball z z.property (ha z z.property)), ha0 z z.property⟩
  refine ⟨Equiv.ofBijective (fun z ↦ ⟨a z, hmem z⟩) ⟨fun z z' hzz' ↦ ?_, fun y ↦ ?_⟩,
    fun z ↦ mem_closedBall.1 (ha z z.property)⟩
  · by_contra hne
    exact (closedBall_disjoint_closedBall
      (hsep z z.property z' z'.property (Subtype.coe_ne_coe.2 hne))).ne_of_mem
      (ha z z.property) (ha z' z'.property) (congrArg Subtype.val hzz')
  · obtain ⟨hyK, hy0⟩ := y.property
    obtain ⟨z, hz, hyz⟩ := hcover y hyK hy0
    exact ⟨⟨z, hz⟩, Subtype.ext (huniq z hz y hyz hy0).symm⟩

/-- **Nondegenerate zeros persist, in bijection, under `C¹`-small perturbations.**

Let `f` be continuous on the compact set `K`, and let every zero of `f` in `K` be an interior point
of `K` at which the derivative of `f` is continuous and invertible. Then for every `ε > 0` there
is `δ > 0` such that every `g` differentiable on `K` with `‖g x - f x‖ ≤ δ` and
`‖fderiv 𝕜 g x - fderiv 𝕜 f x‖ ≤ δ` on `K` again has only zeros in the interior of `K` at which
the derivative of `g` is invertible, and there is a bijection between the zeros of `f` and those
of `g` in `K` moving each zero by at most `ε`. -/
theorem exists_pos_forall_exists_equiv_sep_eq_zero (hK : IsCompact K) (hf : ContinuousOn f K)
    (hz : ∀ x ∈ K, f x = 0 →
      x ∈ interior K ∧ ContinuousAt (fderiv 𝕜 f) x ∧ (fderiv 𝕜 f x).IsInvertible)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ g : E → F, (∀ x ∈ K, DifferentiableAt 𝕜 g x) → (∀ x ∈ K, ‖g x - f x‖ ≤ δ) →
      (∀ x ∈ K, ‖fderiv 𝕜 g x - fderiv 𝕜 f x‖ ≤ δ) →
      (∀ x ∈ K, g x = 0 → x ∈ interior K ∧ (fderiv 𝕜 g x).IsInvertible) ∧
      ∃ e : {x ∈ K | f x = 0} ≃ {x ∈ K | g x = 0}, ∀ x, dist (e x : E) x ≤ ε := by
  set Z := {x ∈ K | f x = 0}
  have hZ : Z.Finite :=
    hK.finite_inter_preimage_of_isInvertible_fderiv (y := 0) hf fun x hx ↦ (hz x hx.1 hx.2).2.2
  -- One radius `r < ε` for which the balls of radius `r` around the zeros of `f` are pairwise
  -- disjoint, lie in the interior of `K` and carry the local perturbation statement.
  have hsep (p) (_ : p ∈ Z ×ˢ Z) : ∀ᶠ r in 𝓝[>] (0 : ℝ), p.1 ≠ p.2 → r + r < dist p.1 p.2 := by
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h ↦ absurd hp h
    · have h0 : Tendsto (fun r : ℝ ↦ r + r) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).add tendsto_id
      exact ((h0.eventually (eventually_lt_nhds (dist_pos.2 hp))).filter_mono
        nhdsWithin_le_nhds).mono fun _ h _ ↦ h
  obtain ⟨r, ⟨hrZ, hrsep⟩, hr⟩ := ((hZ.eventually_all.2 fun z hzZ ↦
      TauCeti.eventually_closedBall_subset_interior_and_zero_perturbation (hz z hzZ.1 hzZ.2).1
        (hz z hzZ.1 hzZ.2).2.1 (hz z hzZ.1 hzZ.2).2.2).and
      ((hZ.prod hZ).eventually_all.2 hsep)).and (Ioo_mem_nhdsGT hε) |>.exists
  choose! δ hδ hpert using fun z hz ↦ (hrZ z hz).2
  -- Off the balls, `‖f‖` is bounded below by some `m > 0`.
  set K' := K \ ⋃ z ∈ Z, ball z r
  obtain ⟨m, hm, hmf⟩ := (hK.diff (isOpen_biUnion fun _ _ ↦ isOpen_ball)).exists_forall_le'
    (hf.norm.mono sdiff_subset) (a := 0) fun x (hx : x ∈ K') ↦ norm_pos_iff.2 fun h0 ↦
      hx.2 (mem_biUnion (x := x) ⟨hx.1, h0⟩ (mem_ball_self hr.1))
  -- A common `δ` below `m` and below the radius-`r` thresholds of all zeros of `f`.
  have hev : ∀ᶠ δ₀ in 𝓝[>] (0 : ℝ), (δ₀ < m ∧ ∀ z ∈ Z, δ₀ < δ z) ∧ δ₀ ∈ Ioi 0 :=
    ((((eventually_lt_nhds hm).and (hZ.eventually_all.2 fun z hz ↦
      eventually_lt_nhds (hδ z hz))).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  obtain ⟨δ₀, ⟨hδm, hδZ⟩, hδ₀⟩ := hev.exists
  refine ⟨δ₀, hδ₀, fun g hg hgf hgf' ↦ ?_⟩
  -- Each zero `z` of `f` has a unique zero of `g` in its ball.
  have hloc (z) (hz : z ∈ Z) : ∃ a ∈ closedBall z r, g a = 0 ∧ (fderiv 𝕜 g a).IsInvertible ∧
      ∀ y ∈ closedBall z r, g y = 0 → y = a := by
    have hsub : closedBall z r ⊆ K := (hrZ z hz).1.trans interior_subset
    refine hpert z hz g (fun y hy ↦ hg y (hsub hy)) ?_
      (fun y hy ↦ (hgf' y (hsub hy)).trans (hδZ z hz).le)
    simpa [hz.2] using (hgf z hz.1).trans (hδZ z hz).le
  -- Every zero of `g` in `K` lies in one of the balls, since `‖f‖ ≥ m > δ₀` off them.
  have hcover (y) (hy : y ∈ K) (hy0 : g y = 0) : ∃ z ∈ Z, y ∈ closedBall z r := by
    by_contra! hcon
    have hyK' : y ∈ K' := ⟨hy, by
      simp only [mem_iUnion, not_exists]
      exact fun z hz hyz ↦ hcon z hz (ball_subset_closedBall hyz)⟩
    have hfy : ‖f y‖ ≤ δ₀ := by simpa [hy0] using hgf y hy
    linarith [hmf y hyK']
  obtain ⟨hnd, e, he⟩ := nondegenerate_and_exists_equiv_of_closedBall
    (fun z hz z' hz' hne ↦ hrsep (z, z') ⟨hz, hz'⟩ hne) (fun z hz ↦ (hrZ z hz).1) hloc hcover
  exact ⟨hnd, e, fun x ↦ (he x).trans hr.2.le⟩

/-- **The number of nondegenerate zeros is stable under `C¹`-small perturbations.** Under the
hypotheses of `IsCompact.exists_pos_forall_exists_equiv_sep_eq_zero`, every `g` differentiable on
`K` and `δ`-close to `f` in `C¹` on `K`, for a suitable `δ > 0`, has as many zeros in `K` as
`f`. -/
theorem exists_pos_forall_ncard_sep_eq_zero_eq (hK : IsCompact K) (hf : ContinuousOn f K)
    (hz : ∀ x ∈ K, f x = 0 →
      x ∈ interior K ∧ ContinuousAt (fderiv 𝕜 f) x ∧ (fderiv 𝕜 f x).IsInvertible) :
    ∃ δ > 0, ∀ g : E → F, (∀ x ∈ K, DifferentiableAt 𝕜 g x) → (∀ x ∈ K, ‖g x - f x‖ ≤ δ) →
      (∀ x ∈ K, ‖fderiv 𝕜 g x - fderiv 𝕜 f x‖ ≤ δ) →
      {x ∈ K | g x = 0}.ncard = {x ∈ K | f x = 0}.ncard := by
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_exists_equiv_sep_eq_zero hf hz one_pos
  refine ⟨δ, hδ, fun g hg hgf hgf' ↦ ?_⟩
  obtain ⟨-, e, -⟩ := h g hg hgf hgf'
  exact (Set.ncard_congr' e).symm

variable {P : Type*} [TopologicalSpace P] {u : P → E → F} {s : Set P}

/-- **The number of nondegenerate zeros is locally constant along a continuous family.** Let
`u p` be differentiable on the compact set `K` for every parameter `p ∈ s`, with `u p x` and
`fderiv 𝕜 (u p) x` continuous in `(p, x)` on `s ×ˢ K`. If every zero of `u p₀` in `K` is an
interior point of `K` at which the derivative of `u p₀` is invertible, then for `p ∈ s` near `p₀`
the map `u p` has as many zeros in `K` as `u p₀`. -/
theorem eventually_ncard_sep_eq_zero_eq (hK : IsCompact K)
    (hd : ∀ p ∈ s, ∀ x ∈ K, DifferentiableAt 𝕜 (u p) x)
    (hu : ContinuousOn (Function.uncurry u) (s ×ˢ K))
    (hu' : ContinuousOn (fun q : P × E ↦ fderiv 𝕜 (u q.1) q.2) (s ×ˢ K)) {p₀ : P}
    (hp₀ : p₀ ∈ s)
    (hz : ∀ x ∈ K, u p₀ x = 0 → x ∈ interior K ∧ (fderiv 𝕜 (u p₀) x).IsInvertible) :
    ∀ᶠ p in 𝓝[s] p₀, {x ∈ K | u p x = 0}.ncard = {x ∈ K | u p₀ x = 0}.ncard := by
  have hslice : MapsTo (fun x ↦ (p₀, x)) K (s ×ˢ K) := fun x hx ↦ ⟨hp₀, hx⟩
  have hc : ContinuousOn (fderiv 𝕜 (u p₀)) K :=
    hu'.comp (continuousOn_const.prodMk continuousOn_id) hslice
  obtain ⟨δ, hδ, h⟩ := hK.exists_pos_forall_ncard_sep_eq_zero_eq
    (hu.comp (continuousOn_const.prodMk continuousOn_id) hslice) fun x hx hx0 ↦
      ⟨(hz x hx hx0).1, hc.continuousAt (mem_interior_iff_mem_nhds.1 (hz x hx hx0).1),
        (hz x hx hx0).2⟩
  -- The pair `(u p x, fderiv 𝕜 (u p) x)` is uniformly close to its value at `p₀` over `K`.
  obtain ⟨v, hv, hvK⟩ := hK.mem_uniformity_of_prod
    (f := fun p x ↦ (u p x, fderiv 𝕜 (u p) x)) (hu.prodMk hu') hp₀ (dist_mem_uniformity hδ)
  filter_upwards [hv, self_mem_nhdsWithin] with p hp hps
  have hpx (x) (hx : x ∈ K) :
      max ‖u p x - u p₀ x‖ ‖fderiv 𝕜 (u p) x - fderiv 𝕜 (u p₀) x‖ < δ := by
    have hpx : dist (u p x, fderiv 𝕜 (u p) x) (u p₀ x, fderiv 𝕜 (u p₀) x) < δ := hvK p hp x hx
    rwa [Prod.dist_eq, dist_eq_norm, dist_eq_norm] at hpx
  exact h (u p) (hd p hps) (fun x hx ↦ (le_max_left _ _).trans (hpx x hx).le)
    fun x hx ↦ (le_max_right _ _).trans (hpx x hx).le

/-- **The number of nondegenerate zeros is constant along a connected family.** Let `u p` be
differentiable on the compact set `K` for every parameter `p` in a preconnected set `s`, with
`u p x` and `fderiv 𝕜 (u p) x` continuous in `(p, x)` on `s ×ˢ K`. If for every `p ∈ s` every zero
of `u p` in `K` is an interior point of `K` at which the derivative of `u p` is invertible, then
all `u p`, `p ∈ s`, have the same number of zeros in `K`. -/
theorem ncard_sep_eq_zero_eq_of_isPreconnected (hK : IsCompact K) (hs : IsPreconnected s)
    (hd : ∀ p ∈ s, ∀ x ∈ K, DifferentiableAt 𝕜 (u p) x)
    (hu : ContinuousOn (Function.uncurry u) (s ×ˢ K))
    (hu' : ContinuousOn (fun q : P × E ↦ fderiv 𝕜 (u q.1) q.2) (s ×ˢ K))
    (hz : ∀ p ∈ s, ∀ x ∈ K, u p x = 0 → x ∈ interior K ∧ (fderiv 𝕜 (u p) x).IsInvertible)
    {p q : P} (hp : p ∈ s) (hq : q ∈ s) :
    {x ∈ K | u p x = 0}.ncard = {x ∈ K | u q x = 0}.ncard :=
  hs.constant (f := fun p ↦ {x ∈ K | u p x = 0}.ncard) (fun p₀ hp₀ ↦ by
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    exact hK.eventually_ncard_sep_eq_zero_eq hd hu hu' hp₀ (hz p₀ hp₀)) hp hq

end IsCompact

end SmallPerturbations

section ConvergingFamilies

open Set Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} {l : Filter ι} {Φ : ι → E → F} {Φ₀ : E → F} {s K : Set E} {y : F}

/-- **Persistence of a nondegenerate solution.** Let `Φ i → Φ₀` in `C¹` at every point of an open
set `s`, with the maps `Φ i` eventually `C¹` on `s`, and let `x₀ ∈ s` be a solution of
`Φ₀ x₀ = y` at which `D Φ₀ (x₀)` is invertible. Then there is an open neighbourhood `U ⊆ s` of `x₀`
in which `x₀` is the only solution of `Φ₀ x = y`, and points `z i` converging to `x₀` along `l`
such that eventually along `l` the point `z i` is the only solution of `Φ i x = y` in `U`, and
`D Φ i (z i)` is invertible. -/
theorem exists_tendsto_inter_preimage_singleton_eq_singleton_of_tendstoContDiffAt {x₀ : E}
    (hs : IsOpen s) (hx₀ : x₀ ∈ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hy : Φ₀ x₀ = y) (hinv : (fderiv 𝕜 Φ₀ x₀).IsInvertible) :
    ∃ U, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ s ∧ U ∩ Φ₀ ⁻¹' {y} = {x₀} ∧
      ∃ z : ι → E, Tendsto z l (𝓝 x₀) ∧
        ∀ᶠ i in l, U ∩ Φ i ⁻¹' {y} = {z i} ∧ (fderiv 𝕜 (Φ i) (z i)).IsInvertible := by
  obtain ⟨e₀, e, T, -, hT, he₀, hx₀e, hes, hTe, -, hev, hsymm⟩ :=
    exists_openPartialHomeomorph_tendstoContDiffAt_symm hs hx₀ le_rfl hΦ hΦ₀ hconv hinv
  rw [hy] at hT
  have hsymm₀ : e₀.symm y = x₀ := by rw [← hy, ← he₀, e₀.left_inv hx₀e]
  refine ⟨e₀.source, e₀.open_source, hx₀e, hes, ?_, fun i ↦ (e i).symm y, ?_, ?_⟩
  · -- `Φ₀ = e₀` is injective on its source.
    refine eq_singleton_iff_unique_mem.2 ⟨⟨hx₀e, hy⟩, fun x ⟨hx, hxy⟩ ↦ ?_⟩
    refine e₀.injOn hx hx₀e ?_
    simp only [he₀, mem_preimage, mem_singleton_iff] at hxy ⊢
    rw [hxy, hy]
  · -- The inverses converge continuously at `y`.
    have h := (hsymm y hT).tendsto.comp (tendsto_id.prodMk (tendsto_const_nhds (x := y)))
    rwa [hsymm₀] at h
  · filter_upwards [hev, hΦ] with i ⟨hei, hsrc, hT', hsymmc⟩ hΦi
    have hyT : y ∈ (e i).target := hT' hT
    have hz : (e i).symm y ∈ (e i).source := (e i).map_target hyT
    have hzU : (e i).symm y ∈ e₀.source := hsrc ▸ hz
    have hΦz : Φ i ((e i).symm y) = y := by rw [← hei, (e i).right_inv hyT]
    refine ⟨eq_singleton_iff_unique_mem.2 ⟨⟨hzU, hΦz⟩, fun x ⟨hx, hxy⟩ ↦ ?_⟩, ?_⟩
    · -- `Φ i = e i` is injective on the common source.
      refine (e i).injOn (hsrc ▸ hx) hz ?_
      simp only [hei, mem_preimage, mem_singleton_iff] at hxy ⊢
      rw [hxy, hΦz]
    · -- The inverse of `e i` is differentiable at `y`, so the derivative at `z i` is invertible.
      have hd : DifferentiableAt 𝕜 (e i) ((e i).symm y) := by
        rw [hei]
        exact (hΦi.contDiffAt (hs.mem_nhds (hes hzU))).differentiableAt one_ne_zero
      have hds : DifferentiableAt 𝕜 (e i).symm (e i ((e i).symm y)) := by
        rw [(e i).right_inv hyT]
        exact (hsymmc.contDiffAt ((e i).open_target.mem_nhds hyT)).differentiableAt one_ne_zero
      simpa only [hei] using (e i).isInvertible_fderiv hz hd hds

/-- **Persistence of the solutions in a compact set.** Let `Φ i → Φ₀` in `C¹` at every point of an
open set `s`, with the maps `Φ i` eventually `C¹` on `s`, and let `K ⊆ s` be compact. Suppose that
every solution of `Φ₀ x = y` in `K` lies in the interior of `K` and is nondegenerate. Then there are
points `z i x`, converging to `x` along `l` for every solution `x` of `Φ₀ x = y` in `K`, such that
eventually along `l` the map `x ↦ z i x` is a bijection from the solutions of `Φ₀ x = y` in `K`
onto the solutions of `Φ i x = y` in `K`, and `D Φ i` is invertible at each of the latter. -/
theorem exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hint : K ∩ Φ₀ ⁻¹' {y} ⊆ interior K)
    (hinv : ∀ x ∈ K ∩ Φ₀ ⁻¹' {y}, (fderiv 𝕜 Φ₀ x).IsInvertible) :
    ∃ z : ι → E → E, (∀ x ∈ K ∩ Φ₀ ⁻¹' {y}, Tendsto (fun i ↦ z i x) l (𝓝 x)) ∧
      ∀ᶠ i in l, BijOn (z i) (K ∩ Φ₀ ⁻¹' {y}) (K ∩ Φ i ⁻¹' {y}) ∧
        ∀ x ∈ K ∩ Φ i ⁻¹' {y}, (fderiv 𝕜 (Φ i) x).IsInvertible := by
  set Z := K ∩ Φ₀ ⁻¹' {y}
  have hZfin : Z.Finite := hK.finite_inter_preimage_of_isInvertible_fderiv
    (hΦ₀.continuousOn.mono hKs) hinv
  -- Disjoint open neighbourhoods `V x` of the finitely many solutions for `Φ₀`.
  obtain ⟨V, hV, hVdisj⟩ := hZfin.t2_separation
  -- Around each solution, it persists uniquely in a neighbourhood `U x ⊆ V x ∩ interior K`.
  have hloc : ∀ x ∈ Z, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ s ∩ interior K ∩ V x ∧
      ∃ w : ι → E, Tendsto w l (𝓝 x) ∧
        ∀ᶠ i in l, U ∩ Φ i ⁻¹' {y} = {w i} ∧ (fderiv 𝕜 (Φ i) (w i)).IsInvertible := by
    intro x hx
    have hs' : IsOpen (s ∩ interior K ∩ V x) := (hs.inter isOpen_interior).inter (hV x).2
    have hxs' : x ∈ s ∩ interior K ∩ V x := ⟨⟨hKs hx.1, hint hx⟩, (hV x).1⟩
    obtain ⟨U, hU, hxU, hUs, -, w, hw, hev⟩ :=
      exists_tendsto_inter_preimage_singleton_eq_singleton_of_tendstoContDiffAt hs' hxs'
        (hΦ.mono fun i hi ↦ hi.mono fun y hy ↦ hy.1.1) (hΦ₀.mono fun y hy ↦ hy.1.1)
        (fun y hy ↦ hconv y hy.1.1) hx.2 (hinv x hx)
    exact ⟨U, hU, hxU, hUs, w, hw, hev⟩
  choose! U hU hxU hUs w hw hev using hloc
  -- Off the neighbourhoods `U x`, the maps `Φ i` eventually do not take the value `y` on `K`.
  have haway : ∀ᶠ i in l, ∀ a ∈ K \ ⋃ x ∈ Z, U x, Φ i a ∈ ({y}ᶜ : Set F) :=
    (hK.diff (isOpen_biUnion fun x hx ↦ hU x hx)).eventually_forall_mem_of_tendsto_prod_nhds
      isOpen_compl_singleton (fun a ha ↦ (hconv a (hKs ha.1)).tendsto)
      fun a ha hay ↦ ha.2 (mem_biUnion ⟨ha.1, hay⟩ (hxU a ⟨ha.1, hay⟩))
  refine ⟨fun i x ↦ w x i, fun x hx ↦ hw x hx, ?_⟩
  filter_upwards [haway, (hZfin.eventually_all (p := fun x i ↦ U x ∩ Φ i ⁻¹' {y} = {w x i} ∧
    (fderiv 𝕜 (Φ i) (w x i)).IsInvertible)).2 hev] with i hi hall
  -- The solution `w x i` of `Φ i x = y` is the only one in `U x`.
  have hmem (x : E) (hx : x ∈ Z) : w x i ∈ U x ∩ Φ i ⁻¹' {y} := by
    rw [(hall x hx).1]
    exact mem_singleton _
  -- Every solution of `Φ i x = y` in `K` lies in some `U x`, hence is some `w x i`.
  have hsurj : ∀ y' ∈ K ∩ Φ i ⁻¹' {y}, ∃ x ∈ Z, w x i = y' := fun y' ⟨hyK, hyy⟩ ↦ by
    by_contra hne
    simp only [not_exists, not_and] at hne
    refine hi y' ⟨hyK, fun hyU ↦ ?_⟩ hyy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
    have h : y' ∈ U x ∩ Φ i ⁻¹' {y} := ⟨hyx, hyy⟩
    rw [(hall x hx).1] at h
    exact hne x hx h.symm
  refine ⟨⟨fun x hx ↦ ⟨interior_subset (hUs x hx (hmem x hx).1).1.2, (hmem x hx).2⟩,
    fun x hx x' hx' hxx' ↦ ?_, hsurj⟩, fun y' hy' ↦ ?_⟩
  · -- Distinct solutions for `Φ₀` have disjoint neighbourhoods `V x`.
    by_contra hne
    exact (hVdisj hx hx' hne).ne_of_mem ((hUs x hx (hmem x hx).1).2)
      ((hUs x' hx' (hmem x' hx').1).2) hxx'
  · obtain ⟨x, hx, rfl⟩ := hsurj y' hy'
    exact (hall x hx).2

/-- **The number of solutions in a compact set is eventually constant.** Under the hypotheses of
`TauCeti.exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt`, eventually along `l`
the equation `Φ i x = y` has as many solutions in `K` as `Φ₀ x = y`. -/
theorem eventually_ncard_inter_preimage_singleton_eq_of_tendstoContDiffAt (hs : IsOpen s)
    (hK : IsCompact K) (hKs : K ⊆ s) (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 1 (Φ i) s)
    (hΦ₀ : ContDiffOn 𝕜 1 Φ₀ s) (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 1 Φ Φ₀ l x)
    (hint : K ∩ Φ₀ ⁻¹' {y} ⊆ interior K)
    (hinv : ∀ x ∈ K ∩ Φ₀ ⁻¹' {y}, (fderiv 𝕜 Φ₀ x).IsInvertible) :
    ∀ᶠ i in l, (K ∩ Φ i ⁻¹' {y}).ncard = (K ∩ Φ₀ ⁻¹' {y}).ncard := by
  obtain ⟨z, -, hev⟩ := exists_tendsto_bijOn_inter_preimage_singleton_of_tendstoContDiffAt
    hs hK hKs hΦ hΦ₀ hconv hint hinv
  filter_upwards [hev] with i hi
  rw [← hi.1.image_eq, hi.1.injOn.ncard_image]

end TauCeti

end ConvergingFamilies
