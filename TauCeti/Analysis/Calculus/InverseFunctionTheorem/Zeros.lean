/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.UniformSpace.HeineCantor
public import TauCeti.Analysis.Calculus.ApproximatesLinearOn
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Persistence and count of nondegenerate zeros under `C¹`-small perturbations

Let `f : E → F` be a map between Banach spaces and `K ⊆ E` compact. Call a zero `x` of `f` in `K`
*nondegenerate* if `x` is an interior point of `K` and the derivative of `f` at `x` is invertible.
If every zero of a map continuous on `K` has invertible derivative, there are only finitely many
zeros in `K` (`IsCompact.finite_sep_eq_zero_of_isInvertible_fderiv`). If `f` is continuous on
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

## References

* V. Guillemin and A. Pollack, *Differential topology*, Prentice-Hall, 1974, Chapter 1, §6
  (stability of transversality) and Chapter 2, §4 (intersection numbers mod 2 are invariant under
  homotopy).
* J. Milnor, *Topology from the differentiable viewpoint*, University Press of Virginia, 1965,
  §1 (the number of preimages of a regular value is locally constant).
-/

public section

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

The argument was first written in Tau Ceti for critical points, in
`TauCeti.IsNondegenerateCriticalPoint.exists_criticalPoint_perturbation`; here `fderiv ℝ g` is
replaced by `g`, and that theorem is derived from this one. -/
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
`‖fderiv 𝕜 g x - fderiv 𝕜 f x‖ ≤ δ` on `K` again has only such zeros in `K`, and there is a
bijection between the zeros of `f` and those of `g` in `K` moving each zero by at most `ε`. -/
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
    hK.finite_sep_eq_zero_of_isInvertible_fderiv hf fun x hx hx0 ↦ (hz x hx hx0).2.2
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
