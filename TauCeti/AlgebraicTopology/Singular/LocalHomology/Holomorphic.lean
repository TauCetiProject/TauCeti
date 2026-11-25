/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.Homotopy.Affine
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.Sard.EqualDimension
import TauCeti.Analysis.Complex.IsolatedZero
import TauCeti.Analysis.Normed.Module.Ball.Radial.ProperExtension
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.LinearIndependent.Prod
import TauCeti.LinearAlgebra.LinearMap.Coprod
import TauCeti.Topology.Maps.Proper.Metric

/-!
# Local indices of holomorphic maps are positive

Let `E` be a finite-dimensional complex normed space, regarded as a real manifold modelled on
itself and oriented by a homological orientation `o` (`TauCeti.HomologicalOrientation`), used on
both the source and the target of a continuous map `f : E → E`. If `f` is holomorphic near a point
`x` which is isolated in its fibre `f⁻¹(f x)`, then the topological local index of `f` at `x`
(`TauCeti.HomologicalOrientation.localIndex`) is positive
(`TauCeti.HomologicalOrientation.localIndex_pos_of_analyticAt`). Since a point which is not isolated
in its fibre has local index `0` by convention, the local index of a holomorphic map is always
nonnegative, and it is positive exactly at the isolated points of the fibres
(`TauCeti.HomologicalOrientation.localIndex_pos_iff_eventually_ne_of_analyticAt`). For maps of one
variable this is `TauCeti.HomologicalOrientation.localIndex_pos_iff_of_analyticAt` of
`TauCeti.Analysis.Complex.Conformal.LocalIndex`, where the index is the order of vanishing.

Positivity is the source of the positivity of intersections of holomorphic curves. Two holomorphic
discs `u₁, u₂ : ℂ → ℂ²` meeting at an isolated point `u₁ z₀ = u₂ w₀` have, as local intersection
number, the local index of `(z, w) ↦ u₁ z - u₂ w` at `(z₀, w₀)`, and it is positive
(`TauCeti.HomologicalOrientation.localIndex_pos_of_apply_eq_sub`). This is the model case,
for the standard complex structure of `ℂ²`, of the local intersection multiplicities of distinct
branches of pseudoholomorphic curves in a four-manifold.

The same positivity of real Jacobians shows that local indices do not change under changes of
coordinates whose derivative at the point is complex linear and injective: on the target, for the
difference `a - b` of two maps
(`TauCeti.HomologicalOrientation.localIndex_eq_of_apply_eq_sub_of_hasStrictFDerivAt`), and on the
source (`TauCeti.HomologicalOrientation.localIndex_comp_eq_of_hasStrictFDerivAt`). These are the
specializations of the real statements
`TauCeti.HomologicalOrientation.localIndex_eq_sign_det_mul_of_apply_eq_sub` and
`TauCeti.HomologicalOrientation.localIndex_comp_eq_mul_sign_det`. The target changes include the
unitary maps and the holomorphic changes of coordinates, which preserve the standard complex
structure. A `C¹` chart whose derivative at the intersection point carries a different complex
structure there to the standard one has a derivative that is not complex linear for the standard
structure; such charts fall under the real statement
`TauCeti.HomologicalOrientation.localIndex_eq_sign_det_mul_of_apply_eq_sub`, once the sign of its
real Jacobian determinant is known.

## Proof

A complex-linear map has real determinant `|det_ℂ|²` (`LinearMap.det_restrictScalars_eq_normSq`),
so at a point where the complex derivative is invertible the local index, the sign of the real
Jacobian, is `1` (`TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasFDerivAt`). Hence the
degree of a proper map is the number of preimages of a value all of whose preimages are such
regular points (`TauCeti.HomologicalOrientation.degree_eq_ncard_of_hasFDerivAt`), and the local
index at an isolated point is the number of solutions in a small ball of `f z = y` for nearby such
values `y` (`TauCeti.HomologicalOrientation.localIndex_eq_ncard_of_hasFDerivAt`).

This alone does not give positivity, since the derivative of `f` may be singular everywhere near
`x`, in which case no value near `f x` has a regular preimage. The proof perturbs `f`. Choose a
closed ball `B` about `x` whose only solution of `f z = f x` is `x`, and replace `f` by a proper map
`g` agreeing with it on `B` and staying at distance at least `δ > 0` from `f x` outside the interior
of `B` (`ContinuousOn.exists_isProperMap_eqOn_closedBall_and_le_norm_sub`); the local index of `f`
at `x` is the degree of `g`. For a small `ε > 0` such that `-ε` is not an eigenvalue of `Df(x)`, the
map `G z = g z + ε ρ(z - x)`, with `ρ` the radial retraction onto the ball of radius `r` of `B`, is
`f + ε (· - x)` on `B` and moves `g` by at most `ε r < δ`. So the straight homotopy from `g` to `G`
never takes the value `f x` outside `B`, and `g` and `G` have the same degree. Now `G` has the
invertible derivative `Df(x) + ε` at `x`, hence local index `1` there, so `G` maps the interior of
`B` onto a neighbourhood of `f x`; by the equal-dimensional Sard theorem
(`TauCeti.dense_setOf_forall_surjective_fderiv`) this neighbourhood contains a value all of whose
preimages are regular, and it has at least one. So the degree of `G` is a positive number of
preimages.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasFDerivAt`: at a point with invertible
  complex derivative the local index is `1`.
* `TauCeti.HomologicalOrientation.localIndex_eq_of_apply_eq_sub_of_hasStrictFDerivAt`,
  `TauCeti.HomologicalOrientation.localIndex_comp_eq_of_hasStrictFDerivAt`: local indices are
  invariant under changes of coordinates of the target and of the source with complex-linear
  derivative.
* `TauCeti.HomologicalOrientation.degree_eq_ncard_of_hasFDerivAt`: the degree of a proper map is the
  number of preimages of a value whose preimages have invertible complex derivatives.
* `TauCeti.HomologicalOrientation.localIndex_eq_ncard_of_hasFDerivAt`: the local index counts the
  solutions in a small ball of `f z = y` for such values `y` near `f x`.
* `TauCeti.HomologicalOrientation.localIndex_pos_of_analyticAt`: **the local index of a holomorphic
  map at an isolated point of its fibre is positive.**
* `TauCeti.HomologicalOrientation.localIndex_pos_iff_eventually_ne_of_analyticAt`,
  `TauCeti.HomologicalOrientation.localIndex_nonneg_of_analyticAt`: positivity exactly at isolated
  points, and nonnegativity everywhere.
* `TauCeti.HomologicalOrientation.localIndex_pos_of_apply_eq_sub`: **positivity of the local
  intersection numbers of holomorphic discs in `ℂ²`**;
  `TauCeti.HomologicalOrientation.localIndex_eq_one_of_apply_eq_sub`: a transverse intersection
  counts `1`.

The examples at the end of the file compute the local intersection numbers of the line `w = 0`
with the lines `z = 0` and `w = z` (both `1`) and with itself (there is no isolated intersection,
and the index is `0`). Tangent and critical intersections, such as that of the line `w = 0` with the
parabola `w = z²`, are computed by orders of vanishing in
`TauCeti.AlgebraicTopology.Singular.LocalHomology.GraphIntersection`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix E (local intersection numbers and their positivity).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages of a regular value).
-/

public section

noncomputable section

open Filter Metric Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

section Real

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Inside any neighbourhood `U` of an isolated point `x` of `f⁻¹(f x)`, there is a closed ball
about `x` contained in `U` whose only solution of `f z = f x` is `x`, and a positive lower bound
for `‖f - f x‖` on its boundary sphere. -/
private theorem exists_closedBall_subset_and_le_norm_sub {f : C(E, E)} {x : E} {U : Set E}
    (hU : U ∈ 𝓝 x) (hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x) :
    ∃ r > 0, ∃ δ > 0, closedBall x r ⊆ U ∧ (∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖) ∧
      (∀ z ∈ closedBall x r, f z = f x → z = x) := by
  obtain ⟨R, hR, hRU⟩ := Metric.eventually_nhds_iff_ball.1
    (Filter.Eventually.and hU (eventually_nhdsWithin_iff.1 hiso))
  have hr : 0 < R / 2 := half_pos hR
  have hrR : closedBall x (R / 2) ⊆ ball x R := closedBall_subset_ball (half_lt_self hR)
  have hiso' (z : E) (hz : z ∈ closedBall x (R / 2)) (hfz : f z = f x) : z = x :=
    by_contra fun hzx ↦ (hRU z (hrR hz)).2 hzx hfz
  obtain ⟨δ, hδ, hfδ⟩ := exists_pos_le_norm_of_mem_sphere
    (f.continuous.continuousOn.sub continuousOn_const) fun z hz ↦ sub_ne_zero.2 fun h ↦
      ne_of_mem_sphere hz hr.ne' (hiso' z (sphere_subset_closedBall hz) h)
  exact ⟨R / 2, hr, δ, hδ, fun z hz ↦ (hRU z (hrR hz)).1, hfδ, hiso'⟩

variable {n : ℕ} (o : HomologicalOrientation E E n)

/-- If `x` is the only solution of `f z = f x` in the ball of radius `r` about `x`, and `f` stays
at distance at least `δ > 0` from `f x` on the sphere of radius `r`, then `f` agrees on the closed
ball with a proper map `g` which stays at distance at least `δ` from `f x` outside the open ball,
whose fibre over each value `y` within `δ` of `f x` is the set of solutions of `f z = y` in the
open ball, and the local index of `f` at `x` is the degree of `g`. -/
private theorem exists_isProperMap_eqOn_localIndex_eq_degree (hE : finrank ℝ E = n)
    {f : C(E, E)} {x : E} {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖) (hiso : ∀ z ∈ ball x r, f z = f x → z = x) :
    ∃ g : C(E, E), IsProperMap g ∧ EqOn g f (closedBall x r) ∧
      (∀ z, r ≤ dist z x → δ ≤ ‖g z - f x‖) ∧
      (∀ y, ‖y - f x‖ < δ → g ⁻¹' {y} = {z ∈ ball x r | f z = y}) ∧
      o.localIndex o f x = o.degree o hE g := by
  have hrpos : 0 < r := hr.lt_of_ne' fun h ↦ (hfδ x (by simp [h])).not_gt (by simpa using hδ)
  obtain ⟨g, hgp, hgf, hgout⟩ :=
    f.continuous.continuousOn.exists_isProperMap_eqOn_closedBall_and_le_norm_sub hr hδ hfδ
  -- Outside the open ball `g` stays at distance at least `δ` from `f x`, so its fibre over a value
  -- `y` within `δ` of `f x` is the set of solutions in the open ball.
  have hgfib (y : E) (hy : ‖y - f x‖ < δ) : g ⁻¹' {y} = {z ∈ ball x r | f z = y} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    refine ⟨fun hz ↦ ?_, fun hz ↦ (hgf (ball_subset_closedBall hz.1)).trans hz.2⟩
    have hzb : z ∈ ball x r := mem_ball.2 (not_le.1 fun h ↦ (hgout z h).not_gt (hz ▸ hy))
    exact ⟨hzb, (hgf (ball_subset_closedBall hzb)).symm.trans hz⟩
  refine ⟨g, hgp, hgf, hgout, hgfib, ?_⟩
  -- `x` is the only preimage of `f x` under `g`, so the local index is the degree.
  have hfib₀ : g ⁻¹' {f x} = {x} := by
    rw [hgfib (f x) (by rwa [sub_self, norm_zero])]
    ext z
    simp only [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun hz ↦ hiso z hz.1 hz.2, by rintro rfl; exact ⟨mem_ball_self hrpos, rfl⟩⟩
  have hgf_nhds : g =ᶠ[𝓝 x] f :=
    eventually_of_mem (ball_mem_nhds x hrpos) fun _ hw ↦ hgf (ball_subset_closedBall hw)
  rw [o.localIndex_congr o hE hgf_nhds.symm, ← o.localDegree_eq_localIndex o hE hE g hfib₀,
    o.localDegree_eq_degree o hE hE hgp]

/-- A continuous map `f : E → E` with nonzero local index at `x` carries every neighbourhood of `x`
to a neighbourhood of `f x`. -/
private theorem image_mem_nhds_of_localIndex_ne_zero (hE : finrank ℝ E = n) {f : C(E, E)} {x : E}
    (hf : o.localIndex o f x ≠ 0) {U : Set E} (hU : U ∈ 𝓝 x) : f '' U ∈ 𝓝 (f x) := by
  have hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
    by_contra h
    exact hf (o.localIndex_of_frequently_eq o f (by simpa using not_eventually.1 h))
  obtain ⟨r, hr, δ, hδ, hrU, hfδ, hiso'⟩ := exists_closedBall_subset_and_le_norm_sub hU hiso
  obtain ⟨g, hgp, -, -, hgfib, hidx⟩ := o.exists_isProperMap_eqOn_localIndex_eq_degree hE hr.le hδ
    hfδ fun z hz ↦ hiso' z (ball_subset_closedBall hz)
  refine mem_of_superset (ball_mem_nhds (f x) hδ) fun y hy ↦ ?_
  obtain ⟨z, hz⟩ := o.surjective_of_degree_ne_zero o hE hE hgp (hidx ▸ hf) y
  have hmem : z ∈ g ⁻¹' {y} := hz
  rw [hgfib y (by rwa [← dist_eq_norm])] at hmem
  exact ⟨z, hrU (ball_subset_closedBall hmem.1), hmem.2⟩

/-- The degree of a proper map `f : E → E` counts the preimages of a value all of whose preimages
have positive Jacobian determinant. -/
private theorem degree_eq_ncard_of_det_pos (hE : finrank ℝ E = n) {f : C(E, E)}
    (hf : IsProperMap f) {f' : E → E →L[ℝ] E} {y : E}
    (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hpos : ∀ x ∈ f ⁻¹' {y}, 0 < (f' x).det) :
    o.degree o hE f = (f ⁻¹' {y}).ncard := by
  have h₁ : {x | 0 < (f' x).det} ∩ f ⁻¹' {y} = f ⁻¹' {y} := inter_eq_right.2 hpos
  have h₂ : {x | (f' x).det < 0} ∩ f ⁻¹' {y} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx ↦ (hpos x hx.2).not_gt hx.1
  rw [o.degree_eq_ncard_sub_ncard hE hf hderiv (fun x hx ↦ (hpos x hx).ne'), h₁, h₂,
    ncard_empty, Nat.cast_zero, sub_zero]

/-- A proper map `G : E → E` which is differentiable with nonnegative Jacobian determinant on a set
`U` containing the fibres of all values near `G x`, and has nonzero Jacobian determinant at `x`,
has positive degree. -/
private theorem degree_pos_of_hasFDerivAt (hE : finrank ℝ E = n) {G : C(E, E)}
    (hG : IsProperMap G) {U : Set E} {D : E → E →L[ℝ] E}
    (hGd : ∀ z ∈ U, HasFDerivAt G (D z) z) (hdet : ∀ z ∈ U, 0 ≤ (D z).det) {x : E}
    (hDx : (D x).det ≠ 0) (hfib : ∀ᶠ y in 𝓝 (G x), G ⁻¹' {y} ⊆ U) :
    0 < o.degree o hE G := by
  have hU : U ∈ 𝓝 x := (G.continuous.continuousAt.eventually hfib).mono fun _ hz ↦ hz rfl
  have hidx : o.localIndex o G x ≠ 0 := by
    have hpos : 0 < (D x).det := (hdet x (mem_of_mem_nhds hU)).lt_of_ne' hDx
    rw [o.localIndex_eq_sign_det hE (hGd x (mem_of_mem_nhds hU)) hDx, sign_pos hpos,
      SignType.coe_one]
    exact one_ne_zero
  have hW : G '' U ∩ {y' | G ⁻¹' {y'} ⊆ U} ∈ 𝓝 (G x) :=
    inter_mem (o.image_mem_nhds_of_localIndex_ne_zero hE hidx hU) hfib
  -- By Sard's theorem the regular values of `G` on `U` are dense, so some value in the interior of
  -- this neighbourhood has only regular preimages.
  borelize E
  obtain ⟨y', hy'W, hy'S⟩ := (dense_setOf_forall_surjective_fderiv (s := U) (f := G)
    (fun z hz ↦ (hGd z hz).differentiableAt) rfl).inter_open_nonempty
    (interior (G '' U ∩ {y' | G ⁻¹' {y'} ⊆ U})) isOpen_interior
    ⟨G x, mem_interior_iff_mem_nhds.2 hW⟩
  obtain ⟨⟨z₀, -, hGz₀⟩, hy'U⟩ := interior_subset hy'W
  have hpos {z : E} (hz : z ∈ G ⁻¹' {y'}) : 0 < (D z).det := by
    have hsurj := hy'S z (hy'U hz) hz
    rw [(hGd z (hy'U hz)).fderiv] at hsurj
    have hdetz : (D z).det ≠ 0 := fun h ↦
      LinearMap.det_eq_zero_iff_ker_ne_bot.1 h
        (LinearMap.ker_eq_bot.2 (LinearMap.injective_iff_surjective.2 hsurj))
    exact (hdet z (hy'U hz)).lt_of_ne' hdetz
  have hfin : (G ⁻¹' {y'}).Finite :=
    (hG.isCompact_preimage isCompact_singleton).finite_of_hasFDerivAt
      (fun z hz ↦ hGd z (hy'U hz)) fun z hz ↦
        ⟨_, ((D z).toContinuousLinearEquivOfDetNeZero (hpos hz).ne').antilipschitzWith⟩
  rw [o.degree_eq_ncard_of_det_pos hE hG (f' := D) (y := y')
    (fun z hz ↦ hGd z (hy'U hz)) fun z hz ↦ hpos hz]
  exact_mod_cast (ncard_pos hfin).2 ⟨z₀, hGz₀⟩

/-- Near a point `x` which is the only solution of `f z = f x` in the ball of radius `r`, with `f`
at distance at least `δ` from `f x` on the sphere of radius `r`, the map `f` and the map
`f + ε • (· - x)`, for `|ε| * r < δ`, are related by a proper homotopy: there is a proper map `G`
whose degree is the local index of `f` at `x`, equal to `f + ε • (· - x)` on the closed ball, and
at distance at least `δ - |ε| * r` from `f x` outside the open ball. -/
private theorem exists_isProperMap_localIndex_eq_degree (hE : finrank ℝ E = n) {f : C(E, E)}
    {x : E} {r δ ε : ℝ} (hr : 0 ≤ r) (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖)
    (hiso : ∀ z ∈ ball x r, f z = f x → z = x) (hε : |ε| * r < δ) :
    ∃ G : C(E, E), IsProperMap G ∧ o.localIndex o f x = o.degree o hE G ∧
      EqOn G (fun z ↦ f z + ε • (z - x)) (closedBall x r) ∧
      ∀ z, r ≤ dist z x → δ - |ε| * r ≤ ‖G z - f x‖ := by
  obtain ⟨g, hgp, hgf, hgout, -, hidx⟩ := o.exists_isProperMap_eqOn_localIndex_eq_degree hE hr
    ((mul_nonneg (abs_nonneg ε) hr).trans_lt hε) hfδ hiso
  let G : C(E, E) :=
    ⟨fun z ↦ g z + ε • radialRetraction r (z - x),
      g.continuous.add
        (((lipschitzWith_radialRetraction hr).continuous.comp
          (continuous_id.sub continuous_const)).const_smul ε)⟩
  have hdist (z : E) : dist (g z) (G z) ≤ |ε| * r := by
    rw [dist_comm, dist_eq_norm]
    simp only [G, ContinuousMap.coe_mk, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simp [norm_radialRetraction hr]) (abs_nonneg ε)
  have hGp : IsProperMap G := hgp.of_dist_le G.continuous hdist
  -- The straight-line homotopy from `g` to `G` has a compact fibre over `f x`, inside `I × B`.
  let H := ContinuousMap.Homotopy.affine g G
  have hHc : IsCompact (H ⁻¹' {f x}) := by
    refine (isCompact_univ.prod (isCompact_closedBall x r)).of_isClosed_subset
      (isClosed_singleton.preimage H.continuous) fun p hp ↦ ⟨mem_univ _, ?_⟩
    by_contra hpB
    have h1 : δ ≤ dist (g p.2) (f x) := by
      rw [dist_eq_norm]
      exact hgout p.2 (not_le.1 (mem_closedBall.not.1 hpB)).le
    have h2 : dist (H p) (g p.2) ≤ |ε| * r := by
      have ht : ‖(p.1 : ℝ)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg p.1.property.1]
        exact p.1.property.2
      simpa only [H, ContinuousMap.Homotopy.affine_apply, dist_lineMap_left] using
        (mul_le_of_le_one_left dist_nonneg ht).trans (hdist p.2)
    rw [mem_singleton_iff.1 hp, dist_comm] at h2
    linarith
  refine ⟨G, hGp, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hidx, ← o.localDegree_eq_degree o hE hE hgp (f x),
      o.localDegree_eq_of_homotopy_of_isCompact o hE hE H hHc, o.localDegree_eq_degree o hE hE hGp]
  · simp only [G, ContinuousMap.coe_mk, hgf hz,
      radialRetraction_of_norm_le (by simpa [dist_eq_norm] using hz : ‖z - x‖ ≤ r)]
  · have h3 := dist_triangle (g z) (G z) (f x)
    rw [dist_eq_norm (g z), dist_eq_norm (G z)] at h3
    linarith [hgout z hz, hdist z]

end Real

section Holomorphic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
  (o : HomologicalOrientation E E n)

/-- **The local index at a point with invertible complex derivative is `1`.** If `f` is complex
differentiable at `x` with injective derivative, its local index at `x`, for the same orientation of
`E` on source and target, is `1`: the real Jacobian determinant `|det_ℂ f'|²` is positive. -/
theorem localIndex_eq_one_of_hasFDerivAt (hE : finrank ℝ E = n) {f : C(E, E)} {f' : E →L[ℂ] E}
    {x : E} (hf : HasFDerivAt f f' x) (hf' : Function.Injective f') :
    o.localIndex o f x = 1 := by
  have hpos : 0 < (f'.restrictScalars ℝ).det :=
    LinearMap.det_restrictScalars_pos_iff_injective.2 hf'
  rw [o.localIndex_eq_sign_det hE (hf.restrictScalars ℝ) hpos.ne', sign_pos hpos,
    SignType.coe_one]

/-- **The degree of a holomorphic proper map counts preimages.** If every preimage of `y` under the
proper map `f : E → E` is a point where `f` is complex differentiable with injective derivative,
then the degree of `f` is the number of preimages of `y`. -/
theorem degree_eq_ncard_of_hasFDerivAt (hE : finrank ℝ E = n) {f : C(E, E)} (hf : IsProperMap f)
    {f' : E → E →L[ℂ] E} {y : E} (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hinj : ∀ x ∈ f ⁻¹' {y}, Function.Injective (f' x)) :
    o.degree o hE f = (f ⁻¹' {y}).ncard :=
  o.degree_eq_ncard_of_det_pos hE hf (f' := fun x ↦ (f' x).restrictScalars ℝ)
    (fun x hx ↦ (hderiv x hx).restrictScalars ℝ)
    fun x hx ↦ LinearMap.det_restrictScalars_pos_iff_injective.2 (hinj x hx)

/-- **The local index of a holomorphic map counts nearby solutions.** Suppose that `x` is the only
solution of `f z = f x` in the ball of radius `r` about `x`, that `f` stays at distance at least
`δ` from `f x` on the sphere of radius `r`, and that `y` is a value within `δ` of `f x` at whose
preimages in the ball `f` is complex differentiable with injective derivative. Then the local index
of `f` at `x` is the number of solutions of `f z = y` in the ball. -/
theorem localIndex_eq_ncard_of_hasFDerivAt (hE : finrank ℝ E = n) {f : C(E, E)} {x y : E}
    {r δ : ℝ} (hr : 0 ≤ r) (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖)
    (hiso : ∀ z ∈ ball x r, f z = f x → z = x) (hy : ‖y - f x‖ < δ) {f' : E → E →L[ℂ] E}
    (hderiv : ∀ z ∈ ball x r, f z = y → HasFDerivAt f (f' z) z)
    (hinj : ∀ z ∈ ball x r, f z = y → Function.Injective (f' z)) :
    o.localIndex o f x = {z ∈ ball x r | f z = y}.ncard := by
  obtain ⟨g, hgp, hgf, -, hgfib, hidx⟩ :=
    o.exists_isProperMap_eqOn_localIndex_eq_degree hE hr ((norm_nonneg _).trans_lt hy) hfδ hiso
  replace hgfib := hgfib y hy
  rw [hidx, o.degree_eq_ncard_of_hasFDerivAt hE hgp (f' := f') (y := y), hgfib]
  · intro z hz
    rw [hgfib] at hz
    exact (hderiv z hz.1 hz.2).congr_of_eventuallyEq
      (eventually_of_mem (isOpen_ball.mem_nhds hz.1) fun _ hw ↦ hgf (ball_subset_closedBall hw))
  · intro z hz
    rw [hgfib] at hz
    exact hinj z hz.1 hz.2

/-- **The local index of a holomorphic map at an isolated point of its fibre is positive.** If `f`
is analytic at `x` and `x` is isolated in the fibre `f⁻¹(f x)`, then the local index of `f` at `x`,
for the same orientation of `E` on source and target, is positive. -/
theorem localIndex_pos_of_analyticAt (hE : finrank ℝ E = n) {f : C(E, E)} {x : E}
    (hf : AnalyticAt ℂ f x) (hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x) : 0 < o.localIndex o f x := by
  -- A ball of radius `r` about `x` on which `f` is analytic and `x` is the only solution of
  -- `f z = f x`, and a lower bound `δ` for `‖f - f x‖` on its boundary sphere.
  obtain ⟨r, hr, δ, hδ, hfa, hfδ, hiso'⟩ :=
    exists_closedBall_subset_and_le_norm_sub (U := {z | AnalyticAt ℂ f z})
      hf.eventually_analyticAt hiso
  -- A small `ε` with `ε r < δ` such that `-ε` is not an eigenvalue of `Df(x)`.
  obtain ⟨ε, ⟨hε, hεδ⟩, hεA⟩ : ∃ ε ∈ Ioo 0 (δ / r),
      ¬Module.End.HasEigenvalue (fderiv ℂ f x : Module.End ℂ E) (-(ε : ℂ)) :=
    (Ioo_infinite (div_pos hδ hr)).exists_notMem_finite
      ((Module.End.finite_hasEigenvalue (fderiv ℂ f x : Module.End ℂ E)).preimage
        fun a _ b _ h ↦ by simpa using h)
  have hεr : |ε| * r < δ := by
    rw [abs_of_pos hε]
    exact (lt_div_iff₀ hr).1 hεδ
  -- The local index of `f` is the degree of a proper map `G`, equal to `f + ε (· - x)` near `x`,
  -- complex differentiable there with derivative `Df + ε`, which is invertible at `x`.
  obtain ⟨G, hGp, hidx, hGf, hGout⟩ := o.exists_isProperMap_localIndex_eq_degree hE hr.le hfδ
    (fun z hz ↦ hiso' z (ball_subset_closedBall hz)) hεr
  have hGeq {z : E} (hz : z ∈ ball x r) :
      (G : E → E) =ᶠ[𝓝 z] fun w ↦ f w + (ε : ℂ) • (w - x) :=
    eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw ↦ by
      simpa [Complex.coe_smul] using hGf (ball_subset_closedBall hw)
  have hDx : Function.Injective (fderiv ℂ f x + (ε : ℂ) • ContinuousLinearMap.id ℂ E) :=
    (injective_iff_map_eq_zero _).2 fun v hv ↦ by_contra fun hv0 ↦ hεA
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2
        (by rw [neg_smul, eq_neg_iff_add_eq_zero]; simpa using hv), hv0⟩)
  rw [hidx]
  refine o.degree_pos_of_hasFDerivAt hE hGp (U := ball x r)
    (D := fun z ↦ (fderiv ℂ f z + (ε : ℂ) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ)
    (fun z hz ↦ (((hfa (ball_subset_closedBall hz)).differentiableAt.hasFDerivAt.add
      (((hasFDerivAt_id z).sub_const x).const_smul (ε : ℂ))).congr_of_eventuallyEq
      (hGeq hz)).restrictScalars ℝ)
    (fun z _ ↦ LinearMap.det_restrictScalars_nonneg _)
    (LinearMap.det_restrictScalars_pos_iff_injective.2 hDx).ne' ?_
  -- Values within `δ - |ε| r` of `G x = f x` have all their preimages in the open ball.
  have hGx : G x = f x := by simp [hGf (mem_closedBall_self hr.le)]
  rw [hGx]
  filter_upwards [ball_mem_nhds (f x) (sub_pos.2 hεr)] with y' hy' z (hz : G z = y')
  by_contra hzb
  have h := hGout z (not_lt.1 (mem_ball.not.1 hzb))
  rw [hz, ← dist_eq_norm] at h
  linarith [mem_ball.1 hy']

/-- **The local index of a holomorphic map is positive exactly at isolated points of its
fibres.** If `f` is analytic at `x`, its local index at `x` is positive if and only if `x` is
isolated in the fibre `f⁻¹(f x)`. -/
theorem localIndex_pos_iff_eventually_ne_of_analyticAt (hE : finrank ℝ E = n) {f : C(E, E)}
    {x : E} (hf : AnalyticAt ℂ f x) :
    0 < o.localIndex o f x ↔ ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
  refine ⟨fun h ↦ ?_, o.localIndex_pos_of_analyticAt hE hf⟩
  by_contra hiso
  rw [o.localIndex_of_frequently_eq o f (by simpa using not_eventually.1 hiso)] at h
  exact lt_irrefl 0 h

/-- **The local index of a holomorphic map is nonnegative.** -/
theorem localIndex_nonneg_of_analyticAt (hE : finrank ℝ E = n) {f : C(E, E)} {x : E}
    (hf : AnalyticAt ℂ f x) : 0 ≤ o.localIndex o f x := by
  by_cases hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · exact (o.localIndex_pos_of_analyticAt hE hf hiso).le
  · rw [o.localIndex_of_frequently_eq o f (by simpa using not_eventually.1 hiso)]

end Holomorphic

/-! ### Changes of coordinates -/

section CoordinateChange

/-- **Local intersection indices are invariant under changes of coordinates of the target with
complex-linear derivative.** Let `F p = a p - b p` for maps `a, b : M → E` continuous at `x` with
`a x = b x`. If `Ψ : E → E` is strictly differentiable at `a x` with an injective complex-linear
derivative, such as a holomorphic chart or a unitary map, then `G' p = Ψ (a p) - Ψ (b p)` has the
same local index as `F` at `x`: the real Jacobian determinant `|det_ℂ|²` of the derivative is
positive. -/
theorem localIndex_eq_of_apply_eq_sub_of_hasStrictFDerivAt {M G E : Type} [TopologicalSpace M]
    [T2Space M] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [ChartedSpace G M] [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
    (o : HomologicalOrientation M G n) (o' : HomologicalOrientation E E n) (hE : finrank ℝ E = n)
    {F G' : C(M, E)} {a b : M → E} {Ψ : E → E} {L : E →L[ℂ] E} {x : M}
    (hF : ∀ p, F p = a p - b p) (hG' : ∀ p, G' p = Ψ (a p) - Ψ (b p))
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (hab : a x = b x)
    (hΨ : HasStrictFDerivAt Ψ (L.restrictScalars ℝ) (a x)) (hL : Function.Injective L) :
    o.localIndex o' G' x = o.localIndex o' F x := by
  have hpos : 0 < (L.restrictScalars ℝ).det :=
    LinearMap.det_restrictScalars_pos_iff_injective.2 hL
  rw [o.localIndex_eq_sign_det_mul_of_apply_eq_sub o' hE hF hG' ha hb hab hΨ hpos.ne',
    sign_pos hpos, SignType.coe_one, one_mul]

/-- **Local indices are invariant under changes of coordinates of the source with complex-linear
derivative.** If `φ : E → E` is strictly differentiable at `x` with an injective complex-linear
derivative, such as a holomorphic reparametrization, then the local index of `F ∘ φ` at `x` is
that of `F` at `φ x`. Only the target dimension must equal `n`; the source dimension may differ. -/
theorem localIndex_comp_eq_of_hasStrictFDerivAt {E N G : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] [TopologicalSpace N] [T2Space N]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [ChartedSpace G N] {n : ℕ}
    (o : HomologicalOrientation E E n) (o' : HomologicalOrientation N G n) (hG : finrank ℝ G = n)
    {F : C(E, N)} {φ : C(E, E)} {φ' : E →L[ℂ] E} {x : E}
    (hφ : HasStrictFDerivAt φ (φ'.restrictScalars ℝ) x) (hφ' : Function.Injective φ') :
    o.localIndex o' (F.comp φ) x = o.localIndex o' F (φ x) := by
  have hpos : 0 < (φ'.restrictScalars ℝ).det :=
    LinearMap.det_restrictScalars_pos_iff_injective.2 hφ'
  rw [o.localIndex_comp_eq_mul_sign_det o' hG hφ hpos.ne', sign_pos hpos, SignType.coe_one,
    mul_one]

end CoordinateChange

/-! ### Intersections of holomorphic discs in `ℂ²` -/

section Disc

variable {n : ℕ} (o : HomologicalOrientation (ℂ × ℂ) (ℂ × ℂ) n)

/-- **Positivity of intersections of holomorphic discs in `ℂ²`.** Let `u₁` and `u₂` be holomorphic
near `z₀` and `w₀`, meeting at `u₁ z₀ = u₂ w₀` in an isolated point: `u₁ z ≠ u₂ w` for
`(z, w) ≠ (z₀, w₀)` near `(z₀, w₀)`. Then their local intersection number, the local index at
`(z₀, w₀)` of the map `F (z, w) = u₁ z - u₂ w`, is positive. -/
theorem localIndex_pos_of_apply_eq_sub (hn : finrank ℝ (ℂ × ℂ) = n) {F : C(ℂ × ℂ, ℂ × ℂ)}
    {u₁ u₂ : ℂ → ℂ × ℂ} (hF : ∀ p, F p = u₁ p.1 - u₂ p.2) {z₀ w₀ : ℂ} (h₁ : AnalyticAt ℂ u₁ z₀)
    (h₂ : AnalyticAt ℂ u₂ w₀) (h : u₁ z₀ = u₂ w₀)
    (hiso : ∀ᶠ p in 𝓝[≠] (z₀, w₀), u₁ p.1 ≠ u₂ p.2) : 0 < o.localIndex o F (z₀, w₀) := by
  refine o.localIndex_pos_of_analyticAt hn
    (((h₁.comp analyticAt_fst).sub (h₂.comp analyticAt_snd)).congr
      (.of_forall fun p ↦ (hF p).symm)) ?_
  filter_upwards [hiso] with p hp
  rw [hF p, hF (z₀, w₀), h, sub_self]
  exact sub_ne_zero.2 hp

/-- **A transverse intersection of holomorphic discs counts `1`.** If `u₁` and `u₂` have
derivatives `a` at `z₀` and `b` at `w₀` which are linearly independent over `ℂ`, then the local
index at `(z₀, w₀)` of the map `F (z, w) = u₁ z - u₂ w` is `1`. -/
theorem localIndex_eq_one_of_apply_eq_sub (hn : finrank ℝ (ℂ × ℂ) = n) {F : C(ℂ × ℂ, ℂ × ℂ)}
    {u₁ u₂ : ℂ → ℂ × ℂ} (hF : ∀ p, F p = u₁ p.1 - u₂ p.2) {z₀ w₀ : ℂ} {a b : ℂ × ℂ}
    (h₁ : HasDerivAt u₁ a z₀) (h₂ : HasDerivAt u₂ b w₀) (hab : LinearIndependent ℂ ![a, b]) :
    o.localIndex o F (z₀, w₀) = 1 :=
  o.localIndex_eq_one_of_hasFDerivAt hn
    ((h₁.hasFDerivAt_comp_fst_sub_comp_snd h₂).congr_of_eventuallyEq (.of_forall hF))
    (LinearMap.injective_fst_smulRight_sub_snd_smulRight_iff.2 hab)

/-! #### Examples -/

/-- The line `w = 0` of `ℂ²` has derivative `(1, 0)`. -/
private theorem hasDerivAt_lineZero (z : ℂ) :
    HasDerivAt (fun z : ℂ ↦ ((z, 0) : ℂ × ℂ)) ((1 : ℂ), (0 : ℂ)) z :=
  (hasDerivAt_id z).prodMk (hasDerivAt_const z 0)

/-- The coordinate lines `w = 0` and `z = 0` of `ℂ²` meet at the origin with local intersection
number `1`. -/
example (hn : finrank ℝ (ℂ × ℂ) = n) :
    o.localIndex o ⟨fun p ↦ (p.1, -p.2), by fun_prop⟩ (0, 0) = 1 :=
  o.localIndex_eq_one_of_apply_eq_sub hn (u₁ := fun z ↦ (z, 0)) (u₂ := fun w ↦ (0, w))
    (fun p ↦ by simp) (hasDerivAt_lineZero 0)
    ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id 0))
    (linearIndependent_pair_mk_one_iff.2 (by simp))

/-- The lines `w = 0` and `w = z` of `ℂ²` meet at the origin with local intersection number `1`. -/
example (hn : finrank ℝ (ℂ × ℂ) = n) :
    o.localIndex o ⟨fun p ↦ (p.1 - p.2, -p.2), by fun_prop⟩ (0, 0) = 1 :=
  o.localIndex_eq_one_of_apply_eq_sub hn (u₁ := fun z ↦ (z, 0)) (u₂ := fun w ↦ (w, w))
    (fun p ↦ by simp) (hasDerivAt_lineZero 0) ((hasDerivAt_id 0).prodMk (hasDerivAt_id 0))
    (linearIndependent_pair_mk_one_iff.2 (by simp))

/-- The line `w = 0` meets itself along a whole line: `(z, z)` is not isolated among the solutions
of `z - w = 0`, and the local index there is `0`. -/
example (z : ℂ) : o.localIndex o ⟨fun p ↦ (p.1 - p.2, 0), by fun_prop⟩ (z, z) = 0 := by
  refine o.localIndex_of_frequently_eq o _ ?_
  have h : Tendsto (fun t : ℂ ↦ (z + t, z + t)) (𝓝[≠] 0) (𝓝[≠] (z, z)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun t : ℂ ↦ (z + t, z + t) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact h.frequently (Frequently.of_forall fun t ↦ by simp)

end Disc

end HomologicalOrientation

end TauCeti
