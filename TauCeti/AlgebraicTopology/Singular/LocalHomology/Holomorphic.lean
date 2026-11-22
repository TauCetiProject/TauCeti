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
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
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
invertible derivative `Df(x) + ε` at `x`, so by the inverse function theorem `G` maps the interior
of `B` onto a neighbourhood of `f x`; by the equal-dimensional Sard theorem
(`TauCeti.dense_setOf_forall_surjective_fderiv`) this neighbourhood contains a value all of whose
preimages are regular, and it has at least one. So the degree of `G` is a
positive number of preimages.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasFDerivAt`: at a point with invertible
  complex derivative the local index is `1`.
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

section Holomorphic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
  (o : HomologicalOrientation E E n) (hE : finrank ℝ E = n)

include hE in
/-- **The local index at a point with invertible complex derivative is `1`.** If `f` is complex
differentiable at `x` with injective derivative, its local index at `x`, for the same orientation of
`E` on source and target, is `1`: the real Jacobian determinant `|det_ℂ f'|²` is positive. -/
theorem localIndex_eq_one_of_hasFDerivAt {f : C(E, E)} {f' : E →L[ℂ] E} {x : E}
    (hf : HasFDerivAt f f' x) (hf' : Function.Injective f') : o.localIndex o f x = 1 := by
  have hpos : 0 < (f'.restrictScalars ℝ).det :=
    LinearMap.det_restrictScalars_pos_iff_injective.2 hf'
  rw [o.localIndex_eq_sign_det hE (hf.restrictScalars ℝ) hpos.ne', sign_pos hpos,
    SignType.coe_one]

include hE in
/-- **The degree of a holomorphic proper map counts preimages.** If every preimage of `y` under the
proper map `f : E → E` is a point where `f` is complex differentiable with injective derivative,
then the degree of `f` is the number of preimages of `y`. -/
theorem degree_eq_ncard_of_hasFDerivAt {f : C(E, E)} (hf : IsProperMap f) {f' : E → E →L[ℂ] E}
    {y : E} (hderiv : ∀ x ∈ f ⁻¹' {y}, HasFDerivAt f (f' x) x)
    (hinj : ∀ x ∈ f ⁻¹' {y}, Function.Injective (f' x)) :
    o.degree o hE f = (f ⁻¹' {y}).ncard := by
  have hpos (x : E) (hx : x ∈ f ⁻¹' {y}) : 0 < ((f' x).restrictScalars ℝ).det :=
    LinearMap.det_restrictScalars_pos_iff_injective.2 (hinj x hx)
  have h₁ : {x | 0 < ((f' x).restrictScalars ℝ).det} ∩ f ⁻¹' {y} = f ⁻¹' {y} :=
    inter_eq_right.2 fun x hx ↦ hpos x hx
  have h₂ : {x | ((f' x).restrictScalars ℝ).det < 0} ∩ f ⁻¹' {y} = ∅ :=
    eq_empty_iff_forall_notMem.2 fun x hx ↦ (hpos x hx.2).not_gt hx.1
  rw [o.degree_eq_ncard_sub_ncard hE hf (f' := fun x ↦ (f' x).restrictScalars ℝ)
    (fun x hx ↦ (hderiv x hx).restrictScalars ℝ) fun x hx ↦ (hpos x hx).ne', h₁, h₂,
    ncard_empty, Nat.cast_zero, sub_zero]

include hE in
/-- If `x` is the only solution of `f z = f x` in the ball of radius `r` about `x`, and `f` stays
at distance at least `δ > 0` from `f x` on the sphere of radius `r`, then `f` agrees on the closed
ball with a proper map `g` which stays at distance at least `δ` from `f x` outside the open ball,
whose fibre over each value `y` within `δ` of `f x` is the set of solutions of `f z = y` in the
open ball, and the local index of `f` at `x` is the degree of `g`. -/
private theorem exists_isProperMap_eqOn_localIndex_eq_degree {f : C(E, E)} {x : E} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖)
    (hiso : ∀ z ∈ ball x r, f z = f x → z = x) :
    ∃ g : C(E, E), IsProperMap g ∧ EqOn g f (closedBall x r) ∧
      (∀ z, r ≤ dist z x → δ ≤ ‖g z - f x‖) ∧
      (∀ y, ‖y - f x‖ < δ → g ⁻¹' {y} = {z ∈ ball x r | f z = y}) ∧
      o.localIndex o f x = o.degree o hE g := by
  obtain ⟨g, hgp, hgf, hgout⟩ :=
    f.continuous.continuousOn.exists_isProperMap_eqOn_closedBall_and_le_norm_sub hr.le hδ hfδ
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
    exact ⟨fun hz ↦ hiso z hz.1 hz.2, by rintro rfl; exact ⟨mem_ball_self hr, rfl⟩⟩
  have hgf_nhds : g =ᶠ[𝓝 x] f :=
    eventually_of_mem (ball_mem_nhds x hr) fun _ hw ↦ hgf (ball_subset_closedBall hw)
  rw [o.localIndex_congr o hE hgf_nhds.symm, ← o.localDegree_eq_localIndex o hE hE g hfib₀,
    o.localDegree_eq_degree o hE hE hgp]

include hE in
/-- **The local index of a holomorphic map counts nearby solutions.** Suppose that `x` is the only
solution of `f z = f x` in the ball of radius `r` about `x`, that `f` stays at distance at least
`δ > 0` from `f x` on the sphere of radius `r`, and that `y` is a value within `δ` of `f x` at
whose preimages in the ball `f` is complex differentiable with injective derivative. Then the local
index of `f` at `x` is the number of solutions of `f z = y` in the ball. -/
theorem localIndex_eq_ncard_of_hasFDerivAt {f : C(E, E)} {x y : E} {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖)
    (hiso : ∀ z ∈ ball x r, f z = f x → z = x) (hy : ‖y - f x‖ < δ) {f' : E → E →L[ℂ] E}
    (hderiv : ∀ z ∈ ball x r, f z = y → HasFDerivAt f (f' z) z)
    (hinj : ∀ z ∈ ball x r, f z = y → Function.Injective (f' z)) :
    o.localIndex o f x = {z ∈ ball x r | f z = y}.ncard := by
  obtain ⟨g, hgp, hgf, -, hgfib, hidx⟩ :=
    o.exists_isProperMap_eqOn_localIndex_eq_degree hE hr hδ hfδ hiso
  replace hgfib := hgfib y hy
  rw [hidx, o.degree_eq_ncard_of_hasFDerivAt hE hgp (f' := f') (y := y), hgfib]
  · intro z hz
    rw [hgfib] at hz
    exact (hderiv z hz.1 hz.2).congr_of_eventuallyEq
      (eventually_of_mem (isOpen_ball.mem_nhds hz.1) fun _ hw ↦ hgf (ball_subset_closedBall hw))
  · intro z hz
    rw [hgfib] at hz
    exact hinj z hz.1 hz.2

include hE in
/-- **A proper holomorphic map with a regular preimage has positive degree.** Let `G : E → E` be
proper and complex differentiable, with derivatives `D z`, on a neighbourhood `U` of `x`
containing the preimages of all values near `y = G x`. If `G` is strictly differentiable at `x`
with injective derivative `D x`, then the degree of `G` is positive. -/
theorem degree_pos_of_hasStrictFDerivAt {G : C(E, E)} (hG : IsProperMap G) {U : Set E}
    {D : E → E →L[ℂ] E} (hGd : ∀ z ∈ U, HasFDerivAt G (D z) z) {x y : E} (hU : U ∈ 𝓝 x)
    (hGx : G x = y) (hstrict : HasStrictFDerivAt G (D x) x) (hDx : Function.Injective (D x))
    (hfib : ∀ᶠ y' in 𝓝 y, G ⁻¹' {y'} ⊆ U) : 0 < o.degree o hE G := by
  -- By the inverse function theorem, `G` maps `U` onto a neighbourhood of `y`.
  have hdetx : (D x).det ≠ 0 := fun h ↦
    LinearMap.det_eq_zero_iff_ker_ne_bot.1 h (LinearMap.ker_eq_bot.2 hDx)
  have hstrict' : HasStrictFDerivAt G
      ((D x).toContinuousLinearEquivOfDetNeZero hdetx : E →L[ℂ] E) x := by
    rwa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  have hW : G '' U ∩ {y' | G ⁻¹' {y'} ⊆ U} ∈ 𝓝 y := by
    refine inter_mem ?_ hfib
    rw [← hGx, ← hstrict'.map_nhds_eq_of_equiv]
    exact image_mem_map hU
  -- By Sard's theorem the regular values of `G` on `U` are dense, so some value in the interior of
  -- this neighbourhood has only regular preimages.
  borelize E
  obtain ⟨y', hy'W, hy'S⟩ := (dense_setOf_forall_surjective_fderiv (s := U) (f := G)
    (fun z hz ↦ ((hGd z hz).restrictScalars ℝ).differentiableAt) rfl).inter_open_nonempty
    (interior (G '' U ∩ {y' | G ⁻¹' {y'} ⊆ U})) isOpen_interior
    ⟨y, mem_interior_iff_mem_nhds.2 hW⟩
  obtain ⟨⟨z₀, -, hGz₀⟩, hy'U⟩ := interior_subset hy'W
  have hreg {z : E} (hz : z ∈ G ⁻¹' {y'}) : Function.Injective (D z) := by
    have hsurj := hy'S z (hy'U hz) hz
    rw [((hGd z (hy'U hz)).restrictScalars ℝ).fderiv] at hsurj
    exact LinearMap.injective_iff_surjective.2 hsurj
  have hfin : (G ⁻¹' {y'}).Finite :=
    (hG.isCompact_preimage isCompact_singleton).finite_of_hasFDerivAt
      (f' := fun z ↦ (D z).restrictScalars ℝ)
      (fun z hz ↦ (hGd z (hy'U hz)).restrictScalars ℝ) fun z hz ↦
        ⟨_, (((D z).restrictScalars ℝ).toContinuousLinearEquivOfDetNeZero
          (LinearMap.det_restrictScalars_pos_iff_injective.2 (hreg hz)).ne').antilipschitzWith⟩
  rw [o.degree_eq_ncard_of_hasFDerivAt hE hG (f' := D) (y := y')
    (fun z hz ↦ hGd z (hy'U hz)) fun z hz ↦ hreg hz]
  exact_mod_cast (ncard_pos hfin).2 ⟨z₀, hGz₀⟩

include hE in
/-- Near a point `x` which is the only solution of `f z = f x` in the ball of radius `r`, with `f`
at distance at least `δ` from `f x` on the sphere of radius `r`, the map `f` and the map
`f + c • (· - x)`, for `‖c‖ r < δ`, are related by a proper homotopy: there is a proper map `G`
whose degree is the local index of `f` at `x`, equal to `f + c • (· - x)` on the closed ball, and
at distance at least `δ - ‖c‖ r` from `f x` outside the open ball. -/
private theorem exists_isProperMap_localIndex_eq_degree {f : C(E, E)} {x : E} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hfδ : ∀ z ∈ sphere x r, δ ≤ ‖f z - f x‖)
    (hiso : ∀ z ∈ ball x r, f z = f x → z = x) {c : ℂ} (hc : ‖c‖ * r < δ) :
    ∃ G : C(E, E), IsProperMap G ∧ o.localIndex o f x = o.degree o hE G ∧
      EqOn G (fun z ↦ f z + c • (z - x)) (closedBall x r) ∧
      ∀ z, r ≤ dist z x → δ - ‖c‖ * r ≤ ‖G z - f x‖ := by
  obtain ⟨g, hgp, hgf, hgout, -, hidx⟩ :=
    o.exists_isProperMap_eqOn_localIndex_eq_degree hE hr hδ hfδ hiso
  -- The perturbation `t • c • ρ`, with `ρ z = radialRetraction r (z - x)` equal to `z - x` on the
  -- closed ball and of norm at most `r`.
  set ρ : E → E := fun z ↦ radialRetraction r (z - x) with hρ_def
  have hρc : Continuous ρ :=
    (lipschitzWith_radialRetraction hr.le).continuous.comp (continuous_id.sub continuous_const)
  have hpert {t : ℝ} (ht : |t| ≤ 1) (z : E) : ‖(t : ℂ) • c • ρ z‖ ≤ ‖c‖ * r := by
    have hρn : ‖ρ z‖ ≤ r := by simp only [hρ_def, norm_radialRetraction hr.le, min_le_right]
    rw [norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * (‖c‖ * ‖ρ z‖) ≤ 1 * (‖c‖ * r) := by gcongr
      _ = ‖c‖ * r := one_mul _
  have hfar {t : ℝ} (ht : |t| ≤ 1) {z : E} (hz : r ≤ dist z x) :
      δ - ‖c‖ * r ≤ ‖g z + (t : ℂ) • c • ρ z - f x‖ := by
    have h := norm_sub_norm_le (g z - f x) (-((t : ℂ) • c • ρ z))
    rw [norm_neg, sub_neg_eq_add, sub_add_eq_add_sub] at h
    linarith [hgout z hz, hpert ht z]
  let G : C(E, E) := ⟨fun z ↦ g z + c • ρ z, g.continuous.add (hρc.const_smul c)⟩
  have hG (z : E) : G z = g z + ((1 : ℝ) : ℂ) • c • ρ z := by
    simp [G]
  have hGp : IsProperMap G := hgp.of_dist_le G.continuous (C := ‖c‖ * r) fun z ↦ by
    rw [dist_eq_norm, hG, sub_add_cancel_left, norm_neg]
    exact hpert (by simp) z
  -- The straight homotopy from `g` to `G` has a compact fibre over `f x`, inside `I × B`.
  let H : g.Homotopy G :=
    { toFun := fun p ↦ g p.2 + ((p.1 : ℝ) : ℂ) • c • ρ p.2
      continuous_toFun :=
        (g.continuous.comp continuous_snd).add
          ((Complex.continuous_ofReal.comp (continuous_subtypeVal.comp continuous_fst)).smul
            ((hρc.comp continuous_snd).const_smul c))
      map_zero_left := fun z ↦ by simp
      map_one_left := fun z ↦ (hG z).symm }
  -- The values of `H` are given by its defining formula.
  have hH (p : unitInterval × E) : H p = g p.2 + ((p.1 : ℝ) : ℂ) • c • ρ p.2 := rfl
  have hHc : IsCompact (H ⁻¹' {f x}) := by
    refine (isCompact_univ.prod (isCompact_closedBall x r)).of_isClosed_subset
      (isClosed_singleton.preimage H.continuous) fun p hp ↦ ⟨mem_univ _, ?_⟩
    by_contra hpB
    have h := hfar (by rw [abs_of_nonneg p.1.property.1]; exact p.1.property.2)
      (not_le.1 (mem_closedBall.not.1 hpB)).le
    rw [← hH, (hp : H p = f x), sub_self, norm_zero] at h
    linarith
  refine ⟨G, hGp, ?_, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hidx, ← o.localDegree_eq_degree o hE hE hgp (f x),
      o.localDegree_eq_of_homotopy_of_isCompact o hE hE H hHc, o.localDegree_eq_degree o hE hE hGp]
  · simp only [G, ContinuousMap.coe_mk, hgf hz, hρ_def,
      radialRetraction_of_norm_le (by simpa [dist_eq_norm] using hz : ‖z - x‖ ≤ r)]
  · rw [hG]
    exact hfar (by simp) hz

include hE in
/-- **The local index of a holomorphic map at an isolated point of its fibre is positive.** If `f`
is analytic at `x` and `x` is isolated in the fibre `f⁻¹(f x)`, then the local index of `f` at `x`,
for the same orientation of `E` on source and target, is positive. -/
theorem localIndex_pos_of_analyticAt {f : C(E, E)} {x : E} (hf : AnalyticAt ℂ f x)
    (hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x) : 0 < o.localIndex o f x := by
  -- A ball of radius `r` about `x` on which `f` is analytic and `x` is the only solution of
  -- `f z = f x`, and a lower bound `δ` for `‖f - f x‖` on its boundary sphere.
  obtain ⟨R, hR, hfR⟩ := Metric.eventually_nhds_iff_ball.1
    (hf.eventually_analyticAt.and (eventually_nhdsWithin_iff.1 hiso))
  have hr : 0 < R / 2 := half_pos hR
  have hrR : closedBall x (R / 2) ⊆ ball x R := closedBall_subset_ball (half_lt_self hR)
  have hiso' (z : E) (hz : z ∈ closedBall x (R / 2)) (hfz : f z = f x) : z = x :=
    by_contra fun hzx ↦ (hfR z (hrR hz)).2 hzx hfz
  obtain ⟨δ, hδ, hfδ⟩ : ∃ δ > 0, ∀ z ∈ sphere x (R / 2), δ ≤ ‖f z - f x‖ :=
    exists_pos_le_norm_of_mem_sphere (f.continuous.continuousOn.sub continuousOn_const)
      fun z hz ↦ sub_ne_zero.2 fun h ↦
        ne_of_mem_sphere hz hr.ne' (hiso' z (sphere_subset_closedBall hz) h)
  -- A small `ε` with `ε R / 2 < δ` such that `-ε` is not an eigenvalue of `Df(x)`.
  obtain ⟨ε, ⟨hε, hεδ⟩, hεA⟩ : ∃ ε ∈ Ioo 0 (δ / (R / 2)),
      ¬Module.End.HasEigenvalue (fderiv ℂ f x : Module.End ℂ E) (-(ε : ℂ)) :=
    (Ioo_infinite (div_pos hδ hr)).exists_notMem_finite
      ((Module.End.finite_hasEigenvalue (fderiv ℂ f x : Module.End ℂ E)).preimage
        fun a _ b _ h ↦ by simpa using h)
  have hεr : ‖(ε : ℂ)‖ * (R / 2) < δ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hε.le]
    exact (lt_div_iff₀ hr).1 hεδ
  -- The local index of `f` is the degree of a proper map `G`, equal to `f + ε (· - x)` near `x`,
  -- complex differentiable there with derivative `Df + ε`, which is invertible at `x`.
  obtain ⟨G, hGp, hidx, hGf, hGout⟩ := o.exists_isProperMap_localIndex_eq_degree hE hr hδ hfδ
    (fun z hz ↦ hiso' z (ball_subset_closedBall hz)) hεr
  have hGeq {z : E} (hz : z ∈ ball x (R / 2)) :
      (G : E → E) =ᶠ[𝓝 z] fun w ↦ f w + (ε : ℂ) • (w - x) :=
    eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw ↦ hGf (ball_subset_closedBall hw)
  have hDx : Function.Injective (fderiv ℂ f x + (ε : ℂ) • ContinuousLinearMap.id ℂ E) :=
    (injective_iff_map_eq_zero _).2 fun v hv ↦ by_contra fun hv0 ↦ hεA
      (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2
        (by rw [neg_smul, eq_neg_iff_add_eq_zero]; simpa using hv), hv0⟩)
  rw [hidx]
  refine o.degree_pos_of_hasStrictFDerivAt hE hGp (U := ball x (R / 2)) (y := f x)
    (D := fun z ↦ fderiv ℂ f z + (ε : ℂ) • ContinuousLinearMap.id ℂ E) (fun z hz ↦ ?_)
    (ball_mem_nhds x hr) (by simp [hGf (mem_closedBall_self hr.le)]) ?_ hDx ?_
  · exact (((hfR z (hrR (ball_subset_closedBall hz))).1.differentiableAt.hasFDerivAt).add
      (((hasFDerivAt_id z).sub_const x).const_smul (ε : ℂ))).congr_of_eventuallyEq (hGeq hz)
  · exact (hf.hasStrictFDerivAt.add
      (((hasStrictFDerivAt_id x).sub_const x).const_smul (ε : ℂ))).congr_of_eventuallyEq
      (hGeq (mem_ball_self hr)).symm
  · -- Values within `δ - ε R / 2` of `f x` have all their preimages in the open ball.
    filter_upwards [ball_mem_nhds (f x) (sub_pos.2 hεr)] with y' hy' z (hz : G z = y')
    by_contra hzb
    have h := hGout z (not_lt.1 (mem_ball.not.1 hzb))
    rw [hz, ← dist_eq_norm] at h
    linarith [mem_ball.1 hy']

include hE in
/-- **The local index of a holomorphic map is positive exactly at isolated points of its
fibres.** If `f` is analytic at `x`, its local index at `x` is positive if and only if `x` is
isolated in the fibre `f⁻¹(f x)`. -/
theorem localIndex_pos_iff_eventually_ne_of_analyticAt {f : C(E, E)} {x : E}
    (hf : AnalyticAt ℂ f x) :
    0 < o.localIndex o f x ↔ ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
  refine ⟨fun h ↦ ?_, o.localIndex_pos_of_analyticAt hE hf⟩
  by_contra hiso
  rw [o.localIndex_of_frequently_eq o f (by simpa [Filter.not_eventually] using hiso)] at h
  exact lt_irrefl 0 h

include hE in
/-- **The local index of a holomorphic map is nonnegative.** -/
theorem localIndex_nonneg_of_analyticAt {f : C(E, E)} {x : E} (hf : AnalyticAt ℂ f x) :
    0 ≤ o.localIndex o f x := by
  by_cases hiso : ∀ᶠ z in 𝓝[≠] x, f z ≠ f x
  · exact (o.localIndex_pos_of_analyticAt hE hf hiso).le
  · rw [o.localIndex_of_frequently_eq o f (by simpa [Filter.not_eventually] using hiso)]

end Holomorphic

/-! ### Intersections of holomorphic discs in `ℂ²` -/

section Disc

variable {n : ℕ} (o : HomologicalOrientation (ℂ × ℂ) (ℂ × ℂ) n) (hn : finrank ℝ (ℂ × ℂ) = n)

include hn in
/-- **Positivity of intersections of holomorphic discs in `ℂ²`.** Let `u₁` and `u₂` be holomorphic
near `z₀` and `w₀`, meeting at `u₁ z₀ = u₂ w₀` in an isolated point: `u₁ z ≠ u₂ w` for
`(z, w) ≠ (z₀, w₀)` near `(z₀, w₀)`. Then their local intersection number, the local index at
`(z₀, w₀)` of the map `F (z, w) = u₁ z - u₂ w`, is positive. -/
theorem localIndex_pos_of_apply_eq_sub {F : C(ℂ × ℂ, ℂ × ℂ)} {u₁ u₂ : ℂ → ℂ × ℂ}
    (hF : ∀ p, F p = u₁ p.1 - u₂ p.2) {z₀ w₀ : ℂ} (h₁ : AnalyticAt ℂ u₁ z₀)
    (h₂ : AnalyticAt ℂ u₂ w₀) (h : u₁ z₀ = u₂ w₀)
    (hiso : ∀ᶠ p in 𝓝[≠] (z₀, w₀), u₁ p.1 ≠ u₂ p.2) : 0 < o.localIndex o F (z₀, w₀) := by
  have hF' : (F : ℂ × ℂ → ℂ × ℂ) = fun p ↦ u₁ p.1 - u₂ p.2 := funext hF
  refine o.localIndex_pos_of_analyticAt hn ?_ ?_
  · rw [hF']
    exact (h₁.comp analyticAt_fst).sub (h₂.comp analyticAt_snd)
  · filter_upwards [hiso] with p hp
    rw [hF p, hF (z₀, w₀), h, sub_self]
    exact sub_ne_zero.2 hp

include hn in
/-- **A transverse intersection of holomorphic discs counts `1`.** If `u₁` and `u₂` have
derivatives `a` at `z₀` and `b` at `w₀` which are linearly independent over `ℂ`, then the local
index at `(z₀, w₀)` of the map `F (z, w) = u₁ z - u₂ w` is `1`. -/
theorem localIndex_eq_one_of_apply_eq_sub {F : C(ℂ × ℂ, ℂ × ℂ)} {u₁ u₂ : ℂ → ℂ × ℂ}
    (hF : ∀ p, F p = u₁ p.1 - u₂ p.2) {z₀ w₀ : ℂ} {a b : ℂ × ℂ} (h₁ : HasDerivAt u₁ a z₀)
    (h₂ : HasDerivAt u₂ b w₀) (hab : LinearIndependent ℂ ![a, b]) :
    o.localIndex o F (z₀, w₀) = 1 :=
  o.localIndex_eq_one_of_hasFDerivAt hn
    ((h₁.hasFDerivAt_comp_fst_sub_comp_snd h₂).congr_of_eventuallyEq (.of_forall hF))
    (LinearMap.injective_fst_smulRight_sub_snd_smulRight_iff.2 hab)

/-! #### Examples -/

/-- The line `w = 0` of `ℂ²` has derivative `(1, 0)`. -/
private theorem hasDerivAt_lineZero (z : ℂ) :
    HasDerivAt (fun z : ℂ ↦ ((z, 0) : ℂ × ℂ)) ((1 : ℂ), (0 : ℂ)) z :=
  (hasDerivAt_id z).prodMk (hasDerivAt_const z 0)

include hn in
/-- The coordinate lines `w = 0` and `z = 0` of `ℂ²` meet at the origin with local intersection
number `1`. -/
example : o.localIndex o ⟨fun p ↦ (p.1, -p.2), by fun_prop⟩ (0, 0) = 1 :=
  o.localIndex_eq_one_of_apply_eq_sub hn (u₁ := fun z ↦ (z, 0)) (u₂ := fun w ↦ (0, w))
    (fun p ↦ by simp) (hasDerivAt_lineZero 0)
    ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id 0))
    (linearIndependent_pair_mk_one_iff.2 (by simp))

include hn in
/-- The lines `w = 0` and `w = z` of `ℂ²` meet at the origin with local intersection number `1`. -/
example : o.localIndex o ⟨fun p ↦ (p.1 - p.2, -p.2), by fun_prop⟩ (0, 0) = 1 :=
  o.localIndex_eq_one_of_apply_eq_sub hn (u₁ := fun z ↦ (z, 0)) (u₂ := fun w ↦ (w, w))
    (fun p ↦ by simp) (hasDerivAt_lineZero 0) ((hasDerivAt_id 0).prodMk (hasDerivAt_id 0))
    (linearIndependent_pair_mk_one_iff.2 (by simp))

include hn in
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
