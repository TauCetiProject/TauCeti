/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import TauCeti.Analysis.Complex.Conformal.LocalDegree
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import TauCeti.Analysis.Analytic.Order

/-!
# The local index of a holomorphic map is its order of vanishing

Orient `ℂ`, regarded as a real manifold of dimension `2`, by a homological orientation `o`
(`TauCeti.HomologicalOrientation ℂ ℂ 2`), and use the same orientation on the source and the target
of a continuous map `f : ℂ → ℂ`, so that no choice of orientation enters. The topological local
index `o.localIndex o f z₀` (`TauCeti.HomologicalOrientation.localIndex`) of a map which is
analytic at `z₀` is the order of vanishing of `f - f z₀` at `z₀`
(`TauCeti.HomologicalOrientation.localIndex_eq_analyticOrderNatAt`). In particular the local
index of a holomorphic map at a point near which it is not constant is a positive integer
(`TauCeti.HomologicalOrientation.localIndex_pos_of_analyticAt`): the isolated zeros of a
holomorphic function carry positive topological multiplicities, which are the zero orders. This is
the input that compares the zero orders of a holomorphic section with its topological local
indices, and so with the signed count of the zeros of a transverse section, in the zero count of
the PseudoholomorphicCurveAnalysis roadmap.

At a point where `f` is complex differentiable with nonzero derivative `c`, its real derivative is
multiplication by `c`, of determinant `‖c‖² > 0`, so the local index is `1`
(`TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasDerivAt`). This is not true of every map
with invertible derivative: complex conjugation has local index `-1`
(`TauCeti.HomologicalOrientation.localIndex_conj`), so the statements here depend on `f` being
holomorphic, not only on the orientation being the same on both sides.

The proof of the general statement counts preimages. Choose a closed disc `D` around `z₀` on which
`f` is analytic, `z₀` is the only solution of `f z = f z₀`, and `f'` vanishes nowhere except
possibly at `z₀`. Extend `f|_D` radially to a proper map `g : ℂ → ℂ` whose values outside the open
disc stay a fixed distance away from `f z₀`. The degree of `g` is its local index at `z₀`, the only
preimage of `f z₀`, which is the local index of `f`. At a value `w ≠ f z₀` close to `f z₀`, the
preimages of `w` under `g` are the `m` distinct simple solutions of `f z = w` in the disc, with `m`
the order of `f - f z₀` at `z₀` (`TauCeti.localDegree_card`, a Rouché argument). Each has local
index `1`, so the degree of `g` is also `m`.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasDerivAt`: at a point with nonzero
  complex derivative the local index is `1`.
* `TauCeti.HomologicalOrientation.localIndex_eq_analyticOrderNatAt`: the local index of a map
  analytic at `z₀` is the order of vanishing of `f - f z₀` at `z₀`.
* `TauCeti.HomologicalOrientation.localIndex_pos_of_analyticAt`: it is positive when `f` is not
  constant near `z₀`.
* `TauCeti.HomologicalOrientation.localIndex_pow`: `z ↦ z ^ m` has local index `m` at `0`.
* `TauCeti.HomologicalOrientation.localIndex_conj`: complex conjugation has local index `-1`.

## References

* L. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill, 1979, Chapter 4, §3.3 (the local
  mapping theorem).
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VIII, §4 (the degree as a
  sum of local indices).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (orientation and the sign of the Jacobian).
-/

public section

noncomputable section

open Complex Filter Metric Module Set Topology

namespace TauCeti

namespace HomologicalOrientation

variable (o : HomologicalOrientation ℂ ℂ 2)

/-- **A complex derivative has positive Jacobian.** If `f` is complex differentiable at `z` with
nonzero derivative `c`, its local index at `z` is `1`: the real derivative is multiplication by
`c`, of determinant `‖c‖² > 0`. -/
theorem localIndex_eq_one_of_hasDerivAt {f : C(ℂ, ℂ)} {c z : ℂ} (hf : HasDerivAt f c z)
    (hc : c ≠ 0) : o.localIndex o f z = 1 := by
  have hdet : ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det =
      normSq c := by
    simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  have hpos : 0 < normSq c := normSq_pos.2 hc
  rw [o.localIndex_eq_sign_det finrank_real_complex (hf.hasFDerivAt.restrictScalars ℝ)
    (hdet ▸ hpos.ne'), hdet, sign_pos hpos]
  rfl

/-- **Complex conjugation reverses orientation**: it has local index `-1` at every point, for the
same orientation of `ℂ` on source and target. -/
theorem localIndex_conj (z : ℂ) :
    o.localIndex o ⟨starRingEnd ℂ, continuous_conj⟩ z = -1 := by
  have hdet : (conjCLE : ℂ →L[ℝ] ℂ).det = -1 := det_conjAe
  have h := o.localIndex_eq_sign_det finrank_real_complex (f := ⟨starRingEnd ℂ, continuous_conj⟩)
    (conjCLE.hasFDerivAt (x := z)) (by rw [hdet]; norm_num)
  rw [h, hdet]
  simp

/-- The radial extension of a map from a closed disc: if `f` stays at distance at least `δ` from
`f z₀` on the circle of radius `r` about `z₀`, then `f` agrees on the closed disc with a proper map
`g : ℂ → ℂ` which stays at distance at least `δ` from `f z₀` outside the open disc. Explicitly,
`g (z₀ + s u) = f z₀ + (s / r) (f (z₀ + r u) - f z₀)` for `s ≥ r` and `‖u‖ = 1`. -/
private theorem exists_isProperMap_eqOn_closedBall (f : C(ℂ, ℂ)) {z₀ : ℂ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hfδ : ∀ z ∈ sphere z₀ r, δ ≤ ‖f z - f z₀‖) :
    ∃ g : C(ℂ, ℂ), IsProperMap g ∧ EqOn g f (closedBall z₀ r) ∧
      ∀ z, r ≤ ‖z - z₀‖ → δ ≤ ‖g z - f z₀‖ := by
  set s : ℂ → ℝ := fun z ↦ max 1 (‖z - z₀‖ / r) with hs
  have hs1 (z : ℂ) : 1 ≤ s z := le_max_left _ _
  have hs0 (z : ℂ) : (s z : ℂ) ≠ 0 := ofReal_ne_zero.2 (zero_lt_one.trans_le (hs1 z)).ne'
  have hsc : Continuous s :=
    continuous_const.max ((continuous_id.sub continuous_const).norm.div_const r)
  have hsinv : Continuous fun z ↦ ((s z : ℂ))⁻¹ := (continuous_ofReal.comp hsc).inv₀ hs0
  let g : C(ℂ, ℂ) :=
    ⟨fun z ↦ f z₀ + (s z : ℂ) * (f (z₀ + ((s z : ℂ))⁻¹ * (z - z₀)) - f z₀),
      continuous_const.add ((continuous_ofReal.comp hsc).mul ((f.continuous.comp
        (continuous_const.add (hsinv.mul (continuous_id.sub continuous_const)))).sub
          continuous_const))⟩
  have hg (z : ℂ) : g z = f z₀ + (s z : ℂ) * (f (z₀ + ((s z : ℂ))⁻¹ * (z - z₀)) - f z₀) := rfl
  -- Outside the open disc, `g z - f z₀` is `s z` times the value of `f - f z₀` at the point of the
  -- circle on the ray through `z`.
  have hout (z : ℂ) (hz : r ≤ ‖z - z₀‖) : s z * δ ≤ ‖g z - f z₀‖ := by
    have hsz : s z = ‖z - z₀‖ / r := max_eq_right ((one_le_div hr).2 hz)
    have hmem : z₀ + ((s z : ℂ))⁻¹ * (z - z₀) ∈ sphere z₀ r := by
      rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_inv, norm_real,
        Real.norm_of_nonneg (zero_le_one.trans (hs1 z)), hsz]
      field_simp [(hr.trans_le hz).ne']
    rw [hg, add_sub_cancel_left, norm_mul, norm_real,
      Real.norm_of_nonneg (zero_le_one.trans (hs1 z))]
    exact mul_le_mul_of_nonneg_left (hfδ _ hmem) (zero_le_one.trans (hs1 z))
  refine ⟨g, ?_, fun z hz ↦ ?_, fun z hz ↦
    (le_mul_of_one_le_left hδ.le (hs1 z)).trans (hout z hz)⟩
  · -- The preimage of a compact set is closed and, by `hout`, bounded.
    refine isProperMap_iff_isCompact_preimage.2 ⟨g.continuous, fun K hK ↦ ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (f z₀)
    refine isCompact_of_isClosed_isBounded (hK.isClosed.preimage g.continuous)
      ((isBounded_closedBall (x := z₀) (r := max r (R * r / δ))).subset fun z hz ↦ ?_)
    rw [mem_closedBall, dist_eq_norm]
    by_cases hzr : r ≤ ‖z - z₀‖
    · have h1 := (hout z hzr).trans (by simpa [dist_eq_norm] using hR hz)
      have hsz : s z = ‖z - z₀‖ / r := max_eq_right ((one_le_div hr).2 hzr)
      rw [hsz, div_mul_eq_mul_div, div_le_iff₀ hr] at h1
      exact le_max_of_le_right ((le_div_iff₀ hδ).2 (by nlinarith))
    · exact le_max_of_le_left (not_le.1 hzr).le
  · have hz' : ‖z - z₀‖ ≤ r := by simpa [dist_eq_norm] using hz
    have hsz : s z = 1 := max_eq_left ((div_le_one hr).2 hz')
    rw [hg, hsz]
    simp

/-- **The local index of a holomorphic map is its order of vanishing.** If `f : ℂ → ℂ` is analytic
at `z₀`, its local index at `z₀`, for the same orientation of `ℂ` on source and target, is the
order of vanishing of `f - f z₀` at `z₀`. Both sides are `0` when `f` is constant near `z₀`. -/
theorem localIndex_eq_analyticOrderNatAt {f : C(ℂ, ℂ)} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    o.localIndex o f z₀ = analyticOrderNatAt (fun z ↦ f z - f z₀) z₀ := by
  rcases (hf.sub analyticAt_const).eventually_eq_zero_or_eventually_ne_zero with hconst | hisol
  · -- `f` is constant near `z₀`: `z₀` is not isolated in its fibre, and the order is infinite.
    have h : ∃ᶠ z in 𝓝[≠] z₀, f z = f z₀ :=
      (eventually_nhdsWithin_of_eventually_nhds hconst).frequently.mono fun _ h ↦ sub_eq_zero.1 h
    have htop : analyticOrderAt (fun z ↦ f z - f z₀) z₀ = ⊤ :=
      analyticOrderAt_eq_top.2 (hconst.mono fun _ h ↦ h)
    rw [o.localIndex_of_frequently_eq o f h, analyticOrderNatAt, htop]
    rfl
  have hE : finrank ℝ ℂ = 2 := finrank_real_complex
  -- A closed disc of radius `r` on which `f` is analytic, `z₀` is the only solution of
  -- `f z = f z₀`, and `f'` vanishes nowhere except possibly at `z₀`.
  have hderiv : ∀ᶠ z in 𝓝[≠] z₀, deriv f z ≠ 0 :=
    eventually_deriv_ne_zero_of_eventually_ne hf (hisol.mono fun _ h ↦ sub_ne_zero.1 h)
  have hall : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ f z ∧ (z ≠ z₀ → f z ≠ f z₀) ∧
      (z ≠ z₀ → deriv f z ≠ 0) := by
    filter_upwards [hf.eventually_analyticAt, eventually_nhdsWithin_iff.1 hisol,
      eventually_nhdsWithin_iff.1 hderiv] with z h1 h2 h3
    exact ⟨h1, fun hz ↦ sub_ne_zero.1 (h2 hz), h3⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hall
  set r := ε / 2 with hr_def
  have hr : 0 < r := half_pos hε
  have hsub (z : ℂ) (hz : z ∈ closedBall z₀ r) : dist z z₀ < ε :=
    (mem_closedBall.1 hz).trans_lt (half_lt_self hε)
  have hfr : AnalyticOnNhd ℂ f (closedBall z₀ r) := fun z hz ↦ (hball (hsub z hz)).1
  have hisolr (z : ℂ) (hz : z ∈ closedBall z₀ r) (hzz : z ≠ z₀) : f z ≠ f z₀ :=
    (hball (hsub z hz)).2.1 hzz
  have hderivr (z : ℂ) (hz : z ∈ ball z₀ r) (hzz : z ≠ z₀) : deriv f z ≠ 0 :=
    (hball (hsub z (ball_subset_closedBall hz))).2.2 hzz
  -- Values within `δ₁` of `f z₀` have `m` distinct simple preimages in the open disc, and `f` stays
  -- at distance at least `δ₂` from `f z₀` on the circle.
  obtain ⟨δ₁, hδ₁, hcard⟩ := localDegree_card hr hfr hisolr hderivr
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_le_norm_of_mem_sphere (f := fun z ↦ f z - f z₀)
    (f.continuous.continuousOn.sub continuousOn_const) fun z hz ↦ sub_ne_zero.2
      (hisolr z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.ne'))
  obtain ⟨g, hgp, hgf, hgout⟩ := exists_isProperMap_eqOn_closedBall f hr hδ₂ hδ₂le
  have hgf_nhds (x : ℂ) (hx : x ∈ ball z₀ r) : g =ᶠ[𝓝 x] f :=
    eventually_of_mem (isOpen_ball.mem_nhds hx) fun _ hy ↦ hgf (ball_subset_closedBall hy)
  -- Outside the open disc `g` misses the ball of radius `δ₂` about `f z₀`.
  have hgball (z : ℂ) {w : ℂ} (hw : ‖w - f z₀‖ < δ₂) (hz : g z = w) : z ∈ ball z₀ r := by
    rw [mem_ball, dist_eq_norm]
    by_contra h
    exact (hgout z (not_lt.1 h)).not_gt (hz ▸ hw)
  -- The fibre of `g` over `f z₀` is `{z₀}`.
  have hfib₀ : g ⁻¹' {f z₀} = {z₀} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    refine ⟨fun hz ↦ ?_, fun hz ↦ by subst hz; exact hgf (mem_closedBall_self hr.le)⟩
    have hzb := ball_subset_closedBall (hgball z (by simpa using hδ₂) hz)
    by_contra hne
    exact hisolr z hzb hne ((hgf hzb).symm.trans hz)
  -- A value `w ≠ f z₀` close to `f z₀`, and its fibre under `g`.
  set w : ℂ := f z₀ + ((min δ₁ δ₂ / 2 : ℝ) : ℂ) with hw_def
  have hwnorm : ‖w - f z₀‖ = min δ₁ δ₂ / 2 := by
    rw [hw_def, add_sub_cancel_left, norm_real, Real.norm_of_nonneg
      (half_pos (lt_min hδ₁ hδ₂)).le]
  have hwne : w ≠ f z₀ := fun h ↦ by
    rw [h, sub_self, norm_zero] at hwnorm
    linarith [half_pos (lt_min hδ₁ hδ₂)]
  have hw₁ : ‖w - f z₀‖ < δ₁ := by
    rw [hwnorm]; linarith [min_le_left δ₁ δ₂, half_lt_self (lt_min hδ₁ hδ₂)]
  have hw₂ : ‖w - f z₀‖ < δ₂ := by
    rw [hwnorm]; linarith [min_le_right δ₁ δ₂, half_lt_self (lt_min hδ₁ hδ₂)]
  obtain ⟨hfin, hncard, -⟩ := hcard w hwne hw₁
  have hfibw : g ⁻¹' {w} = {z ∈ ball z₀ r | f z = w} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    refine ⟨fun hz ↦ ?_, fun hz ↦ (hgf (ball_subset_closedBall hz.1)).trans hz.2⟩
    have hzb := hgball z hw₂ hz
    exact ⟨hzb, (hgf (ball_subset_closedBall hzb)).symm.trans hz⟩
  have hfin' : (g ⁻¹' {w}).Finite := hfibw ▸ hfin
  -- The degree of `g` is its local index at `z₀`, which is that of `f` ...
  have hdeg₀ := o.localDegree_eq_degree o hE hE hgp (f z₀)
  rw [o.localDegree_eq_localIndex o hE hE g hfib₀,
    o.localIndex_congr o hE (hgf_nhds z₀ (mem_ball_self hr))] at hdeg₀
  -- ... and the number of preimages of `w`, each of local index `1`.
  rw [hdeg₀, ← o.localDegree_eq_degree o hE hE hgp w,
    o.localDegree_eq_sum_localIndex o hE hE g hfin',
    Finset.sum_congr rfl fun x hx ↦ ?_, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← ncard_eq_toFinset_card _ hfin', hfibw, hncard]
  rw [Finite.mem_toFinset, hfibw] at hx
  have hxz : x ≠ z₀ := fun h ↦ hwne (h ▸ hx.2).symm
  rw [o.localIndex_congr o hE (hgf_nhds x hx.1)]
  exact o.localIndex_eq_one_of_hasDerivAt
    (hfr x (ball_subset_closedBall hx.1)).differentiableAt.hasDerivAt (hderivr x hx.1 hxz)

/-- **Isolated zeros of holomorphic maps have positive local index.** If `f` is analytic at `z₀`
and not constant near `z₀`, its local index at `z₀` is a positive integer. -/
theorem localIndex_pos_of_analyticAt {f : C(ℂ, ℂ)} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hne : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ f z₀) : 0 < o.localIndex o f z₀ := by
  rw [o.localIndex_eq_analyticOrderNatAt hf, Nat.cast_pos]
  have htop : analyticOrderAt (fun z ↦ f z - f z₀) z₀ ≠ ⊤ := fun h ↦ by
    have h' := (eventually_nhdsWithin_of_eventually_nhds (analyticOrderAt_eq_top.1 h)).and hne
    obtain ⟨z, hz, hz'⟩ := h'.exists
    exact hz' (sub_eq_zero.1 hz)
  have hzero : analyticOrderAt (fun z ↦ f z - f z₀) z₀ ≠ 0 := by
    have hA : AnalyticAt ℂ (fun z ↦ f z - f z₀) z₀ := hf.sub analyticAt_const
    simp [analyticOrderAt_eq_zero, hA]
  exact Nat.pos_of_ne_zero fun h ↦ hzero ((ENat.toNat_eq_zero.1 h).resolve_right htop)

/-- The power map `z ↦ z ^ m` has local index `m` at `0`. -/
theorem localIndex_pow (m : ℕ) : o.localIndex o ⟨(· ^ m), continuous_pow m⟩ 0 = m := by
  rw [o.localIndex_eq_analyticOrderNatAt (analyticAt_id.pow m)]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [analyticOrderNatAt, analyticOrderAt_eq_top]
  · simp only [ContinuousMap.coe_mk]
    rw [analyticOrderNatAt, analyticOrderAt_pow_sub_zero_pow hm]
    rfl

end HomologicalOrientation

end TauCeti
