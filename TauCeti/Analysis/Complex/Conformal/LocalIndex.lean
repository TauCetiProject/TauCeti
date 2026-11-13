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
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.Determinant
import TauCeti.Analysis.Normed.Module.Ball.Radial.ProperExtension

/-!
# The local index of a holomorphic map is its order of vanishing

Orient `ℂ`, regarded as a real manifold of dimension `2`, by a homological orientation `o`
(`TauCeti.HomologicalOrientation ℂ ℂ 2`), and use the same orientation on the source and the target
of a continuous map `f : ℂ → ℂ`, so that no choice of orientation enters. The topological local
index `o.localIndex o f z₀` (`TauCeti.HomologicalOrientation.localIndex`) of a map which is
analytic at `z₀` is the order of vanishing of `f - f z₀` at `z₀`
(`TauCeti.HomologicalOrientation.localIndex_eq_analyticOrderNatAt`). In particular the local
index of a holomorphic map at `z₀` is positive exactly when the map is not constant near `z₀`
(`TauCeti.HomologicalOrientation.localIndex_pos_iff_of_analyticAt`): the zeros of a holomorphic
function which is not locally constant carry positive topological multiplicities, which are the
zero orders. This is
the input that compares the zero orders of a holomorphic section with its topological local
indices, and so with the signed count of the zeros of a transverse section.

At a point where `f` is complex differentiable with nonzero derivative `c`, its real derivative is
multiplication by `c`, of determinant `‖c‖² > 0`, so the local index is `1`
(`TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasDerivAt`). This is not true of every map
with invertible derivative: complex conjugation has local index `-1`
(`TauCeti.HomologicalOrientation.localIndex_conj`), so the statements here depend on `f` being
holomorphic, not only on the orientation being the same on both sides.

The same statements hold for a map `f : U → V` between open subsets of `ℂ`, oriented by restricting
`o`, which agrees on `U` with a map `φ : ℂ → ℂ`, such as a holomorphic function on a domain read in
local coordinates (`TauCeti.HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt`): the
local index is computed for a map of `ℂ` agreeing with `φ` near the point
(`TauCeti.HomologicalOrientation.exists_localIndex_comap_eq`).

The proof of the general statement counts preimages. Choose a closed disc `D` around `z₀` on which
`f` is analytic, `z₀` is the only solution of `f z = f z₀`, and `f'` vanishes nowhere except
possibly at `z₀`. Extend `f|_D` radially to a proper map `g : ℂ → ℂ` whose values outside the open
disc stay a fixed distance away from `f z₀` (`ContinuousOn.exists_isProperMap_eqOn_closedBall`).
The degree of `g` is its local index at `z₀`, the only preimage of `f z₀`, which is the local index
of `f`. At a value `w ≠ f z₀` close to `f z₀`, the preimages of `w` under `g` are the `m` distinct
simple solutions of `f z = w` in the disc, with `m` the order of `f - f z₀` at `z₀`
(`TauCeti.localDegree_card`, a Rouché argument). Each has local index `1`, so the degree of `g` is
also `m`.

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasDerivAt`: at a point with nonzero
  complex derivative the local index is `1`.
* `TauCeti.HomologicalOrientation.localIndex_eq_analyticOrderNatAt`: the local index of a map
  analytic at `z₀` is the order of vanishing of `f - f z₀` at `z₀`.
* `TauCeti.HomologicalOrientation.localIndex_pos_iff_of_analyticAt`: it is positive exactly when
  `f` is not constant near `z₀`.
* `TauCeti.HomologicalOrientation.localIndex_pow_zero`: `z ↦ z ^ m` has local index `m` at `0`.
* `TauCeti.HomologicalOrientation.localIndex_conj`: complex conjugation has local index `-1`.
* `TauCeti.HomologicalOrientation.localIndex_comap_eq_one_of_hasDerivAt`,
  `TauCeti.HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt`,
  `TauCeti.HomologicalOrientation.localIndex_comap_pos_iff_of_analyticAt`: the same for maps
  between open subsets of `ℂ`.

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

/-- **Local index at a point with nonzero complex derivative is `1`.** If `f` is complex
differentiable at `z` with nonzero derivative `c`, its local index at `z` is `1`: the real
derivative is multiplication by `c`, whose Jacobian determinant `‖c‖²` is positive. -/
theorem localIndex_eq_one_of_hasDerivAt {f : C(ℂ, ℂ)} {c z : ℂ} (hf : HasDerivAt f c z)
    (hc : c ≠ 0) : o.localIndex o f z = 1 := by
  have hdet : ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
    simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using
      ContinuousLinearMap.det_restrictScalars_smulRight_one c
  have hpos : 0 < ‖c‖ ^ 2 := pow_pos (norm_pos_iff.2 hc) 2
  rw [o.localIndex_eq_sign_det finrank_real_complex (hf.hasFDerivAt.restrictScalars ℝ)
    (hdet ▸ hpos.ne'), hdet, sign_pos hpos, SignType.coe_one]

/-- **Complex conjugation reverses orientation**: it has local index `-1` at every point, for the
same orientation of `ℂ` on source and target. -/
@[simp]
theorem localIndex_conj (z : ℂ) :
    o.localIndex o ⟨starRingEnd ℂ, continuous_conj⟩ z = -1 := by
  have hdet : (conjCLE : ℂ →L[ℝ] ℂ).det = -1 := by simp [ContinuousLinearMap.det]
  have hderiv : HasFDerivAt (starRingEnd ℂ) (conjCLE : ℂ →L[ℝ] ℂ) z :=
    conjCLE.hasFDerivAt.congr_of_eventuallyEq (.of_forall conjCLE_apply)
  rw [o.localIndex_eq_sign_det finrank_real_complex (f := ⟨starRingEnd ℂ, continuous_conj⟩)
    hderiv (by rw [hdet]; norm_num), hdet]
  simp

/-- The local index of `f` at `z₀` is the order of vanishing of `f - f z₀` at `z₀`, given a closed
disc about `z₀` on which `f` is analytic, `z₀` is the only solution of `f z = f z₀`, and `f'`
vanishes nowhere except possibly at `z₀`. -/
private theorem localIndex_eq_analyticOrderNatAt_of_closedBall {f : C(ℂ, ℂ)} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hfr : AnalyticOnNhd ℂ f (closedBall z₀ r))
    (hisolr : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀)
    (hderivr : ∀ z ∈ ball z₀ r, z ≠ z₀ → deriv f z ≠ 0) :
    o.localIndex o f z₀ = analyticOrderNatAt (fun z ↦ f z - f z₀) z₀ := by
  have hE : finrank ℝ ℂ = 2 := finrank_real_complex
  -- Values within `δ₁` of `f z₀` have `m` distinct simple preimages in the open disc, and `f` stays
  -- at distance at least `δ₂` from `f z₀` on the circle.
  obtain ⟨δ₁, hδ₁, hcard⟩ := localDegree_card hr hfr hisolr hderivr
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_le_norm_of_mem_sphere (f := fun z ↦ f z - f z₀)
    (f.continuous.continuousOn.sub continuousOn_const) fun z hz ↦ sub_ne_zero.2
      (hisolr z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.ne'))
  obtain ⟨g, hgp, hgf, hgout⟩ :=
    f.continuous.continuousOn.exists_isProperMap_eqOn_closedBall hr hδ₂ hδ₂le
  have hgf_nhds (x : ℂ) (hx : x ∈ ball z₀ r) : g =ᶠ[𝓝 x] f :=
    eventually_of_mem (isOpen_ball.mem_nhds hx) fun _ hy ↦ hgf (ball_subset_closedBall hy)
  -- Outside the open disc `g` misses the ball of radius `δ₂` about `f z₀`, so the fibres of `g`
  -- over that ball are the solutions of `f z = w` in the open disc.
  have hgfib {w : ℂ} (hw : ‖w - f z₀‖ < δ₂) : g ⁻¹' {w} = {z ∈ ball z₀ r | f z = w} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    refine ⟨fun hz ↦ ?_, fun hz ↦ (hgf (ball_subset_closedBall hz.1)).trans hz.2⟩
    have hzb : z ∈ ball z₀ r := mem_ball.2 (not_le.1 fun h ↦ (hgout z h).not_gt (hz ▸ hw))
    exact ⟨hzb, (hgf (ball_subset_closedBall hzb)).symm.trans hz⟩
  have hfib₀ : g ⁻¹' {f z₀} = {z₀} := by
    rw [hgfib (by simpa using hδ₂)]
    ext z
    refine ⟨fun hz ↦ mem_singleton_iff.2 ?_, fun hz ↦ ?_⟩
    · by_contra hne
      exact hisolr z (ball_subset_closedBall hz.1) hne hz.2
    · rw [mem_singleton_iff.1 hz]
      exact ⟨mem_ball_self hr, rfl⟩
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
  have hfibw := hgfib hw₂
  have hfin' : (g ⁻¹' {w}).Finite := hfibw ▸ hfin
  -- The degree of `g` is its local index at `z₀`, which is that of `f` ...
  have hdeg₀ := o.localDegree_eq_degree o hE hE hgp (f z₀)
  rw [o.localDegree_eq_localIndex o hE hE g hfib₀,
    o.localIndex_congr o hE (hgf_nhds z₀ (mem_ball_self hr))] at hdeg₀
  -- ... and the number of preimages of `w`, each of local index `1`.
  have hidx (x : ℂ) (hx : x ∈ hfin'.toFinset) : o.localIndex o g x = 1 := by
    rw [Finite.mem_toFinset, hfibw] at hx
    have hxz : x ≠ z₀ := fun h ↦ hwne (h ▸ hx.2).symm
    rw [o.localIndex_congr o hE (hgf_nhds x hx.1)]
    exact o.localIndex_eq_one_of_hasDerivAt
      (hfr x (ball_subset_closedBall hx.1)).differentiableAt.hasDerivAt (hderivr x hx.1 hxz)
  rw [hdeg₀, o.degree_eq_sum_localIndex o hE hE hgp hfin', Finset.sum_eq_card_nsmul hidx,
    ← ncard_eq_toFinset_card _ hfin', hfibw, hncard, nsmul_one]

/-- **The local index of a holomorphic map is its order of vanishing.** If `f : ℂ → ℂ` is analytic
at `z₀`, its local index at `z₀`, for the same orientation of `ℂ` on source and target, is the
order of vanishing of `f - f z₀` at `z₀`. Both sides are `0` when `f` is constant near `z₀`. -/
theorem localIndex_eq_analyticOrderNatAt {f : C(ℂ, ℂ)} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    o.localIndex o f z₀ = analyticOrderNatAt (fun z ↦ f z - f z₀) z₀ := by
  rcases hf.eventually_eq_or_eventually_ne analyticAt_const with hconst | hisol
  · -- `f` is constant near `z₀`: `z₀` is not isolated in its fibre, and the order is infinite.
    have htop : analyticOrderAt (fun z ↦ f z - f z₀) z₀ = ⊤ :=
      analyticOrderAt_eq_top.2 (hconst.mono fun _ h ↦ sub_eq_zero.2 h)
    rw [o.localIndex_of_frequently_eq o f
      (eventually_nhdsWithin_of_eventually_nhds hconst).frequently, analyticOrderNatAt, htop,
      ENat.toNat_top, Nat.cast_zero]
  -- A closed disc on which `f` is analytic, `z₀` is the only solution of `f z = f z₀`, and `f'`
  -- vanishes nowhere except possibly at `z₀`.
  obtain ⟨r, ⟨hfr, hisolr, hderivr⟩, hr⟩ :=
    ((hf.eventually_analyticOnNhd_closedBall_and_ne_and_deriv_ne_zero hisol).and
      self_mem_nhdsWithin).exists
  exact localIndex_eq_analyticOrderNatAt_of_closedBall o hr hfr hisolr hderivr

/-- **Positivity of the local index of a holomorphic map.** If `f` is analytic at `z₀`, its local
index at `z₀` is positive if and only if `f` is not constant near `z₀`. -/
theorem localIndex_pos_iff_of_analyticAt {f : C(ℂ, ℂ)} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    0 < o.localIndex o f z₀ ↔ ¬ EventuallyConst f (𝓝 z₀) := by
  rw [o.localIndex_eq_analyticOrderNatAt hf, Nat.cast_pos, analyticOrderNatAt,
    eventuallyConst_iff_analyticOrderAt_sub_eq_top, Nat.pos_iff_ne_zero, ne_eq,
    ENat.toNat_eq_zero, not_or]
  have hA : AnalyticAt ℂ (fun z ↦ f z - f z₀) z₀ := hf.sub analyticAt_const
  exact and_iff_right (by simp [analyticOrderAt_eq_zero, hA])

/-- The power map `z ↦ z ^ m` has local index `m` at `0`. -/
@[simp]
theorem localIndex_pow_zero (m : ℕ) : o.localIndex o ⟨(· ^ m), continuous_pow m⟩ 0 = m := by
  rw [o.localIndex_eq_analyticOrderNatAt (analyticAt_id.pow m)]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [analyticOrderNatAt]
  · simp only [ContinuousMap.coe_mk]
    rw [analyticOrderNatAt, analyticOrderAt_pow_sub_zero_pow hm, ENat.toNat_natCast]

/-! ### Maps between open subsets of `ℂ` -/

/-- **Local index at a point with nonzero complex derivative, between open subsets.** Let `U` and
`V` be open subsets of `ℂ`, oriented by restricting `o`, and let `f : U → V` agree on `U` with a
map `φ : ℂ → ℂ` which is complex differentiable at `x` with nonzero derivative. Then the local index
of `f` at `x` is `1`. -/
theorem localIndex_comap_eq_one_of_hasDerivAt {U V : TopologicalSpace.Opens ℂ} {f : C(U, V)}
    {φ : ℂ → ℂ} (hφ : ∀ z : U, φ z = f z) {c : ℂ} {x : U} (hd : HasDerivAt φ c x) (hc : c ≠ 0) :
    (o.comap U.isOpenEmbedding').localIndex (o.comap V.isOpenEmbedding') f x = 1 := by
  obtain ⟨G, hGφ, h⟩ := o.exists_localIndex_comap_eq finrank_real_complex hφ x
  rw [h, o.localIndex_eq_one_of_hasDerivAt (hd.congr_of_eventuallyEq hGφ) hc]

/-- **The local index of a holomorphic map between open subsets is its order of vanishing.** Let
`U` and `V` be open subsets of `ℂ`, oriented by restricting `o`, and let `f : U → V` agree on `U`
with a map `φ : ℂ → ℂ` which is analytic at `x`. Then the local index of `f` at `x` is the order of
vanishing of `φ - φ x` at `x`. -/
theorem localIndex_comap_eq_analyticOrderNatAt {U V : TopologicalSpace.Opens ℂ} {f : C(U, V)}
    {φ : ℂ → ℂ} (hφ : ∀ z : U, φ z = f z) {x : U} (hd : AnalyticAt ℂ φ x) :
    (o.comap U.isOpenEmbedding').localIndex (o.comap V.isOpenEmbedding') f x =
      analyticOrderNatAt (fun z ↦ φ z - φ x) x := by
  obtain ⟨G, hGφ, h⟩ := o.exists_localIndex_comap_eq finrank_real_complex hφ x
  have hsub : (fun z ↦ G z - G x) =ᶠ[𝓝 (x : ℂ)] fun z ↦ φ z - φ x := by
    filter_upwards [hGφ] with z hz
    rw [hz, hGφ.eq_of_nhds]
  rw [h, o.localIndex_eq_analyticOrderNatAt (hd.congr hGφ.symm), analyticOrderNatAt,
    analyticOrderNatAt, analyticOrderAt_congr hsub]

/-- **Positivity of the local index of a holomorphic map between open subsets.** Let `U` and `V` be
open subsets of `ℂ`, oriented by restricting `o`, and let `f : U → V` agree on `U` with a map
`φ : ℂ → ℂ` which is analytic at `x`. Then the local index of `f` at `x` is positive if and only if
`φ` is not constant near `x`. -/
theorem localIndex_comap_pos_iff_of_analyticAt {U V : TopologicalSpace.Opens ℂ} {f : C(U, V)}
    {φ : ℂ → ℂ} (hφ : ∀ z : U, φ z = f z) {x : U} (hd : AnalyticAt ℂ φ x) :
    0 < (o.comap U.isOpenEmbedding').localIndex (o.comap V.isOpenEmbedding') f x ↔
      ¬ EventuallyConst φ (𝓝 (x : ℂ)) := by
  obtain ⟨G, hGφ, h⟩ := o.exists_localIndex_comap_eq finrank_real_complex hφ x
  rw [h, o.localIndex_pos_iff_of_analyticAt (hd.congr hGφ.symm), hGφ.eventuallyConst_iff]

end HomologicalOrientation

end TauCeti
