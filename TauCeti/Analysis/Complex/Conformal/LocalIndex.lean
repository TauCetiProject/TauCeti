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
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Holomorphic
import TauCeti.Analysis.Analytic.IsolatedCriticalPoints
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Complex.IsolatedZero

/-!
# The local index of a holomorphic map is its order of vanishing

Orient `ℂ`, regarded as a real manifold of dimension `2`, by a homological orientation `o`
(`TauCeti.HomologicalOrientation ℂ ℂ 2`), and use the same orientation on the source and the target
of a continuous map `f : ℂ → ℂ`, so that no choice of orientation enters. The topological local
index `o.localIndex o f z₀` (`TauCeti.HomologicalOrientation.localIndex`) of a map which is
analytic at `z₀` is the order of vanishing of `f - f z₀` at `z₀`
(`TauCeti.HomologicalOrientation.localIndex_eq_analyticOrderNatAt_sub`). In particular the local
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

The same statements hold for a map `f : M → N` read near a point `x` through open embeddings
`j : M → ℂ` and `k : N → ℂ`, oriented by pulling back `o`, as a map `φ : ℂ → ℂ` with
`φ (j z) = k (f z)` near `x`, such as a holomorphic function on a domain or a map of Riemann
surfaces read in local coordinates
(`TauCeti.HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub`): the local index
is computed for a map of `ℂ` agreeing with `φ` near `j x`
(`TauCeti.HomologicalOrientation.exists_eventuallyEq_and_localIndex_comap_eq`).

The proof of the general statement counts preimages. Choose a closed disc `D` around `z₀` on which
`f` is analytic, `z₀` is the only solution of `f z = f z₀`, and `f'` vanishes nowhere except
possibly at `z₀`. The local index of `f` at `z₀` is then the number of solutions in the disc of
`f z = w`, for any value `w` close to `f z₀` at whose solutions `f'` does not vanish
(`TauCeti.HomologicalOrientation.localIndex_eq_ncard_of_hasFDerivAt`). For `w ≠ f z₀` these are
the `m` distinct simple solutions of `f z = w` in the disc, with `m` the order of `f - f z₀` at
`z₀` (`TauCeti.localDegree_card`, a Rouché argument).

## Main results

* `TauCeti.HomologicalOrientation.localIndex_eq_one_of_hasDerivAt`: at a point with nonzero
  complex derivative the local index is `1`.
* `TauCeti.HomologicalOrientation.localIndex_eq_analyticOrderNatAt_sub`: the local index of a map
  analytic at `z₀` is the order of vanishing of `f - f z₀` at `z₀`.
* `TauCeti.HomologicalOrientation.localIndex_pos_iff_of_analyticAt`: it is positive exactly when
  `f` is not constant near `z₀`.
* `TauCeti.HomologicalOrientation.localIndex_pow`: `z ↦ z ^ m` has local index `m` at `0`.
* `TauCeti.HomologicalOrientation.localIndex_conj`: complex conjugation has local index `-1`.
* `TauCeti.HomologicalOrientation.localIndex_comap_eq_one_of_hasDerivAt`,
  `TauCeti.HomologicalOrientation.localIndex_comap_eq_analyticOrderNatAt_sub`,
  `TauCeti.HomologicalOrientation.localIndex_comap_pos_iff_of_analyticAt`: the same for maps
  read through open embeddings into `ℂ`, such as maps between open subsets of `ℂ`.

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
    (hc : c ≠ 0) : o.localIndex o f z = 1 :=
  o.localIndex_eq_one_of_hasFDerivAt finrank_real_complex hf.hasFDerivAt
    (smul_left_injective ℂ hc)

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
private theorem localIndex_eq_analyticOrderNatAt_sub_of_closedBall {f : C(ℂ, ℂ)} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hfr : AnalyticOnNhd ℂ f (closedBall z₀ r))
    (hisolr : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ f z₀)
    (hderivr : ∀ z ∈ ball z₀ r, z ≠ z₀ → deriv f z ≠ 0) :
    o.localIndex o f z₀ = analyticOrderNatAt (fun z ↦ f z - f z₀) z₀ := by
  -- Values within `δ₁` of `f z₀` have `m` distinct simple preimages in the open disc, and `f` stays
  -- at distance at least `δ₂` from `f z₀` on the circle.
  obtain ⟨δ₁, hδ₁, hcard⟩ := localDegree_card hr hfr hisolr hderivr
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_le_norm_of_mem_sphere (f := fun z ↦ f z - f z₀)
    (f.continuous.continuousOn.sub continuousOn_const) fun z hz ↦ sub_ne_zero.2
      (hisolr z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.ne'))
  -- A value `w ≠ f z₀` close to `f z₀`.
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
  obtain ⟨-, hncard, -⟩ := hcard w hwne hw₁
  -- The local index counts the solutions of `f z = w` in the disc, at each of which `f` has nonzero
  -- derivative.
  rw [o.localIndex_eq_ncard_of_hasFDerivAt finrank_real_complex hr hδ₂ hδ₂le
    (fun z hz hfz ↦ by_contra fun hne ↦ hisolr z (ball_subset_closedBall hz) hne hfz) hw₂
    (f' := fun z ↦ (1 : ℂ →L[ℂ] ℂ).smulRight (deriv f z))
    (fun z hz _ ↦ (hfr z (ball_subset_closedBall hz)).differentiableAt.hasDerivAt.hasFDerivAt)
    (fun z hz hfz ↦ smul_left_injective ℂ (hderivr z hz fun h ↦ hwne (h ▸ hfz).symm)), hncard]

/-- **The local index of a holomorphic map is its order of vanishing.** If `f : ℂ → ℂ` is analytic
at `z₀`, its local index at `z₀`, for the same orientation of `ℂ` on source and target, is the
order of vanishing of `f - f z₀` at `z₀`. Both sides are `0` when `f` is constant near `z₀`. -/
theorem localIndex_eq_analyticOrderNatAt_sub {f : C(ℂ, ℂ)} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) :
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
  exact localIndex_eq_analyticOrderNatAt_sub_of_closedBall o hr hfr hisolr hderivr

/-- **Positivity of the local index of a holomorphic map.** If `f` is analytic at `z₀`, its local
index at `z₀` is positive if and only if `f` is not constant near `z₀`. -/
theorem localIndex_pos_iff_of_analyticAt {f : C(ℂ, ℂ)} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    0 < o.localIndex o f z₀ ↔ ¬ EventuallyConst f (𝓝 z₀) := by
  rw [o.localIndex_eq_analyticOrderNatAt_sub hf, Nat.cast_pos, analyticOrderNatAt,
    eventuallyConst_iff_analyticOrderAt_sub_eq_top, Nat.pos_iff_ne_zero, ne_eq,
    ENat.toNat_eq_zero, not_or]
  have hA : AnalyticAt ℂ (fun z ↦ f z - f z₀) z₀ := hf.sub analyticAt_const
  exact and_iff_right (by simp [analyticOrderAt_eq_zero, hA])

/-- The power map `z ↦ z ^ m` has local index `m` at `0`. -/
@[simp]
theorem localIndex_pow (m : ℕ) : o.localIndex o ⟨(· ^ m), continuous_pow m⟩ 0 = m := by
  rw [o.localIndex_eq_analyticOrderNatAt_sub (analyticAt_id.pow m)]
  rcases eq_or_ne m 0 with rfl | hm
  · simp [analyticOrderNatAt]
  · simp only [ContinuousMap.coe_mk]
    rw [analyticOrderNatAt, analyticOrderAt_pow_sub_zero_pow hm, ENat.toNat_natCast]

/-! ### Maps read through open embeddings into `ℂ` -/

section OpenEmbedding

variable {M N : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [TopologicalSpace N]
  [T2Space N] [ChartedSpace ℂ N] {j : M → ℂ} (hj : IsOpenEmbedding j) {k : N → ℂ}
  (hk : IsOpenEmbedding k) {f : C(M, N)} {φ : ℂ → ℂ} {x : M}

/-- **Local index at a point with nonzero complex derivative, in open coordinates.** Let
`j : M → ℂ` and `k : N → ℂ` be open embeddings, with the orientations pulled back from `o`, and let
`f : M → N` be given near `x` by a map `φ : ℂ → ℂ`, so that `φ (j z) = k (f z)` near `x`. If `φ`
is complex differentiable at `j x` with nonzero derivative, then the local index of `f` at `x` is
`1`. -/
theorem localIndex_comap_eq_one_of_hasDerivAt (hφ : ∀ᶠ z in 𝓝 x, φ (j z) = k (f z)) {c : ℂ}
    (hd : HasDerivAt φ c (j x)) (hc : c ≠ 0) :
    (o.comap hj).localIndex (o.comap hk) f x = 1 := by
  obtain ⟨G, hGφ, h⟩ :=
    o.exists_eventuallyEq_and_localIndex_comap_eq o finrank_real_complex hj hk hφ
  rw [h, o.localIndex_eq_one_of_hasDerivAt (hd.congr_of_eventuallyEq hGφ) hc]

/-- **The local index of a holomorphic map is its order of vanishing, in open coordinates.** Let
`j : M → ℂ` and `k : N → ℂ` be open embeddings, with the orientations pulled back from `o`, and let
`f : M → N` be given near `x` by a map `φ : ℂ → ℂ`, so that `φ (j z) = k (f z)` near `x`. If `φ`
is analytic at `j x`, then the local index of `f` at `x` is the order of vanishing of `φ - φ (j x)`
at `j x`. -/
theorem localIndex_comap_eq_analyticOrderNatAt_sub (hφ : ∀ᶠ z in 𝓝 x, φ (j z) = k (f z))
    (hd : AnalyticAt ℂ φ (j x)) :
    (o.comap hj).localIndex (o.comap hk) f x =
      analyticOrderNatAt (fun z ↦ φ z - φ (j x)) (j x) := by
  obtain ⟨G, hGφ, h⟩ :=
    o.exists_eventuallyEq_and_localIndex_comap_eq o finrank_real_complex hj hk hφ
  have hsub : (fun z ↦ G z - G (j x)) =ᶠ[𝓝 (j x)] fun z ↦ φ z - φ (j x) := by
    filter_upwards [hGφ] with z hz
    rw [hz, hGφ.eq_of_nhds]
  rw [h, o.localIndex_eq_analyticOrderNatAt_sub (hd.congr hGφ.symm), analyticOrderNatAt,
    analyticOrderNatAt, analyticOrderAt_congr hsub]

/-- **Positivity of the local index of a holomorphic map, in open coordinates.** Let `j : M → ℂ`
and `k : N → ℂ` be open embeddings, with the orientations pulled back from `o`, and let `f : M → N`
be given near `x` by a map `φ : ℂ → ℂ`, so that `φ (j z) = k (f z)` near `x`. If `φ` is analytic at
`j x`, then the local index of `f` at `x` is positive if and only if `φ` is not constant near
`j x`. -/
theorem localIndex_comap_pos_iff_of_analyticAt (hφ : ∀ᶠ z in 𝓝 x, φ (j z) = k (f z))
    (hd : AnalyticAt ℂ φ (j x)) :
    0 < (o.comap hj).localIndex (o.comap hk) f x ↔ ¬ EventuallyConst φ (𝓝 (j x)) := by
  obtain ⟨G, hGφ, h⟩ :=
    o.exists_eventuallyEq_and_localIndex_comap_eq o finrank_real_complex hj hk hφ
  rw [h, o.localIndex_pos_iff_of_analyticAt (hd.congr hGφ.symm), hGφ.eventuallyConst_iff]

end OpenEmbedding

end HomologicalOrientation

end TauCeti
