/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Topology.Maps.DomRestrict

/-!
# Open projections of zero sets with a nonvanishing vertical derivative

Write points of a cylinder `X × ℝ` as `(u, t)`, with base point `u` and height `t`. Let `F` be a
real function, continuous near a point `x`, which vanishes at `x` and whose restriction to the
vertical line through `x` has a nonzero derivative at `x`. Then `F` takes values of opposite signs
at two heights just below and just above `x`, hence also over every base point near the base
point of `x`; by the intermediate value theorem, the vertical segment over each such base point
meets the zero set of `F`. So the projection to the base of any neighbourhood of `x` in the zero
set of `F` is a neighbourhood of the base point of `x`
(`TauCeti.image_fst_inter_setOf_eq_zero_mem_nhds`). This is a purely topological form of the
implicit function theorem: no differentiability in the base direction, and no uniqueness of the
vertical zero, is needed.

Following Łojasiewicz, a set `Z ⊆ X × ℝ` has *property (P)* when the projection of each of its
relatively open subsets to the base is open, that is, when `Z.domRestrict Prod.fst` is an open map.
Now let `F₀, F₁, …, F_q` be functions on an open set `U ⊆ X × ℝ`, each of `F₀, …, F_{q-1}`
continuous on `U` and with vertical derivative the next one, and suppose that `F_q` vanishes
nowhere on `U`. Then the set of points of `U` at which one of `F₀, …, F_{q-1}` vanishes has
property (P) (`TauCeti.isOpenMap_domRestrict_fst_setOf_exists_eq_zero`). Indeed, at each of its
points `x`, the last of these functions vanishing at `x` has a nonvanishing vertical derivative
there. Applied to the successive vertical derivatives of a real analytic function, this gives
Łojasiewicz's lemma on hypersurfaces with property (P)
(`AnalyticAt.exists_isOpenMap_domRestrict_fst_setOf_mul_eq_zero`).

## Main results

* `TauCeti.image_fst_inter_setOf_eq_zero_mem_nhds`: near a zero with nonvanishing vertical
  derivative, the zero set projects onto a neighbourhood of the base point.
* `TauCeti.isOpenMap_domRestrict_fst_setOf_exists_eq_zero`: the set where some function of a chain
  of successive vertical derivatives ending in a nonvanishing function vanishes has property (P).

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §2 (property (P)).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- **Zeros with a nonvanishing vertical derivative persist over nearby base points.** Let
`F : X × ℝ → ℝ` be continuous near `x` and vanish at `x`, and let the restriction of `F` to the
vertical line through `x` have a nonzero derivative at `x`. Then for every neighbourhood `G` of
`x`, the projection to the base of the zeros of `F` in `G` is a neighbourhood of `x.1`. -/
theorem image_fst_inter_setOf_eq_zero_mem_nhds {F : X × ℝ → ℝ} {F' : ℝ} {x : X × ℝ}
    (hF : ∀ᶠ y in 𝓝 x, ContinuousAt F y) (hx : F x = 0)
    (hd : HasDerivAt (fun t ↦ F (x.1, t)) F' x.2) (hF' : F' ≠ 0) {G : Set (X × ℝ)}
    (hG : G ∈ 𝓝 x) : Prod.fst '' (G ∩ {y | F y = 0}) ∈ 𝓝 x.1 := by
  -- Along the vertical line through `x`, `F' • F` has positive derivative at its zero `x.2`, so
  -- its sign is that of `t - x.2` near `x.2`.
  have hsign : ∀ᶠ t in 𝓝 x.2, SignType.sign (F' * F (x.1, t)) = SignType.sign (t - x.2) := by
    refine eventually_nhdsWithin_sign_eq_of_deriv_pos ?_ (by simp [hx])
    rw [(hd.const_mul F').deriv]
    exact mul_self_pos.2 hF'
  -- A box `U ×ˢ T` around `x` inside `G`, on which `F` is continuous.
  obtain ⟨U, hU, T, hT, hUT⟩ := mem_nhds_prod_iff.1 (inter_mem hG hF)
  obtain ⟨r, hr, hrT⟩ := Metric.eventually_nhds_iff.1 (hsign.and hT)
  set a := x.2 - r / 2 with ha_def
  set b := x.2 + r / 2 with hb_def
  have hab : a ≤ b := by linarith
  have hsegment' {t : ℝ} (ht : t ∈ uIcc a b) : dist t x.2 < r := by
    rw [uIcc_of_le hab] at ht
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, ha_def, hb_def]
  have hsegment {t : ℝ} (ht : t ∈ uIcc a b) : t ∈ T := (hrT (hsegment' ht)).2
  have hcont {u : X} (hu : u ∈ U) {t : ℝ} (ht : t ∈ T) : ContinuousAt F (u, t) :=
    (hUT ⟨hu, ht⟩).2
  -- `F` has values of opposite signs at the ends of the vertical segment through `x`.
  have hneg : F (x.1, a) * F (x.1, b) < 0 := by
    have ha := (hrT (hsegment' left_mem_uIcc)).1
    have hb := (hrT (hsegment' right_mem_uIcc)).1
    rw [show a - x.2 = -(r / 2) by ring, sign_neg (show -(r / 2) < 0 by linarith),
      sign_eq_neg_one_iff] at ha
    rw [show b - x.2 = r / 2 by ring, sign_pos (show 0 < r / 2 by linarith), sign_eq_one_iff] at hb
    refine neg_of_mul_neg_right (a := F' * F') ?_ (mul_self_nonneg F')
    calc F' * F' * (F (x.1, a) * F (x.1, b)) = F' * F (x.1, a) * (F' * F (x.1, b)) := by ring
      _ < 0 := mul_neg_of_neg_of_pos ha hb
  -- By continuity, they still have opposite signs over every base point near `x.1`.
  have hends : ContinuousAt (fun u ↦ F (u, a) * F (u, b)) x.1 :=
    ((hcont (mem_of_mem_nhds hU) (hsegment left_mem_uIcc)).comp_of_eq
        (continuous_id.prodMk continuous_const).continuousAt rfl).mul
      ((hcont (mem_of_mem_nhds hU) (hsegment right_mem_uIcc)).comp_of_eq
        (continuous_id.prodMk continuous_const).continuousAt rfl)
  filter_upwards [hU, hends.eventually_lt continuousAt_const hneg] with u hu hu'
  -- The intermediate value theorem gives a zero of `F` on the vertical segment over `u`.
  have hIVT := intermediate_value_uIcc (a := a) (b := b) (f := fun t ↦ F (u, t))
    fun t ht ↦ ((hcont hu (hsegment ht)).comp_of_eq
      (continuous_const.prodMk continuous_id).continuousAt rfl).continuousWithinAt
  have h0 : (0 : ℝ) ∈ uIcc (F (u, a)) (F (u, b)) := by
    rcases mul_neg_iff.1 hu' with h | h
    · exact mem_uIcc.2 (Or.inr ⟨h.2.le, h.1.le⟩)
    · exact mem_uIcc.2 (Or.inl ⟨h.1.le, h.2.le⟩)
  obtain ⟨τ, hτ, hτ0⟩ := hIVT h0
  exact ⟨(u, τ), ⟨(hUT ⟨hu, hsegment hτ⟩).1, hτ0⟩, rfl⟩

/-- **Property (P) for a chain of vertical derivatives.** Let `F 0, F 1, …, F q` be functions on an
open set `U ⊆ X × ℝ` such that, for `k < q`, `F k` is continuous on `U` and has vertical derivative
`F (k + 1)` at every point of `U`, and such that `F q` vanishes nowhere on `U`. Then the projection
to the base of every relatively open subset of the set of points of `U` at which some `F k` with
`k < q` vanishes is open. -/
theorem isOpenMap_domRestrict_fst_setOf_exists_eq_zero {F : ℕ → X × ℝ → ℝ} {q : ℕ}
    {U : Set (X × ℝ)} (hU : IsOpen U) (hc : ∀ k < q, ContinuousOn (F k) U)
    (hd : ∀ k < q, ∀ x ∈ U, HasDerivAt (fun t ↦ F k (x.1, t)) (F (k + 1) x) x.2)
    (hq : ∀ x ∈ U, F q x ≠ 0) :
    IsOpenMap ({x ∈ U | ∃ k < q, F k x = 0}.domRestrict Prod.fst) := by
  refine isOpenMap_domRestrict_iff.2 ?_
  rintro x ⟨hxU, k, hk, hxk⟩ G hG
  -- The last function of the chain vanishing at `x` has a nonvanishing vertical derivative there.
  set j := Nat.findGreatest (fun i ↦ F i x = 0) q
  have hj : F j x = 0 := Nat.findGreatest_spec (P := fun i ↦ F i x = 0) hk.le hxk
  have hjq : j < q :=
    (Nat.findGreatest_le q).lt_of_ne fun h ↦ hq x hxU (h ▸ hj)
  have hj' : F (j + 1) x ≠ 0 := Nat.findGreatest_is_greatest (Nat.lt_succ_self j) hjq
  refine mem_of_superset (image_fst_inter_setOf_eq_zero_mem_nhds ?_ hj (hd j hjq x hxU) hj'
    (inter_mem hG (hU.mem_nhds hxU))) (image_mono ?_)
  · filter_upwards [hU.mem_nhds hxU] with y hy
    exact (hc j hjq).continuousAt (hU.mem_nhds hy)
  · rintro y ⟨⟨hyG, hyU⟩, hy⟩
    exact ⟨hyG, hyU, j, hjq, hy⟩

end TauCeti
