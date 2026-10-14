/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Data.Set.Card

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Maps that are locally the power map `w ↦ w ^ e`

A map `f : X → Y` is *locally the `e`-th power map at `x`* (`TauCeti.IsLocalPowerAt f x e`) if, in
some chart `φ : X → ℂ` centred at `x` and some chart `ψ : Y → ℂ` centred at `f x`, it reads as
`w ↦ w ^ e`. This is the local model of a topological branched covering of surfaces at a point of
local degree `e`: unbranched points are those with `e = 1`, and a branch point of a branched
covering of the sphere has some `e > 1` there.

The charts are only homeomorphisms onto open subsets of `ℂ`, with no compatibility between them,
so the exponent cannot be read off as an order of vanishing. It is nevertheless a topological
invariant of `f` at `x`, because it counts preimages: on every small enough neighbourhood `V` of
`x`, every point `y ≠ f x` close enough to `f x` has exactly `e` preimages in `V`
(`TauCeti.IsLocalPowerAt.exists_ncard_inter_preimage_eq`). Two pairs of charts exhibiting `f` as a
power map at `x` therefore exhibit the same power (`TauCeti.IsLocalPowerAt.unique`). The same count
is what adds up the local degrees over a fibre of a finite branched covering.

## Main definitions

* `TauCeti.IsLocalPowerAt f x e`: `f` is `w ↦ w ^ e` near `x`, in charts centred at `x` and
  `f x`.

## Main results

* `TauCeti.IsLocalPowerAt.ne_zero`: the exponent is positive.
* `TauCeti.IsLocalPowerAt.eventually_ne`: `x` is isolated in its fibre.
* `TauCeti.IsLocalPowerAt.exists_ncard_inter_preimage_eq`: the exponent counts the preimages near
  `x` of the points near `f x`.
* `TauCeti.IsLocalPowerAt.unique`: the exponent is determined by `f` and `x`.
* `TauCeti.IsLocalPowerAt.comp_homeomorph`: invariance under a homeomorphism of the source.
* `IsLocalHomeomorphOn.isLocalPowerAt_one`: a local homeomorphism is locally the first power map
  wherever the target has a chart.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Theorem 2.1 (the local model `z ↦ z ^ k`) and §4 (its exponent as a local preimage count).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {x : X} {e : ℕ}

/-- The map `f` is **locally the `e`-th power map at `x`**: there are a chart `φ` of `X` centred at
`x` and a chart `ψ` of `Y` centred at `f x` such that `ψ (f (φ.symm w)) = w ^ e` for every `w` in
the image of `φ`. The exponent is positive (`TauCeti.IsLocalPowerAt.ne_zero`) and, for `f`
continuous at `x`, unique (`TauCeti.IsLocalPowerAt.unique`). -/
def IsLocalPowerAt (f : X → Y) (x : X) (e : ℕ) : Prop :=
  ∃ (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph Y ℂ),
    x ∈ φ.source ∧ f x ∈ ψ.source ∧ φ x = 0 ∧ ψ (f x) = 0 ∧
      ∀ w ∈ φ.target, ψ (f (φ.symm w)) = w ^ e

/-- Unfolding `TauCeti.IsLocalPowerAt`. -/
theorem isLocalPowerAt_iff :
    IsLocalPowerAt f x e ↔ ∃ (φ : OpenPartialHomeomorph X ℂ) (ψ : OpenPartialHomeomorph Y ℂ),
      x ∈ φ.source ∧ f x ∈ ψ.source ∧ φ x = 0 ∧ ψ (f x) = 0 ∧
        ∀ w ∈ φ.target, ψ (f (φ.symm w)) = w ^ e :=
  Iff.rfl

namespace IsLocalPowerAt

/-- The exponent of a local power map is positive: `w ↦ w ^ 0` does not vanish at `0`. -/
theorem ne_zero (h : IsLocalPowerAt f x e) : e ≠ 0 := by
  obtain ⟨φ, ψ, hx, -, hφx, hψx, hpow⟩ := h
  rintro rfl
  have h0 := hpow 0 (hφx ▸ φ.map_source hx)
  rw [← hφx, φ.left_inv hx, hψx, pow_zero] at h0
  exact zero_ne_one h0

/-- The value `f x` is not isolated in the target of a local power map. -/
theorem nhdsNE_neBot (h : IsLocalPowerAt f x e) : (𝓝[≠] f x).NeBot := by
  obtain ⟨-, ψ, -, hψ, -⟩ := h
  exact ψ.nhdsNE_neBot hψ

/-- A point at which `f` is locally a power map is isolated in its fibre. -/
theorem eventually_ne (h : IsLocalPowerAt f x e) : ∀ᶠ x' in 𝓝[≠] x, f x' ≠ f x := by
  have he := h.ne_zero
  obtain ⟨φ, ψ, hx, -, hφx, hψx, hpow⟩ := h
  filter_upwards [nhdsWithin_le_nhds (φ.open_source.mem_nhds hx), self_mem_nhdsWithin]
    with x' hx' hne heq
  refine hne (φ.injOn hx' hx ?_)
  rw [hφx, ← pow_eq_zero_iff he, ← hpow _ (φ.map_source hx'), φ.left_inv hx', heq, hψx]

/-- **The exponent counts preimages.** If `f` is locally the `e`-th power map at `x` and continuous
there, then inside any neighbourhood `N` of `x` there is an open neighbourhood `V` of `x` such that
every point `y ≠ f x` close enough to `f x` has exactly `e` preimages in `V`. -/
theorem exists_ncard_inter_preimage_eq (h : IsLocalPowerAt f x e) (hf : ContinuousAt f x)
    {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ V ⊆ N, IsOpen V ∧ x ∈ V ∧ ∀ᶠ y in 𝓝[≠] f x, (V ∩ f ⁻¹' {y}).ncard = e := by
  classical
  have he := h.ne_zero
  obtain ⟨φ, ψ, hx, hψ, hφx, hψx, hpow⟩ := h
  have h0 : (0 : ℂ) ∈ φ.target := hφx ▸ φ.map_source hx
  have hsymm0 : φ.symm 0 = x := by rw [← hφx, φ.left_inv hx]
  -- A radius `r` such that the disc `ball 0 r` lies in the chart, inside `N`, and over `ψ`.
  have hmem : {w | w ∈ φ.target ∧ φ.symm w ∈ N ∧ f (φ.symm w) ∈ ψ.source} ∈ 𝓝 (0 : ℂ) := by
    have hc : ContinuousAt φ.symm 0 := φ.continuousAt_symm h0
    rw [← hsymm0] at hN hψ hf
    exact inter_mem (φ.open_target.mem_nhds h0)
      (inter_mem (hc.preimage_mem_nhds hN) ((hf.comp hc).preimage_mem_nhds
        (ψ.open_source.mem_nhds hψ)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨φ.source ∩ φ ⁻¹' Metric.ball 0 r, ?_, φ.isOpen_inter_preimage Metric.isOpen_ball,
    ⟨hx, by simpa [hφx] using hr⟩, ?_⟩
  · rintro x' ⟨hx', hx'r⟩
    simpa only [φ.left_inv hx'] using (hball hx'r).2.1
  have hsmall : ∀ᶠ y in 𝓝 (f x), y ∈ ψ.source ∧ ψ y ∈ Metric.ball (0 : ℂ) (r ^ e) :=
    Eventually.and (ψ.open_source.mem_nhds hψ) ((ψ.continuousAt hψ).preimage_mem_nhds
      (by rw [hψx]; exact Metric.ball_mem_nhds _ (pow_pos hr e)))
  filter_upwards [nhdsWithin_le_nhds hsmall, self_mem_nhdsWithin] with y ⟨hy, hyr⟩ hne
  have hψy : ψ y ≠ 0 := fun h0 => hne (ψ.injOn hy hψ (h0.trans hψx.symm))
  -- The chart `φ` maps the preimages of `y` in `V` onto the `e`-th roots of `ψ y`.
  have himage : φ '' (φ.source ∩ φ ⁻¹' Metric.ball 0 r ∩ f ⁻¹' {y}) =
      (Polynomial.nthRootsFinset e (ψ y) : Set ℂ) := by
    ext w
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero he)]
    constructor
    · rintro ⟨x', ⟨⟨hx', -⟩, hfx'⟩, rfl⟩
      rw [← hpow _ (φ.map_source hx'), φ.left_inv hx', mem_singleton_iff.1 hfx']
    · intro hw
      have hwr : w ∈ Metric.ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff] at hyr ⊢
        rw [← pow_lt_pow_iff_left₀ (norm_nonneg w) hr.le he, ← norm_pow, hw]
        exact hyr
      obtain ⟨hwt, -, hfw⟩ := hball hwr
      refine ⟨φ.symm w, ⟨⟨φ.map_target hwt, ?_⟩, ?_⟩, φ.right_inv hwt⟩
      · rwa [mem_preimage, φ.right_inv hwt]
      · exact ψ.injOn hfw hy ((hpow w hwt).trans hw)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (ψ y) (Nat.pos_of_ne_zero he)
  rw [← (φ.injOn.mono fun _ hx' => hx'.1.1).ncard_image, himage, Set.ncard_coe_finset,
    (Complex.isPrimitiveRoot_exp e he).card_nthRootsFinset_of_pow_eq hα hψy]

/-- **The exponent of a local power map is unique**: if `f` is continuous at `x`, two pairs of
charts exhibiting `f` near `x` as `w ↦ w ^ e` and as `w ↦ w ^ e'` have `e = e'`. -/
theorem unique {e' : ℕ} (h : IsLocalPowerAt f x e) (h' : IsLocalPowerAt f x e')
    (hf : ContinuousAt f x) : e = e' := by
  suffices key : ∀ {e e' : ℕ}, IsLocalPowerAt f x e → IsLocalPowerAt f x e' → e ≤ e' from
    (key h h').antisymm (key h' h)
  intro e e' h h'
  obtain ⟨V', -, hV'o, hxV', hV'⟩ := h'.exists_ncard_inter_preimage_eq hf univ_mem
  obtain ⟨V, hVV', -, -, hV⟩ := h.exists_ncard_inter_preimage_eq hf (hV'o.mem_nhds hxV')
  have := h.nhdsNE_neBot
  obtain ⟨y, hy, hy'⟩ := (hV.and hV').exists
  rw [← hy, ← hy']
  exact Set.ncard_le_ncard (inter_subset_inter_left _ hVV')
    (Set.finite_of_ncard_ne_zero (hy' ▸ h'.ne_zero))

/-- Being locally a power map is invariant under a homeomorphism of the source. -/
theorem comp_homeomorph {X' : Type*} [TopologicalSpace X'] (g : X' ≃ₜ X) {x' : X'}
    (h : IsLocalPowerAt f (g x') e) : IsLocalPowerAt (f ∘ g) x' e := by
  obtain ⟨φ, ψ, hx, hψ, hφx, hψx, hpow⟩ := h
  refine ⟨g.toOpenPartialHomeomorph.trans φ, ψ, by simpa using hx, hψ, hφx, hψx, fun w hw => ?_⟩
  simp only [OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    preimage_univ, inter_univ] at hw
  simpa using hpow w hw

end IsLocalPowerAt

end TauCeti

open TauCeti

/-- **A local homeomorphism is locally the first power map** at every point of `s` whose image
lies in the source of some chart `ψ` of the target. -/
theorem IsLocalHomeomorphOn.isLocalPowerAt_one {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {s : Set X} {x : X} (hf : IsLocalHomeomorphOn f s)
    (hx : x ∈ s) {ψ : OpenPartialHomeomorph Y ℂ} (hψ : f x ∈ ψ.source) :
    IsLocalPowerAt f x 1 := by
  obtain ⟨φ, hxφ, rfl⟩ := hf x hx
  -- Recentre `ψ` at `φ x` by a translation of `ℂ`.
  set τ := ψ.trans (Homeomorph.addRight (-ψ (φ x))).toOpenPartialHomeomorph
  have hτ : τ.source = ψ.source := by simp [τ]
  refine ⟨φ.trans τ, τ, by simpa [hτ] using ⟨hxφ, hψ⟩, hτ ▸ hψ, by simp [τ], by simp [τ],
    fun w hw => ?_⟩
  rw [OpenPartialHomeomorph.trans_target] at hw
  rw [OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply, φ.right_inv hw.2,
    τ.right_inv hw.1, pow_one]
