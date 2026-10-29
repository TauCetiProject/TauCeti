/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.Order.IntermediateValue

/-!
# Curves tending to a circle cross the rays of an arc

Let `γ` be a curve, parametrised by an interval `(a, b)`, that tends to the circle `sphere c R`
from inside as `t → b`. If `γ` does not converge, it clusters at two distinct points of the
circle. Then for every angle `θ` of one of the two open arcs between them, `γ` meets the ray
`{circleMap c r θ | 0 < r}` at parameters arbitrarily close to `b`, hence at radii arbitrarily
close to `R`. Consequently a function `f` with a limit `w` along `γ` has radial limit `w` at every
angle of that arc where it has a radial limit at all.

This is the crossing step in the proof that the preimage under a conformal map of the disc of a
curve ending at a boundary point ends at a single point of the circle. Were the preimage not to
end at a point, the map would have the end point as radial limit at every angle of an arc where
it has a radial limit at all. Conformal maps onto bounded domains have radial limits at almost
every angle, and a bounded holomorphic function with the same radial limit on a set of angles of
positive measure is constant (`TauCeti.eqOn_const_ball_of_tendsto_circleMap`).

The rays are the sets `(circleMap c · θ) '' Ioi 0`. The proof measures angles from the ray at an
angle `θ'` the curve eventually avoids, through `arg (-((z - c) * exp (-(θ' * I))))`. This is
continuous off that ray and the centre, so if `γ` also eventually avoids a second ray between the
two cluster points, the intermediate value theorem confines a tail of `γ` to one side of it.

## Main results

* `TauCeti.frequently_mem_image_circleMap_Ioi_or_frequently_mem_image_circleMap_Ioi` — a curve
  clustering at points of the rays at angles `θ₁ < θ₂` meets, arbitrarily late, the ray at any
  `θ ∈ (θ₁, θ₂)` or the ray at any `θ' ∈ (θ₂, θ₁ + 2π)`.
* `TauCeti.eq_of_tendsto_circleMap_of_frequently_mem_image_circleMap_Ioi` — a radial limit along a
  ray that a curve tending to the circle meets arbitrarily late is the limit along the curve.
* `TauCeti.exists_lt_forall_eq_of_tendsto_circleMap_of_mapClusterPt` — if a curve tending to the
  circle has two distinct cluster points, every radial limit at an angle of some nondegenerate
  arc is the limit along the curve.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer (1992), Proposition 2.14.
* E. Lindelöf, *Sur un principe général de l'analyse et ses applications à la théorie de la
  représentation conforme*, Acta Soc. Sci. Fennicae **46** (1915).
-/

public section

open Complex Filter Set Topology
open scoped Real

namespace TauCeti

/-- On the ray at angle `φ`, the angle measured from the ray at angle `θ` through
`arg (-((z - c) * exp (-(θ * I))))` is `φ - θ + π`, for `φ ∈ (θ - 2π, θ]`. -/
private theorem arg_neg_mul_exp_circleMap_sub {c : ℂ} {r φ θ : ℝ} (hr : 0 < r)
    (hφ : φ ∈ Ioc (θ - 2 * π) θ) :
    arg (-((circleMap c r φ - c) * exp (-(θ * I)))) = φ - θ + π := by
  have h : -((circleMap c r φ - c) * exp (-(θ * I))) = r * exp ((φ - θ + π : ℝ) * I) := by
    rw [circleMap_sub_center, circleMap_zero]
    push_cast
    rw [show ((φ : ℂ) - θ + π) * I = φ * I + -(θ * I) + π * I by ring, exp_add, exp_add,
      exp_pi_mul_I]
    ring
  rw [h, arg_real_mul _ hr, arg_exp_mul_I, toIocMod_eq_self]
  constructor <;> linarith [hφ.1, hφ.2]

/-- A point other than `c` at angle `φ - θ + π` from the ray at angle `θ`, measured through
`arg (-((z - c) * exp (-(θ * I))))`, lies on the ray at angle `φ`. -/
private theorem mem_image_circleMap_Ioi_of_arg_neg_mul_exp {c z : ℂ} {φ θ : ℝ} (hz : z ≠ c)
    (h : arg (-((z - c) * exp (-(θ * I)))) = φ - θ + π) :
    z ∈ (circleMap c · φ) '' Ioi 0 := by
  set w := -((z - c) * exp (-(θ * I))) with hw
  have hw0 : w ≠ 0 := by simp [hw, sub_ne_zero.2 hz, exp_ne_zero]
  refine ⟨‖w‖, norm_pos_iff.2 hw0, ?_⟩
  have hpolar := norm_mul_exp_arg_mul_I w
  rw [h] at hpolar
  have hrot : exp ((φ - θ + π : ℝ) * I) * exp (θ * I) = -exp (φ * I) := by
    rw [← exp_add]
    push_cast
    rw [show ((φ : ℂ) - θ + π) * I + θ * I = φ * I + π * I by ring, exp_add, exp_pi_mul_I]
    ring
  have hexp : exp (-(θ * I)) * exp (θ * I) = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  simp only [circleMap]
  linear_combination (‖w‖ : ℂ) * hrot - exp (θ * I) * hpolar - exp (θ * I) * hw + (z - c) * hexp

/-- The angle `arg (-((z - c) * exp (-(θ * I))))` is continuous at every `z ≠ c` where it is not
`π`, that is, off the ray at angle `θ`. -/
private theorem continuousAt_arg_neg_mul_exp {c z : ℂ} {θ : ℝ} (hz : z ≠ c)
    (h : arg (-((z - c) * exp (-(θ * I)))) ≠ π) :
    ContinuousAt (fun z ↦ arg (-((z - c) * exp (-(θ * I))))) z := by
  have hw : -((z - c) * exp (-(θ * I))) ∈ slitPlane :=
    mem_slitPlane_iff_arg.2 ⟨h, by simp [sub_ne_zero.2 hz, exp_ne_zero]⟩
  exact (continuousAt_arg hw).comp (f := fun z ↦ -((z - c) * exp (-(θ * I)))) (by fun_prop)

variable {γ : ℝ → ℂ} {c : ℂ} {a b : ℝ}

/-- **A curve clustering at two rays crosses the rays between them.** Let `γ` be continuous on
`(a, b)` and eventually different from `c` as `t → b`, and let it cluster at points of the rays
from `c` at angles `θ₁ < θ₂`. For `θ₁ < θ < θ₂ < θ' < θ₁ + 2π`, the curve meets the ray at angle
`θ` or the ray at angle `θ'` at parameters arbitrarily close to `b`. Otherwise a tail of `γ` would
avoid both rays, and so stay in one of the two sectors they bound, which does not contain both
cluster points. -/
theorem frequently_mem_image_circleMap_Ioi_or_frequently_mem_image_circleMap_Ioi (hab : a < b)
    (hγ : ContinuousOn γ (Ioo a b)) (hc : ∀ᶠ t in 𝓝[<] b, γ t ≠ c) {ρ₁ ρ₂ θ₁ θ₂ θ θ' : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) (h₁ : MapClusterPt (circleMap c ρ₁ θ₁) (𝓝[<] b) γ)
    (h₂ : MapClusterPt (circleMap c ρ₂ θ₂) (𝓝[<] b) γ) (hθ₁ : θ₁ < θ) (hθ₂ : θ < θ₂)
    (hθ' : θ₂ < θ') (hθ'₁ : θ' < θ₁ + 2 * π) :
    (∃ᶠ t in 𝓝[<] b, γ t ∈ (circleMap c · θ) '' Ioi 0) ∨
      ∃ᶠ t in 𝓝[<] b, γ t ∈ (circleMap c · θ') '' Ioi 0 := by
  by_contra! h
  -- the angle measured from the ray at `θ'`, continuous off that ray and the centre
  set ψ : ℂ → ℝ := fun z ↦ arg (-((z - c) * exp (-(θ' * I))))
  have hψ₁ : arg (-((circleMap c ρ₁ θ₁ - c) * exp (-(θ' * I)))) = θ₁ - θ' + π :=
    arg_neg_mul_exp_circleMap_sub hρ₁ ⟨by linarith, by linarith⟩
  have hψ₂ : arg (-((circleMap c ρ₂ θ₂ - c) * exp (-(θ' * I)))) = θ₂ - θ' + π :=
    arg_neg_mul_exp_circleMap_sub hρ₂ ⟨by linarith, by linarith⟩
  have hcont {z : ℂ} (hz : z ≠ c) (hz' : z ∉ (circleMap c · θ') '' Ioi 0) : ContinuousAt ψ z :=
    continuousAt_arg_neg_mul_exp hz fun hπ ↦ hz' <|
      mem_image_circleMap_Ioi_of_arg_neg_mul_exp hz (by rw [hπ]; ring)
  -- `γ` comes arbitrarily late on both sides of the ray at `θ`
  have hlt : ∃ᶠ t in 𝓝[<] b, ψ (γ t) < θ - θ' + π :=
    (h₁.continuousAt_comp (continuousAt_arg_neg_mul_exp (circleMap_ne_center hρ₁.ne')
      (by rw [hψ₁]; linarith))).frequently (Iio_mem_nhds (by rw [hψ₁]; linarith))
  have hgt : ∃ᶠ t in 𝓝[<] b, θ - θ' + π < ψ (γ t) :=
    (h₂.continuousAt_comp (continuousAt_arg_neg_mul_exp (circleMap_ne_center hρ₂.ne')
      (by rw [hψ₂]; linarith))).frequently (Ioi_mem_nhds (by rw [hψ₂]; linarith))
  -- but a tail of `γ` avoids the centre and both rays
  obtain ⟨t₀, ht₀, hgood⟩ := (nhdsLT_basis b).eventually_iff.1 (hc.and (h.1.and h.2))
  have hI : Ioo (max a t₀) b ∈ 𝓝[<] b := Ioo_mem_nhdsLT (max_lt hab ht₀)
  obtain ⟨s₁, hs₁, hs₁I⟩ := (hlt.and_eventually hI).exists
  obtain ⟨s₂, hs₂, hs₂I⟩ := (hgt.and_eventually hI).exists
  have hsub : uIcc s₁ s₂ ⊆ Ioo (max a t₀) b := ordConnected_Ioo.uIcc_subset hs₁I hs₂I
  have hgood' {s : ℝ} (hs : s ∈ uIcc s₁ s₂) :=
    hgood (Ioo_subset_Ioo_left (le_max_right _ _) (hsub hs))
  have hψγ : ContinuousOn (ψ ∘ γ) (uIcc s₁ s₂) := fun s hs ↦
    (hcont (hgood' hs).1 (hgood' hs).2.2).comp_continuousWithinAt
      (hγ.mono (hsub.trans (Ioo_subset_Ioo_left (le_max_left _ _))) s hs)
  -- so by the intermediate value theorem it meets the ray at `θ`
  obtain ⟨s, hs, hψs⟩ := intermediate_value_uIcc hψγ (mem_uIcc_of_le hs₁.le hs₂.le)
  exact (hgood' hs).2.1 <| mem_image_circleMap_Ioi_of_arg_neg_mul_exp (hgood' hs).1 hψs

/-- **The radial limit along a crossed ray is the limit along the curve.** If `γ` tends to the
circle `sphere c R` from inside, `f` tends to `w` along `γ`, and `γ` meets the ray at angle `θ`
frequently, then the radial limit of `f` at `θ`, if it exists, is `w`. -/
theorem eq_of_tendsto_circleMap_of_frequently_mem_image_circleMap_Ioi {ι X : Type*}
    [TopologicalSpace X] [T2Space X] {l : Filter ι} {γ : ι → ℂ} {f : ℂ → X} {R θ : ℝ} {w L : X}
    (hd : Tendsto (fun t ↦ dist (γ t) c) l (𝓝[<] R))
    (hθ : ∃ᶠ t in l, γ t ∈ (circleMap c · θ) '' Ioi 0) (hfγ : Tendsto (f ∘ γ) l (𝓝 w))
    (hL : Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 L)) : L = w := by
  set l' := l ⊓ 𝓟 {t | γ t ∈ (circleMap c · θ) '' Ioi 0}
  have : l'.NeBot := frequently_iff_neBot.1 hθ
  -- along the crossing times, `γ t` is the point of the ray at its own distance from `c`
  have heq : ∀ᶠ t in l', f (circleMap c (dist (γ t) c) θ) = (f ∘ γ) t := by
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with t ⟨r, hr, hrt⟩
    rw [← hrt, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hr]
    exact congrArg f hrt
  exact tendsto_nhds_unique ((hL.comp (hd.mono_left inf_le_left)).congr' heq)
    (hfγ.mono_left inf_le_left)

/-- **Limits along a curve that does not end at a point of the circle.** Let `γ` be continuous on
`(a, b)` and tend to the circle `sphere c R` from inside as `t → b`, and let `f` tend to `w` along
`γ`. If `γ` has two distinct cluster points, there is a nondegenerate interval of angles `θ` at
each of which every radial limit `lim_{r → R⁻} f (circleMap c r θ)` is `w`. -/
theorem exists_lt_forall_eq_of_tendsto_circleMap_of_mapClusterPt {X : Type*} [TopologicalSpace X]
    [T2Space X] {f : ℂ → X} {R : ℝ} {w : X} {ζ₁ ζ₂ : ℂ} (hab : a < b)
    (hγ : ContinuousOn γ (Ioo a b)) (hd : Tendsto (fun t ↦ dist (γ t) c) (𝓝[<] b) (𝓝[<] R))
    (hfγ : Tendsto (f ∘ γ) (𝓝[<] b) (𝓝 w)) (h₁ : MapClusterPt ζ₁ (𝓝[<] b) γ)
    (h₂ : MapClusterPt ζ₂ (𝓝[<] b) γ) (hζ : ζ₁ ≠ ζ₂) :
    ∃ θ₁ θ₂, θ₁ < θ₂ ∧ ∀ θ ∈ Ioo θ₁ θ₂, ∀ L,
      Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 L) → L = w := by
  have hdR : Tendsto (fun t ↦ dist (γ t) c) (𝓝[<] b) (𝓝 R) := hd.mono_right nhdsWithin_le_nhds
  have hR : 0 < R := by
    obtain ⟨t, ht⟩ := (hd.eventually (eventually_mem_nhdsWithin (a := R) (s := Iio R))).exists
    exact dist_nonneg.trans_lt ht
  have hc : ∀ᶠ t in 𝓝[<] b, γ t ≠ c := (hdR.eventually_const_lt hR).mono fun _ ht ↦ dist_pos.1 ht
  -- every cluster point of `γ` is the point of the circle at its own argument
  have hrep {ζ : ℂ} (h : MapClusterPt ζ (𝓝[<] b) γ) : circleMap c R (arg (ζ - c)) = ζ := by
    have hζR : dist ζ c = R := eq_of_nhds_neBot <| ClusterPt.mono
      (MapClusterPt.continuousAt_comp (f := fun z : ℂ ↦ dist z c) (by fun_prop) h) hdR
    rw [← hζR, dist_eq_norm, circleMap, norm_mul_exp_arg_mul_I, add_sub_cancel]
  -- the conclusion along the arc of all angles that `γ` crosses arbitrarily late
  have hcross {θ₁ θ₂ : ℝ} (h₁₂ : θ₁ < θ₂)
      (hall : ∀ θ ∈ Ioo θ₁ θ₂, ∃ᶠ t in 𝓝[<] b, γ t ∈ (circleMap c · θ) '' Ioi 0) :
      ∃ θ₁ θ₂, θ₁ < θ₂ ∧ ∀ θ ∈ Ioo θ₁ θ₂, ∀ L,
        Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 L) → L = w :=
    ⟨θ₁, θ₂, h₁₂, fun θ hθ _ hL ↦
      eq_of_tendsto_circleMap_of_frequently_mem_image_circleMap_Ioi hd (hall θ hθ) hfγ hL⟩
  -- by symmetry, order the two cluster points by argument
  have key {ζ ζ' : ℂ} (h : MapClusterPt ζ (𝓝[<] b) γ) (h' : MapClusterPt ζ' (𝓝[<] b) γ)
      (hlt : arg (ζ - c) < arg (ζ' - c)) :
      ∃ θ₁ θ₂, θ₁ < θ₂ ∧ ∀ θ ∈ Ioo θ₁ θ₂, ∀ L,
        Tendsto (fun r ↦ f (circleMap c r θ)) (𝓝[<] R) (𝓝 L) → L = w := by
    have hlt' : arg (ζ' - c) < arg (ζ - c) + 2 * π := by
      linarith [arg_le_pi (ζ' - c), neg_pi_lt_arg (ζ - c)]
    by_cases hall : ∀ θ ∈ Ioo (arg (ζ - c)) (arg (ζ' - c)),
        ∃ᶠ t in 𝓝[<] b, γ t ∈ (circleMap c · θ) '' Ioi 0
    · exact hcross hlt hall
    · simp only [not_forall] at hall
      obtain ⟨θ, hθ, hnot⟩ := hall
      refine hcross hlt' fun θ' hθ' ↦ ?_
      rw [← hrep h] at h
      rw [← hrep h'] at h'
      exact (frequently_mem_image_circleMap_Ioi_or_frequently_mem_image_circleMap_Ioi hab hγ hc
        hR hR h h' hθ.1 hθ.2 hθ'.1 hθ'.2).resolve_left hnot
  have hne : arg (ζ₁ - c) ≠ arg (ζ₂ - c) := fun heq ↦ hζ <| by rw [← hrep h₁, ← hrep h₂, heq]
  rcases hne.lt_or_gt with hlt | hlt
  exacts [key h₁ h₂ hlt, key h₂ h₁ hlt]

end TauCeti
