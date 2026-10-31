/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Complexification.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Analysis.Complex.PiBall

/-!
# Complexification of real analytic functions on open sets

A real analytic function on an open set `U ⊆ ι → ℝ`, with `ι` finite, extends to a holomorphic
function on an open neighborhood `W ⊆ ι → ℂ` of the real points of `U`. The neighborhood can be
chosen invariant under complex conjugation and with real points exactly those of `U`, and the
extension commutes with conjugation. Such an extension is unique near the real points: two
holomorphic functions on an open neighborhood of the real points of `U` that agree at those
points agree on a smaller conjugation-invariant open neighborhood of them.

The pointwise statement `AnalyticAt.exists_complexification` gives a holomorphic extension on a
polydisc (a ball for the sup norm) centred at each real point of `U`. The extensions on two such
polydiscs agree on their intersection: the intersection is convex, it contains the real part of
each of its points, and near such a real point both extensions agree with the original function
on the real points, hence agree by the identity theorem on the real points
(`AnalyticAt.eventuallyEq_of_eventually_real`). The extensions therefore glue to a function on
the union of the polydiscs. Shrinking each polydisc so that its real points lie in `U` makes the
real points of the union exactly `U`, and polydiscs centred at real points are invariant under
conjugation.

## Main declarations

* `AnalyticOnNhd.exists_complexification`: a real analytic function on an open set extends to a
  holomorphic function on a conjugation-invariant open neighborhood of its real points.
* `AnalyticOnNhd.exists_complexification_pi`: the same for real analytic maps to `κ → ℝ`.
* `AnalyticOnNhd.exists_eqOn_of_forall_real`: uniqueness of such an extension on a
  conjugation-invariant open neighborhood of the real points.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
-/

public section

open Filter Metric Set
open scoped Topology

variable {ι κ : Type*} [Fintype ι]

/-- Two complex analytic functions on polydiscs centred at real points that agree at the common
real points of the polydiscs agree on their intersection. -/
private theorem eqOn_inter_ball_of_forall_real {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {F G : (ι → ℂ) → E} {a b : ι → ℝ} {r s : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball (fun i ↦ (a i : ℂ)) r))
    (hG : AnalyticOnNhd ℂ G (ball (fun i ↦ (b i : ℂ)) s))
    (hFG : ∀ y ∈ ball a r ∩ ball b s, F (fun i ↦ (y i : ℂ)) = G fun i ↦ (y i : ℂ)) :
    EqOn F G (ball (fun i ↦ (a i : ℂ)) r ∩ ball (fun i ↦ (b i : ℂ)) s) := by
  rcases eq_empty_or_nonempty (ball (fun i ↦ (a i : ℂ)) r ∩ ball (fun i ↦ (b i : ℂ)) s) with
    h | ⟨z, hza, hzb⟩
  · simp [h]
  -- the real part of a common point is a common real point, where the identity theorem applies
  set w : ι → ℝ := fun i ↦ (z i).re
  have hwa := Complex.pi_re_mem_ball hza
  have hwa' := Complex.pi_ofReal_re_mem_ball hza
  have hwb := Complex.pi_re_mem_ball hzb
  have hwb' := Complex.pi_ofReal_re_mem_ball hzb
  refine (hF.mono inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono inter_subset_right) ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    ⟨hwa', hwb'⟩ ((hF _ hwa').eventuallyEq_of_eventually_real (hG _ hwb') ?_)
  filter_upwards [(isOpen_ball.inter isOpen_ball).mem_nhds ⟨hwa, hwb⟩] with v hv using hFG v hv

/-- Holomorphic extensions of a function `g` from real-centred polydiscs around the points of an
open set `U`, each commuting with conjugation, glue to a holomorphic extension on a
conjugation-invariant open neighborhood of the real points of `U`. -/
private theorem exists_complexification_of_local {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [StarAddMonoid E] {U : Set (ι → ℝ)} (hU : IsOpen U) (g : (ι → ℝ) → E)
    (hloc : ∀ x ∈ U, ∃ r > (0 : ℝ), ∃ F : (ι → ℂ) → E,
      AnalyticOnNhd ℂ F (ball (fun i ↦ (x i : ℂ)) r) ∧
        (∀ y ∈ ball x r, F (fun i ↦ (y i : ℂ)) = g y) ∧ ∀ z, F (star z) = star (F z)) :
    ∃ W : Set (ι → ℂ), IsOpen W ∧ (∀ x : ι → ℝ, (fun i ↦ (x i : ℂ)) ∈ W ↔ x ∈ U) ∧
      (∀ z, star z ∈ W ↔ z ∈ W) ∧ ∃ F : (ι → ℂ) → E, AnalyticOnNhd ℂ F W ∧
        (∀ x ∈ U, F (fun i ↦ (x i : ℂ)) = g x) ∧ ∀ z, F (star z) = star (F z) := by
  classical
  -- shrink each local polydisc so that its real points lie in `U`
  have hloc' (x : U) : ∃ r > (0 : ℝ), ball (x : ι → ℝ) r ⊆ U ∧ ∃ F : (ι → ℂ) → E,
      AnalyticOnNhd ℂ F (ball (fun i ↦ ((x : ι → ℝ) i : ℂ)) r) ∧
        (∀ y ∈ ball (x : ι → ℝ) r, F (fun i ↦ (y i : ℂ)) = g y) ∧
          ∀ z, F (star z) = star (F z) := by
    obtain ⟨r, hr, F, hF, hFg, hFs⟩ := hloc x x.2
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x x.2
    exact ⟨min r ε, lt_min hr hε, (ball_subset_ball (min_le_right _ _)).trans hεU, F,
      hF.mono (ball_subset_ball (min_le_left _ _)),
      fun y hy ↦ hFg y (ball_subset_ball (min_le_left _ _) hy), hFs⟩
  choose r hr hrU F hF hFg hFs using hloc'
  -- two local extensions agree on the intersection of their polydiscs
  have hagree (x y : U) : EqOn (F x) (F y)
      (ball (fun i ↦ ((x : ι → ℝ) i : ℂ)) (r x) ∩ ball (fun i ↦ ((y : ι → ℝ) i : ℂ)) (r y)) :=
    eqOn_inter_ball_of_forall_real (hF x) (hF y) fun v hv ↦ by rw [hFg x v hv.1, hFg y v hv.2]
  set W := ⋃ x : U, ball (fun i ↦ ((x : ι → ℝ) i : ℂ)) (r x)
  have hWstar (z : ι → ℂ) : star z ∈ W ↔ z ∈ W := Complex.pi_star_mem_iUnion_ball_iff
  -- the glued extension, using any polydisc containing the point
  let G : (ι → ℂ) → E := fun z ↦ if h : z ∈ W then F (mem_iUnion.1 h).choose z else 0
  have hG (x : U) {z : ι → ℂ} (hz : z ∈ ball (fun i ↦ ((x : ι → ℝ) i : ℂ)) (r x)) :
      G z = F x z := by
    have h : z ∈ W := mem_iUnion.2 ⟨x, hz⟩
    simp only [G, h, ↓reduceDIte]
    exact hagree _ _ ⟨(mem_iUnion.1 h).choose_spec, hz⟩
  refine ⟨W, isOpen_iUnion fun _ ↦ isOpen_ball,
    fun _ ↦ Complex.pi_ofReal_mem_iUnion_ball_iff hr hrU, hWstar, G, fun z hz ↦ ?_,
    fun x hx ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨x, hx⟩ := mem_iUnion.1 hz
    exact (hF x z hx).congr (eventually_of_mem (isOpen_ball.mem_nhds hx) fun z' hz' ↦
      (hG x hz').symm)
  · rw [hG ⟨x, hx⟩ (mem_ball_self (hr _)), hFg ⟨x, hx⟩ x (mem_ball_self (hr _))]
  · by_cases hz : z ∈ W
    · obtain ⟨x, hx⟩ := mem_iUnion.1 hz
      rw [hG x (Complex.pi_star_mem_ball_iff.2 hx), hG x hx, hFs]
    · have hz' : star z ∉ W := fun h ↦ hz ((hWstar z).1 h)
      simp only [G, hz, hz', ↓reduceDIte, star_zero]

namespace AnalyticOnNhd

/-- **Complexification of a real analytic function on an open set.** A function of finitely many
real variables that is analytic on an open set `U` extends to a function `F` of as many complex
variables that is complex analytic on an open set `W` whose real points are exactly those of `U`.
The set `W` is invariant under complex conjugation, `F` agrees with `f` at the real points of
`U`, and `F` commutes with complex conjugation. -/
theorem exists_complexification {f : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)} (hf : AnalyticOnNhd ℝ f U)
    (hU : IsOpen U) :
    ∃ W : Set (ι → ℂ), IsOpen W ∧ (∀ x : ι → ℝ, (fun i ↦ (x i : ℂ)) ∈ W ↔ x ∈ U) ∧
      (∀ z, star z ∈ W ↔ z ∈ W) ∧ ∃ F : (ι → ℂ) → ℂ, AnalyticOnNhd ℂ F W ∧
        (∀ x ∈ U, F (fun i ↦ (x i : ℂ)) = f x) ∧ ∀ z, F (star z) = star (F z) :=
  exists_complexification_of_local hU (fun x ↦ (f x : ℂ)) fun x hx ↦
    (hf x hx).exists_complexification

/-- **Complexification of a real analytic map on an open set.** A map from `ι → ℝ` to `κ → ℝ`,
with `ι` and `κ` finite, that is analytic on an open set `U` extends to a map
`F : (ι → ℂ) → (κ → ℂ)` that is complex analytic on an open set `W` whose real points are exactly
those of `U`. The set `W` is invariant under complex conjugation, `F` agrees with `f` at the real
points of `U`, and `F` commutes with complex conjugation. -/
theorem exists_complexification_pi [Fintype κ] {f : (ι → ℝ) → κ → ℝ} {U : Set (ι → ℝ)}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsOpen U) :
    ∃ W : Set (ι → ℂ), IsOpen W ∧ (∀ x : ι → ℝ, (fun i ↦ (x i : ℂ)) ∈ W ↔ x ∈ U) ∧
      (∀ z, star z ∈ W ↔ z ∈ W) ∧ ∃ F : (ι → ℂ) → κ → ℂ, AnalyticOnNhd ℂ F W ∧
        (∀ x ∈ U, F (fun i ↦ (x i : ℂ)) = fun k ↦ (f x k : ℂ)) ∧
          ∀ z, F (star z) = star (F z) :=
  exists_complexification_of_local hU (fun x k ↦ (f x k : ℂ)) fun x hx ↦
    (hf x hx).exists_complexification_pi

/-- **Uniqueness of complexifications.** Two complex analytic functions of finitely many variables
on an open neighborhood `W` of the real points of an open set `U`, agreeing at those real points,
agree on a smaller open set `V ⊆ W` that is invariant under complex conjugation and whose real
points are exactly those of `U`. -/
theorem exists_eqOn_of_forall_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F G : (ι → ℂ) → E} {U : Set (ι → ℝ)} {W : Set (ι → ℂ)} (hF : AnalyticOnNhd ℂ F W)
    (hG : AnalyticOnNhd ℂ G W) (hU : IsOpen U) (hW : IsOpen W)
    (hUW : ∀ x ∈ U, (fun i ↦ (x i : ℂ)) ∈ W)
    (hFG : ∀ x ∈ U, F (fun i ↦ (x i : ℂ)) = G fun i ↦ (x i : ℂ)) :
    ∃ V ⊆ W, IsOpen V ∧ (∀ x : ι → ℝ, (fun i ↦ (x i : ℂ)) ∈ V ↔ x ∈ U) ∧
      (∀ z, star z ∈ V ↔ z ∈ V) ∧ EqOn F G V := by
  -- polydiscs centred at the real points of `U`, contained in `W`, with real points in `U`
  have hball (x : U) : ∃ s > (0 : ℝ), ball (fun i ↦ ((x : ι → ℝ) i : ℂ)) s ⊆ W ∧
      ball (x : ι → ℝ) s ⊆ U := by
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW _ (hUW x x.2)
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x x.2
    exact ⟨min ε δ, lt_min hε hδ, (ball_subset_ball (min_le_left _ _)).trans hεW,
      (ball_subset_ball (min_le_right _ _)).trans hδU⟩
  choose s hs hsW hsU using hball
  refine ⟨_, iUnion_subset hsW, isOpen_iUnion fun _ ↦ isOpen_ball,
    fun _ ↦ Complex.pi_ofReal_mem_iUnion_ball_iff hs hsU,
    fun _ ↦ Complex.pi_star_mem_iUnion_ball_iff, fun z hz ↦ ?_⟩
  obtain ⟨x, hx⟩ := mem_iUnion.1 hz
  exact eqOn_inter_ball_of_forall_real (hF.mono (hsW x)) (hG.mono (hsW x))
    (fun y hy ↦ hFG y (hsU x hy.1)) ⟨hx, hx⟩

end AnalyticOnNhd
