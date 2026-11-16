/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.RCLike.Basic

-- Proof-only: the identity principle
-- `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` and its analytic inputs, and
-- `SeparatingDual.exists_continuousLinearEquiv_apply_eq` for the change of coordinates.
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Analytic functions are determined by their restrictions to lines

A function analytic at `p` vanishes on a neighbourhood of `p` exactly when its restriction
`t ↦ f (p + t • v)` to every line through `p` vanishes on a neighbourhood of `0`. The nontrivial
direction is the identity principle along each line: on a ball around `p` where `f` is analytic,
the restriction to the line through `p` and a point `y` of the ball is analytic on a disc
containing `0` and `1`, so it vanishes at `1`, that is at `y`.

In several complex variables this is the first step of putting a nonzero germ in general position:
some direction `v` has a restriction that does not vanish identically, and in linear coordinates
whose last axis is `v` the germ becomes regular in the last variable, as Weierstrass preparation
requires (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`).

The name follows Mathlib's `Mathlib.Analysis.Analytic.Uniqueness`, where the identity principle
lives.

## Main declarations

* `AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul`: an analytic function
  vanishes near `p` exactly when all its restrictions to lines through `p` vanish near `0`.
* `AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`: after a linear change of
  coordinates, a function on `E × 𝕜` not vanishing near `p` has finite order in the last variable.
* `AnalyticAt.mul_eventuallyEq_zero_iff`, `Finset.prod_eventuallyEq_zero_iff`: in a domain, a
  product of analytic functions vanishes near `p` exactly when one of the factors does.
* `TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top`: after a single linear
  change of coordinates, finitely many analytic functions on `E × 𝕜` none of which vanishes near
  `p` all have finite order in the last variable.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
-/

public section

open Filter Metric Topology

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The nontrivial direction of
`AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul` for a complete
codomain, where `f` is analytic on a ball around `p`. -/
private theorem AnalyticAt.eventuallyEq_zero_of_forall_eventuallyEq_zero_comp_add_smul
    [CompleteSpace F] {f : E → F} {p : E} (hf : AnalyticAt 𝕜 f p)
    (h : ∀ v : E, (fun t : 𝕜 ↦ f (p + t • v)) =ᶠ[𝓝 0] 0) : f =ᶠ[𝓝 p] 0 := by
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  filter_upwards [ball_mem_nhds p hr] with y hy
  set v := y - p
  rcases eq_or_ne v 0 with hv | hv
  · -- On the trivial direction the restriction is the constant `f p = f y`.
    simpa [sub_eq_zero.1 hv] using (h 0).self_of_nhds
  -- On the line through `p` and `y`, the restriction is analytic on a disc containing `0` and `1`.
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hmem : ∀ t ∈ ball (0 : 𝕜) (r / ‖v‖), p + t • v ∈ ball p r := fun t ht ↦ by
    rw [mem_ball_zero_iff, lt_div_iff₀ hv'] at ht
    simpa [dist_eq_norm, norm_smul] using ht
  have hline (t : 𝕜) : AnalyticAt 𝕜 (fun t : 𝕜 ↦ p + t • v) t := by fun_prop
  have han : AnalyticOnNhd 𝕜 (fun t : 𝕜 ↦ f (p + t • v)) (ball (0 : 𝕜) (r / ‖v‖)) :=
    fun t ht ↦ AnalyticAt.comp (g := f) (hfr _ (hmem t ht)) (hline t)
  have h1 : (1 : 𝕜) ∈ ball (0 : 𝕜) (r / ‖v‖) := by
    rw [mem_ball_zero_iff, norm_one, one_lt_div hv']
    simpa [v, dist_eq_norm] using hy
  simpa [v] using han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : 𝕜) _).isPreconnected (mem_ball_self (div_pos hr hv')) (h v) h1

/-- **An analytic function is determined near a point by its restrictions to lines.** A function
analytic at `p` vanishes on a neighbourhood of `p` exactly when, for every direction `v`, the
restriction `t ↦ f (p + t • v)` vanishes on a neighbourhood of `0`. -/
theorem AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul {f : E → F}
    {p : E} (hf : AnalyticAt 𝕜 f p) :
    f =ᶠ[𝓝 p] 0 ↔ ∀ v : E, (fun t : 𝕜 ↦ f (p + t • v)) =ᶠ[𝓝 0] 0 := by
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · have hline : Tendsto (fun t : 𝕜 ↦ p + t • v) (𝓝 0) (𝓝 p) := by
      have : Continuous fun t : 𝕜 ↦ p + t • v := by fun_prop
      simpa using this.tendsto (0 : 𝕜)
    exact hline.eventually h
  -- Pass to the completion of `F`, as in Mathlib's identity principle.
  let e : F →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have he : (e ∘ f) =ᶠ[𝓝 p] 0 :=
    ((e.analyticAt _).comp hf).eventuallyEq_zero_of_forall_eventuallyEq_zero_comp_add_smul
      fun v ↦ (h v).mono fun t ht ↦ by simp [ht]
  exact he.mono fun y hy ↦ UniformSpace.Completion.coe_injective F (by simpa [e] using hy)

/-- **General position in the last variable.** A function analytic at `p` on `E × 𝕜` that does not
vanish near `p` becomes regular in the last variable after a linear change of coordinates: there
are a continuous linear automorphism `L` and a point `q` with `L q = p` such that
`t ↦ f (L (q.1, t))` has finite analytic order at `q.2`. The last axis is sent to a direction along
which the restriction of `f` does not vanish identically. -/
theorem AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top {f : E × 𝕜 → F}
    {p : E × 𝕜} (hf : AnalyticAt 𝕜 f p) (hf0 : ¬f =ᶠ[𝓝 p] 0) :
    ∃ (L : (E × 𝕜) ≃L[𝕜] E × 𝕜) (q : E × 𝕜), L q = p ∧
      analyticOrderAt (fun t ↦ f (L (q.1, t))) q.2 ≠ ⊤ := by
  obtain ⟨v, hv⟩ : ∃ v, ¬(fun t : 𝕜 ↦ f (p + t • v)) =ᶠ[𝓝 0] 0 := by
    by_contra! h
    exact hf0 (hf.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul.2 h)
  rcases eq_or_ne v 0 with rfl | hv0
  · -- The trivial direction only occurs when `f p ≠ 0`, and then any coordinates work.
    refine ⟨.refl 𝕜 _, p, rfl, fun h ↦ hv (Eventually.of_forall fun t ↦ ?_)⟩
    simpa using (analyticOrderAt_eq_top.1 h).self_of_nhds
  -- Move to linear coordinates in which `v` is the last axis.
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := 𝕜)
    (x := ((0 : E), (1 : 𝕜))) (by simp) hv0
  obtain ⟨⟨x₀, w₀⟩, rfl⟩ : ∃ q, L q = p := ⟨L.symm p, L.apply_symm_apply p⟩
  refine ⟨L, (x₀, w₀), rfl, ?_⟩
  -- The vertical slice is the restriction of `f` to the line through `p` along `v`.
  rw [Ne, analyticOrderAt_eq_top]
  refine fun h ↦ hv ?_
  have ht : Tendsto (fun t : 𝕜 ↦ w₀ + t) (𝓝 0) (𝓝 w₀) := by
    have : Continuous fun t : 𝕜 ↦ w₀ + t := by fun_prop
    simpa using this.tendsto 0
  filter_upwards [ht.eventually h] with t ht
  have hLt : L (x₀, w₀ + t) = L (x₀, w₀) + t • v := by
    rw [← hL, ← L.map_smul, ← L.map_add]
    simp
  simpa [hLt] using ht

/-- **Integrity of the ring of analytic germs.** A product of two analytic functions valued in a
normed domain vanishes near `p` if and only if one of the factors vanishes near `p`. -/
theorem AnalyticAt.mul_eventuallyEq_zero_iff {A : Type*} [NormedRing A]
    [NoZeroDivisors A] [NormedAlgebra 𝕜 A] {f g : E → A} {p : E} (hf : AnalyticAt 𝕜 f p)
    (hg : AnalyticAt 𝕜 g p) : f * g =ᶠ[𝓝 p] 0 ↔ f =ᶠ[𝓝 p] 0 ∨ g =ᶠ[𝓝 p] 0 := by
  refine ⟨fun hfg ↦ ?_, ?_⟩
  · by_contra! h
    -- Embed `A` as a normed `𝕜`-vector space into its completion to obtain balls of analyticity,
    -- while using `NoZeroDivisors A` directly in `A`.
    let e : A →L[𝕜] UniformSpace.Completion A := UniformSpace.Completion.toComplL
    have he_inj : Function.Injective e := UniformSpace.Completion.coe_injective A
    obtain ⟨r₁, hr₁, hfB⟩ := ((e.analyticAt _).comp hf).exists_ball_analyticOnNhd
    obtain ⟨r₂, hr₂, hgB⟩ := ((e.analyticAt _).comp hg).exists_ball_analyticOnNhd
    obtain ⟨r₃, hr₃, hfgB⟩ := Metric.eventually_nhds_iff_ball.1 hfg
    set r := min r₁ (min r₂ r₃)
    have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
    have hy : ∃ y ∈ ball p r, f y ≠ 0 := by
      by_contra! hall
      exact h.1 (Filter.eventually_of_mem (ball_mem_nhds p hr) hall)
    obtain ⟨y, hyr, hfy⟩ := hy
    have hefy : (e ∘ f) y ≠ 0 := fun h0 ↦ hfy (he_inj (by simpa [e] using h0))
    have hfc : ContinuousAt (e ∘ f) y :=
      (hfB y (ball_subset_ball (min_le_left _ _) hyr)).continuousAt
    have hgy : (e ∘ g) =ᶠ[𝓝 y] 0 := by
      filter_upwards [hfc.eventually_ne hefy, isOpen_ball.mem_nhds hyr] with z hefz hzr
      have hfz : f z ≠ 0 := fun h0 ↦ hefz (by simp [h0])
      have hz0 : f z * g z = 0 :=
        hfgB z (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hzr)
      simp [(mul_eq_zero.1 hz0).resolve_left hfz]
    let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    have hg0 : Set.EqOn (e ∘ g) 0 (ball p r) :=
      (hgB.mono (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))))
        |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball p r).isPreconnected hyr hgy
    exact h.2 ((Filter.eventually_of_mem (ball_mem_nhds p hr) hg0).mono fun z hz ↦
      he_inj (by simpa [e] using hz))
  · rintro (hf0 | hg0)
    · exact hf0.mono fun x hx ↦ by simp [hx]
    · exact hg0.mono fun x hx ↦ by simp [hx]

/-- A finite product of analytic functions valued in a nontrivial commutative normed domain vanishes
near `p` if and only if one of its factors vanishes near `p`. -/
theorem Finset.prod_eventuallyEq_zero_iff {ι A : Type*} [NormedCommRing A]
    [NoZeroDivisors A] [Nontrivial A] [NormedAlgebra 𝕜 A] {f : ι → E → A} {p : E} (s : Finset ι)
    (hf : ∀ i ∈ s, AnalyticAt 𝕜 (f i) p) :
    ∏ i ∈ s, f i =ᶠ[𝓝 p] 0 ↔ ∃ i ∈ s, f i =ᶠ[𝓝 p] 0 := by
  induction s using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.notMem_empty, false_and, exists_false, iff_false]
    exact fun h ↦ one_ne_zero (α := A) h.self_of_nhds
  | cons a s ha ih =>
    have hfa : AnalyticAt 𝕜 (f a) p := hf a (Finset.mem_cons_self a s)
    have hfs : AnalyticAt 𝕜 (∏ i ∈ s, f i) p :=
      s.analyticAt_prod fun i hi ↦ hf i (Finset.mem_cons_of_mem hi)
    rw [Finset.prod_cons, hfa.mul_eventuallyEq_zero_iff hfs,
      ih fun i hi ↦ hf i (Finset.mem_cons_of_mem hi)]
    simp only [Finset.mem_cons, exists_eq_or_imp]

/-- **Simultaneous general position for a finite family.** Finitely many analytic functions on
`E × 𝕜` valued in a nontrivial commutative normed domain, none of which vanishes near `p`, all
become regular in the last variable after a single linear change of coordinates: there are a
continuous linear automorphism `L` and a point `q` with `L q = p` such that every vertical slice
`t ↦ f i (L (q.1, t))` has finite analytic order at `q.2`. -/
theorem TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top {ι A : Type*}
    [Finite ι] [NormedCommRing A] [NoZeroDivisors A] [Nontrivial A]
    [NormedAlgebra 𝕜 A] {f : ι → E × 𝕜 → A} {p : E × 𝕜} (hf : ∀ i, AnalyticAt 𝕜 (f i) p)
    (hf0 : ∀ i, ¬f i =ᶠ[𝓝 p] 0) :
    ∃ (L : (E × 𝕜) ≃L[𝕜] E × 𝕜) (q : E × 𝕜), L q = p ∧
      ∀ i, analyticOrderAt (fun t ↦ f i (L (q.1, t))) q.2 ≠ ⊤ := by
  cases nonempty_fintype ι
  -- Place the product of the family in general position; a slice of the product cannot vanish
  -- identically without one of its factors vanishing identically.
  have hP : AnalyticAt 𝕜 (∏ i : ι, f i) p := Finset.univ.analyticAt_prod fun i _ ↦ hf i
  have hP0 : ¬(∏ i : ι, f i) =ᶠ[𝓝 p] 0 := by
    rw [Finset.univ.prod_eventuallyEq_zero_iff fun i _ ↦ hf i]
    exact fun ⟨i, _, hi⟩ ↦ hf0 i hi
  obtain ⟨L, q, rfl, hord⟩ := hP.exists_continuousLinearEquiv_analyticOrderAt_ne_top hP0
  refine ⟨L, q, rfl, fun i hi ↦ hord ?_⟩
  rw [analyticOrderAt_eq_top] at hi ⊢
  filter_upwards [hi] with t ht
  rw [Finset.prod_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ i) ht

end
