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
* `AnalyticAt.smul_eventuallyEq_zero_iff`, `AnalyticAt.mul_eventuallyEq_zero_iff`,
  `Finset.prod_eventuallyEq_zero_iff_of_analyticAt`: analytic germs at `p` have no zero divisors.
* `AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`: after a linear change of
  coordinates, a function on `E × 𝕜` not vanishing near `p` has finite order in the last variable.
* `TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top`: simultaneous general
  position in the last variable for a finite family of analytic functions.

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

/-- A scalar analytic germ acting on a vector-valued analytic germ vanishes near `p` if and only if
one of the two germs vanishes near `p`. -/
theorem AnalyticAt.smul_eventuallyEq_zero_iff {f : E → 𝕜} {g : E → F} {p : E}
    (hf : AnalyticAt 𝕜 f p) (hg : AnalyticAt 𝕜 g p) :
    f • g =ᶠ[𝓝 p] 0 ↔ f =ᶠ[𝓝 p] 0 ∨ g =ᶠ[𝓝 p] 0 := by
  refine ⟨fun hfg ↦ or_iff_not_imp_left.2 fun hf0 ↦ ?_, ?_⟩
  · let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    let e : F →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL
    obtain ⟨r₁, hr₁, hfr⟩ := hf.exists_ball_analyticOnNhd
    obtain ⟨r₂, hr₂, hgr⟩ := ((e.analyticAt _).comp hg).exists_ball_analyticOnNhd
    obtain ⟨r₃, hr₃, hfg_ball⟩ := Metric.eventually_nhds_iff.1 hfg
    set r := min r₁ (min r₂ r₃)
    have hr : 0 < r := lt_min hr₁ (lt_min hr₂ hr₃)
    have hr₁' : ball p r ⊆ ball p r₁ := ball_subset_ball (min_le_left _ _)
    have hr₂' : ball p r ⊆ ball p r₂ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
    have hr₃' : ball p r ⊆ ball p r₃ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
    -- Pick a point of the common ball where `f` is nonzero; `e ∘ g` must vanish on a neighborhood
    -- of that point, hence on the whole ball by the identity principle.
    obtain ⟨x, hx, hfx⟩ : ∃ x ∈ ball p r, f x ≠ 0 := by
      by_contra! hall
      exact hf0 (eventuallyEq_iff_exists_mem.2 ⟨ball p r, ball_mem_nhds p hr, hall⟩)
    have hgx : (e ∘ g) =ᶠ[𝓝 x] 0 := by
      have hf_ne := (hfr x (hr₁' hx)).continuousAt.eventually_ne hfx
      filter_upwards [isOpen_ball.mem_nhds hx, hf_ne] with y hy hfy
      have h0 : g y = 0 :=
        (smul_eq_zero.1 (hfg_ball (mem_ball.1 (hr₃' hy)))).resolve_left hfy
      simp [h0]
    have heg : (e ∘ g) =ᶠ[𝓝 p] 0 := eventuallyEq_iff_exists_mem.2 ⟨ball p r, ball_mem_nhds p hr,
      (hgr.mono hr₂').eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball p r).isPreconnected hx hgx⟩
    exact heg.mono fun y hy ↦ UniformSpace.Completion.coe_injective F (by simpa [e] using hy)
  · rintro (hf0 | hg0)
    · exact hf0.mono fun x hx ↦ by simp [hx]
    · exact hg0.mono fun x hx ↦ by simp [hx]

/-- The product of two scalar analytic germs at `p` vanishes near `p` if and only if one of the
factors vanishes near `p`. -/
theorem AnalyticAt.mul_eventuallyEq_zero_iff {f g : E → 𝕜} {p : E}
    (hf : AnalyticAt 𝕜 f p) (hg : AnalyticAt 𝕜 g p) :
    f * g =ᶠ[𝓝 p] 0 ↔ f =ᶠ[𝓝 p] 0 ∨ g =ᶠ[𝓝 p] 0 :=
  hf.smul_eventuallyEq_zero_iff hg

/-- A finite product of scalar analytic germs at `p` vanishes near `p` if and only if one of its
factors vanishes near `p`. -/
theorem Finset.prod_eventuallyEq_zero_iff_of_analyticAt {ι : Type*} {f : ι → E → 𝕜} {p : E}
    (s : Finset ι) (hf : ∀ i ∈ s, AnalyticAt 𝕜 (f i) p) :
    (∏ i ∈ s, f i) =ᶠ[𝓝 p] 0 ↔ ∃ i ∈ s, f i =ᶠ[𝓝 p] 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, Finset.notMem_empty, false_and, exists_false, iff_false]
    intro h
    exact one_ne_zero (h.self_of_nhds : (1 : 𝕜) = 0)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha,
      (hf a (Finset.mem_insert_self a s)).mul_eventuallyEq_zero_iff
        (s.analyticAt_prod fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi), Finset.exists_mem_insert]

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

/-- **Simultaneous general position for a finite family.** Given finitely many functions on
`E × 𝕜` analytic at `p`, there are a continuous linear automorphism `L` and a point `q` with
`L q = p` in which every member not vanishing on a neighborhood of `p` has finite analytic order
in the last variable at `q.2`. Identically zero germs are ignored rather than excluded. -/
theorem TauCeti.exists_continuousLinearEquiv_forall_analyticOrderAt_ne_top {ι : Type*} [Finite ι]
    {f : ι → E × 𝕜 → F} {p : E × 𝕜} (hf : ∀ i, AnalyticAt 𝕜 (f i) p) :
    ∃ (L : (E × 𝕜) ≃L[𝕜] E × 𝕜) (q : E × 𝕜), L q = p ∧
      ∀ i, ¬f i =ᶠ[𝓝 p] 0 → analyticOrderAt (fun t ↦ f i (L (q.1, t))) q.2 ≠ ⊤ := by
  classical
  let := Fintype.ofFinite ι
  let e : F →L[𝕜] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  let s : Finset ι := Finset.univ.filter fun i ↦ ¬f i =ᶠ[𝓝 p] 0
  -- Pair each nonvanishing germ with a continuous linear functional so its scalar projection is
  -- still nonvanishing near `p`, then put the product of those scalar projections in general
  -- position.
  have hℓ (i : s) : ∃ ℓ : StrongDual 𝕜 F, ¬(ℓ ∘ f i.1) =ᶠ[𝓝 p] 0 := by
    have hi : ¬f i.1 =ᶠ[𝓝 p] 0 := (Finset.mem_filter.1 i.2).2
    obtain ⟨r, hr, hfr⟩ := ((e.analyticAt _).comp (hf i.1)).exists_ball_analyticOnNhd
    obtain ⟨y, hy, hfy⟩ : ∃ y ∈ ball p r, e (f i.1 y) ≠ 0 := by
      by_contra! hall
      refine hi ?_
      filter_upwards [ball_mem_nhds p hr] with y hy
      exact UniformSpace.Completion.coe_injective F (by simpa [e] using hall y hy)
    obtain ⟨ℓ', hℓ'y⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hfy
    refine ⟨ℓ'.comp e, fun h0 ↦ ?_⟩
    let : NormedSpace ℝ (E × 𝕜) := NormedSpace.restrictScalars ℝ 𝕜 (E × 𝕜)
    have han : AnalyticOnNhd 𝕜 (ℓ'.comp e ∘ f i.1) (ball p r) :=
      fun z hz ↦ (ℓ'.analyticAt _).comp (hfr z hz)
    exact hℓ'y (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball p r).isPreconnected (mem_ball_self hr) h0 hy)
  choose ℓ hℓ using hℓ
  let g : s → E × 𝕜 → 𝕜 := fun i ↦ ℓ i ∘ f i.1
  have hg (i : s) : AnalyticAt 𝕜 (g i) p := ((ℓ i).analyticAt _).comp (hf i.1)
  have hprod0 : ¬(∏ i : s, g i) =ᶠ[𝓝 p] 0 := by
    rw [Finset.univ.prod_eventuallyEq_zero_iff_of_analyticAt fun i _ ↦ hg i]
    rintro ⟨i, -, hi⟩
    exact hℓ i hi
  obtain ⟨L, q, hLq, hord⟩ :=
    (Finset.univ.analyticAt_prod fun i _ ↦ hg i).exists_continuousLinearEquiv_analyticOrderAt_ne_top
      hprod0
  refine ⟨L, q, hLq, fun i hi htop ↦ hord ?_⟩
  let i' : s := ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
  rw [analyticOrderAt_eq_top] at htop ⊢
  filter_upwards [htop] with t ht
  simp only [Finset.prod_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ i') (by simp [g, i', ht])

end
