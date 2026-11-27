/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.Mazur
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Convex energies at weak limits, by Mazur's lemma

Let `f` be a real function, convex on a real-convex set `s` of a locally convex space `E`, and
lower semicontinuous within `s` at a point `x` in the original topology. If a family `uᵢ` in `s`
converges weakly to `x`, then

`f x ≤ liminf f (uᵢ)`

(`ConvexOn.le_liminf_of_tendsto_weak`, stated in `EReal` so that no boundedness is needed). The
proof is Mazur's lemma: if `f (uᵢ) ≤ c` frequently, the weak limit `x` lies in the closure, in the
original topology, of the convex hull of those `uᵢ`
(`TauCeti.mem_closure_convexHull_range_of_tendsto_weak`), and that hull lies in the convex
sublevel set `{y ∈ s | f y ≤ c}`; lower semicontinuity at `x` then gives `f x ≤ c`
(`ConvexOn.le_of_tendsto_weak_of_frequently_le`). The family is only used along the indices
where `f (uᵢ) ≤ c`, that is along a subfamily realizing the lower limit: convex combinations of
the whole family do not control the limiting energy.

Only lower semicontinuity at the limit point is used, and `s` need not be closed. Global weak
lower semicontinuity of lower semicontinuous convex functions is
`QuasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm`; this file gives the sequential route.
For a complex space, convexity is real convexity.

## Main results

* `ConvexOn.le_of_tendsto_weak_of_frequently_le`: a bound `f (uᵢ) ≤ c` holding frequently passes
  to the weak limit.
* `ConvexOn.le_liminf_of_tendsto_weak`: `f x ≤ liminf f (uᵢ)`, in `EReal`.
-/

public section

open Filter Set Topology

variable {𝕜 E : Type*} [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]
  {ι : Type*} {l : Filter ι} {s : Set E} {f : E → ℝ} {u : ι → E} {x : E}

namespace ConvexOn

/-- **A convex energy at a weak limit, along a subfamily.** If `f` is convex on `s` and lower
semicontinuous within `s` at `x`, the family `uᵢ` lies eventually in `s` and converges weakly to
`x`, and `f (uᵢ) ≤ c` frequently, then `f x ≤ c`. -/
theorem le_of_tendsto_weak_of_frequently_le (hf : ConvexOn ℝ s f)
    (hfx : LowerSemicontinuousWithinAt f s x) (hus : ∀ᶠ i in l, u i ∈ s)
    (hu : Tendsto (fun i ↦ toWeakSpace 𝕜 E (u i)) l (𝓝 (toWeakSpace 𝕜 E x))) {c : ℝ}
    (hc : ∃ᶠ i in l, f (u i) ≤ c) : f x ≤ c := by
  set P : ι → Prop := fun i ↦ u i ∈ s ∧ f (u i) ≤ c
  have hP : ∃ᶠ i in l, P i := hc.and_eventually hus |>.mono fun _ h ↦ ⟨h.2, h.1⟩
  have : (comap ((↑) : Subtype P → ι) l).NeBot := comap_neBot fun _ ht ↦ by
    obtain ⟨i, hiP, hi⟩ := (hP.and_eventually ht).exists
    exact ⟨⟨i, hiP⟩, hi⟩
  -- Mazur: `x` is in the closure of the convex hull of the `uᵢ` with `P i`.
  have hx := TauCeti.mem_closure_convexHull_range_of_tendsto_weak (𝕜 := 𝕜)
    (u := fun i : Subtype P ↦ u i) (hu.comp tendsto_comap)
  have hsub : convexHull ℝ (range fun i : Subtype P ↦ u i) ⊆ {y ∈ s | f y ≤ c} :=
    convexHull_min (range_subset_iff.mpr fun i ↦ i.property) (hf.convex_le c)
  by_contra! hlt
  obtain ⟨U, hU, hUf⟩ := mem_nhdsWithin.mp (hfx c hlt)
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff_nhds.mp hx U (hU.mem_nhds hUf.1)
  exact (hsub hy).2.not_gt (hUf.2 ⟨hyU, (hsub hy).1⟩)

/-- **A convex energy is sequentially weakly lower semicontinuous at a point of lower
semicontinuity**: if `f` is convex on `s` and lower semicontinuous within `s` at `x`, and the
family `uᵢ` lies eventually in `s` and converges weakly to `x`, then `f x ≤ liminf f (uᵢ)`. The
lower limit is taken in `EReal`, so no boundedness of `f (uᵢ)` is assumed. -/
theorem le_liminf_of_tendsto_weak (hf : ConvexOn ℝ s f)
    (hfx : LowerSemicontinuousWithinAt f s x) (hus : ∀ᶠ i in l, u i ∈ s)
    (hu : Tendsto (fun i ↦ toWeakSpace 𝕜 E (u i)) l (𝓝 (toWeakSpace 𝕜 E x))) :
    (f x : EReal) ≤ liminf (fun i ↦ (f (u i) : EReal)) l := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
  induction c using EReal.rec with
  | bot => exact absurd hc not_lt_bot
  | top => exact le_top
  | coe c =>
    refine EReal.coe_le_coe_iff.mpr (hf.le_of_tendsto_weak_of_frequently_le hfx hus hu ?_)
    exact (frequently_lt_of_liminf_lt (by isBoundedDefault) hc).mono fun _ h ↦
      (EReal.coe_lt_coe_iff.mp h).le

end ConvexOn
