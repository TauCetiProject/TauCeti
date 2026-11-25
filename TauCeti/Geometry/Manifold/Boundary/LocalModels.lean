/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.OneDimensional
import TauCeti.Topology.OpenPartialHomeomorph.Constructions

/-!
# Compact spaces locally modelled on the half-line

Compactified spaces of trajectories in Morse theory are not given with an atlas but with local
models: each broken trajectory has a neighbourhood homeomorphic to `[0, ε)`, and each unbroken
trajectory a neighbourhood homeomorphic to an open subset of a line. This file assembles such local
models into an atlas modelled on the half-line `EuclideanHalfSpace 1`
(`TauCeti.exists_chartedSpace_euclideanHalfSpace_one_boundary_eq`), and transfers to these spaces
the counts of boundary points of compact one-dimensional manifolds from
`TauCeti.Geometry.Manifold.Boundary.OneDimensional`:

* the points with a half-open model are finitely many
  (`TauCeti.finite_of_forall_exists_homeomorph_Ico`) and, in a Hausdorff space, even in number
  (`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`);
* if the remaining points are oriented by charts to `ℝ` with increasing transition maps, the
  points with a half-open model along which the orientation points outward are as many as those
  along which it points inward (`TauCeti.ncard_eq_ncard_of_forall_exists_homeomorph_Ico`).

A half-open local model also transports between two ways of recording the points of a
compactified space: along maps `ι` and `π` identifying a set `R` near a point `a` with the closure
of a set `P` near `ι a`, a half-open model of `R` at `a` gives one of the closure of `P` at `ι a`
(`TauCeti.exists_homeomorph_Ico_closure_of_homeomorph_Ico`). Its two steps are that a half-open
arc stays near its endpoint on a shorter interval (`TauCeti.exists_pos_forall_lt_mem`) and that a
continuous map on `[0, δ)` sending the positive points into `P` sends `0` into the closure of `P`
(`TauCeti.mem_closure_of_forall_ne_zero`).

The second statement is the signed count of the endpoints of a compact oriented one-manifold,
which makes the signed counts of broken trajectories cancel in the proof that the integral Morse
boundary squares to zero, as the first makes them cancel modulo two.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  Appendix (the classification of one-manifolds).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (compactified trajectory spaces as compact oriented
  one-manifolds with boundary).
-/

public section

noncomputable section

open Function Set Topology

open scoped Manifold

open TauCeti.EuclideanHalfSpace

namespace TauCeti

section LocalModels

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Set X}

/-- A point with a neighbourhood homeomorphic to `[0, ε)`, by a homeomorphism sending `0` to it,
lies in a chart of the half-line model reading it with coordinate `0`. -/
private theorem exists_openPartialHomeomorph_coord_eq_zero {x : X} {N : Set X} (hN : N ∈ 𝓝 x)
    {ε : ℝ} (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N) (hex : (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x) :
    ∃ c : OpenPartialHomeomorph X (EuclideanHalfSpace 1), x ∈ c.source ∧ (c x).val 0 = 0 := by
  have hx : x ∈ interior N := mem_interior_iff_mem_nhds.2 hN
  let g : interior N → EuclideanHalfSpace 1 := fun y ↦
    ((homeomorphNormalIio ε).symm (e.symm (inclusion interior_subset y)) : EuclideanHalfSpace 1)
  have hg : IsOpenEmbedding g :=
    (isOpen_normalIio ε).isOpenEmbedding_subtypeVal.comp
      ((homeomorphNormalIio ε).symm.isOpenEmbedding.comp
        (e.symm.isOpenEmbedding.comp
          (IsOpenEmbedding.inclusion interior_subset
            (isOpen_interior.preimage continuous_subtypeVal))))
  obtain ⟨c, hcs, hcg⟩ :=
    OpenPartialHomeomorph.exists_source_eq_of_isOpenEmbedding isOpen_interior hg ⟨x, hx⟩
  have hxc : x ∈ c.source := hcs ▸ hx
  have hcx : c x = g ⟨x, hx⟩ := hcg ⟨x, hx⟩
  refine ⟨c, hxc, ?_⟩
  have he : e.symm (inclusion interior_subset ⟨x, hx⟩) = ⟨0, left_mem_Ico.2 hε⟩ :=
    e.symm_apply_eq.2 (Subtype.ext hex.symm)
  rw [hcx, ← coe_homeomorphNormalIio, Homeomorph.apply_symm_apply, he]

/-- A point with a neighbourhood homeomorphic to an open subset of a one-dimensional real normed
space lies in a chart of the half-line model reading it with positive coordinate. -/
private theorem exists_openPartialHomeomorph_coord_pos (hF : Module.finrank ℝ F = 1) {x : X}
    {N : Set X} (hN : N ∈ 𝓝 x) {V : Set F} (hV : IsOpen V) (e : V ≃ₜ N) :
    ∃ c : OpenPartialHomeomorph X (EuclideanHalfSpace 1), x ∈ c.source ∧ 0 < (c x).val 0 := by
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  have hx : x ∈ interior N := mem_interior_iff_mem_nhds.2 hN
  let L : F ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hF, finrank_euclideanSpace_fin])
  let g : interior N → EuclideanHalfSpace 1 := fun y ↦
    interiorEmbedding 0 (L (e.symm (inclusion interior_subset y)))
  have hg : IsOpenEmbedding g :=
    (isOpenEmbedding_interiorEmbedding 0).comp (L.toHomeomorph.isOpenEmbedding.comp
      (hV.isOpenEmbedding_subtypeVal.comp (e.symm.isOpenEmbedding.comp
        (IsOpenEmbedding.inclusion interior_subset
          (isOpen_interior.preimage continuous_subtypeVal)))))
  obtain ⟨c, hcs, hcg⟩ :=
    OpenPartialHomeomorph.exists_source_eq_of_isOpenEmbedding isOpen_interior hg ⟨x, hx⟩
  have hxc : x ∈ c.source := hcs ▸ hx
  have hcx : c x = g ⟨x, hx⟩ := hcg ⟨x, hx⟩
  refine ⟨c, hxc, ?_⟩
  rw [hcx]
  exact (range_interiorEmbedding 0).subset (mem_range_self _)

/-- **Local models assemble into a one-dimensional manifold with boundary.** If each point of `B`
has a neighbourhood `N` with a homeomorphism `[0, ε) ≃ₜ N` sending `0` to it, and each other point
has a neighbourhood homeomorphic to an open subset of a one-dimensional real normed space `F`, then
`X` carries an atlas modelled on the half-line `EuclideanHalfSpace 1` whose boundary is exactly
`B`. The atlas is topological: no compatibility of its charts is claimed. -/
theorem exists_chartedSpace_euclideanHalfSpace_one_boundary_eq (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) :
    ∃ _ : ChartedSpace (EuclideanHalfSpace 1) X, (𝓡∂ 1).boundary X = B := by
  have hc (x : X) : ∃ c : OpenPartialHomeomorph X (EuclideanHalfSpace 1),
      x ∈ c.source ∧ ((c x).val 0 = 0 ↔ x ∈ B) := by
    by_cases hxB : x ∈ B
    · obtain ⟨N, hN, ε, hε, e, hex⟩ := hB x hxB
      obtain ⟨c, hxc, hcx⟩ := exists_openPartialHomeomorph_coord_eq_zero hN hε e hex
      exact ⟨c, hxc, iff_of_true hcx hxB⟩
    · obtain ⟨N, hN, V, hV, ⟨e⟩⟩ := hX x hxB
      obtain ⟨c, hxc, hcx⟩ := exists_openPartialHomeomorph_coord_pos hF hN hV e
      exact ⟨c, hxc, iff_of_false hcx.ne' hxB⟩
  choose c hxc hcB using hc
  let C : ChartedSpace (EuclideanHalfSpace 1) X :=
    { atlas := range c
      chartAt := c
      mem_chart_source := hxc
      chart_mem_atlas := mem_range_self }
  refine ⟨C, Set.ext fun x ↦ ?_⟩
  rw [ModelWithCorners.mem_boundary_euclideanHalfSpace_one_iff (hxc x)]
  exact hcB x

/-- A homeomorphism `[0, ε) ≃ₜ N` sending `0` to `x` gives an injective path from `x` on
`[0, ε / 2]`. At each positive time `s` it is the homeomorphism, so a function strictly monotone
along the homeomorphism near the parameter `s` is strictly monotone along the path near `s`. -/
private theorem exists_path_of_homeomorph_Ico {x : X} {N : Set X} {ε : ℝ} (hε : 0 < ε)
    (e : Ico (0 : ℝ) ε ≃ₜ N) (hex : (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x) :
    ∃ γ : ℝ → X, γ 0 = x ∧ ContinuousOn γ (Icc 0 (ε / 2)) ∧ InjOn γ (Icc 0 (ε / 2)) ∧
      ∀ s ∈ Ioo 0 (ε / 2), ∃ t : Ico (0 : ℝ) ε, 0 < (t : ℝ) ∧ γ s = e t ∧
        ∀ {β : Type} [Preorder β] (f : X → β),
          StrictMonoAt (fun r ↦ f (e r)) t → StrictMonoAt (f ∘ γ) s := by
  classical
  set γ : ℝ → X := fun r ↦ if h : r ∈ Ico 0 ε then (e ⟨r, h⟩ : X) else x
  have hγ : ∀ r (h : r ∈ Ico 0 ε), γ r = e ⟨r, h⟩ := fun r h ↦ by simp only [γ, h, ↓reduceDIte]
  have hsub : Icc 0 (ε / 2) ⊆ Ico 0 ε := fun r hr ↦ ⟨hr.1, by linarith [hr.2]⟩
  refine ⟨γ, by rw [hγ 0 (left_mem_Ico.2 hε)]; exact hex, ?_, fun r hr r' hr' h ↦ ?_,
    fun s hs ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (Icc 0 (ε / 2)).domRestrict γ =
        fun r : Icc (0 : ℝ) (ε / 2) ↦ (e ⟨r, hsub r.property⟩ : X) :=
      funext fun r ↦ hγ r (hsub r.property)
    rw [this]
    exact continuous_subtypeVal.comp (e.continuous.comp (continuous_subtypeVal.subtype_mk _))
  · rw [hγ r (hsub hr), hγ r' (hsub hr')] at h
    exact congrArg Subtype.val (e.injective (Subtype.ext h))
  · have hsI : s ∈ Ico 0 ε := ⟨hs.1.le, by linarith [hs.2]⟩
    refine ⟨⟨s, hsI⟩, hs.1, hγ s hsI, fun f hf ↦ ?_⟩
    obtain ⟨U, hU, hmono⟩ := strictMonoAt_iff.1 hf
    obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ _ _).1 hU
    refine StrictMonoOn.strictMonoAt (s := V ∩ Ioo 0 ε) (fun r hr r' hr' hrr' ↦ ?_)
      (Filter.inter_mem hV (Ioo_mem_nhds hs.1 (by linarith [hs.2])))
    have hrI : r ∈ Ico 0 ε := Ioo_subset_Ico_self hr.2
    have hr'I : r' ∈ Ico 0 ε := Ioo_subset_Ico_self hr'.2
    simp only [comp_apply, hγ r hrI, hγ r' hr'I]
    exact hmono (hVU (mem_preimage.2 hr.1)) (hVU (mem_preimage.2 hr'.1)) (Subtype.mk_lt_mk.2 hrr')

variable [CompactSpace X]

/-- **A compact space locally modelled on the half-line has finitely many endpoints.** Let `X` be
compact, and let `B` be a set of points of `X` such that

* each `x ∈ B` has a neighbourhood `N` with a homeomorphism `[0, ε) ≃ₜ N` sending `0` to `x`, and
* each `x ∉ B` has a neighbourhood homeomorphic to an open subset of a one-dimensional real
  normed space `F`.

Then `B` is finite. -/
theorem finite_of_forall_exists_homeomorph_Ico (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) :
    B.Finite := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hC ▸ ModelWithCorners.finite_boundary_euclideanHalfSpace_one

/-- **A compact Hausdorff space locally modelled on the half-line has an even number of
endpoints.** Let `X` be compact and Hausdorff, and let `B` be a set of points of `X` such that

* each `x ∈ B` has a neighbourhood `N` with a homeomorphism `[0, ε) ≃ₜ N` sending `0` to `x`, and
* each `x ∉ B` has a neighbourhood homeomorphic to an open subset of a one-dimensional real
  normed space `F`.

Then `B` has an even number of elements; it is finite by
`TauCeti.finite_of_forall_exists_homeomorph_Ico`. This is
`TauCeti.ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one` for a space described by
local homeomorphisms rather than by an atlas. Local gluing describes a neighbourhood of a broken
trajectory in this way (compare `TauCeti.exists_homeomorph_closure_splitGluingPairs`), so for a
compactified space of index-two trajectories `B` is the set of broken trajectories. -/
theorem even_ncard_of_forall_exists_homeomorph_Ico [T2Space X] (hF : Module.finrank ℝ F = 1)
    (hB : ∀ x ∈ B, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x)
    (hX : ∀ x ∉ B, ∃ N ∈ 𝓝 x, ∃ V : Set F, IsOpen V ∧ Nonempty (V ≃ₜ N)) :
    Even B.ncard := by
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq hF hB hX
  exact hC ▸ ModelWithCorners.even_ncard_boundary_euclideanHalfSpace_one

/-- **A compact oriented space locally modelled on the half-line has as many outward as inward
endpoints.** Let `X` be compact and Hausdorff, oriented away from two sets `Bₒ` and `Bᵢ` by a set
`𝒪` of charts to `ℝ`: they cover the points outside `Bₒ ∪ Bᵢ`, and any two of them have a
transition map increasing near every common point. Suppose that

* each `x ∈ Bₒ` has a neighbourhood `N` with a homeomorphism `e : [0, ε) ≃ₜ N` sending `0` to
  `x`, along which the charts of `𝒪` decrease: the orientation points outward at `x`;
* each `x ∈ Bᵢ` has such a neighbourhood and homeomorphism, along which the charts of `𝒪`
  increase: the orientation points inward at `x`.

Then `Bₒ` and `Bᵢ` have the same number of elements; they are finite by
`TauCeti.finite_of_forall_exists_homeomorph_Ico`. With the outward-first convention this says
that the signed count of the endpoints vanishes. It is
`TauCeti.ModelWithCorners.ncard_eq_ncard_boundary_euclideanHalfSpace_one` for a space described
by local homeomorphisms rather than by an atlas, and refines
`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`. -/
theorem ncard_eq_ncard_of_forall_exists_homeomorph_Ico [T2Space X]
    {𝒪 : Set (OpenPartialHomeomorph X ℝ)} {Bₒ Bᵢ : Set X}
    (hcover : ∀ x, x ∉ Bₒ → x ∉ Bᵢ → ∃ c ∈ 𝒪, x ∈ c.source)
    (hcompat : ∀ c ∈ 𝒪, ∀ c' ∈ 𝒪, ∀ x ∈ c.source ∩ c'.source, StrictMonoAt (c' ∘ c.symm) (c x))
    (hBₒ : ∀ x ∈ Bₒ, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x ∧ ∀ t : Ico (0 : ℝ) ε, 0 < (t : ℝ) → ∀ c ∈ 𝒪,
        (e t : X) ∈ c.source → StrictAntiAt (fun s ↦ c (e s)) t)
    (hBᵢ : ∀ x ∈ Bᵢ, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x ∧ ∀ t : Ico (0 : ℝ) ε, 0 < (t : ℝ) → ∀ c ∈ 𝒪,
        (e t : X) ∈ c.source → StrictMonoAt (fun s ↦ c (e s)) t) :
    Bₒ.ncard = Bᵢ.ncard := by
  have hmodel : ∀ x ∈ Bₒ ∪ Bᵢ, ∃ N ∈ 𝓝 x, ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hε⟩ : X) = x := by
    rintro x (hx | hx)
    · obtain ⟨N, hN, ε, hε, e, hex, -⟩ := hBₒ x hx
      exact ⟨N, hN, ε, hε, e, hex⟩
    · obtain ⟨N, hN, ε, hε, e, hex, -⟩ := hBᵢ x hx
      exact ⟨N, hN, ε, hε, e, hex⟩
  obtain ⟨C, hC⟩ := exists_chartedSpace_euclideanHalfSpace_one_boundary_eq (F := ℝ)
    (Module.finrank_self ℝ) hmodel fun x hx ↦ by
      obtain ⟨c, -, hxc⟩ := hcover x (fun h ↦ hx (Or.inl h)) fun h ↦ hx (Or.inr h)
      exact ⟨c.source, c.open_source.mem_nhds hxc, c.target, c.open_target,
        ⟨c.toHomeomorphSourceTarget.symm⟩⟩
  refine ModelWithCorners.ncard_eq_ncard_boundary_euclideanHalfSpace_one (fun x hx ↦ ?_) hcompat
    hC (fun b hb ↦ ?_) fun b hb ↦ ?_
  · rw [hC] at hx
    exact hcover x (fun h ↦ hx (Or.inl h)) fun h ↦ hx (Or.inr h)
  · obtain ⟨N, -, ε, hε, e, hex, he⟩ := hBₒ b hb
    obtain ⟨γ, hγ0, hγc, hγi, hγe⟩ := exists_path_of_homeomorph_Ico hε e hex
    refine ⟨γ, ε / 2, half_pos hε, hγ0, hγc, hγi, fun s hs c hc hsc ↦ ?_⟩
    obtain ⟨t, ht0, hγt, hcomp⟩ := hγe s hs
    exact strictMonoAt_toDual_comp_iff.1 <| hcomp (OrderDual.toDual ∘ c)
      (strictMonoAt_toDual_comp_iff.2 (he t ht0 c hc (hγt ▸ hsc)))
  · obtain ⟨N, -, ε, hε, e, hex, he⟩ := hBᵢ b hb
    obtain ⟨γ, hγ0, hγc, hγi, hγe⟩ := exists_path_of_homeomorph_Ico hε e hex
    refine ⟨γ, ε / 2, half_pos hε, hγ0, hγc, hγi, fun s hs c hc hsc ↦ ?_⟩
    obtain ⟨t, ht0, hγt, hcomp⟩ := hγe s hs
    exact hcomp c (he t ht0 c hc (hγt ▸ hsc))

/-- A half-open arc stays in any neighbourhood of its endpoint on a shorter interval `[0, ε)`. -/
theorem exists_pos_forall_lt_mem {Y : Type*} [TopologicalSpace Y] {N U : Set Y} {δ : ℝ}
    (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N) (hU : U ∈ 𝓝 (e ⟨0, left_mem_Ico.2 hδ⟩ : Y)) :
    ∃ ε > 0, ∀ s : Ico (0 : ℝ) δ, (s : ℝ) < ε → (e s : Y) ∈ U := by
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype _ _ _).1
    ((continuous_subtypeVal.comp e.continuous).continuousAt.preimage_mem_nhds hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨ε, hε, fun s hs ↦ @hVU s (hball ?_)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg s.property.1]
  exact hs

/-- If a continuous map on `[0, δ)` sends every positive point into `P`, it sends `0` into the
closure of `P`. -/
theorem mem_closure_of_forall_ne_zero {Z : Type*} [TopologicalSpace Z] {P : Set Z}
    {δ : ℝ} (hδ : 0 < δ) {g : Ico (0 : ℝ) δ → Z} (hg : Continuous g)
    (hP : ∀ s : Ico (0 : ℝ) δ, (s : ℝ) ≠ 0 → g s ∈ P) : g ⟨0, left_mem_Ico.2 hδ⟩ ∈ closure P := by
  -- `g 0` is the limit of the points `g (δ / (n + 2))`.
  let u : ℕ → Ico (0 : ℝ) δ := fun n ↦ ⟨δ / ((n + 2 : ℕ) : ℝ), by positivity, by
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith⟩
  have hu : Filter.Tendsto u Filter.atTop (𝓝 ⟨0, left_mem_Ico.2 hδ⟩) :=
    tendsto_subtype_rng.2 ((tendsto_const_div_atTop_nhds_zero_nat δ).comp
      (Filter.tendsto_add_atTop_nat 2))
  exact mem_closure_of_tendsto ((hg.tendsto _).comp hu) (.of_forall fun n ↦ hP _ (by positivity))

/-- **Transporting a half-open local model into a closure.** Let `P` be a set in a space `Z`, and
`a` a point of a set `R` in a space `Y` with a neighbourhood `N` in `R` homeomorphic to `[0, δ)`,
by a homeomorphism sending `0` to `a`. Suppose that maps `ι : Y → Z` and `π : Z → Y`, with `ι`
continuous on `R` and `π` continuous, identify `R` near `a` with the closure of `P` near
`b = ι a`:

* `π ∘ ι` is the identity on `R`;
* `ι` sends the points of `R` near `a`, other than `a`, into `P`;
* near `b`, every point `q` of the closure of `P` is `ι (π q)` with `π q ∈ R`.

Then `b` lies in the closure of `P`, and has a neighbourhood there homeomorphic to `[0, δ')`, by a
homeomorphism sending `0` to `b`. This transports the half-open charts of compactified moduli
spaces between two ways of recording their points. -/
theorem exists_homeomorph_Ico_closure_of_homeomorph_Ico {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] {P : Set Z} {R N : Set Y} {a : Y} {b : Z} (π : Z → Y) (ι : Y → Z)
    (hπ : Continuous π) (hι : ContinuousOn ι R) (hπι : ∀ v ∈ R, π (ι v) = v) (hιa : ι a = b)
    (hP : ∀ᶠ v in 𝓝[R \ {a}] a, ι v ∈ P)
    (hcov : ∀ᶠ q in 𝓝[closure P] b, π q ∈ R ∧ ι (π q) = q)
    {δ : ℝ} (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N) (he : (e ⟨0, left_mem_Ico.2 hδ⟩ : Y) = a)
    (hNR : N ⊆ R) (hN : N ∈ 𝓝[R] a) :
    ∃ hb : b ∈ closure P, ∃ N' ∈ 𝓝 (⟨b, hb⟩ : closure P), ∃ (δ' : ℝ) (hδ' : 0 < δ')
      (e' : Ico (0 : ℝ) δ' ≃ₜ N'), (e' ⟨0, left_mem_Ico.2 hδ'⟩ : closure P) = ⟨b, hb⟩ := by
  obtain ⟨U, hU, hUP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hP
  set g : Ico (0 : ℝ) δ → Y := fun s ↦ e s
  have hg : Continuous g := continuous_subtypeVal.comp e.continuous
  have haR : a ∈ R := he ▸ hNR (e _).property
  have hgR (s : Ico (0 : ℝ) δ) : g s ∈ R := hNR (e s).property
  -- On a shorter interval `[0, δ')`, the arc stays in `U`, so `ι` sends it into `P` but at `0`.
  obtain ⟨ε, hε, hεU⟩ := exists_pos_forall_lt_mem hδ e (he.symm ▸ hU)
  set δ' := min ε δ
  have hδ' : 0 < δ' := lt_min hε hδ
  let incl : Ico (0 : ℝ) δ' → Ico (0 : ℝ) δ := inclusion (Ico_subset_Ico_right (min_le_right _ _))
  have hP' (s : Ico (0 : ℝ) δ') (hs : (s : ℝ) ≠ 0) : ι (g (incl s)) ∈ P :=
    hUP ⟨hεU _ (s.property.2.trans_le (min_le_left _ _)), hgR _, fun h ↦
      hs (congrArg Subtype.val (e.injective (Subtype.ext (h.trans he.symm))))⟩
  have hG₀ : Continuous fun s ↦ ι (g (incl s)) :=
    hι.comp_continuous (hg.comp (continuous_inclusion _)) fun _ ↦ hgR _
  have h0 : ι (g (incl ⟨0, left_mem_Ico.2 hδ'⟩)) = b := (congrArg ι he).trans hιa
  have hb : b ∈ closure P := h0 ▸ mem_closure_of_forall_ne_zero hδ' hG₀ hP'
  have hmem (s : Ico (0 : ℝ) δ') : ι (g (incl s)) ∈ closure P := by
    by_cases hs : (s : ℝ) = 0
    · rw [show s = ⟨0, left_mem_Ico.2 hδ'⟩ from Subtype.ext hs, h0]
      exact hb
    · exact subset_closure (hP' s hs)
  let G : Ico (0 : ℝ) δ' → closure P := fun s ↦ ⟨ι (g (incl s)), hmem s⟩
  have hG : IsEmbedding G := by
    refine IsEmbedding.of_comp (hG₀.subtype_mk _) (hπ.comp continuous_subtypeVal) ?_
    have : (π ∘ Subtype.val) ∘ G = g ∘ incl := funext fun s ↦ hπι _ (hgR _)
    rw [this]
    exact (IsEmbedding.subtypeVal.comp e.isEmbedding).comp (IsEmbedding.inclusion _)
  -- The image of `[0, δ')` is open in `N`, so it is a neighbourhood of `a` in `R`, and near `b`
  -- the closure of `P` is its image under `ι`.
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1
    (e.isOpenMap {s | (s : ℝ) < δ'} (isOpen_lt continuous_subtypeVal continuous_const))
  have haO : a ∈ O := by
    have : e ⟨0, left_mem_Ico.2 hδ⟩ ∈ e '' {s | (s : ℝ) < δ'} := mem_image_of_mem _ hδ'
    rw [← hOe, mem_preimage, he] at this
    exact this
  have hπt : Filter.Tendsto π (𝓝[closure P] b) (𝓝[R] a) := tendsto_nhdsWithin_iff.2
    ⟨(hιa ▸ hπι a haR) ▸ (hπ.tendsto b).mono_left nhdsWithin_le_nhds, hcov.mono fun _ hq ↦ hq.1⟩
  have hrange : range G ∈ 𝓝 (⟨b, hb⟩ : closure P) := by
    rw [mem_nhds_subtype_iff_nhdsWithin]
    filter_upwards [hπt (Filter.inter_mem hN (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds haO))), hcov]
      with q hq hq'
    have hqO : (⟨π q, hq.1⟩ : N) ∈ Subtype.val ⁻¹' O := mem_preimage.2 hq.2
    rw [hOe] at hqO
    obtain ⟨s, hs, hsq⟩ := hqO
    refine ⟨G ⟨s, s.property.1, hs⟩, mem_range_self _, ?_⟩
    simp only [G, g, incl]
    rw [hsq, hq'.2]
  -- The homeomorphism onto the range is `G` itself, which sends `0` to `ι a = b`.
  exact ⟨hb, range G, hrange, δ', hδ', hG.toHomeomorph, Subtype.ext h0⟩

end LocalModels

end TauCeti
