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

end LocalModels

end TauCeti
