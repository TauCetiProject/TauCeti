/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.FilledHull
public import TauCeti.Topology.Schoenflies.LocallyFlat
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.Topology.Compactification.OnePoint.FilledHull
import TauCeti.Topology.ConnectedComponents

/-!
# The generalized Schoenflies theorem in finite-dimensional real normed spaces

Let `E` be a finite-dimensional real normed space of dimension `d = finrank ℝ E` and let
`f : sphere (0 : E) 1 → E` be an injective locally bicollared map (for instance, a locally flat
embedding). Embedding `E` into the unit sphere `Sᵈ` of `EuclideanSpace ℝ (Fin (d + 1))` through the
one-point compactification `onePointEquivSphereOfFinrankEq` turns `f` into an injective locally
bicollared sphere `σ : S(E) → Sᵈ` missing the point at infinity `p∞`.

By Brown's bicollaring and generalized Schoenflies theorems
(`TauCeti.Topology.Schoenflies.LocallyFlat`), `σ` has a global bicollar and `(range σ)ᶜ` splits
into two connected components: the component `U∞` of `p∞` and a second component `U₀` whose closure
`U₀ ∪ range σ` avoids `p∞`. Pulling `U₀` and its closure back to `E` identifies them with the
bounded inside `filledHull (range f) \ range f` and with the filled hull `filledHull (range f)`,
in every finite dimension `d ≥ 0` (including `d = 1`, where `(range f)ᶜ` in `E` has two unbounded
rays glued at `p∞` into `U∞`, and `d = 0`, where `S(E) = ∅` and `filledHull ∅ = {0}`).

Consequently `filledHull (range f)` is homeomorphic to `closedBall (0 : E) 1` by a homeomorphism
inverting `f` on `range f` and sending `range f` onto `sphere (0 : E) 1`, and `f` extends to a
closed embedding `closedBall (0 : E) 1 → E` carrying `ball (0 : E) 1` onto
`filledHull (range f) \ range f`.

## Main results

* `TauCeti.IsLocallyBicollared.exists_homeomorph_filledHull_range_closedBall` and
  `TauCeti.IsLocallyBicollared.exists_isClosedEmbedding_closedBall_filledHull`: the generalized
  Schoenflies theorem in `E` for injective locally bicollared spheres.
* `TauCeti.IsLocallyBicollared.isPathConnected_filledHull_sdiff_range`,
  `TauCeti.IsLocallyBicollared.isConnected_filledHull_sdiff_range`, and
  `TauCeti.IsLocallyBicollared.nonempty_filledHull_sdiff_range`: the bounded inside
  `filledHull (range f) \ range f` is path-connected, connected, and nonempty.
* `TauCeti.IsLocallyBicollared.closure_filledHull_sdiff_range` and
  `TauCeti.IsLocallyBicollared.frontier_filledHull_sdiff_range`: its closure is
  `filledHull (range f)` and its frontier is `range f`.
* `TauCeti.IsLocallyFlat.exists_homeomorph_filledHull_range_closedBall`,
  `TauCeti.IsLocallyFlat.exists_isClosedEmbedding_closedBall_filledHull`,
  `TauCeti.IsLocallyFlat.isPathConnected_filledHull_sdiff_range`,
  `TauCeti.IsLocallyFlat.isConnected_filledHull_sdiff_range`,
  `TauCeti.IsLocallyFlat.nonempty_filledHull_sdiff_range`,
  `TauCeti.IsLocallyFlat.closure_filledHull_sdiff_range`, and
  `TauCeti.IsLocallyFlat.frontier_filledHull_sdiff_range`: the corresponding statements for locally
  flat embeddings `f : sphere (0 : E) 1 → E`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
-/

public section

open Bornology Function Metric Module Set Topology
open scoped OnePoint

namespace TauCeti

section OnePointBridge

/-- In `OnePoint E ≃ₜ S`, if a complementary component `U₀` is disjoint from the component of `∞`
and its closure adds only points of `K`, then `closure U₀` misses `∞` and lies in the image of
`E`. -/
private lemma closure_connectedComponentIn_subset_range_onePoint {E S : Type*}
    [TopologicalSpace E] [TopologicalSpace S] {K : Set E} (Φ : OnePoint E ≃ₜ S) {q₀ : S}
    (hinf : Φ ∞ ∉ Φ '' (((↑) : E → OnePoint E) '' K))
    (hdisj : Disjoint (connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ (Φ ∞))
      (connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀))
    (hcl₀ : closure (connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀) =
      connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀ ∪
        Φ '' (((↑) : E → OnePoint E) '' K)) :
    closure (connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀) ⊆
      range (Φ ∘ ((↑) : E → OnePoint E)) := fun z hz ↦ by
  have hzne : z ≠ Φ ∞ := by
    rintro rfl
    exact (hcl₀ ▸ hz).elim (hdisj.notMem_of_mem_left (mem_connectedComponentIn hinf)) hinf
  obtain ⟨x, hx⟩ := show Φ.symm z ∈ range ((↑) : E → OnePoint E) from
    not_not.1 fun hn ↦ hzne (Φ.symm_apply_eq.1 (OnePoint.notMem_range_coe_iff.1 hn))
  exact ⟨x, by simp [hx]⟩

/-- In `OnePoint E ≃ₜ S`, the complementary component missing `∞` pulls back to `filledHull K \ K`,
and its closure pulls back to `filledHull K`. -/
private lemma preimage_connectedComponentIn_onePoint_sphere {E S : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace S] [CompactSpace S] {K : Set E} (hK : IsCompact K)
    (Φ : OnePoint E ≃ₜ S) {q₀ : S}
    (hinf : Φ ∞ ∉ Φ '' (((↑) : E → OnePoint E) '' K))
    (hdisj : Disjoint (connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ (Φ ∞))
      (connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀))
    (hcompl : (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ =
      connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ (Φ ∞) ∪
        connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀)
    (hcl₀ : closure (connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀) =
      connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀ ∪
        Φ '' (((↑) : E → OnePoint E) '' K)) :
    let ψ : E → S := Φ ∘ ((↑) : E → OnePoint E)
    let U₀ := connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ q₀
    closure U₀ ⊆ range ψ ∧ ψ ⁻¹' U₀ = filledHull K \ K ∧ ψ ⁻¹' closure U₀ = filledHull K := by
  intro ψ U₀
  have hψ : IsOpenEmbedding ψ := Φ.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  have hψK : Φ '' (((↑) : E → OnePoint E) '' K) = ψ '' K := image_image _ _ _
  have hcl_sub : closure U₀ ⊆ range ψ :=
    closure_connectedComponentIn_subset_range_onePoint Φ hinf hdisj hcl₀
  have hpre_U₀ : ψ ⁻¹' U₀ = filledHull K \ K := by
    refine Subset.antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    · have hxK : x ∉ K := fun h ↦ connectedComponentIn_subset _ _ hx (hψK.symm ▸ ⟨x, h, rfl⟩)
      have hU₀x : connectedComponentIn (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ (ψ x) = U₀ :=
        (connectedComponentIn_eq hx).symm
      have himg := hψ.isInducing.image_connectedComponentIn_preimage
        (F := (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ) (y := x)
        (hU₀x.symm ▸ (subset_closure.trans hcl_sub))
      rw [hψK, preimage_compl, hψ.injective.preimage_image, ← hψK, hU₀x] at himg
      have : CompactSpace (closure U₀) := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
      have hD_comp : IsCompact (ψ ⁻¹' closure U₀) := isCompact_iff_compactSpace.2
        (hψ.isEmbedding.homeomorphOfSubsetRange hcl_sub).symm.compactSpace
      have hsub : connectedComponentIn Kᶜ x ⊆ ψ ⁻¹' closure U₀ := by
        rw [← hψ.injective.preimage_image (connectedComponentIn Kᶜ x), himg]
        exact preimage_mono subset_closure
      exact ⟨mem_filledHull_iff.2 (hD_comp.isBounded.subset hsub), hxK⟩
    · have hxψ : ψ x ∈ (Φ '' (((↑) : E → OnePoint E) '' K))ᶜ :=
        hψK ▸ fun ⟨w, hw, hwx⟩ ↦ hx.2 (hψ.injective hwx ▸ hw)
      refine (hcompl ▸ hxψ).resolve_left fun hxinf ↦ ?_
      set W : Set (OnePoint E) := ((↑) : E → OnePoint E) '' connectedComponentIn Kᶜ x
      have hW_open : IsOpen (Φ '' W) :=
        Φ.isOpenMap _ (OnePoint.isOpenEmbedding_coe.isOpenMap _
          hK.isClosed.isOpen_compl.connectedComponentIn)
      have hW_cl : closure (Φ '' W) ⊆ Φ '' W ∪ Φ '' (((↑) : E → OnePoint E) '' K) := by
        rw [← Φ.image_closure]
        exact (image_mono (closure_image_coe_connectedComponentIn_subset hK.isClosed hx.1)).trans
          (by rw [image_union, image_union])
      have hsub := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hW_open
        ⟨ψ x, hxinf, ⟨x, mem_image_of_mem _ (mem_connectedComponentIn hx.2), rfl⟩⟩ fun z hz ↦
          (hW_cl hz.1).resolve_right (connectedComponentIn_subset _ _ hz.2)
      obtain ⟨_, ⟨y, _, hy⟩, hΦ⟩ := hsub (mem_connectedComponentIn hinf)
      exact OnePoint.coe_ne_infty y (hy.trans (Φ.injective hΦ))
  refine ⟨hcl_sub, hpre_U₀, ?_⟩
  rw [hcl₀, preimage_union, hpre_U₀, hψK, hψ.injective.preimage_image, sdiff_union_self,
    union_eq_left.2 subset_filledHull]

/-- Embed `E` into `Sᵈ` via `OnePoint E` and extract the global bicollar and inside component for an
injective locally bicollared sphere `f : sphere (0 : E) 1 → E`. -/
private lemma exists_isOpenEmbedding_sphere_filledHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : sphere (0 : E) 1 → E} (hf : IsLocallyBicollared f) (hinj : Injective f) :
    ∃ (ψ : E → sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1)
      (b : sphere (0 : E) 1 × ℝ →
        sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1)
      (q₀ : sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1),
      IsOpenEmbedding ψ ∧
      IsBicollar (ψ ∘ f) b ∧
      q₀ ∉ range (ψ ∘ f) ∧
      closure (connectedComponentIn (range (ψ ∘ f))ᶜ q₀) ⊆ range ψ ∧
      ψ ⁻¹' connectedComponentIn (range (ψ ∘ f))ᶜ q₀ = filledHull (range f) \ range f ∧
      ψ ⁻¹' closure (connectedComponentIn (range (ψ ∘ f))ᶜ q₀) = filledHull (range f) := by
  let Φ : OnePoint E ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let ψ : E → sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1 :=
    Φ ∘ ((↑) : E → OnePoint E)
  have hψ : IsOpenEmbedding ψ := Φ.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
  have hσ_eq : Φ '' (((↑) : E → OnePoint E) '' range f) = range (ψ ∘ f) := by
    rw [image_image, ← range_comp]
    rfl
  have hpinf : Φ ∞ ∉ range (ψ ∘ f) := by
    rintro ⟨x, hx⟩
    exact OnePoint.coe_ne_infty (f x) (Φ.injective hx)
  obtain ⟨b, hb⟩ := isBicollared_iff.1 <|
    (hf.isOpenEmbedding_comp hψ).isBicollared_of_finrank_eq (by simp) (hψ.injective.comp hinj)
  obtain ⟨q₀, hq₀, hdisj, hcompl⟩ :=
    exists_connectedComponentIn_compl_range_sphere_eq_union (by simp) hb.continuous
      hb.injective hpinf
  have hcl₀ := hb.closure_connectedComponentIn_compl_range_of_finrank_eq (by simp) hq₀
  have hK : IsCompact (range f) := isCompact_range hf.continuous
  obtain ⟨hcl_sub, hpre_U₀, hpre_cl⟩ := preimage_connectedComponentIn_onePoint_sphere hK Φ
    (hσ_eq.symm ▸ hpinf) (by simpa only [hσ_eq] using hdisj)
    (by simpa only [hσ_eq] using hcompl) (by simpa only [hσ_eq] using hcl₀)
  refine ⟨ψ, b, q₀, hψ, hb, hq₀, ?_, ?_, ?_⟩
  · simpa only [hσ_eq] using hcl_sub
  · simpa only [hσ_eq] using hpre_U₀
  · simpa only [hσ_eq] using hpre_cl

end OnePointBridge

/-! ### The generalized Schoenflies theorem for locally bicollared spheres in `E` -/

namespace IsLocallyBicollared

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {f : sphere (0 : E) 1 → E}

/-- **The generalized Schoenflies theorem in a finite-dimensional real normed space
(local-bicollar form).** For any injective locally bicollared map `f : sphere (0 : E) 1 → E`, the
filled hull `filledHull (range f)` is homeomorphic to `closedBall (0 : E) 1` by a homeomorphism
inverting `f` on `range f` and carrying `range f` onto `sphere (0 : E) 1`. -/
theorem exists_homeomorph_filledHull_range_closedBall (hf : IsLocallyBicollared f)
    (hinj : Injective f) :
    ∃ h : filledHull (range f) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : filledHull (range f)) x, (z : E) = f x → (h z : E) = x) ∧
      ∀ z : filledHull (range f), (h z : E) ∈ sphere (0 : E) 1 ↔ (z : E) ∈ range f := by
  obtain ⟨ψ, b, q₀, hψ, hb, hq₀, hcl_sub, -, hpre_cl⟩ :=
    exists_isOpenEmbedding_sphere_filledHull hf hinj
  obtain ⟨hS, hhS_inv, hhS_sph⟩ :=
    hb.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq (by simp) hq₀
  let eD : filledHull (range f) ≃ₜ closure (connectedComponentIn (range (ψ ∘ f))ᶜ q₀) :=
    (Homeomorph.setCongr hpre_cl.symm).trans (hψ.isEmbedding.homeomorphOfSubsetRange hcl_sub)
  have heD (z : filledHull (range f)) :
      (eD z : sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1) = ψ z := rfl
  refine ⟨eD.trans hS, fun z x hzx ↦ hhS_inv (eD z) x (by simp [heD, hzx]), fun z ↦ ?_⟩
  exact (hhS_sph (eD z)).trans <| by
    rw [heD, range_comp]
    exact hψ.injective.mem_set_image

/-- **Closed-ball extension form of the generalized Schoenflies theorem in `E`.** Every injective
locally bicollared sphere `f : sphere (0 : E) 1 → E` in a finite-dimensional real normed space `E`
extends to a closed embedding `g : closedBall (0 : E) 1 → E` with range `filledHull (range f)`
carrying `ball (0 : E) 1` onto `filledHull (range f) \ range f`. -/
theorem exists_isClosedEmbedding_closedBall_filledHull (hf : IsLocallyBicollared f)
    (hinj : Injective f) :
    ∃ g : closedBall (0 : E) 1 → E, IsClosedEmbedding g ∧
      (∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.2⟩ = f x) ∧
      range g = filledHull (range f) ∧
      (∀ z : closedBall (0 : E) 1,
        (z : E) ∈ ball (0 : E) 1 ↔ g z ∈ filledHull (range f) \ range f) := by
  have hclosed : IsClosed (filledHull (range f)) :=
    (isCompact_range hf.continuous).isClosed.isClosed_filledHull
  obtain ⟨h, hh_inv, hh_sph⟩ := hf.exists_homeomorph_filledHull_range_closedBall hinj
  let g : closedBall (0 : E) 1 → E := Subtype.val ∘ h.symm
  refine ⟨g, hclosed.isClosedEmbedding_subtypeVal.comp h.symm.isClosedEmbedding,
    fun x ↦ ?_, by rw [range_comp, h.symm.surjective.range_eq, image_univ, Subtype.range_coe],
    fun z ↦ ?_⟩
  · have hxmem : f x ∈ filledHull (range f) := subset_filledHull (mem_range_self x)
    have hxeq : h ⟨f x, hxmem⟩ = ⟨x, sphere_subset_closedBall x.2⟩ :=
      Subtype.ext (hh_inv ⟨f x, hxmem⟩ x rfl)
    simpa [g] using congrArg (Subtype.val ∘ h.symm) hxeq.symm
  · have hz_norm : (z : E) ∈ ball (0 : E) 1 ↔ (z : E) ∉ sphere (0 : E) 1 := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm]
      exact (mem_closedBall_zero_iff.1 z.2).lt_iff_ne
    have hiff := hh_sph (h.symm z)
    rw [h.apply_symm_apply] at hiff
    rw [hz_norm, hiff]
    exact ⟨fun hn ↦ ⟨(h.symm z).2, hn⟩, fun hz ↦ hz.2⟩

/-- **The bounded inside `filledHull (range f) \ range f` is path-connected.** -/
theorem isPathConnected_filledHull_sdiff_range (hf : IsLocallyBicollared f) (hinj : Injective f) :
    IsPathConnected (filledHull (range f) \ range f) := by
  obtain ⟨g, hg_emb, -, hg_range, hg_ball⟩ := hf.exists_isClosedEmbedding_closedBall_filledHull hinj
  let ι : ball (0 : E) 1 → closedBall (0 : E) 1 := Set.inclusion ball_subset_closedBall
  have : PathConnectedSpace (ball (0 : E) 1) :=
    isPathConnected_iff_pathConnectedSpace.1
      ((convex_ball (0 : E) 1).isPathConnected (nonempty_ball.2 one_pos))
  have hrange : range (g ∘ ι) = filledHull (range f) \ range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (hg_ball (ι x)).1 x.2
    · intro hy
      obtain ⟨z, rfl⟩ := hg_range ▸ hy.1
      exact ⟨⟨z, (hg_ball z).2 hy⟩, rfl⟩
  rw [← hrange]
  exact isPathConnected_range (hg_emb.continuous.comp (continuous_inclusion ball_subset_closedBall))

/-- **The bounded inside `filledHull (range f) \ range f` is connected.** -/
theorem isConnected_filledHull_sdiff_range (hf : IsLocallyBicollared f) (hinj : Injective f) :
    IsConnected (filledHull (range f) \ range f) :=
  (hf.isPathConnected_filledHull_sdiff_range hinj).isConnected

/-- **An embedded locally bicollared sphere encloses a nonempty bounded inside.** -/
theorem nonempty_filledHull_sdiff_range (hf : IsLocallyBicollared f) (hinj : Injective f) :
    (filledHull (range f) \ range f).Nonempty :=
  (hf.isPathConnected_filledHull_sdiff_range hinj).nonempty

/-- **The closure of the bounded inside is `filledHull (range f)`.** -/
theorem closure_filledHull_sdiff_range (hf : IsLocallyBicollared f) (hinj : Injective f) :
    closure (filledHull (range f) \ range f) = filledHull (range f) := by
  obtain ⟨ψ, -, q₀, hψ, -, -, -, hpre_U₀, hpre_cl⟩ :=
    exists_isOpenEmbedding_sphere_filledHull hf hinj
  rw [← hpre_U₀, ← hpre_cl,
    (hψ.isOpenMap.preimage_closure_eq_closure_preimage hψ.continuous _).symm]

/-- **The frontier of the bounded inside is `range f`.** -/
theorem frontier_filledHull_sdiff_range (hf : IsLocallyBicollared f) (hinj : Injective f) :
    frontier (filledHull (range f) \ range f) = range f := by
  have hK : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  rw [frontier, hf.closure_filledHull_sdiff_range hinj,
    (hK.isOpen_filledHull_sdiff).interior_eq]
  ext x
  simp only [mem_sdiff, not_and, not_not]
  exact ⟨fun ⟨hxH, himp⟩ ↦ himp hxH, fun hx ↦ ⟨subset_filledHull hx, fun _ ↦ hx⟩⟩

end IsLocallyBicollared

/-! ### The generalized Schoenflies theorem for locally flat spheres in `E` -/

namespace IsLocallyFlat

variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {f : sphere (0 : E) 1 → E}

/-- **The generalized Schoenflies theorem in a finite-dimensional real normed space.** Every
locally flat embedding `f : sphere (0 : E) 1 → E` encloses a filled hull homeomorphic to
`closedBall (0 : E) 1` by a homeomorphism inverting `f` on `range f` and sending `range f` onto
`sphere (0 : E) 1`. -/
theorem exists_homeomorph_filledHull_range_closedBall (hf : IsLocallyFlat H ℝ f) :
    ∃ h : filledHull (range f) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : filledHull (range f)) x, (z : E) = f x → (h z : E) = x) ∧
      ∀ z : filledHull (range f), (h z : E) ∈ sphere (0 : E) 1 ↔ (z : E) ∈ range f :=
  hf.isLocallyBicollared.exists_homeomorph_filledHull_range_closedBall hf.injective

/-- **Closed-ball extension form of the generalized Schoenflies theorem in `E`.** Every locally flat
embedding `f : sphere (0 : E) 1 → E` in a finite-dimensional real normed space `E` extends to a
closed embedding `g : closedBall (0 : E) 1 → E` with range `filledHull (range f)` carrying
`ball (0 : E) 1` onto `filledHull (range f) \ range f`. -/
theorem exists_isClosedEmbedding_closedBall_filledHull (hf : IsLocallyFlat H ℝ f) :
    ∃ g : closedBall (0 : E) 1 → E, IsClosedEmbedding g ∧
      (∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.2⟩ = f x) ∧
      range g = filledHull (range f) ∧
      (∀ z : closedBall (0 : E) 1,
        (z : E) ∈ ball (0 : E) 1 ↔ g z ∈ filledHull (range f) \ range f) :=
  hf.isLocallyBicollared.exists_isClosedEmbedding_closedBall_filledHull hf.injective

/-- **The bounded inside `filledHull (range f) \ range f` of a locally flat sphere in `E` is
path-connected.** -/
theorem isPathConnected_filledHull_sdiff_range (hf : IsLocallyFlat H ℝ f) :
    IsPathConnected (filledHull (range f) \ range f) :=
  hf.isLocallyBicollared.isPathConnected_filledHull_sdiff_range hf.injective

/-- **The bounded inside `filledHull (range f) \ range f` of a locally flat sphere in `E` is
connected.** -/
theorem isConnected_filledHull_sdiff_range (hf : IsLocallyFlat H ℝ f) :
    IsConnected (filledHull (range f) \ range f) :=
  hf.isLocallyBicollared.isConnected_filledHull_sdiff_range hf.injective

/-- **A locally flat sphere in `E` encloses a nonempty bounded inside.** -/
theorem nonempty_filledHull_sdiff_range (hf : IsLocallyFlat H ℝ f) :
    (filledHull (range f) \ range f).Nonempty :=
  hf.isLocallyBicollared.nonempty_filledHull_sdiff_range hf.injective

/-- **The closure of the bounded inside of a locally flat sphere in `E` is
`filledHull (range f)`.** -/
theorem closure_filledHull_sdiff_range (hf : IsLocallyFlat H ℝ f) :
    closure (filledHull (range f) \ range f) = filledHull (range f) :=
  hf.isLocallyBicollared.closure_filledHull_sdiff_range hf.injective

/-- **The frontier of the bounded inside of a locally flat sphere in `E` is `range f`.** -/
theorem frontier_filledHull_sdiff_range (hf : IsLocallyFlat H ℝ f) :
    frontier (filledHull (range f) \ range f) = range f :=
  hf.isLocallyBicollared.frontier_filledHull_sdiff_range hf.injective

end IsLocallyFlat

end TauCeti
