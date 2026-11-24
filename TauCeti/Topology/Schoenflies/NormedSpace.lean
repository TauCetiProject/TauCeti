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
`U₀ ∪ range σ` avoids `p∞`. Pulling `U₀` and its closure back to `E` via
`TauCeti.Topology.Compactification.OnePoint.FilledHull` identifies them with the bounded inside
`filledHull (range f) \ range f` and with the filled hull `filledHull (range f)`, in every finite
dimension `d ≥ 0` (including `d = 1`, where `(range f)ᶜ` in `E` has two unbounded rays glued at
`p∞` into `U∞`, and `d = 0`, where `S(E) = ∅` and `filledHull ∅ = {0}`).

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
  have hσ_eq : ψ '' range f = range (ψ ∘ f) := (range_comp ψ f).symm
  have hpinf : Φ ∞ ∉ range (ψ ∘ f) := by
    rintro ⟨x, hx⟩
    exact OnePoint.coe_ne_infty (f x) (Φ.injective hx)
  obtain ⟨b, hb⟩ := isBicollared_iff.1 <|
    (hf.isOpenEmbedding_comp hψ).isBicollared_of_finrank_eq (by simp) (hψ.injective.comp hinj)
  obtain ⟨q₀, hq₀, hdisj, hcompl⟩ :=
    exists_connectedComponentIn_compl_range_sphere_eq_union (by simp) hb.continuous
      hb.injective hpinf
  have hcl₀ := hb.closure_connectedComponentIn_compl_range (by simp) hq₀
  have hK : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  have hdisj' := hσ_eq ▸ hdisj
  have hcompl' := hσ_eq ▸ hcompl
  have hcl₀' := hσ_eq ▸ hcl₀
  refine ⟨ψ, b, q₀, hψ, hb, hq₀, ?_, ?_, ?_⟩
  · simpa only [ψ, range_comp] using
      closure_connectedComponentIn_subset_range_onePoint Φ hdisj' hcl₀'.subset
  · simpa only [ψ, range_comp] using
      preimage_connectedComponentIn_onePoint hK Φ hdisj' hcompl' hcl₀'.subset
  · simpa only [ψ, range_comp] using
      preimage_closure_connectedComponentIn_onePoint hK Φ hdisj' hcompl' hcl₀'

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
    hb.exists_homeomorph_closure_connectedComponentIn_compl_range (by simp) hq₀
  let eD : filledHull (range f) ≃ₜ closure (connectedComponentIn (range (ψ ∘ f))ᶜ q₀) :=
    (Homeomorph.setCongr hpre_cl.symm).trans (hψ.isEmbedding.homeomorphOfSubsetRange hcl_sub)
  have heD (z : filledHull (range f)) :
      (eD z : sphere (0 : EuclideanSpace ℝ (Fin (finrank ℝ E + 1))) 1) = ψ z := by
    simp [eD, Homeomorph.setCongr]
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
      (∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.property⟩ = f x) ∧
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
    have hxeq : h ⟨f x, hxmem⟩ = ⟨x, sphere_subset_closedBall x.property⟩ :=
      Subtype.ext (hh_inv ⟨f x, hxmem⟩ x rfl)
    simpa [g] using congrArg (Subtype.val ∘ h.symm) hxeq.symm
  · have hz_norm : (z : E) ∈ ball (0 : E) 1 ↔ (z : E) ∉ sphere (0 : E) 1 := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm]
      exact (mem_closedBall_zero_iff.1 z.property).lt_iff_ne
    have hiff := hh_sph (h.symm z)
    rw [h.apply_symm_apply] at hiff
    rw [hz_norm, hiff]
    exact ⟨fun hn ↦ ⟨(h.symm z).property, hn⟩, fun hz ↦ hz.2⟩

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
      exact (hg_ball (ι x)).1 x.property
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
      (∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.property⟩ = f x) ∧
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
