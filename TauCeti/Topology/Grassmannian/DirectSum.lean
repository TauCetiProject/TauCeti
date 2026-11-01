/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.Stabilization

/-!
# Direct-sum maps of finite Grassmannians

An injective linear map `f : 𝕜^N × 𝕜^M → 𝕜^P` sends an `a`-plane `V ⊆ 𝕜^N` and a `b`-plane
`W ⊆ 𝕜^M` to the `(a + b)`-plane `f(V × W) ⊆ 𝕜^P`. This is
`TauCeti.finiteGrassmannian.directSum`. On frames it lists the images of the vectors of a
frame of `V`, followed by the images of the vectors of a frame of `W`. Over a topological
field and for continuous `f`, the resulting map of Grassmannians is jointly continuous for the
frame-quotient topologies, because a product of the open frame-span quotient maps is again a
quotient map. The two summands are recovered as inverse images under `f ∘ inl` and `f ∘ inr`,
so the map is injective; over the real or complex numbers it is a closed embedding.

Direct-sum maps commute with the image maps of `TauCeti.Topology.Grassmannian.Map`, both in the
target and in each summand. The standard coordinate block sum
`TauCeti.finiteGrassmannian.blockSum : Gr_a(𝕜^N) × Gr_b(𝕜^M) → Gr_(a+b)(𝕜^(N+M))` uses the
concatenation of coordinate vectors, with the first summand in the coordinates `Fin.castAdd`
and the second in the coordinates `Fin.natAdd`. Appending a zero last coordinate to its second
summand is the same as appending it to the block sum. Other coordinate conventions for the sum
of two planes, such as interleaving coordinates, are direct-sum maps for other injective `f`.

The construction of Grassmannians as quotients of frame spaces follows
J. Milnor and J. Stasheff, *Characteristic Classes*, §5.
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] {a b N M P L N' M' : ℕ}

namespace finiteFullRankFrame

/-- The frame of a direct sum: the images under `f` of the vectors of the first frame,
followed by the images of the vectors of the second frame. -/
def directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜)) (hf : Function.Injective f)
    (v : finiteFullRankFrame 𝕜 a N) (w : finiteFullRankFrame 𝕜 b M) :
    finiteFullRankFrame 𝕜 (a + b) P :=
  ⟨Fin.append (fun i ↦ f (v.1 i, 0)) (fun j ↦ f (0, w.1 j)), by
    have h := (linearIndependent_equiv finSumFinEquiv.symm).2
      ((linearIndependent_inl_union_inr' v.2 w.2).map' f (LinearMap.ker_eq_bot.2 hf))
    convert h using 1
    ext k : 1
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp⟩

@[simp]
theorem coe_directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (v : finiteFullRankFrame 𝕜 a N) (w : finiteFullRankFrame 𝕜 b M) :
    (directSum f hf v w).1 = Fin.append (fun i ↦ f (v.1 i, 0)) (fun j ↦ f (0, w.1 j)) := (rfl)

/-- Combining two frames along a continuous linear map is jointly continuous. -/
theorem continuous_directSum [TopologicalSpace 𝕜]
    (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜)) (hf : Function.Injective f)
    (hfc : Continuous f) :
    Continuous fun p : finiteFullRankFrame 𝕜 a N × finiteFullRankFrame 𝕜 b M ↦
      directSum f hf p.1 p.2 := by
  refine Continuous.subtype_mk (continuous_pi fun k ↦ ?_) _
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
  · simp only [Fin.append_left]
    exact hfc.comp (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_const)
  · simp only [Fin.append_right]
    exact hfc.comp (continuous_const.prodMk
      ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)))

end finiteFullRankFrame

namespace finiteGrassmannian

/-- The direct sum of an `a`-plane `V` and a `b`-plane `W` along an injective linear map
`f` on the product of their ambient spaces: the `(a + b)`-plane `f(V × W)`. -/
noncomputable def directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (V : finiteGrassmannian 𝕜 a N) (W : finiteGrassmannian 𝕜 b M) :
    finiteGrassmannian 𝕜 (a + b) P :=
  ⟨(V.1.prod W.1).map f, by
    rw [← (Submodule.equivMapOfInjective f hf _).finrank_eq,
      (Submodule.prodEquiv V.1 W.1).finrank_eq, Module.finrank_prod, V.2, W.2]⟩

/-- The direct sum is the image of the product plane.
Use `mem_directSum` for membership simplification. -/
theorem coe_directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (V : finiteGrassmannian 𝕜 a N) (W : finiteGrassmannian 𝕜 b M) :
    (directSum f hf V W).1 = (V.1.prod W.1).map f := (rfl)

/-- A vector lies in a direct sum exactly when it is the image of a pair of vectors of the
two summands. -/
@[simp]
theorem mem_directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (V : finiteGrassmannian 𝕜 a N) (W : finiteGrassmannian 𝕜 b M)
    (x : Fin P → 𝕜) :
    x ∈ (directSum f hf V W).1 ↔ ∃ v ∈ V.1, ∃ w ∈ W.1, f (v, w) = x := by
  simp only [coe_directSum, Submodule.mem_map, Submodule.mem_prod, Prod.exists]
  constructor
  · rintro ⟨v, w, ⟨hv, hw⟩, rfl⟩
    exact ⟨v, hv, w, hw, rfl⟩
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨v, w, ⟨hv, hw⟩, rfl⟩

/-- Taking spans commutes with combining frames. -/
@[simp]
theorem frameSpan_directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (v : finiteFullRankFrame 𝕜 a N) (w : finiteFullRankFrame 𝕜 b M) :
    frameSpan (finiteFullRankFrame.directSum f hf v w) =
      directSum f hf (frameSpan v) (frameSpan w) := by
  apply Subtype.ext
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [coe_frameSpan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · simp only [finiteFullRankFrame.coe_directSum, Fin.append_left, SetLike.mem_coe,
        mem_directSum, coe_frameSpan]
      exact ⟨v.1 i, Submodule.subset_span (mem_range_self i), 0, Submodule.zero_mem _, rfl⟩
    · simp only [finiteFullRankFrame.coe_directSum, Fin.append_right, SetLike.mem_coe,
        mem_directSum, coe_frameSpan]
      exact ⟨0, Submodule.zero_mem _, w.1 j, Submodule.subset_span (mem_range_self j), rfl⟩
  · exact (frameSpan _).2.trans (directSum f hf (frameSpan v) (frameSpan w)).2.symm

/-- Over a topological field, the direct sum along a continuous linear map is jointly
continuous for the frame-quotient topologies. -/
theorem continuous_directSum [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
    (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜)) (hf : Function.Injective f)
    (hfc : Continuous f) :
    Continuous fun p : finiteGrassmannian 𝕜 a N × finiteGrassmannian 𝕜 b M ↦
      directSum f hf p.1 p.2 := by
  apply ((isOpenQuotientMap_frameSpan (𝕜 := 𝕜) (r := a) (N := N)).prodMap
    (isOpenQuotientMap_frameSpan (𝕜 := 𝕜) (r := b) (N := M))).isQuotientMap.continuous_iff.2
  exact (continuous_frameSpan.comp (finiteFullRankFrame.continuous_directSum f hf hfc)).congr
    fun p ↦ frameSpan_directSum f hf p.1 p.2

/-- Applying an injective linear map to a direct sum is the direct sum along the composite. -/
theorem map_directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (g : (Fin P → 𝕜) →ₗ[𝕜] (Fin L → 𝕜)) (hg : Function.Injective g)
    (V : finiteGrassmannian 𝕜 a N) (W : finiteGrassmannian 𝕜 b M) :
    map g hg (directSum f hf V W) = directSum (g ∘ₗ f) (hg.comp hf) V W :=
  Subtype.ext (by rw [coe_map, coe_directSum, coe_directSum, Submodule.map_comp])

/-- A direct sum of images of planes is the direct sum along the composite with the product
of the two linear maps. -/
theorem directSum_map_map (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (g : (Fin N' → 𝕜) →ₗ[𝕜] (Fin N → 𝕜)) (hg : Function.Injective g)
    (h : (Fin M' → 𝕜) →ₗ[𝕜] (Fin M → 𝕜)) (hh : Function.Injective h)
    (V : finiteGrassmannian 𝕜 a N') (W : finiteGrassmannian 𝕜 b M') :
    directSum f hf (map g hg V) (map h hh W) =
      directSum (f ∘ₗ g.prodMap h) (hf.comp (hg.prodMap hh)) V W := by
  apply Subtype.ext
  simp only [coe_directSum, coe_map, ← LinearMap.prodMap_map_prod, Submodule.map_comp]

/-- The first summand is the inverse image of a direct sum under `f ∘ inl`. -/
@[simp]
theorem comap_inl_directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (V : finiteGrassmannian 𝕜 a N) (W : finiteGrassmannian 𝕜 b M) :
    (directSum f hf V W).1.comap (f ∘ₗ LinearMap.inl 𝕜 _ _) = V.1 := by
  rw [Submodule.comap_comp, coe_directSum, Submodule.comap_map_eq_of_injective hf,
    Submodule.prod_comap_inl]

/-- The second summand is the inverse image of a direct sum under `f ∘ inr`. -/
@[simp]
theorem comap_inr_directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) (V : finiteGrassmannian 𝕜 a N) (W : finiteGrassmannian 𝕜 b M) :
    (directSum f hf V W).1.comap (f ∘ₗ LinearMap.inr 𝕜 _ _) = W.1 := by
  rw [Submodule.comap_comp, coe_directSum, Submodule.comap_map_eq_of_injective hf,
    Submodule.prod_comap_inr]

/-- A direct sum determines both of its summands. -/
theorem directSum_injective (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) :
    Function.Injective fun p : finiteGrassmannian 𝕜 a N × finiteGrassmannian 𝕜 b M ↦
      directSum f hf p.1 p.2 := by
  rintro ⟨V, W⟩ ⟨V', W'⟩ h
  have h' : directSum f hf V W = directSum f hf V' W' := h
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rw [← comap_inl_directSum f hf V W, h', comap_inl_directSum]
  · rw [← comap_inr_directSum f hf V W, h', comap_inr_directSum]

/-- The standard coordinate block sum of an `a`-plane in `𝕜^N` and a `b`-plane in `𝕜^M`:
the first plane occupies the coordinates `Fin.castAdd M` and the second the coordinates
`Fin.natAdd N` of `𝕜^(N + M)`. -/
noncomputable def blockSum (V : finiteGrassmannian 𝕜 a N) (W : finiteGrassmannian 𝕜 b M) :
    finiteGrassmannian 𝕜 (a + b) (N + M) :=
  directSum ((LinearEquiv.funCongrLeft 𝕜 𝕜 finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin N) (Fin M) 𝕜 𝕜)).symm.toLinearMap
    (LinearEquiv.injective _) V W

/-- Membership in a block sum: the initial coordinates lie in the first plane and the final
coordinates lie in the second plane. -/
@[simp]
theorem mem_blockSum (V : finiteGrassmannian 𝕜 a N) (W : finiteGrassmannian 𝕜 b M)
    (x : Fin (N + M) → 𝕜) :
    x ∈ (blockSum V W).1 ↔
      (fun i ↦ x (Fin.castAdd M i)) ∈ V.1 ∧ (fun j ↦ x (Fin.natAdd N j)) ∈ W.1 := by
  rw [blockSum, coe_directSum, Submodule.mem_map_equiv, LinearEquiv.symm_symm,
    Submodule.mem_prod]
  -- Splitting evaluates at `finSumFinEquiv (Sum.inl i) = Fin.castAdd M i` and
  -- `finSumFinEquiv (Sum.inr j) = Fin.natAdd N j`, both by definition.
  exact Iff.rfl

/-- Over a topological field, the coordinate block sum is jointly continuous. -/
@[fun_prop]
theorem continuous_blockSum [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] :
    Continuous fun p : finiteGrassmannian 𝕜 a N × finiteGrassmannian 𝕜 b M ↦
      blockSum p.1 p.2 := by
  refine continuous_directSum _ _ ((Fin.continuous_append N M).congr fun ⟨x, y⟩ ↦ ?_)
  ext k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
    simp [LinearEquiv.funCongrLeft_symm, LinearEquiv.funCongrLeft_apply]

/-- Appending a zero last coordinate to the second summand of a block sum is the same as
appending it to the block sum. -/
theorem blockSum_ambientStabilization (V : finiteGrassmannian 𝕜 a N)
    (W : finiteGrassmannian 𝕜 b M) :
    blockSum V (ambientStabilization W) = ambientStabilization (blockSum V W) := by
  apply Subtype.ext
  ext x
  simp only [mem_blockSum, mem_ambientStabilization, Fin.init, Fin.init_def, Fin.natAdd_castSucc,
    Fin.natAdd_last, Fin.castSucc_castAdd, and_assoc]

/-- A block sum determines both of its summands. -/
theorem blockSum_injective :
    Function.Injective fun p : finiteGrassmannian 𝕜 a N × finiteGrassmannian 𝕜 b M ↦
      blockSum p.1 p.2 :=
  directSum_injective _ _

end finiteGrassmannian

namespace finiteGrassmannian

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Over the real or complex numbers, every direct-sum map is a closed embedding. -/
theorem isClosedEmbedding_directSum (f : (Fin N → 𝕜) × (Fin M → 𝕜) →ₗ[𝕜] (Fin P → 𝕜))
    (hf : Function.Injective f) :
    Topology.IsClosedEmbedding fun p : finiteGrassmannian 𝕜 a N × finiteGrassmannian 𝕜 b M ↦
      directSum f hf p.1 p.2 :=
  (continuous_directSum f hf (LinearMap.continuous_of_finiteDimensional f)).isClosedEmbedding
    (directSum_injective f hf)

/-- Over the real or complex numbers, the coordinate block sum is a closed embedding. -/
theorem isClosedEmbedding_blockSum :
    Topology.IsClosedEmbedding fun p : finiteGrassmannian 𝕜 a N × finiteGrassmannian 𝕜 b M ↦
      blockSum p.1 p.2 :=
  isClosedEmbedding_directSum _ _

end finiteGrassmannian

end TauCeti
