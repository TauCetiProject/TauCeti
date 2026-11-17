/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Fin.Interleave
public import TauCeti.Topology.Grassmannian.Tautological
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.Grassmannian.DirectSum
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Interleaved Whitney sums of finite Grassmannians

The sum of a `k`-plane in `𝕜ᵃ` and an `l`-plane in `𝕜ᵇ` is a `(k+l)`-plane in
`𝕜^(2 max(a,b))`. The first plane occupies the even coordinates and the second the odd
coordinates. This fixed convention gives a concrete finite-stage sum, rather than a sum
specified only up to a coordinate isomorphism. Its continuity is for the frame-quotient
topologies: concatenating frames lifts the sum, and the product of the two open frame-span
quotient maps is a quotient map. The induced linear equivalences on tautological fibres
assemble into an actual homeomorphism of the pulled-back bundle total spaces.

The construction specializes the existing `finiteGrassmannian.directSum` and
`finiteFullRankFrame.directSum` APIs to the interleaving linear map. The total-space
comparison uses `TauCeti.bundleHomeomorph`, whose inverse-continuity theorem applies to
finite-dimensional bundle models. These constructions include zero ranks and empty
Grassmannians.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1 (direct sums) and §1.2,
  proof of Theorem 1.16, pp. 29–30 (tautological pullback identification and disjoint
  odd/even coordinate embeddings). We use zero-based coordinates, with the first
  input in even positions.
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] {k l a b : ℕ}

namespace finiteFullRankFrame

/-- Concatenate two frames in disjoint even/odd coordinate blocks. -/
noncomputable def whitneySum (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) : finiteFullRankFrame 𝕜 (k + l) (2 * max a b) :=
  directSum (interleaveLinearMap 𝕜 𝕜 a b) interleaveLinearMap_injective f g

@[simp] theorem whitneySum_castAdd (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) (i : Fin k) :
    (whitneySum f g).1 (Fin.castAdd l i) =
      interleaveLinearMap 𝕜 𝕜 a b (f.1 i, 0) := by simp [whitneySum]

@[simp] theorem whitneySum_natAdd (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) (i : Fin l) :
    (whitneySum f g).1 (Fin.natAdd k i) =
      interleaveLinearMap 𝕜 𝕜 a b (0, g.1 i) := by simp [whitneySum]

/-- The concatenated frame ranges over the interleaved images of the two input frames. -/
theorem range_whitneySum (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) :
    range (whitneySum f g).1 = interleaveLinearMap 𝕜 𝕜 a b ''
      (range (fun i ↦ (f.1 i, 0)) ∪ range (fun j ↦ (0, g.1 j))) := by
  have h : (whitneySum f g).1 = interleaveLinearMap 𝕜 𝕜 a b ∘
      Sum.elim (fun i ↦ (f.1 i, 0)) (fun j ↦ (0, g.1 j)) ∘ finSumFinEquiv.symm := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp [whitneySum]
  rw [h, range_comp]
  exact congrArg _ ((finSumFinEquiv.symm.surjective.range_comp _).trans
    (Set.Sum.elim_range _ _))

/-- Concatenation in the interleaved coordinates depends continuously on both frames. -/
@[fun_prop] theorem continuous_whitneySum [TopologicalSpace 𝕜] :
    Continuous (fun p : finiteFullRankFrame 𝕜 k a × finiteFullRankFrame 𝕜 l b ↦
      whitneySum p.1 p.2) := by
  exact continuous_directSum _ interleaveLinearMap_injective continuous_interleaveLinearMap

end finiteFullRankFrame

namespace finiteGrassmannian

/-- The Whitney sum of two planes, with the first in even positions and the second in odd
positions in the ambient space of dimension `2 * max a b`. -/
noncomputable def whitneySum (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) : finiteGrassmannian 𝕜 (k + l) (2 * max a b) :=
  directSum (interleaveLinearMap 𝕜 𝕜 a b) interleaveLinearMap_injective V W

theorem coe_whitneySum (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) :
    (whitneySum V W).1 = (V.1.prod W.1).map (interleaveLinearMap 𝕜 𝕜 a b) :=
  coe_directSum _ interleaveLinearMap_injective V W

/-- A vector lies in the sum plane exactly when it is the interleaving of vectors in the two
input planes. -/
theorem mem_whitneySum_iff (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) (z : Fin (2 * max a b) → 𝕜) :
    z ∈ (whitneySum V W).1 ↔ ∃ v ∈ V.1, ∃ w ∈ W.1,
      interleaveLinearMap 𝕜 𝕜 a b (v, w) = z := by
  exact mem_directSum _ interleaveLinearMap_injective V W z

/-- An interleaved vector lies in the sum plane exactly when both components lie in their
respective input planes. -/
@[simp] theorem interleaveLinearMap_mem_whitneySum_iff (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) (v : Fin a → 𝕜) (w : Fin b → 𝕜) :
    interleaveLinearMap 𝕜 𝕜 a b (v, w) ∈ (whitneySum V W).1 ↔ v ∈ V.1 ∧ w ∈ W.1 := by
  simp only [coe_whitneySum, Submodule.mem_map, interleaveLinearMap_injective.eq_iff,
    exists_eq_right, Submodule.mem_prod]

/-- Taking spans of concatenated frames gives the interleaved sum of their spans. -/
@[simp] theorem frameSpan_whitneySum (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) :
    frameSpan (f.whitneySum g) = whitneySum (frameSpan f) (frameSpan g) := by
  exact frameSpan_directSum _ interleaveLinearMap_injective f g

/-- The finite-stage Whitney sum is continuous for the frame-quotient topologies. -/
@[fun_prop] theorem continuous_whitneySum [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] :
    Continuous (fun p : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦
      whitneySum p.1 p.2) := by
  exact continuous_directSum _ interleaveLinearMap_injective continuous_interleaveLinearMap

end finiteGrassmannian
end TauCeti

namespace TauCeti.finiteGrassmannian

open Bundle

variable {𝕜 : Type*} [RCLike 𝕜] {k l a b : ℕ}

/-- Interleaving gives the linear equivalence between the two tautological fibres and the
fibre of the sum plane. The coordinate identification with Euclidean space is retained. -/
noncomputable def whitneySumTautologicalEquiv (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) :
    (Tautological 𝕜 k a V × Tautological 𝕜 l b W) ≃L[𝕜]
      Tautological 𝕜 (k + l) (2 * max a b) (whitneySum V W) :=
  ((((((tautologicalEquiv 𝕜 k a V).prodCongr (tautologicalEquiv 𝕜 l b W)).trans
    (V.1.prodEquiv W.1).symm).trans
    (Submodule.equivMapOfInjective _ interleaveLinearMap_injective (V.1.prod W.1))).trans
    (LinearEquiv.ofEq _ _ (coe_whitneySum V W).symm)).trans
    (tautologicalEquiv 𝕜 (k + l) (2 * max a b) (whitneySum V W)).symm).toContinuousLinearEquiv

/-- The tautological comparison interleaves the underlying coordinate vectors. -/
@[simp] theorem whitneySumTautologicalEquiv_apply (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) (v : Tautological 𝕜 k a V × Tautological 𝕜 l b W) :
    (whitneySumTautologicalEquiv V W v : EuclideanSpace 𝕜 (Fin (2 * max a b))) =
      WithLp.toLp 2 (interleaveLinearMap 𝕜 𝕜 a b (WithLp.ofLp v.1.1, WithLp.ofLp v.2.1)) := by
  simp [whitneySumTautologicalEquiv, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]

/-- The inverse tautological comparison reads the first vector from the even coordinates. -/
@[simp] theorem whitneySumTautologicalEquiv_symm_fst (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b)
    (z : Tautological 𝕜 (k + l) (2 * max a b) (whitneySum V W)) (i : Fin a) :
    WithLp.ofLp ((whitneySumTautologicalEquiv V W).symm z).1.1 i =
      WithLp.ofLp z.1 (interleaveIndex a b (.inl i)) := by
  have h := congrArg (fun t : Tautological 𝕜 (k + l) (2 * max a b) (whitneySum V W) ↦
    WithLp.ofLp t.1 (interleaveIndex a b (.inl i)))
    ((whitneySumTautologicalEquiv V W).apply_symm_apply z)
  simpa only [whitneySumTautologicalEquiv_apply, WithLp.ofLp_toLp,
    interleaveLinearMap_apply_inl] using h

/-- The inverse tautological comparison reads the second vector from the odd coordinates. -/
@[simp] theorem whitneySumTautologicalEquiv_symm_snd (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b)
    (z : Tautological 𝕜 (k + l) (2 * max a b) (whitneySum V W)) (i : Fin b) :
    WithLp.ofLp ((whitneySumTautologicalEquiv V W).symm z).2.1 i =
      WithLp.ofLp z.1 (interleaveIndex a b (.inr i)) := by
  have h := congrArg (fun t : Tautological 𝕜 (k + l) (2 * max a b) (whitneySum V W) ↦
    WithLp.ofLp t.1 (interleaveIndex a b (.inr i)))
    ((whitneySumTautologicalEquiv V W).apply_symm_apply z)
  simpa only [whitneySumTautologicalEquiv_apply, WithLp.ofLp_toLp,
    interleaveLinearMap_apply_inr] using h

/-- The tautological comparison is continuous on the total space of the Whitney sum of the
two pulled-back bundles. -/
theorem continuous_whitneySumTautologicalEquiv :
    Continuous (fun p : TotalSpace ((Fin k → 𝕜) × (Fin l → 𝕜))
      ((Prod.fst *ᵖ (Tautological 𝕜 k a)) ×ᵇ (Prod.snd *ᵖ (Tautological 𝕜 l b))) ↦
      TotalSpace.mk' (Fin (k + l) → 𝕜)
        (E := (fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦
          whitneySum q.1 q.2) *ᵖ (Tautological 𝕜 (k + l) (2 * max a b)))
        p.proj (whitneySumTautologicalEquiv p.proj.1 p.proj.2 p.2)) := by
  let E : (finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) → Type _ :=
    Prod.fst *ᵖ (Tautological 𝕜 k a)
  let F : (finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) → Type _ :=
    Prod.snd *ᵖ (Tautological 𝕜 l b)
  have hd := (FiberBundle.Prod.isInducing_diag (Fin k → 𝕜) E (Fin l → 𝕜) F).continuous
  have h₁ := (isEmbedding_totalSpace_range (Fin k → 𝕜)
    (fun V : finiteGrassmannian 𝕜 k a ↦ V.toEuclidean.starProjection)).continuous.comp
      ((Pullback.continuous_lift (Fin k → 𝕜) (Tautological 𝕜 k a) Prod.fst).comp
        (continuous_fst.comp hd))
  have h₂ := (isEmbedding_totalSpace_range (Fin l → 𝕜)
    (fun W : finiteGrassmannian 𝕜 l b ↦ W.toEuclidean.starProjection)).continuous.comp
      ((Pullback.continuous_lift (Fin l → 𝕜) (Tautological 𝕜 l b) Prod.snd).comp
        (continuous_snd.comp hd))
  have hb := (Pullback.continuous_proj (Fin k → 𝕜) (Tautological 𝕜 k a) Prod.fst).comp
    (continuous_fst.comp hd)
  apply (inducing_pullbackTotalSpaceEmbedding _ _ _).continuous_iff.2
  refine hb.prodMk ?_
  apply (isEmbedding_totalSpace_range _ _).isInducing.continuous_iff.2
  refine (continuous_whitneySum.comp hb).prodMk ?_
  have hc : Continuous (fun p : TotalSpace ((Fin k → 𝕜) × (Fin l → 𝕜)) (E ×ᵇ F) ↦
      (WithLp.toLp 2 (interleaveLinearMap 𝕜 𝕜 a b
        (WithLp.ofLp p.2.1.1, WithLp.ofLp p.2.2.1)) : EuclideanSpace 𝕜 (Fin (2 * max a b)))) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_interleaveLinearMap.comp
      (((PiLp.continuous_ofLp 2 _).comp (continuous_snd.comp h₁)).prodMk
        ((PiLp.continuous_ofLp 2 _).comp (continuous_snd.comp h₂))))
  exact hc.congr fun p ↦ (whitneySumTautologicalEquiv_apply p.proj.1 p.proj.2 p.2).symm

noncomputable section

/-- Pull back the first tautological fibre bundle to the product base. -/
instance : FiberBundle (Fin k → 𝕜)
    ((Prod.fst : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b → _) *ᵖ
      (Tautological 𝕜 k a)) :=
  FiberBundle.pullback (⟨Prod.fst, continuous_fst⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b, finiteGrassmannian 𝕜 k a))

/-- Pull back the second tautological fibre bundle to the product base. -/
instance : FiberBundle (Fin l → 𝕜)
    ((Prod.snd : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b → _) *ᵖ
      (Tautological 𝕜 l b)) :=
  FiberBundle.pullback (⟨Prod.snd, continuous_snd⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b, finiteGrassmannian 𝕜 l b))

/-- Pull back the tautological fibre bundle along the finite-stage sum. -/
instance : FiberBundle (Fin (k + l) → 𝕜)
    ((fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦ whitneySum q.1 q.2)
      *ᵖ (Tautological 𝕜 (k + l) (2 * max a b))) :=
  FiberBundle.pullback (⟨fun q ↦ whitneySum q.1 q.2, continuous_whitneySum⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b,
      finiteGrassmannian 𝕜 (k + l) (2 * max a b)))

/-- The first tautological pullback is a vector bundle on the product base. -/
instance : VectorBundle 𝕜 (Fin k → 𝕜)
    ((Prod.fst : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b → _) *ᵖ
      (Tautological 𝕜 k a)) :=
  VectorBundle.pullback 𝕜 (⟨Prod.fst, continuous_fst⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b, finiteGrassmannian 𝕜 k a))

/-- The second tautological pullback is a vector bundle on the product base. -/
instance : VectorBundle 𝕜 (Fin l → 𝕜)
    ((Prod.snd : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b → _) *ᵖ
      (Tautological 𝕜 l b)) :=
  VectorBundle.pullback 𝕜 (⟨Prod.snd, continuous_snd⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b, finiteGrassmannian 𝕜 l b))

/-- The tautological pullback along the sum is a vector bundle. -/
instance : VectorBundle 𝕜 (Fin (k + l) → 𝕜)
    ((fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦ whitneySum q.1 q.2)
      *ᵖ (Tautological 𝕜 (k + l) (2 * max a b))) :=
  VectorBundle.pullback 𝕜 (⟨fun q ↦ whitneySum q.1 q.2, continuous_whitneySum⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b,
      finiteGrassmannian 𝕜 (k + l) (2 * max a b)))

/-- The actual tautological-bundle isomorphism for the interleaved finite-stage sum:
`pr₁*γₖ ⊕ pr₂*γₗ ≃ μ*γₖ₊ₗ`, over the identity on the product of Grassmannians. -/
noncomputable def whitneySumTautologicalHomeomorph :
    TotalSpace ((Fin k → 𝕜) × (Fin l → 𝕜))
      ((Prod.fst *ᵖ (Tautological 𝕜 k a)) ×ᵇ (Prod.snd *ᵖ (Tautological 𝕜 l b))) ≃ₜ
    TotalSpace (Fin (k + l) → 𝕜)
      ((fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦ whitneySum q.1 q.2)
        *ᵖ (Tautological 𝕜 (k + l) (2 * max a b))) := by
  exact bundleHomeomorph
    (E₁ := (Prod.fst *ᵖ (Tautological 𝕜 k a)) ×ᵇ (Prod.snd *ᵖ (Tautological 𝕜 l b)))
    (E₂ := (fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦ whitneySum q.1 q.2)
      *ᵖ (Tautological 𝕜 (k + l) (2 * max a b)))
    (fun q ↦ whitneySumTautologicalEquiv q.1 q.2) continuous_whitneySumTautologicalEquiv

/-- The total-space comparison is the specified linear equivalence on every fibre. -/
@[simp] theorem whitneySumTautologicalHomeomorph_apply
    (p : TotalSpace ((Fin k → 𝕜) × (Fin l → 𝕜))
      ((Prod.fst *ᵖ (Tautological 𝕜 k a)) ×ᵇ (Prod.snd *ᵖ (Tautological 𝕜 l b)))) :
    whitneySumTautologicalHomeomorph p =
      TotalSpace.mk' (Fin (k + l) → 𝕜) p.proj
        (whitneySumTautologicalEquiv p.proj.1 p.proj.2 p.2) := by
  unfold whitneySumTautologicalHomeomorph
  apply bundleHomeomorph_apply

/-- The inverse total-space comparison uses the inverse linear equivalence on every fibre. -/
@[simp] theorem whitneySumTautologicalHomeomorph_symm_apply
    (p : TotalSpace (Fin (k + l) → 𝕜)
      ((fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦ whitneySum q.1 q.2)
        *ᵖ (Tautological 𝕜 (k + l) (2 * max a b)))) :
    whitneySumTautologicalHomeomorph.symm p =
      TotalSpace.mk' ((Fin k → 𝕜) × (Fin l → 𝕜)) p.proj
        ((whitneySumTautologicalEquiv p.proj.1 p.proj.2).symm p.2) := by
  unfold whitneySumTautologicalHomeomorph
  apply bundleHomeomorph_symm_apply

end

end TauCeti.finiteGrassmannian
