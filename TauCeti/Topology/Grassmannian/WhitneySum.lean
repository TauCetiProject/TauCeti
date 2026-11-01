/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Fin.Interleave
public import TauCeti.Topology.Grassmannian.Tautological
public import TauCeti.Topology.VectorBundle.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Interleaved Whitney sums of finite Grassmannians

The sum of a `k`-plane in `𝕜ᵃ` and an `l`-plane in `𝕜ᵇ` is a `(k+l)`-plane in
`𝕜^(2 max(a,b))`. The first plane occupies the even coordinates and the second the odd
coordinates. This fixed convention gives a concrete finite-stage sum, rather than a sum
specified only up to a coordinate isomorphism. Its continuity is for the frame-quotient
topologies: concatenating frames lifts the sum, and the product of the two open frame-span
quotient maps is a quotient map. The induced linear equivalences on tautological fibres
assemble into an actual homeomorphism of the pulled-back bundle total spaces.

The construction uses Mathlib's product submodules, their dimension and linear-independence
API, and the existing open frame-span quotient of finite Grassmannians. The total-space
comparison uses `TauCeti.bundleHomeomorph`, whose inverse-continuity theorem applies to
finite-dimensional bundle models. These constructions include zero ranks and empty
Grassmannians.
-/

public section

open Set

namespace TauCeti

variable {𝕜 : Type*} [Field 𝕜] {k l a b : ℕ}

namespace finiteFullRankFrame

/-- Concatenate two frames in disjoint even/odd coordinate blocks. -/
noncomputable def whitneySum (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) : finiteFullRankFrame 𝕜 (k + l) (2 * max a b) :=
  ⟨fun i ↦ interleaveLinearMap 𝕜 𝕜 a b
      (Sum.elim (fun j ↦ (f.1 j, 0)) (fun j ↦ (0, g.1 j)) (finSumFinEquiv.symm i)),
    ((linearIndependent_inl_union_inr' f.2 g.2).map'
      (interleaveLinearMap 𝕜 𝕜 a b)
      (LinearMap.ker_eq_bot.2 interleaveLinearMap_injective)).comp _
        finSumFinEquiv.symm.injective⟩

@[simp] theorem whitneySum_inl (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) (i : Fin k) :
    (whitneySum f g).1 (Fin.castAdd l i) =
      interleaveLinearMap 𝕜 𝕜 a b (f.1 i, 0) := by simp [whitneySum]

@[simp] theorem whitneySum_inr (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) (i : Fin l) :
    (whitneySum f g).1 (Fin.natAdd k i) =
      interleaveLinearMap 𝕜 𝕜 a b (0, g.1 i) := by simp [whitneySum]

/-- Concatenation in the interleaved coordinates depends continuously on both frames. -/
@[fun_prop] theorem continuous_whitneySum [TopologicalSpace 𝕜] :
    Continuous (fun p : finiteFullRankFrame 𝕜 k a × finiteFullRankFrame 𝕜 l b ↦
      whitneySum p.1 p.2) := by
  refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  cases j with
  | inl j =>
    simp only [Equiv.symm_apply_apply, Sum.elim_inl]
    exact continuous_interleaveLinearMap.comp
      (((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_const)
  | inr j =>
    simp only [Equiv.symm_apply_apply, Sum.elim_inr]
    exact continuous_interleaveLinearMap.comp
      (continuous_const.prodMk
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)))

end finiteFullRankFrame

namespace finiteGrassmannian

/-- The Whitney sum of two planes, with the first in even positions and the second in odd
positions in the ambient space of dimension `2 * max a b`. -/
noncomputable def whitneySum (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) : finiteGrassmannian 𝕜 (k + l) (2 * max a b) :=
  ⟨(V.1.prod W.1).map (interleaveLinearMap 𝕜 𝕜 a b), by
    rw [← (Submodule.equivMapOfInjective _ interleaveLinearMap_injective
      (V.1.prod W.1)).finrank_eq, (V.1.prodEquiv W.1).finrank_eq,
      Module.finrank_prod, V.2, W.2]⟩

theorem coe_whitneySum (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) :
    (whitneySum V W).1 = (V.1.prod W.1).map (interleaveLinearMap 𝕜 𝕜 a b) := (rfl)

/-- A vector lies in the sum plane exactly when it is the interleaving of vectors in the two
input planes. -/
theorem mem_whitneySum_iff (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) (z : Fin (2 * max a b) → 𝕜) :
    z ∈ (whitneySum V W).1 ↔ ∃ v ∈ V.1, ∃ w ∈ W.1,
      interleaveLinearMap 𝕜 𝕜 a b (v, w) = z := by
  constructor
  · rintro ⟨⟨v, w⟩, ⟨hv, hw⟩, h⟩
    exact ⟨v, hv, w, hw, h⟩
  · rintro ⟨v, hv, w, hw, h⟩
    exact ⟨(v, w), ⟨hv, hw⟩, h⟩

/-- An interleaved vector lies in the sum plane exactly when both components lie in their
respective input planes. -/
@[simp] theorem interleave_mem_whitneySum_iff (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) (v : Fin a → 𝕜) (w : Fin b → 𝕜) :
    interleaveLinearMap 𝕜 𝕜 a b (v, w) ∈ (whitneySum V W).1 ↔ v ∈ V.1 ∧ w ∈ W.1 := by
  simp only [coe_whitneySum, Submodule.mem_map, interleaveLinearMap_injective.eq_iff,
    exists_eq_right, Submodule.mem_prod]

/-- Taking spans of concatenated frames gives the interleaved sum of their spans. -/
@[simp] theorem frameSpan_whitneySum (f : finiteFullRankFrame 𝕜 k a)
    (g : finiteFullRankFrame 𝕜 l b) :
    frameSpan (f.whitneySum g) = whitneySum (frameSpan f) (frameSpan g) := by
  apply Subtype.ext
  simp only [coe_frameSpan, coe_whitneySum, finiteFullRankFrame.whitneySum]
  have hr := EquivLike.range_comp
    (fun j ↦ interleaveLinearMap 𝕜 𝕜 a b
      (Sum.elim (fun i ↦ (f.1 i, 0)) (fun i ↦ (0, g.1 i)) j))
    (finSumFinEquiv.symm : Fin (k + l) ≃ Fin k ⊕ Fin l)
  simp only [Function.comp_def] at hr
  rw [hr, range_comp', Submodule.span_image, Sum.elim_range]
  congr 1
  simpa only [← range_comp, Function.comp_def, LinearMap.inl_apply, LinearMap.inr_apply] using
    (LinearMap.span_inl_union_inr (R := 𝕜) (s := range f.1) (t := range g.1))

/-- The finite-stage Whitney sum is continuous for the frame-quotient topologies. -/
@[fun_prop] theorem continuous_whitneySum [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] :
    Continuous (fun p : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦
      whitneySum p.1 p.2) := by
  apply ((isOpenQuotientMap_frameSpan.prodMap
    isOpenQuotientMap_frameSpan).isQuotientMap.continuous_iff).2
  exact (continuous_frameSpan.comp finiteFullRankFrame.continuous_whitneySum).congr
    fun p ↦ frameSpan_whitneySum p.1 p.2

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
      Tautological 𝕜 (k + l) (2 * max a b) (whitneySum V W) := by
  let f : (Tautological 𝕜 k a V × Tautological 𝕜 l b W) →ₗ[𝕜]
      Tautological 𝕜 (k + l) (2 * max a b) (whitneySum V W) :=
    { toFun := fun v ↦ ⟨WithLp.toLp 2 (interleaveLinearMap 𝕜 𝕜 a b
        (WithLp.ofLp v.1.1, WithLp.ofLp v.2.1)), by
        simpa only [Submodule.range_starProjection, mem_toEuclidean,
          WithLp.ofLp_toLp, interleave_mem_whitneySum_iff] using
          And.intro v.1.2 v.2.2⟩
      map_add' v w := Subtype.ext <| congrArg (WithLp.toLp 2)
        ((interleaveLinearMap 𝕜 𝕜 a b).map_add
          (WithLp.ofLp v.1.1, WithLp.ofLp v.2.1) (WithLp.ofLp w.1.1, WithLp.ofLp w.2.1))
      map_smul' r v := Subtype.ext <| congrArg (WithLp.toLp 2)
        ((interleaveLinearMap 𝕜 𝕜 a b).map_smul r (WithLp.ofLp v.1.1, WithLp.ofLp v.2.1)) }
  apply LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective f ?_)
  constructor
  · intro v w h
    have hh := congrArg (fun z ↦ WithLp.ofLp z.1) h
    have hi := interleaveLinearMap_injective hh
    exact Prod.ext (Subtype.ext (WithLp.ofLp_injective 2 (congrArg Prod.fst hi)))
      (Subtype.ext (WithLp.ofLp_injective 2 (congrArg Prod.snd hi)))
  · intro z
    have hz : WithLp.ofLp z.1 ∈ (whitneySum V W).1 := by
      simpa only [Submodule.range_starProjection, mem_toEuclidean] using z.2
    obtain ⟨v, hv, w, hw, h⟩ := (mem_whitneySum_iff V W _).1 hz
    refine ⟨(⟨WithLp.toLp 2 v, ?_⟩, ⟨WithLp.toLp 2 w, ?_⟩), ?_⟩
    · simpa only [Submodule.range_starProjection, mem_toEuclidean, WithLp.ofLp_toLp] using hv
    · simpa only [Submodule.range_starProjection, mem_toEuclidean, WithLp.ofLp_toLp] using hw
    · apply Subtype.ext
      exact WithLp.ofLp_injective 2 h

/-- The tautological comparison interleaves the underlying coordinate vectors. -/
@[simp] theorem whitneySumTautologicalEquiv_apply (V : finiteGrassmannian 𝕜 k a)
    (W : finiteGrassmannian 𝕜 l b) (v : Tautological 𝕜 k a V × Tautological 𝕜 l b W) :
    (whitneySumTautologicalEquiv V W v : EuclideanSpace 𝕜 (Fin (2 * max a b))) =
      WithLp.toLp 2 (interleaveLinearMap 𝕜 𝕜 a b (WithLp.ofLp v.1.1, WithLp.ofLp v.2.1)) :=
  (rfl)

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

-- Native pullbacks supply additive monoids and modules, but not the inherited group and
-- topological-module instances needed by the bundle inverse-continuity theorem. These local
-- instances install exactly those inherited structures on the three tautological pullbacks.
/-- The first tautological pullback inherits its fibrewise additive groups. -/
local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    AddCommGroup ((Prod.fst *ᵖ (Tautological 𝕜 k a)) q) :=
  inferInstanceAs (AddCommGroup (Tautological 𝕜 k a q.1))

/-- The second tautological pullback inherits its fibrewise additive groups. -/
local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    AddCommGroup ((Prod.snd *ᵖ (Tautological 𝕜 l b)) q) :=
  inferInstanceAs (AddCommGroup (Tautological 𝕜 l b q.2))

/-- The tautological pullback along the sum inherits its fibrewise additive groups. -/
local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    AddCommGroup (((fun q ↦ whitneySum q.1 q.2) *ᵖ
      (Tautological 𝕜 (k + l) (2 * max a b))) q) :=
  inferInstanceAs (AddCommGroup (Tautological 𝕜 (k + l) (2 * max a b) (whitneySum q.1 q.2)))

local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    IsTopologicalAddGroup ((Prod.fst *ᵖ (Tautological 𝕜 k a)) q) :=
  inferInstanceAs (IsTopologicalAddGroup (Tautological 𝕜 k a q.1))

local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    IsTopologicalAddGroup ((Prod.snd *ᵖ (Tautological 𝕜 l b)) q) :=
  inferInstanceAs (IsTopologicalAddGroup (Tautological 𝕜 l b q.2))

local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    IsTopologicalAddGroup (((fun q ↦ whitneySum q.1 q.2) *ᵖ
      (Tautological 𝕜 (k + l) (2 * max a b))) q) :=
  inferInstanceAs (IsTopologicalAddGroup
    (Tautological 𝕜 (k + l) (2 * max a b) (whitneySum q.1 q.2)))

local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    ContinuousSMul 𝕜 ((Prod.fst *ᵖ (Tautological 𝕜 k a)) q) :=
  inferInstanceAs (ContinuousSMul 𝕜 (Tautological 𝕜 k a q.1))

local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    ContinuousSMul 𝕜 ((Prod.snd *ᵖ (Tautological 𝕜 l b)) q) :=
  inferInstanceAs (ContinuousSMul 𝕜 (Tautological 𝕜 l b q.2))

local instance (q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b) :
    ContinuousSMul 𝕜 (((fun q ↦ whitneySum q.1 q.2) *ᵖ
      (Tautological 𝕜 (k + l) (2 * max a b))) q) :=
  inferInstanceAs (ContinuousSMul 𝕜
    (Tautological 𝕜 (k + l) (2 * max a b) (whitneySum q.1 q.2)))

/-- Pull back the first tautological fibre bundle to the product base. -/
local instance : FiberBundle (Fin k → 𝕜)
    ((Prod.fst : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b → _) *ᵖ
      (Tautological 𝕜 k a)) :=
  FiberBundle.pullback (⟨Prod.fst, continuous_fst⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b, finiteGrassmannian 𝕜 k a))

/-- Pull back the second tautological fibre bundle to the product base. -/
local instance : FiberBundle (Fin l → 𝕜)
    ((Prod.snd : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b → _) *ᵖ
      (Tautological 𝕜 l b)) :=
  FiberBundle.pullback (⟨Prod.snd, continuous_snd⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b, finiteGrassmannian 𝕜 l b))

/-- Pull back the tautological fibre bundle along the finite-stage sum. -/
local instance : FiberBundle (Fin (k + l) → 𝕜)
    ((fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦ whitneySum q.1 q.2)
      *ᵖ (Tautological 𝕜 (k + l) (2 * max a b))) :=
  FiberBundle.pullback (⟨fun q ↦ whitneySum q.1 q.2, continuous_whitneySum⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b,
      finiteGrassmannian 𝕜 (k + l) (2 * max a b)))

local instance : VectorBundle 𝕜 (Fin k → 𝕜)
    ((Prod.fst : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b → _) *ᵖ
      (Tautological 𝕜 k a)) :=
  VectorBundle.pullback 𝕜 (⟨Prod.fst, continuous_fst⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b, finiteGrassmannian 𝕜 k a))

local instance : VectorBundle 𝕜 (Fin l → 𝕜)
    ((Prod.snd : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b → _) *ᵖ
      (Tautological 𝕜 l b)) :=
  VectorBundle.pullback 𝕜 (⟨Prod.snd, continuous_snd⟩ :
    C(finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b, finiteGrassmannian 𝕜 l b))

local instance : VectorBundle 𝕜 (Fin (k + l) → 𝕜)
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
theorem whitneySumTautologicalHomeomorph_apply
    (p : TotalSpace ((Fin k → 𝕜) × (Fin l → 𝕜))
      ((Prod.fst *ᵖ (Tautological 𝕜 k a)) ×ᵇ (Prod.snd *ᵖ (Tautological 𝕜 l b)))) :
    whitneySumTautologicalHomeomorph p =
      TotalSpace.mk' (Fin (k + l) → 𝕜) p.proj
        (whitneySumTautologicalEquiv p.proj.1 p.proj.2 p.2) := by
  unfold whitneySumTautologicalHomeomorph
  apply bundleHomeomorph_apply

/-- The inverse total-space comparison uses the inverse linear equivalence on every fibre. -/
theorem whitneySumTautologicalHomeomorph_symm_apply
    (p : TotalSpace (Fin (k + l) → 𝕜)
      ((fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦ whitneySum q.1 q.2)
        *ᵖ (Tautological 𝕜 (k + l) (2 * max a b)))) :
    whitneySumTautologicalHomeomorph.symm p =
      TotalSpace.mk' ((Fin k → 𝕜) × (Fin l → 𝕜)) p.proj
        ((whitneySumTautologicalEquiv p.proj.1 p.proj.2).symm p.2) := by
  unfold whitneySumTautologicalHomeomorph
  apply bundleHomeomorph_symm_apply

/-- The tautological comparison covers the identity of the product base. -/
@[simp] theorem whitneySumTautologicalHomeomorph_proj
    (p : TotalSpace ((Fin k → 𝕜) × (Fin l → 𝕜))
      ((Prod.fst *ᵖ (Tautological 𝕜 k a)) ×ᵇ (Prod.snd *ᵖ (Tautological 𝕜 l b)))) :
    (whitneySumTautologicalHomeomorph p).proj = p.proj := by
  rw [whitneySumTautologicalHomeomorph_apply]

/-- The inverse tautological comparison also covers the identity of the product base. -/
@[simp] theorem whitneySumTautologicalHomeomorph_symm_proj
    (p : TotalSpace (Fin (k + l) → 𝕜)
      ((fun q : finiteGrassmannian 𝕜 k a × finiteGrassmannian 𝕜 l b ↦ whitneySum q.1 q.2)
        *ᵖ (Tautological 𝕜 (k + l) (2 * max a b)))) :
    (whitneySumTautologicalHomeomorph.symm p).proj = p.proj := by
  rw [whitneySumTautologicalHomeomorph_symm_apply]

end

end TauCeti.finiteGrassmannian
