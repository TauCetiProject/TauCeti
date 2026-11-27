/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GrassmannBundle.Map
public import TauCeti.Topology.VectorBundle.Riemannian.Hermitian
import TauCeti.Topology.FiberBundle.Separation
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# The Grassmann bundle over a subset of the base

Let `E → B` be a real vector bundle whose fibres are real inner product spaces, and let `W ⊆ B`.
The restriction of `E` to `W` is the pullback `E|_W = ContinuousMap.subtypeVal W *ᵖ E`, whose fibre
over `x ∈ W` is `E x` with its inner product. Its Grassmann bundle `G_k(E|_W)` includes into
`G_k(E)` by `(x, P) ↦ (x, P)` (`TauCeti.grassmannBundle.inclusion`), the map of Grassmann bundles
induced by the inclusion `W → B` covered by the identities of the fibres.

* The inclusion is continuous and injective, and its image is the part `π⁻¹(W)` of `G_k(E)` over
  `W` (`TauCeti.grassmannBundle.range_inclusion`).
* For a finite-rank bundle with continuous fibre norm over a Hausdorff base and an open `W`, it is
  an open embedding (`TauCeti.grassmannBundle.isOpenEmbedding_inclusion`), as is every continuous
  map of Grassmann bundles induced by an open embedding of the bases
  (`TauCeti.grassmannBundle.isOpenEmbedding_map`).
* For `W ⊆ B` and `W' ⊆ W`, the Grassmann bundle of `(E|_W)|_{W'}` is homeomorphic to that of
  `E|_{W'}` over the inclusions into `G_k(E)`
  (`TauCeti.grassmannBundle.restrictRestrictHomeomorph`).

This is the carrier of the restriction of a varifold on `B` to an open subset
(`TauCeti.grassmannBundle.restrictOpens`).

## References

* L. Simon, *Lectures on Geometric Measure Theory*, Proceedings of the Centre for Mathematical
  Analysis, Australian National University 3, 1983, §38.
-/

public section

noncomputable section

open Bundle Filter Set Topology

namespace TauCeti

namespace grassmannBundle

section Map

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  {k : ℕ} (W : Set B)

variable (F E k) in
/-- The inclusion `G_k(E|_W) → G_k(E)`, `(x, P) ↦ (x, P)`, of the Grassmann bundle of the
restriction `ContinuousMap.subtypeVal W *ᵖ E` of `E` to `W`: the map of Grassmann bundles induced
by the inclusion of `W` covered by the identities of the fibres. -/
def inclusion :
    grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k → grassmannBundle F E k :=
  map (ContinuousMap.subtypeVal W) fun x ↦ LinearIsometryEquiv.refl ℝ (E x)

/-- The inclusion keeps the plane and includes the base point. -/
@[simp]
theorem coe_inclusion_apply (p : grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k) :
    (inclusion F E k W p).val = ⟨(p.val.proj : B), p.val.snd⟩ := by
  refine (coe_map_apply (ContinuousMap.subtypeVal W) (fun x ↦ LinearIsometryEquiv.refl ℝ (E x))
    p).trans ?_
  -- The pullback fibre is the fibre of `E`, on which conjugating by the identity is trivial.
  exact TotalSpace.ext rfl (heq_of_eq (congrFun ((congrArg DFunLike.coe
    (LinearIsometryEquiv.conjStarAlgEquiv_refl (𝕜 := ℝ) (H := E p.val.proj))).trans
      StarAlgEquiv.coe_refl) p.val.snd))

/-- The inclusion covers the inclusion of `W`. -/
@[simp]
theorem proj_inclusion (p : grassmannBundle F (ContinuousMap.subtypeVal W *ᵖ E) k) :
    proj (inclusion F E k W p) = ((proj p : W) : B) :=
  proj_map (ContinuousMap.subtypeVal W) (fun x ↦ LinearIsometryEquiv.refl ℝ (E x)) p

/-- The inclusion `G_k(E|_W) → G_k(E)` is injective. -/
theorem inclusion_injective : Function.Injective (inclusion F E k W) :=
  map_injective _ _ Subtype.val_injective

/-- The image of the inclusion is the part `π⁻¹(W)` of `G_k(E)` over `W`. -/
theorem range_inclusion : range (inclusion F E k W) = proj ⁻¹' W :=
  (range_map (ContinuousMap.subtypeVal W) fun x ↦ LinearIsometryEquiv.refl ℝ (E x)).trans
    (congrArg (proj ⁻¹' ·) Subtype.range_coe)

/-- The preimage under the inclusion of the planes over `A ⊆ B` are the planes over `A ∩ W`. -/
theorem preimage_inclusion_preimage_proj (A : Set B) :
    inclusion F E k W ⁻¹' (proj ⁻¹' A) = proj ⁻¹' (Subtype.val ⁻¹' A) := by
  ext p
  simp only [mem_preimage, proj_inclusion]

/-- The image under the inclusion of the planes over `A ⊆ W` are the planes over the image of
`A` in `B`. -/
theorem image_inclusion_preimage_proj (A : Set W) :
    inclusion F E k W '' (proj ⁻¹' A) = proj ⁻¹' (Subtype.val '' A) := by
  refine Subset.antisymm (image_subset_iff.2 fun p hp ↦ ?_) fun q hq ↦ ?_
  · simp only [mem_preimage, proj_inclusion]
    exact mem_image_of_mem _ hp
  obtain ⟨x, hxA, hx⟩ := hq
  obtain ⟨p, rfl⟩ := (range_inclusion W).ge (show proj q ∈ W from hx ▸ x.property)
  refine ⟨p, ?_, rfl⟩
  rw [proj_inclusion] at hx
  rw [mem_preimage, ← Subtype.val_injective hx]
  exact hxA

end Map

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
  [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)] [∀ b, CompleteSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {k : ℕ} (W : Set B)

/-- **The inclusion of Grassmann bundles is continuous.** -/
theorem continuous_inclusion : Continuous (inclusion F E k W) :=
  -- The trivializations of a pullback are by definition the pullbacks of those of `E`
  -- (`FiberBundle.pullback`), which read a fibre vector through the trivialization of `E` at the
  -- image point (`Bundle.Trivialization.pullback_apply`), so the hypothesis holds by `rfl`.
  continuous_map (ContinuousMap.subtypeVal W).continuous fun _ ↦
    ContinuousLinearMap.continuousAt_inCoordinates_of_trivializationAt_apply
      continuous_subtypeVal.continuousAt (.of_forall fun _ _ ↦ rfl)

section Transitivity

variable {W}

variable (F E k) in
/-- **Transitivity of restriction for Grassmann bundles.** For `W ⊆ B` and `W' ⊆ W`, the Grassmann
bundle of the iterated restriction `(E|_W)|_{W'}` is homeomorphic to that of the single restriction
`E|_{W'}`, with `W'` read as a subset of `B`, compatibly with the inclusions into `G_k(E)`
(`TauCeti.grassmannBundle.inclusion_restrictRestrictHomeomorph`): it is induced by the
identification of `W'` with its image in `B`, covered by the identities of the fibres. -/
def restrictRestrictHomeomorph (W' : Set W) :
    grassmannBundle F (ContinuousMap.subtypeVal W' *ᵖ (ContinuousMap.subtypeVal W *ᵖ E)) k ≃ₜ
      grassmannBundle F (ContinuousMap.subtypeVal (Subtype.val '' W') *ᵖ E) k :=
  mapHomeomorphOfInverse k (fun x ↦ ⟨x.val.val, mem_image_of_mem _ x.property⟩)
    (fun x ↦ LinearIsometryEquiv.refl ℝ (E x.val.val))
    (fun y ↦ ⟨⟨y.val, image_val_subset y.property⟩, mem_of_mem_image_val y.property⟩)
    (fun y ↦ LinearIsometryEquiv.refl ℝ (E y.val)) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    ((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _)
    ((continuous_subtypeVal.subtype_mk _).subtype_mk _)
    -- All trivializations involved are pullbacks of those of `E`, so, as in
    -- `continuous_inclusion`, the identities of the fibres are the identity in coordinates by
    -- `rfl`.
    (fun _ ↦ ContinuousLinearMap.continuousAt_inCoordinates_of_trivializationAt_apply
      ((continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _).continuousAt
      (.of_forall fun _ _ ↦ rfl))
    (fun _ ↦ ContinuousLinearMap.continuousAt_inCoordinates_of_trivializationAt_apply
      ((continuous_subtypeVal.subtype_mk _).subtype_mk _).continuousAt
      (.of_forall fun _ _ ↦ rfl))

/-- The homeomorphism `G_k((E|_W)|_{W'}) ≃ₜ G_k(E|_{W'})` commutes with the inclusions into
`G_k(E)`. -/
@[simp]
theorem inclusion_restrictRestrictHomeomorph {W' : Set W}
    (p : grassmannBundle F (ContinuousMap.subtypeVal W' *ᵖ (ContinuousMap.subtypeVal W *ᵖ E)) k) :
    inclusion F E k (Subtype.val '' W') (restrictRestrictHomeomorph F E k W' p) =
      inclusion F E k W (inclusion F (ContinuousMap.subtypeVal W *ᵖ E) k W' p) := by
  refine (congrArg (inclusion F E k (Subtype.val '' W'))
    (congrFun (coe_mapHomeomorphOfInverse ..) p)).trans ?_
  -- Both sides are composites of two induced maps (`inclusion` is `map` by definition), covering
  -- inclusions of bases by identities of fibres. `map_comp` turns each composite into a single
  -- induced map, and `map_congr` compares the two on the total space of `E`, where both send
  -- `(x, v)` to `(x, v)`. The `by exact` defers that pointwise `rfl` until both `map_comp`s have
  -- fixed the two maps it compares.
  exact congrFun ((map_comp _ _ _ _).symm.trans ((map_congr (by exact fun _ _ ↦ rfl)).trans
    (map_comp (ContinuousMap.subtypeVal W')
      (fun x ↦ LinearIsometryEquiv.refl ℝ ((ContinuousMap.subtypeVal W *ᵖ E) x))
      (ContinuousMap.subtypeVal W) fun x ↦ LinearIsometryEquiv.refl ℝ (E x)))) p

/-- The homeomorphism `G_k((E|_W)|_{W'}) ≃ₜ G_k(E|_{W'})` covers the identification of `W'` with
its image in `B`. -/
@[simp]
theorem coe_proj_restrictRestrictHomeomorph {W' : Set W}
    (p : grassmannBundle F (ContinuousMap.subtypeVal W' *ᵖ (ContinuousMap.subtypeVal W *ᵖ E)) k) :
    ((proj (restrictRestrictHomeomorph F E k W' p) : Subtype.val '' W') : B) =
      ((proj p : W') : B) := by
  rw [← proj_inclusion, inclusion_restrictRestrictHomeomorph, proj_inclusion, proj_inclusion]

end Transitivity

variable [T2Space B] [FiniteDimensional ℝ F] [ContinuousFiberNorm F E]

/-- **The inclusion `G_k(E|_W) → G_k(E)` is an open embedding** for an open `W`, when `E` has
finite rank and continuous fibre norm and `B` is Hausdorff. -/
theorem isOpenEmbedding_inclusion (hW : IsOpen W) : IsOpenEmbedding (inclusion F E k W) :=
  isOpenEmbedding_map hW.isOpenEmbedding_subtypeVal (continuous_inclusion W)

end grassmannBundle

end TauCeti
