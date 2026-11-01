/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.TopologicalNerve
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
public import TauCeti.Topology.CategoryTheory.ActionGroupoid

/-!
# The fat classifying space of an action groupoid and its coarse map

Let a topological group `G` act on a space `X`, and let `Γ = G ⋉ X` be the action groupoid with
its label-source topology on arrows. Its fat classifying space `BΓ` is the fat realization of the
topological nerve (`TauCeti.fatClassifyingSpace`). Every arrow of `Γ` joins two points of the same
orbit, so sending a string of composable arrows to the orbit of its first vertex is an
augmentation of the nerve over the orbit space `X/G` (`TauCeti.ActionGroupoid.nerveAugmentation`).
It induces the coarse map `q : BΓ → X/G` (`TauCeti.ActionGroupoid.coarseMap`), which sends a point
`[F, t]` to the orbit of any vertex of `F` and is surjective.

The main result is the open restriction theorem. Let `U` be a `G`-invariant open subset of `X`,
that is, a saturated open set of objects of `Γ`, and let `Γ|U = G ⋉ U` be the full subgroupoid on
`U` (`CategoryTheory.ActionCategory.restrict`). A string of composable arrows of `Γ` lies in the
nerve of `Γ|U` exactly when its first vertex lies in `U`, and the restricted nerve is levelwise an
open subspace. Hence the induced map `B(Γ|U) → BΓ` is an open embedding
(`TauCeti.ActionGroupoid.isOpenEmbedding_fatClassifyingSpaceMap_restrict`) whose image is the
preimage under `q` of the image of `U` in `X/G`
(`TauCeti.ActionGroupoid.preimage_coarseMap_eq_range_fatClassifyingSpaceMap_restrict`): the part
of `BΓ` over a saturated open set is the fat classifying space of the restricted groupoid, with its
own quotient topology. No continuity of the action is needed, and labels acting trivially are
kept, so ineffective isotropy survives in `BΓ`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology MulAction
open CategoryTheory.ActionCategory

universe u

namespace TauCeti.ActionGroupoid

section Monoid

variable {M X : Type*} [Monoid M] [MulAction M X] (U : SubMulAction M X)

/-- A string of composable arrows of `M ⋉ X` comes from `M ⋉ U` exactly when its first vertex lies
in the invariant subset `U`. -/
theorem range_mapComposableArrows_obj_restrict (n : ℕ) :
    range ((restrict U).mapComposableArrows n).obj = {F | (F.obj 0).back ∈ U} := by
  ext F
  refine ⟨?_, fun hF => ?_⟩
  · rintro ⟨F', rfl⟩
    simp
  · -- Every vertex is a translate of the first one, so it lies in `U` as well.
    have hF' (i : Fin (n + 1)) : (F.obj i).back ∈ U := by
      convert U.smul_mem (F.map (homOfLE (Fin.zero_le i))).hom hF using 1
      exact (F.map _).map_val.symm
    exact ⟨restrictLift U F hF', restrictLift_comp_restrict U F hF'⟩

variable [TopologicalSpace M] [TopologicalSpace X]

/-- The inclusion of the action groupoid on an invariant subset is an embedding on total arrows.
In label-source coordinates it is the product of the identity of `M` and the inclusion of the
subset. -/
theorem isEmbedding_mapTotal_restrict : IsEmbedding (restrict U).toPrefunctor.mapTotal := by
  have : (restrict U).toPrefunctor.mapTotal =
      (arrowHomeomorph M X).symm ∘ Prod.map id Subtype.val ∘ arrowHomeomorph M U := by
    funext f
    apply (arrowHomeomorph M X).injective
    simp [Prefunctor.mapTotal, objEquiv]
  rw [this]
  exact (arrowHomeomorph M X).symm.isEmbedding.comp
    ((IsEmbedding.id.prodMap IsEmbedding.subtypeVal).comp (arrowHomeomorph M U).isEmbedding)

/-- Each vertex of a string of composable arrows of the action groupoid depends continuously on
the string. -/
@[fun_prop]
theorem continuous_back_obj {n : ℕ} (i : Fin (n + 1)) :
    Continuous fun F : ComposableArrows (ActionCategory M X) n => (F.obj i).back := by
  simpa [Function.comp_def] using (objectHomeomorph M X).continuous.comp
    ((continuous_source M X).comp (ComposableArrows.continuous_totalArrow i i le_rfl))

end Monoid

variable {G X : Type u} [Group G] [MulAction G X]

/-- All vertices of a string of composable arrows of the action groupoid lie in one orbit. -/
theorem mk_back_obj {n : ℕ} (F : ComposableArrows (ActionCategory G X) n) (i : Fin (n + 1)) :
    (Quotient.mk _ (F.obj i).back : orbitRel.Quotient G X) = Quotient.mk _ (F.obj 0).back :=
  Quotient.sound ⟨(F.map (homOfLE (Fin.zero_le i))).hom, (F.map (homOfLE _)).map_val⟩

variable [TopologicalSpace G] [TopologicalSpace X]

variable (G X)

/-- The augmentation of the topological nerve of the action groupoid over the orbit space,
sending a string of composable arrows to the orbit of its first vertex. -/
def nerveAugmentation : topologicalNerve (ActionCategory G X) ⟶
    (Functor.const _).obj (TopCat.of (orbitRel.Quotient G X)) where
  app _ := TopCat.ofHom ⟨fun F => Quotient.mk _ (F.obj 0).back,
    continuous_quotient_mk'.comp (continuous_back_obj 0)⟩
  naturality _ _ f := by
    ext F
    exact mk_back_obj F _

variable {G X} in
-- Not `simp`: `simp` rewrites the constant functor in the type of the left-hand side.
/-- The augmentation sends a string of composable arrows to the orbit of its first vertex. -/
theorem nerveAugmentation_app_apply (Δ : SimplexCategoryᵒᵖ)
    (F : ComposableArrows (ActionCategory G X) Δ.unop.len) :
    (nerveAugmentation G X).app Δ F = Quotient.mk _ (F.obj 0).back := (rfl)

/-- The augmentation of the nerve, restricted to its semi-simplicial part. -/
private def semiNerveAugmentation :
    SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve (ActionCategory G X) ⟶
      (Functor.const _).obj (TopCat.of (orbitRel.Quotient G X)) :=
  Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op (nerveAugmentation G X) ≫
    ((Functor.constCompWhiskeringLeftIso (C := TopCat.{u})
      (F := SemiSimplexCategory.toSimplexCategory.op)).app _).hom

/-- The coarse map `q : BΓ → X/G` from the fat classifying space of the action groupoid to the
orbit space, induced by the augmentation of the nerve. -/
def coarseMap : fatClassifyingSpace (ActionCategory G X) ⟶ TopCat.of (orbitRel.Quotient G X) :=
  fatRealization.augment (semiNerveAugmentation G X)

variable {G X}

-- Not `simp`: `simp` rewrites the nerve level in the type of the left-hand side.
/-- The coarse map sends `[F, t]` to the orbit of the first vertex of `F`. -/
theorem coarseMap_ι (n : SemiSimplexCategory)
    (F : ComposableArrows (ActionCategory G X) (SemiSimplexCategory.toSimplexCategory.obj n).len)
    (t : SemiSimplexCategory.toTop.obj n) :
    coarseMap G X (fatRealization.ι _ n (F, t)) = Quotient.mk _ (F.obj 0).back :=
  fatRealization.augment_ι
    (X := SemiSimplexCategory.toSimplexCategory.op ⋙ topologicalNerve (ActionCategory G X)) _ n F t

/-- The coarse map is surjective: the orbit of `x` is the image of the vertex at `x`. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap G X) := by
  rintro ⟨x⟩
  obtain ⟨t⟩ : Nonempty (SemiSimplexCategory.toTop.{u}.obj (.mk 0)) :=
    inferInstanceAs (Nonempty (SimplexCategory.toTop.{u}.obj _))
  exact ⟨fatRealization.ι _ (.mk 0) (ComposableArrows.mk₀ (objEquiv G X x), t),
    coarseMap_ι _ _ _⟩

variable (U : SubMulAction G X)

/-- The image of the nerve of `G ⋉ U` in each level of the nerve of `G ⋉ X` is the preimage, under
the augmentation, of the image of `U` in the orbit space. -/
theorem range_topologicalNerveMap_restrict (Δ : SimplexCategoryᵒᵖ) :
    range ((topologicalNerveMap (restrict U) (isEmbedding_mapTotal_restrict U).continuous).app Δ) =
      (nerveAugmentation G X).app Δ ⁻¹' (Quotient.mk _ '' (U : Set X)) := by
  rw [coe_topologicalNerveMap_app]
  refine (range_mapComposableArrows_obj_restrict U _).trans (Set.ext fun F => ?_)
  refine ⟨fun hF => ⟨_, hF, rfl⟩, ?_⟩
  rintro ⟨x, hx, hxF⟩
  obtain ⟨g, rfl⟩ := Quotient.exact hxF
  simpa using U.smul_mem g⁻¹ hx

/-- For an open invariant subset `U`, the nerve of `G ⋉ U` is levelwise an open subspace of the
nerve of `G ⋉ X`. -/
theorem isOpenEmbedding_topologicalNerveMap_restrict (hU : IsOpen (U : Set X))
    (Δ : SimplexCategoryᵒᵖ) :
    IsOpenEmbedding
      ((topologicalNerveMap (restrict U) (isEmbedding_mapTotal_restrict U).continuous).app Δ) := by
  rw [coe_topologicalNerveMap_app]
  refine ⟨ComposableArrows.isEmbedding_mapComposableArrows_obj (isEmbedding_mapTotal_restrict U),
    ?_⟩
  -- The level of the topological nerve is `ComposableArrows` with its composite topology.
  have : IsOpen (range ((restrict U).mapComposableArrows Δ.unop.len).obj) := by
    rw [range_mapComposableArrows_obj_restrict]
    exact hU.preimage (continuous_back_obj 0)
  exact this

/-- **Open restriction.** For a `G`-invariant open subset `U`, the map of fat classifying spaces
induced by the inclusion `G ⋉ U ⥤ G ⋉ X` is an open embedding. -/
theorem isOpenEmbedding_fatClassifyingSpaceMap_restrict (hU : IsOpen (U : Set X)) :
    IsOpenEmbedding (fatClassifyingSpaceMap (restrict U)
      (isEmbedding_mapTotal_restrict U).continuous) :=
  fatRealization.isOpenEmbedding_map_of_range_eq_preimage (semiNerveAugmentation G X)
    (V := Quotient.mk _ '' (U : Set X))
    (fun _ => isOpenEmbedding_topologicalNerveMap_restrict U hU _)
    (fun Δ => range_topologicalNerveMap_restrict U (SemiSimplexCategory.toSimplexCategory.op.obj Δ))

/-- **Open restriction.** The part of the fat classifying space of `G ⋉ X` lying over the image of
a `G`-invariant subset `U` is the image of the fat classifying space of `G ⋉ U`. -/
theorem preimage_coarseMap_eq_range_fatClassifyingSpaceMap_restrict :
    coarseMap G X ⁻¹' (Quotient.mk _ '' (U : Set X)) =
      range (fatClassifyingSpaceMap (restrict U) (isEmbedding_mapTotal_restrict U).continuous) :=
  fatRealization.preimage_augment_eq_range_map _ fun Δ =>
    range_topologicalNerveMap_restrict U (SemiSimplexCategory.toSimplexCategory.op.obj Δ)

end TauCeti.ActionGroupoid
