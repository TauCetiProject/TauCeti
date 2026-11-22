/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Pullbacks of fibre bundles

Five facts about Mathlib's pullback bundle `f *ᵖ E`, whose fibre over `x` is the fibre of `E` over
`f x`, needed to pull back bundles with extra structure on their fibres or on their atlas.

* The fibres of `f *ᵖ E` carry the scalar operations and monoid actions on the fibres of `E`
  (`Bundle.Pullback.instSMul`, `Bundle.Pullback.instMulAction`), as Mathlib already does for
  module structures. This is what
  makes the pullback of a principal bundle again carry a right action on its fibres.
* The fibrewise inverse of a pulled-back trivialization `e.pullback f` agrees with that of `e` at
  the image point (`Bundle.Trivialization.pullback_symm_apply`), and the coordinate change between
  the pullbacks `e.pullback f` and `e'.pullback f` of two trivializations, over a point `x` with
  `f x` in the base set of `e`, is the coordinate change between `e` and `e'` over `f x`
  (`Bundle.Trivialization.coordChange_pullback`). This transfers regularity of the coordinate
  changes of `E` to those of `f *ᵖ E`.
* The canonical lift `Bundle.Pullback.lift f : TotalSpace F (f *ᵖ E) → TotalSpace F E` has range
  `(π F E) ⁻¹' Set.range f` and inherits injectivity, inducingness, and topological (or open /
  closed) embedding properties from `f` (`Bundle.Pullback.isEmbedding_lift`). A point of the
  total space of `f *ᵖ E` is determined by its projection and its lift
  (`Bundle.Pullback.totalSpace_ext`).
* A map into the total space of `f *ᵖ E` is continuous exactly when its projection and its lift to
  the total space of `E` are (`Bundle.Pullback.continuous_iff`).
* The canonical lift is the base change of `f` along the projection of `E`, so it inherits
  openness from `f` (`Bundle.Pullback.isOpenMap_lift`). If `f` is the quotient map of a covering
  action of a group `G` and `G` acts on the total space of `f *ᵖ E` over its action on the base,
  fixing the lifts of points, then the lift is the quotient map of this action
  (`Bundle.Pullback.isQuotientCoveringMap_lift`). For the orientation double cover this makes the
  total space of the bundle pulled back to the cover a double cover of the original total space.
-/

public section

open Bundle Set Topology

variable {B B' : Type*}

/-- The fibres of a pullback bundle inherit scalar multiplication from the original fibres. -/
instance Bundle.Pullback.instSMul {M : Type*} {E : B → Type*}
    [i : ∀ b, SMul M (E b)] (f : B' → B) (x : B') : SMul M ((f *ᵖ E) x) :=
  i (f x)

/-- The fibres of a pullback bundle `f *ᵖ E` carry the actions on the fibres of `E`: the fibre over
`x` is the fibre of `E` over `f x`. -/
instance Bundle.Pullback.instMulAction {M : Type*} [Monoid M] {E : B → Type*}
    [i : ∀ b, MulAction M (E b)] (f : B' → B) (x : B') : MulAction M ((f *ᵖ E) x) :=
  i (f x)

/-- Scalar multiplication on a fibre of a pullback bundle `f *ᵖ E` agrees with the scalar
multiplication on the corresponding fibre of `E`. -/
theorem Bundle.Pullback.smul_eq {M : Type*} {E : B → Type*} [∀ b, SMul M (E b)] (f : B' → B)
    (x : B') (m : M) (v : (f *ᵖ E) x) :
    m • v = @HSMul.hSMul M (E (f x)) (E (f x)) _ m v :=
  rfl

section Lift

variable {F : Type*} {E : B → Type*}

/-- The canonical lift from the pullback total space `f *ᵖ E` to `E` has image equal to the
part of `E` lying over the range of `f`. -/
@[simp]
theorem Bundle.Pullback.range_lift (f : B' → B) :
    range (Pullback.lift (F := F) (E := E) f) = π F E ⁻¹' range f := by
  ext w
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.proj, rfl⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · exact cast (congrArg E hx.symm) w.snd
    · cases w with | mk b v => cases hx; rfl

/-- If `f` is injective, the canonical lift `Pullback.lift f` on total spaces is injective. -/
theorem Bundle.Pullback.lift_injective {f : B' → B} (hf : Function.Injective f) :
    Function.Injective (Pullback.lift (F := F) (E := E) f) := by
  rintro ⟨x₁, v₁⟩ ⟨x₂, v₂⟩ h
  obtain rfl : x₁ = x₂ := hf (congrArg (π F E) h)
  exact TotalSpace.ext rfl (TotalSpace.ext_iff.mp h).2

/-- Two points of the total space of a pullback bundle are equal when they have the same base
point and the same lift to the original total space. -/
theorem Bundle.Pullback.totalSpace_ext {f : B' → B} {z z' : TotalSpace F (f *ᵖ E)}
    (h : z.proj = z'.proj) (h' : Pullback.lift f z = Pullback.lift f z') : z = z' := by
  obtain ⟨y, a⟩ := z
  obtain ⟨y', a'⟩ := z'
  obtain rfl : y = y' := h
  exact congrArg (TotalSpace.mk y) (TotalSpace.mk_injective (F := F) (E := E) (f y) h')

variable [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)]

omit [TopologicalSpace B] in
/-- A map into the total space of a pullback bundle `f *ᵖ E` is continuous exactly when its
projection to the new base and its lift to the total space of `E` are continuous. -/
theorem Bundle.Pullback.continuous_iff {Z : Type*} [TopologicalSpace Z] {f : B' → B}
    {g : Z → TotalSpace F (f *ᵖ E)} :
    Continuous g ↔ Continuous (fun z ↦ (g z).proj) ∧ Continuous (fun z ↦ Pullback.lift f (g z)) :=
  (inducing_pullbackTotalSpaceEmbedding F E f).continuous_iff.trans continuous_prodMk

omit [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)] in
/-- The canonical lift sends the points of the total space of `f *ᵖ E` over `U` whose lift lies in
`V` onto the points of `V` over `f '' U`. -/
theorem Bundle.Pullback.image_lift_inter (f : B' → B) (U : Set B') (V : Set (TotalSpace F E)) :
    Pullback.lift f '' (π F (f *ᵖ E) ⁻¹' U ∩ Pullback.lift f ⁻¹' V) =
      V ∩ π F E ⁻¹' (f '' U) := by
  ext w
  refine ⟨?_, ?_⟩
  · rintro ⟨z, ⟨hzU, hzV⟩, rfl⟩
    exact ⟨hzV, z.proj, hzU, rfl⟩
  · obtain ⟨b, v⟩ := w
    rintro ⟨hwV, x, hxU, rfl⟩
    exact ⟨⟨x, v⟩, ⟨hxU, hwV⟩, rfl⟩

/-- If `f` is an open map and the projection `π F E` is continuous, the canonical lift
`Pullback.lift f` is an open map: it is the base change of `f` along the projection. -/
theorem Bundle.Pullback.isOpenMap_lift {f : B' → B} (hf : IsOpenMap f) (hπ : Continuous (π F E)) :
    IsOpenMap (Pullback.lift (F := F) (E := E) f) := by
  refine fun O hO ↦ isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨z, hz, rfl⟩
  -- A basic neighbourhood of `z` inside `O`: the points over `U` whose lift lies in `V`.
  have hO' := hO.mem_nhds hz
  rw [(inducing_pullbackTotalSpaceEmbedding F E f).nhds_eq_comap, nhds_prod_eq] at hO'
  obtain ⟨t, ht, htO⟩ := hO'
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.1 ht
  obtain ⟨U', hU'U, hU', hzU'⟩ := mem_nhds_iff.1 hU
  obtain ⟨V', hV'V, hV', hzV'⟩ := mem_nhds_iff.1 hV
  refine Filter.mem_of_superset ((hV'.inter ((hf U' hU').preimage hπ)).mem_nhds
    ⟨hzV', z.proj, hzU', rfl⟩) ?_
  rw [← image_lift_inter]
  exact image_mono fun y hy ↦ htO (hUV ⟨hU'U hy.1, hV'V hy.2⟩)

/-- **The pullback of a quotient covering map.** Let `f : B' → B` present `B` as the quotient of
`B'` by a group `G`, in the sense of Mathlib's `IsQuotientCoveringMap`, and let `G` act on the
total space of the pullback `f *ᵖ E` over its action on `B'`, fixing the lift of each point to the
total space of `E`. Then the canonical lift `Pullback.lift f` presents the total space of `E` as the
quotient of the total space of `f *ᵖ E` by `G`. -/
theorem Bundle.Pullback.isQuotientCoveringMap_lift {G : Type*} [Group G] [MulAction G B']
    {f : B' → B} [MulAction G (TotalSpace F (f *ᵖ E))] (hf : IsQuotientCoveringMap f G)
    (hπ : Continuous (π F E))
    (hproj : ∀ (g : G) (z : TotalSpace F (f *ᵖ E)), (g • z).proj = g • z.proj)
    (hlift : ∀ (g : G) (z : TotalSpace F (f *ᵖ E)), Pullback.lift f (g • z) = Pullback.lift f z) :
    IsQuotientCoveringMap (Pullback.lift (F := F) (E := E) f) G := by
  have : ContinuousConstSMul G B' := hf.toContinuousConstSMul
  refine
    { toIsQuotientMap := IsOpenQuotientMap.isQuotientMap
        ⟨fun w ↦ ?_, Pullback.continuous_lift F E f,
          isOpenMap_lift hf.isOpenQuotientMap.isOpenMap hπ⟩
      continuous_const_smul := fun g ↦ continuous_iff.2 ⟨?_, ?_⟩
      apply_eq_iff_mem_orbit := fun {z₁ z₂} ↦ ⟨fun h ↦ ?_, ?_⟩
      disjoint := fun z ↦ ?_ }
  · rw [← mem_range, range_lift]
    exact hf.surjective w.proj
  · simp_rw [hproj]
    exact (continuous_const_smul g).comp (Pullback.continuous_proj F E f)
  · simp_rw [hlift]
    exact Pullback.continuous_lift F E f
  · obtain ⟨g, hg⟩ := hf.apply_eq_iff_mem_orbit.1 (congrArg (π F E) h)
    exact ⟨g, totalSpace_ext ((hproj g z₂).trans hg) ((hlift g z₂).trans h.symm)⟩
  · rintro ⟨g, rfl⟩
    exact hlift g z₂
  · -- The points over a neighbourhood of `z.proj` with pairwise disjoint translates.
    obtain ⟨U, hU, hUd⟩ := hf.disjoint z.proj
    refine ⟨π F (f *ᵖ E) ⁻¹' U, (Pullback.continuous_proj F E f).continuousAt.preimage_mem_nhds hU,
      fun g ⟨_, ⟨y, hy, rfl⟩, hy'⟩ ↦ hUd g ⟨_, ⟨y.proj, hy, rfl⟩, ?_⟩⟩
    rw [mem_preimage, hproj] at hy'
    exact hy'

/-- If `f` is a topological inducing map and the projection `π F E` is continuous, then
`Pullback.lift f` is a topological inducing map. -/
theorem Bundle.Pullback.isInducing_lift_of_continuous_proj {f : B' → B} (hf : IsInducing f)
    (hπ : Continuous (π F E)) :
    IsInducing (Pullback.lift (F := F) (E := E) f) :=
  IsInducing.of_comp (Pullback.continuous_lift F E f) (hπ.prodMk continuous_id)
    ((hf.prodMap .id).comp (inducing_pullbackTotalSpaceEmbedding F E f))

variable [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- Along a topological inducing map `f`, the canonical lift `Pullback.lift f` of a fibre bundle
is a topological inducing map. -/
theorem Bundle.Pullback.isInducing_lift {f : B' → B} (hf : IsInducing f) :
    IsInducing (Pullback.lift (F := F) (E := E) f) :=
  isInducing_lift_of_continuous_proj hf (FiberBundle.continuous_proj F E)

/-- Along a topological embedding `f`, the canonical lift `Pullback.lift f` of a fibre bundle is a
topological embedding. -/
theorem Bundle.Pullback.isEmbedding_lift {f : B' → B} (hf : IsEmbedding f) :
    IsEmbedding (Pullback.lift (F := F) (E := E) f) :=
  ⟨isInducing_lift hf.isInducing, lift_injective hf.injective⟩

/-- Along a closed embedding `f`, the canonical lift `Pullback.lift f` of a fibre bundle is a
closed embedding. -/
theorem Bundle.Pullback.isClosedEmbedding_lift {f : B' → B} (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (Pullback.lift (F := F) (E := E) f) :=
  ⟨isEmbedding_lift hf.isEmbedding,
    (range_lift (F := F) (E := E) f).symm ▸
      hf.isClosed_range.preimage (FiberBundle.continuous_proj F E)⟩

/-- Along an open embedding `f`, the canonical lift `Pullback.lift f` of a fibre bundle is an open
embedding. -/
theorem Bundle.Pullback.isOpenEmbedding_lift {f : B' → B} (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (Pullback.lift (F := F) (E := E) f) :=
  ⟨isEmbedding_lift hf.isEmbedding,
    (range_lift (F := F) (E := E) f).symm ▸
      hf.isOpen_range.preimage (FiberBundle.continuous_proj F E)⟩

end Lift

variable {F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, Nonempty (E b)] {K : Type*} [FunLike K B' B]
  [ContinuousMapClass K B' B]

/-- The fibre coordinate in a pullback chart is the original chart's fibre coordinate at the
canonical lift. -/
theorem Bundle.Pullback.trivializationAt_snd [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    (f : K) (x₀ : B') (z : TotalSpace F ((f : B' → B) *ᵖ E)) :
    (trivializationAt F ((f : B' → B) *ᵖ E) x₀ z).2 =
      (trivializationAt F E (f x₀) (Pullback.lift f z)).2 := by
  simp only [trivializationAt, FiberBundle.pullback_trivializationAt',
    Trivialization.pullback_apply]

/-- Evaluating the fibrewise inverse of a pulled-back trivialization at `x` agrees with evaluating
the original fibrewise inverse at `f x` on the base set. -/
@[simp]
theorem Bundle.Trivialization.pullback_symm_apply (e : Trivialization F (π F E)) (f : K)
    {x : B'} (hx : f x ∈ e.baseSet) (v : F) :
    (e.pullback f).symm x v = e.symm (f x) v :=
  (e.pullback f).toPretrivialization.symm_apply hx v

/-- The coordinate change between the pullbacks of two trivializations, over a point `x` whose
image `f x` lies in the base set of the first, is the coordinate change between the
trivializations over `f x`. -/
theorem Bundle.Trivialization.coordChange_pullback (e e' : Trivialization F (π F E)) (f : K)
    {x : B'} (hx : f x ∈ e.baseSet) (v : F) :
    (e.pullback f).coordChange (e'.pullback f) x v = e.coordChange e' (f x) v := by
  rw [Trivialization.coordChange, Trivialization.coordChange, Trivialization.pullback_apply,
    ← e.mk_symm hx]
  -- By construction, the inverse of `e.pullback f` sends `(x, v)` to the point `e.symm (f x) v` of
  -- the fibre over `x`, and `Pullback.lift f` sends that point to `⟨f x, e.symm (f x) v⟩`.
  rfl
