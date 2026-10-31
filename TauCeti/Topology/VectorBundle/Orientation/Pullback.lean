/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# Pullbacks of bundle orientations and orientation covers

The orientation cover of a pulled-back real vector bundle is canonically homeomorphic to
the pullback of its orientation cover. The comparison retains the actual fibre orientation,
commutes with the deck involutions, and takes a pulled-back orientation section to the
pullback of the original section. In particular, the orientation cover and its sections
can be transported along finite-stage bundle inclusions without choosing a metric.

Both signs are retained in rank zero. No separation assumptions on either base are needed.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9.
-/

public section
noncomputable section

open Bundle Filter Module Set
open scoped Topology

variable {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] {ι : Type*}

namespace Bundle.Trivialization

/-- A pulled-back chart reads the same fibre orientation as the original chart. -/
@[simp]
theorem mapOrientation_pullback (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (f : C(B', B)) {b : B'} (hb : f b ∈ e.baseSet)
    (o : Orientation ℝ (((f : B' → B) *ᵖ E) b) ι) :
    (e.pullback f).mapOrientation ι hb o = e.mapOrientation ι hb o := by
  have he : (e.pullback f).linearEquivAt ℝ b hb = e.linearEquivAt ℝ (f b) hb := by
    ext v
    rfl
  calc
    _ = Orientation.map ι ((e.pullback f).linearEquivAt ℝ b hb) o :=
      mapOrientation_apply _ _ _
    _ = Orientation.map ι (e.linearEquivAt ℝ (f b) hb) o :=
      congrArg (fun L ↦ Orientation.map ι L o) he
    _ = _ := (mapOrientation_apply _ _ _).symm

end Bundle.Trivialization

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

namespace TauCeti.VectorBundleOrientation

/-- Pull back an orientation along a continuous map, retaining its fibre orientations. -/
def pullback (o : VectorBundleOrientation F E ι) (f : C(B', B)) :
    VectorBundleOrientation F ((f : B' → B) *ᵖ E) ι where
  toFun b := o (f b)
  eventually_mapOrientation_eq' b := by
    have h := f.continuous.continuousAt.eventually (o.eventually_mapOrientation_eq' (f b))
    filter_upwards [h] with x hx hxe
    simp only [FiberBundle.pullback_trivializationAt']
    exact (Trivialization.mapOrientation_pullback _ f hxe _).trans
      ((hx hxe).trans (Trivialization.mapOrientation_pullback _ f _ _).symm)

@[simp]
theorem pullback_apply (o : VectorBundleOrientation F E ι) (f : C(B', B)) (b : B') :
    o.pullback f b = o (f b) :=
  (rfl)

/-- Pullback commutes with reversal of the orientation. -/
@[simp]
theorem pullback_neg (o : VectorBundleOrientation F E ι) (f : C(B', B)) :
    (-o).pullback f = -(o.pullback f) := by
  ext b
  simp only [pullback_apply, neg_apply]
  rfl

end TauCeti.VectorBundleOrientation

namespace TauCeti.VectorBundleOrientationCover

/-- The map from the orientation cover of a pullback bundle to the original orientation cover.
It changes only the base point by `f`. -/
def pullbackLift (f : C(B', B))
    (p : VectorBundleOrientationCover F ((f : B' → B) *ᵖ E) ι) :
    VectorBundleOrientationCover F E ι :=
  ⟨f p.proj, p.orientation⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
@[simp]
theorem pullbackLift_mk (f : C(B', B)) (b : B') (o : Orientation ℝ (E (f b)) ι) :
    pullbackLift f (⟨b, o⟩ : VectorBundleOrientationCover F ((f : B' → B) *ᵖ E) ι) =
      (⟨f b, o⟩ : VectorBundleOrientationCover F E ι) :=
  (rfl)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
@[simp]
theorem proj_pullbackLift (f : C(B', B))
    (p : VectorBundleOrientationCover F ((f : B' → B) *ᵖ E) ι) :
    (pullbackLift f p).proj = f p.proj :=
  (rfl)

/-- The canonical lift commutes with orientation reversal. -/
@[simp]
theorem pullbackLift_deck (f : C(B', B))
    (p : VectorBundleOrientationCover F ((f : B' → B) *ᵖ E) ι) :
    pullbackLift f (deck p) = deck (pullbackLift f p) := by
  cases p
  simp only [deck_apply]
  rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
/-- The lift along the identity map retains the point of the orientation cover. -/
@[simp]
theorem pullbackLift_id (p : VectorBundleOrientationCover F E ι) :
    pullbackLift (ContinuousMap.id B) p = p := by
  cases p
  rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
/-- Lifting along a composite agrees with the two successive lifts. -/
@[simp]
theorem pullbackLift_comp {B'' : Type*} [TopologicalSpace B'']
    (f : C(B', B)) (g : C(B'', B'))
    (p : VectorBundleOrientationCover F ((g : B'' → B') *ᵖ ((f : B' → B) *ᵖ E)) ι) :
    pullbackLift f (pullbackLift g p) = pullbackLift (f.comp g) p :=
  (rfl)

omit [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E] in
/-- Sheets pull back to the sheets of the pulled-back bundle charts. -/
@[simp]
theorem preimage_sheet_pullbackLift (f : C(B', B))
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] (o : Orientation ℝ F ι) :
    pullbackLift f ⁻¹' sheet e o = sheet (e.pullback f) o := by
  ext ⟨x, a⟩
  simp only [mem_preimage, mem_sheet_iff, Trivialization.pullback_baseSet]
  exact exists_congr fun h ↦
    (iff_of_eq (congrArg (fun a ↦ a = o) (e.mapOrientation_pullback f h a))).symm

/-- The lift to the original orientation cover is continuous. -/
theorem continuous_pullbackLift [Fintype ι] [FiniteDimensional ℝ F]
    (hι : Fintype.card ι = finrank ℝ F) (f : C(B', B)) :
    Continuous (pullbackLift (F := F) (E := E) (ι := ι) f) := by
  refine continuous_of_isOpen_preimage_sheet (f.continuous.comp continuous_proj) fun b o ↦ ?_
  rw [preimage_sheet_pullbackLift]
  let : MemTrivializationAtlas ((trivializationAt F E b).pullback f) :=
    ⟨⟨trivializationAt F E b, inferInstance, rfl⟩⟩
  exact isOpen_sheet hι _ o

/-- The topological pullback of the orientation cover along `f`, as a subspace of the product. -/
abbrev Pullback (f : C(B', B)) :=
  {p : B' × VectorBundleOrientationCover F E ι // f p.1 = p.2.proj}

private def fromPullback (f : C(B', B)) (p : Pullback (F := F) (E := E) (ι := ι) f) :
    VectorBundleOrientationCover F ((f : B' → B) *ᵖ E) ι :=
  -- The pullback fibre is the original fibre at the image point.
  ⟨p.1.1, (show Orientation ℝ (E (f p.1.1)) ι from p.2.symm ▸ p.1.2.orientation)⟩

private theorem continuous_fromPullback (f : C(B', B)) :
    Continuous (fromPullback (F := F) (E := E) (ι := ι) f) := by
  refine continuous_of_isOpen_preimage_sheet
    (continuous_fst.comp continuous_subtype_val) fun b o ↦ ?_
  have hset : fromPullback f ⁻¹' sheet (trivializationAt F ((f : B' → B) *ᵖ E) b) o =
      (fun p : Pullback (F := F) (E := E) (ι := ι) f ↦ p.1.2) ⁻¹'
        sheet (trivializationAt F E (f b)) o := by
    ext ⟨⟨x, ⟨y, a⟩⟩, h⟩
    dsimp only at h
    subst y
    simp only [mem_preimage, fromPullback, mem_sheet_iff,
      FiberBundle.pullback_trivializationAt', Trivialization.pullback_baseSet, mem_preimage]
    exact exists_congr fun h ↦ iff_of_eq (congrArg (fun a ↦ a = o)
      ((trivializationAt F E (f b)).mapOrientation_pullback f h a))
  rw [hset]
  exact (isOpen_sheet_trivializationAt _ _).preimage
    (continuous_snd.comp continuous_subtype_val)

/-- The orientation cover commutes with continuous pullback as an actual homeomorphism over
the new base. Its forward map remembers the new base point and the unchanged fibre orientation. -/
def pullbackHomeomorph [Fintype ι] [FiniteDimensional ℝ F]
    (hι : Fintype.card ι = finrank ℝ F) (f : C(B', B)) :
    VectorBundleOrientationCover F ((f : B' → B) *ᵖ E) ι ≃ₜ
      Pullback (F := F) (E := E) (ι := ι) f where
  toFun p := ⟨(p.proj, pullbackLift f p), rfl⟩
  invFun := fromPullback f
  left_inv p := by cases p; rfl
  right_inv p := by
    rcases p with ⟨⟨x, ⟨y, a⟩⟩, h⟩
    dsimp only at h
    subst y
    rfl
  continuous_toFun :=
    (continuous_proj.prodMk (continuous_pullbackLift hι f)).subtype_mk _
  continuous_invFun := continuous_fromPullback f

variable [Fintype ι] [FiniteDimensional ℝ F]

@[simp]
theorem pullbackHomeomorph_apply (hι : Fintype.card ι = finrank ℝ F) (f : C(B', B))
    (p : VectorBundleOrientationCover F ((f : B' → B) *ᵖ E) ι) :
    pullbackHomeomorph hι f p = ⟨(p.proj, pullbackLift f p), (proj_pullbackLift f p).symm⟩ :=
  (rfl)

@[simp]
theorem pullbackHomeomorph_symm_mk (hι : Fintype.card ι = finrank ℝ F) (f : C(B', B))
    (b : B') (o : Orientation ℝ (E (f b)) ι) :
    (pullbackHomeomorph hι f).symm ⟨(b, ⟨f b, o⟩), rfl⟩ = ⟨b, o⟩ :=
  (rfl)

end TauCeti.VectorBundleOrientationCover
