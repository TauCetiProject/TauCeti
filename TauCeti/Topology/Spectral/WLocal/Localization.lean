/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.WLocal.Basic
public import TauCeti.Topology.Spectral.Limits.Basic
public import Mathlib.Topology.WithTopology
import TauCeti.Topology.Spectral.ConnectedComponents

/-!
# W-localization of spectral spaces

The w-localization of a spectral space `X` consists of pairs `(x, y)` with `y` a
generalization of `x`, inside `WithConstructibleTopology X × X`. The second projection
is the counit to `X`; the first labels the connected components by the constructible
topology of `X`. Its closed points are precisely the diagonal pairs.

This construction supplies w-local covers without discarding specialization chains.
It is functorial for spectral maps, and has a unique w-local lift of each spectral map
from a w-local space. W-local maps are spectral maps preserving closed points.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369
  (2015), §2.1, Lemma 2.1.10 and Remark 2.1.11.
* P. Scholze, *Étale cohomology of diamonds*, §7, Lemmas 7.13–7.14.
-/

public section

open Function Set Topology TopologicalSpace

universe u v w

namespace TauCeti

/-- The specialization-pair model of w-localization. The first coordinate has the
constructible topology, and the second retains the original topology. -/
-- The module compiler requires this for the subtype carrier and endpoint projections.
@[expose]
def WLocalization (X : Type u) [TopologicalSpace X] :=
  {q : WithConstructibleTopology X × X // q.2 ⤳ WithTopology.ofTopology q.1}

namespace WLocalization

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

instance : TopologicalSpace (WLocalization X) :=
  inferInstanceAs (TopologicalSpace {q : WithConstructibleTopology X × X |
    q.2 ⤳ WithTopology.ofTopology q.1})

local instance [SpectralSpace X] : SpectralSpace (WithConstructibleTopology X) :=
  spectralSpace_of_zeroDimensionalSpace _

/-- The counit sends a pair to its generalizing endpoint. -/
def toBase (q : WLocalization X) : X := q.val.2

/-- The component label is the specialization endpoint, with the constructible topology. -/
def componentLabel (q : WLocalization X) : WithConstructibleTopology X := q.val.1

/-- The endpoints of a specialization pair have the indicated specialization relation. -/
theorem specializes_label (q : WLocalization X) :
    toBase q ⤳ WithTopology.ofTopology (componentLabel q) := q.property

/-- A pair is determined by its two endpoints. -/
@[ext]
theorem ext {q r : WLocalization X} (h₁ : componentLabel q = componentLabel r)
    (h₂ : toBase q = toBase r) : q = r := Subtype.ext (Prod.ext h₁ h₂)

/-- Construct a pair from a label and one of its generalizations. -/
def ofSpecializes (x : WithConstructibleTopology X) (y : X)
    (h : y ⤳ WithTopology.ofTopology x) : WLocalization X := ⟨(x, y), h⟩

@[simp]
theorem componentLabel_ofSpecializes (x : WithConstructibleTopology X) (y : X)
    (h : y ⤳ WithTopology.ofTopology x) : componentLabel (ofSpecializes x y h) = x := (rfl)

@[simp]
theorem toBase_ofSpecializes (x : WithConstructibleTopology X) (y : X)
    (h : y ⤳ WithTopology.ofTopology x) : toBase (ofSpecializes x y h) = y := (rfl)

/-- Reconstructing a pair from its endpoints gives the original pair. -/
@[simp]
theorem ofSpecializes_componentLabel_toBase (q : WLocalization X) :
    ofSpecializes (componentLabel q) (toBase q) q.specializes_label = q := (rfl)

/-- The diagonal pair labelled by a constructible point. -/
def diagonal (x : WithConstructibleTopology X) : WLocalization X :=
  ⟨(x, WithTopology.ofTopology x), specializes_rfl⟩

@[simp]
theorem componentLabel_diagonal (x : WithConstructibleTopology X) :
    componentLabel (diagonal x) = x := (rfl)

@[simp]
theorem toBase_diagonal (x : WithConstructibleTopology X) :
    toBase (diagonal x) = WithTopology.ofTopology x := (rfl)

/-- Every pair specializes to the diagonal point in its component. -/
theorem specializes_diagonal (q : WLocalization X) : q ⤳ diagonal (componentLabel q) :=
  (subtype_specializes_iff q _).2 (specializes_rfl.prod q.specializes_label)

/-- The component label is continuous. -/
theorem continuous_componentLabel : Continuous (componentLabel : WLocalization X → _) :=
  continuous_fst.comp continuous_subtypeVal

/-- The counit is continuous. -/
theorem continuous_toBase : Continuous (toBase : WLocalization X → X) :=
  continuous_snd.comp continuous_subtypeVal

/-- A map into w-localization is continuous exactly when both endpoint maps are continuous. -/
theorem continuous_iff {f : Y → WLocalization X} :
    Continuous f ↔ Continuous (componentLabel ∘ f) ∧ Continuous (toBase ∘ f) := by
  constructor
  · intro hf
    exact ⟨continuous_componentLabel.comp hf, continuous_toBase.comp hf⟩
  · rintro ⟨h₁, h₂⟩
    exact (h₁.prodMk h₂).subtype_mk _

/-- Continuous endpoint maps satisfying specialization give a continuous family of pairs. -/
theorem continuous_ofSpecializes {x : Y → WithConstructibleTopology X} {y : Y → X}
    (hx : Continuous x) (hy : Continuous y)
    (h : ∀ z, y z ⤳ WithTopology.ofTopology (x z)) :
    Continuous (fun z ↦ ofSpecializes (x z) (y z) (h z)) :=
  continuous_iff.2 ⟨hx, hy⟩

/-- The counit is surjective, including when the base is empty. -/
theorem surjective_toBase : Surjective (toBase : WLocalization X → X) :=
  fun x ↦ ⟨diagonal (WithTopology.toTopology _ x), rfl⟩

/-- The component label is surjective. -/
theorem surjective_componentLabel : Surjective (componentLabel : WLocalization X → _) :=
  fun x ↦ ⟨diagonal x, rfl⟩

section Spectral

variable [SpectralSpace X]

private theorem isProConstructible_pairs :
    IsProConstructible {q : WithConstructibleTopology X × X |
      q.2 ⤳ WithTopology.ofTopology q.1} := by
  have heq : {q : WithConstructibleTopology X × X |
      q.2 ⤳ WithTopology.ofTopology q.1} =
      ⋂ U : {U : Set X // IsOpen U ∧ IsCompact U},
        ((Prod.fst ⁻¹' (WithTopology.ofTopology ⁻¹' U.val))ᶜ ∪ Prod.snd ⁻¹' U.val) := by
    ext q
    simp only [mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, mem_preimage]
    rw [← not_iff_not, PrespectralSpace.not_specializes_iff_exists_isOpen_isCompact]
    simp
  rw [heq]
  refine IsProConstructible.iInter fun U ↦ ?_
  have hU := U.property.2.isClopen_preimage_ofTopology_of_isOpen U.property.1
  exact (hU.isOpen.isClosed_compl.isProConstructible.preimage
    isProperMap_fst_of_compactSpace.isSpectralMap).union
    (U.property.2.isProConstructible U.property.1 |>.preimage
      isProperMap_snd_of_compactSpace.isSpectralMap)

/-- W-localization is spectral. -/
instance : SpectralSpace (WLocalization X) := by
  exact isProConstructible_pairs.spectralSpace

/-- The counit is spectral. -/
theorem isSpectralMap_toBase : IsSpectralMap (toBase : WLocalization X → X) := by
  exact isProConstructible_pairs.isSpectralMap_snd

/-- The component label is spectral. -/
theorem isSpectralMap_componentLabel :
    IsSpectralMap (componentLabel : WLocalization X → _) := by
  exact isProConstructible_pairs.isSpectralMap_fst

end Spectral

section Specialization

variable [PrespectralSpace X] [T0Space X]

omit [T0Space X] in
/-- The diagonal is continuous from the constructible topology to w-localization. -/
theorem continuous_diagonal : Continuous (diagonal : WithConstructibleTopology X → _) :=
  continuous_iff.2 ⟨continuous_id, continuous_ofTopology_withConstructibleTopology X⟩

/-- Specializations keep the label fixed and specialize the generalizing endpoint. -/
@[simp]
theorem specializes_iff {q r : WLocalization X} :
    q ⤳ r ↔ componentLabel q = componentLabel r ∧ toBase q ⤳ toBase r := by
  exact (subtype_specializes_iff q r).trans (specializes_prod.trans
    (and_congr specializes_iff_eq Iff.rfl))

/-- The diagonal points are closed. -/
theorem isClosed_singleton_diagonal (x : WithConstructibleTopology X) :
    IsClosed ({diagonal x} : Set (WLocalization X)) := by
  rw [← closure_subset_iff_isClosed]
  intro q hq
  have h := specializes_iff.1 (specializes_iff_mem_closure.2 hq)
  have heq : toBase q = WithTopology.ofTopology x :=
    (q.specializes_label.trans
      (specializes_of_eq (congrArg WithTopology.ofTopology h.1.symm))).antisymm h.2 |>.eq
  exact mem_singleton_iff.2 (ext h.1.symm heq)

/-- A point is closed exactly when its two endpoints coincide. -/
theorem isClosed_singleton_iff (q : WLocalization X) :
    IsClosed ({q} : Set (WLocalization X)) ↔
      toBase q = WithTopology.ofTopology (componentLabel q) := by
  constructor
  · intro hq
    have h := q.specializes_diagonal.mem_closed hq (mem_singleton q)
    exact congrArg toBase (mem_singleton_iff.1 h).symm
  · intro hq
    have heq : q = diagonal (componentLabel q) := ext rfl hq
    rw [heq]
    exact isClosed_singleton_diagonal _

/-- Two points belong to the same connected component exactly when their labels agree. -/
theorem mem_connectedComponent_iff {q r : WLocalization X} :
    q ∈ connectedComponent r ↔ componentLabel q = componentLabel r := by
  constructor
  · intro h
    exact mem_singleton_iff.1 (continuous_componentLabel.image_connectedComponent_eq_singleton r ▸
      mem_image_of_mem componentLabel h)
  · intro h
    have hr := r.specializes_diagonal.mem_closed isClosed_connectedComponent mem_connectedComponent
    have hq := q.specializes_diagonal.mem_closed isClosed_connectedComponent mem_connectedComponent
    rw [h] at hq
    rw [connectedComponent_eq hr, ← connectedComponent_eq hq]
    exact mem_connectedComponent

end Specialization

section Spectral

variable [SpectralSpace X]

/-- W-localization has split open covers and a closed locus of closed points. -/
theorem isWLocal : IsWLocalSpace (WLocalization X) := by
  rw [isWLocalSpace_def]
  refine ⟨inferInstance, (openCoversSplit_iff _).2 fun q ↦ ?_, ?_⟩
  · refine ⟨diagonal (componentLabel q),
      ⟨mem_connectedComponent_iff.2 rfl, isClosed_singleton_diagonal _⟩, ?_⟩
    rintro r ⟨hr, hc⟩
    have hlabel := mem_connectedComponent_iff.1 hr
    apply ext (r := diagonal (componentLabel q)) hlabel
    exact ((isClosed_singleton_iff r).1 hc).trans (congrArg WithTopology.ofTopology hlabel)
  · have heq : closedPoints (WLocalization X) =
        ⋂ U : {U : Set X // IsOpen U ∧ IsCompact U},
          (toBase ⁻¹' U.val)ᶜ ∪ componentLabel ⁻¹' (WithTopology.ofTopology ⁻¹' U.val) := by
      ext q
      simp only [mem_closedPoints_iff, isClosed_singleton_iff, mem_iInter, mem_union,
        mem_compl_iff, mem_preimage]
      constructor
      · intro h U
        exact not_or_of_imp (fun hy ↦ h ▸ hy)
      · intro h
        have hs : WithTopology.ofTopology (componentLabel q) ⤳ toBase q := by
          rw [← not_not (a := WithTopology.ofTopology (componentLabel q) ⤳ toBase q),
            PrespectralSpace.not_specializes_iff_exists_isOpen_isCompact]
          simpa [Subtype.forall, or_iff_not_imp_left] using h
        exact q.specializes_label.antisymm hs |>.eq
    rw [heq]
    exact isClosed_iInter fun U ↦
      (U.property.1.preimage continuous_toBase).isClosed_compl.union
        ((U.property.2.isClopen_preimage_ofTopology_of_isOpen U.property.1).isClosed.preimage
          continuous_componentLabel)

end Spectral

/-- A fibre of the component label is the space of generalizations of that label. -/
def componentFibre (x : WithConstructibleTopology X) :
    {q : WLocalization X // componentLabel q = x} ≃ₜ {y : X // y ⤳ WithTopology.ofTopology x} where
  toFun q := ⟨toBase q.val, q.val.specializes_label.trans
    (specializes_of_eq (congrArg WithTopology.ofTopology q.property))⟩
  invFun y := ⟨ofSpecializes x y.val y.property, rfl⟩
  left_inv q := Subtype.ext (ext q.property.symm rfl)
  right_inv _ := rfl
  continuous_toFun := (continuous_toBase.comp continuous_subtypeVal).subtype_mk _
  continuous_invFun :=
    (continuous_ofSpecializes continuous_const continuous_subtypeVal _).subtype_mk _

/-- The fibre comparison keeps the generalizing endpoint. -/
@[simp]
theorem componentFibre_apply (x : WithConstructibleTopology X)
    (q : {q : WLocalization X // componentLabel q = x}) :
    (componentFibre x q).val = toBase q.val := (rfl)

/-- The inverse fibre comparison constructs the pair with the specified label and endpoint. -/
@[simp]
theorem componentFibre_symm_apply (x : WithConstructibleTopology X)
    (y : {y : X // y ⤳ WithTopology.ofTopology x}) :
    ((componentFibre x).symm y).val = ofSpecializes x y.val y.property := (rfl)

private theorem bijective_componentLabel_connectedComponentsLift
    [PrespectralSpace X] [T0Space X] :
    Bijective (continuous_componentLabel (X := X)).connectedComponentsLift := by
  constructor
  · intro a b hab
    obtain ⟨q, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨r, rfl⟩ := ConnectedComponents.surjective_coe b
    exact ConnectedComponents.coe_eq_coe'.2 (mem_connectedComponent_iff.2 hab)
  · intro x
    exact ⟨ConnectedComponents.mk (diagonal x), rfl⟩

section Components

variable [SpectralSpace X]

/-- The connected components of w-localization are the constructible points of the base. -/
noncomputable def pi0 : ConnectedComponents (WLocalization X) ≃ₜ WithConstructibleTopology X :=
  ((isHomeomorph_iff_continuous_bijective).2
    ⟨continuous_componentLabel.connectedComponentsLift_continuous,
      bijective_componentLabel_connectedComponentsLift⟩).homeomorph
    (continuous_componentLabel (X := X)).connectedComponentsLift

/-- The component comparison sends each pair to its specialization endpoint. -/
@[simp]
theorem pi0_mk (q : WLocalization X) : pi0 (ConnectedComponents.mk q) = componentLabel q := by
  simp [pi0]

/-- The inverse component comparison is represented by the diagonal pair with that label. -/
@[simp]
theorem pi0_symm_apply (x : WithConstructibleTopology X) :
    pi0.symm x = ConnectedComponents.mk (diagonal x) := by
  apply pi0.injective
  simp

/-- Maps into w-localization are spectral exactly when both endpoint maps are spectral. -/
theorem isSpectralMap_iff {f : Y → WLocalization X} :
    IsSpectralMap f ↔ IsSpectralMap (componentLabel ∘ f) ∧ IsSpectralMap (toBase ∘ f) := by
  constructor
  · intro hf
    exact ⟨isSpectralMap_componentLabel.comp hf, isSpectralMap_toBase.comp hf⟩
  · rintro ⟨h₁, h₂⟩
    have hb := isTopologicalBasis_subtype
      ((PrespectralSpace.isTopologicalBasis (X := WithConstructibleTopology X)).prod
        (PrespectralSpace.isTopologicalBasis (X := X)))
      (fun q : WithConstructibleTopology X × X ↦ q.2 ⤳ WithTopology.ofTopology q.1)
    refine isSpectralMap_of_isTopologicalBasis hb
      (continuous_iff.2 ⟨h₁.continuous, h₂.continuous⟩) ?_
    rintro _ ⟨_, ⟨U, hU, V, hV, rfl⟩, rfl⟩
    exact (h₂.isCompact_preimage_of_isOpen hV.1 hV.2).inter_left
      (hU.2.isClosed.preimage h₁.continuous)

end Components

/-! ### Functoriality -/

/-- A continuous map acts on both endpoints of a specialization pair. -/
def map (f : X → Y) (hf : Continuous f) (q : WLocalization X) : WLocalization Y :=
  ⟨(WithTopology.toTopology _ (f (WithTopology.ofTopology (componentLabel q))), f (toBase q)),
    q.specializes_label.map hf⟩

@[simp]
theorem toBase_map {f : X → Y} (hf : Continuous f) (q : WLocalization X) :
    toBase (map f hf q) = f (toBase q) := (rfl)

@[simp]
theorem componentLabel_map {f : X → Y} (hf : Continuous f) (q : WLocalization X) :
    componentLabel (map f hf q) =
      WithTopology.toTopology _ (f (WithTopology.ofTopology (componentLabel q))) := (rfl)

@[simp]
theorem map_diagonal {f : X → Y} (hf : Continuous f) (x : WithConstructibleTopology X) :
    map f hf (diagonal x) = diagonal (WithTopology.toTopology _ (f (WithTopology.ofTopology x))) :=
  (rfl)

@[simp]
theorem map_id (q : WLocalization X) : map id continuous_id q = q := (rfl)

@[simp]
theorem map_comp {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g)
    (q : WLocalization X) : map (g ∘ f) (hg.comp hf) q = map g hg (map f hf q) := (rfl)

/-- A spectral map induces a continuous map of w-localizations. -/
theorem continuous_map {f : X → Y} (hf : IsSpectralMap f) : Continuous (map f hf.continuous) :=
  continuous_iff.2 ⟨hf.continuous_withConstructibleTopology.comp continuous_componentLabel,
    hf.continuous.comp continuous_toBase⟩

/-- A spectral map induces a spectral map of w-localizations. -/
theorem isSpectralMap_map [SpectralSpace X] [SpectralSpace Y] {f : X → Y}
    (hf : IsSpectralMap f) : IsSpectralMap (map f hf.continuous) := by
  have hpatch : IsSpectralMap (fun x : WithConstructibleTopology X ↦
      WithTopology.toTopology _ (f (WithTopology.ofTopology x))) :=
    hf.continuous_withConstructibleTopology.isProperMap.isSpectralMap
  exact isSpectralMap_iff.2
    ⟨hpatch.comp isSpectralMap_componentLabel, hf.comp isSpectralMap_toBase⟩

/-- The map induced by a spectral map preserves closed points. -/
theorem isWLocalMap_map [SpectralSpace X] [SpectralSpace Y] {f : X → Y}
    (hf : IsSpectralMap f) : IsWLocalMap (map f hf.continuous) := by
  refine ⟨isSpectralMap_map hf, fun q hq ↦ ?_⟩
  rw [mem_closedPoints_iff, isClosed_singleton_iff, toBase_map, componentLabel_map]
  exact congrArg f ((isClosed_singleton_iff q).1 hq)

/-! ### The universal property -/

/-- Lift a continuous map from a w-local space by labelling each point with the image of
its unique closed specialization. -/
noncomputable def lift (hY : IsWLocalSpace Y) (f : Y → X) (hf : Continuous f)
    (y : Y) : WLocalization X :=
  ⟨(WithTopology.toTopology _ (f (hY.closedPoint y)), f y),
    (hY.specializes_closedPoint y).map hf⟩

@[simp]
theorem toBase_lift (hY : IsWLocalSpace Y) {f : Y → X} (hf : Continuous f) (y : Y) :
    toBase (lift hY f hf y) = f y := (rfl)

@[simp]
theorem componentLabel_lift (hY : IsWLocalSpace Y) {f : Y → X} (hf : Continuous f) (y : Y) :
    componentLabel (lift hY f hf y) = WithTopology.toTopology _ (f (hY.closedPoint y)) := (rfl)

/-- The canonical lift is w-local. -/
theorem isWLocalMap_lift [SpectralSpace X] (hY : IsWLocalSpace Y) {f : Y → X}
    (hf : IsSpectralMap f) : IsWLocalMap (lift hY f hf.continuous) := by
  have := hY.spectralSpace
  have : T2Space (closedPoints Y) := hY.closedPointsHomeomorphConnectedComponents.symm.t2Space
  have : CompactSpace (closedPoints Y) :=
    isCompact_iff_compactSpace.1 hY.isClosed_closedPoints.isCompact
  have hinc := hY.isClosed_closedPoints.isClosedEmbedding_subtypeVal.isProperMap.isSpectralMap
  have hpatch := (hf.comp hinc).continuous_toConstructibleTopology.isProperMap.isSpectralMap
  refine ⟨isSpectralMap_iff.2 ⟨hpatch.comp hY.isSpectralMap_closedPoint, hf⟩, fun y hy ↦ ?_⟩
  rw [mem_closedPoints_iff, isClosed_singleton_iff, toBase_lift, componentLabel_lift]
  exact congrArg f (congrArg Subtype.val (hY.closedPoint_coe ⟨y, hy⟩)).symm

/-- A continuous lift preserving closed points is determined by its composite with the counit. -/
theorem lift_unique [PrespectralSpace X] [T0Space X] (hY : IsWLocalSpace Y)
    {f : Y → X} (hf : Continuous f)
    {g : Y → WLocalization X} (hg : Continuous g)
    (hclosed : MapsTo g (closedPoints Y) (closedPoints (WLocalization X)))
    (hgf : toBase ∘ g = f) :
    g = lift hY f hf := by
  funext y
  apply ext
  · apply WithTopology.ofTopology_injective
    have hlabel := (specializes_iff.1
      ((hY.specializes_closedPoint y).map hg)).1
    have hdiag := (isClosed_singleton_iff (g (hY.closedPoint y))).1
      (hclosed (hY.closedPoint y).property)
    calc
      WithTopology.ofTopology (componentLabel (g y)) =
          WithTopology.ofTopology (componentLabel (g (hY.closedPoint y))) :=
        congrArg WithTopology.ofTopology hlabel
      _ = toBase (g (hY.closedPoint y)) := hdiag.symm
      _ = f (hY.closedPoint y) := congrFun hgf _
      _ = WithTopology.ofTopology (componentLabel (lift hY f hf y)) := rfl
  · exact congrFun hgf y

/-- W-localization has a unique w-local lift of every spectral map from a w-local space.
This is the right-adjoint universal property, with the second projection as counit. -/
theorem universal [SpectralSpace X] (hY : IsWLocalSpace Y) {f : Y → X} (hf : IsSpectralMap f) :
    ∃! g : Y → WLocalization X, IsWLocalMap g ∧ toBase ∘ g = f :=
  ⟨lift hY f hf.continuous, ⟨isWLocalMap_lift hY hf, rfl⟩,
    fun _ ⟨hg, hgf⟩ ↦ lift_unique hY hf.continuous hg.continuous hg.map_closedPoints hgf⟩

end WLocalization
end TauCeti
