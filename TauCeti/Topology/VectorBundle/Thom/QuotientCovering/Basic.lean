/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Quotient
public import TauCeti.Topology.FiberBundle.Pullback
public import TauCeti.Topology.VectorBundle.EulerClass

/-!
# The Thom pair of a bundle pulled back along a quotient covering map

Let `f : X → B` be the quotient covering map of an action of a group `G` on `X`, in the sense of
Mathlib's `IsQuotientCoveringMap`, and let `E → B` be a fibre bundle. Let `G` act on the total
space `E'` of the pull-back `f^*E` over its action on `X`, fixing the image of each point in the
total space of `E`; the action `Bundle.Pullback.totalSpaceMulAction`, which moves base points and
keeps vectors, is one such action. This file shows that the Thom pair `(E', E'₀)` of the pull-back
is then the quotient-covering-space presentation of the Thom pair `(E, E₀)` of `E`:

* the action preserves the nonzero vectors `E'₀`, and the restricted action
  (`TauCeti.pullbackThomPairSndMulAction`) is continuous when the action on `E'` is
  (`TauCeti.pullbackThomPairSndMulAction_continuousConstSMul`) and commutes with the embedding
  `E'₀ → E'` (`TauCeti.pullbackThomPairSndMulAction_thomPair_map_smul`);
* both maps underlying the map of Thom pairs `(E', E'₀) ⟶ (E, E₀)` (`TauCeti.pullbackThomPairMap`)
  are quotient covering maps of the action of `G`
  (`TauCeti.isQuotientCoveringMap_pullbackThomPairMap_fst`,
  `TauCeti.isQuotientCoveringMap_pullbackThomPairMap_snd`).

These are the hypotheses under which the relative chains of `(E', E'₀)`, as a complex of
representations of `G`, compute the homology of `(E, E₀)` with coefficients in the local system
associated to a representation of `G` (`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`),
and under which an equivariant Thom cocycle upstairs descends to a Thom isomorphism downstairs
(`TauCeti.quotientTwistedHomologyThomIso`). The orientation double cover of `E`, with `G = ℤˣ`, is
one instance (`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_pullbackThomPairMap_fst`);
the universal cover of the base, with `G = π₁(B)`, is another, and is the route to the Thom
isomorphism with coefficients in an arbitrary local system on the base.

As in `TauCeti.pullbackThomPairMap`, the zeros of the fibres of the pull-back are read through
`TauCeti.pullbackFiberZero`, so that the Thom pair of `f^*E` here is the source of that map.

## Main definitions and results

* `TauCeti.pullbackThomPairFstMulAction`, `TauCeti.pullbackThomPairSndMulAction`: an action on the
  total space of the pull-back, as an action on the two spaces of its Thom pair.
* `TauCeti.isQuotientCoveringMap_pullbackThomPairMap_fst`,
  `TauCeti.isQuotientCoveringMap_pullbackThomPairMap_snd`: the Thom pair of the pull-back covers the
  Thom pair of `E`, as the quotient of a free action of `G` on both of its spaces.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (covering spaces as
  quotients of covering space actions) and §3.H (local coefficients).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill, 1966, Chapter 5, Section 7 (the Thom
  isomorphism with local coefficients).
-/

public section

open Bundle Set Topology

namespace TauCeti

universe w

variable {B : Type w} [TopologicalSpace B] {F : Type*} [TopologicalSpace F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] {X : Type w} [TopologicalSpace X]
  {f : C(X, B)}

-- The zeros of the fibres of the pull-back are read as in `TauCeti.pullbackThomPairMap`, so that
-- the Thom pair of the pull-back below is the source of that map.
attribute [local instance] pullbackFiberZero

variable {G : Type*} [Monoid G] [MulAction G (TotalSpace F ((⇑f) *ᵖ E))]

variable (F E f G) in
/-- An action of `G` on the total space `E'` of the pull-back `f^*E`, as an action on the total
space of the Thom pair `(E', E'₀)`.

This is not an instance, since `(thomPair F _).fst` is a different type for instance search;
statements using it introduce it with `letI`. -/
abbrev pullbackThomPairFstMulAction : MulAction G (thomPair F ((⇑f) *ᵖ E)).fst :=
  ‹MulAction G (TotalSpace F ((⇑f) *ᵖ E))›

/-- **The action on the nonzero vectors of a pull-back.** An action of `G` on the total space `E'`
of the pull-back `f^*E` which fixes the image of each point in the total space of `E` preserves the
nonzero vectors `E'₀`, the subspace of the Thom pair of `f^*E`, since a vector of `f^*E` is nonzero
exactly when its image in `E` is: this is the restricted action.

This is not an instance, since it depends on the hypothesis on the action of `G`; statements using
it introduce it with `letI`. -/
abbrev pullbackThomPairSndMulAction
    (hlift : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)),
      Pullback.lift f (g • z) = Pullback.lift f z) :
    MulAction G (thomPair F ((⇑f) *ᵖ E)).snd where
  smul g v := ⟨g • v.val, (preimage_pullbackLift_zeroSectionCompl _).subset <| by
    rw [Set.mem_preimage, hlift]
    exact (preimage_pullbackLift_zeroSectionCompl (F := F) (E := E) f).superset v.property⟩
  one_smul v := Subtype.ext (one_smul G v.val)
  mul_smul g g' v := Subtype.ext (mul_smul g g' v.val)

omit [TopologicalSpace F] in
/-- The action `TauCeti.pullbackThomPairSndMulAction` on the nonzero vectors of a pull-back is the
action on the underlying vectors. -/
@[simp]
theorem pullbackThomPairSndMulAction_coe_smul
    (hlift : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)),
      Pullback.lift f (g • z) = Pullback.lift f z)
    (g : G) (v : (thomPair F ((⇑f) *ᵖ E)).snd) :
    letI := pullbackThomPairSndMulAction hlift
    (g • v).val = g • v.val :=
  (rfl)

omit [TopologicalSpace F] in
/-- The embedding `E'₀ → E'` of the Thom pair of a pull-back commutes with the actions
`TauCeti.pullbackThomPairSndMulAction` and `TauCeti.pullbackThomPairFstMulAction`. -/
theorem pullbackThomPairSndMulAction_thomPair_map_smul
    (hlift : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)),
      Pullback.lift f (g • z) = Pullback.lift f z)
    (g : G) (v : (thomPair F ((⇑f) *ᵖ E)).snd) :
    letI := pullbackThomPairFstMulAction F E f G
    letI := pullbackThomPairSndMulAction hlift
    (thomPair F ((⇑f) *ᵖ E)).map (g • v) = g • (thomPair F ((⇑f) *ᵖ E)).map v := by
  rw [TopPair.ofSubset_map]
  exact pullbackThomPairSndMulAction_coe_smul hlift g v

omit [TopologicalSpace F] in
/-- The action `TauCeti.pullbackThomPairFstMulAction` on the total space of the Thom pair of a
pull-back is continuous when the action on the total space of the pull-back is. -/
theorem pullbackThomPairFstMulAction_continuousConstSMul
    [ContinuousConstSMul G (TotalSpace F ((⇑f) *ᵖ E))] :
    letI := pullbackThomPairFstMulAction F E f G
    ContinuousConstSMul G (thomPair F ((⇑f) *ᵖ E)).fst :=
  ‹ContinuousConstSMul G (TotalSpace F ((⇑f) *ᵖ E))›

omit [TopologicalSpace F] in
/-- The action `TauCeti.pullbackThomPairSndMulAction` on the nonzero vectors of a pull-back is
continuous when the action on the total space is. -/
theorem pullbackThomPairSndMulAction_continuousConstSMul
    [ContinuousConstSMul G (TotalSpace F ((⇑f) *ᵖ E))]
    (hlift : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)),
      Pullback.lift f (g • z) = Pullback.lift f z) :
    letI := pullbackThomPairSndMulAction hlift
    ContinuousConstSMul G (thomPair F ((⇑f) *ᵖ E)).snd :=
  letI := pullbackThomPairSndMulAction hlift
  ⟨fun g ↦ ((continuous_const_smul g : Continuous fun z : TotalSpace F ((⇑f) *ᵖ E) ↦
    g • z).comp continuous_subtypeVal).subtype_mk _⟩

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The projection `E' → X` of the pull-back commutes with the action
`TauCeti.pullbackThomPairFstMulAction` on the total space of its Thom pair when the action on the
total space covers an action on `X`. -/
theorem pullbackThomPairFstMulAction_thomPairProj_smul [MulAction G X]
    (hproj : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)), (g • z).proj = g • z.proj) (g : G)
    (v : (thomPair F ((⇑f) *ᵖ E)).fst) :
    letI := pullbackThomPairFstMulAction F E f G
    thomPairProj F ((⇑f) *ᵖ E) (g • v) = g • thomPairProj F ((⇑f) *ᵖ E) v :=
  (thomPairProj_apply F _ _).trans
    ((hproj g v).trans (congrArg (g • ·) (thomPairProj_apply F _ v).symm))

/-- **The Thom pair of a pull-back along a quotient covering map: total spaces.** If `f : X → B` is
the quotient covering map of an action of a group `G`, and `G` acts on the total space of `f^*E`
over its action on `X`, fixing the image of each point in the total space of `E`, then the map of
total spaces underlying the map of Thom pairs `(f^*E, (f^*E)₀) ⟶ (E, E₀)` is the quotient covering
map of this action. -/
theorem isQuotientCoveringMap_pullbackThomPairMap_fst {G : Type*} [Group G] [MulAction G X]
    [MulAction G (TotalSpace F ((⇑f) *ᵖ E))] (hf : IsQuotientCoveringMap f G)
    (hproj : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)), (g • z).proj = g • z.proj)
    (hlift : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)),
      Pullback.lift f (g • z) = Pullback.lift f z) :
    letI := pullbackThomPairFstMulAction F E f G
    IsQuotientCoveringMap (TopPair.Hom.fst (pullbackThomPairMap F E f)) G := by
  rw [show ⇑(TopPair.Hom.fst (pullbackThomPairMap F E f)) = Pullback.lift f from
    funext (pullbackThomPairMap_fst_apply F E f)]
  exact Pullback.isQuotientCoveringMap_lift hf (FiberBundle.continuous_proj F E) hproj hlift

/-- **The Thom pair of a pull-back along a quotient covering map: nonzero vectors.** If `f : X → B`
is the quotient covering map of an action of a group `G`, and `G` acts on the total space of `f^*E`
over its action on `X`, fixing the image of each point in the total space of `E`, then the map of
nonzero vectors underlying the map of Thom pairs `(f^*E, (f^*E)₀) ⟶ (E, E₀)` is the quotient
covering map of the restricted action `TauCeti.pullbackThomPairSndMulAction`. With
`TauCeti.isQuotientCoveringMap_pullbackThomPairMap_fst`, this presents the Thom pair `(E, E₀)` as
the quotient of the pair `(f^*E, (f^*E)₀)` by a free action of `G`. -/
theorem isQuotientCoveringMap_pullbackThomPairMap_snd {G : Type*} [Group G] [MulAction G X]
    [MulAction G (TotalSpace F ((⇑f) *ᵖ E))] (hf : IsQuotientCoveringMap f G)
    (hproj : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)), (g • z).proj = g • z.proj)
    (hlift : ∀ (g : G) (z : TotalSpace F ((⇑f) *ᵖ E)),
      Pullback.lift f (g • z) = Pullback.lift f z) :
    letI := pullbackThomPairSndMulAction hlift
    IsQuotientCoveringMap (TopPair.Hom.snd (pullbackThomPairMap F E f)) G := by
  -- `IsQuotientCoveringMap.restrict` asks for the action on the subtype of nonzero vectors, which
  -- `(thomPair F _).snd` unfolds to (`thomPair` is `TopPair.ofSubset` of `zeroSectionCompl`).
  let : MulAction G (zeroSectionCompl F ((⇑f) *ᵖ E)) := pullbackThomPairSndMulAction hlift
  -- The nonzero vectors of the pull-back are the preimage of those of `E`, so the map they
  -- underlie is the restriction of `Pullback.lift`.
  have h : Set.MapsTo (Pullback.lift f) (zeroSectionCompl F ((⇑f) *ᵖ E)) (zeroSectionCompl F E) :=
    Set.mapsTo_iff_subset_preimage.2 (preimage_pullbackLift_zeroSectionCompl _).superset
  rw [show ⇑(TopPair.Hom.snd (pullbackThomPairMap F E f)) = h.restrict _ _ _ from
    funext fun v ↦ Subtype.ext (pullbackThomPairMap_snd_apply F E f v)]
  exact (Pullback.isQuotientCoveringMap_lift hf (FiberBundle.continuous_proj F E) hproj
    hlift).restrict (pullbackThomPairSndMulAction_coe_smul hlift) h
    (preimage_pullbackLift_zeroSectionCompl _).subset

end TauCeti
