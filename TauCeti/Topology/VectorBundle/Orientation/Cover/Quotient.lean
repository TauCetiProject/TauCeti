/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Quotient
public import TauCeti.Topology.FiberBundle.Pullback
public import TauCeti.Topology.VectorBundle.EulerClass
public import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# The orientation double cover as a quotient by `ℤˣ`

Let `E → B` be a real vector bundle with model fibre `F`, and let `ι` have cardinality the rank of
`E`. The units `ℤˣ = {1, -1}` act on the orientation double cover `B'` of `E`, with `-1` reversing
the orientation and fixing the base point, so that `-1` acts by the deck involution
(`TauCeti.VectorBundleOrientationCover.neg_one_smul_eq_deck`), a continuous action since the deck
involution is continuous. The projection `B' → B` is then
the quotient map of this action in the strong sense of Mathlib's `IsQuotientCoveringMap`: its
fibres are the orbits, and every point has a neighbourhood disjoint from its image under the deck
involution, namely its sheet in a trivialization
(`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_proj`).

Pull `E` back to `B'`. A point of the total space `E'` of the pullback is a point `p` of the cover
and a vector of the fibre of `E` over the base point of `p`; since the action fixes base points,
`ℤˣ` acts on `E'` by acting on `p` and keeping the vector
(`TauCeti.VectorBundleOrientationCover.pullbackMulAction`). This action covers the action on `B'`
and fixes the image of each point in the total space of `E`, so the canonical map `E' → E` is again
the quotient map of a free action of `ℤˣ`
(`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_lift`), by the general statement for
pullbacks of quotient covering maps (`Bundle.Pullback.isQuotientCoveringMap_lift`). This map
preserves vectors, so the preimage of the nonzero vectors `E₀` of `E` is the set of nonzero vectors
`E'₀` of `E'` (`TauCeti.preimage_pullbackLift_zeroSectionCompl`). So the Thom pair `(E', E'₀)` of
the pulled-back bundle is a double cover of the Thom pair `(E, E₀)` of `E`, as the quotient of a
free action of `ℤˣ` preserving `E'₀`. In the form of a quotient of topological pairs: `ℤˣ` acts on
both spaces of the Thom pair `(E', E'₀)`
(`TauCeti.VectorBundleOrientationCover.thomPairFstMulAction`,
`TauCeti.VectorBundleOrientationCover.thomPairSndMulAction`), continuously
(`TauCeti.VectorBundleOrientationCover.continuousConstSMul_thomPairFst`,
`TauCeti.VectorBundleOrientationCover.continuousConstSMul_thomPairSnd`), the embedding `E'₀ → E'`
and the projection `E' → B'` commute with the actions
(`TauCeti.VectorBundleOrientationCover.thomPair_map_smul`,
`TauCeti.VectorBundleOrientationCover.thomPairProj_smul`), and both maps underlying the
map of Thom pairs `(E', E'₀) ⟶ (E, E₀)` (`TauCeti.pullbackThomPairMap`) are quotient covering maps
(`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_pullbackThomPairMap_fst` and
`TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_pullbackThomPairMap_snd`, the second by
restricting the first, `IsQuotientCoveringMap.restrict`). These are the hypotheses under which the
relative chains of `(E', E'₀)`, as a complex of representations of `ℤˣ`, compute the homology of
`(E, E₀)` with coefficients in the local system associated to any representation
(`TopPair.twistedHomologyIsoHomologyCoinvariantsTensorObj`). As in `TauCeti.pullbackThomPairMap`,
the zeros of the fibres of the pull-back are read through `TauCeti.pullbackFiberZero`, so that the
Thom pair `(E', E'₀)` here is the source of that map.

The pulled-back bundle carries the tautological orientation
(`TauCeti.VectorBundleOrientationCover.tautologicalOrientation`), which the action of `-1` reverses.
This is the shape in which a non-orientable bundle is handled through its orientation cover: with
coefficients in which `2` is invertible, the homology of the pair `(E, E₀)` is the part of the
homology of `(E', E'₀)` fixed by `ℤˣ`, by the transfer of a finite quotient covering.

## Main results

* `TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_proj`: the orientation double cover
  is the quotient of a free action of `ℤˣ` by deck transformations.
* `Bundle.Pullback.isQuotientCoveringMap_lift` (in `TauCeti.Topology.FiberBundle.Pullback`): the
  pullback of a quotient covering map along the projection of a bundle is a quotient covering map.
* `TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_lift`: the total space of the bundle
  pulled back to the orientation double cover is the quotient of the free action of `ℤˣ` lifted
  from the cover.
* `TauCeti.preimage_pullbackLift_zeroSectionCompl` (in `TauCeti.Topology.VectorBundle.EulerClass`):
  the canonical map of a pullback bundle sends exactly the nonzero vectors to nonzero vectors.
* `TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_pullbackThomPairMap_fst`,
  `TauCeti.VectorBundleOrientationCover.isQuotientCoveringMap_pullbackThomPairMap_snd`: the Thom
  pair of the pulled-back bundle is the quotient of a free action of `ℤˣ` on both of its spaces,
  over the Thom pair of the original bundle.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §1.3 (covering spaces as
  quotients of covering space actions) and §3.H (the orientation double cover of a bundle).
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §12.
-/

public section

open Bundle Module Set Topology

universe u

namespace TauCeti

namespace VectorBundleOrientationCover

variable {B : Type*} {F : Type*} {E : B → Type*} [TopologicalSpace B] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] {ι : Type*}

/-- The units `ℤˣ = {1, -1}` act on the orientation double cover: a unit `u` multiplies the
orientation of the fibre by the sign `u`, fixing the base point, so that `-1` reverses it. -/
instance : MulAction ℤˣ (VectorBundleOrientationCover F E ι) where
  smul u p := ⟨p.proj, Units.map (Int.castRingHom ℝ : ℤ →* ℝ) u • p.orientation⟩
  one_smul p := congrArg (mk p.proj) (by rw [map_one, one_smul])
  -- The orientation of `v • p` is `v • p.orientation`, by definition of the action.
  mul_smul u v p := congrArg (mk p.proj) (by rw [map_mul, mul_smul]; rfl)

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)] in
/-- A unit `u` keeps the base point of a point of the orientation double cover and multiplies its
orientation by the sign `u`. -/
theorem smul_def (u : ℤˣ) (p : VectorBundleOrientationCover F E ι) :
    u • p = ⟨p.proj, Units.map (Int.castRingHom ℝ : ℤ →* ℝ) u • p.orientation⟩ :=
  (rfl)

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)] in
/-- The action of `ℤˣ` on the orientation double cover fixes the base point. -/
@[simp]
theorem proj_smul (u : ℤˣ) (p : VectorBundleOrientationCover F E ι) : (u • p).proj = p.proj :=
  (rfl)

omit [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F E)] in
/-- A unit `u` multiplies the orientation of each point of the orientation double cover by the
sign `u`. -/
@[simp]
theorem orientation_smul (u : ℤˣ) (p : VectorBundleOrientationCover F E ι) :
    (proj_smul u p) ▸ (u • p).orientation =
      Units.map (Int.castRingHom ℝ : ℤ →* ℝ) u • p.orientation :=
  (rfl)

variable [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The unit `-1` acts on the orientation double cover by the deck involution. -/
theorem neg_one_smul_eq_deck (p : VectorBundleOrientationCover F E ι) : (-1 : ℤˣ) • p = deck p := by
  rw [smul_def, deck_apply]
  refine congrArg (mk p.proj) (Module.Ray.units_smul_of_neg _ ?_ _)
  simp

/-- The units act continuously on the orientation double cover: `-1` acts by the deck involution.
-/
instance : ContinuousConstSMul ℤˣ (VectorBundleOrientationCover F E ι) where
  continuous_const_smul u := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp_rw [one_smul]
      exact continuous_id
    · simp_rw [neg_one_smul_eq_deck]
      exact (deck (F := F) (E := E) (ι := ι)).continuous

/-- **The orientation double cover is the quotient by its deck transformations.** If `ι` has
cardinality the rank of the bundle, the projection of the orientation double cover is the quotient
map of the action of `ℤˣ`, whose element `-1` acts by the deck involution: the fibres of the
projection are the orbits, and every point has a neighbourhood disjoint from its image under the
deck involution. -/
theorem isQuotientCoveringMap_proj [Fintype ι] [FiniteDimensional ℝ F]
    (hι : Fintype.card ι = finrank ℝ F) :
    IsQuotientCoveringMap (proj : VectorBundleOrientationCover F E ι → B) ℤˣ := by
  refine (isQuotientCoveringMap_iff_isCoveringMap_and _ ℤˣ).2
    ⟨isCoveringMap_proj hι, surjective_proj hι, inferInstance,
      isCancelSMul_iff_eq_one_of_smul_eq.2 fun u p h ↦ ?_, fun {p q} ↦ ⟨fun h ↦ ?_, ?_⟩⟩
  · -- The unit `-1` acts by the deck involution, which fixes no point.
    rcases Int.units_eq_one_or u with rfl | rfl
    · rfl
    · exact absurd ((neg_one_smul_eq_deck p).symm.trans h) (deck_ne_self p)
  · rcases eq_or_eq_deck hι h with rfl | rfl
    exacts [⟨1, one_smul ℤˣ _⟩, ⟨-1, neg_one_smul_eq_deck _⟩]
  · rintro ⟨u, rfl⟩
    exact proj_smul u q

/-- The units `ℤˣ` act on the total space of the bundle pulled back to the orientation double
cover through their action on the cover, keeping the vector: the fibre over `u • p` is the fibre
over `p`, since both are the fibre of the original bundle over the base point of `p`.

This is not a global instance: when the fibres are additive groups, the total space already
carries the fibrewise action `Bundle.TotalSpace.instMulAction` of `ℤˣ` by `v ↦ ±v`, which keeps
the base point instead. The statements below use this action as a local instance. -/
abbrev pullbackMulAction :
    MulAction ℤˣ (TotalSpace F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)) where
  smul u z := ⟨u • z.proj, z.snd⟩
  one_smul z := Pullback.totalSpace_ext (one_smul ℤˣ z.proj) rfl
  mul_smul u v z := Pullback.totalSpace_ext (mul_smul u v z.proj) rfl

attribute [local instance] pullbackMulAction

/-- The action `pullbackMulAction` of `ℤˣ` on the total space of the pulled-back bundle covers its
action on the orientation double cover. -/
@[simp]
theorem proj_smul_totalSpace (u : ℤˣ)
    (z : TotalSpace F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)) :
    (u • z).proj = u • z.proj :=
  (rfl)

-- Not a simp lemma: simplifying the coercion of the bundled projection rewrites the left-hand
-- side, as for `TauCeti.VectorBundleOrientationCover.tautologicalOrientation_apply`.
/-- The action `pullbackMulAction` of `ℤˣ` on the total space of the pulled-back bundle fixes the
image of each point in the total space of the original bundle. -/
theorem lift_smul (u : ℤˣ)
    (z : TotalSpace F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E)) :
    Pullback.lift (projection : VectorBundleOrientationCover F E ι → B) (u • z) =
      Pullback.lift (projection : VectorBundleOrientationCover F E ι → B) z :=
  (rfl)

/-- **The pulled-back total space is a double cover of the original one.** If `ι` has cardinality
the rank of the bundle, the canonical map from the total space of the bundle pulled back to its
orientation double cover to the total space of the bundle is the quotient map of the action
`pullbackMulAction` of `ℤˣ` lifted from the cover. By
`TauCeti.preimage_pullbackLift_zeroSectionCompl`, the preimage of the nonzero vectors is the set of
nonzero vectors of the pulled-back bundle. -/
theorem isQuotientCoveringMap_lift [Fintype ι] [FiniteDimensional ℝ F]
    (hι : Fintype.card ι = finrank ℝ F) :
    IsQuotientCoveringMap (Pullback.lift (projection : VectorBundleOrientationCover F E ι → B) :
      TotalSpace F ((projection : VectorBundleOrientationCover F E ι → B) *ᵖ E) →
        TotalSpace F E) ℤˣ :=
  Pullback.isQuotientCoveringMap_lift (isQuotientCoveringMap_proj hι)
    (FiberBundle.continuous_proj F E) proj_smul_totalSpace lift_smul

section ThomPair

universe w

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type}

-- The zeros of the fibres of the pull-back are read as in `TauCeti.pullbackThomPairMap`, so that
-- the Thom pair of the pull-back below is the source of that map.
attribute [local instance] pullbackFiberZero

/-- The action `pullbackMulAction` of `ℤˣ`, on the total space of the Thom pair `(E', E'₀)` of the
bundle pulled back to the orientation double cover.

Like `pullbackMulAction`, it is not a global instance; the statements below use it as a local
instance. -/
abbrev thomPairFstMulAction :
    MulAction ℤˣ (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst :=
  pullbackMulAction

/-- The action `pullbackMulAction` of `ℤˣ` keeps the vector, so it preserves the nonzero vectors
`E'₀` of the bundle pulled back to the orientation double cover, the subspace of its Thom pair:
this is the restricted action.

Like `pullbackMulAction`, it is not a global instance; the statements below use it as a local
instance. -/
abbrev thomPairSndMulAction :
    MulAction ℤˣ (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd
    where
  smul u v := ⟨u • v.val, (preimage_pullbackLift_zeroSectionCompl _).subset <| by
    rw [Set.mem_preimage, lift_smul]
    exact (preimage_pullbackLift_zeroSectionCompl (F := F) (E := E) projection).superset v.property⟩
  one_smul v := Subtype.ext (one_smul ℤˣ v.val)
  mul_smul u u' v := Subtype.ext (mul_smul u u' v.val)

attribute [local instance] thomPairFstMulAction thomPairSndMulAction

/-- The action `thomPairSndMulAction` of `ℤˣ` on the nonzero vectors `E'₀` of the bundle pulled back
to the orientation double cover is the action `pullbackMulAction` on the underlying vectors. -/
@[simp]
theorem coe_thomPairSnd_smul (u : ℤˣ)
    (v : (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd) :
    (u • v).val = u • v.val :=
  (rfl)

/-- The embedding `E'₀ → E'` of the Thom pair of the bundle pulled back to the orientation double
cover commutes with the actions `thomPairSndMulAction` and `thomPairFstMulAction` of `ℤˣ`. -/
theorem thomPair_map_smul (u : ℤˣ)
    (v : (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd) :
    (thomPair F _).map (u • v) = u • (thomPair F _).map v := by
  rw [TopPair.ofSubset_map]
  exact coe_thomPairSnd_smul u v

/-- The projection `E' → B'` of the bundle pulled back to the orientation double cover commutes
with the action `thomPairFstMulAction` of `ℤˣ` on the total space of its Thom pair and the action
on the cover. -/
theorem thomPairProj_smul (u : ℤˣ)
    (v : (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst) :
    thomPairProj F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) (u • v) =
      u • thomPairProj F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E) v :=
  (thomPairProj_apply F _ (u • v)).trans
    ((proj_smul_totalSpace u v).trans (congrArg (u • ·) (thomPairProj_apply F _ v).symm))

/-- The action `thomPairFstMulAction` of `ℤˣ` on the total space `E'` of the Thom pair of the
bundle pulled back to the orientation double cover is continuous: it acts on the cover
continuously and keeps the vector of `E`.

Like `thomPairFstMulAction`, it is not a global instance; it is used as a local instance. -/
theorem continuousConstSMul_thomPairFst :
    ContinuousConstSMul ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst where
  continuous_const_smul u := Pullback.continuous_iff.2
    ⟨(continuous_const_smul u).comp (Pullback.continuous_proj F E _),
      Pullback.continuous_lift F E _⟩

attribute [local instance] continuousConstSMul_thomPairFst

/-- The action `thomPairSndMulAction` of `ℤˣ` on the nonzero vectors `E'₀` of the Thom pair of the
bundle pulled back to the orientation double cover is continuous, as the restriction of the
continuous action `continuousConstSMul_thomPairFst`.

Like `thomPairSndMulAction`, it is not a global instance. -/
theorem continuousConstSMul_thomPairSnd :
    ContinuousConstSMul ℤˣ
      (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).snd where
  continuous_const_smul u := ((continuous_const_smul u : Continuous fun x :
    (thomPair F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)).fst ↦
      u • x).comp continuous_subtypeVal).subtype_mk _

variable [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)

include hι

/-- **The Thom pair of the pulled-back bundle covers the Thom pair: total spaces.** If `ι` has
cardinality the rank of the bundle, the map of total spaces underlying the map of Thom pairs
`(E', E'₀) ⟶ (E, E₀)` from the bundle pulled back to the orientation double cover is the quotient
covering map of the action `thomPairFstMulAction` of `ℤˣ`. -/
theorem isQuotientCoveringMap_pullbackThomPairMap_fst :
    IsQuotientCoveringMap
      (TopPair.Hom.fst (pullbackThomPairMap F E (projection (F := F) (E := E) (ι := ι)))) ℤˣ := by
  rw [show ⇑(TopPair.Hom.fst (pullbackThomPairMap F E projection)) = Pullback.lift _ from
    funext (pullbackThomPairMap_fst_apply F E _)]
  exact isQuotientCoveringMap_lift (F := F) (E := E) hι

/-- **The Thom pair of the pulled-back bundle covers the Thom pair: nonzero vectors.** If `ι` has
cardinality the rank of the bundle, the map of nonzero vectors underlying the map of Thom pairs
`(E', E'₀) ⟶ (E, E₀)` from the bundle pulled back to the orientation double cover is the quotient
covering map of the action `thomPairSndMulAction` of `ℤˣ`. With
`isQuotientCoveringMap_pullbackThomPairMap_fst` and `thomPair_map_smul`, this presents the Thom pair
`(E, E₀)` as the quotient of the pair `(E', E'₀)` by a free action of `ℤˣ`. -/
theorem isQuotientCoveringMap_pullbackThomPairMap_snd :
    IsQuotientCoveringMap
      (TopPair.Hom.snd (pullbackThomPairMap F E (projection (F := F) (E := E) (ι := ι)))) ℤˣ := by
  -- `IsQuotientCoveringMap.restrict` asks for the action on the subtype of nonzero vectors, which
  -- `(thomPair F _).snd` unfolds to (`thomPair` is `TopPair.ofSubset` of `zeroSectionCompl`), so
  -- `thomPairSndMulAction` and its lemma `coe_thomPairSnd_smul` are used on that subtype.
  let : MulAction ℤˣ
      (zeroSectionCompl F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)) :=
    thomPairSndMulAction
  -- The nonzero vectors of the pull-back are the preimage of those of `E`, so the map they
  -- underlie is the restriction of `Pullback.lift`.
  have h : Set.MapsTo (Pullback.lift (projection : C(VectorBundleOrientationCover F E ι, B)))
      (zeroSectionCompl F (_ *ᵖ E)) (zeroSectionCompl F E) :=
    Set.mapsTo_iff_subset_preimage.2 (preimage_pullbackLift_zeroSectionCompl _).superset
  rw [show ⇑(TopPair.Hom.snd (pullbackThomPairMap F E projection)) = h.restrict _ _ _ from
    funext fun v ↦ Subtype.ext (pullbackThomPairMap_snd_apply F E _ v)]
  exact (isQuotientCoveringMap_lift (F := F) (E := E) hι).restrict coe_thomPairSnd_smul h
    (preimage_pullbackLift_zeroSectionCompl _).subset

end ThomPair

end VectorBundleOrientationCover

end TauCeti
