/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FiberBundle.Pullback
public import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# The orientation double cover as a quotient by `ℤˣ`

Let `E → B` be a real vector bundle with model fibre `F`, and let `ι` have cardinality the rank of
`E`. The units `ℤˣ = {1, -1}` act on the orientation double cover `B'` of `E`, with `-1` reversing
the orientation and fixing the base point, so that `-1` acts by the deck involution
(`TauCeti.VectorBundleOrientationCover.neg_one_smul_eq_deck`). The projection `B' → B` is then
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
free action of `ℤˣ` preserving `E'₀`.

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

/-- Each unit acts on the orientation double cover as the identity or as the deck involution. -/
private theorem smul_eq_or (u : ℤˣ) :
    (u • · : VectorBundleOrientationCover F E ι → _) = id ∨
      (u • · : VectorBundleOrientationCover F E ι → _) = deck := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact .inl (funext (one_smul ℤˣ))
  · exact .inr (funext neg_one_smul_eq_deck)

/-- **The orientation double cover is the quotient by its deck transformations.** If `ι` has
cardinality the rank of the bundle, the projection of the orientation double cover is the quotient
map of the action of `ℤˣ`, whose element `-1` acts by the deck involution: the fibres of the
projection are the orbits, and every point has a neighbourhood disjoint from its image under the
deck involution. -/
theorem isQuotientCoveringMap_proj [Fintype ι] [FiniteDimensional ℝ F]
    (hι : Fintype.card ι = finrank ℝ F) :
    IsQuotientCoveringMap (proj : VectorBundleOrientationCover F E ι → B) ℤˣ := by
  refine (isQuotientCoveringMap_iff_isCoveringMap_and _ ℤˣ).2
    ⟨isCoveringMap_proj hι, surjective_proj hι, ⟨fun u ↦ ?_⟩,
      isCancelSMul_iff_eq_one_of_smul_eq.2 fun u p h ↦ ?_, fun {p q} ↦ ⟨fun h ↦ ?_, ?_⟩⟩
  · rcases smul_eq_or (F := F) (E := E) (ι := ι) u with h | h <;> rw [h]
    exacts [continuous_id, deck.continuous]
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

variable [Fintype ι] [FiniteDimensional ℝ F]

/-- The orientation cover modulo its deck action is the original base. -/
noncomputable abbrev orbitQuotientHomeomorph (hι : Fintype.card ι = finrank ℝ F) :
    MulAction.orbitRel.Quotient ℤˣ (VectorBundleOrientationCover F E ι) ≃ₜ B :=
  (Homeomorph.Quotient.congrRight
    (r' := Setoid.ker (proj : VectorBundleOrientationCover F E ι → B))
    (fun _ _ ↦ MulAction.orbitRel_apply.trans
      (isQuotientCoveringMap_proj hι).apply_eq_iff_mem_orbit.symm)).trans
    (IsQuotientMap.homeomorph
      (f := ⟨proj, (isQuotientCoveringMap_proj hι).toIsQuotientMap.continuous⟩)
      (isQuotientCoveringMap_proj hι).toIsQuotientMap)

@[simp]
theorem orbitQuotientHomeomorph_mk (hι : Fintype.card ι = finrank ℝ F)
    (p : VectorBundleOrientationCover F E ι) :
    orbitQuotientHomeomorph hι (Quotient.mk _ p) = p.proj :=
  rfl

@[simp]
theorem orbitQuotientHomeomorph_symm_proj (hι : Fintype.card ι = finrank ℝ F)
    (p : VectorBundleOrientationCover F E ι) :
    (orbitQuotientHomeomorph hι).symm p.proj = Quotient.mk _ p :=
  (orbitQuotientHomeomorph hι).symm_apply_eq.2 (orbitQuotientHomeomorph_mk hι p).symm

end VectorBundleOrientationCover

end TauCeti
