/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# The faces of a regular cone are indexed by subsets of its rays

A regular cone is the cone hull of the images of its primitive ray generators, and those images
are part of a real basis of the ambient space. The faces of such a cone are therefore exactly the
cones spanned by subfamilies of the primitive ray generators, and the assignment is an order
isomorphism between Mathlib's face lattice of the cone and the powerset of its ray type.

Under this isomorphism a face corresponds to the set of its own rays, so a face of a regular cone
is determined by, and can be prescribed by, the rays of the ambient cone that it contains. This is
the combinatorial input of the orbit description of an affine toric chart: the rays of a regular
cone index the coordinates of the mixed chart, a face is cut out by demanding that the
coordinates of its rays vanish, and the face lattice must match the lattice of such coordinate
conditions.

Regularity is used only through simpliciality, and simpliciality cannot be dropped: the cone over
a square in `ℝ³`, spanned by `(1, 0, 1)`, `(0, 1, 1)`, `(-1, 0, 1)` and `(0, -1, 1)`, is salient
with four rays, but the cone spanned by two opposite rays is not a face, so its ten faces do not
exhaust the sixteen subsets of its rays.

## Main declarations

* `TauCeti.Toric.IsRegularCone.faceOrderIso`: the face lattice of a regular cone is the lattice
  of subsets of its rays.
* `TauCeti.Toric.IsRegularCone.faceOrderIso_apply`: the subset attached to a face is the set of
  rays of that face; for a ray, `TauCeti.Toric.IsRegularCone.faceOrderIso_toricRay`, it is that
  ray alone.
* `TauCeti.Toric.IsRegularCone.faceOrderIso_symm_apply_toPointedCone`: the face attached to a
  subset of rays is the cone spanned by the corresponding primitive ray generators.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2 and Proposition 1.2.10.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

private noncomputable def toricRayEquivOfLinearIndependent
    {C : PointedCone ℝ V} {ι : Type*} [Finite ι] (v : ι → V)
    (hv : LinearIndependent ℝ v) (hcone : C = PointedCone.hull ℝ (Set.range v)) :
    ToricRay C ≃ ι := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let e := PointedCone.faceOrderIsoSet hv hcone
  have hdim (G : C.Face) :
      Module.finrank ℝ (Submodule.span ℝ (G.toPointedCone : Set V)) =
        Nat.card {a : ι // a ∈ e G} :=
    finrank_span_face_eq_card_faceOrderIsoSet v hv hcone G
  let f : ToricRay C → ι := fun ρ ↦
    (Classical.choose (Nat.card_eq_one_iff_exists.mp ((hdim ρ.1).symm.trans ρ.2))).1
  have hf (ρ : ToricRay C) : e ρ.1 = {f ρ} := by
    let h := Nat.card_eq_one_iff_exists.mp ((hdim ρ.1).symm.trans ρ.2)
    ext a
    constructor
    · intro ha
      exact congrArg Subtype.val (Classical.choose_spec h ⟨a, ha⟩)
    · intro ha
      subst a
      exact (Classical.choose h).2
  have hfinj : Function.Injective f := by
    intro ρ ν h
    apply Subtype.ext
    exact e.injective (by rw [hf ρ, hf ν, h])
  have hfsurj : Function.Surjective f := by
    intro a
    let G := e.symm {a}
    have hG : Module.finrank ℝ (Submodule.span ℝ (G.toPointedCone : Set V)) = 1 := by
      rw [hdim, e.apply_symm_apply]
      simp
    let ρ : ToricRay C := ⟨G, hG⟩
    refine ⟨ρ, ?_⟩
    have h : e G = {f ρ} := by simpa only [ρ, Subtype.coe_mk] using hf ρ
    rw [e.apply_symm_apply] at h
    exact Set.singleton_injective h.symm
  exact Equiv.ofBijective f ⟨hfinj, hfsurj⟩

/-- The real dimension of a face of a simplicial cone is its number of rays. -/
theorem finrank_span_face_eq_card_rays_of_isSimplicial (hσ : σ.IsSimplicial) (F : σ.Face) :
    Module.finrank ℝ (Submodule.span ℝ (F.toPointedCone : Set V)) =
      Nat.card (ToricRay F.toPointedCone) := by
  obtain ⟨s, hs, hli, hsσ⟩ := hσ
  have hF : F.toPointedCone.IsSimplicial := by
    refine ⟨s ∩ (F : Set V), hs.inter_of_left _, hli.mono Set.inter_subset_left, ?_⟩
    exact (F.eq_hull_inter_of_eq_hull s hsσ.symm).symm
  obtain ⟨t, ht, hlt, htF⟩ := hF
  let v : t → V := Subtype.val
  have hv : LinearIndependent ℝ v := linearIndependent_subtype_iff.mpr hlt
  have hcone : F.toPointedCone = PointedCone.hull ℝ (Set.range v) := by
    have hrange : Set.range v = t := by ext x; simp [v]
    rw [hrange]
    exact htF.symm
  let e : F.toPointedCone.Face ≃o Set t := PointedCone.faceOrderIsoSet hv hcone
  classical
  let _ : Fintype t := ht.fintype
  have hdim (G : F.toPointedCone.Face) :
      Module.finrank ℝ (Submodule.span ℝ (G.toPointedCone : Set V)) =
        Nat.card {a : t // a ∈ e G} :=
    finrank_span_face_eq_card_faceOrderIsoSet v hv hcone G
  rw [hdim ⟨F.toPointedCone, PointedCone.IsFaceOf.refl _⟩]
  have he : e ⟨F.toPointedCone, PointedCone.IsFaceOf.refl _⟩ = Set.univ := by
    ext a
    simp only [e, PointedCone.faceOrderIsoSet_apply, Set.mem_univ, iff_true]
    rw [hcone]
    exact PointedCone.subset_hull ⟨a, rfl⟩
  rw [he]
  simpa using (Nat.card_congr (toricRayEquivOfLinearIndependent v hv hcone)).symm

namespace IsRegularCone

variable (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)

/-- The face lattice of a regular cone is the lattice of subsets of its rays: a face is recorded
by the set of rays it contains, and a set of rays spans the corresponding face. -/
noncomputable def faceOrderIso : σ.Face ≃o Set (ToricRay σ) :=
  PointedCone.faceOrderIsoSet (hσ.linearIndependent_primitiveGenerator hi) <| by
    have h : (Set.range fun ρ : ToricRay σ ↦ i (primitiveGenerator hi hσ.toIsToricCone ρ)) =
        i '' Set.range (primitiveGenerator hi hσ.toIsToricCone) := Set.range_comp _ _
    rw [h]
    exact (hσ.toIsToricCone.hull_primitiveGenerator hi).symm

/-- A ray of a regular cone lies in the subset attached to a face exactly when the image of its
primitive generator lies in that face. This is not a `simp` lemma: `faceOrderIso_apply` rewrites
the left-hand side, whose `simp` normal form is containment of the ray in the face. -/
theorem mem_faceOrderIso_iff (F : σ.Face) (ρ : ToricRay σ) :
    ρ ∈ faceOrderIso hi hσ F ↔ i (primitiveGenerator hi hσ.toIsToricCone ρ) ∈ F := by
  rw [faceOrderIso, PointedCone.faceOrderIsoSet_apply]
  exact Iff.rfl

/-- The face of a regular cone attached to a subset of its rays is the cone spanned by the images
of the primitive generators of those rays. -/
@[simp]
theorem faceOrderIso_symm_apply_toPointedCone (A : Set (ToricRay σ)) :
    ((faceOrderIso hi hσ).symm A).toPointedCone =
      PointedCone.hull ℝ (i '' (primitiveGenerator hi hσ.toIsToricCone '' A)) := by
  rw [faceOrderIso, PointedCone.faceOrderIsoSet_symm_apply_toPointedCone, Set.image_image]

/-- The subset of rays attached to a face of a regular cone is the set of rays of that face. -/
@[simp]
theorem faceOrderIso_apply (F : σ.Face) :
    faceOrderIso hi hσ F = Set.range (ToricRay.faceEmbedding F.isFaceOf) := by
  rw [ToricRay.range_faceEmbedding]
  ext ρ
  rw [mem_faceOrderIso_iff, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ h (primitiveGenerator_mem hi hσ.toIsToricCone ρ)⟩
  rw [ρ.eq_hull_singleton (hσ.salient.anti ρ.1.isFaceOf.le)
    (primitiveGenerator_mem hi hσ.toIsToricCone ρ)
    (by simpa using hi.injective.ne (primitiveGenerator_ne_zero hi hσ.toIsToricCone ρ))]
  exact Submodule.span_le.2 (Set.singleton_subset_iff.2 h)

/-- A ray of a regular cone, viewed as a face, contains no other ray. This is not a `simp` lemma:
`faceOrderIso_apply` rewrites its left-hand side. -/
theorem faceOrderIso_toricRay (ρ : ToricRay σ) : faceOrderIso hi hσ ρ.1 = {ρ} := by
  ext ν
  rw [faceOrderIso_apply, ToricRay.range_faceEmbedding, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ToricRay.toPointedCone_le_toPointedCone_iff hσ.salient

/-- The real dimension of a face of a regular cone is the number of rays it contains. -/
theorem finrank_span_face_eq_card_rays (F : σ.Face) :
    Module.finrank ℝ (Submodule.span ℝ (F.toPointedCone : Set V)) =
      Nat.card {ρ : ToricRay σ // ρ ∈ hσ.faceOrderIso hi F} := by
  rw [finrank_span_face_eq_card_rays_of_isSimplicial (hσ.isSimplicial hi) F,
    hσ.faceOrderIso_apply hi F]
  let e : ToricRay F.toPointedCone ≃
      {ρ : ToricRay σ // ρ ∈ Set.range (ToricRay.faceEmbedding F.isFaceOf)} :=
    Equiv.ofBijective
      (fun ρ ↦ ⟨ToricRay.faceEmbedding F.isFaceOf ρ, Set.mem_range_self ρ⟩) <| by
        constructor
        · intro ρ ν h
          exact (ToricRay.faceEmbedding F.isFaceOf).injective (congrArg Subtype.val h)
        · rintro ⟨ρ, ν, rfl⟩
          exact ⟨ν, rfl⟩
  exact Nat.card_congr e

end IsRegularCone

end TauCeti.Toric
