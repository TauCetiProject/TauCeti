/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution.Unbounded.Basic

/-!
# The unbounded projective horseshoe

Given a conflation and prescribed projective resolutions of its two ends, construct a projective
resolution of the middle object and augmentation-compatible chain maps forming a degreewise
split short complex. No enough-projectives assumption is needed: the prescribed resolutions
already provide all the required covers.

The construction iterates `ExactStructure.exists_conflation_biprod_of_conflation_of_projective`.
The successive syzygies form conflations, while each middle resolving term is the biproduct of
the prescribed outer terms. This applies to graded exact categories as well: conflation-exact
functors preserving relative projectives transport the resulting horseshoe, including the
internal grading shift and its inverse. The chain-map and transport API follows
`ExactStructure.FiniteResolution.Horseshoe`; the iteration here retains infinitely many
syzygies rather than recursing on finite lengths.

## References

* Theo Bühler, *Exact categories*, Section 12.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Lemma 2.2.8.
-/

public section

namespace TauCeti.ExactStructure.ProjectiveResolution

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C}
  {S : ShortComplex C} (r₁ : E.ProjectiveResolution S.X₁) (r₃ : E.ProjectiveResolution S.X₃)

/-- A projective horseshoe over a short complex: a middle resolution and compatible chain maps,
with a split short complex in every degree. -/
structure Horseshoe where
  /-- The projective resolution of the middle object. -/
  resolution : E.ProjectiveResolution S.X₂
  /-- The chain map lifting the first map of the short complex. -/
  ι : r₁.toChainComplex ⟶ resolution.toChainComplex
  /-- The chain map lifting the second map of the short complex. -/
  π : resolution.toChainComplex ⟶ r₃.toChainComplex
  /-- The chain maps have zero composite. -/
  zero : ι ≫ π = 0
  /-- The injection commutes with the augmentations. -/
  ι_aug : ι.f 0 ≫ resolution.aug = r₁.aug ≫ S.f
  /-- The projection commutes with the augmentations. -/
  π_aug : π.f 0 ≫ r₃.aug = resolution.aug ≫ S.g
  /-- The induced short complex splits in each degree. -/
  split (n : ℕ) : Nonempty (ShortComplex.mk (ι.f n) (π.f n)
    (by exact congrArg (fun f => f.f n) zero)).Splitting

attribute [reassoc (attr := simp)] Horseshoe.zero Horseshoe.ι_aug Horseshoe.π_aug

/-- A conflation between the prescribed syzygies in one degree. -/
private structure Frame (n : ℕ) where
  Y : C
  f : r₁.K n ⟶ Y
  g : Y ⟶ r₃.K n
  zero : f ≫ g = 0
  conflation : E.Conflation (ShortComplex.mk f g zero)

/-- The one-step horseshoe, retaining the four squares needed when splicing. -/
private structure Advance {n : ℕ} (t : Frame r₁ r₃ n) where
  next : Frame r₁ r₃ (n + 1)
  i : next.Y ⟶ r₁.X n ⊞ r₃.X n
  p : r₁.X n ⊞ r₃.X n ⟶ t.Y
  zero : i ≫ p = 0
  conflation : E.Conflation (ShortComplex.mk i p zero)
  left_p : biprod.inl ≫ p = r₁.π n ≫ t.f
  right_p : p ≫ t.g = biprod.snd ≫ r₃.π n
  left_i : next.f ≫ i = r₁.ι n ≫ biprod.inl
  right_i : i ≫ biprod.snd = next.g ≫ r₃.ι n

private noncomputable def advance {n : ℕ} (t : Frame r₁ r₃ n) : Advance r₁ r₃ t :=
  Classical.choice (by
    obtain ⟨K, i, p, z, f, g, z', hc, hc', hp₁, hp₃, hi₁, hi₃⟩ :=
      E.exists_conflation_biprod_of_conflation_of_projective t.conflation
        (r₁.conflation n) (r₃.conflation n) (r₃.isProjective n)
    exact ⟨⟨⟨K, f, g, z', hc'⟩, i, p, z, hc, hp₁, hp₃, hi₁, hi₃⟩⟩)

/-- Replace the end objects by the specified zeroth syzygies. -/
private abbrev initial (hS : E.Conflation S) : Frame r₁ r₃ 0 where
  Y := S.X₂
  f := r₁.iso.hom ≫ S.f
  g := S.g ≫ r₃.iso.inv
  zero := by simp
  conflation := E.conflation_of_iso
    (ShortComplex.isoMk r₁.iso.symm (Iso.refl _) r₃.iso.symm (by simp) (by simp)) hS

/-- Recursion retains all syzygies at once, so no finite truncation or limiting argument enters. -/
private noncomputable abbrev frames (hS : E.Conflation S) : (n : ℕ) → Frame r₁ r₃ n :=
  Nat.rec (initial r₁ r₃ hS) (fun _ t => (advance r₁ r₃ t).next)

private noncomputable def middle (hS : E.Conflation S) : E.ProjectiveResolution S.X₂ where
  K n := (frames r₁ r₃ hS n).Y
  X n := r₁.X n ⊞ r₃.X n
  iso := Iso.refl _
  ι n := (advance r₁ r₃ (frames r₁ r₃ hS n)).i
  π n := (advance r₁ r₃ (frames r₁ r₃ hS n)).p
  zero n := (advance r₁ r₃ (frames r₁ r₃ hS n)).zero
  conflation n := (advance r₁ r₃ (frames r₁ r₃ hS n)).conflation
  isProjective n := E.isProjective_biprod (r₁.isProjective n) (r₃.isProjective n)

private lemma middle_d_inl (hS : E.Conflation S) (n : ℕ) :
    biprod.inl ≫ (middle r₁ r₃ hS).d n = r₁.d n ≫ biprod.inl := by
  rw [d_def, d_def]
  dsimp [middle]
  rw [← Category.assoc, (advance r₁ r₃ (frames r₁ r₃ hS (n + 1))).left_p,
    Category.assoc, (advance r₁ r₃ (frames r₁ r₃ hS n)).left_i]
  simp only [Category.assoc]

private lemma middle_d_snd (hS : E.Conflation S) (n : ℕ) :
    (middle r₁ r₃ hS).d n ≫ biprod.snd = biprod.snd ≫ r₃.d n := by
  rw [d_def, d_def]
  dsimp [middle]
  rw [Category.assoc, (advance r₁ r₃ (frames r₁ r₃ hS n)).right_i,
    ← Category.assoc, (advance r₁ r₃ (frames r₁ r₃ hS (n + 1))).right_p]
  simp only [Category.assoc]

/-- **The unbounded projective horseshoe lemma.** The prescribed outer resolutions of a
conflation admit an augmentation-compatible, degreewise split horseshoe. The construction
works in an arbitrary additive exact category, without ambient kernels or cokernels. -/
noncomputable def horseshoe (hS : E.Conflation S) : Horseshoe r₁ r₃ where
  resolution := middle r₁ r₃ hS
  ι := ChainComplex.ofHom (fun _ => biprod.inl) (by
    intro n
    rw [toChainComplex_d, toChainComplex_d]
    exact middle_d_inl r₁ r₃ hS n)
  π := ChainComplex.ofHom (fun _ => biprod.snd) (by
    intro n
    rw [toChainComplex_d, toChainComplex_d]
    exact (middle_d_snd r₁ r₃ hS n).symm)
  zero := by ext n; exact biprod.inl_snd
  ι_aug := by
    rw [aug_def, aug_def]
    dsimp [middle]
    simpa using (advance r₁ r₃ (frames r₁ r₃ hS 0)).left_p
  π_aug := by
    rw [aug_def, aug_def]
    dsimp [middle]
    have h := (advance r₁ r₃ (frames r₁ r₃ hS 0)).right_p =≫ r₃.iso.hom
    simpa using h.symm
  split n := ⟨ShortComplex.Splitting.ofHasBinaryBiproduct _ _⟩

namespace Horseshoe

variable {r₁ r₃} (h : Horseshoe r₁ r₃)

/-- Each middle term is a biproduct of the prescribed outer terms, compatibly with the
horseshoe injection and projection. -/
noncomputable def termIsoBiprod (n : ℕ) : h.resolution.X n ≅ r₁.X n ⊞ r₃.X n :=
  (h.split n).some.isoBinaryBiproduct

@[reassoc (attr := simp)]
lemma ι_f_termIsoBiprod_hom (n : ℕ) : h.ι.f n ≫ (h.termIsoBiprod n).hom = biprod.inl := by
  apply biprod.hom_ext
  · simp [termIsoBiprod, (h.split n).some.f_r]
  · simp only [termIsoBiprod, ShortComplex.Splitting.isoBinaryBiproduct_hom,
      Category.assoc, biprod.lift_snd, biprod.inl_snd]
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      congrArg (fun f => f.f n) h.zero

@[reassoc (attr := simp)]
lemma termIsoBiprod_hom_snd (n : ℕ) : (h.termIsoBiprod n).hom ≫ biprod.snd = h.π.f n := by
  simp [termIsoBiprod]

section Map

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F) (hproj : E.isProjective ≤ E'.isProjective.inverseImage F)

/-- Transport a horseshoe along a conflation-exact functor preserving relative projectives.
This applies in particular to the internal shift and its inverse in a graded exact category. -/
noncomputable def map : Horseshoe (S := S.map F) (r₁.map hF hproj) (r₃.map hF hproj) where
  resolution := h.resolution.map hF hproj
  ι := (r₁.toChainComplexMapIso hF hproj).hom ≫
    (F.mapHomologicalComplex _).map h.ι ≫ (h.resolution.toChainComplexMapIso hF hproj).inv
  π := (h.resolution.toChainComplexMapIso hF hproj).hom ≫
    (F.mapHomologicalComplex _).map h.π ≫ (r₃.toChainComplexMapIso hF hproj).inv
  zero := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc, h.zero]
    simp
  ι_aug := by
    simp only [HomologicalComplex.comp_f, toChainComplexMapIso_hom_f,
      toChainComplexMapIso_inv_f, Functor.mapHomologicalComplex_map_f, map_aug,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp, h.ι_aug, F.map_comp]
    rfl
  π_aug := by
    simp only [HomologicalComplex.comp_f, toChainComplexMapIso_hom_f,
      toChainComplexMapIso_inv_f, Functor.mapHomologicalComplex_map_f, map_aug,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp, h.π_aug, F.map_comp]
    rfl
  split n := by
    let t := (h.split n).some.map F
    refine ⟨t.ofIso (ShortComplex.isoMk (r₁.mapXIso hF hproj n).symm
      (h.resolution.mapXIso hF hproj n).symm (r₃.mapXIso hF hproj n).symm ?_ ?_)⟩
    · simp
    · simp

/-- The resolution of a transported horseshoe is the transported resolution. -/
@[simp] lemma map_resolution : (h.map hF hproj).resolution = h.resolution.map hF hproj := (rfl)

/-- The transported injection is the functor's image of the injection, under the canonical
complex comparisons. -/
@[simp] lemma map_ι : (h.map hF hproj).ι =
    (r₁.toChainComplexMapIso hF hproj).hom ≫
      (F.mapHomologicalComplex _).map h.ι ≫ (h.resolution.toChainComplexMapIso hF hproj).inv ≫
        eqToHom (congrArg toChainComplex (h.map_resolution hF hproj).symm) := by
  -- The middle-resolution transport is an identity; `simp` does not unfold its proof.
  change _ = (r₁.toChainComplexMapIso hF hproj).hom ≫
    (F.mapHomologicalComplex _).map h.ι ≫ (h.resolution.toChainComplexMapIso hF hproj).inv ≫ 𝟙 _
  simp only [Category.comp_id]
  rfl

/-- The transported projection is the functor's image of the projection, under the canonical
complex comparisons. -/
@[simp] lemma map_π : (h.map hF hproj).π =
    eqToHom (congrArg toChainComplex (h.map_resolution hF hproj)) ≫
      (h.resolution.toChainComplexMapIso hF hproj).hom ≫
        (F.mapHomologicalComplex _).map h.π ≫ (r₃.toChainComplexMapIso hF hproj).inv := by
  -- The middle-resolution transport is an identity; `simp` does not unfold its proof.
  change _ = (𝟙 _) ≫ (h.resolution.toChainComplexMapIso hF hproj).hom ≫
    (F.mapHomologicalComplex _).map h.π ≫ (r₃.toChainComplexMapIso hF hproj).inv
  simp only [Category.id_comp]
  rfl

end Map

end Horseshoe

end TauCeti.ExactStructure.ProjectiveResolution
