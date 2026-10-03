/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Resolution.ChainComplex
public import TauCeti.CategoryTheory.Exact.Projective

/-!
# The horseshoe of finite projective resolutions

For a conflation `X ↪ Y ↠ Z` and finite resolutions of `X` and `Z` by relative projectives,
construct a finite projective resolution of `Y` and compatible chain maps. In each degree the
resulting short complex splits, so the middle term is the biproduct of the two prescribed outer
terms. Its length is at most the maximum of the two outer lengths.

The construction iterates the one-step horseshoe lemma for conflations, retaining the maps
between successive syzygies. No ambient kernels, cokernels, or enough-projectives hypothesis is
needed. In a graded exact category the same construction applies to graded objects and
morphisms; the shift and every conflation-exact functor preserving projectives transport the
resulting horseshoe.

## References

* Theo Bühler, *Exact categories*, Section 12, for the horseshoe lemma in exact categories.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Lemma 2.2.8.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure.FiniteResolution

variable {E : ExactStructure C}

/-- A horseshoe over a conflation, with prescribed finite projective resolutions of its outer
terms: a middle resolution, augmentation-compatible chain maps, and degreewise split exactness.
The middle resolution is no longer than the longer of the prescribed resolutions. -/
structure Horseshoe (S : ShortComplex C) (r₁ : E.FiniteResolution E.isProjective S.X₁)
    (r₃ : E.FiniteResolution E.isProjective S.X₃) where
  /-- The finite projective resolution of the middle object. -/
  resolution : E.FiniteResolution E.isProjective S.X₂
  /-- The chain map lifting the inflation of the conflation. -/
  ι : r₁.toChainComplex ⟶ resolution.toChainComplex
  /-- The chain map lifting the deflation of the conflation. -/
  π : resolution.toChainComplex ⟶ r₃.toChainComplex
  /-- The two chain maps have zero composite. -/
  zero : ι ≫ π = 0
  /-- The left chain map commutes with the augmentations. -/
  ι_aug : ι.f 0 ≫ resolution.aug = r₁.aug ≫ S.f
  /-- The right chain map commutes with the augmentations. -/
  π_aug : π.f 0 ≫ r₃.aug = resolution.aug ≫ S.g
  /-- The induced short complex in each degree splits. -/
  split (n : ℕ) : Nonempty (ShortComplex.mk (ι.f n) (π.f n)
    (by exact congrArg (fun f => f.f n) zero)).Splitting
  /-- The bound on the length of the middle resolution. -/
  length_le : resolution.length ≤ max r₁.length r₃.length

attribute [reassoc (attr := simp)] Horseshoe.zero Horseshoe.ι_aug Horseshoe.π_aug

/-- Component data used only to assemble the chain maps of the horseshoe. -/
private structure Data (S : ShortComplex C) (r₁ : E.FiniteResolution E.isProjective S.X₁)
    (r₃ : E.FiniteResolution E.isProjective S.X₃) where
  resolution : E.FiniteResolution E.isProjective S.X₂
  left (n : ℕ) : r₁.term n ⟶ resolution.term n
  right (n : ℕ) : resolution.term n ⟶ r₃.term n
  left_comm (n : ℕ) : left (n + 1) ≫ resolution.d n = r₁.d n ≫ left n
  right_comm (n : ℕ) : right (n + 1) ≫ r₃.d n = resolution.d n ≫ right n
  zero (n : ℕ) : left n ≫ right n = 0
  left_aug : left 0 ≫ resolution.aug = r₁.aug ≫ S.f
  right_aug : right 0 ≫ r₃.aug = resolution.aug ≫ S.g
  split (n : ℕ) : Nonempty (ShortComplex.mk (left n) (right n) (zero n)).Splitting
  length_le : resolution.length ≤ max r₁.length r₃.length

/-- Assemble component data into the chain maps of a horseshoe. -/
private noncomputable def Data.toHorseshoe {S : ShortComplex C}
    {r₁ : E.FiniteResolution E.isProjective S.X₁} {r₃ : E.FiniteResolution E.isProjective S.X₃}
    (h : Data S r₁ r₃) : Horseshoe S r₁ r₃ where
  resolution := h.resolution
  ι := ChainComplex.ofHom h.left (by simpa using h.left_comm)
  π := ChainComplex.ofHom h.right (by simpa using h.right_comm)
  zero := by ext n; exact h.zero n
  ι_aug := h.left_aug
  π_aug := h.right_aug
  split := h.split
  length_le := h.length_le

/-- Iterate the one-step horseshoe, keeping the syzygy maps so that the component maps commute
with the spliced differentials. A length-zero outer resolution is continued by the trivial
conflation `0 ↪ X ↠ X`; no length is added to the result when both resolutions have ended. -/
private theorem horseshoeData :
    ∀ {S : ShortComplex C}, E.Conflation S →
      (r₁ : E.FiniteResolution E.isProjective S.X₁) →
      (r₃ : E.FiniteResolution E.isProjective S.X₃) → Nonempty (Data S r₁ r₃)
  | S, hS, .base h₁, .base h₃ =>
      ⟨{
        resolution := .base ((E.isExtensionClosed_of_le_isProjective le_rfl).prop_X₂ hS h₁ h₃)
        left := fun n => match n with | 0 => S.f | _ + 1 => 0
        right := fun n => match n with | 0 => S.g | _ + 1 => 0
        left_comm := fun n => by cases n <;> simp
        right_comm := fun n => by cases n <;> simp
        zero := fun n => by cases n <;> simp [S.zero]
        left_aug := by simp
        right_aug := by simp
        split := fun n => match n with
          | 0 => ⟨E.splittingOfProjective hS h₃⟩
          | _ + 1 => ⟨{ r := 0, s := 0
                        f_r := (isZero_zero C).eq_of_src _ _
                        s_g := (isZero_zero C).eq_of_src _ _
                        id := (isZero_zero C).eq_of_src _ _ }⟩
        length_le := by simp }⟩
  | S, hS, .base h₁, .step hQ₃ i₃ p₃ z₃ hc₃ r₃ => by
      -- The left resolution has ended; its remaining syzygy and all higher maps are zero.
      obtain ⟨K, u, a, zu, v, w, zv, hc, hK, ha₁, ha₃, hu₁, hu₃⟩ :=
        E.exists_conflation_biprod_of_conflation_of_projective hS
          (E.conflation_zero_id S.X₁) hc₃ hQ₃
      obtain ⟨h⟩ := horseshoeData hK (.base (E.isProjective.prop_zero)) r₃
      refine
        ⟨{
          resolution := .step (E.isProjective_biprod h₁ hQ₃) u a zu hc h.resolution
          left := fun n => match n with | 0 => biprod.inl | _ + 1 => 0
          right := fun n => match n with | 0 => biprod.snd | n + 1 => h.right n
          left_comm := ?_
          right_comm := ?_
          zero := ?_
          left_aug := by simpa using ha₁
          right_aug := by simpa using ha₃.symm
          split := ?_
          length_le := ?_ }⟩
      · intro n; cases n <;> simp
      · intro n
        cases n with
        | zero => simp [reassoc_of% h.right_aug, hu₃]
        | succ n => simpa using h.right_comm n
      · intro n; cases n <;> simp
      · intro n
        cases n with
        | zero => exact ⟨ShortComplex.Splitting.ofHasBinaryBiproduct _ _⟩
        | succ n =>
            have hz : h.left n = 0 := by
              cases n <;> exact (isZero_zero C).eq_of_src _ _
            cases n with
            | zero => simpa only [hz] using h.split 0
            | succ n => simpa only [hz] using h.split (n + 1)
      · have := h.length_le
        simp only [length_step, length_base] at *
        omega
  | S, hS, .step hQ₁ i₁ p₁ z₁ hc₁ r₁, .base h₃ => by
      -- Dually, continue the right resolution by zero while resolving the left syzygy.
      obtain ⟨K, u, a, zu, v, w, zv, hc, hK, ha₁, ha₃, hu₁, hu₃⟩ :=
        E.exists_conflation_biprod_of_conflation_of_projective hS hc₁
          (E.conflation_zero_id S.X₃) h₃
      obtain ⟨h⟩ := horseshoeData hK r₁ (.base (E.isProjective.prop_zero))
      refine
        ⟨{
          resolution := .step (E.isProjective_biprod hQ₁ h₃) u a zu hc h.resolution
          left := fun n => match n with | 0 => biprod.inl | n + 1 => h.left n
          right := fun n => match n with | 0 => biprod.snd | _ + 1 => 0
          left_comm := ?_
          right_comm := ?_
          zero := ?_
          left_aug := by simpa using ha₁
          right_aug := by simpa using ha₃.symm
          split := ?_
          length_le := ?_ }⟩
      · intro n
        cases n with
        | zero => simp [reassoc_of% h.left_aug, hu₁]
        | succ n => simpa using h.left_comm n
      · intro n; cases n <;> simp [hu₃]
      · intro n; cases n <;> simp
      · intro n
        cases n with
        | zero => exact ⟨ShortComplex.Splitting.ofHasBinaryBiproduct _ _⟩
        | succ n =>
            have hz : h.right n = 0 := by
              cases n <;> exact (isZero_zero C).eq_of_tgt _ _
            cases n with
            | zero => simpa only [hz] using h.split 0
            | succ n => simpa only [hz] using h.split (n + 1)
      · have := h.length_le
        simp only [length_step, length_base] at *
        omega
  | S, hS, .step hQ₁ i₁ p₁ z₁ hc₁ r₁, .step hQ₃ i₃ p₃ z₃ hc₃ r₃ => by
      -- Resolve the syzygy conflation recursively, then prepend the biproduct of the covers.
      obtain ⟨K, u, a, zu, v, w, zv, hc, hK, ha₁, ha₃, hu₁, hu₃⟩ :=
        E.exists_conflation_biprod_of_conflation_of_projective hS hc₁ hc₃ hQ₃
      obtain ⟨h⟩ := horseshoeData hK r₁ r₃
      refine
        ⟨{
          resolution := .step (E.isProjective_biprod hQ₁ hQ₃) u a zu hc h.resolution
          left := fun n => match n with | 0 => biprod.inl | n + 1 => h.left n
          right := fun n => match n with | 0 => biprod.snd | n + 1 => h.right n
          left_comm := ?_
          right_comm := ?_
          zero := ?_
          left_aug := by simpa using ha₁
          right_aug := by simpa using ha₃.symm
          split := ?_
          length_le := ?_ }⟩
      · intro n
        cases n with
        | zero => simp [reassoc_of% h.left_aug, hu₁]
        | succ n => simpa using h.left_comm n
      · intro n
        cases n with
        | zero => simp [reassoc_of% h.right_aug, hu₃]
        | succ n => simpa using h.right_comm n
      · intro n
        cases n with
        | zero => simp
        | succ n => exact h.zero n
      · intro n
        cases n with
        | zero => exact ⟨ShortComplex.Splitting.ofHasBinaryBiproduct _ _⟩
        | succ n => exact h.split n
      · have := h.length_le
        simp only [length_step] at *
        omega
termination_by _ _ r₁ r₃ => r₁.length + r₃.length

/-- **The finite projective horseshoe lemma.** A conflation and finite projective resolutions of
its outer terms admit an augmentation-compatible, degreewise split horseshoe whose middle
resolution has length at most the maximum of the outer lengths. -/
noncomputable def horseshoe {S : ShortComplex C} (hS : E.Conflation S)
    (r₁ : E.FiniteResolution E.isProjective S.X₁)
    (r₃ : E.FiniteResolution E.isProjective S.X₃) : Horseshoe S r₁ r₃ :=
  (horseshoeData hS r₁ r₃).some.toHorseshoe

namespace Horseshoe

variable {S : ShortComplex C} {r₁ : E.FiniteResolution E.isProjective S.X₁}
  {r₃ : E.FiniteResolution E.isProjective S.X₃} (h : Horseshoe S r₁ r₃)

/-- Each middle term of a horseshoe is isomorphic to the biproduct of the prescribed outer
terms. The isomorphism is compatible with the injection and projection, through the standard
splitting API. -/
noncomputable def termIsoBiprod (n : ℕ) :
    h.resolution.term n ≅ r₁.term n ⊞ r₃.term n :=
  (h.split n).some.isoBinaryBiproduct

/-- The termwise biproduct isomorphism sends the horseshoe injection to the left inclusion. -/
@[reassoc (attr := simp)]
theorem ι_f_termIsoBiprod_hom (n : ℕ) :
    h.ι.f n ≫ (h.termIsoBiprod n).hom = biprod.inl := by
  apply biprod.hom_ext
  · simp [termIsoBiprod, (h.split n).some.f_r]
  · simp only [termIsoBiprod, ShortComplex.Splitting.isoBinaryBiproduct_hom,
      Category.assoc, biprod.lift_snd, biprod.inl_snd]
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      congrArg (fun f => f.f n) h.zero

/-- The right projection after the termwise biproduct isomorphism is the horseshoe projection. -/
@[reassoc (attr := simp)]
theorem termIsoBiprod_hom_snd (n : ℕ) :
    (h.termIsoBiprod n).hom ≫ biprod.snd = h.π.f n := by
  simp [termIsoBiprod]

section Map

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D] {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]
  (hF : E.IsConflationExact E' F) (hproj : E.isProjective ≤ E'.isProjective.inverseImage F)

/-- A conflation-exact additive functor preserving relative projectives transports a horseshoe.
In particular this applies to the grading shift and its inverse in a graded exact category. -/
noncomputable def map : Horseshoe (S.map F) (r₁.map hF hproj) (r₃.map hF hproj) where
  resolution := h.resolution.map hF hproj
  ι := (toChainComplexMapIso hF hproj r₁).hom ≫
    (F.mapHomologicalComplex _).map h.ι ≫ (toChainComplexMapIso hF hproj h.resolution).inv
  π := (toChainComplexMapIso hF hproj h.resolution).hom ≫
    (F.mapHomologicalComplex _).map h.π ≫ (toChainComplexMapIso hF hproj r₃).inv
  zero := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp_assoc, h.zero]
    simp
  ι_aug := by
    simp only [HomologicalComplex.comp_f, toChainComplexMapIso_hom_f,
      toChainComplexMapIso_inv_f, Functor.mapHomologicalComplex_map_f, aug_map,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp, h.ι_aug, F.map_comp]
    rfl
  π_aug := by
    simp only [HomologicalComplex.comp_f, toChainComplexMapIso_hom_f,
      toChainComplexMapIso_inv_f, Functor.mapHomologicalComplex_map_f, aug_map,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← F.map_comp, h.π_aug, F.map_comp]
    rfl
  split n := by
    let t := (h.split n).some.map F
    refine ⟨t.ofIso (ShortComplex.isoMk (termMapIso hF hproj r₁ n).symm
      (termMapIso hF hproj h.resolution n).symm (termMapIso hF hproj r₃ n).symm ?_ ?_)⟩
    · simp
    · simp
  length_le := by simpa using h.length_le

/-- The middle resolution of the transported horseshoe is the transported middle resolution. -/
@[simp]
theorem map_resolution : (h.map hF hproj).resolution = h.resolution.map hF hproj := (rfl)

/-- Each component of the transported injection is the functor's image of the original component,
conjugated by the term isomorphisms and identified with the transported middle term. -/
@[simp]
theorem map_ι_f (n : ℕ) : (h.map hF hproj).ι.f n =
    (termMapIso hF hproj r₁ n).hom ≫ F.map (h.ι.f n) ≫
      (termMapIso hF hproj h.resolution n).inv ≫
        eqToHom (congrArg (fun r => r.term n) (h.map_resolution hF hproj).symm) := by
  simp [map]

/-- Each component of the transported projection is the functor's image of the original component,
conjugated by the term isomorphisms after identifying the transported middle term. -/
@[simp]
theorem map_π_f (n : ℕ) : (h.map hF hproj).π.f n =
    eqToHom (congrArg (fun r => r.term n) (h.map_resolution hF hproj)) ≫
      (termMapIso hF hproj h.resolution n).hom ≫ F.map (h.π.f n) ≫
      (termMapIso hF hproj r₃ n).inv := by
  -- The identification is reflexive here, but `simp [map]` does not unfold the types in `eqToHom`.
  change _ = (𝟙 _) ≫ (termMapIso hF hproj h.resolution n).hom ≫ F.map (h.π.f n) ≫
    (termMapIso hF hproj r₃ n).inv
  simp [map]

end Map

end Horseshoe

end ExactStructure.FiniteResolution

end TauCeti
