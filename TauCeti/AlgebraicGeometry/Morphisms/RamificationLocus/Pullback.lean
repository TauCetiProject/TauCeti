/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus.Basic

/-!
# Base change and descent of the ramification, non-étale and branch loci

For a pullback square `H : IsPullback gX f' f gY` of schemes, this file compares the ramification,
non-étale, and branch loci of `f' : X' ⟶ Y'` with those of `f : X ⟶ Y`:

* `AlgebraicGeometry.Scheme.Hom.ramificationLocus_subset_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.nonEtaleLocus_subset_preimage_of_isPullback`, and their flat
  base-change equalities `ramificationLocus_eq_preimage_of_isPullback`,
  `branchLocus_eq_preimage_of_isPullback`, `nonEtaleLocus_eq_preimage_of_isPullback`.
* `AlgebraicGeometry.Scheme.Hom.image_branchLocus_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_iff_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.etale_morphismRestrict_iff_of_isPullback`: faithfully flat descent
  for the branch locus and étaleness over opens.
* `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_iUnion_range_section_iff_of_isPullback`:
  faithfully flat descent of section-supported branch-locus bounds.

## References

* [The Stacks Project, Tag 02G3](https://stacks.math.columbia.edu/tag/02G3),
  [Tag 036W](https://stacks.math.columbia.edu/tag/036W).
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé I, §9 and Exposé X.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

section Pullback

variable {X Y X' Y' : Scheme.{u}} {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}

/-- Under an arbitrary pullback, `f'.ramificationLocus ⊆ gX ⁻¹' f.ramificationLocus`. -/
theorem ramificationLocus_subset_preimage_of_isPullback (H : IsPullback gX f' f gY) :
    f'.ramificationLocus ⊆ gX ⁻¹' f.ramificationLocus := fun x' hx' ↦
  mem_ramificationLocus_iff.mpr fun hfu ↦
    mem_ramificationLocus_iff.mp hx' (formallyUnramified_stalkMap_of_isPullback H x' hfu)

/-- Under an arbitrary pullback, `f'.branchLocus ⊆ gY ⁻¹' f.branchLocus`. -/
theorem branchLocus_subset_preimage_of_isPullback (H : IsPullback gX f' f gY) :
    f'.branchLocus ⊆ gY ⁻¹' f.branchLocus := by
  rw [branchLocus_def, branchLocus_def, ← Scheme.image_preimage_eq_of_isPullback H]
  exact Set.image_mono (ramificationLocus_subset_preimage_of_isPullback H)

/-- Under an arbitrary pullback, `f'.nonEtaleLocus ⊆ gX ⁻¹' f.nonEtaleLocus`. -/
theorem nonEtaleLocus_subset_preimage_of_isPullback (H : IsPullback gX f' f gY) :
    f'.nonEtaleLocus ⊆ gX ⁻¹' f.nonEtaleLocus := fun x' hx' ↦ by
  rw [Set.mem_preimage, mem_nonEtaleLocus_iff]; rw [mem_nonEtaleLocus_iff] at hx'
  rintro ⟨W, hxW, _⟩
  exact hx' ⟨gX ⁻¹ᵁ W, hxW, MorphismProperty.of_isPullback (P := @Etale)
    ((isPullback_morphismRestrict gX W).paste_vert H) inferInstance⟩

/-- **Flat base change of the ramification locus.** -/
theorem ramificationLocus_eq_preimage_of_isPullback (H : IsPullback gX f' f gY) [Flat gY] :
    f'.ramificationLocus = gX ⁻¹' f.ramificationLocus :=
  Set.ext fun x' ↦ by
    rw [Set.mem_preimage, mem_ramificationLocus_iff, mem_ramificationLocus_iff]
    exact not_congr (formallyUnramified_stalkMap_iff_of_isPullback H x')

/-- **Flat base change of the branch locus.** -/
theorem branchLocus_eq_preimage_of_isPullback (H : IsPullback gX f' f gY) [Flat gY] :
    f'.branchLocus = gY ⁻¹' f.branchLocus := by
  rw [branchLocus_def, branchLocus_def, ramificationLocus_eq_preimage_of_isPullback H,
    Scheme.image_preimage_eq_of_isPullback H]

/-- **Flat base change of the non-étale locus** for `f` locally of finite presentation. -/
theorem nonEtaleLocus_eq_preimage_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    [LocallyOfFinitePresentation f] :
    f'.nonEtaleLocus = gX ⁻¹' f.nonEtaleLocus := by
  have : Flat gX := MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  refine (nonEtaleLocus_subset_preimage_of_isPullback H).antisymm fun x' hx' ↦ ?_
  rw [Set.mem_preimage, mem_nonEtaleLocus_iff] at hx'; rw [mem_nonEtaleLocus_iff]
  rintro ⟨W', hx'W', _⟩
  have : Flat ((W'.ι ≫ gX) ≫ f) := by rw [Category.assoc, H.w, ← Category.assoc]; infer_instance
  exact hx' ((etaleAt_iff_stalkMap f (gX x')).mpr
    ⟨(W'.ι ≫ gX).flat_stalkMap_of_comp f ⟨x', hx'W'⟩ (Flat.stalkMap _ _) (Flat.stalkMap _ _),
      (formallyUnramified_stalkMap_iff_of_isPullback H x').mp
        (formallyUnramified_stalkMap_of_isOpenImmersion_comp f' W'.ι ⟨x', hx'W'⟩)⟩)

/-- **Faithfully flat base change of the branch locus.** -/
theorem image_branchLocus_of_isPullback (H : IsPullback gX f' f gY) [Flat gY] [Surjective gY] :
    gY '' f'.branchLocus = f.branchLocus := by
  rw [branchLocus_eq_preimage_of_isPullback H, Set.image_preimage_eq _ gY.surjective]

/-- **Faithfully flat descent of branch-locus containment.** -/
theorem branchLocus_subset_iff_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    [Surjective gY] {B : Set Y} :
    f'.branchLocus ⊆ gY ⁻¹' B ↔ f.branchLocus ⊆ B := by
  rw [branchLocus_eq_preimage_of_isPullback H, gY.surjective.preimage_subset_preimage_iff]

/-- **Faithfully flat descent of étaleness outside a closed subset.** -/
theorem etale_morphismRestrict_iff_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    [Surjective gY] [LocallyOfFinitePresentation f] (U : Y.Opens) :
    Etale (f' ∣_ (gY ⁻¹ᵁ U)) ↔ Etale (f ∣_ U) := by
  have : Surjective gX := MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance
  have hpre : (f' ⁻¹ᵁ gY ⁻¹ᵁ U : Set X') = gX ⁻¹' (f ⁻¹ᵁ U : Set X) := by
    rw [← Scheme.Hom.comp_preimage, ← H.w, Scheme.Hom.comp_preimage]; rfl
  rw [etale_morphismRestrict_iff, etale_morphismRestrict_iff, hpre,
    nonEtaleLocus_eq_preimage_of_isPullback H]
  exact ⟨fun h ↦ Set.disjoint_left.mpr fun x hx hne ↦
      let ⟨x', hx'⟩ := gX.surjective x
      Set.disjoint_left.mp h (by rwa [Set.mem_preimage, hx']) (by rwa [Set.mem_preimage, hx']),
    fun h ↦ h.preimage gX⟩

end Pullback

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

/-- **Faithfully flat descent of branch-locus containment in a family of sections.** Let
`Y' = Y ×_S S'` along a faithfully flat morphism `b : S' ⟶ S` (for instance `Spec L ⟶ Spec k` for
a field extension `L / k`), let `s i : S ⟶ Y` be a family of sections lifted to compatible
sections `s' i : S' ⟶ Y'`, and let `f' : X' ⟶ Y'` be the pullback of `f : X ⟶ Y` along `Y' ⟶ Y`.
Then `f'` is branched only in `⋃ i, Set.range (s' i)` iff `f` is branched only in
`⋃ i, Set.range (s i)`. -/
theorem branchLocus_subset_iUnion_range_section_iff_of_isPullback
    {S S' X Y X' Y' : Scheme.{u}} {ι : Sort*} {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {gY : Y' ⟶ Y} {p' : Y' ⟶ S'} {p : Y ⟶ S} {b : S' ⟶ S}
    (Hf : IsPullback gX f' f gY) (HY : IsPullback gY p' p b) [Flat b] [Surjective b]
    {s : ι → (S ⟶ Y)} (hs : ∀ i, s i ≫ p = 𝟙 S)
    {s' : ι → (S' ⟶ Y')} (hs'p : ∀ i, s' i ≫ p' = 𝟙 S')
    (hs'g : ∀ i, s' i ≫ gY = b ≫ s i) :
    f'.branchLocus ⊆ ⋃ i, Set.range (s' i) ↔ f.branchLocus ⊆ ⋃ i, Set.range (s i) := by
  have : Flat gY := MorphismProperty.of_isPullback (P := @Flat) HY.flip inferInstance
  have : Surjective gY := MorphismProperty.of_isPullback (P := @Surjective) HY.flip inferInstance
  have hpre : gY ⁻¹' (⋃ i, Set.range (s i)) = ⋃ i, Set.range (s' i) := by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun i ↦
      TauCeti.AlgebraicGeometry.preimage_range_section_of_isPullback HY (hs i) (hs'p i) (hs'g i)
  rw [← hpre, branchLocus_subset_iff_of_isPullback Hf]

end AlgebraicGeometry.Scheme.Hom
