/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.BaseChangeSection
public import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus.Basic
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap
public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
public import TauCeti.AlgebraicGeometry.ResidueField
public import TauCeti.RingTheory.Unramified.BaseChange
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Base change and descent of the ramification, non-étale and branch loci

For a pullback square `H : IsPullback gX f' f gY` of schemes, this file compares the ramification,
non-étale, and branch loci of `f' : X' ⟶ Y'` with those of `f : X ⟶ Y`:

* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_iff_of_isPullback_of_flat_stalkMap`,
  `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_iff_of_isPullback`: preservation and
  flat descent of formal unramifiedness on stalks (with no finite-type hypothesis).
* `AlgebraicGeometry.Scheme.Hom.ramificationLocus_subset_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.nonEtaleLocus_subset_preimage_of_isPullback`, and their flat
  base-change equalities `ramificationLocus_eq_preimage_of_isPullback`,
  `branchLocus_eq_preimage_of_isPullback`, `nonEtaleLocus_eq_preimage_of_isPullback`.
* `AlgebraicGeometry.Scheme.Hom.image_branchLocus_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_iff_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.etale_morphismRestrict_iff_of_isPullback`: faithfully flat descent
  for the branch locus and étaleness over opens.
* `TauCeti.AlgebraicGeometry.preimage_range_section_of_isPullback`,
  `TauCeti.AlgebraicGeometry.preimage_range_section_eq_range_baseChangeSection`,
  `TauCeti.AlgebraicGeometry.preimage_singleton_section_closedPoint_of_isPullback`, and
  `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_iUnion_range_section_iff_of_isPullback`:
  preimages of sections and faithfully flat descent of section-supported branch-locus bounds.

## References

* [The Stacks Project, Tag 02G3](https://stacks.math.columbia.edu/tag/02G3),
  [Tag 036W](https://stacks.math.columbia.edu/tag/036W).
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé I, §9 and Exposé X.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

section OpenImmersionSquare

/-- Postcomposing with an open immersion preserves isomorphism-invariant stalk-map properties. -/
private theorem stalkMap_comp_isOpenImmersion_right_iff
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {X₀ Y₀ Y : Scheme.{u}} (h : X₀ ⟶ Y₀) (j : Y₀ ⟶ Y)
    [IsOpenImmersion j] (q : X₀) :
    Q ((h ≫ j).stalkMap q).hom ↔ Q (h.stalkMap q).hom :=
  Iff.trans (by rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]; exact Iff.rfl)
    (hQ.cancel_left_isIso (j.stalkMap (h q)) (h.stalkMap q))

/-- In a commutative square `ι ≫ f' = h ≫ j` with open immersions `ι` and `j`, any
isomorphism-invariant ring-hom property holds for `f'.stalkMap (ι q)` iff it holds for
`h.stalkMap q`. -/
private theorem stalkMap_iff_of_isOpenImmersion_square
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {X₀ Y₀ X' Y' : Scheme.{u}} (ι : X₀ ⟶ X') (f' : X' ⟶ Y')
    (h : X₀ ⟶ Y₀) (j : Y₀ ⟶ Y') [IsOpenImmersion ι] [IsOpenImmersion j]
    (e : ι ≫ f' = h ≫ j) (q : X₀) :
    Q (f'.stalkMap (ι q)).hom ↔ Q (h.stalkMap q).hom :=
  (hQ.stalkMap_comp_isOpenImmersion_iff ι f' q).symm.trans <|
    (iff_of_eq (congrArg (fun k : X₀ ⟶ Y' ↦ Q (k.stalkMap q).hom) e)).trans
      (stalkMap_comp_isOpenImmersion_right_iff hQ h j q)

end OpenImmersionSquare

section Pullback

variable {X Y X' Y' : Scheme.{u}} {gX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {gY : Y' ⟶ Y}

/-- Extract an affine tensor-product chart around `x' : X'`, reducing the horizontal stalk maps at
`x'` and `gX x'` and flatness of `gX.stalkMap x'` to an affine pushout `S ⊗[R] A`. -/
private theorem exists_isPushout_stalkMap_iff_of_isPullback
    (H : IsPullback gX f' f gY) (x' : X') :
    ∃ (R S A : Type u) (_ : CommRing R) (_ : CommRing S) (_ : CommRing A)
      (_ : Algebra R S) (_ : Algebra R A) (q : PrimeSpectrum (S ⊗[R] A)),
      letI : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
      ((f'.stalkMap x').hom.FormallyUnramified ↔ Algebra.IsUnramifiedAt S q.asIdeal) ∧
      ((f.stalkMap (gX x')).hom.FormallyUnramified ↔
        Algebra.IsUnramifiedAt R (q.asIdeal.under A)) ∧
      ((gX.stalkMap x').hom.Flat ↔ Module.Flat A (Localization.AtPrime q.asIdeal)) := by
  have hcomm : gY (f' x') = f (gX x') := by
    rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (gX x'))) isOpen_univ
  obtain ⟨_, ⟨U', hU' : IsAffineOpen U', rfl⟩, hx'U', hU'U⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show gY (f' x') ∈ U from hcomm ▸ hxU) (U.is_open'.preimage gY.continuous)
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show f (gX x') ∈ U from hxU) (U.is_open'.preimage f.continuous)
  algebraize [(gY.appLE U U' hU'U).hom, (f.appLE U V hVU).hom]
  let _ : Algebra Γ(X, V) (Γ(Y', U') ⊗[Γ(Y, U)] Γ(X, V)) := Algebra.TensorProduct.rightAlgebra
  have := hU.isOpenImmersion_fromSpec
  have := hU'.isOpenImmersion_fromSpec
  have := hV.isOpenImmersion_fromSpec
  obtain ⟨ι, hι, h₁, h₂, hrange⟩ :=
    TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_of_isPullback H
      (iY := hU.fromSpec) (iY' := hU'.fromSpec) (iX := hV.fromSpec)
      (hU.SpecMap_appLE_fromSpec gY hU' hU'U) (hU.SpecMap_appLE_fromSpec f hV hVU)
  obtain ⟨q, rfl⟩ : x' ∈ Set.range ι := by
    rw [hrange, hU'.range_fromSpec, hV.range_fromSpec]; exact ⟨hx'U', hxV⟩
  let φR := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[Γ(Y, U)]
      Γ(Y', U') ⊗[Γ(Y, U)] Γ(X, V)).toRingHom
  let qA := Spec.map φR q
  have hgx : gX (ι q) = hV.fromSpec qA := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : _ ⟶ X ↦ k q) h₂
  have hqA : PrimeSpectrum.asIdeal qA = q.asIdeal.under Γ(X, V) :=
    (congrArg PrimeSpectrum.asIdeal (Spec.map_apply φR q)).trans (PrimeSpectrum.comap_asIdeal _ q)
  refine ⟨Γ(Y, U), Γ(Y', U'), Γ(X, V), inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q,
    (stalkMap_iff_of_isOpenImmersion_square RingHom.FormallyUnramified.respectsIso
      ι f' _ hU'.fromSpec h₁ q).trans (formallyUnramified_stalkMap_specMap_iff q), ?_,
    (stalkMap_iff_of_isOpenImmersion_square RingHom.Flat.respectsIso
      ι gX _ hV.fromSpec h₂ q).trans (flat_stalkMap_specMap_iff q)⟩
  rw [hgx]
  simpa only [hqA] using (stalkMap_iff_of_isOpenImmersion_square
    RingHom.FormallyUnramified.respectsIso hV.fromSpec f (Spec.map (f.appLE U V hVU)) hU.fromSpec
    (hU.SpecMap_appLE_fromSpec f hV hVU).symm qA).trans (formallyUnramified_stalkMap_specMap_iff qA)

/-- **Formal unramifiedness of stalk maps is preserved under arbitrary pullback** (no flatness
or finite-type hypothesis). -/
theorem formallyUnramified_stalkMap_of_isPullback (H : IsPullback gX f' f gY) (x' : X')
    (h : (f.stalkMap (gX x')).hom.FormallyUnramified) :
    (f'.stalkMap x').hom.FormallyUnramified := by
  obtain ⟨R, S, A, _, _, _, _, _, q, hf', hf, -⟩ := exists_isPushout_stalkMap_iff_of_isPullback H x'
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsUnramifiedAt R (q.asIdeal.under A) := hf.mp h
  exact hf'.mpr (Algebra.IsUnramifiedAt.of_isPushout R A q.asIdeal)

/-- If `gX` has a flat stalk map at `x'`, then `f'` is formally unramified on stalks at `x'` iff
`f` is at `gX x'`. -/
theorem formallyUnramified_stalkMap_iff_of_isPullback_of_flat_stalkMap
    (H : IsPullback gX f' f gY) (x' : X') (hflat : (gX.stalkMap x').hom.Flat) :
    (f'.stalkMap x').hom.FormallyUnramified ↔ (f.stalkMap (gX x')).hom.FormallyUnramified := by
  obtain ⟨R, S, A, _, _, _, _, _, q, hf', hf, hfl⟩ :=
    exists_isPushout_stalkMap_iff_of_isPullback H x'
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let _ := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under A) q.asIdeal
  have : Module.Flat A (Localization.AtPrime q.asIdeal) := hfl.mp hflat
  have hloc : Module.Flat (Localization.AtPrime (q.asIdeal.under A))
      (Localization.AtPrime q.asIdeal) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.asIdeal.under A))
      (q.asIdeal.under A).primeCompl (Localization.AtPrime q.asIdeal)).mpr inferInstance
  exact hf'.trans <| (Algebra.isUnramifiedAt_iff_of_isPushout_of_flat (R := R) (S := S) (A := A)
    q.asIdeal hloc).trans hf.symm

/-- **Flat base change of unramified stalk maps.** For flat `gY`, `f'` is formally unramified on
stalks at `x'` iff `f` is at `gX x'`. -/
theorem formallyUnramified_stalkMap_iff_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    (x' : X') :
    (f'.stalkMap x').hom.FormallyUnramified ↔ (f.stalkMap (gX x')).hom.FormallyUnramified :=
  haveI : Flat gX := MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  formallyUnramified_stalkMap_iff_of_isPullback_of_flat_stalkMap H x' (Flat.stalkMap gX x')

/-- Under an arbitrary pullback, `f'.ramificationLocus ⊆ gX ⁻¹' f.ramificationLocus`. -/
theorem ramificationLocus_subset_preimage_of_isPullback (H : IsPullback gX f' f gY) :
    f'.ramificationLocus ⊆ gX ⁻¹' f.ramificationLocus := fun x' hx' ↦
  mem_ramificationLocus_iff.mpr fun hfu ↦
    mem_ramificationLocus_iff.mp hx' (formallyUnramified_stalkMap_of_isPullback H x' hfu)

/-- Under an arbitrary pullback, `f'.branchLocus ⊆ gY ⁻¹' f.branchLocus`. -/
theorem branchLocus_subset_preimage_of_isPullback (H : IsPullback gX f' f gY) :
    f'.branchLocus ⊆ gY ⁻¹' f.branchLocus := fun y' hy' ↦ by
  obtain ⟨x', hx', rfl⟩ := mem_branchLocus_iff.mp hy'
  have hw : gY (f' x') = f (gX x') := by rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]
  exact mem_branchLocus_iff.mpr
    ⟨gX x', ramificationLocus_subset_preimage_of_isPullback H hx', hw.symm⟩

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
  refine (branchLocus_subset_preimage_of_isPullback H).antisymm fun y' hy' ↦ ?_
  obtain ⟨x, hx, hxy'⟩ := mem_branchLocus_iff.mp hy'
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y' hxy'
  exact mem_branchLocus_iff.mpr ⟨H.isoPullback.inv z, by
    rwa [ramificationLocus_eq_preimage_of_isPullback H, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hz₁],
    by rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_snd, hz₂]⟩

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

namespace TauCeti.AlgebraicGeometry

section SectionPullback

variable {S S' Y Y' : Scheme.{u}} {gY : Y' ⟶ Y} {p' : Y' ⟶ S'} {p : Y ⟶ S} {b : S' ⟶ S}

/-- **The preimage of a section in a pullback square is the lifted section.** Let `Y'` be the
pullback of `p : Y ⟶ S` along `b : S' ⟶ S`, let `s : S ⟶ Y` be a section of `p`, and let
`s' : S' ⟶ Y'` be a section of `p'` satisfying `s' ≫ gY = b ≫ s`. Then
`gY ⁻¹' Set.range s = Set.range s'`, with no assumption on `b`. -/
theorem preimage_range_section_of_isPullback (H : IsPullback gY p' p b)
    {s : S ⟶ Y} (hs : s ≫ p = 𝟙 S) {s' : S' ⟶ Y'} (hs'p : s' ≫ p' = 𝟙 S')
    (hs'g : s' ≫ gY = b ≫ s) :
    gY ⁻¹' Set.range s = Set.range s' := by
  refine Set.ext fun y' ↦ ⟨fun ⟨t, ht⟩ ↦ ?_, ?_⟩
  · have htb : t = b (p' y') := by
      calc t = (s ≫ p) t := by simp [hs]
        _ = (gY ≫ p) y' := by rw [Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
        _ = b (p' y') := by rw [H.w, Scheme.Hom.comp_apply]
    let y'₁ : Y' := s' (p' y')
    have hp₁ : p' y' = p' y'₁ := by dsimp [y'₁]; rw [← Scheme.Hom.comp_apply, hs'p]; simp
    have hg₁ : gY y' = gY y'₁ := by
      rw [← ht, htb, ← Scheme.Hom.comp_apply, ← hs'g, Scheme.Hom.comp_apply]
    have hsnd : pullback.snd b p (H.flip.isoPullback.hom y'₁) = s t := by
      rw [← Scheme.Hom.comp_apply, H.flip.isoPullback_hom_snd, ← hg₁, ht]
    have : IsIso (p.residueFieldMap (pullback.snd b p (H.flip.isoPullback.hom y'₁))) := by
      rw [hsnd]; exact isIso_residueFieldMap_of_section hs t
    have hz : H.flip.isoPullback.hom y' = H.flip.isoPullback.hom y'₁ :=
      Scheme.Pullback.eq_of_fst_eq_snd_eq_of_isIso
        (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, H.flip.isoPullback_hom_fst, hp₁])
        (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, H.flip.isoPullback_hom_snd, hg₁])
    exact ⟨p' y', ((Scheme.homeoOfIso H.flip.isoPullback).injective hz).symm⟩
  · rintro ⟨t', rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hs'g, Scheme.Hom.comp_apply]
    exact ⟨b t', rfl⟩

/-- Specialization of `preimage_range_section_of_isPullback` to `baseChangeSection`. -/
@[simp]
theorem preimage_range_section_eq_range_baseChangeSection {s : S ⟶ Y} (hs : s ≫ p = 𝟙 S)
    (b : S' ⟶ S) :
    pullback.snd b p ⁻¹' Set.range s = Set.range (baseChangeSection p s hs (Over.mk b)) :=
  preimage_range_section_of_isPullback (IsPullback.of_hasPullback b p).flip hs
    (baseChangeSection_fst p s hs (Over.mk b)) (baseChangeSection_snd p s hs (Over.mk b))

/-- Over a field extension `L / k`, the preimage of a `k`-rational point `s (closedPoint k)` under
the base-change projection `Y' ⟶ Y` is the single `L`-rational point `s' (closedPoint L)`. -/
theorem preimage_singleton_section_closedPoint_of_isPullback {k L : Type u} [Field k] [Field L]
    [Algebra k L] {gY : Y' ⟶ Y} {p' : Y' ⟶ Spec (.of L)} {p : Y ⟶ Spec (.of k)}
    (H : IsPullback gY p' p (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    {s : Spec (.of k) ⟶ Y} (hs : s ≫ p = 𝟙 _) {s' : Spec (.of L) ⟶ Y'} (hs'p : s' ≫ p' = 𝟙 _)
    (hs'g : s' ≫ gY = Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ s) :
    gY ⁻¹' {s (IsLocalRing.closedPoint k)} = {s' (IsLocalRing.closedPoint L)} := by
  have hrk : Set.range s = {s (IsLocalRing.closedPoint k)} :=
    Set.ext fun _ ↦ ⟨fun ⟨z, hz⟩ ↦ hz ▸ congrArg s (Subsingleton.elim z _), fun h ↦ ⟨_, h.symm⟩⟩
  have hrL : Set.range s' = {s' (IsLocalRing.closedPoint L)} :=
    Set.ext fun _ ↦ ⟨fun ⟨z, hz⟩ ↦ hz ▸ congrArg s' (Subsingleton.elim z _), fun h ↦ ⟨_, h.symm⟩⟩
  rw [← hrk, ← hrL]
  exact preimage_range_section_of_isPullback H hs hs'p hs'g

end SectionPullback

end TauCeti.AlgebraicGeometry

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
