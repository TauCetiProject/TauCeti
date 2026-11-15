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

Let `f' : X' ⟶ Y'` be the pullback of `f : X ⟶ Y` along `gY : Y' ⟶ Y`, with top projection
`gX : X' ⟶ X` (`H : IsPullback gX f' f gY`). This file relates the ramification, non-étale and
branch loci of `f'` to those of `f`:

* Under an **arbitrary** base change, with no flatness or finiteness assumption on `f` or `gY`,
  unramifiedness of stalk maps is preserved (`formallyUnramified_stalkMap_of_isPullback`), so
  `f'.ramificationLocus ⊆ gX ⁻¹' f.ramificationLocus`,
  `f'.branchLocus ⊆ gY ⁻¹' f.branchLocus`, and
  `f'.nonEtaleLocus ⊆ gX ⁻¹' f.nonEtaleLocus`.
* When `gX` has a flat stalk map at `x'` — in particular when `gY` is flat — formal unramifiedness
  of the horizontal stalk maps is equivalent (`formallyUnramified_stalkMap_iff_of_isPullback`), so
  for flat `gY`,
  `f'.ramificationLocus = gX ⁻¹' f.ramificationLocus`,
  `f'.branchLocus = gY ⁻¹' f.branchLocus`, and (for `f` locally of finite presentation)
  `f'.nonEtaleLocus = gX ⁻¹' f.nonEtaleLocus`.
* When `gY` is faithfully flat (`Flat` and `Surjective`, for instance base change along an
  extension of fields), `gY '' f'.branchLocus = f.branchLocus`, containment of the branch locus in
  a subset `B ⊆ Y` descends from `Y'` (`branchLocus_subset_iff_of_isPullback`), and étaleness over
  an open `U ⊆ Y` is equivalent to étaleness of `f'` over `gY ⁻¹ᵁ U`
  (`etale_morphismRestrict_iff_of_isPullback`).
* For a section `s : S ⟶ Y` of `p : Y ⟶ S` lifted to a compatible section `s' : S' ⟶ Y'` of a
  pullback `p' : Y' ⟶ S'`, the preimage of `Set.range s` along `Y' ⟶ Y` is `Set.range s'` with no
  assumption on the base map `S' ⟶ S` (`preimage_range_section_of_isPullback`). Combined with
  faithfully flat descent of the branch locus, a morphism is branched only in a prescribed family
  of sections (such as `{0, 1, ∞}` on `ℙ¹`) if and only if its base change is
  (`branchLocus_subset_iUnion_range_section_iff_of_isPullback`).

## Main results

* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_of_isPullback`
* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_stalkMap_iff_of_isPullback`
* `AlgebraicGeometry.Scheme.Hom.ramificationLocus_subset_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.ramificationLocus_eq_preimage_of_isPullback`
* `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.branchLocus_eq_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.image_branchLocus_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_iff_of_isPullback`
* `AlgebraicGeometry.Scheme.Hom.nonEtaleLocus_subset_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.nonEtaleLocus_eq_preimage_of_isPullback`,
  `AlgebraicGeometry.Scheme.Hom.etale_morphismRestrict_iff_of_isPullback`
* `TauCeti.AlgebraicGeometry.preimage_range_section_of_isPullback`,
  `TauCeti.AlgebraicGeometry.preimage_singleton_section_closedPoint_of_isPullback`
* `AlgebraicGeometry.Scheme.Hom.branchLocus_subset_iUnion_range_section_iff_of_isPullback`

## References

* [The Stacks Project, Tag 02G3](https://stacks.math.columbia.edu/tag/02G3) (unramified morphisms
  and base change)
* [The Stacks Project, Tag 036W](https://stacks.math.columbia.edu/tag/036W) (descent of étaleness)
* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé I, §9 and Exposé X.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

section OpenImmersionSquare

/-- Postcomposing with an open immersion leaves any isomorphism-invariant ring-hom property of a
stalk map unchanged. -/
private theorem stalkMap_comp_isOpenImmersion_right_iff
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {X₀ Y₀ Y : Scheme.{u}} (h : X₀ ⟶ Y₀) (j : Y₀ ⟶ Y)
    [IsOpenImmersion j] (q : X₀) :
    Q ((h ≫ j).stalkMap q).hom ↔ Q (h.stalkMap q).hom := by
  refine Iff.trans ?_ (hQ.cancel_left_isIso (j.stalkMap (h q)) (h.stalkMap q))
  rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
  exact Iff.rfl

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

/-- Extract an affine tensor-product chart around a point `x'` of a pullback `X'`, reducing the
horizontal stalk maps at `x'` and `gX x'` and flatness of `gX.stalkMap x'` to an affine pushout
`S ⊗[R] A`. -/
private theorem exists_isPushout_stalkMap_iff_of_isPullback
    (H : IsPullback gX f' f gY) (x' : X') :
    ∃ (R S A : Type u) (_ : CommRing R) (_ : CommRing S) (_ : CommRing A)
      (_ : Algebra R S) (_ : Algebra R A) (q : PrimeSpectrum (S ⊗[R] A)),
      letI : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
      ((f'.stalkMap x').hom.FormallyUnramified ↔ Algebra.IsUnramifiedAt S q.asIdeal) ∧
      ((f.stalkMap (gX x')).hom.FormallyUnramified ↔
        Algebra.IsUnramifiedAt R (q.asIdeal.under A)) ∧
      ((gX.stalkMap x').hom.Flat ↔ Module.Flat A (Localization.AtPrime q.asIdeal)) := by
  have hcomm : gY (f' x') = f (gX x') :=
    (Scheme.Hom.comp_apply f' gY x').symm.trans <|
      (congrArg (fun h : X' ⟶ Y ↦ h x') H.w.symm).trans (Scheme.Hom.comp_apply gX f x')
  obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (gX x'))) isOpen_univ
  obtain ⟨_, ⟨U', hU' : IsAffineOpen U', rfl⟩, hx'U', hU'U⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open
      (show gY (f' x') ∈ U from hcomm ▸ hxU) (U.2.preimage gY.continuous)
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show f (gX x') ∈ U from hxU) (U.2.preimage f.continuous)
  algebraize [(gY.appLE U U' hU'U).hom, (f.appLE U V hVU).hom]
  let _ : Algebra Γ(X, V) (Γ(Y', U') ⊗[Γ(Y, U)] Γ(X, V)) := Algebra.TensorProduct.rightAlgebra
  have := hU.isOpenImmersion_fromSpec
  have := hU'.isOpenImmersion_fromSpec
  have := hV.isOpenImmersion_fromSpec
  obtain ⟨ι, hι, h₁, h₂, hrange⟩ :=
    TauCeti.AlgebraicGeometry.exists_isOpenImmersion_spec_tensorProduct_of_isPullback H
      (iY := hU.fromSpec) (iY' := hU'.fromSpec) (iX := hV.fromSpec)
      (hU.SpecMap_appLE_fromSpec gY hU' hU'U) (hU.SpecMap_appLE_fromSpec f hV hVU)
  have hx'ι : x' ∈ Set.range ι := by
    rw [hrange, hU'.range_fromSpec, hV.range_fromSpec]
    exact ⟨hx'U', hxV⟩
  obtain ⟨q₀, rfl⟩ := hx'ι
  let q : PrimeSpectrum (Γ(Y', U') ⊗[Γ(Y, U)] Γ(X, V)) := q₀
  let φR := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : Γ(X, V) →ₐ[Γ(Y, U)]
      Γ(Y', U') ⊗[Γ(Y, U)] Γ(X, V)).toRingHom
  let qA := Spec.map φR q₀
  have hgx : gX (ι q₀) = hV.fromSpec qA := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : _ ⟶ X ↦ k q₀) h₂
  have hqA : PrimeSpectrum.asIdeal qA = q.asIdeal.under Γ(X, V) :=
    (congrArg PrimeSpectrum.asIdeal (Spec.map_apply φR q₀)).trans
      (PrimeSpectrum.comap_asIdeal _ q)
  refine ⟨Γ(Y, U), Γ(Y', U'), Γ(X, V), inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q, ?_, ?_, ?_⟩
  · exact (stalkMap_iff_of_isOpenImmersion_square RingHom.FormallyUnramified.respectsIso
      ι f' _ hU'.fromSpec h₁ q₀).trans (formallyUnramified_stalkMap_specMap_iff q)
  · rw [hgx]
    simpa only [hqA] using
      (stalkMap_iff_of_isOpenImmersion_square RingHom.FormallyUnramified.respectsIso
        hV.fromSpec f (Spec.map (f.appLE U V hVU)) hU.fromSpec
        (hU.SpecMap_appLE_fromSpec f hV hVU).symm qA).trans
        (formallyUnramified_stalkMap_specMap_iff qA)
  · exact (stalkMap_iff_of_isOpenImmersion_square RingHom.Flat.respectsIso
      ι gX _ hV.fromSpec h₂ q₀).trans (flat_stalkMap_specMap_iff q)

/-- **Formal unramifiedness of stalk maps is preserved under arbitrary pullback**, with no flatness
or finite-type hypothesis on either morphism. -/
theorem formallyUnramified_stalkMap_of_isPullback (H : IsPullback gX f' f gY) (x' : X')
    (h : (f.stalkMap (gX x')).hom.FormallyUnramified) :
    (f'.stalkMap x').hom.FormallyUnramified := by
  obtain ⟨R, S, A, _, _, _, _, _, q, hf', hf, -⟩ :=
    exists_isPushout_stalkMap_iff_of_isPullback H x'
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsUnramifiedAt R (q.asIdeal.under A) := hf.mp h
  exact hf'.mpr (Algebra.IsUnramifiedAt.of_isPushout R A q.asIdeal)

/-- In a pullback square `H : IsPullback gX f' f gY`, if `gX` has a flat stalk map at `x'`, then
`f'` has a formally unramified stalk map at `x'` iff `f` has a formally unramified stalk map at
`gX x'`. No finite-type hypothesis is needed. -/
theorem formallyUnramified_stalkMap_iff_of_isPullback_of_flat_stalkMap
    (H : IsPullback gX f' f gY) (x' : X') (hflat : (gX.stalkMap x').hom.Flat) :
    (f'.stalkMap x').hom.FormallyUnramified ↔
      (f.stalkMap (gX x')).hom.FormallyUnramified := by
  obtain ⟨R, S, A, _, _, _, _, _, q, hf', hf, hfl⟩ :=
    exists_isPushout_stalkMap_iff_of_isPullback H x'
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let p := q.asIdeal.under A
  let _ := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  have : Module.Flat A (Localization.AtPrime q.asIdeal) := hfl.mp hflat
  have hloc : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (Localization.AtPrime q.asIdeal)).mpr inferInstance
  exact hf'.trans <| (Algebra.isUnramifiedAt_iff_of_isPushout_of_flat (R := R) (S := S) (A := A)
    q.asIdeal hloc).trans hf.symm

/-- **Flat base change of unramified stalk maps.** In a pullback square along a flat morphism `gY`,
`f'` is formally unramified on stalks at `x'` iff `f` is at `gX x'`, with no finite-type
hypothesis. -/
theorem formallyUnramified_stalkMap_iff_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    (x' : X') :
    (f'.stalkMap x').hom.FormallyUnramified ↔
      (f.stalkMap (gX x')).hom.FormallyUnramified :=
  haveI : Flat gX := MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  formallyUnramified_stalkMap_iff_of_isPullback_of_flat_stalkMap H x' (Flat.stalkMap gX x')

/-- Under an arbitrary pullback, the ramification locus of `f'` is contained in the preimage of the
ramification locus of `f`. -/
theorem ramificationLocus_subset_preimage_of_isPullback (H : IsPullback gX f' f gY) :
    f'.ramificationLocus ⊆ gX ⁻¹' f.ramificationLocus := by
  intro x' hx'
  rw [Set.mem_preimage, mem_ramificationLocus_iff]
  rw [mem_ramificationLocus_iff] at hx'
  exact fun hfu ↦ hx' (formallyUnramified_stalkMap_of_isPullback H x' hfu)

/-- Under an arbitrary pullback, the branch locus of `f'` is contained in the preimage of the
branch locus of `f`. -/
theorem branchLocus_subset_preimage_of_isPullback (H : IsPullback gX f' f gY) :
    f'.branchLocus ⊆ gY ⁻¹' f.branchLocus := by
  intro y' hy'
  obtain ⟨x', hx', rfl⟩ := mem_branchLocus_iff.mp hy'
  have hw : gY (f' x') = f (gX x') :=
    (Scheme.Hom.comp_apply f' gY x').symm.trans <|
      (congrArg (fun h : X' ⟶ Y ↦ h x') H.w.symm).trans (Scheme.Hom.comp_apply gX f x')
  rw [Set.mem_preimage, hw, mem_branchLocus_iff]
  exact ⟨gX x', ramificationLocus_subset_preimage_of_isPullback H hx', rfl⟩

/-- Under an arbitrary pullback, the non-étale locus of `f'` is contained in the preimage of the
non-étale locus of `f`. -/
theorem nonEtaleLocus_subset_preimage_of_isPullback (H : IsPullback gX f' f gY) :
    f'.nonEtaleLocus ⊆ gX ⁻¹' f.nonEtaleLocus := by
  intro x' hx'
  rw [Set.mem_preimage, mem_nonEtaleLocus_iff]
  rw [mem_nonEtaleLocus_iff] at hx'
  rintro ⟨W, hxW, _⟩
  refine hx' ⟨gX ⁻¹ᵁ W, hxW, ?_⟩
  exact MorphismProperty.of_isPullback (P := @Etale)
    ((isPullback_morphismRestrict gX W).paste_vert H) inferInstance

/-- **Flat base change of the ramification locus.** For a pullback along a flat morphism `gY`, the
ramification locus of `f'` is the preimage of the ramification locus of `f`. -/
theorem ramificationLocus_eq_preimage_of_isPullback (H : IsPullback gX f' f gY) [Flat gY] :
    f'.ramificationLocus = gX ⁻¹' f.ramificationLocus := by
  ext x'
  rw [Set.mem_preimage, mem_ramificationLocus_iff, mem_ramificationLocus_iff]
  exact not_congr (formallyUnramified_stalkMap_iff_of_isPullback H x')

/-- **Flat base change of the branch locus.** For a pullback along a flat morphism `gY`, the branch
locus of `f'` is the preimage of the branch locus of `f`. -/
theorem branchLocus_eq_preimage_of_isPullback (H : IsPullback gX f' f gY) [Flat gY] :
    f'.branchLocus = gY ⁻¹' f.branchLocus := by
  refine (branchLocus_subset_preimage_of_isPullback H).antisymm fun y' hy' ↦ ?_
  obtain ⟨x, hx, hxy'⟩ := mem_branchLocus_iff.mp hy'
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y' hxy'
  rw [mem_branchLocus_iff]
  refine ⟨H.isoPullback.inv z, ?_, ?_⟩
  · rw [ramificationLocus_eq_preimage_of_isPullback H, Set.mem_preimage,
      ← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hz₁]
    exact hx
  · rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_snd, hz₂]

/-- **Flat base change of the non-étale locus.** For a morphism `f` locally of finite presentation
and a flat base change `gY`, the non-étale locus of `f'` is the preimage of the non-étale locus of
`f`. -/
theorem nonEtaleLocus_eq_preimage_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    [LocallyOfFinitePresentation f] :
    f'.nonEtaleLocus = gX ⁻¹' f.nonEtaleLocus := by
  have : Flat gX := MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  refine (nonEtaleLocus_subset_preimage_of_isPullback H).antisymm fun x' hx' ↦ ?_
  rw [Set.mem_preimage, mem_nonEtaleLocus_iff] at hx'
  rw [mem_nonEtaleLocus_iff]
  rintro ⟨W', hx'W', _⟩
  refine hx' ((etaleAt_iff_stalkMap f (gX x')).mpr ⟨?_, ?_⟩)
  · have hcomp : (W'.ι ≫ gX) ≫ f = (W'.ι ≫ f') ≫ gY := by
      simp only [Category.assoc, H.w]
    have hfl : Flat ((W'.ι ≫ gX) ≫ f) := by
      rw [hcomp]
      infer_instance
    exact (W'.ι ≫ gX).flat_stalkMap_of_comp f ⟨x', hx'W'⟩ (Flat.stalkMap _ _) (Flat.stalkMap _ _)
  · exact (formallyUnramified_stalkMap_iff_of_isPullback H x').mp
      (formallyUnramified_stalkMap_of_isOpenImmersion_comp f' W'.ι ⟨x', hx'W'⟩)

/-- **Faithfully flat base change of the branch locus.** When `gY` is flat and surjective, the
image of the branch locus of `f'` under `gY` is the branch locus of `f`. -/
theorem image_branchLocus_of_isPullback (H : IsPullback gX f' f gY) [Flat gY] [Surjective gY] :
    gY '' f'.branchLocus = f.branchLocus := by
  rw [branchLocus_eq_preimage_of_isPullback H, Set.image_preimage_eq _ gY.surjective]

/-- **Faithfully flat descent of branch-locus containment.** When `gY` is flat and surjective, the
branch locus of `f'` lies in `gY ⁻¹' B` iff the branch locus of `f` lies in `B`. -/
theorem branchLocus_subset_iff_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    [Surjective gY] {B : Set Y} :
    f'.branchLocus ⊆ gY ⁻¹' B ↔ f.branchLocus ⊆ B := by
  rw [branchLocus_eq_preimage_of_isPullback H, gY.surjective.preimage_subset_preimage_iff]

/-- **Faithfully flat descent of étaleness outside a closed subset.** For `f` locally of finite
presentation and `gY` flat and surjective, `f'` is étale over `gY ⁻¹ᵁ U` iff `f` is étale over
`U`. -/
theorem etale_morphismRestrict_iff_of_isPullback (H : IsPullback gX f' f gY) [Flat gY]
    [Surjective gY] [LocallyOfFinitePresentation f] (U : Y.Opens) :
    Etale (f' ∣_ (gY ⁻¹ᵁ U)) ↔ Etale (f ∣_ U) := by
  have : Surjective gX := MorphismProperty.of_isPullback (P := @Surjective) H.flip inferInstance
  have hpre : (f' ⁻¹ᵁ gY ⁻¹ᵁ U : Set X') = gX ⁻¹' (f ⁻¹ᵁ U : Set X) := by
    rw [← Scheme.Hom.comp_preimage, ← H.w, Scheme.Hom.comp_preimage]
    rfl
  rw [etale_morphismRestrict_iff, etale_morphismRestrict_iff, hpre,
    nonEtaleLocus_eq_preimage_of_isPullback H]
  exact ⟨fun h ↦ Set.disjoint_left.mpr fun x hx hne ↦ by
      obtain ⟨x', rfl⟩ := gX.surjective x
      exact Set.disjoint_left.mp h hx hne,
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
  ext y'
  refine ⟨fun ⟨t, ht⟩ ↦ ?_, ?_⟩
  · have htb : t = b (p' y') := by
      calc t = (s ≫ p) t := by simp [hs]
        _ = (gY ≫ p) y' := by rw [Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
        _ = b (p' y') := by rw [H.w, Scheme.Hom.comp_apply]
    let y'₁ : Y' := s' (p' y')
    have hp₁ : p' y' = p' y'₁ := by
      dsimp only [y'₁]
      rw [← Scheme.Hom.comp_apply, hs'p]
      simp
    have hg₁ : gY y' = gY y'₁ := by
      calc gY y' = s (b (p' y')) := by rw [← ht, htb]
        _ = (b ≫ s) (p' y') := (Scheme.Hom.comp_apply b s (p' y')).symm
        _ = gY y'₁ := by rw [← hs'g, Scheme.Hom.comp_apply]
    have hsnd : pullback.snd b p (H.flip.isoPullback.hom y'₁) = s t := by
      rw [← Scheme.Hom.comp_apply, H.flip.isoPullback_hom_snd, ← hg₁, ht]
    have : IsIso (p.residueFieldMap (pullback.snd b p (H.flip.isoPullback.hom y'₁))) := by
      rw [hsnd]
      exact isIso_residueFieldMap_of_section hs t
    have hfst_eq :
        pullback.fst b p (H.flip.isoPullback.hom y') =
          pullback.fst b p (H.flip.isoPullback.hom y'₁) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, H.flip.isoPullback_hom_fst, hp₁]
    have hsnd_eq :
        pullback.snd b p (H.flip.isoPullback.hom y') =
          pullback.snd b p (H.flip.isoPullback.hom y'₁) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, H.flip.isoPullback_hom_snd, hg₁]
    have hz : H.flip.isoPullback.hom y' = H.flip.isoPullback.hom y'₁ :=
      Scheme.Pullback.eq_of_fst_eq_snd_eq_of_isIso hfst_eq hsnd_eq
    exact ⟨p' y', ((Scheme.homeoOfIso H.flip.isoPullback).injective hz).symm⟩
  · rintro ⟨t', rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hs'g, Scheme.Hom.comp_apply]
    exact ⟨b t', rfl⟩

/-- Specialization of `preimage_range_section_of_isPullback` to `baseChangeSection`. -/
@[simp]
theorem preimage_range_section_eq_range_baseChangeSection {s : S ⟶ Y} (hs : s ≫ p = 𝟙 S)
    (b : S' ⟶ S) :
    pullback.snd b p ⁻¹' Set.range s =
      Set.range (baseChangeSection p s hs (Over.mk b)) :=
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
  have hrk : Set.range s = {s (IsLocalRing.closedPoint k)} := by
    ext y
    exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ congrArg s (Subsingleton.elim z _), fun hy ↦ ⟨_, hy.symm⟩⟩
  have hrL : Set.range s' = {s' (IsLocalRing.closedPoint L)} := by
    ext y'
    exact ⟨fun ⟨z, hz⟩ ↦ hz ▸ congrArg s' (Subsingleton.elim z _), fun hy ↦ ⟨_, hy.symm⟩⟩
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
