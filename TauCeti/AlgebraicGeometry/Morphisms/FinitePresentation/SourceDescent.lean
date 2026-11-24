/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import TauCeti.RingTheory.Finiteness.SourceDescent

/-!
# Local finite presentation along smooth surjections of the source

A morphism `f : X ⟶ S` is locally of finite presentation as soon as `u ≫ f` is, for some smooth
surjection `u : X' ⟶ X` (`AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_surjective`).
Together with stability under composition, being locally of finite presentation is local on the
source for the smooth topology, in particular for the étale topology. No quasi-compactness is
asked of the cover.

Both properties are local on the base and on the source, so `X = Spec A` and `S = Spec R` may be
taken affine. As `u` is open and `Spec A` is quasi-compact, finitely many affine opens of `X'`
already cover `X`, and their disjoint union is an affine scheme `Spec B`, smooth and surjective
over `Spec A`. Then `B` is a smooth, faithfully flat `A`-algebra of finite presentation over `R`,
so `A` is of finite presentation over `R` by
`Algebra.FinitePresentation.of_smooth_of_faithfullyFlat`.

## Main results

* `AlgebraicGeometry.LocallyOfFinitePresentation.of_comp_surjective`: local finite presentation
  descends along smooth surjections of the source.
* `AlgebraicGeometry.locallyOfFinitePresentation_iff_comp_of_smooth_of_surjective`: the iff form.

## References

* The Stacks Project, Descent, Section *Properties of morphisms local in the fppf topology on the
  source*: being locally of finite presentation is fppf local on the source.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Over affine schemes, local finite presentation descends along a smooth surjection from an
affine scheme. -/
private theorem LocallyOfFinitePresentation.of_comp_surjective_of_isAffine {R A : CommRingCat.{u}}
    {Z : Scheme.{u}} [IsAffine Z] (h : Z ⟶ Spec A) (φ : R ⟶ A) [Smooth h] [Surjective h]
    [LocallyOfFinitePresentation (h ≫ Spec.map φ)] : LocallyOfFinitePresentation (Spec.map φ) := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ h)
  have : Smooth (Spec.map ψ) := hψ ▸ inferInstance
  have : Surjective (Spec.map ψ) := hψ ▸ inferInstance
  have : LocallyOfFinitePresentation (Spec.map ψ ≫ Spec.map φ) := by
    rw [hψ, Category.assoc]
    infer_instance
  rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at this
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at ‹Smooth (Spec.map ψ)›
  algebraize [φ.hom, ψ.hom, (φ ≫ ψ).hom]
  have : IsScalarTower R A Γ(Z, ⊤) := .of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat A Γ(Z, ⊤) := .of_comap_surjective (Spec.map ψ).surjective
  exact Algebra.FinitePresentation.of_smooth_of_faithfullyFlat (A := A) (B := Γ(Z, ⊤))

/-- Over an affine target, local finite presentation descends along any smooth surjection: the
images of finitely many affine opens of the source already cover the target. -/
private theorem LocallyOfFinitePresentation.of_comp_surjective_of_spec {R A : CommRingCat.{u}}
    {X' : Scheme.{u}} (u : X' ⟶ Spec A) (f : Spec A ⟶ Spec R) [Smooth u] [Surjective u]
    [LocallyOfFinitePresentation (u ≫ f)] : LocallyOfFinitePresentation f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  -- Instance search does not find these through `HasRingHomProperty`.
  have : IsZariskiLocalAtSource @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Smooth)
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  -- `u` is open, so the images of the affine opens of `X'` form an open cover of `Spec A`.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun W : X'.affineOpens ↦ u '' (W : Set X')) (fun W ↦ u.isOpenMap _ W.val.isOpen)
    fun x _ ↦ by
      obtain ⟨y, rfl⟩ := u.surjective x
      obtain ⟨W, hW, hyW, -⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
          (TopologicalSpace.Opens.mem_top y)
      exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, y, hyW, rfl⟩
  let g (W : t) : (W.val.val : Scheme) ⟶ Spec A := W.val.val.ι ≫ u
  have : Smooth (Sigma.desc g) := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : Surjective (Sigma.desc g) := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_univ_subset ?_)
    refine ht.trans (Set.iUnion₂_subset fun W hW ↦ ?_)
    rw [← W.val.range_ι, ← Set.range_comp]
    exact Set.subset_iUnion_of_subset ⟨W, hW⟩ subset_rfl
  have : LocallyOfFinitePresentation (Sigma.desc g ≫ Spec.map φ) := by
    have hdesc : Sigma.desc g ≫ Spec.map φ = Sigma.desc fun W ↦ g W ≫ Spec.map φ :=
      Sigma.hom_ext _ _ fun _ ↦ by simp
    rw [hdesc]
    exact IsZariskiLocalAtSource.sigmaDesc fun _ ↦ by
      rw [Category.assoc]
      infer_instance
  exact of_comp_surjective_of_isAffine (Sigma.desc g) φ

/-- Over an affine base, local finite presentation descends along any smooth surjection: it can
be checked on an affine open cover of the source. -/
private theorem LocallyOfFinitePresentation.of_comp_surjective_of_isAffine_base
    {R : CommRingCat.{u}} {X' X : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ Spec R) [Smooth u]
    [Surjective u] [LocallyOfFinitePresentation (u ≫ f)] : LocallyOfFinitePresentation f := by
  have hu (i : X.affineCover.I₀) : Smooth (pullback.snd u (X.affineCover.f i)) ∧
      Surjective (pullback.snd u (X.affineCover.f i)) :=
    ⟨inferInstance, inferInstance⟩
  -- Instance search does not find source locality through `HasRingHomProperty`.
  have : IsZariskiLocalAtSource @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i ↦ ?_
  have : LocallyOfFinitePresentation
      (pullback.snd u (X.affineCover.f i) ≫ X.affineCover.f i ≫ f) := by
    rw [← pullback.condition_assoc]
    exact IsZariskiLocalAtSource.comp ‹_› _
  -- The chart `X.affineCover.X i` is a spectrum only up to unfolding, so instances are explicit.
  exact @of_comp_surjective_of_spec _ _ _ (pullback.snd u (X.affineCover.f i))
    (X.affineCover.f i ≫ f) (hu i).1 (hu i).2 this

/-- **Local finite presentation descends along smooth surjections of the source.** If
`u : X' ⟶ X` is smooth and surjective and `u ≫ f` is locally of finite presentation, then so is
`f`. The cover `u` need not be quasi-compact. -/
theorem LocallyOfFinitePresentation.of_comp_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X)
    (f : X ⟶ S) [Smooth u] [Surjective u] [LocallyOfFinitePresentation (u ≫ f)] :
    LocallyOfFinitePresentation f := by
  -- Base change along an affine open cover of `S` reduces to an affine base.
  have hcomp (i : S.affineCover.I₀) : LocallyOfFinitePresentation
      (pullback.snd u (pullback.fst f (S.affineCover.f i)) ≫
        pullback.snd f (S.affineCover.f i)) := by
    rw [← pullbackRightPullbackFstIso_hom_snd]
    infer_instance
  -- Instance search does not find target locality through `HasRingHomProperty`.
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FinitePresentation)
  -- The chart `S.affineCover.X i` is a spectrum only up to unfolding, so instances are explicit.
  exact IsZariskiLocalAtTarget.of_openCover S.affineCover fun i ↦
    @of_comp_surjective_of_isAffine_base _ _ _ (pullback.snd u (pullback.fst f (S.affineCover.f i)))
      (pullback.snd f (S.affineCover.f i)) inferInstance inferInstance (hcomp i)

/-- Being locally of finite presentation can be checked after a smooth surjection of the
source. -/
theorem locallyOfFinitePresentation_iff_comp_of_smooth_of_surjective {X' X S : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) [Smooth u] [Surjective u] :
    LocallyOfFinitePresentation f ↔ LocallyOfFinitePresentation (u ≫ f) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_comp_surjective u f⟩

end AlgebraicGeometry
