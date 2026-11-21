/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Fiber
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Smooth
import TauCeti.RingTheory.Syntomic.SourceDescent

/-!
# Syntomicity along étale surjections of the source

A morphism `f : X ⟶ S`, locally of finite presentation, is syntomic of relative dimension `n` as
soon as `u ≫ f` is, for some étale surjection `u : X' ⟶ X`
(`TauCeti.AlgebraicGeometry.SyntomicOfRelativeDimension.of_comp_surjective`). Flatness descends
along the flat surjection `u`, and by the fibrewise criterion it suffices to treat a morphism to
the spectrum of a field. There, near a point of `X` under a point of an affine open of `X'`, the
ring-theoretic descent of local complete intersections along étale maps
(`TauCeti.exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_etale`) gives a
standard syntomic basic open neighbourhood.

The resulting morphism must be locally of finite presentation, as for smooth morphisms
(`AlgebraicGeometry.Smooth.of_comp_surjective`). The étale cover need not be quasi-compact.

## References

* The Stacks Project, Descent, Section *Properties of morphisms local in the syntomic topology on
  the source*: syntomicity is local on the source for the syntomic, hence the étale, topology.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {n : ℕ}

/-- Let `A` be of finite type over a field `K`, and `u : X' ⟶ Spec A` étale with `X' ⟶ Spec K`
syntomic of relative dimension `n`. Then every point of `Spec A` in the image of `u` has a
basic open neighbourhood `D(a)` with `A[1/a]` standard syntomic of relative dimension `n`. -/
private theorem exists_notMem_isStandardSyntomicOfRelativeDimension_of_etale {K : Type u}
    [Field K] {A : CommRingCat.{u}} [Algebra K A] [Algebra.FiniteType K A] {X' : Scheme.{u}}
    (u : X' ⟶ Spec A) [Etale u]
    [SyntomicOfRelativeDimension n (u ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)))]
    (x' : X') : ∃ a : A, a ∉ (u x').asIdeal ∧
      Algebra.IsStandardSyntomicOfRelativeDimension n K (Localization.Away a) := by
  -- An affine chart `Spec B` of `X'` through a point `y` over `x'`; `Spec B → Spec A` is étale.
  let 𝒱 := X'.affineOpenCover
  obtain ⟨y, hy⟩ := 𝒱.covers x'
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (𝒱.f (𝒱.idx x') ≫ u)
  algebraize [χ.hom]
  let : Algebra K (𝒱.X (𝒱.idx x')) := ((algebraMap A _).comp (algebraMap K A)).toAlgebra
  have : IsScalarTower K A (𝒱.X (𝒱.idx x')) := .of_algebraMap_eq' rfl
  have : Algebra.Etale A (𝒱.X (𝒱.idx x')) := by
    rw [← RingHom.etale_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp (hχ ▸ inferInstance)
  have h : RingHom.Locally (IsStandardSyntomicOfRelativeDimension n)
      (algebraMap K (𝒱.X (𝒱.idx x'))) := by
    have : SyntomicOfRelativeDimension n
        (𝒱.f (𝒱.idx x') ≫ u ≫ Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
      IsZariskiLocalAtSource.comp ‹_› _
    rw [← Category.assoc, ← hχ, ← Spec.map_comp, syntomicOfRelativeDimension_SpecMap_iff] at this
    exact this
  have hQ : y.asIdeal.comap (algebraMap A (𝒱.X (𝒱.idx x'))) = (u x').asIdeal := by
    have : u x' = Spec.map χ y := by rw [hχ, Scheme.Hom.comp_apply, hy]
    rw [this, Spec.map_apply, RingHom.algebraMap_toAlgebra]
    exact (PrimeSpectrum.comap_asIdeal χ.hom y).symm
  have : y.asIdeal.IsPrime := y.isPrime
  obtain ⟨g, hg, hstd⟩ :=
    exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_etale (A := A) h
      y.asIdeal
  exact ⟨g, hQ ▸ hg, hstd⟩

/-- Over a field, syntomicity of a morphism locally of finite type descends along an étale
surjection of the source. -/
private theorem SyntomicOfRelativeDimension.of_comp_surjective_of_field {K : Type u} [Field K]
    {X' X : Scheme.{u}} (u : X' ⟶ X) (f : X ⟶ Spec (.of K)) [Etale u] [Surjective u]
    [LocallyOfFiniteType f] [SyntomicOfRelativeDimension n (u ≫ f)] :
    SyntomicOfRelativeDimension n f := by
  wlog hX : ∃ A, X = Spec A generalizing X X' with H
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SyntomicOfRelativeDimension n)
      X.affineCover]
    intro i
    have : SyntomicOfRelativeDimension n
        (pullback.snd u (X.affineCover.f i) ≫ X.affineCover.f i ≫ f) := by
      rw [← pullback.condition_assoc]
      exact IsZariskiLocalAtSource.comp ‹_› _
    exact H (pullback.snd u (X.affineCover.f i)) _ ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  have hφ : φ = CommRingCat.ofHom (algebraMap K A) := by
    ext
    simp [RingHom.algebraMap_toAlgebra]
  rw [hφ] at ‹LocallyOfFiniteType _› ‹SyntomicOfRelativeDimension n _› ⊢
  have : Algebra.FiniteType K A := by
    rw [← RingHom.finiteType_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp ‹_›
  -- Each point `x` of `Spec A` has a standard syntomic basic open neighbourhood `D(a x)`.
  have key (x : Spec A) : ∃ a : A, a ∉ x.asIdeal ∧
      Algebra.IsStandardSyntomicOfRelativeDimension n K (Localization.Away a) := by
    obtain ⟨x', rfl⟩ := u.surjective x
    exact exists_notMem_isStandardSyntomicOfRelativeDimension_of_etale u x'
  choose a ha hstd using key
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun x ↦ PrimeSpectrum.basicOpen (a x))
    (top_unique fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, ha x⟩) fun x ↦ ?_
  rw [← basicOpenIsoSpecAway_hom_SpecMap, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @SyntomicOfRelativeDimension n),
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have := hstd x
  infer_instance

/-- **Syntomicity of a morphism locally of finite presentation descends along étale surjections of
the source.** If `f` is locally of finite presentation, `u : X' ⟶ X` is étale and surjective, and
`u ≫ f` is syntomic of relative dimension `n`, then so is `f`. The cover `u` need not be
quasi-compact. -/
theorem SyntomicOfRelativeDimension.of_comp_surjective {X' X S : Scheme.{u}} (u : X' ⟶ X)
    (f : X ⟶ S) [Etale u] [Surjective u] [LocallyOfFinitePresentation f]
    [SyntomicOfRelativeDimension n (u ≫ f)] : SyntomicOfRelativeDimension n f := by
  have := SyntomicOfRelativeDimension.flat n (u ≫ f)
  have : Flat f := Flat.of_comp_surjective u f
  refine SyntomicOfRelativeDimension.of_fiberToSpecResidueField f fun s ↦ ?_
  -- Unfold the named fibre so pullback instances can see its projection maps.
  dsimp only [Scheme.Hom.fiber, Scheme.Hom.fiberToSpecResidueField]
  let g := S.fromSpecResidueField s
  have : SyntomicOfRelativeDimension n
      (pullback.snd u (pullback.fst f g) ≫ pullback.snd f g) := by
    rw [← pullbackRightPullbackFstIso_hom_snd,
      MorphismProperty.cancel_left_of_respectsIso (P := @SyntomicOfRelativeDimension n)]
    infer_instance
  exact SyntomicOfRelativeDimension.of_comp_surjective_of_field (K := S.residueField s)
    (pullback.snd u (pullback.fst f g)) (pullback.snd f g)

/-- Among morphisms locally of finite presentation, syntomicity of relative dimension `n` can be
checked after an étale surjection of the source. -/
theorem syntomicOfRelativeDimension_iff_comp_of_etale_of_surjective {X' X S : Scheme.{u}}
    (u : X' ⟶ X) (f : X ⟶ S) [Etale u] [Surjective u] [LocallyOfFinitePresentation f] :
    SyntomicOfRelativeDimension n f ↔ SyntomicOfRelativeDimension n (u ≫ f) := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ .of_comp_surjective u f⟩
  exact zero_add n ▸ inferInstanceAs (SyntomicOfRelativeDimension (0 + n) (u ≫ f))

end TauCeti.AlgebraicGeometry
