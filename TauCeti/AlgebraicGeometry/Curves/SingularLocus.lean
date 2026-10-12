/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Pullback
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.StandardSmooth
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.PureRelativeDimension
public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Smooth

/-!
# The relative singular locus

Let `X` be flat and locally of finite presentation over a commutative ring `R`, with every
nonempty fibre pure of dimension one. The sheaf of relative differentials `Ω_{X/R}` is
quasi-coherent, and its sections over every affine open are finitely generated, so it has Fitting
ideal sheaves. The **relative singular locus** `Sing(X/R)` is the closed subscheme of `X` cut out
by the first Fitting ideal sheaf `Fitt₁(Ω_{X/R})`.

Over an affine open `U` its ideal is the first Fitting ideal of the module of Kähler differentials
`Ω[Γ(X, U)⁄R]`, and a point `x` lies in `Sing(X/R)` exactly when the fibre `Ω_{X/R} ⊗ κ(x)` has
dimension at least two, that is, when `Ω_{X/R}` needs at least two generators near `x`. For a
family of curves this is the closed subscheme in terms of which the Stacks Project defines
families of nodal curves.

## Main definitions

* `AlgebraicGeometry.Scheme.singularLocus R X`: the ideal sheaf `Fitt₁(Ω_{X/R})` of the relative
  singular locus; its closed subscheme is `(X.singularLocus R).subscheme`.

## Main results

* `AlgebraicGeometry.Scheme.singularLocus_ideal`: over an affine open `U`, the ideal of the
  singular locus is the first Fitting ideal of `Ω[Γ(X, U)⁄R]`.
* `AlgebraicGeometry.Scheme.mem_support_singularLocus_iff`: a point `x` of an affine open `U` lies
  in the singular locus exactly when `1 < dim_{κ(x)} κ(x) ⊗ Ω[Γ(X, U)⁄R]`.
* `AlgebraicGeometry.Scheme.singularLocus_ideal_top_Spec`: on `Spec A`, the ideal of global
  sections is the image of the first Fitting ideal of `Ω[A⁄R]`.
* `AlgebraicGeometry.Scheme.singularLocus_eq_top`: a smooth relative curve, smooth of relative
  dimension one over `Spec R`, has empty singular locus: there `Ω_{X/R}` is locally free of rank
  one, so its first Fitting ideal sheaf is the unit ideal sheaf.
* `AlgebraicGeometry.Scheme.singularLocus_eq_comap_of_isPullback`: the formation of the singular
  locus commutes with base change along `Spec R' → Spec R`: if `X'` is the base change of `X`,
  then `Sing(X'/R')` is the inverse image of `Sing(X/R)`.
* `AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι`: the same for the closed
  subschemes, `Sing(X'/R') = Sing(X/R) ×_X X'`.

This compatibility lets the affine-base singular loci agree on affine overlaps and identifies the
singular subscheme after extending the ground ring. It is therefore the local input for gluing the
relative singular locus over a general base and for transporting that locus under base change.

## References

* [Stacks Project, Tag 0C3C](https://stacks.math.columbia.edu/tag/0C3C): Fitting ideals of a
  finite type quasi-coherent module.
* [Stacks Project, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): families of nodal
  curves, where the singular locus of a family of curves is cut out by the first Fitting ideal of
  its sheaf of relative differentials.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite TauCeti.AlgebraicGeometry

open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The **relative singular locus** of a flat, locally finitely presented scheme `X` of pure
relative dimension one over `Spec R`, as an ideal sheaf: the first Fitting ideal sheaf
`Fitt₁(Ω_{X/R})` of the sheaf of relative differentials. Its support is the set of points at which
the fibre of `Ω_{X/R}` has dimension at least two
(`AlgebraicGeometry.Scheme.mem_support_singularLocus_iff`). -/
def _root_.AlgebraicGeometry.Scheme.singularLocus
    [_hflat : Flat (X ↘ Spec (.of R))]
    [_hfinite : LocallyOfFinitePresentation (X ↘ Spec (.of R))]
    [_hpure : PureRelativeDimension 1 (X ↘ Spec (.of R))] : X.IdealSheafData :=
  (X.relativeDifferentials R).fittingIdeal (fun _ ↦ inferInstance) 1

variable [Flat (X ↘ Spec (.of R))]
  [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]

/-- The singular locus is the first Fitting ideal sheaf of the relative differentials. -/
theorem _root_.AlgebraicGeometry.Scheme.singularLocus_def :
    X.singularLocus R = (X.relativeDifferentials R).fittingIdeal (fun _ ↦ inferInstance) 1 :=
  (rfl)

/-- Over an affine open `U`, the ideal of the singular locus is the first Fitting ideal of the
module of Kähler differentials `Ω[Γ(X, U)⁄R]`. -/
theorem _root_.AlgebraicGeometry.Scheme.singularLocus_ideal (U : X.affineOpens) :
    letI : Algebra R Γ(X, U) :=
      ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
    haveI := finiteType_sections_of_locallyOfFiniteType R X U
    (X.singularLocus R).ideal U = fittingIdeal Γ(X, U) Ω[Γ(X, U)⁄R] 1 := by
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  have := finiteType_sections_of_locallyOfFiniteType R X U
  rw [Scheme.singularLocus_def, Scheme.Modules.fittingIdeal_ideal]
  exact (fittingIdeal_congr (relativeDifferentialsSectionsEquiv R X U) 1).symm

/-- **The support of the singular locus.** A point `x` of an affine open `U` lies in the singular
locus exactly when the fibre `κ(x) ⊗ Ω[Γ(X, U)⁄R]` of the relative differentials at `x` has
dimension greater than one. -/
theorem _root_.AlgebraicGeometry.Scheme.mem_support_singularLocus_iff {x : X}
    {U : X.affineOpens} (hx : x ∈ U.1) :
    x ∈ (X.singularLocus R).support ↔
      letI := (X.evaluation U x hx).hom.toAlgebra
      letI : Algebra R Γ(X, U) :=
        ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
      1 < Module.finrank (X.residueField x) (X.residueField x ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) := by
  let := (X.evaluation U x hx).hom.toAlgebra
  let : Algebra R Γ(X, U) :=
    ((X.baseRingToStructurePresheaf R).app (op U.val)).hom.toAlgebra
  rw [Scheme.singularLocus_def, Scheme.Modules.mem_support_fittingIdeal_iff _ _ hx,
    ((relativeDifferentialsSectionsEquiv R X U).baseChange Γ(X, U) _ _ _).finrank_eq]

/-- On an affine scheme `Spec A` of finite type over `R`, the ideal of global sections of the
singular locus is the image of the first Fitting ideal of `Ω[A⁄R]` under `A ≅ Γ(Spec A, ⊤)`. -/
theorem _root_.AlgebraicGeometry.Scheme.singularLocus_ideal_top_Spec (A : CommRingCat.{u})
    [Algebra R A] [Algebra.FiniteType R A]
    [Flat (Spec A ↘ Spec (.of R))]
    [LocallyOfFinitePresentation (Spec A ↘ Spec (.of R))]
    [PureRelativeDimension 1 (Spec A ↘ Spec (.of R))] :
    ((Spec A).singularLocus R).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (fittingIdeal A Ω[A⁄R] 1).map (Scheme.ΓSpecIso A).inv.hom := by
  let : Algebra R Γ(Spec A, ⊤) :=
    (((Spec A).baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  have : IsScalarTower R A Γ(Spec A, ⊤) := .of_algebraMap_eq fun r ↦
    Scheme.baseRingToStructurePresheaf_Spec_app_apply R A (op ⊤) r
  -- `A → Γ(Spec A, ⊤)` is an isomorphism, so `Ω` of the global sections is the base change
  -- of `Ω[A⁄R]`, and Fitting ideals commute with base change.
  have hmap : algebraMap A Γ(Spec A, ⊤) = (Scheme.ΓSpecIso A).inv.hom := by
    have h : (homOfLE le_top : (⊤ : (Spec A).Opens) ⟶ ⊤) = 𝟙 _ := rfl
    rw [IsAffineOpen.algebraMap_Spec_obj, h, op_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have hbij : Function.Bijective (algebraMap A Γ(Spec A, ⊤)) := by
    rw [hmap]
    exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv
  have : Algebra.FormallyEtale A Γ(Spec A, ⊤) :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId A Γ(Spec A, ⊤)) hbij)
  have := finiteType_sections_of_locallyOfFiniteType R (Spec A) ⟨⊤, isAffineOpen_top _⟩
  rw [Scheme.singularLocus_ideal, ← hmap]
  exact (KaehlerDifferential.isBaseChange_of_formallyEtale R A Γ(Spec A, ⊤)).fittingIdeal_eq_map 1

variable {R X} in
/-- At a point `x` of an affine open `W` whose ring of functions is standard smooth of relative
dimension one over `R`, the fibre of `Ω_{X/R}` is one-dimensional, so `x` does not lie in the
singular locus. -/
private theorem notMem_support_singularLocus_of_isStandardSmooth {x : X} {W : X.affineOpens}
    (hxW : x ∈ W.1)
    (hW : ((X.baseRingToStructurePresheaf R).app (op W.1)).hom.IsStandardSmoothOfRelativeDimension
      1) :
    x ∉ (X.singularLocus R).support := by
  let := (X.evaluation W x hxW).hom.toAlgebra
  let : Algebra R Γ(X, W) := ((X.baseRingToStructurePresheaf R).app (op W.1)).hom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R Γ(X, W) := hW.toAlgebra
  have : Algebra.IsStandardSmooth R Γ(X, W) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
  -- `Ω[Γ(X, W)⁄R]` is free of rank one, hence so is its fibre at `x`.
  have hrank : Module.finrank Γ(X, W) Ω[Γ(X, W)⁄R] = 1 :=
    Module.finrank_eq_of_rank_eq
      (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1)
  rw [Scheme.mem_support_singularLocus_iff R X hxW, Module.finrank_baseChange, hrank]
  exact lt_irrefl 1

end

section Smooth

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- **A smooth relative curve has empty singular locus.** If `X` is smooth of relative dimension
one over `Spec R`, then the first Fitting ideal sheaf of `Ω_{X/R}` is the unit ideal sheaf, since
`Ω_{X/R}` is locally free of rank one. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.singularLocus_eq_top
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of R))] :
    haveI := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of R))
    X.singularLocus R = ⊤ := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of R))
  refine (Scheme.IdealSheafData.support_eq_bot_iff _).mp (eq_bot_iff.mpr fun x hx ↦ ?_)
  obtain ⟨W, hxW, hW⟩ := exists_isStandardSmoothOfRelativeDimension R 1 x
  exact notMem_support_singularLocus_of_isStandardSmooth hxW hW hx

end Smooth

section BaseChange

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  {X X' : Scheme.{u}} [X.Over (Spec (.of R))] [X'.Over (Spec (.of R'))] {g : X' ⟶ X}

variable [Flat (X ↘ Spec (.of R))] [LocallyOfFinitePresentation (X ↘ Spec (.of R))]
  [PureRelativeDimension 1 (X ↘ Spec (.of R))]
  [Flat (X' ↘ Spec (.of R'))] [LocallyOfFinitePresentation (X' ↘ Spec (.of R'))]
  [PureRelativeDimension 1 (X' ↘ Spec (.of R'))]

/-- **The singular locus commutes with base change.** If `X'` is the base change of `X` along
`Spec R' → Spec R`, with projection `g : X' ⟶ X`, then the singular locus of `X'` over `R'` is the
inverse image under `g` of the singular locus of `X` over `R`. For the closed subschemes, see
`AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι`. -/
theorem _root_.AlgebraicGeometry.Scheme.singularLocus_eq_comap_of_isPullback
    (H : IsPullback g (X' ↘ Spec (.of R')) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    X'.singularLocus R' = (X.singularLocus R).comap g := by
  have : IsAffineHom g := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  -- Compare both ideal sheaves on the cover of `X'` by the preimages of affine opens of `X`.
  have charts (x : X') : ∃ U : X.Opens, IsAffineOpen U ∧ g x ∈ U := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (U := ⊤) (x := g x) (by simp)
    exact ⟨U, hU, hx⟩
  choose U hU hx using charts
  let 𝒰 : X'.OpenCover := Scheme.Cover.mkOfCovers X' (fun x ↦ Spec Γ(X', g ⁻¹ᵁ U x))
    (fun x ↦ ((hU x).preimage g).fromSpec) (fun x ↦ ⟨x, by
      have hmem : x ∈ Set.range ((hU x).preimage g).fromSpec :=
        ((hU x).preimage g).range_fromSpec.symm ▸ hx x
      simpa only [Set.mem_range] using hmem⟩)
  refine Scheme.IdealSheafData.ext_of_comap_openCover 𝒰 fun x ↦ ?_
  -- `rw` cannot reduce the cover's dependent index and object projections together, so restate
  -- the goal using the chosen chart maps.
  change (X'.singularLocus R').comap ((hU x).preimage g).fromSpec =
    ((X.singularLocus R).comap g).comap ((hU x).preimage g).fromSpec
  rw [Scheme.IdealSheafData.comap_fromSpec_eq_ofIdealTop,
    Scheme.IdealSheafData.comap_comap_fromSpec_eq_ofIdealTop _ g (hU x) ((hU x).preimage g) le_rfl,
    Scheme.singularLocus_ideal, Scheme.singularLocus_ideal,
    Scheme.fittingIdeal_kaehlerDifferential_preimage_eq_map H (hU x) 1]

/-- **The singular subscheme commutes with base change.** If `X'` is the base change of `X` along
`Spec R' → Spec R`, with projection `g : X' ⟶ X`, then `Sing(X'/R')` is the base change
`Sing(X/R) ×_X X'` of the closed subscheme `Sing(X/R)`, and hence the base change of `Sing(X/R)`
along `Spec R' → Spec R`. -/
theorem _root_.AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι
    (H : IsPullback g (X' ↘ Spec (.of R')) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    IsPullback (X'.singularLocus R').subschemeι
      ((X'.singularLocus R').subschemeMap (X.singularLocus R) g
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
          (Scheme.singularLocus_eq_comap_of_isPullback H).ge))
      g (X.singularLocus R).subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _ (by simp) (by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.singularLocus_eq_comap_of_isPullback H])

end BaseChange

end TauCeti
