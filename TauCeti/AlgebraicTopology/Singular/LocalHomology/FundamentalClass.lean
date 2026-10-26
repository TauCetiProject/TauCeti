/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Homological
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.TopHomology

/-!
# The integral fundamental class of an oriented manifold

Let `M` be a Hausdorff space modelled on a real normed space `E` of finite dimension `n`, that is,
a topological `n`-manifold without boundary, and let `o` be an orientation of `M`
(`TauCeti.HomologicalOrientation M E n`).

For a compact subset `A ⊆ M`, the local orientations of `o` glue to a unique class
`o.fundamentalClassOn hn hA` of `Hₙ(M, M ∖ A; ℤ)` restricting to the local orientation `o x` at
each point `x ∈ A`. These classes are compatible with restriction to smaller compact subsets.

For `M` compact, there is a unique class `o.fundamentalClass hn` of `Hₙ(M; ℤ)`, the *fundamental
class* of `M` for the orientation `o`, whose image in `Hₙ(M, M ∖ {x}; ℤ)` is `o x` for every
`x`. Reversing the orientation negates it. If `M` is moreover connected, the fundamental class
generates `Hₙ(M; ℤ)` freely: `c ↦ c • o.fundamentalClass hn` is an isomorphism from `ℤ`.

A continuous map `f : M → X` carries the fundamental class to a class `f_*[M] ∈ Hₙ(X; ℤ)`, which
is functorial in `f` and depends only on the homotopy class of `f`.

The fundamental class is what cohomology classes are evaluated on, through the Kronecker map
`TopCat.singularKronecker`, and what Poincaré duality caps with.

## Main definitions

* `TauCeti.HomologicalOrientation.fundamentalClassOn`: the fundamental class `μ_A` of `M` along a
  compact subset `A`.
* `TauCeti.HomologicalOrientation.fundamentalClass`: the fundamental class of a compact oriented
  manifold.
* `TauCeti.HomologicalOrientation.fundamentalClassEquiv`: for a compact connected oriented
  manifold, the isomorphism `ℤ ≃ₗ[ℤ] Hₙ(M; ℤ)` sending `1` to the fundamental class.
* `TauCeti.HomologicalOrientation.mapFundamentalClass`: the image `f_*[M] ∈ Hₙ(X; ℤ)` of the
  fundamental class under a continuous map `f : M → X`.

## Main results

* `TauCeti.HomologicalOrientation.eq_fundamentalClass`: the fundamental class is the only class
  restricting to the orientation at every point.
* `TauCeti.HomologicalOrientation.fundamentalClass_neg`: the fundamental class of the reversed
  orientation is the negated fundamental class.
* `TauCeti.HomologicalOrientation.mapFundamentalClass_eq_of_homotopic`: homotopic maps carry the
  fundamental class to the same class.

## Implementation notes

The manifold lives in `Type`. The gluing results this file rests on
(`TauCeti.existsUnique_localHomologyRestriction_eq_of_invariant` and the top homology of a compact
manifold) take coefficients in `ModuleCat.{w} Λ` for a ring `Λ : Type w` in the universe of `M`,
as Mathlib's exactness of filtered colimits of modules is stated in that generality; the integral
coefficients `ModuleCat.of ℤ (ULift ℤ)` of local orientations meet this condition in `Type`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, Lemma 3.27 and Theorem 3.26.
-/

public section

noncomputable section

open CategoryTheory Module Set

namespace TauCeti

namespace HomologicalOrientation

variable {M E : Type} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ} (o : HomologicalOrientation M E n) (hn : finrank ℝ E = n)

/-- The local orientations of `o`, as a family of local homology classes, are invariant under
transport. -/
private theorem localHomologyTransport_coe_apply {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyTransport (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) M E n f
      (o x.as).val = (o y.as).val := by
  rw [← coe_localOrientationTransport, localOrientationTransport_apply]

/-- The map `Hₙ(M; ℤ) → Hₙ(M, M ∖ {x}; ℤ)`, the quotient map to `Hₙ(M, M ∖ M; ℤ)` followed by
restriction, with its source written as the singular homology of `M`. -/
private def toLocalHomology (x : M) :
    ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ) →ₗ[ℤ]
      localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) ({x} : Set M) n :=
  ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
      (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) n ≫
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (subset_univ {x}) n).hom

omit [T2Space M] in
private theorem toLocalHomology_apply (x : M)
    (γ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)) :
    toLocalHomology x γ =
      localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (subset_univ {x}) n
      (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
        (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom γ) :=
  (rfl)

section Compact

variable {A : Set M} (hA : IsCompact A)

include hn hA in
private theorem existsUnique_fundamentalClassOn :
    ∃! γ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) A n,
      ∀ x (hx : x ∈ A), localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
        (singleton_subset_iff.2 hx) n γ = (o x).val :=
  existsUnique_localHomologyRestriction_eq_of_invariant (ModuleCat.of ℤ (ULift.{0} ℤ)) hn hA
    (fun x ↦ (o x).val) o.localHomologyTransport_coe_apply

/-- **The fundamental class of `M` along a compact subset** `A`: the unique class of
`Hₙ(M, M ∖ A; ℤ)` whose restriction to `Hₙ(M, M ∖ {x}; ℤ)` is the local orientation `o x` at
every point `x ∈ A`. -/
def fundamentalClassOn : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) A n :=
  (o.existsUnique_fundamentalClassOn hn hA).exists.choose

/-- The fundamental class along `A` restricts to the local orientation at every point of `A`. -/
theorem localHomologyRestriction_fundamentalClassOn {x : M} (hx : x ∈ A) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (singleton_subset_iff.2 hx) n
      (o.fundamentalClassOn hn hA) = (o x).val :=
  (o.existsUnique_fundamentalClassOn hn hA).exists.choose_spec x hx

/-- **Uniqueness of the fundamental class along `A`**: a class of `Hₙ(M, M ∖ A; ℤ)` restricting
to the local orientation at every point of `A` is the fundamental class along `A`. -/
theorem eq_fundamentalClassOn
    {γ : localHomology (A := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) A n}
    (hγ : ∀ x (hx : x ∈ A), localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ))
      (singleton_subset_iff.2 hx) n γ = (o x).val) :
    γ = o.fundamentalClassOn hn hA :=
  (o.existsUnique_fundamentalClassOn hn hA).unique hγ fun _ hx ↦
    o.localHomologyRestriction_fundamentalClassOn hn hA hx

/-- The fundamental classes along compact subsets are compatible with restriction: for compact
`B ⊆ A`, the fundamental class along `A` restricts to the fundamental class along `B`. -/
@[simp]
theorem localHomologyRestriction_fundamentalClassOn_of_subset {B : Set M} (hB : IsCompact B)
    (hBA : B ⊆ A) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) hBA n (o.fundamentalClassOn hn hA) =
      o.fundamentalClassOn hn hB := by
  refine o.eq_fundamentalClassOn hn hB fun x hx ↦ ?_
  rw [localHomologyRestriction_comp_apply]
  exact o.localHomologyRestriction_fundamentalClassOn hn hA (hBA hx)

/-- The fundamental class along a point is the local orientation there. -/
@[simp]
theorem fundamentalClassOn_singleton (x : M) (hx : IsCompact ({x} : Set M)) :
    o.fundamentalClassOn hn hx = (o x).val := by
  rw [← o.localHomologyRestriction_fundamentalClassOn hn hx (mem_singleton x),
    localHomologyRestriction_refl, ModuleCat.id_apply]

/-- Reversing the orientation negates the fundamental class along `A`. -/
@[simp]
theorem fundamentalClassOn_neg :
    (-o).fundamentalClassOn hn hA = -o.fundamentalClassOn hn hA := by
  refine ((-o).eq_fundamentalClassOn hn hA fun x hx ↦ ?_).symm
  rw [map_neg, o.localHomologyRestriction_fundamentalClassOn hn hA hx, neg_apply,
    LocalOrientation.coe_neg]

end Compact

section CompactSpace

variable [CompactSpace M]

include hn in
private theorem existsUnique_fundamentalClass :
    ∃! γ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
        ModuleCat.{0} ℤ),
      ∀ x : M, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (subset_univ {x}) n
        (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
          (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom γ) = (o x).val :=
  existsUnique_singularHomology_localHomologyRestriction_eq_of_invariant
    (ModuleCat.of ℤ (ULift.{0} ℤ)) hn (fun x ↦ (o x).val) o.localHomologyTransport_coe_apply

/-- **The fundamental class of a compact oriented manifold**: the unique class of `Hₙ(M; ℤ)`
whose image in the local homology `Hₙ(M, M ∖ {x}; ℤ)` is the local orientation `o x` at every
point `x`. The image in local homology is the quotient map to `Hₙ(M, M ∖ M; ℤ)` followed by
restriction. -/
def fundamentalClass :
    ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ) :=
  (o.existsUnique_fundamentalClass hn).exists.choose

/-- The fundamental class restricts to the local orientation at every point. -/
theorem localHomologyRestriction_singularHomologyπ_fundamentalClass (x : M) :
    localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (subset_univ {x}) n
      (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
        (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom (o.fundamentalClass hn)) =
      (o x).val :=
  (o.existsUnique_fundamentalClass hn).exists.choose_spec x

/-- **Uniqueness of the fundamental class**: a class of `Hₙ(M; ℤ)` whose image in the local
homology at every point is the local orientation there is the fundamental class. -/
theorem eq_fundamentalClass
    {γ : ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ)}
    (hγ : ∀ x : M, localHomologyRestriction (ModuleCat.of ℤ (ULift.{0} ℤ)) (subset_univ {x}) n
      (((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
        (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom γ) = (o x).val) :
    γ = o.fundamentalClass hn :=
  (o.existsUnique_fundamentalClass hn).unique hγ
    (o.localHomologyRestriction_singularHomologyπ_fundamentalClass hn)

/-- The image of the fundamental class in `Hₙ(M, M ∖ M; ℤ)` is the fundamental class along the
whole of `M`. -/
theorem singularHomologyπ_fundamentalClass :
    ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
      (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) n).hom (o.fundamentalClass hn) =
      o.fundamentalClassOn hn isCompact_univ :=
  o.eq_fundamentalClassOn hn isCompact_univ fun x _ ↦
    o.localHomologyRestriction_singularHomologyπ_fundamentalClass hn x

/-- Reversing the orientation negates the fundamental class. -/
@[simp]
theorem fundamentalClass_neg : (-o).fundamentalClass hn = -o.fundamentalClass hn := by
  refine ((-o).eq_fundamentalClass hn fun x ↦ ?_).symm
  rw [← toLocalHomology_apply, map_neg, toLocalHomology_apply,
    localHomologyRestriction_singularHomologyπ_fundamentalClass, neg_apply,
    LocalOrientation.coe_neg]

section Map

open AlgebraicTopology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The image `f_*[M] ∈ Hₙ(X; ℤ)` of the fundamental class of a compact oriented manifold `M` under
a continuous map `f : M → X`: the homology class carried by the singular manifold `f`. -/
def mapFundamentalClass (f : C(M, X)) :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).obj
      (TopCat.of X) :=
  (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
    (TopCat.ofHom f)).hom (o.fundamentalClass hn)

theorem mapFundamentalClass_def (f : C(M, X)) :
    o.mapFundamentalClass hn f =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom f)).hom (o.fundamentalClass hn) :=
  (rfl)

/-- The image of the fundamental class under the identity is the fundamental class. -/
@[simp]
theorem mapFundamentalClass_id : o.mapFundamentalClass hn (ContinuousMap.id M) =
    o.fundamentalClass hn := by
  rw [mapFundamentalClass_def, TopCat.ofHom_id, CategoryTheory.Functor.map_id]
  -- The identity morphism acts as the identity; its source is read as `SSet.homology`.
  rfl

/-- The image of the fundamental class under a composite `g ∘ f` is the image under `g` of its
image under `f`. -/
theorem mapFundamentalClass_comp (g : C(X, Y)) (f : C(M, X)) :
    o.mapFundamentalClass hn (g.comp f) =
      (((singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj (ModuleCat.of ℤ (ULift.{0} ℤ))).map
        (TopCat.ofHom g)).hom (o.mapFundamentalClass hn f) := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, TopCat.ofHom_comp,
    CategoryTheory.Functor.map_comp]
  -- The fundamental class lives in `SSet.homology`, which `rw` does not see through.
  rfl

/-- **Homotopy invariance**: homotopic maps carry the fundamental class to the same class. -/
theorem mapFundamentalClass_eq_of_homotopic {f g : C(M, X)} (h : f.Homotopic g) :
    o.mapFundamentalClass hn f = o.mapFundamentalClass hn g := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def]
  congr 2
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{0} ℤ)
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) h.some _ n

/-- Reversing the orientation negates the image of the fundamental class. -/
@[simp]
theorem mapFundamentalClass_neg (f : C(M, X)) :
    (-o).mapFundamentalClass hn f = -o.mapFundamentalClass hn f := by
  rw [mapFundamentalClass_def, mapFundamentalClass_def, fundamentalClass_neg]
  exact map_neg _ _

end Map

/-- Multiples of the fundamental class restrict to the same multiples of the local orientation. -/
private theorem toLocalHomology_comp_toSpanSingleton (x : M) :
    toLocalHomology x ∘ₗ LinearMap.toSpanSingleton ℤ _ (o.fundamentalClass hn) =
      LinearMap.toSpanSingleton ℤ _ (o x).val := by
  ext
  rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply_one,
    LinearMap.toSpanSingleton_apply_one, toLocalHomology_apply,
    localHomologyRestriction_singularHomologyπ_fundamentalClass]

variable [ConnectedSpace M]

include hn in
/-- On a compact connected manifold, a class of `Hₙ(M; ℤ)` is determined by its image in the
local homology at any one point. -/
private theorem toLocalHomology_injective (x : M) :
    Function.Injective (toLocalHomology (n := n) x) := by
  have : IsEmpty (TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).snd := by
    simp only [compl_univ]
    exact inferInstanceAs (IsEmpty (∅ : Set M))
  have hπ : IsIso ((TopPair.ofSubset ((univ : Set (TopCat.of M))ᶜ)).singularHomologyπ
      (C := ModuleCat.{0} ℤ) (ModuleCat.of ℤ (ULift.{0} ℤ)) n) := inferInstance
  intro γ δ h
  rw [toLocalHomology_apply, toLocalHomology_apply] at h
  exact ((ConcreteCategory.isIso_iff_bijective _).1 hπ).1
    (localHomologySystemCone_π_app_injective (ModuleCat.of ℤ (ULift.{0} ℤ)) hn
      (FundamentalGroupoid.mk x) h)

/-- The map `c ↦ c • o.fundamentalClass hn` is bijective on a compact connected manifold. -/
private theorem bijective_toSpanSingleton_fundamentalClass :
    Function.Bijective (LinearMap.toSpanSingleton ℤ _ (o.fundamentalClass hn)) := by
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := M)
  have hx (c : ℤ) : toLocalHomology x (LinearMap.toSpanSingleton ℤ _ (o.fundamentalClass hn) c) =
      c • (o x).val := by
    rw [← LinearMap.comp_apply, o.toLocalHomology_comp_toSpanSingleton hn x,
      LinearMap.toSpanSingleton_apply]
    exact int_smul_eq_zsmul _ c _
  refine ⟨fun c c' h ↦ ?_, fun γ ↦ ?_⟩
  · -- Compare the images in the local homology at `x`, where `o x` has infinite order.
    have h' : (c - c') • (o x).val = 0 := by
      rw [sub_zsmul, ← hx, ← hx, h]
      simp
    subst hn
    exact sub_eq_zero.1 (((o x).property.zsmul_eq_zero_iff
      (singularHomologyComplSingletonFinrankIso _ (chartAt E x) (mem_chart_source E x))).1 h')
  · -- The image of `γ` at `x` is a multiple of the generator `o x`.
    obtain ⟨c, hc⟩ := (isLocalOrientation_iff _ _ _).1 (o x).property (toLocalHomology x γ)
    exact ⟨c, toLocalHomology_injective hn x ((hx c).trans hc)⟩

/-- **The fundamental class generates the top homology freely.** For a compact connected oriented
manifold, `c ↦ c • o.fundamentalClass hn` is an isomorphism `ℤ ≃ₗ[ℤ] Hₙ(M; ℤ)`. -/
def fundamentalClassEquiv :
    ℤ ≃ₗ[ℤ] ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) n :
      ModuleCat.{0} ℤ) :=
  LinearEquiv.ofBijective _ (o.bijective_toSpanSingleton_fundamentalClass hn)

@[simp]
theorem fundamentalClassEquiv_apply (c : ℤ) :
    o.fundamentalClassEquiv hn c = c • o.fundamentalClass hn :=
  int_smul_eq_zsmul _ c _

end CompactSpace

end HomologicalOrientation

end TauCeti
