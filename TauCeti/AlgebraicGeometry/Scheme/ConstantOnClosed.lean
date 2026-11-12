/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Morphisms of schemes that are constant on a closed subset

Let `f : X ⟶ Y` be a morphism of schemes and `Z` a closed subset of `X`. This file compares
three ways of saying that `f` is constant on `Z`:

* set-theoretically, the image `f '' Z` has at most one point;
* dimension-theoretically, the closure of `f '' Z` has Krull dimension zero;
* scheme-theoretically, the restriction of `f` to the reduced induced closed subscheme on `Z`
  factors through the spectrum `Spec κ(y)` of the residue field of a point `y` of `Y`, and when
  `Y` is locally of finite type over an algebraically closed field `K`, through a `K`-point of `Y`.

When `f` is locally of finite type and `Y` is a Jacobson scheme, for instance when `X` and `Y` are
locally of finite type over a field, the set-theoretic and scheme-theoretic descriptions agree for
nonempty closed subsets `Z`, and all three agree when `Z` is moreover irreducible. (Without
irreducibility the dimension condition is weaker: two distinct closed points have image of
dimension zero under the identity.) The input is that such a morphism maps closed
points to closed points (`AlgebraicGeometry.Scheme.Hom.closedPoints_subset_preimage_closedPoints`),
and that every nonempty closed subset of `X` contains a closed point. Thus a morphism constant on
a nonempty closed subset maps it to a closed point `y`, and the morphism `Spec κ(y) ⟶ Y` is then a
closed immersion through which the restriction to the reduced subscheme lifts.

Applied to an irreducible component of a geometric fibre of a family of curves, these give the
equivalent descriptions of a component contracted by a map from the curve.

Constancy also survives base change from an algebraically closed field `K` to a one-point scheme
over `K`, such as the spectrum of a field extension. The image of a closed subset on which `f` is
constant is a closed point `y` of `Y`, which is the image of a `K`-point `σ` because `κ(y) = K`.
Over a one-point scheme `T`, the fibre of `Y ×_K T ⟶ Y` over `y` is a single point, since it is
the fibre product of `σ` with that projection, which is `Spec K ×_K T ≅ T`. So the base change of
`f` is constant on the preimage of the closed subset.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isClosed_singleton_image_eq`: a morphism constant on a
  nonempty locally closed subset maps it to a closed point.
* `AlgebraicGeometry.Scheme.Hom.subsingleton_image_iff_topologicalKrullDim_closure_eq_zero`:
  constancy on an irreducible locally closed subset is dimension zero of the closure of its image.
* `AlgebraicGeometry.Scheme.Hom.subsingleton_image_iff_exists_subschemeι_comp_eq`: constancy on
  a nonempty closed subset is factorization of the restriction through some `Spec κ(y)`.
* `AlgebraicGeometry.Scheme.Hom.subsingleton_image_iff_exists_subschemeι_comp_eq_section`: over
  an algebraically closed field `K`, constancy is factorization through a `K`-point of `Y`.
* `AlgebraicGeometry.Scheme.Hom.subsingleton_preimage_range_pullback_fst`: after base change to a
  one-point scheme, the fibre over a point in the image of a section is a single point.
* `AlgebraicGeometry.Scheme.Hom.subsingleton_image_preimage_of_subsingleton_image`: over an
  algebraically closed field, constancy on a locally closed subset survives base change to a
  one-point scheme, for instance the spectrum of a field extension.

## References

* [The Stacks Project, Lemma 01TB](https://stacks.math.columbia.edu/tag/01TB): morphisms locally
  of finite type into a Jacobson scheme preserve closed points.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism locally of finite type into a Jacobson scheme which is constant on a nonempty
locally closed subset `Z` maps `Z` to a closed point. -/
theorem exists_isClosed_singleton_image_eq [JacobsonSpace Y] [LocallyOfFiniteType f]
    {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) (h : (f '' Z).Subsingleton) :
    ∃ y, IsClosed {y} ∧ f '' Z = {y} := by
  have := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxZ, hx⟩ := nonempty_inter_closedPoints hne hZ
  exact ⟨f x, f.closedPoints_subset_preimage_closedPoints hx,
    h.eq_singleton_of_mem (Set.mem_image_of_mem f hxZ)⟩

/-- A morphism locally of finite type into a Jacobson scheme is constant on an irreducible locally
closed subset `Z` if and only if the closure of the image of `Z` has Krull dimension zero. -/
theorem subsingleton_image_iff_topologicalKrullDim_closure_eq_zero [JacobsonSpace Y]
    [LocallyOfFiniteType f] {Z : Set X} (hZ : IsLocallyClosed Z) (hZi : IsIrreducible Z) :
    (f '' Z).Subsingleton ↔ topologicalKrullDim (closure (f '' Z)) = 0 := by
  have := Subtype.irreducibleSpace (hZi.image f f.continuous.continuousOn).closure
  rw [TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton, Set.subsingleton_coe]
  refine ⟨fun h ↦ ?_, fun h ↦ h.anti subset_closure⟩
  obtain ⟨y, hy, hZy⟩ := f.exists_isClosed_singleton_image_eq hZ hZi.nonempty h
  rw [hZy, hy.closure_eq]
  exact Set.subsingleton_singleton

/-- The range of the restriction of `f` to the reduced induced closed subscheme on a closed
subset `Z` is the image `f '' Z`. -/
theorem range_subschemeι_comp (Z : Closeds X) :
    Set.range ((IdealSheafData.vanishingIdeal Z).subschemeι ≫ f) = f '' Z := by
  rw [comp_base, TopCat.coe_comp, Set.range_comp, IdealSheafData.range_subschemeι,
    IdealSheafData.coe_support_vanishingIdeal]

/-- If `f` maps a closed subset `Z` into a closed point `y`, then the restriction of `f` to the
reduced induced closed subscheme on `Z` factors through `Spec κ(y) ⟶ Y`. -/
theorem exists_subschemeι_comp_eq_of_image_subset {Z : Closeds X} {y : Y} (hy : IsClosed {y})
    (h : f '' Z ⊆ {y}) :
    ∃ g : (IdealSheafData.vanishingIdeal Z).subscheme ⟶ Spec (Y.residueField y),
      (IdealSheafData.vanishingIdeal Z).subschemeι ≫ f = g ≫ Y.fromSpecResidueField y := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hy
  -- The kernel of `Spec κ(y) ⟶ Y` vanishes on `y`, hence on the closure of `f '' Z`, which is
  -- the kernel of the restriction of `f`.
  have H : (Y.fromSpecResidueField y).ker ≤
      ((IdealSheafData.vanishingIdeal Z).subschemeι ≫ f).ker := by
    rw [ker_comp, IdealSheafData.ker_subschemeι, IdealSheafData.map_vanishingIdeal,
      ← IdealSheafData.le_support_iff_le_vanishingIdeal, Closeds.closure_le]
    exact h.trans ((range_fromSpecResidueField y).symm.subset.trans
      (Y.fromSpecResidueField y).range_subset_ker_support)
  exact ⟨IsClosedImmersion.lift _ _ H, (IsClosedImmersion.lift_fac _ _ H).symm⟩

/-- A morphism locally of finite type into a Jacobson scheme is constant on a nonempty closed
subset `Z` if and only if its restriction to the reduced induced closed subscheme on `Z` factors
through `Spec κ(y) ⟶ Y` for some point `y`. -/
theorem subsingleton_image_iff_exists_subschemeι_comp_eq [JacobsonSpace Y] [LocallyOfFiniteType f]
    {Z : Closeds X} (hne : (Z : Set X).Nonempty) :
    (f '' Z).Subsingleton ↔ ∃ (y : Y) (g : (IdealSheafData.vanishingIdeal Z).subscheme ⟶
      Spec (Y.residueField y)),
      (IdealSheafData.vanishingIdeal Z).subschemeι ≫ f = g ≫ Y.fromSpecResidueField y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨y, hy, hZy⟩ := f.exists_isClosed_singleton_image_eq Z.isClosed.isLocallyClosed hne h
    exact ⟨y, f.exists_subschemeι_comp_eq_of_image_subset hy hZy.subset⟩
  · rintro ⟨y, g, hg⟩
    -- The image of `Z` is the range of the restriction, which lies in the one-point range of
    -- `Spec κ(y) ⟶ Y`.
    rw [← range_subschemeι_comp, hg, comp_base, TopCat.coe_comp]
    exact (range_fromSpecResidueField y ▸ Set.subsingleton_singleton).anti
      (Set.range_comp_subset_range _ _)

/-- Over an algebraically closed field `K`, a morphism `f : X ⟶ Y` locally of finite type, with
`Y` locally of finite type over `K`, is constant on a nonempty closed subset `Z` if and only if its
restriction to the reduced induced closed subscheme on `Z` is the constant morphism through a
`K`-point `σ` of `Y`. -/
theorem subsingleton_image_iff_exists_subschemeι_comp_eq_section {K : Type u} [Field K]
    [IsAlgClosed K] (p : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {Z : Closeds X} (hne : (Z : Set X).Nonempty) :
    (f '' Z).Subsingleton ↔ ∃ σ : Spec (.of K) ⟶ Y, σ ≫ p = 𝟙 _ ∧
      (IdealSheafData.vanishingIdeal Z).subschemeι ≫ f =
        (IdealSheafData.vanishingIdeal Z).subschemeι ≫ f ≫ p ≫ σ := by
  have := LocallyOfFiniteType.jacobsonSpace p
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨y, hy, hZy⟩ := f.exists_isClosed_singleton_image_eq Z.isClosed.isLocallyClosed hne h
    obtain ⟨g, hg⟩ := f.exists_subschemeι_comp_eq_of_image_subset hy hZy.subset
    -- `Spec κ(y) ⟶ Y` is the constant morphism through the `K`-point at `y`, because
    -- `κ(y) = K`.
    have hσ : Y.fromSpecResidueField y =
        Y.fromSpecResidueField y ≫ p ≫ pointOfClosedPoint p y hy := by
      rw [pointOfClosedPoint, ← Category.assoc, ← SpecMap_residueFieldIsoBase_inv p y hy,
        ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
    refine ⟨pointOfClosedPoint p y hy, pointOfClosedPoint_comp p y hy, ?_⟩
    rw [reassoc_of% hg, ← hσ, hg]
  · rintro ⟨σ, -, hσ⟩
    -- The image of `Z` lies in the range of `σ`, a point.
    rw [← range_subschemeι_comp, hσ]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [comp_apply]
    exact congr(σ $(Subsingleton.elim _ _))

/-- Let `q : X ⟶ S` have a section `σ`. After base change along a morphism `g : T ⟶ S` from a
one-point scheme, for instance the spectrum of a field, the fibre of `X ×_S T ⟶ X` over the image
of `σ` has at most one point: it is the fibre product of `σ` with that projection, which is
`S ×_S T ≅ T`. -/
theorem subsingleton_preimage_range_pullback_fst {S T : Scheme.{u}} (q : X ⟶ S) (g : T ⟶ S)
    [Subsingleton T] {σ : S ⟶ X} (hσ : σ ≫ q = 𝟙 S) :
    (pullback.fst q g ⁻¹' Set.range σ).Subsingleton := by
  rw [← Scheme.Pullback.range_snd]
  have e := pullbackRightPullbackFstIso q g σ ≪≫ pullback.congrHom hσ rfl ≪≫
    asIso (pullback.snd (𝟙 S) g)
  have : Subsingleton ↥(pullback σ (pullback.fst q g)) := e.hom.homeomorph.subsingleton
  exact Set.subsingleton_range _

/-- Let `K` be an algebraically closed field, `q : Y ⟶ Spec K` locally of finite type, and
`f : X ⟶ Y` locally of finite type. Let `f' : X' ⟶ Y ×_K T` lie over `f` along `p : X' ⟶ X`, where
`T` is a one-point scheme over `K`, for instance the spectrum of a field extension of `K`. If `f` is
constant on a locally closed subset `Z` of `X`, then `f'` is constant on its preimage `p ⁻¹' Z`. -/
theorem subsingleton_image_preimage_of_subsingleton_image {K : Type u} [Field K] [IsAlgClosed K]
    {X' T : Scheme.{u}} (q : Y ⟶ Spec (.of K)) [LocallyOfFiniteType q] [LocallyOfFiniteType f]
    (g : T ⟶ Spec (.of K)) [Subsingleton T] (p : X' ⟶ X) (f' : X' ⟶ pullback q g)
    (w : f' ≫ pullback.fst q g = p ≫ f) {Z : Set X} (hZ : IsLocallyClosed Z)
    (h : (f '' Z).Subsingleton) : (f' '' (p ⁻¹' Z)).Subsingleton := by
  have := LocallyOfFiniteType.jacobsonSpace q
  rcases Z.eq_empty_or_nonempty with rfl | hne
  · simp
  -- `f` maps `Z` to a closed point `y`, the image of the `K`-point at `y`.
  obtain ⟨y, hy, hZy⟩ := f.exists_isClosed_singleton_image_eq hZ hne h
  refine (q.subsingleton_preimage_range_pullback_fst g (pointOfClosedPoint_comp q y hy)).anti ?_
  rintro _ ⟨x', hx', rfl⟩
  have hx'y : f (p x') = y := hZy.subset ⟨_, hx', rfl⟩
  refine ⟨Nonempty.some inferInstance, ?_⟩
  rw [pointOfClosedPoint_apply, ← hx'y, ← Scheme.Hom.comp_apply p f, ← w, Scheme.Hom.comp_apply]

end AlgebraicGeometry.Scheme.Hom
