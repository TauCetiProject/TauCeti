/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Restriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.GradedContraction

/-!
# Classes of contracted complexes under change of group

Let `J` be a complex of topological `G`-representations with a contraction `c` onto `X`, in the
sense of `TopRep.ResolutionContraction`. Every `G`-invariant cocycle `z` of `J` has a class
`c.cohomologyClass z` in `Hⁿ(G, X)`. This file computes the image of that class under the map
`ContinuousCohomology.map φ f` of a compatible pair, a continuous homomorphism `φ : H →ₜ* G`
together with a morphism `f : res φ X ⟶ Y` of `H`-representations.

The contraction maps of `c` need not be equivariant, so they contract the restriction of `J` along
`φ` onto the restriction of `X` as well (`TopRep.ResolutionContraction.res`). Restricting along `φ`
then sends the class of `z` to the class of the same cocycle in the restricted complex, now
invariant under `H` (`TopRep.ResolutionContraction.map_cohomologyClass_res`). More generally, a
chain map from the restricted complex to a complex contracted onto `Y` lying over `f` carries `z`
to a cocycle whose class is the image of the class of `z`
(`TopRep.ResolutionContraction.map_cohomologyClass`). Restriction to a subgroup is the special case
`TopRep.ResolutionContraction.res_cohomologyClass`. For complexes assembled from graded
representations, a morphism of degree zero commuting with the differentials gives such a chain map
(`TopRep.gradedCochainComplexResMap`), and the statement becomes one about homogeneous cocycles on
the total modules (`TopRep.ResolutionContraction.map_gradedCohomologyClass`).

So restriction and inflation of a class built on a contracted complex, such as the class of the
diagonal tensor of a cocycle on the tensor-induced resolution of an open subgroup in Evens'
multiplicative transfer, are computed on the complex itself, without passing through the
coinduced resolution. As for the independence of these classes from the comparison map, the group
`H` is assumed locally compact.

## Main definitions

* `TopRep.ResolutionContraction.res`: the restriction of a contraction along a continuous
  homomorphism.

## Main results

* `TopRep.ResolutionContraction.map_cohomologyClass_res`: restriction along `φ` of the class of an
  invariant cocycle is its class in the restricted complex.
* `TopRep.ResolutionContraction.map_cohomologyClass`: naturality of the classes of contracted
  complexes in compatible pairs.
* `TopRep.ResolutionContraction.res_cohomologyClass`: the restriction to a subgroup.
* `TopRep.ResolutionContraction.map_gradedCohomologyClass`: naturality of the classes of
  homogeneous cocycles in compatible pairs.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Comparison Theorem 2.3.7.
* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. 108 (1963), §6, for the restriction and inflation of the multiplicative transfer.
-/

public section

open CategoryTheory

universe u v w

namespace TopRep.ResolutionContraction

open TauCeti.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G H : Type v} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (φ : H →ₜ* G)
  {X : TopRep.{max v w} k G} {J : CochainComplex (TopRep.{max v w} k G) ℕ}
  (c : ResolutionContraction X J)

/-- The **restriction of a contraction** along a continuous homomorphism `φ : H →ₜ* G`. The
augmentation, retraction and homotopy of `c` are unchanged; since they were never required to be
equivariant, they contract the restriction of `J` along `φ` onto the restriction of `X`. -/
noncomputable def res : ResolutionContraction (TopRep.res (φ : H →* G) X)
    (((resFunctor (φ : H →* G)).mapHomologicalComplex _).obj J) where
  ι := (resFunctor (φ : H →* G)).map c.ι
  proj := c.proj
  hom := c.hom
  proj_ι := c.proj_ι
  ι_proj_add_hom_d := c.ι_proj_add_hom_d
  d_hom_add_hom_d := c.d_hom_add_hom_d
  continuous_proj := (c.continuous_proj.comp
    (continuous_fst.prodMk (φ.continuous.comp continuous_snd))).congr fun p ↦ by
      simp [map_inv]
  continuous_hom n := (c.continuous_hom n |>.comp
    (continuous_fst.prodMk (φ.continuous.comp continuous_snd))).congr fun p ↦ by
      simp [map_inv]

/-- The augmentation of the restricted contraction is the restricted augmentation. -/
@[simp]
theorem res_ι : (c.res φ).ι = (resFunctor (φ : H →* G)).map c.ι :=
  (rfl)

/-- The retraction of the restricted contraction is the retraction of `c`. -/
@[simp]
theorem res_proj : (c.res φ).proj = c.proj :=
  (rfl)

/-- The homotopy of the restricted contraction is the homotopy of `c`. -/
@[simp]
theorem res_hom (n : ℕ) : (c.res φ).hom n = c.hom n :=
  (rfl)

section Homotopy

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [LocallyCompactSpace H]

/-- **Restriction of the class of a contracted complex.** Restricting along `φ : H →ₜ* G` the
class in `Hⁿ(G, X)` of a `G`-invariant cocycle `z` of `J` gives the class in
`Hⁿ(H, res φ X)` of the same cocycle, which is invariant under `H`, in the restricted complex
contracted by `c.res φ`. -/
theorem map_cohomologyClass_res {n : ℕ} (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    _root_.ContinuousCohomology.map φ (𝟙 (TopRep.res (φ : H →* G) X)) n (c.cohomologyClass z hz) =
      (c.res φ).cohomologyClass
        (Submodule.inclusion ((J.X n).ρ.invariants_le_invariants_restrict (φ : H →* G)) z) hz := by
  -- Restricting the comparison of `c` and then applying the coefficient map of `φ` is a chain map
  -- into the coinduced resolution of `res φ X` over the identity, so it induces the same map on
  -- cohomology as the comparison of `c.res φ`.
  let α := ((resFunctor (φ : H →* G)).mapHomologicalComplex _).map c.comparison ≫
    shiftedResolutionResMap φ (𝟙 (TopRep.res (φ : H →* G) X))
  have hα : (c.res φ).ι ≫ α.f 0 = d (TopRep.res (φ : H →* G) X) 0 := by
    have h := _root_.ContinuousCohomology.resolutionMap_comp_d φ
      (𝟙 (TopRep.res (φ : H →* G) X)) 0
    rw [_root_.ContinuousCohomology.resolutionMap_zero, Category.id_comp] at h
    rw [h, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, res_ι,
      ← Functor.map_comp_assoc, ι_comp_comparison_f_zero, shiftedResolutionResMap_f]
  rw [cohomologyClass_def, map_cochainClass]
  refine Eq.trans ?_ ((c.res φ).cohomologyMap_homologyπ (n := n)
    (Submodule.inclusion ((J.X n).ρ.invariants_le_invariants_restrict (φ : H →* G)) z) hz)
  rw [cohomologyMap_def, ← (c.res φ).homologyMap_eq_homologyMap_comparison α hα n,
    HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq, ← cochainClass_def]
  -- Both cochains are `resolutionMap φ (𝟙 _) (n + 1) (c.comparison.f n z)`: this is how `α` and
  -- Mathlib's `cochainsMap` are defined, and `Submodule.inclusion` does not change the element.
  simp only [α, Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f, Functor.map_comp,
    shiftedResolutionResMap_f]
  rfl

/-- **Naturality of the classes of contracted complexes in compatible pairs.** Let `c` contract
`J` onto `X` over `G`, let `c'` contract `J'` onto `Y` over `H`, and let `F` be a chain map from
the restriction of `J` along `φ : H →ₜ* G` to `J'` lying over `f : res φ X ⟶ Y`. Then the map of
the compatible pair `(φ, f)` carries the class of a `G`-invariant cocycle `z` of `J` to the class
of `F z`. -/
theorem map_cohomologyClass {Y : TopRep.{max v w} k H}
    {J' : CochainComplex (TopRep.{max v w} k H) ℕ} (c' : ResolutionContraction Y J')
    (f : TopRep.res (φ : H →* G) X ⟶ Y)
    (F : ((resFunctor (φ : H →* G)).mapHomologicalComplex _).obj J ⟶ J')
    (hF : (resFunctor (φ : H →* G)).map c.ι ≫ F.f 0 = f ≫ c'.ι) {n : ℕ}
    (z : (J.X n).ρ.invariants) (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    _root_.ContinuousCohomology.map φ f n (c.cohomologyClass z hz) =
      c'.cohomologyClass ((F.f n).hom.mapInvariantsOfRes (φ : H →* G) z)
        (d_mapInvariants_f_apply F
          (Submodule.inclusion ((J.X n).ρ.invariants_le_invariants_restrict (φ : H →* G)) z)
          hz) := by
  -- The map of `(φ, f)` is restriction along `φ` followed by the coefficient map of `f`.
  have hmap : _root_.ContinuousCohomology.map φ f n =
      _root_.ContinuousCohomology.map φ (𝟙 (TopRep.res (φ : H →* G) X)) n ≫ coeffMap f n := by
    rw [map_comp_coeffMap φ (𝟙 _) f (𝟙 X) f
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp]), coeffMap_id, Category.id_comp]
  rw [hmap, ConcreteCategory.comp_apply, map_cohomologyClass_res]
  -- `mapInvariants` applied to the inclusion of `z` and `mapInvariantsOfRes` applied to `z` are
  -- both `F z`, with the invariance proof that `ContIntertwiningMap` supplies.
  exact coeffMap_cohomologyClass (c.res φ) c' f F hF _ _

/-- **Restriction to a subgroup of the class of a contracted complex.** For a subgroup `S` of `G`,
the restriction to `S` of the class of a `G`-invariant cocycle `z` of `J` is the class of `z` in
the restricted complex. -/
theorem res_cohomologyClass (S : Subgroup G) [LocallyCompactSpace S] {n : ℕ}
    (z : (J.X n).ρ.invariants) (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    TauCeti.ContinuousCohomology.res S X n (c.cohomologyClass z hz) =
      (c.res (TauCeti.ContinuousMonoidHom.subgroupSubtype S)).cohomologyClass
        (Submodule.inclusion ((J.X n).ρ.invariants_le_invariants_restrict S.subtype) z) hz := by
  rw [TauCeti.ContinuousCohomology.res_def]
  exact c.map_cohomologyClass_res (TauCeti.ContinuousMonoidHom.subgroupSubtype S) z hz

end Homotopy

end TopRep.ResolutionContraction

namespace TopRep

namespace ResolutionContraction

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] (φ : H →ₜ* G)
  {X : TopRep.{max v w} k G} {Y : TopRep.{max v w} k H}

/-- **Naturality of the classes of homogeneous cocycles in compatible pairs.** Let `c` contract the
complex of a graded `G`-representation `M` onto `X`, and `c'` the complex of a graded
`H`-representation `M'` onto `Y`. Let `F : res φ M ⟶ M'` be of degree zero, commute with the
differentials and carry the augmentation of `c` to that of `c'` over `f : res φ X ⟶ Y`. Then the
map of the compatible pair `(φ, f)` carries the class of a homogeneous cocycle `z` of `M` fixed by
`G` to the class of `F z`. -/
theorem map_gradedCohomologyClass {M : TopRep.{max v w} k G} {ℳ : ℤ → Submodule k M.V}
    {hρ : ∀ n g x, x ∈ ℳ n → M.ρ g x ∈ ℳ n} {d : M ⟶ M}
    {hd : TauCeti.LinearMap.IsHomogeneous d.hom.toLinearMap ℳ ℳ 1} {hdd : d ≫ d = 0}
    {M' : TopRep.{max v w} k H} {ℳ' : ℤ → Submodule k M'.V}
    {hρ' : ∀ n g x, x ∈ ℳ' n → M'.ρ g x ∈ ℳ' n} {d' : M' ⟶ M'}
    {hd' : TauCeti.LinearMap.IsHomogeneous d'.hom.toLinearMap ℳ' ℳ' 1} {hdd' : d' ≫ d' = 0}
    (c : ResolutionContraction X (M.gradedCochainComplex ℳ hρ d hd hdd))
    (c' : ResolutionContraction Y (M'.gradedCochainComplex ℳ' hρ' d' hd' hdd'))
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (F : TopRep.res (φ : H →* G) M ⟶ M')
    (hF : TauCeti.LinearMap.IsHomogeneous F.hom.toLinearMap ℳ ℳ' 0)
    (hFd : (resFunctor (φ : H →* G)).map d ≫ F = F ≫ d')
    (hι : ∀ x, F.hom (c.ι.hom x).1 = (c'.ι.hom (f.hom x)).1)
    {n : ℕ} {z : M.V} (hz : z ∈ ℳ n) (hinv : ∀ g, M.ρ g z = z) (hdz : d.hom z = 0) :
    _root_.ContinuousCohomology.map φ f n (c.gradedCohomologyClass z hz hinv hdz) =
      c'.gradedCohomologyClass (F.hom z)
        (by have h := hF.map_mem hz; rw [add_zero] at h; exact h)
        (fun h ↦ by rw [← hom_comm_apply]; exact congrArg F.hom (hinv (φ h)))
        (by
          rw [← comp_apply, ← hFd, comp_apply]
          exact (congrArg F.hom hdz).trans (map_zero _)) := by
  have hf : (resFunctor (φ : H →* G)).map c.ι ≫
      (gradedCochainComplexResMap (hρ' := hρ') (hd' := hd') (hdd' := hdd') (φ : H →* G) F hF
        hFd).f 0 = f ≫ c'.ι := by
    refine ConcreteCategory.hom_ext _ _ fun x ↦
      gradedCochainComplexι_injective M' ℳ' hρ' d' hd' hdd' 0 ?_
    rw [comp_apply, comp_apply, gradedCochainComplexι_apply, gradedCochainComplexResMap_f_apply,
      gradedCochainComplexι_apply]
    exact hι x
  rw [gradedCohomologyClass_def, c.map_cohomologyClass φ c' f _ hf]
  refine Eq.trans ?_ (c'.gradedCohomologyClass_def _ _ _ _).symm
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  rw [ContIntertwiningMap.mapInvariantsOfRes_apply, gradedCochainComplexResMap_f_apply,
    gradedCochainComplexInvariant_val, gradedCochainComplexInvariant_val]

end ResolutionContraction

end TopRep
