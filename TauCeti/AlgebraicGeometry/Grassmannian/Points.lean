/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cover.Open
public import TauCeti.AlgebraicGeometry.Grassmannian.Basic
public import TauCeti.AlgebraicGeometry.Scheme.AffinePoints
public import TauCeti.RingTheory.Grassmannian.Chart.Locus
public import TauCeti.RingTheory.Grassmannian.Localization

/-!
# The points of the Grassmannian scheme

Let `M` be a module over a commutative ring `R` and `k` a natural number. This file proves that the
Grassmannian scheme `Module.Grassmannian.scheme R M k`, glued from the standard charts, represents
the Grassmannian functor `A ↦ G(k, A ⊗[R] M; A)` on affine schemes over `Spec R`: for an
`R`-algebra `A`, the points `N ∈ G(k, A ⊗[R] M; A)` correspond to the morphisms
`Spec A ⟶ G(k, M)` over `Spec R` (`Module.Grassmannian.schemeHomEquiv`), naturally in `A`.

The comparison rests on `Module.Grassmannian.specMap_comp_chartι_eq_iff`: two morphisms
`Spec A ⟶ G(k, M)` through the charts at `x` and `y`, classified by `R`-algebra maps out of the
chart algebras, agree exactly when they classify the same point of `G(k, A ⊗[R] M; A)`, because
the two charts meet along their overlap. A point `N` lies in some chart over each basic open of a
cover of `Spec A` (`Module.Grassmannian.iSup_chartLocus_tmul_eq_top`), and the morphisms to these
charts glue to the morphism `Module.Grassmannian.toSchemeHom N` classifying `N`. Conversely, a
morphism over `Spec R` lands in a chart over each basic open of a cover of `Spec A`, and the points
it classifies there glue along the Zariski cover
(`Module.Grassmannian.exists_map_eq_of_isLocalized_span`).

## Main definitions

* `Module.Grassmannian.toSchemeHom N`: the morphism `Spec A ⟶ G(k, M)` classifying a point `N`.
* `Module.Grassmannian.schemeHomEquiv R M k A`: the points of `G(k, A ⊗[R] M; A)` are the
  morphisms `Spec A ⟶ G(k, M)` over `Spec R`.
* `Module.Grassmannian.homOfPoints F hF`: the morphism out of `G(k, M)` given on points by a
  family of maps `F` natural in the algebra.

## Main results

* `Module.Grassmannian.specMap_comp_chartι_eq_iff`: morphisms through two charts agree exactly when
  they classify the same point.
* `Module.Grassmannian.specMap_comp_toSchemeHom_eq_iff`: the morphism classifying `N`, restricted
  along `Spec B ⟶ Spec A`, is a morphism through a chart exactly when that chart morphism
  classifies the base change of `N` to `B`.
* `Module.Grassmannian.toSchemeHom_chartHomEquiv_id`: `chartι R x` classifies the universal point
  of `ChartAlgebra R x`.
* `Module.Grassmannian.toSchemeHom_map`: naturality of `toSchemeHom` in the algebra.
* `Module.Grassmannian.toSchemeHom_injective` and `Module.Grassmannian.exists_toSchemeHom_eq`:
  every morphism over `Spec R` classifies a unique point.
* `Module.Grassmannian.scheme_hom_ext` and `Module.Grassmannian.toSchemeHom_comp_homOfPoints`:
  morphisms out of `G(k, M)` are determined by, and can be built from, their points.
* `Module.Grassmannian.isEmpty_scheme_of_rankAtStalk_lt`, `Module.Grassmannian.isIso_toSpec_zero`,
  and `Module.Grassmannian.isIso_toSpec_of_rankAtStalk_eq`: extreme-dimension Grassmannian schemes.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor and its representability.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}
  {A B C D : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C]
  [Algebra R C] [CommRing D] [Algebra R D]

open ChartAlgebra

section Chart

-- An `R`-algebra map out of a chart which factors through the overlap with the chart at `y`.
private lemma specMap_comp_chartι_of_overlap (x y : Fin k → M)
    (φ : OverlapAlgebra R x y →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom
        ((φ.comp (IsScalarTower.toAlgHom R _ _) : ChartAlgebra R x →ₐ[R] A) :
          ChartAlgebra R x →+* A)) ≫ chartι R x =
      Spec.map (CommRingCat.ofHom
        (((φ.comp (transitionAlgEquiv R x y : OverlapAlgebra R y x →ₐ[R] _)).comp
          (IsScalarTower.toAlgHom R _ _) : ChartAlgebra R y →ₐ[R] A) :
            ChartAlgebra R y →+* A)) ≫ chartι R y := by
  simp only [AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    IsScalarTower.coe_toAlgHom]
  exact congrArg (_ ≫ ·) (transition_chartι x y).symm

/-- **Two charts meet along their overlap.** The morphisms `Spec A ⟶ G(k, M)` through the charts at
`x` and at `y` classified by `g` and `g'` agree exactly when `g` and `g'` classify the same point of
`G(k, A ⊗[R] M; A)`. -/
theorem specMap_comp_chartι_eq_iff (x y : Fin k → M) (g : ChartAlgebra R x →ₐ[R] A)
    (g' : ChartAlgebra R y →ₐ[R] A) :
    Spec.map (CommRingCat.ofHom (g : ChartAlgebra R x →+* A)) ≫ chartι R x =
        Spec.map (CommRingCat.ofHom (g' : ChartAlgebra R y →+* A)) ≫ chartι R y ↔
      (chartHomEquiv R x A g).val = (chartHomEquiv R y A g').val := by
  constructor
  · intro h
    -- the two morphisms factor through the overlap `Spec (OverlapAlgebra R x y)`
    obtain ⟨l, h₁, h₂⟩ : ∃ l : Spec (.of A) ⟶ Spec (.of (OverlapAlgebra R x y)),
        l ≫ Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y))) =
            Spec.map (CommRingCat.ofHom (g : ChartAlgebra R x →+* A)) ∧
          l ≫ Spec.map (CommRingCat.ofHom
              (transitionAlgEquiv R x y : OverlapAlgebra R y x →+* OverlapAlgebra R x y)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R y) (OverlapAlgebra R y x))) =
            Spec.map (CommRingCat.ofHom (g' : ChartAlgebra R y →+* A)) :=
      ⟨_, (isPullback_chartι x y).lift_fst _ _ h, (isPullback_chartι x y).lift_snd _ _ h⟩
    obtain ⟨φ, rfl⟩ := Spec.map_surjective l
    have e₁ : CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)) ≫ φ =
        CommRingCat.ofHom (g : ChartAlgebra R x →+* A) :=
      Spec.map_injective (by rw [Spec.map_comp]; exact h₁)
    have e₂ : CommRingCat.ofHom (algebraMap (ChartAlgebra R y) (OverlapAlgebra R y x)) ≫
        CommRingCat.ofHom
          (transitionAlgEquiv R x y : OverlapAlgebra R y x →+* OverlapAlgebra R x y) ≫ φ =
        CommRingCat.ofHom (g' : ChartAlgebra R y →+* A) :=
      Spec.map_injective (by rw [Spec.map_comp, Spec.map_comp]; exact h₂)
    -- `φ` is an `R`-algebra map, since its restriction to the chart at `x` is `g`
    let φ' : OverlapAlgebra R x y →ₐ[R] A :=
      { φ.hom with
        commutes' r := by
          simpa [← IsScalarTower.algebraMap_apply] using
            DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e₁) (algebraMap R _ r) }
    have hg : φ'.comp (IsScalarTower.toAlgHom R _ _) = g :=
      AlgHom.ext fun a ↦ DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e₁) a
    have hg' : (φ'.comp (transitionAlgEquiv R x y : OverlapAlgebra R y x →ₐ[R] _)).comp
        (IsScalarTower.toAlgHom R (ChartAlgebra R y) _) = g' :=
      AlgHom.ext fun a ↦ DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e₂) a
    rw [← hg, ← hg', ← coe_overlapHomEquiv_apply, ← coe_overlapHomEquiv_apply]
    exact (overlapHomEquiv_comp_transitionAlgEquiv x y φ').symm
  · intro h
    have hy : (chartHomEquiv R x A g).val ∈ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i) :=
      h ▸ (chartHomEquiv R y A g').property
    -- `g` and `g'` both factor through the overlap of the two charts
    let φ := (overlapHomEquiv R x y A).symm ⟨_, (chartHomEquiv R x A g).property, hy⟩
    have hφ : (overlapHomEquiv R x y A φ).val = (chartHomEquiv R x A g).val := by
      simp [φ]
    have hg : φ.comp (IsScalarTower.toAlgHom R _ _) = g :=
      (chartHomEquiv R x A).injective <| Subtype.ext <|
        (coe_overlapHomEquiv_apply x y φ).symm.trans hφ
    have hg' : (φ.comp (transitionAlgEquiv R x y : OverlapAlgebra R y x →ₐ[R] _)).comp
        (IsScalarTower.toAlgHom R (ChartAlgebra R y) _) = g' :=
      (chartHomEquiv R y A).injective <| Subtype.ext <|
        (coe_overlapHomEquiv_apply y x _).symm.trans
          ((overlapHomEquiv_comp_transitionAlgEquiv x y φ).trans (hφ.trans h))
    rw [← hg, ← hg']
    exact specMap_comp_chartι_of_overlap x y φ

/-- The morphisms `Spec D ⟶ G(k, M)` obtained from points of charts over `B` and `C` along
`f : B → D` and `f' : C → D` agree exactly when the two points have the same base change to `D`. -/
private lemma specMap_comp_specMap_comp_chartι_eq_iff {x y : Fin k → M} (f : B →ₐ[R] D)
    (f' : C →ₐ[R] D) (g : ChartAlgebra R x →ₐ[R] B) (g' : ChartAlgebra R y →ₐ[R] C) :
    Spec.map (CommRingCat.ofHom (f : B →+* D)) ≫ Spec.map (CommRingCat.ofHom (g : _ →+* B)) ≫
        chartι R x =
      Spec.map (CommRingCat.ofHom (f' : C →+* D)) ≫ Spec.map (CommRingCat.ofHom (g' : _ →+* C)) ≫
        chartι R y ↔
      map f (chartHomEquiv R x B g).val = map f' (chartHomEquiv R y C g').val := by
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom, ← AlgHom.comp_toRingHom,
    specMap_comp_chartι_eq_iff, chartHomEquiv_comp, chartHomEquiv_comp]

end Chart

section ToSchemeHom

/-- The `a : A` over whose basic open `D(a)` the point `N` lies in one of the standard charts. -/
private def chartSet (N : G(k, A ⊗[R] M; A)) : Set A :=
  {a | ∃ x : Fin k → M, a ∈ chartLocus N (fun i ↦ (1 : A) ⊗ₜ[R] x i)}

private lemma span_chartSet (N : G(k, A ⊗[R] M; A)) : Ideal.span (chartSet N) = ⊤ :=
  eq_top_iff.mpr <| (iSup_chartLocus_tmul_eq_top N).ge.trans <|
    iSup_le fun x _ ha ↦ Ideal.subset_span ⟨x, ha⟩

private lemma map_mem_chart {N : G(k, A ⊗[R] M; A)} (a : chartSet N) :
    map (IsScalarTower.toAlgHom R A (Localization.Away a.val)) N ∈
      chart (Localization.Away a.val) (fun i ↦ (1 : Localization.Away a.val) ⊗ₜ[R] a.property.choose
          i) :=
  (map_mem_chart_iff _ N _).2 <| Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ a.property.choose_spec) (IsLocalization.Away.algebraMap_isUnit a.val)

/-- The map classifying the base change of `N` to `A[1/a]` in its chart. -/
private noncomputable def chartPoint {N : G(k, A ⊗[R] M; A)} (a : chartSet N) :
    ChartAlgebra R a.property.choose →ₐ[R] Localization.Away a.val :=
  (chartHomEquiv R _ _).symm ⟨_, map_mem_chart a⟩

private lemma coe_chartHomEquiv_chartPoint {N : G(k, A ⊗[R] M; A)} (a : chartSet N) :
    (chartHomEquiv R _ _ (chartPoint a)).val =
      map (IsScalarTower.toAlgHom R A (Localization.Away a.val)) N := by
  simp [chartPoint]

/-- The basic opens of `Spec A` over which `N` lies in a chart. -/
private noncomputable def chartCover (N : G(k, A ⊗[R] M; A)) : (Spec (.of A)).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of A) (fun a : chartSet N ↦ a.val)
    (by rw [Subtype.range_coe]; exact span_chartSet N)).openCover

/-- The **morphism to the Grassmannian scheme classifying a point**. For an `R`-algebra `A` and
`N ∈ G(k, A ⊗[R] M; A)`, this is the morphism `Spec A ⟶ G(k, M)` which, over each basic open of
`Spec A` on which `N` lies in the chart at `x`, is the morphism to that chart classifying `N`. It is
characterised by `Module.Grassmannian.specMap_comp_toSchemeHom_eq_iff`, and
`Module.Grassmannian.schemeHomEquiv` shows that every morphism over `Spec R` arises from a unique
point. -/
noncomputable def toSchemeHom (N : G(k, A ⊗[R] M; A)) : Spec (.of A) ⟶ scheme R M k :=
  (chartCover N).glueMorphisms
    (fun a : chartSet N ↦
      Spec.map (CommRingCat.ofHom (chartPoint a : _ →+* Localization.Away a.val)) ≫
        chartι R a.property.choose) fun (a b : chartSet N) ↦ by
    -- the pullback of two basic opens is `Spec (A[1/a] ⊗[A] A[1/b])`
    refine (cancel_epi
      (pullbackSpecIso A (Localization.Away a.val) (Localization.Away b.val)).inv).mp ?_
    let f₁ : Localization.Away a.val →ₐ[R] Localization.Away a.val ⊗[A] Localization.Away b.val :=
      Algebra.TensorProduct.includeLeft
    let f₂ : Localization.Away b.val →ₐ[R] Localization.Away a.val ⊗[A] Localization.Away b.val :=
      Algebra.TensorProduct.includeRight.restrictScalars R
    have e₁ : (pullbackSpecIso A (Localization.Away a.val) (Localization.Away b.val)).inv ≫
        pullback.fst ((chartCover N).f a) ((chartCover N).f b) =
          Spec.map (CommRingCat.ofHom (f₁ : _ →+* _)) := pullbackSpecIso_inv_fst _ _ _
    have e₂ : (pullbackSpecIso A (Localization.Away a.val) (Localization.Away b.val)).inv ≫
        pullback.snd ((chartCover N).f a) ((chartCover N).f b) =
          Spec.map (CommRingCat.ofHom (f₂ : _ →+* _)) := pullbackSpecIso_inv_snd _ _ _
    -- both points are the base change of `N` along `A → A[1/a] ⊗[A] A[1/b]`
    have hpts : map f₁ (chartHomEquiv R _ _ (chartPoint a)).val =
        map f₂ (chartHomEquiv R _ _ (chartPoint b)).val := by
      rw [coe_chartHomEquiv_chartPoint, coe_chartHomEquiv_chartPoint, ← map_comp, ← map_comp]
      congr 1
      exact AlgHom.ext fun r ↦
        DFunLike.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap) r
    exact ((reassoc_of% e₁) _).trans <|
      ((specMap_comp_specMap_comp_chartι_eq_iff f₁ f₂ _ _).2 hpts).trans
        ((reassoc_of% e₂) _).symm

private lemma specMap_comp_toSchemeHom_chartSet {N : G(k, A ⊗[R] M; A)} (a : chartSet N) :
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫ toSchemeHom N =
      Spec.map (CommRingCat.ofHom (chartPoint a : _ →+* Localization.Away a.val)) ≫
        chartι R a.property.choose :=
  (chartCover N).ι_glueMorphisms _ _ a

-- Over a ring `C` receiving compatible maps from `A[1/a]`, `a ∈ chartSet N`, and from `B`, the
-- morphisms in `specMap_comp_toSchemeHom_eq_iff` become morphisms through charts.
private lemma specMap_comp_toSchemeHom_eq_iff_of_comp {N : G(k, A ⊗[R] M; A)} (a : chartSet N)
    (f : A →ₐ[R] B) (u : Localization.Away a.val →ₐ[R] C) (v : B →ₐ[R] C)
    (huv : u.comp (IsScalarTower.toAlgHom R A _) = v.comp f) (x : Fin k → M)
    (g : ChartAlgebra R x →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (v : B →+* C)) ≫ Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫
        toSchemeHom N =
      Spec.map (CommRingCat.ofHom (v : B →+* C)) ≫
        Spec.map (CommRingCat.ofHom (g : ChartAlgebra R x →+* B)) ≫ chartι R x ↔
      map v (map f N) = map v (chartHomEquiv R x B g).val := by
  have hl : Spec.map (CommRingCat.ofHom (v : B →+* C)) ≫
      Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ toSchemeHom N =
        Spec.map (CommRingCat.ofHom (u : _ →+* C)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫ toSchemeHom N
              := by
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext y
    exact (DFunLike.congr_fun huv y).symm
  replace hl := hl.trans (congrArg (_ ≫ ·) (specMap_comp_toSchemeHom_chartSet a))
  refine (Eq.congr_left hl).trans <| (specMap_comp_specMap_comp_chartι_eq_iff u v _ g).trans ?_
  rw [coe_chartHomEquiv_chartPoint, ← map_comp, huv, map_comp]

/-- **The morphism classifying a point is characterised by its restrictions to the charts.** For
`f : A →ₐ[R] B`, the composite `Spec B ⟶ Spec A ⟶ G(k, M)` of the morphism classifying `N` is the
morphism through the chart at `x` classified by `g` exactly when `g` classifies the base change of
`N` to `B`. -/
theorem specMap_comp_toSchemeHom_eq_iff (N : G(k, A ⊗[R] M; A)) (f : A →ₐ[R] B) (x : Fin k → M)
    (g : ChartAlgebra R x →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ toSchemeHom N =
        Spec.map (CommRingCat.ofHom (g : ChartAlgebra R x →+* B)) ≫ chartι R x ↔
      map f N = (chartHomEquiv R x B g).val := by
  have hs : Ideal.span (f '' chartSet N) = ⊤ := by
    rw [← Ideal.map_span, span_chartSet, Ideal.map_top]
  -- over each `B[1/f a]`, `a ∈ chartSet N`, both sides are morphisms through charts
  have key (r : f '' chartSet N) :
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r.val))) ≫
          Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ toSchemeHom N =
        Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r.val))) ≫
          Spec.map (CommRingCat.ofHom (g : ChartAlgebra R x →+* B)) ≫ chartι R x ↔
      map (IsScalarTower.toAlgHom R B (Localization.Away r.val)) (map f N) =
        map (IsScalarTower.toAlgHom R B (Localization.Away r.val)) (chartHomEquiv R x B g).val := by
    obtain ⟨_, a, ha, rfl⟩ := r
    exact specMap_comp_toSchemeHom_eq_iff_of_comp ⟨a, ha⟩ f (Localization.awayMapₐ f a)
      (IsScalarTower.toAlgHom R B _) (AlgHom.ext fun _ ↦ by simp [IsLocalization.Away.map]) x g
  constructor
  · intro h
    exact eq_of_isLocalized_span (B := fun r : f '' chartSet N ↦ Localization.Away r.val) _ hs
      fun r ↦ (key r).1 (congrArg (_ ≫ ·) h)
  · intro h
    exact TauCeti.AlgebraicGeometry.Spec.hom_ext_of_span_eq_top _ hs fun r ↦ (key r).2 (by rw [h])

/-- The morphism classifying a point of the chart at `x` is the morphism to that chart. -/
@[simp]
theorem toSchemeHom_chartHomEquiv (x : Fin k → M) (g : ChartAlgebra R x →ₐ[R] A) :
    toSchemeHom (chartHomEquiv R x A g).val =
      Spec.map (CommRingCat.ofHom (g : ChartAlgebra R x →+* A)) ≫ chartι R x := by
  have h := (specMap_comp_toSchemeHom_eq_iff (chartHomEquiv R x A g).val (AlgHom.id R A) x g).2
    (map_id k (CommAlgCat.of R A) _)
  -- `Spec.map` of the identity of `A` is the identity of `Spec A`
  rwa [show CommRingCat.ofHom ((AlgHom.id R A : A →ₐ[R] A) : A →+* A) = 𝟙 _ from rfl,
    Spec.map_id, Category.id_comp] at h

/-- The chart open immersion `chartι R x` classifies the universal point of `ChartAlgebra R x`. -/
theorem toSchemeHom_chartHomEquiv_id (x : Fin k → M) :
    toSchemeHom (chartHomEquiv R x (ChartAlgebra R x) (AlgHom.id R _)).val = chartι R x := by
  simp

/-- **Naturality.** The morphism classifying the base change of `N` along `f : A →ₐ[R] B` is the
composite of `Spec B ⟶ Spec A` with the morphism classifying `N`. -/
theorem toSchemeHom_map (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom (map f N) = Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ toSchemeHom N := by
  refine TauCeti.AlgebraicGeometry.Spec.hom_ext_of_span_eq_top _ (span_chartSet (map f N))
    fun b ↦ ?_
  rw [specMap_comp_toSchemeHom_chartSet, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  refine ((specMap_comp_toSchemeHom_eq_iff N ((IsScalarTower.toAlgHom R B _).comp f) _ _).2 ?_).symm
  rw [map_comp, coe_chartHomEquiv_chartPoint]

/-- The morphism classifying a point lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_toSpec (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  refine TauCeti.AlgebraicGeometry.Spec.hom_ext_of_span_eq_top _ (span_chartSet N) fun a ↦ ?_
  calc _ = Spec.map (CommRingCat.ofHom (chartPoint a : _ →+* Localization.Away a.val)) ≫
        chartι R a.property.choose ≫ toSpec R M k :=
        (reassoc_of% specMap_comp_toSchemeHom_chartSet a) _
    _ = Spec.map (CommRingCat.ofHom (chartPoint a : _ →+* Localization.Away a.val)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ChartAlgebra R a.property.choose))) :=
        congrArg (_ ≫ ·) (chartι_toSpec _)
    _ = _ := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext r
      simp [← IsScalarTower.algebraMap_apply]

/-- Distinct points are classified by distinct morphisms. -/
theorem toSchemeHom_injective :
    Function.Injective (toSchemeHom : G(k, A ⊗[R] M; A) → (Spec (.of A) ⟶ scheme R M k)) := by
  intro N N' h
  refine eq_of_isLocalized_span (B := fun a : chartSet N ↦ Localization.Away a.val) _
    (span_chartSet N) fun a ↦ ?_
  rw [← coe_chartHomEquiv_chartPoint a]
  exact ((specMap_comp_toSchemeHom_eq_iff N' _ _ _).1
    (h ▸ specMap_comp_toSchemeHom_chartSet a)).symm

/-- The elements `a : A` such that a morphism `Spec A ⟶ G(k, M)` over `Spec R` restricts on the
basic open `D(a)` to a morphism into a chart generate the unit ideal. -/
private lemma span_factorsThroughChart_eq_top (h : Spec (.of A) ⟶ scheme R M k)
    (hh : h ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Ideal.span {a : A | ∃ (x : Fin k → M) (g : ChartAlgebra R x →ₐ[R] Localization.Away a),
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ h =
        Spec.map (CommRingCat.ofHom (g : _ →+* Localization.Away a)) ≫ chartι R x} = ⊤ := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hs
  let p : Spec (.of A) := ⟨m, hm.isPrime⟩
  obtain ⟨x, y, hy⟩ := chartι_jointly_surjective (h p)
  -- a basic open `D(a)` around `p` on which `h` lands in the chart at `x`
  obtain ⟨_, ⟨a, rfl⟩, hpa, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := p) (u := h ⁻¹' Set.range (chartι R x)) ⟨y, hy⟩
      ((chartι R x).isOpenEmbedding.isOpen_range.preimage h.continuous)
  have hrange :
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ h) ⊆
        Set.range (chartι R x) := by
    rintro _ ⟨q, rfl⟩
    exact hsub
      ((PrimeSpectrum.localization_away_comap_range (Localization.Away a) a).le ⟨q, rfl⟩)
  -- the lift of `h` to the chart is `Spec` of an `R`-algebra map
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift (chartι R x) _ hrange)
  have hφR : CommRingCat.ofHom (algebraMap R (ChartAlgebra R x)) ≫ φ =
      CommRingCat.ofHom (algebraMap R (Localization.Away a)) := by
    refine Spec.map_injective ?_
    have h₁ : Spec.map φ ≫ chartι R x = _ :=
      (congrArg (· ≫ chartι R x) hφ).trans
        (IsOpenImmersion.lift_fac (chartι R x) _ hrange)
    calc _ = Spec.map φ ≫ chartι R x ≫ toSpec R M k := by
          rw [Spec.map_comp, chartι_toSpec]
      _ = _ := by
        rw [reassoc_of% h₁, hh, ← Spec.map_comp]
        congr 1
  let g : ChartAlgebra R x →ₐ[R] Localization.Away a :=
    { φ.hom with commutes' := fun r ↦ DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hφR) r }
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hpa (hsm (Ideal.subset_span
    ⟨x, g, (IsOpenImmersion.lift_fac (chartι R x) _ hrange).symm.trans
      (congrArg (· ≫ chartι R x) hφ.symm)⟩))

/-- Every morphism `Spec A ⟶ G(k, M)` over `Spec R` classifies a point. -/
theorem exists_toSchemeHom_eq (h : Spec (.of A) ⟶ scheme R M k)
    (hh : h ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ N : G(k, A ⊗[R] M; A), toSchemeHom N = h := by
  -- the `a : A` over whose basic open `h` is a morphism to a chart
  let s : Set A := {a | ∃ (x : Fin k → M) (g : ChartAlgebra R x →ₐ[R] Localization.Away a),
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) ≫ h =
      Spec.map (CommRingCat.ofHom (g : _ →+* Localization.Away a)) ≫ chartι R x}
  have hs : Ideal.span s = ⊤ := span_factorsThroughChart_eq_top h hh
  -- over each `D(a)`, `a ∈ s`, the morphism `h` classifies a point; these points glue
  let x (r : s) : Fin k → M := r.property.choose
  let g (r : s) : ChartAlgebra R (x r) →ₐ[R] Localization.Away r.val
      := r.property.choose_spec.choose
  have hg (r : s) : Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away r.val))) ≫ h =
      Spec.map (CommRingCat.ofHom (g r : _ →+* Localization.Away r.val)) ≫ chartι R (x r) :=
    r.property.choose_spec.choose_spec
  have hcompat (r r' : s) :
      map (Algebra.TensorProduct.includeLeft :
          Localization.Away r.val →ₐ[R] Localization.Away r.val ⊗[A] Localization.Away r'.val)
          (chartHomEquiv R (x r) _ (g r)).val =
        map ((Algebra.TensorProduct.includeRight : Localization.Away r'.val →ₐ[A]
          Localization.Away r.val ⊗[A] Localization.Away r'.val).restrictScalars R)
          (chartHomEquiv R (x r') _ (g r')).val := by
    refine (specMap_comp_specMap_comp_chartι_eq_iff _ _ (g r) (g r')).1 ?_
    refine (congrArg (_ ≫ ·) (hg r).symm).trans <| Eq.trans ?_ (congrArg (_ ≫ ·) (hg r'))
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact DFunLike.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap) a
  obtain ⟨N, hN⟩ := exists_map_eq_of_isLocalized_span (B := fun r : s ↦ Localization.Away r.val) s
    (fun r ↦ (chartHomEquiv R (x r) _ (g r)).val) hs hcompat
  exact ⟨N, TauCeti.AlgebraicGeometry.Spec.hom_ext_of_span_eq_top s hs fun r ↦
    ((specMap_comp_toSchemeHom_eq_iff N _ _ (g r)).2 (hN r)).trans (hg r).symm⟩

end ToSchemeHom

variable (R M k) in
/-- **The universal property of the Grassmannian scheme.** For an `R`-algebra `A`, the points of
`G(k, A ⊗[R] M; A)` are in bijection with the morphisms `Spec A ⟶ G(k, M)` over `Spec R`, by
`Module.Grassmannian.toSchemeHom`. The bijection is natural in `A`
(`Module.Grassmannian.toSchemeHom_map`). -/
noncomputable def schemeHomEquiv (A : Type u) [CommRing A] [Algebra R A] :
    G(k, A ⊗[R] M; A) ≃ {h : Spec (.of A) ⟶ scheme R M k //
      h ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))} :=
  Equiv.ofBijective (fun N ↦ ⟨toSchemeHom N, toSchemeHom_toSpec N⟩)
    ⟨fun _ _ h ↦ toSchemeHom_injective (congrArg Subtype.val h),
      fun h ↦ (exists_toSchemeHom_eq h.val h.property).imp fun _ hN ↦ Subtype.ext hN⟩

@[simp]
theorem coe_schemeHomEquiv_apply (N : G(k, A ⊗[R] M; A)) :
    (schemeHomEquiv R M k A N : Spec (.of A) ⟶ scheme R M k) = toSchemeHom N :=
  (rfl)

@[simp]
theorem toSchemeHom_schemeHomEquiv_symm_apply
    (h : {h : Spec (.of A) ⟶ scheme R M k //
      h ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))}) :
    toSchemeHom ((schemeHomEquiv R M k A).symm h) = h.val :=
  congrArg Subtype.val ((schemeHomEquiv R M k A).apply_symm_apply h)

section HomOfPoints

variable {X : Scheme.{u}}

/-- **Morphisms out of the Grassmannian are determined by its points.** Two morphisms out of
`G(k, M)` which agree after composition with the morphism classifying every point over every
`R`-algebra are equal. -/
theorem scheme_hom_ext {f g : scheme R M k ⟶ X}
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)),
      toSchemeHom N ≫ f = toSchemeHom N ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall_spec fun B a ↦ ?_
  -- make `B` an `R`-algebra through `a`, so that `a` classifies a point over `B`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R M k)
  let _ : Algebra R B := φ.hom.toAlgebra
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  exact h B N

/-- The morphism `Spec A ⟶ X` assigned by `F` to the point classified by `a : Spec A ⟶ G(k, M)`
over `Spec R`. The algebra structure on `A` is an explicit argument, so that
`homOfPointsAux_congr` can compare different choices. -/
private noncomputable def homOfPointsAux
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → (Spec (.of A) ⟶ X))
    (A : Type u) [CommRing A] (_ : Algebra R A) (a : Spec (.of A) ⟶ scheme R M k)
    (ha : a ≫ toSpec R M k = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Spec (.of A) ⟶ X :=
  F A ((schemeHomEquiv R M k A).symm ⟨a, ha⟩)

-- `homOfPointsAux` depends on the algebra structure on `A` only through its equality class.
private lemma homOfPointsAux_congr
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → (Spec (.of A) ⟶ X))
    (A : Type u) [CommRing A] (i j : Algebra R A) (h : i = j) (a : Spec (.of A) ⟶ scheme R M k)
    (ha ha') : homOfPointsAux F A i a ha = homOfPointsAux F A j a ha' := by
  subst h
  rfl

/-- The map of affine points underlying `homOfPoints`: the algebra structure of `A` over `R` is
read off from the composite `Spec A ⟶ G(k, M) ⟶ Spec R`. -/
private noncomputable def homOfPointsPoint
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → (Spec (.of A) ⟶ X))
    {A : CommRingCat.{u}} (a : Spec A ⟶ scheme R M k) : Spec A ⟶ X :=
  letI : Algebra R A := (Spec.preimage (a ≫ toSpec R M k)).hom.toAlgebra
  homOfPointsAux F A ‹_› a (Spec.map_preimage _).symm

private lemma homOfPointsPoint_toSchemeHom
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → (Spec (.of A) ⟶ X))
    {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    homOfPointsPoint F (toSchemeHom N) = F A N := by
  have hφ : (Spec.preimage (toSchemeHom N ≫ toSpec R M k)).hom = algebraMap R A := by
    rw [toSchemeHom_toSpec, Spec.preimage_map, CommRingCat.hom_ofHom]
  have hi : (Spec.preimage (toSchemeHom N ≫ toSpec R M k)).hom.toAlgebra = ‹Algebra R A› :=
    Algebra.algebra_ext _ _ fun r ↦ DFunLike.congr_fun hφ r
  unfold homOfPointsPoint
  rw [homOfPointsAux_congr F A _ _ hi _ _ (toSchemeHom_toSpec N), homOfPointsAux]
  congr 1
  exact (Equiv.symm_apply_eq _).2 (Subtype.ext (coe_schemeHomEquiv_apply N).symm)

/-- `homOfPointsPoint` is natural in the affine scheme when `F` is natural in the algebra. -/
private lemma homOfPointsPoint_comp
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → (Spec (.of A) ⟶ X))
    (hF : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)),
      F B (map f N) = Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ F A N)
    {B C : CommRingCat.{u}} (ψ : Spec C ⟶ Spec B) (a : Spec B ⟶ scheme R M k) :
    homOfPointsPoint F (ψ ≫ a) = ψ ≫ homOfPointsPoint F a := by
  -- give `B` and `C` the algebra structures over `R` read off from `a` and `ψ ≫ a`; with them,
  -- `χ` is an `R`-algebra map `χ'`
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ toSpec R M k)
  obtain ⟨χ, rfl⟩ := Spec.map_surjective ψ
  let _ : Algebra R B := φ.hom.toAlgebra
  let _ : Algebra R C := (χ.hom.comp φ.hom).toAlgebra
  let χ' : B →ₐ[R] C := { χ.hom with commutes' := fun _ ↦ rfl }
  obtain ⟨N, rfl⟩ := exists_toSchemeHom_eq (A := B) a hφ.symm
  have h : Spec.map χ ≫ toSchemeHom N = toSchemeHom (map χ' N) := (toSchemeHom_map χ' N).symm
  rw [h, homOfPointsPoint_toSchemeHom, homOfPointsPoint_toSchemeHom, hF]
  -- `χ'` has underlying ring map `χ`
  rfl

/-- **A morphism out of the Grassmannian from its points.** A family of maps `F A` from the
points of `G(k, M)` over each `R`-algebra `A` to the morphisms `Spec A ⟶ X`, natural in `A`,
is composition with a unique morphism `G(k, M) ⟶ X` (`toSchemeHom_comp_homOfPoints`,
`scheme_hom_ext`). -/
noncomputable def homOfPoints
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → (Spec (.of A) ⟶ X))
    (hF : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)),
      F B (map f N) = Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ F A N) :
    scheme R M k ⟶ X :=
  Scheme.homOfAffinePoints (homOfPointsPoint F) (homOfPointsPoint_comp F hF)

/-- **`homOfPoints` on points.** The morphism classifying `N` over an `R`-algebra `A`, composed
with `homOfPoints F hF`, is `F A N`. -/
@[reassoc (attr := simp)]
theorem toSchemeHom_comp_homOfPoints
    (F : ∀ (A : Type u) [CommRing A] [Algebra R A], G(k, A ⊗[R] M; A) → (Spec (.of A) ⟶ X))
    (hF : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (f : A →ₐ[R] B) (N : G(k, A ⊗[R] M; A)),
      F B (map f N) = Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ F A N)
    {A : Type u} [CommRing A] [Algebra R A] (N : G(k, A ⊗[R] M; A)) :
    toSchemeHom N ≫ homOfPoints F hF = F A N :=
  (Scheme.comp_homOfAffinePoints _ _ _).trans (homOfPointsPoint_toSchemeHom F N)

end HomOfPoints

section Extreme

/-- When `M` is finite flat over `R` and has rank strictly less than `k` at every prime of `R`,
the Grassmannian scheme `G(k, M)` is empty. -/
theorem isEmpty_scheme_of_rankAtStalk_lt [Module.Finite R M] [Module.Flat R M]
    (h : ∀ p, Module.rankAtStalk (R := R) M p < k) : IsEmpty (scheme R M k) := by
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨x, y, -⟩ := chartι_jointly_surjective z
  let B := ChartAlgebra R x ⧸ y.asIdeal
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr y.isPrime.ne_top
  obtain ⟨q⟩ := PrimeSpectrum.nonempty_iff_nontrivial.mpr ‹Nontrivial B›
  have hlt : Module.rankAtStalk (R := B) (B ⊗[R] M) q < k := by
    rw [Module.rankAtStalk_baseChange]
    exact h _
  exact (isEmpty_of_rankAtStalk_lt (R := B) (M := B ⊗[R] M) ⟨q, hlt⟩).false
    (chartHomEquiv R x B (Ideal.Quotient.mkₐ R y.asIdeal)).val

/-- If `G(k, A ⊗[R] M; A)` is a singleton for every `R`-algebra `A`, then the structure morphism
`toSpec R M k : G(k, M) ⟶ Spec R` is an isomorphism. -/
theorem isIso_toSpec_of_unique
    (hU : ∀ (A : Type u) [CommRing A] [Algebra R A], Unique G(k, A ⊗[R] M; A)) :
    IsIso (toSpec R M k) := by
  refine ⟨toSchemeHom (hU R).default, ?_, ?_⟩
  · refine (chartOpenCover R M k).hom_ext _ _ fun x ↦ ?_
    dsimp only [chartOpenCover]
    rw [chartι_toSpec_assoc, ← IsScalarTower.coe_toAlgHom R R (ChartAlgebra R x),
      ← toSchemeHom_map, Category.comp_id, ← toSchemeHom_chartHomEquiv_id x]
    let _ := hU (ChartAlgebra R x)
    exact congrArg toSchemeHom (Subsingleton.elim _ _)
  · rw [toSchemeHom_toSpec, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- For every module `M`, the structure morphism `G(0, M) ⟶ Spec R` is an isomorphism. -/
instance isIso_toSpec_zero : IsIso (toSpec R M 0) :=
  isIso_toSpec_of_unique fun _ _ _ ↦ uniqueZero

/-- When `M` is finite projective over `R` of constant rank `n`, the structure morphism
`G(n, M) ⟶ Spec R` is an isomorphism. -/
theorem isIso_toSpec_of_rankAtStalk_eq [Module.Finite R M] [Module.Projective R M] {n : ℕ}
    (h : ∀ p, Module.rankAtStalk (R := R) M p = n) : IsIso (toSpec R M n) :=
  isIso_toSpec_of_unique fun A _ _ ↦ uniqueOfRankAtStalkEq fun q ↦ by
    rw [Module.rankAtStalk_baseChange]
    exact h _

end Extreme

end Module.Grassmannian
