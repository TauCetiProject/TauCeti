/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.RingTheory.Grassmannian.Chart.Triple

/-!
# The Grassmannian scheme

Let `M` be a module over a commutative ring `R` and `k` a natural number. This file glues the
standard affine charts of the Grassmannian functor `A ↦ G(k, A ⊗[R] M; A)` into a scheme
`Module.Grassmannian.scheme R M k` over `Spec R`. The module `M` lies in the universe of `R`, so
that the glued scheme and `Spec R` lie in the same category of schemes.

For `x : Fin k → M`, the chart at `x` is `Spec (ChartAlgebra R x)`, whose points over `A` are the
points of `G(k, A ⊗[R] M; A)` for which the images of the `1 ⊗ₜ x i` form a basis of the quotient
(`Module.Grassmannian.chartHomEquiv`). Inside the chart at `x`, the overlap with the chart at `y`
is the basic open set `Spec (OverlapAlgebra R x y)` of the determinant of the universal transition
matrix, and the transition isomorphism `transitionAlgEquiv R x y` identifies the overlaps read in
the two charts (`TauCeti.RingTheory.Grassmannian.Chart.Transition`). The fibre product of the
overlaps with the charts at `y` and at `z` inside the chart at `x` is `Spec` of the triple overlap
algebra `TripleAlgebra R x y z` (`Module.Grassmannian.pullbackTripleIso`), and the cyclic
isomorphisms `TripleAlgebra.cycle` between the triple overlaps satisfy the cocycle condition
(`TauCeti.RingTheory.Grassmannian.Chart.Triple`). These are the gluing data
`Module.Grassmannian.glueData`.

The gluing data are exposed, so the general API of `AlgebraicGeometry.Scheme.GlueData` applies to
the Grassmannian. The chart at `x` is the open immersion
`Module.Grassmannian.chartι R x : Spec (ChartAlgebra R x) ⟶ G(k, M)`, the morphism
`(glueData R M k).ι x` of the gluing data. The charts cover the Grassmannian
(`Module.Grassmannian.chartι_jointly_surjective`), and the charts at `x` and `y` intersect in their
overlap `Spec (OverlapAlgebra R x y)` (`Module.Grassmannian.isPullback_chartι`), where they are
identified by the transition isomorphism (`Module.Grassmannian.transition_chartι`). The structure
morphisms `Spec (ChartAlgebra R x) ⟶ Spec R` of the charts glue to the structure morphism
`Module.Grassmannian.toSpec` of the Grassmannian.

## Main definitions

* `Module.Grassmannian.pullbackTripleIso R M k x y z`: the fibre product of two overlaps inside a
  chart is `Spec` of the triple overlap algebra.
* `Module.Grassmannian.glueData R M k`: the gluing data of the standard charts.
* `Module.Grassmannian.scheme R M k`: the scheme glued from the standard charts.
* `Module.Grassmannian.toSpec R M k`: its structure morphism to `Spec R`.
* `Module.Grassmannian.chartι R x`: the open immersion of the chart at `x`.

## Main results

* `Module.Grassmannian.chartι_toSpec`: the structure morphism restricts on each chart to the
  structure morphism of the chart.
* `Module.Grassmannian.isPullback_chartι`: the charts at `x` and `y` intersect in their overlap.

## References

* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique I* (Springer, 1971), 9.7.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Module.Grassmannian

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (k : ℕ)

open ChartAlgebra TripleAlgebra

/-- Inside the chart at `x`, the fibre product of the overlaps with the charts at `y` and at `z` is
`Spec` of the triple overlap algebra `TripleAlgebra R x y z`. -/
noncomputable def pullbackTripleIso (x y z : Fin k → M) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x z)))) ≅
      Spec (.of (TripleAlgebra R x y z)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (TripleAlgebra.isPushout x y z)).isoPullback.symm

variable {R M k}

@[reassoc (attr := simp)]
theorem pullbackTripleIso_inv_fst (x y z : Fin k → M) :
    (pullbackTripleIso R M k x y z).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap (OverlapAlgebra R x y) (TripleAlgebra R x y z))) :=
  IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
theorem pullbackTripleIso_inv_snd (x y z : Fin k → M) :
    (pullbackTripleIso R M k x y z).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (inr R x y z : OverlapAlgebra R x z →+* TripleAlgebra R x y z)) :=
  IsPullback.isoPullback_hom_snd _

@[reassoc (attr := simp)]
theorem pullbackTripleIso_hom_fst (x y z : Fin k → M) :
    (pullbackTripleIso R M k x y z).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (OverlapAlgebra R x y) (TripleAlgebra R x y z))) =
      pullback.fst _ _ := by
  rw [← pullbackTripleIso_inv_fst, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
theorem pullbackTripleIso_hom_snd (x y z : Fin k → M) :
    (pullbackTripleIso R M k x y z).hom ≫ Spec.map (CommRingCat.ofHom
        (inr R x y z : OverlapAlgebra R x z →+* TripleAlgebra R x y z)) = pullback.snd _ _ := by
  rw [← pullbackTripleIso_inv_snd, Iso.hom_inv_id_assoc]

variable (R M k)

/-- The **gluing data of the Grassmannian**: the standard charts `Spec (ChartAlgebra R x)`, glued
along the overlaps `Spec (OverlapAlgebra R x y)` by the transition isomorphisms
`transitionAlgEquiv R x y`. The cocycle condition is `TripleAlgebra.cycle_cycle`. The body is
exposed so that the charts, overlaps and transition maps of the gluing data unfold to these
explicit schemes and morphisms. -/
@[expose] noncomputable def glueData : Scheme.GlueData.{u} where
  J := Fin k → M
  U x := Spec (.of (ChartAlgebra R x))
  V p := Spec (.of (OverlapAlgebra R p.1 p.2))
  f x y := Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y)))
  f_id x := by
    -- the overlap of a chart with itself is the localization away from `1`
    dsimp only [OverlapAlgebra]
    rw [transitionDet_self]
    have := localization_unit_isIso (.of (ChartAlgebra R x))
    infer_instance
  t x y := Spec.map (CommRingCat.ofHom
      (transitionAlgEquiv R x y : OverlapAlgebra R y x →+* OverlapAlgebra R x y))
  t_id x := by
    rw [transitionAlgEquiv_self]
    exact Spec.map_id _
  t' x y z := (pullbackTripleIso R M k x y z).hom ≫
    Spec.map (CommRingCat.ofHom (cycle R x y z : TripleAlgebra R y z x →+* TripleAlgebra R x y z)) ≫
      (pullbackTripleIso R M k y z x).inv
  t_fac x y z := by
    rw [← pullbackTripleIso_hom_fst]
    simp only [Category.assoc]
    rw [pullbackTripleIso_inv_snd, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext a
    exact DFunLike.congr_fun (cycle_comp_inr x y z) a
  cocycle x y z := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    have : CommRingCat.ofHom (cycle R z x y : TripleAlgebra R x y z →+* TripleAlgebra R z x y) ≫
        CommRingCat.ofHom (cycle R y z x : TripleAlgebra R z x y →+* TripleAlgebra R y z x) ≫
          CommRingCat.ofHom (cycle R x y z : TripleAlgebra R y z x →+* TripleAlgebra R x y z) =
            𝟙 _ := by
      ext a
      exact DFunLike.congr_fun (cycle_cycle x y z) a
    rw [← Category.assoc, this, Spec.map_id]
    simp
  f_open _ _ := inferInstance

/-- The **Grassmannian scheme** `G(k, M)` over `Spec R`: the scheme glued from the standard charts
`Spec (ChartAlgebra R x)` along their overlaps. The chart at `x` is the open subscheme
`(glueData R M k).ι x`, these charts cover the Grassmannian (`(glueData R M k).openCover`), and the
charts at `x` and `y` intersect in their overlap `Spec (OverlapAlgebra R x y)`
(`(glueData R M k).vPullbackConeIsLimit x y`). -/
@[expose] noncomputable def scheme : Scheme.{u} :=
  (glueData R M k).glued

/-- The **structure morphism** of the Grassmannian to `Spec R`, glued from the structure morphisms
`Spec (ChartAlgebra R x) ⟶ Spec R` of the charts. -/
noncomputable def toSpec : scheme R M k ⟶ Spec (.of R) :=
  Multicoequalizer.desc _ _ (fun x ↦ Spec.map (CommRingCat.ofHom (algebraMap R (ChartAlgebra R x))))
    fun p ↦ by
      obtain ⟨x, y⟩ := p
      rw [GlueData.diagram_fst, GlueData.diagram_snd]
      -- the structure morphisms of the two charts agree on their overlap, since the transition
      -- isomorphism is an `R`-algebra map
      have h : Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (ChartAlgebra R x))) =
            (Spec.map (CommRingCat.ofHom
                (transitionAlgEquiv R x y : OverlapAlgebra R y x →+* OverlapAlgebra R x y)) ≫
              Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R y) (OverlapAlgebra R y x)))) ≫
                Spec.map (CommRingCat.ofHom (algebraMap R (ChartAlgebra R y))) := by
        rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext a
        simp [← IsScalarTower.algebraMap_apply]
      exact h

variable {M k} in
/-- The **chart at `x`** of the Grassmannian: the open immersion
`Spec (ChartAlgebra R x) ⟶ G(k, M)` of the standard chart at `x`, that is, the morphism
`(glueData R M k).ι x` of the gluing data. -/
noncomputable def chartι (x : Fin k → M) : Spec (.of (ChartAlgebra R x)) ⟶ scheme R M k :=
  (glueData R M k).ι x

variable {R M k}

instance (x : Fin k → M) : IsOpenImmersion (chartι R x) :=
  Scheme.GlueData.ι_isOpenImmersion (glueData R M k) x

/-- On the chart at `x`, the structure morphism of the Grassmannian is the structure morphism
`Spec (ChartAlgebra R x) ⟶ Spec R` of the chart. -/
@[reassoc, simp]
theorem chartι_toSpec (x : Fin k → M) :
    chartι R x ≫ toSpec R M k =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartAlgebra R x))) :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- **The charts cover the Grassmannian.** -/
theorem chartι_jointly_surjective (z : scheme R M k) :
    ∃ (x : Fin k → M) (y : Spec (.of (ChartAlgebra R x))), chartι R x y = z :=
  (glueData R M k).ι_jointly_surjective z

/-- **The charts at `x` and at `y` intersect in their overlap.** The square formed by the inclusions
of `Spec (OverlapAlgebra R x y)` into the chart at `x` and, through the transition isomorphism, into
the chart at `y` is a pullback square over the Grassmannian. -/
theorem isPullback_chartι (x y : Fin k → M) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y))))
      (Spec.map (CommRingCat.ofHom
          (transitionAlgEquiv R x y : OverlapAlgebra R y x →+* OverlapAlgebra R x y)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R y) (OverlapAlgebra R y x))))
      (chartι R x) (chartι R y) :=
  IsPullback.of_isLimit ((glueData R M k).vPullbackConeIsLimit x y)

/-- **The charts agree on their overlap.** On the overlap of the charts at `x` and `y`, the chart at
`x` is the chart at `y` composed with the transition isomorphism. -/
@[reassoc]
theorem transition_chartι (x y : Fin k → M) :
    Spec.map (CommRingCat.ofHom
        (transitionAlgEquiv R x y : OverlapAlgebra R y x →+* OverlapAlgebra R x y)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R y) (OverlapAlgebra R y x))) ≫
        chartι R y =
      Spec.map (CommRingCat.ofHom (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y))) ≫
        chartι R x :=
  (glueData R M k).glue_condition x y

end Module.Grassmannian
