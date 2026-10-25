/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Comparison

/-!
# Continuous cohomology computed from a contracted complex

Let `J` be a complex of topological `G`-representations with a contraction
`c : TopRep.ResolutionContraction X J` onto `X`, whose maps need not be equivariant. The comparison
`c.comparison : J ⟶ TopRep.resolution' X` induces a map on the cohomology of invariants

```text
c.cohomologyMap n : Hⁿ(Jᴳ) ⟶ Hⁿ(G, X),
```

and every `G`-invariant cocycle `z` of `J` has a class `c.cohomologyClass z` in Mathlib's
continuous cohomology: the class of the homogeneous cocycle into which the comparison carries `z`,
which is also the image of the class of `z` under `c.cohomologyMap`
(`TopRep.ResolutionContraction.cohomologyMap_homologyπ`). This is how a cocycle on a complex built
from other resolutions, such as the diagonal tensor of a cocycle on the tensor-induced resolution
of an open subgroup in Evens' multiplicative transfer, is read as a continuous cohomology class.

Over a locally compact group the comparison is unique up to homotopy, which makes these maps
canonical:

* they do not depend on the contraction, only on its augmentation
  (`TopRep.ResolutionContraction.cohomologyMap_eq_of_ι_eq`);
* they are natural in chain maps of contracted complexes lying over a coefficient morphism
  (`TopRep.ResolutionContraction.cohomologyMap_comp_coeffMap`); in particular a chain map over
  the identity of `X` preserves classes (`TopRep.ResolutionContraction.cohomologyClass_map`);
* for the coinduced resolution contracted by evaluation at `1`, they are the identity and the
  ordinary class map (`TopRep.cohomologyMap_resolutionContraction`,
  `TopRep.cohomologyClass_resolutionContraction`).

Already without local compactness, the class is linear in the cocycle and cohomologous invariant
cocycles have the same class (`TopRep.ResolutionContraction.cohomologyClass_eq_of_sub_eq_d`).

## Main definitions

* `TopRep.ResolutionContraction.cohomologyMap`: the map `Hⁿ(Jᴳ) ⟶ Hⁿ(G, X)` induced by the
  comparison.
* `TopRep.ResolutionContraction.cohomologyClass`: the class in `Hⁿ(G, X)` of an invariant cocycle
  of `J`.

## Main results

* `TopRep.ResolutionContraction.cohomologyMap_homologyπ`: the class of an invariant cocycle is the
  image of its class in `Hⁿ(Jᴳ)`.
* `TopRep.ResolutionContraction.cohomologyClass_eq_of_sub_eq_d`: cohomologous invariant cocycles
  have the same class.
* `TopRep.ResolutionContraction.cohomologyMap_eq_of_ι_eq` and
  `TopRep.ResolutionContraction.cohomologyClass_eq_of_ι_eq`: independence of the contraction.
* `TopRep.ResolutionContraction.cohomologyMap_comp_coeffMap`,
  `TopRep.ResolutionContraction.homologyMap_comp_cohomologyMap`,
  `TopRep.ResolutionContraction.coeffMap_cohomologyClass` and
  `TopRep.ResolutionContraction.cohomologyClass_map`: naturality in the contracted complex and in
  the coefficients.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Comparison Theorem 2.3.7.
* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer. Math.
  Soc. 108 (1963), §§2–5.
-/

public section

open CategoryTheory

namespace TopRep

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G]

section ChainMap

variable {J J' : CochainComplex (TopRep.{w} k G) ℕ}

/-- A chain map of complexes of topological representations carries an invariant cocycle to an
invariant cocycle. -/
theorem d_mapInvariants_f_apply (f : J ⟶ J') {n : ℕ} (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    (J'.d n (n + 1)).hom ((f.f n).hom.mapInvariants z : (J'.X n).V) = 0 := by
  rw [ContIntertwiningMap.mapInvariants_apply, ← ConcreteCategory.comp_apply, f.comm,
    ConcreteCategory.comp_apply, hz, map_zero]

/-- On the cohomology of invariants, a chain map `f : J ⟶ J'` carries the class of an invariant
cocycle `z` to the class of `f z`. -/
@[simp]
theorem homologyMap_homologyπ_cyclesMkOfEq (f : J ⟶ J') {n : ℕ} (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    HomologicalComplex.homologyMap (((invariantsFunctor k G).mapHomologicalComplex _).map f) n
        ((((invariantsFunctor k G).mapHomologicalComplex _).obj J).homologyπ n
          ((((invariantsFunctor k G).mapHomologicalComplex _).obj J).cyclesMkOfEq z (n + 1)
            (CochainComplex.next ℕ n) (Subtype.ext hz))) =
      (((invariantsFunctor k G).mapHomologicalComplex _).obj J').homologyπ n
        ((((invariantsFunctor k G).mapHomologicalComplex _).obj J').cyclesMkOfEq
          ((f.f n).hom.mapInvariants z) (n + 1) (CochainComplex.next ℕ n)
          (Subtype.ext (d_mapInvariants_f_apply f z hz))) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply HomologicalComplex.iCycles_injective
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    HomologicalComplex.iCycles_cyclesMkOfEq, HomologicalComplex.iCycles_cyclesMkOfEq]
  -- The invariants functor maps a morphism to its restriction to invariant elements.
  rfl

end ChainMap

variable [TopologicalSpace G] [IsTopologicalGroup G]

namespace ResolutionContraction

variable {X : TopRep.{max v w} k G} {J : CochainComplex (TopRep.{max v w} k G) ℕ}
  (c : ResolutionContraction X J)

/-- The **map `Hⁿ(Jᴳ) ⟶ Hⁿ(G, X)` of a contracted complex**: the map induced by the comparison
`c.comparison : J ⟶ TopRep.resolution' X` on the cohomology of invariants. -/
noncomputable def cohomologyMap (n : ℕ) :
    (((invariantsFunctor k G).mapHomologicalComplex _).obj J).homology n ⟶
      continuousCohomology n X :=
  HomologicalComplex.homologyMap
    (((invariantsFunctor k G).mapHomologicalComplex _).map c.comparison) n

/-- The defining equation of `cohomologyMap`: it is the map on the cohomology of invariants
induced by the comparison. -/
theorem cohomologyMap_def (n : ℕ) :
    c.cohomologyMap n = HomologicalComplex.homologyMap
      (((invariantsFunctor k G).mapHomologicalComplex _).map c.comparison) n :=
  (rfl)

/-- The comparison carries an invariant cocycle of `J` to a homogeneous cocycle of `X`. -/
theorem d_mapInvariants_comparison_f {n : ℕ} (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    ((homogeneousCochains X).d n (n + 1)).hom ((c.comparison.f n).hom.mapInvariants z) = 0 := by
  apply Subtype.ext
  rw [homogeneousCochains.d_apply, ContIntertwiningMap.mapInvariants_apply, d_comparison_f_apply,
    hz, map_zero, ZeroMemClass.coe_zero]

/-- The **class in `Hⁿ(G, X)` of an invariant cocycle** `z` of the contracted complex `J`: the
class of the homogeneous cocycle into which the comparison carries `z`. -/
noncomputable def cohomologyClass {n : ℕ} (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) : continuousCohomology n X :=
  X.cochainClass n ((c.comparison.f n).hom.mapInvariants z) (c.d_mapInvariants_comparison_f z hz)

/-- The defining equation of `cohomologyClass`. -/
theorem cohomologyClass_def {n : ℕ} (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    c.cohomologyClass z hz =
      X.cochainClass n ((c.comparison.f n).hom.mapInvariants z)
        (c.d_mapInvariants_comparison_f z hz) :=
  (rfl)

/-- **The class of an invariant cocycle is its image under the cohomology map**: `cohomologyMap`
sends the class of `z` in `Hⁿ(Jᴳ)` to `c.cohomologyClass z`. -/
@[simp]
theorem cohomologyMap_homologyπ {n : ℕ} (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    c.cohomologyMap n ((((invariantsFunctor k G).mapHomologicalComplex _).obj J).homologyπ n
        ((((invariantsFunctor k G).mapHomologicalComplex _).obj J).cyclesMkOfEq z (n + 1)
          (CochainComplex.next ℕ n) (Subtype.ext hz))) =
      c.cohomologyClass z hz :=
  (homologyMap_homologyπ_cyclesMkOfEq c.comparison z hz).trans (cochainClass_def _ _ _ _).symm

/-- The class of a sum of invariant cocycles is the sum of their classes. -/
@[simp]
theorem cohomologyClass_add {n : ℕ} (z z' : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0)
    (hz' : (J.d n (n + 1)).hom (z' : (J.X n).V) = 0) :
    c.cohomologyClass (z + z') (by rw [Submodule.coe_add, map_add, hz, hz', add_zero]) =
      c.cohomologyClass z hz + c.cohomologyClass z' hz' := by
  rw [cohomologyClass_def, cohomologyClass_def, cohomologyClass_def, ← cochainClass_add]
  congr 1
  simp only [map_add]

/-- The class of the zero cocycle is zero. -/
@[simp]
theorem cohomologyClass_zero {n : ℕ} :
    c.cohomologyClass (0 : (J.X n).ρ.invariants) (by rw [ZeroMemClass.coe_zero, map_zero]) = 0 := by
  rw [cohomologyClass_def, ← cochainClass_zero]
  congr 1
  simp only [map_zero]

/-- The class of a scalar multiple of an invariant cocycle is the scalar multiple of its class. -/
@[simp]
theorem cohomologyClass_smul {n : ℕ} (r : k) (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    c.cohomologyClass (r • z) (by rw [Submodule.coe_smul, map_smul, hz, smul_zero]) =
      r • c.cohomologyClass z hz := by
  rw [cohomologyClass_def, cohomologyClass_def, ← cochainClass_smul]
  congr 1
  simp only [map_smul]

/-- **Cohomologous invariant cocycles have the same class**: if `z - z'` is the differential of
an invariant element of `J`, then `z` and `z'` have the same class in `Hⁿ⁺¹(G, X)`. -/
theorem cohomologyClass_eq_of_sub_eq_d {n : ℕ} (z z' : (J.X (n + 1)).ρ.invariants)
    (hz : (J.d (n + 1) (n + 2)).hom (z : (J.X (n + 1)).V) = 0)
    (hz' : (J.d (n + 1) (n + 2)).hom (z' : (J.X (n + 1)).V) = 0) (y : (J.X n).ρ.invariants)
    (hy : (z : (J.X (n + 1)).V) - z' = (J.d n (n + 1)).hom y) :
    c.cohomologyClass z hz = c.cohomologyClass z' hz' := by
  refine cochainClass_eq_of_sub_eq_d rfl _ _ ((c.comparison.f n).hom.mapInvariants y)
    (Subtype.ext ?_)
  rw [homogeneousCochains.d_apply, ContIntertwiningMap.mapInvariants_apply, d_comparison_f_apply,
    Submodule.coe_sub, ContIntertwiningMap.mapInvariants_apply,
    ContIntertwiningMap.mapInvariants_apply, ← map_sub, hy]

section Homotopy

variable [LocallyCompactSpace G]

/-- **Independence of the contraction.** Two contractions of `J` onto `X` with the same
augmentation induce the same map on cohomology. -/
theorem cohomologyMap_eq_of_ι_eq (c' : ResolutionContraction X J) (h : c.ι = c'.ι) (n : ℕ) :
    c.cohomologyMap n = c'.cohomologyMap n := by
  rw [cohomologyMap_def, cohomologyMap_def]
  exact (c.homologyMap_eq_homologyMap_comparison c'.comparison
    (by rw [h, ι_comp_comparison_f_zero]) n).symm

/-- **Naturality of the cohomology map.** For contractions `c` of `J` onto `X` and `c'` of `J'`
onto `Y`, a coefficient morphism `g : X ⟶ Y` and a chain map `f : J ⟶ J'` lying over it give a
commutative square: `Hⁿ(Jᴳ) ⟶ Hⁿ(G, X) ⟶ Hⁿ(G, Y)` equals `Hⁿ(Jᴳ) ⟶ Hⁿ(J'ᴳ) ⟶ Hⁿ(G, Y)`. -/
@[reassoc]
theorem cohomologyMap_comp_coeffMap {Y : TopRep.{max v w} k G}
    {J' : CochainComplex (TopRep.{max v w} k G) ℕ} (c' : ResolutionContraction Y J') (g : X ⟶ Y)
    (f : J ⟶ J') (hf : c.ι ≫ f.f 0 = g ≫ c'.ι) (n : ℕ) :
    c.cohomologyMap n ≫ TauCeti.ContinuousCohomology.coeffMap g n =
      HomologicalComplex.homologyMap
        (((invariantsFunctor k G).mapHomologicalComplex _).map f) n ≫ c'.cohomologyMap n := by
  rw [← TauCeti.ContinuousCohomology.homologyMap_shiftedResolutionMap, cohomologyMap_def,
    cohomologyMap_def, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  refine ((invariantsFunctor k G).mapHomotopy (c.homotopy _ _ ?_)).homologyMap_eq n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, reassoc_of% hf,
    ι_comp_comparison_f_zero_assoc, ι_comp_comparison_f_zero,
    TauCeti.ContinuousCohomology.shiftedResolutionMap_f]
  -- The coefficient map in degree zero of the resolution is `g` itself, and restriction along the
  -- identity of `G` does not change the augmentation, so this is Mathlib's commutation of
  -- coefficient maps with the resolution differentials in degree zero.
  exact (ContinuousCohomology.resolutionMap_comp_d (ContinuousMonoidHom.id G) g 0).symm

/-- **Naturality of the cohomology map in the complex.** A chain map `f : J ⟶ J'` of complexes
contracted onto the same `X`, lying over the identity of `X`, commutes with the cohomology
maps. -/
@[reassoc]
theorem homologyMap_comp_cohomologyMap {J' : CochainComplex (TopRep.{max v w} k G) ℕ}
    (c' : ResolutionContraction X J') (f : J ⟶ J') (hf : c.ι ≫ f.f 0 = c'.ι) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((invariantsFunctor k G).mapHomologicalComplex _).map f) n ≫ c'.cohomologyMap n =
      c.cohomologyMap n := by
  rw [cohomologyMap_def, cohomologyMap_def, ← HomologicalComplex.homologyMap_comp,
    ← CategoryTheory.Functor.map_comp]
  exact c.homologyMap_eq_homologyMap_comparison _ (by
    rw [HomologicalComplex.comp_f, reassoc_of% hf, ι_comp_comparison_f_zero]) n

/-- **Classes are independent of the contraction.** Two contractions of `J` onto `X` with the
same augmentation give every invariant cocycle the same class. -/
theorem cohomologyClass_eq_of_ι_eq (c' : ResolutionContraction X J) (h : c.ι = c'.ι) {n : ℕ}
    (z : (J.X n).ρ.invariants) (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    c.cohomologyClass z hz = c'.cohomologyClass z hz := by
  rw [← c.cohomologyMap_homologyπ z hz, ← c'.cohomologyMap_homologyπ z hz,
    c.cohomologyMap_eq_of_ι_eq c' h]

/-- **A chain map over the identity preserves classes.** If `f : J ⟶ J'` lies over the identity
of `X` for contractions `c` of `J` and `c'` of `J'`, then an invariant cocycle `z` of `J` and its
image `f z` have the same class in `Hⁿ(G, X)`. -/
theorem cohomologyClass_map {J' : CochainComplex (TopRep.{max v w} k G) ℕ}
    (c' : ResolutionContraction X J') (f : J ⟶ J') (hf : c.ι ≫ f.f 0 = c'.ι) {n : ℕ}
    (z : (J.X n).ρ.invariants) (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    c'.cohomologyClass ((f.f n).hom.mapInvariants z) (d_mapInvariants_f_apply f z hz) =
      c.cohomologyClass z hz := by
  rw [← c.cohomologyMap_homologyπ z hz, ← c'.cohomologyMap_homologyπ _
    (d_mapInvariants_f_apply f z hz), ← c.homologyMap_comp_cohomologyMap c' f hf n,
    ConcreteCategory.comp_apply, homologyMap_homologyπ_cyclesMkOfEq f z hz]

/-- **Naturality of classes in the coefficients.** For a chain map `f : J ⟶ J'` lying over a
coefficient morphism `g : X ⟶ Y`, the coefficient map of `g` carries the class of an invariant
cocycle `z` of `J` to the class of `f z`. -/
theorem coeffMap_cohomologyClass {Y : TopRep.{max v w} k G}
    {J' : CochainComplex (TopRep.{max v w} k G) ℕ} (c' : ResolutionContraction Y J') (g : X ⟶ Y)
    (f : J ⟶ J') (hf : c.ι ≫ f.f 0 = g ≫ c'.ι) {n : ℕ} (z : (J.X n).ρ.invariants)
    (hz : (J.d n (n + 1)).hom (z : (J.X n).V) = 0) :
    TauCeti.ContinuousCohomology.coeffMap g n (c.cohomologyClass z hz) =
      c'.cohomologyClass ((f.f n).hom.mapInvariants z) (d_mapInvariants_f_apply f z hz) := by
  rw [← c.cohomologyMap_homologyπ z hz, ← c'.cohomologyMap_homologyπ _
    (d_mapInvariants_f_apply f z hz), ← ConcreteCategory.comp_apply,
    c.cohomologyMap_comp_coeffMap c' g f hf n, ConcreteCategory.comp_apply,
    homologyMap_homologyπ_cyclesMkOfEq f z hz]

end Homotopy

end ResolutionContraction

section ResolutionContraction

variable [LocallyCompactSpace G] (X : TopRep.{max v w} k G)

/-- For the coinduced resolution contracted by evaluation at `1`, the cohomology map is the
identity of `Hⁿ(G, X)`. -/
@[simp]
theorem cohomologyMap_resolutionContraction (n : ℕ) :
    (resolutionContraction X).cohomologyMap n = 𝟙 (continuousCohomology n X) := by
  rw [ResolutionContraction.cohomologyMap_def, comparison_resolutionContraction,
    CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]

/-- For the coinduced resolution contracted by evaluation at `1`, the class of an invariant
cocycle is its class in continuous cohomology. -/
@[simp]
theorem cohomologyClass_resolutionContraction {n : ℕ}
    (z : ((resolution' X).X n).ρ.invariants)
    (hz : ((resolution' X).d n (n + 1)).hom (z : ((resolution' X).X n).V) = 0) :
    (resolutionContraction X).cohomologyClass z hz = X.cochainClass n z (Subtype.ext hz) := by
  rw [← ResolutionContraction.cohomologyMap_homologyπ _ z hz, cohomologyMap_resolutionContraction,
    ConcreteCategory.id_apply, cochainClass_def]

end ResolutionContraction

end TopRep
