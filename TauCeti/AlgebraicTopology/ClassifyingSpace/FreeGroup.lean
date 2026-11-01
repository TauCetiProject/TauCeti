/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.ClassifyingSpace.FirstHomology
public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.AlgebraicTopology.ClassifyingSpace.WedgeCircles
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# The homology of the classifying space of a free group

A wedge of circles indexed by `S` is a classifying space of the free group `FreeGroup S`
(`TauCeti.wedgeCirclesHomotopyEquivClassifyingSpace`). Its homology is computed topologically,
and here it is compared with the group homology of the free group.

* **Degrees at least two.** The wedge of circles is a CW complex with no cells of dimension at
  least `2`, so its singular homology vanishes in those degrees
  (`TauCeti.WedgeSum.isZero_singularHomology_circle`), for coefficients in any abelian category
  whose coproducts are exact. By homotopy invariance so does that of Milnor's classifying space
  `classifyingSpace (FreeGroup S)`
  (`TauCeti.isZero_classifyingSpace_singularHomology_freeGroup`), and by the comparison of the
  singular homology of a classifying space with group homology, the group homology of a free
  group with trivial coefficients in a commutative ring `k` vanishes in degrees at least two
  (`TauCeti.isZero_groupHomology_freeGroup`): `Hₙ(F, k) = 0` for `n ≥ 2`.
* **Degree one.** On integral first homology, the homotopy equivalence of the wedge of circles
  with `classifyingSpace (FreeGroup S)` sends the Hurewicz class of a loop to the class of the
  free-group element it represents, both in the abelianization
  (`TauCeti.classifyingSpaceFirstHomologyAddEquiv_map_wedgeCircles`) and in Mathlib's first group
  homology (`TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles`). The
  loop going once around the `i`-th circle goes to the class of the `1`-cycle at the generator
  `i` (`TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles_expLoop`).

## Main results

* `TauCeti.WedgeSum.isZero_singularHomology_circle`: `Hₙ(⋁ S¹; R) = 0` for `n ≥ 2`.
* `TauCeti.isZero_classifyingSpace_singularHomology_freeGroup`: `Hₙ(BF; R) = 0` for `n ≥ 2`.
* `TauCeti.isZero_groupHomology_freeGroup`: `Hₙ(F, k) = 0` for `n ≥ 2`.
* `TauCeti.classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles_expLoop`: the
  loop around the `i`-th circle corresponds to the generator `i` in `H₁(F, ℤ)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.B, Theorem 1B.8, and Section 2.2, Lemma 2.34.
* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Chapter II, Section 4.
-/

public section

noncomputable section

open CategoryTheory Limits FundamentalGroup TauCeti.HurewiczOne

universe u v w

namespace TauCeti

namespace WedgeSum

variable {S : Type u} {A : Type w} [Category.{v} A] [HasCoproducts.{u} A] [Abelian A]
  [AB4OfSize.{u} A] (R : A)

/-- **The homology of a wedge of circles vanishes above degree one.** A wedge of circles is a CW
complex with no cells of dimension at least `2`, so its singular homology vanishes in every
degree `n ≥ 2`, with coefficients in any abelian category with exact coproducts. -/
theorem isZero_singularHomology_circle {n : ℕ} (hn : 2 ≤ n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor.{u} A n).obj R).obj
      (TopCat.of (WedgeSum fun _ : S ↦ (1 : Circle)))) :=
  have := isEmpty_cell_circleCWComplex (S := S) hn
  isZero_singularHomology_of_isEmpty_cell_univ R n

end WedgeSum

open WedgeSum

section Vanishing

variable (S : Type)

/-- **The homology of the classifying space of a free group vanishes above degree one.** Milnor's
classifying space of `FreeGroup S` is homotopy equivalent to the wedge of circles indexed by `S`,
so its singular homology vanishes in every degree `n ≥ 2`, with coefficients in any abelian
category with exact coproducts. -/
theorem isZero_classifyingSpace_singularHomology_freeGroup {A : Type w} [Category.{v} A]
    [HasCoproducts.{0} A] [Abelian A] [AB4OfSize.{0} A] (R : A) {n : ℕ} (hn : 2 ≤ n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor.{0} A n).obj R).obj
      (TopCat.of (classifyingSpace (FreeGroup S)))) :=
  (isZero_singularHomology_circle R hn).of_iso
    ((wedgeCirclesHomotopyEquivClassifyingSpace S).singularHomologyIso R n).symm

/-- **The homology of a free group vanishes above degree one.** For every commutative ring `k`,
the group homology `Hₙ(F, k)` of a free group with trivial coefficients vanishes in every degree
`n ≥ 2`. It is the singular homology of the classifying space of `F`, which is a wedge of
circles. -/
theorem isZero_groupHomology_freeGroup (k : Type) [CommRing k] {n : ℕ} (hn : 2 ≤ n) :
    IsZero (groupHomology (Rep.trivial k (FreeGroup S) k) n) :=
  (isZero_classifyingSpace_singularHomology_freeGroup S (ModuleCat.of k k) hn).of_iso
    (classifyingSpaceSingularHomologyIsoGroupHomology k (FreeGroup S) n).symm

end Vanishing

section FirstHomology

variable (S : Type)

/-- On integral first homology, the homotopy equivalence of a wedge of circles with the
classifying space of the free group sends the Hurewicz class of a loop `a` to the class in the
abelianization of the free-group element that `a` represents. -/
-- Not a simp lemma: singularChainComplexFunctor_obj_map rewrites the chain map first.
theorem classifyingSpaceFirstHomologyAddEquiv_map_wedgeCircles
    (a : FundamentalGroup (WedgeSum fun _ : S ↦ (1 : Circle)) (base _)) :
    classifyingSpaceFirstHomologyAddEquiv (FreeGroup S)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun)) 1).hom
          (hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : S ↦ (1 : Circle)))
            (base _) (Additive.ofMul (Abelianization.of a)))) =
      Additive.ofMul (Abelianization.of (circleFundamentalGroupMulEquiv S a)) := by
  rw [homologyMap_hurewiczHomologyAddEquiv, toMul_ofMul, Abelianization.map_of]
  simp only [TopCat.hom_ofHom]
  rw [← hurewiczHomologyAddEquiv_fundamentalGroupMulEquivOfPath
      (wedgeCirclesClassifyingSpaceBasepointPath S),
    classifyingSpaceFirstHomologyAddEquiv_hurewiczHomologyAddEquiv,
    classifyingSpaceFundamentalGroupMulEquiv_map_wedgeCirclesHomotopyEquivClassifyingSpace]

/-- The topological computation of the first homology of a wedge of circles agrees with the
algebraic one: the homotopy equivalence with the classifying space of the free group sends the
Hurewicz class of a loop `a` to the class in `H₁(F, ℤ)` of the `1`-cycle, with coefficient `1`,
at the free-group element that `a` represents. -/
-- Not a simp lemma: singularChainComplexFunctor_obj_map rewrites the chain map first.
theorem classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles
    (a : FundamentalGroup (WedgeSum fun _ : S ↦ (1 : Circle)) (base _)) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology (FreeGroup S)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun)) 1).hom
          (hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : S ↦ (1 : Circle)))
            (base _) (Additive.ofMul (Abelianization.of a)))) =
      groupHomology.H1π (Rep.trivial ℤ (FreeGroup S) ℤ)
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ (FreeGroup S) ℤ)).inv
          (Finsupp.single (circleFundamentalGroupMulEquiv S a) 1)) := by
  rw [classifyingSpaceFirstHomologyAddEquivGroupHomology_apply,
    classifyingSpaceFirstHomologyAddEquiv_map_wedgeCircles]
  exact groupHomology.H1AddEquivOfIsTrivial_symm_tmul
    (A := Rep.trivial ℤ (FreeGroup S) ℤ) _ 1

/-- The loop going once around the `i`-th circle of the wedge corresponds, under the homotopy
equivalence with the classifying space of the free group, to the class in `H₁(F, ℤ)` of the
`1`-cycle at the generator `i` with coefficient `1`. -/
theorem classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles_expLoop (i : S) :
    classifyingSpaceFirstHomologyAddEquivGroupHomology (FreeGroup S)
      ((HomologicalComplex.homologyMap ((singularChains ℤ).map
        (TopCat.ofHom (wedgeCirclesHomotopyEquivClassifyingSpace S).toFun)) 1).hom
          (hurewiczHomologyAddEquiv (X := TopCat.of (WedgeSum fun _ : S ↦ (1 : Circle)))
            (base _) (Additive.ofMul (Abelianization.of
              (mapOfEq (incl (fun _ : S ↦ (1 : Circle)) i) (incl_apply_self i)
                (fromPath (Path.Homotopic.Quotient.mk Circle.expLoop))))))) =
      groupHomology.H1π (Rep.trivial ℤ (FreeGroup S) ℤ)
        ((groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ (FreeGroup S) ℤ)).inv
          (Finsupp.single (FreeGroup.of i) 1)) := by
  rw [classifyingSpaceFirstHomologyAddEquivGroupHomology_map_wedgeCircles,
    circleFundamentalGroupMulEquiv_expLoop]

end FirstHomology

end TauCeti
