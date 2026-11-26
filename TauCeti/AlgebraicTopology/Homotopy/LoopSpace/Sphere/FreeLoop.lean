/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.LoopSpace.Sphere.Basic
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Sphere
public import TauCeti.Topology.MappingSpace.Sphere.ThreeSphere
public import TauCeti.Topology.PathSpace.Moore.Comparison.FreeLoop

/-!
# The homology of the free loop space of the three-sphere

Let `S³` be the unit sphere of a real normed space of dimension `4`. The singular homology of its
free loop space `𝓛S³`, with coefficients in a ring `R`, is `R` in degree `0` and in every degree
`p ≥ 2`, and vanishes in degree `1`:

* `H_{2j}(𝓛S³; R) ≅ R` for every `j`
  (`TauCeti.singularHomologyCircleMapThreeSphereEvenIso`);
* `H_{2j+3}(𝓛S³; R) ≅ R` for every `j`
  (`TauCeti.singularHomologyCircleMapThreeSphereOddIso`);
* `H_1(𝓛S³; R) = 0` (`TauCeti.isZero_singularHomology_one_circleMap_threeSphere`).

So for a nontrivial ring, `H_p(𝓛S³; R) ≅ R` exactly when `p ≠ 1`
(`TauCeti.nonempty_singularHomology_circleMap_threeSphere_iso_iff`). The same holds for the Moore
free loop space, which is homotopy equivalent to `C(S¹, S³)`
(`TauCeti.MooreFreeLoopSpace.homotopyEquivCircleMap`).

The computation uses the splitting `𝓛S³ ≃ₜ S³ × ΩS³`
(`TauCeti.circleMapThreeSphereHomeomorphProd`) given by the group structure on `S³` transported
from the unit quaternions. The loop space `ΩS³` has homology `R` in every even degree and `0` in
every odd degree
(`TauCeti.singularHomologyLoopSpaceSphereIso`, `TauCeti.isZero_singularHomology_loopSpace_sphere`).
By the Künneth formula for a sphere factor, `Hₘ(S³ × B) ≅ Hₘ(B) ⊕ H_{m-3}(B)`, of which only one
summand is nonzero in each degree here: in even degree `m` the inclusion `B → S³ × B` is an
isomorphism, since `H_{m-3}(ΩS³)` vanishes
(`TauCeti.isIso_singularHomologyMap_prodMk_sphere_iff`), and in odd degree `m ≥ 3`
`Hₘ(S³ × B) ≅ H_{m-3}(B)`, since `Hₘ(ΩS³)` vanishes (`TauCeti.singularHomologySphereProdIso`).

This is the free loop space homology `H_*(𝓛S³; ℤ)`, `ℤ` for `p = 0` and every `p ≥ 2` and `0` for
`p = 1`, of the example of Barraud, Damian, Humilière and Oancea comparing the twisted symplectic
homology of `T*S³` with the homology of `𝓛S³` for coefficients concentrated in infinitely many
degrees.

## Main results

* `TauCeti.singularHomologyCircleMapThreeSphereEvenIso`,
  `TauCeti.singularHomologyCircleMapThreeSphereOddIso`: `H_{2j}(𝓛S³; R) ≅ R` and
  `H_{2j+3}(𝓛S³; R) ≅ R`.
* `TauCeti.isZero_singularHomology_one_circleMap_threeSphere`: `H_1(𝓛S³; R) = 0`.
* `TauCeti.nonempty_singularHomology_circleMap_threeSphere_iso_iff`: `H_p(𝓛S³; R) ≅ R` exactly when
  `p ≠ 1`.
* `TauCeti.singularHomologyMooreFreeLoopSpaceThreeSphereEvenIso`,
  `TauCeti.singularHomologyMooreFreeLoopSpaceThreeSphereOddIso`,
  `TauCeti.isZero_singularHomology_one_mooreFreeLoopSpace_threeSphere`,
  `TauCeti.nonempty_singularHomology_mooreFreeLoopSpace_threeSphere_iso_iff`: the same for the
  Moore free loop space.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.
* A. Hatcher,
  [*Spectral Sequences in Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/SSAT/SSch1.pdf),
  Chapter 1 (the homology of the loop space of a sphere).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Module AlgebraicTopology

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3 + 1)
  (R : Type u) [Ring R]

section Homology

/-- `Hₘ(C(S¹, S³); R) ≅ Hₘ(S³ × ΩS³; R)`. -/
private def singularHomologyCircleMapThreeSphereIsoProd (m : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).obj
        (TopCat.of C(Circle, sphere (0 : E) 1)) ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).obj
        (TopCat.of (sphere (0 : E) 1 × Path (threeSphereOne hE) (threeSphereOne hE))) :=
  (circleMapThreeSphereHomeomorphProd hE).toHomotopyEquiv.singularHomologyIso _ m

/-- `H_{2j}(ΩS³; R) ≅ R`. -/
private def singularHomologyLoopSpaceThreeSphereEvenIso (x : sphere (0 : E) 1) (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) (2 * j)).obj (ModuleCat.of R R)).obj
        (TopCat.of (Path x x)) ≅ ModuleCat.of R R :=
  eqToIso (by rw [show 2 * j = j * (3 - 1) by omega]) ≪≫
    singularHomologyLoopSpaceSphereIso hE (by norm_num) x R j

/-- **The even-degree homology of the free loop space of `S³`**: `H_{2j}(C(S¹, S³); R) ≅ R` for
the unit sphere `S³` of a four-dimensional real normed space, every ring `R` and every `j`. The
inclusion of the loop space `ΩS³` at a point is an isomorphism in these degrees. -/
def singularHomologyCircleMapThreeSphereEvenIso (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) (2 * j)).obj (ModuleCat.of R R)).obj
        (TopCat.of C(Circle, sphere (0 : E) 1)) ≅ ModuleCat.of R R :=
  let x := threeSphereOne hE
  -- The inclusion `ΩS³ → S³ × ΩS³` at `x` is an isomorphism on `H_{2j}`: below degree `3` always,
  -- and from degree `3` on because `H_{2j-3}(ΩS³)` vanishes.
  have hiso : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) (2 * j)).obj
      (ModuleCat.of R R)).map (TopCat.ofHom ((ContinuousMap.const (Path x x) x).prodMk
        (ContinuousMap.id (Path x x))))) := by
    rcases lt_or_ge (2 * j) 3 with hj | hj
    · exact isIso_singularHomologyMap_prodMk_sphere_of_lt _ hE x hj
    · exact (isIso_singularHomologyMap_prodMk_sphere_iff _ hE x (n := 2 * j - 3) (by omega)).2
        (isZero_singularHomology_loopSpace_sphere hE (by norm_num) x R (by omega))
  singularHomologyCircleMapThreeSphereIsoProd hE R (2 * j) ≪≫ (@asIso _ _ _ _ _ hiso).symm ≪≫
    singularHomologyLoopSpaceThreeSphereEvenIso hE R x j

/-- **The odd-degree homology of the free loop space of `S³`**: `H_{2j+3}(C(S¹, S³); R) ≅ R` for
the unit sphere `S³` of a four-dimensional real normed space, every ring `R` and every `j`. By the
Künneth formula it is `H_{2j}(ΩS³; R)`, since `H_{2j+3}(ΩS³; R)` vanishes. -/
def singularHomologyCircleMapThreeSphereOddIso (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) (2 * j + 3)).obj (ModuleCat.of R R)).obj
        (TopCat.of C(Circle, sphere (0 : E) 1)) ≅ ModuleCat.of R R :=
  singularHomologyCircleMapThreeSphereIsoProd hE R (2 * j + 3) ≪≫
    singularHomologySphereProdIso _ hE (n := 2 * j) rfl
      (isZero_singularHomology_loopSpace_sphere hE (by norm_num) _ R (by omega)) ≪≫
    singularHomologyLoopSpaceThreeSphereEvenIso hE R _ j

include hE in
/-- **The first homology of the free loop space of `S³` vanishes**: `H_1(C(S¹, S³); R) = 0` for the
unit sphere `S³` of a four-dimensional real normed space and every ring `R`. -/
theorem isZero_singularHomology_one_circleMap_threeSphere :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) 1).obj (ModuleCat.of R R)).obj
      (TopCat.of C(Circle, sphere (0 : E) 1))) :=
  ((isZero_singularHomology_sphere_prod_iff_of_lt _ hE (by norm_num)).2
    (isZero_singularHomology_loopSpace_sphere hE (by norm_num) _ R (by omega))).of_iso
    (singularHomologyCircleMapThreeSphereIsoProd hE R 1)

include hE in
/-- **The homology of the free loop space of `S³`**: for the unit sphere `S³` of a
four-dimensional real normed space and a nontrivial ring `R`, `H_p(C(S¹, S³); R) ≅ R` exactly when
`p ≠ 1`. -/
theorem nonempty_singularHomology_circleMap_threeSphere_iso_iff [Nontrivial R] (p : ℕ) :
    Nonempty (((singularHomologyFunctor (ModuleCat.{u} R) p).obj (ModuleCat.of R R)).obj
        (TopCat.of C(Circle, sphere (0 : E) 1)) ≅ ModuleCat.of R R) ↔ p ≠ 1 := by
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨e⟩ rfl
    have := ModuleCat.subsingleton_of_isZero
      ((isZero_singularHomology_one_circleMap_threeSphere hE R).of_iso e.symm)
    exact not_subsingleton R this
  · rcases Nat.even_or_odd p with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨eqToIso (by rw [← two_mul]) ≪≫ singularHomologyCircleMapThreeSphereEvenIso hE R j⟩
    · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      exact ⟨eqToIso (by rw [show 2 * (j + 1) + 1 = 2 * j + 3 by ring]) ≪≫
        singularHomologyCircleMapThreeSphereOddIso hE R j⟩

end Homology

section Moore

/-- `Hₘ` of the Moore free loop space of `S³` is that of `C(S¹, S³)`. -/
private def singularHomologyMooreFreeLoopSpaceThreeSphereIso (m : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).obj
        (TopCat.of (MooreFreeLoopSpace (sphere (0 : E) 1))) ≅
      ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).obj
        (TopCat.of C(Circle, sphere (0 : E) 1)) :=
  (MooreFreeLoopSpace.homotopyEquivCircleMap (sphere (0 : E) 1)).singularHomologyIso _ m

/-- **The even-degree homology of the Moore free loop space of `S³`**: `H_{2j}(𝓛S³; R) ≅ R` for
the unit sphere `S³` of a four-dimensional real normed space, every ring `R` and every `j`. -/
def singularHomologyMooreFreeLoopSpaceThreeSphereEvenIso (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) (2 * j)).obj (ModuleCat.of R R)).obj
        (TopCat.of (MooreFreeLoopSpace (sphere (0 : E) 1))) ≅ ModuleCat.of R R :=
  singularHomologyMooreFreeLoopSpaceThreeSphereIso R _ ≪≫
    singularHomologyCircleMapThreeSphereEvenIso hE R j

/-- **The odd-degree homology of the Moore free loop space of `S³`**: `H_{2j+3}(𝓛S³; R) ≅ R` for
the unit sphere `S³` of a four-dimensional real normed space, every ring `R` and every `j`. -/
def singularHomologyMooreFreeLoopSpaceThreeSphereOddIso (j : ℕ) :
    ((singularHomologyFunctor (ModuleCat.{u} R) (2 * j + 3)).obj (ModuleCat.of R R)).obj
        (TopCat.of (MooreFreeLoopSpace (sphere (0 : E) 1))) ≅ ModuleCat.of R R :=
  singularHomologyMooreFreeLoopSpaceThreeSphereIso R _ ≪≫
    singularHomologyCircleMapThreeSphereOddIso hE R j

include hE in
/-- **The first homology of the Moore free loop space of `S³` vanishes**: `H_1(𝓛S³; R) = 0` for the
unit sphere `S³` of a four-dimensional real normed space and every ring `R`. -/
theorem isZero_singularHomology_one_mooreFreeLoopSpace_threeSphere :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} R) 1).obj (ModuleCat.of R R)).obj
      (TopCat.of (MooreFreeLoopSpace (sphere (0 : E) 1)))) :=
  (isZero_singularHomology_one_circleMap_threeSphere hE R).of_iso
    (singularHomologyMooreFreeLoopSpaceThreeSphereIso R 1)

include hE in
/-- **The homology of the Moore free loop space of `S³`**: for the unit sphere `S³` of a
four-dimensional real normed space and a nontrivial ring `R`, `H_p(𝓛S³; R) ≅ R` exactly when
`p ≠ 1`. -/
theorem nonempty_singularHomology_mooreFreeLoopSpace_threeSphere_iso_iff [Nontrivial R] (p : ℕ) :
    Nonempty (((singularHomologyFunctor (ModuleCat.{u} R) p).obj (ModuleCat.of R R)).obj
        (TopCat.of (MooreFreeLoopSpace (sphere (0 : E) 1))) ≅ ModuleCat.of R R) ↔ p ≠ 1 :=
  Iff.trans ⟨fun ⟨e⟩ ↦ ⟨(singularHomologyMooreFreeLoopSpaceThreeSphereIso R p).symm ≪≫ e⟩,
      fun ⟨e⟩ ↦ ⟨singularHomologyMooreFreeLoopSpaceThreeSphereIso R p ≪≫ e⟩⟩
    (nonempty_singularHomology_circleMap_threeSphere_iso_iff hE R p)

end Moore

end TauCeti
