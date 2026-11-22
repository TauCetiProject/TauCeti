/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Lifting
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.From

/-!
# Brown models of the chains on the based path space

Let `R` be a commutative ring and `B` a space with a point `b`. The normalized cubical chains
`C_*(P_b B; R)` on the Moore paths starting at `b` form a differential graded left module over the
chain algebra `C_*(Ω_b B; R)` of the Moore loops at `b`, which act by concatenation in front
(`TauCeti.pathFromChain_isDGLeftModule`). Brown's twisted tensor products model this module by a
semi-free one. A **Brown model** (`TauCeti.BrownModel`) packages such a model:

* a row-finite twisting cocycle `m` over `C_*(Ω_b B; R)` on a graded set of generators `P`, whose
  row relation is well-founded, so that its free module `K_m = P →₀ C_*(Ω_b B; R)` is semi-free;
* the images in `C_*(P_b B; R)` of the generators, a generator of index `n` going to a chain of
  dimension `n`, such that the induced map `K_m → C_*(P_b B; R)`, linear over the loop chains,
  commutes with the differentials (`TauCeti.BrownModel.linearCombination_differential`);
* the statement that this map is a quasi-isomorphism, written on elements: every relative cycle is
  a relative boundary.

For a CW complex, Brown's construction gives a model with one generator for each cell
(`TauCeti.brownModel`), and for the circle the two-cell resolution `TauCeti.loopCellCocycle` is one
(`TauCeti.loopCellBrownModel`). This file shows that a Brown model does not depend on the choices
made to build it: any two Brown models of the same space at the same point, for instance those of
two CW structures or of two choices of paths to the cells, are homologous, so their twisted
complexes with coefficients in every DG right module are homotopy equivalent
(`TauCeti.BrownModel.exists_rowFiniteHomologous_homotopy`). The equivalence is compatible with the
comparisons with `C_*(P_b B; R)`, up to a specified homotopy. Every Brown model computes the
derived tensor product with the ground ring
(`TauCeti.BrownModel.nonempty_localizedFunctor_iso_derivedTensor`, in
`TauCeti.AlgebraicTopology.DGLocalSystem.Path.DerivedTensor`).

## Main definitions

* `TauCeti.BrownModel B b H R P ind`: a semi-free model of `C_*(P_b B; R)` over `C_*(Ω_b B; R)` on
  the generators `P` with indices `ind`.

## Main results

* `TauCeti.BrownModel.linearCombination_differential`: the comparison of a Brown model commutes with
  the differentials.
* `TauCeti.BrownModel.exists_rowFiniteHomologous_homotopy`: two Brown models are homologous,
  compatibly with their comparisons.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

noncomputable section

open Finsupp

universe uB uH uR uP

namespace TauCeti

variable (B : Type uB) [TopologicalSpace B] (b : B) (H : Type uH) (R : Type uR) [CommRing R]
  (P : Type uP) (ind : P → ℤ)

/-- A **Brown model** of the chains `C_*(P_b B; R)` on the Moore paths starting at `b`, over the
chains `C_*(Ω_b B; R)` on the Moore loops at `b`: a semi-free row-finite twisting cocycle `m` on
the generators `P`, and a quasi-isomorphism from its free module `K_m` to `C_*(P_b B; R)`, linear
over the loop chains and given by the images of the generators. The quasi-isomorphism is stated on
elements: every relative cycle `(u, w)`, with `D u = 0` and `g(u) = d w`, is a relative boundary
`(D u', g(u') + d w')`. -/
@[ext]
structure BrownModel where
  /-- The twisting cocycle, whose free module models the chains on the based path space. -/
  cocycle : RowFiniteTwistingCocycle (R := R) (A := loopChainAlgebra B b R)
    (cubicalChainGrading (MooreLoopSpace B b) R) (cubicalChainDifferential (MooreLoopSpace B b) R)
    P ind
  /-- The row relation of the cocycle is well-founded: the model is semi-free. -/
  wellFounded : WellFounded fun y x ↦ y ∈ (cocycle.m x).support
  /-- The images of the generators in the chains on the based path space. -/
  comparison : P → cubicalChainModule (MoorePathFrom B b) H R
  /-- A generator of index `n` goes to a chain of dimension `n`. -/
  comparison_mem : ∀ x, comparison x ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-ind x)
  /-- The comparison sends the row of a generator to the boundary of its image. -/
  linearCombination_comparison_m : ∀ x,
    linearCombination (loopChainAlgebra B b R) comparison (cocycle.m x) =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R (comparison x)
  /-- The comparison is a quasi-isomorphism: every relative cycle is a relative boundary. -/
  exists_differential_eq_and_linearCombination_add_eq : ∀ u w,
    rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
      (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
      (d := cubicalChainDifferential (MooreLoopSpace B b) R) cocycle.m u = 0 →
    linearCombination (loopChainAlgebra B b R) comparison u =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R w →
    ∃ u' w', rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
        (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
        (d := cubicalChainDifferential (MooreLoopSpace B b) R) cocycle.m u' = u ∧
      linearCombination (loopChainAlgebra B b R) comparison u' +
        cubicalChainModuleDifferential (MoorePathFrom B b) H R w' = w

namespace BrownModel

variable {B b H R P ind}

/-- **The comparison of a Brown model commutes with the differentials**: it sends the twisted
differential `D f` of every element `f` of the free module to the boundary of the image of `f`. -/
theorem linearCombination_differential (M : BrownModel B b H R P ind)
    (f : P →₀ loopChainAlgebra B b R) :
    linearCombination (loopChainAlgebra B b R) M.comparison
        (rowFiniteTwistedDifferential (R := R) (A := loopChainAlgebra B b R)
          (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R)
          (d := cubicalChainDifferential (MooreLoopSpace B b) R) M.cocycle.m f) =
      cubicalChainModuleDifferential (MoorePathFrom B b) H R
        (linearCombination (loopChainAlgebra B b R) M.comparison f) :=
  linearCombination_rowFiniteTwistedDifferential (pathFromChain_isDGLeftModule B b H R)
    M.cocycle.m M.linearCombination_comparison_m f

/-- **Brown models are unique up to homotopy.** Two Brown models `M` and `M'` of the chains on the
based path space, with generators in the same universe, are homologous: there are continuation
cocycles in both directions whose composites are homotopic to the identities, so the twisted
complexes of `M` and `M'` with coefficients in every DG right module are homotopy equivalent
(`TauCeti.RowFiniteHomologous.homotopyEquiv`). The continuation cocycle `ν` from `M` to `M'` is
compatible with the comparisons: a homotopy `k`, of degree `-1` and given on the generators, joins
the comparison of `M` to the comparison of `M'` composed with `ν`. This applies to the models of
two CW structures on the same space, or of two choices of paths to the cells. -/
theorem exists_rowFiniteHomologous_homotopy {Q : Type uP} {indQ : Q → ℤ}
    (M : BrownModel B b H R P ind) (M' : BrownModel B b H R Q indQ) :
    ∃ (E : RowFiniteHomologous (loopChain_isDGAlgebra B b R) M.cocycle M'.cocycle)
      (k : P → cubicalChainModule (MoorePathFrom B b) H R),
      (∀ x, k x ∈ cubicalChainModuleGrading (MoorePathFrom B b) H R (-ind x - 1)) ∧
      ∀ x, cubicalChainModuleDifferential (MoorePathFrom B b) H R (k x) +
          rowFiniteSignedMap (R := R) (A := loopChainAlgebra B b R)
            (𝒜 := cubicalChainGrading (MooreLoopSpace B b) R) k (M.cocycle.m x) =
        M.comparison x - linearCombination (loopChainAlgebra B b R) M'.comparison (E.ν.ν x) :=
  TauCeti.exists_rowFiniteHomologous_homotopy M.wellFounded M'.wellFounded
    (pathFromChain_isDGLeftModule B b H R) M.comparison_mem M'.comparison_mem
    M.linearCombination_comparison_m M'.linearCombination_comparison_m
    M.exists_differential_eq_and_linearCombination_add_eq
    M'.exists_differential_eq_and_linearCombination_add_eq

end BrownModel

end TauCeti
