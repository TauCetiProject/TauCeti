/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Projective.Dimension
public import TauCeti.Algebra.Homology.PrincipalIdealRing
public import TauCeti.AlgebraicTopology.Cellular.Comparison
public import TauCeti.AlgebraicTopology.Cellular.Projective
public import TauCeti.AlgebraicTopology.Singular.Empty

/-!
# Projectivity and freeness of cellular homology in a degree without cells above it

Let `(C, D)` be a relative CW complex in a Hausdorff space `X` with no `(n + 1)`-cells. The
cellular chain complex then vanishes in degree `n + 1`, so its homology in degree `n` is the object
of `n`-cycles, the kernel of the cellular differential on `Cₙ(C, D; R)`.

* Over a hereditary abelian category (every object of projective dimension at most one), with
  projective coefficients `R`, the cellular chain group `Cₙ(C, D; R)` is a coproduct of copies of
  `R`, hence projective (`TauCeti.projective_cellularChainGroup`), so its subobject of `n`-cycles
  and therefore cellular homology and relative singular homology `Hₙ(C, D; R)` are projective
  (`TauCeti.projective_cellularHomology_of_isEmpty_cell`,
  `TauCeti.projective_singularHomology_complexBasePair_of_isEmpty_cell`).
* Over a principal ideal ring `k` without zero divisors (in any universe, including `ℤ`), with
  projective coefficients `M` (for instance `M = k`), every submodule of a projective `k`-module is
  free regardless of rank (`Submodule.free_of_projective_of_isPrincipalIdealRing`), so cellular
  homology and relative singular homology `Hₙ(C, D; M)` are free `k`-modules
  (`TauCeti.free_cellularHomology_of_isEmpty_cell`,
  `TauCeti.free_singularHomology_complexBasePair_of_isEmpty_cell`).
* For an absolute CW complex `C` (`D = ∅`), passing across the quotient isomorphism from `(C, ∅)`
  gives projectivity and freeness of ordinary singular homology `Hₙ(C; -)` when there are no
  `(n + 1)`-cells (`TauCeti.projective_singularHomology_of_isEmpty_cell_succ`,
  `TauCeti.free_singularHomology_of_isEmpty_cell_succ`).

No finiteness assumption is imposed on cell counts in any degree (in particular there may be
countably or uncountably infinitely many `n`-cells), and nothing is assumed above degree `n + 1`.
With integral coefficients this says that `Hₙ(C, D; ℤ)` and `Hₙ(C; ℤ)` are free abelian; it does
not make the degree-`n` integral cohomology torsion-free, as `Ext¹_ℤ(Hₙ₋₁, ℤ)` can be nonzero.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34 and Theorem 2.35.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

section Relative

variable {X : Type w} [TopologicalSpace X] [T2Space X] {D : Set X} (C : Set X) [RelCWComplex C D]

section Abelian

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
  [∀ V : A, HasProjectiveDimensionLE V 1] (R : A) [Projective R]

/-- **Cellular homology below an empty degree is projective.** Over a hereditary abelian category,
cellular homology in degree `n` is projective whenever there are no `(n + 1)`-cells and coproducts
indexed by the `n`-cells are exact, with no finiteness assumption on the number of `n`-cells. -/
theorem projective_cellularHomology_of_isEmpty_cell (n : ℕ)
    [HasExactColimitsOfShape (Discrete (cell C n)) A] [IsEmpty (cell C (n + 1))] :
    Projective ((cellularChainComplex C R).homology n) := by
  refine ChainComplex.projective_homology_of_isZero_X_succ_of_hasProjectiveDimensionLE_one
    (cellularChainComplex C R) n ?_
  rw [cellularChainComplex_X]
  exact isZero_cellularChainGroup C (n + 1) R

/-- **Relative homology below an empty degree is projective.** Over a hereditary abelian category,
relative singular homology `Hₙ(C, D; R)` of a CW pair is projective whenever there are no
`(n + 1)`-cells and the `(n + 1)`-skeleton comparison map is an isomorphism on `Hₙ` (as holds for
every finite-dimensional CW pair and whenever sequential colimits are exact in `A`, for instance
for modules over any ring). -/
theorem projective_singularHomology_complexBasePair_of_isEmpty_cell
    [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A] (n : ℕ)
    [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n)]
    [IsEmpty (cell C (n + 1))] :
    Projective ((complexBasePair C).singularHomology R n) :=
  Projective.of_iso (cellularSingularHomologyIso C R n)
    (projective_cellularHomology_of_isEmpty_cell C R n)

end Abelian

section PID

variable {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
  (M : ModuleCat.{w} k) [Module.Projective k M]

/-- **Cellular homology below an empty degree is free.** If a relative CW complex has no
`(n + 1)`-cells, its cellular homology in degree `n`, with coefficients in a projective module
(for instance a free module) over a principal ideal ring without zero divisors in any universe, is
free regardless of the cardinality of the `n`-cells. -/
theorem free_cellularHomology_of_isEmpty_cell (n : ℕ) [IsEmpty (cell C (n + 1))] :
    Module.Free k ((cellularChainComplex C M).homology n : ModuleCat k) := by
  -- There are no `(n + 1)`-chains, so homology in degree `n` is the submodule of `n`-cycles.
  refine ChainComplex.free_homology_of_isZero_X_succ (cellularChainComplex C M) n ?_
  rw [cellularChainComplex_X]
  exact isZero_cellularChainGroup C (n + 1) M

/-- **Relative homology below an empty degree is free.** If a relative CW complex `(C, D)` has no
`(n + 1)`-cells, then `Hₙ(C, D; M)` is free for every projective module `M` (for instance `M = k`)
over a principal ideal ring without zero divisors in any universe, with no finiteness assumption on
cell counts and no dimension bound above `n + 1`. -/
theorem free_singularHomology_complexBasePair_of_isEmpty_cell (n : ℕ)
    [IsEmpty (cell C (n + 1))] :
    Module.Free k ((complexBasePair C).singularHomology M n : ModuleCat k) :=
  have := free_cellularHomology_of_isEmpty_cell C M n
  .of_equiv (cellularSingularHomologyIso C M n).toLinearEquiv

end PID

end Relative

section Absolute

variable {X : Type w} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]

/-- Over a hereditary abelian category, ordinary singular homology `Hₙ(C; R)` of a CW complex is
projective whenever there are no `(n + 1)`-cells and the `(n + 1)`-skeleton comparison map is an
isomorphism on `Hₙ`. -/
theorem projective_singularHomology_of_isEmpty_cell_succ {A : Type u} [Category.{v} A]
    [HasCoproducts.{w} A] [Abelian A] [∀ V : A, HasProjectiveDimensionLE V 1]
    [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A] (R : A) [Projective R] (n : ℕ)
    [IsIso ((skeletonBasePair C (n + 1)).singularHomologyMap
      (skeletonBasePairToComplex C (n + 1)) R n)]
    [IsEmpty (cell C (n + 1))] :
    Projective (((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of C)) :=
  Projective.of_iso (asIso ((complexBasePair C).singularHomologyπ R n)).symm
    (projective_singularHomology_complexBasePair_of_isEmpty_cell C R n)

/-- **Top singular homology of a CW complex is free over a PID.** Over a principal ideal ring
without zero divisors (in any universe, including `ℤ`), ordinary singular homology `Hₙ(C; M)` with
projective coefficients `M` (for instance `M = k`) is a free `k`-module whenever `C` has no
`(n + 1)`-cells, with no finiteness assumption on cell counts and no dimension bound above
`n + 1`. -/
theorem free_singularHomology_of_isEmpty_cell_succ {k : Type u} [CommRing k] [NoZeroDivisors k]
    [IsPrincipalIdealRing k] (M : ModuleCat.{w} k) [Module.Projective k M] (n : ℕ)
    [IsEmpty (cell C (n + 1))] :
    Module.Free k
      (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) n).obj M).obj
        (TopCat.of C)) :=
  have := free_singularHomology_complexBasePair_of_isEmpty_cell C M n
  .of_equiv
    (asIso ((complexBasePair C).singularHomologyπ (C := ModuleCat.{w} k) M n)).symm.toLinearEquiv

end Absolute

end TauCeti
