/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Singular
public import TauCeti.AlgebraicTopology.Cellular.TopHomology
public import TauCeti.AlgebraicTopology.Cohomology.HomotopyInvariance
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.Topology.CWComplex.Classical.Finite

/-!
# Cohomology vanishing and dimension bounds for CW complexes and CW models

Let `(C, D)` be a relative CW complex in a Hausdorff space `X`. Building on the projectivity and
freeness of degree-`d` homology when there are no `(d + 1)`-cells
(`TauCeti.AlgebraicTopology.Cellular.TopHomology`) and the vanishing of homology in empty cell
degrees (`TauCeti.isZero_singularHomology_complexBasePair_of_isEmpty_cell`), this file establishes
cohomology vanishing at missing cells, dimension-bound vanishing above `d`, and the transfers to
CW homotopy models and whole-space CW structures:

* When `(C, D)` has **no `(d + 1)`-cells** (`[IsEmpty (cell C (d + 1))]`), with no finiteness
  assumption on cell counts and no assumption above degree `d + 1`, both terms of the universal
  coefficient sequence
  `0 ⟶ Ext¹_k(H_d(C, D; R), M) ⟶ H^{d+1}(C, D; R, M) ⟶ Hom_k(H_{d+1}(C, D; R), M) ⟶ 0` vanish
  over a hereditary commutative ring `k` (in any universe, including `ℤ`) when `R` is projective:
  `H_d(C, D; R)` is projective so `Ext¹_k(H_d(C, D; R), M) = 0`, and `H_{d+1}(C, D; R) = 0` so
  `Hom_k(H_{d+1}(C, D; R), M) = 0`. Thus `H^{d+1}(C, D; R, M)` vanishes
  (`TauCeti.isZero_singularCohomology_complexBasePair_succ_of_isEmpty_cell`). When `C` carries an
  absolute CW structure (`[CWComplex C]`, i.e. `D = ∅`) with no `(d + 1)`-cells, the same gives
  vanishing of `H^{d+1}(C; R, M)` (`TauCeti.isZero_singularCohomology_succ_of_isEmpty_cell`) and
  of `H^{d+1}(Y; R, M)` for any space `Y` homotopy equivalent to `C`
  (`ContinuousMap.HomotopyEquiv.isZero_singularCohomology_succ_of_isEmpty_cell`).
* Note that even for an absolute `d`-dimensional CW complex `C`, degree-`d` integral cohomology
  `H^d(C; ℤ)` need **not** be torsion-free: the universal coefficient sequence in degree `d`
  contains `Ext¹_ℤ(H_{d-1}(C; ℤ), ℤ)`, which carries the torsion of `H_{d-1}` (for instance
  `H^2(ℝP²; ℤ) ≅ ℤ/2ℤ`).
* For a **CW homotopy model** `e : ContinuousMap.HomotopyEquiv Y C` with an absolute CW structure on
  `C` (`[CWComplex C]`, `D = ∅`), projectivity and freeness of `H_d(Y; -)` when that CW structure
  on `C` has no `(d + 1)`-cells, as well as vanishing of homology and cohomology above `d` when it
  has no cells in dimensions strictly above `d`, transfer directly across `e`
  (`ContinuousMap.HomotopyEquiv.projective_singularHomology_of_isEmpty_cell_succ`,
  `ContinuousMap.HomotopyEquiv.free_singularHomology_of_isEmpty_cell_succ`,
  `ContinuousMap.HomotopyEquiv.isZero_singularHomology_of_isEmpty_cell_gt`,
  `ContinuousMap.HomotopyEquiv.isZero_singularCohomology_of_isEmpty_cell_gt`).
* When `(C, D)` has **no cells in dimensions strictly above `d`**
  (`∀ m, d < m → IsEmpty (cell C m)`), it is finite-dimensional
  (`Topology.RelCWComplex.finiteDimensional_of_isEmpty_cell_gt`), and both relative singular
  homology `Hₙ(C, D; R)` and relative singular cohomology `Hⁿ(C, D; R, M)` vanish in every degree
  `n > d` (`TauCeti.isZero_singularHomology_complexBasePair_of_isEmpty_cell_gt`,
  `TauCeti.isZero_singularCohomology_complexBasePair_of_isEmpty_cell_gt`). When `C` carries an
  absolute CW structure (`[CWComplex C]`, i.e. `D = ∅`) with no cells in dimensions strictly above
  `d`, ordinary singular homology and cohomology vanish in every degree `n > d` — for `C`
  (`TauCeti.isZero_singularHomology_of_isEmpty_cell_gt`,
  `TauCeti.isZero_singularCohomology_of_isEmpty_cell_gt`), for any space homotopy equivalent to `C`,
  and for a space `X` carrying such an absolute CW structure on `Set.univ`
  (`TauCeti.isZero_singularHomology_univ_of_isEmpty_cell_gt`,
  `TauCeti.isZero_singularCohomology_univ_of_isEmpty_cell_gt`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2 (Theorem 2.35) and Section 3.1 (Theorem 3.2).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

section MissingCellCohomology

variable {X : Type w} [TopologicalSpace X] [T2Space X]
  {k : Type u} [CommRing k] [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1]
  (R M : ModuleCat.{w} k) [Module.Projective k R]

/-- **Relative singular cohomology of a CW pair vanishes in degree `d + 1` when there are no
`(d + 1)`-cells**, over any hereditary commutative ring `k` (in any universe, including `ℤ`), with
no finiteness assumption on cell counts and no dimension bound on `C`: `H_d(C, D; R)` is projective
so `Ext¹_k(H_d, M) = 0`, and `H_{d+1}(C, D; R) = 0` so `Hom_k(H_{d+1}, M) = 0`. -/
theorem isZero_singularCohomology_complexBasePair_succ_of_isEmpty_cell {D : Set X} (C : Set X)
    [RelCWComplex C D] (d : ℕ) [IsEmpty (cell C (d + 1))] :
    IsZero ((complexBasePair C).singularCohomology R k M (d + 1)) := by
  have : Projective ((complexBasePair C).singularHomology R d) :=
    projective_singularHomology_complexBasePair_of_isEmpty_cell C R d
  exact (complexBasePair C).isZero_singularCohomology_succ_of_projective_homology R M d
    (isZero_singularHomology_complexBasePair_of_isEmpty_cell C R (d + 1))

/-- **Singular cohomology of a CW complex vanishes in degree `d + 1` when there are no
`(d + 1)`-cells**, over any hereditary commutative ring `k` (in any universe, including `ℤ`), with
no finiteness assumption on cell counts and no dimension bound on `C`. -/
theorem isZero_singularCohomology_succ_of_isEmpty_cell (C : Set X) [CWComplex C] (d : ℕ)
    [IsEmpty (cell C (d + 1))] :
    IsZero ((TopCat.of C).singularCohomology R k M (d + 1)) := by
  have : Projective
      (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) d).obj R).obj
        (TopCat.of C)) :=
    projective_singularHomology_of_isEmpty_cell_succ C R d
  exact (TopCat.of C).isZero_singularCohomology_succ_of_projective_homology R M d
    (isZero_singularHomology_of_isEmpty_cell C R (d + 1))

end MissingCellCohomology

end TauCeti

namespace ContinuousMap.HomotopyEquiv

variable {Y X : Type w} [TopologicalSpace Y] [TopologicalSpace X] [T2Space X]
  {C : Set X} [CWComplex C] (e : ContinuousMap.HomotopyEquiv Y C)
include e

/-- Singular homology of a space homotopy equivalent to a CW complex `C` vanishes in any degree `n`
in which `C` has no `n`-cells, whenever the `(n + 1)`-skeleton comparison map is an isomorphism on
`Hₙ` (in particular for finite-dimensional `C` and for modules over any ring). -/
theorem isZero_singularHomology_of_isEmpty_cell {A : Type u} [Category.{v} A]
    [HasCoproducts.{w} A] [Abelian A]
    [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A] (R : A) (n : ℕ)
    [IsIso ((TauCeti.skeletonBasePair C (n + 1)).singularHomologyMap
      (TauCeti.skeletonBasePairToComplex C (n + 1)) R n)]
    [IsEmpty (cell C n)] :
    IsZero (((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of Y)) :=
  (TauCeti.isZero_singularHomology_of_isEmpty_cell C R n).of_iso (e.singularHomologyIso R n)

/-- Over a hereditary abelian category, `H_d(Y; R)` of a space homotopy equivalent to a CW complex
`C` with no `(d + 1)`-cells is projective, with no finiteness assumption on cell counts. -/
theorem projective_singularHomology_of_isEmpty_cell_succ {A : Type u} [Category.{v} A]
    [HasCoproducts.{w} A] [Abelian A] [∀ V : A, HasProjectiveDimensionLE V 1]
    [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A] (R : A) [Projective R] (d : ℕ)
    [IsIso ((TauCeti.skeletonBasePair C (d + 1)).singularHomologyMap
      (TauCeti.skeletonBasePairToComplex C (d + 1)) R d)]
    [IsEmpty (cell C (d + 1))] :
    Projective (((AlgebraicTopology.singularHomologyFunctor.{w} A d).obj R).obj (TopCat.of Y)) :=
  Projective.of_iso (e.singularHomologyIso R d).symm
    (TauCeti.projective_singularHomology_of_isEmpty_cell_succ C R d)

/-- **Top singular homology of a CW model is free over a PID.** If `Y` is homotopy equivalent to a
CW complex `C` having no `(d + 1)`-cells (for instance a `d`-dimensional CW model with arbitrarily
many `d`-cells), then `H_d(Y; M)` is a free `k`-module over any principal ideal ring `k` without
zero divisors (in any universe, including `ℤ`), for any projective `k`-module `M`. -/
theorem free_singularHomology_of_isEmpty_cell_succ {k : Type u} [CommRing k] [NoZeroDivisors k]
    [IsPrincipalIdealRing k] (M : ModuleCat.{w} k) [Module.Projective k M] (d : ℕ)
    [IsEmpty (cell C (d + 1))] :
    Module.Free k
      (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) d).obj M).obj
        (TopCat.of Y)) :=
  have := TauCeti.free_singularHomology_of_isEmpty_cell_succ C M d
  .of_equiv (e.singularHomologyIso M d).symm.toLinearEquiv

/-- **Singular cohomology of a CW model vanishes in degree `d + 1` when the model has no
`(d + 1)`-cells**, over any hereditary commutative ring `k` (in any universe, including `ℤ`), with
no finiteness assumption on cell counts. -/
theorem isZero_singularCohomology_succ_of_isEmpty_cell {k : Type u} [CommRing k]
    [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] (R M : ModuleCat.{w} k)
    [Module.Projective k R] (d : ℕ) [IsEmpty (cell C (d + 1))] :
    IsZero ((TopCat.of Y).singularCohomology R k M (d + 1)) :=
  (TauCeti.isZero_singularCohomology_succ_of_isEmpty_cell R M C d).of_iso
    (e.singularCohomologyIso R k M (d + 1)).symm

/-- **Singular homology vanishes above the CW dimension of a homotopy model.** If `Y` is homotopy
equivalent to a CW complex `C` with no cells in dimensions strictly above `d` (with arbitrary cell
counts in dimensions at most `d`), then `Hₙ(Y; R) = 0` for every `n > d` and every coefficient
object `R` in an abelian category with exact cell coproducts. -/
theorem isZero_singularHomology_of_isEmpty_cell_gt {A : Type u} [Category.{v} A]
    [HasCoproducts.{w} A] [Abelian A]
    [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A] (R : A) {d n : ℕ}
    (h : ∀ m, d < m → IsEmpty (cell C m)) (hn : d < n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of Y)) :=
  have := RelCWComplex.finiteDimensional_of_isEmpty_cell_gt C h
  have := h n hn
  e.isZero_singularHomology_of_isEmpty_cell R n

/-- **Singular cohomology vanishes above the CW dimension of a homotopy model.** If `Y` is homotopy
equivalent to a CW complex `C` with no cells in dimensions strictly above `d` (with arbitrary cell
counts in dimensions at most `d`), then `Hⁿ(Y; R, M) = 0` for every `n > d` over any hereditary
commutative ring `k` (in any universe, including `ℤ`), for any projective `R` and any `k`-module
`M`. -/
theorem isZero_singularCohomology_of_isEmpty_cell_gt {k : Type u} [CommRing k]
    [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] (R M : ModuleCat.{w} k)
    [Module.Projective k R] {d n : ℕ} (h : ∀ m, d < m → IsEmpty (cell C m)) (hn : d < n) :
    IsZero ((TopCat.of Y).singularCohomology R k M n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  have := h (m + 1) hn
  exact e.isZero_singularCohomology_succ_of_isEmpty_cell R M m

end ContinuousMap.HomotopyEquiv

namespace TauCeti

section DimensionBound

variable {X : Type w} [TopologicalSpace X] [T2Space X]

/-- **Relative singular homology of a `d`-dimensional CW pair vanishes above `d`**, in any abelian
category with exact cell coproducts, with no finiteness assumption on cell counts. -/
theorem isZero_singularHomology_complexBasePair_of_isEmpty_cell_gt {D : Set X} (C : Set X)
    [RelCWComplex C D] {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
    [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A] (R : A) {d n : ℕ}
    (h : ∀ m, d < m → IsEmpty (cell C m)) (hn : d < n) :
    IsZero ((complexBasePair C).singularHomology R n) :=
  have := RelCWComplex.finiteDimensional_of_isEmpty_cell_gt C h
  have := h n hn
  isZero_singularHomology_complexBasePair_of_isEmpty_cell C R n

/-- **Relative singular cohomology of a `d`-dimensional CW pair vanishes above `d`**, over any
hereditary commutative ring `k` (in any universe, including `ℤ`), with no finiteness assumption on
cell counts. -/
theorem isZero_singularCohomology_complexBasePair_of_isEmpty_cell_gt {D : Set X} (C : Set X)
    [RelCWComplex C D] {k : Type u} [CommRing k]
    [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] (R M : ModuleCat.{w} k)
    [Module.Projective k R] {d n : ℕ} (h : ∀ m, d < m → IsEmpty (cell C m)) (hn : d < n) :
    IsZero ((complexBasePair C).singularCohomology R k M n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
  have := h (m + 1) hn
  exact isZero_singularCohomology_complexBasePair_succ_of_isEmpty_cell R M C m

/-- **Singular homology of a `d`-dimensional CW complex vanishes above `d`**, in any abelian
category with exact cell coproducts, with no finiteness assumption on cell counts. -/
theorem isZero_singularHomology_of_isEmpty_cell_gt (C : Set X) [CWComplex C] {A : Type u}
    [Category.{v} A] [HasCoproducts.{w} A] [Abelian A]
    [∀ m, HasExactColimitsOfShape (Discrete (cell C m)) A] (R : A) {d n : ℕ}
    (h : ∀ m, d < m → IsEmpty (cell C m)) (hn : d < n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of C)) :=
  (ContinuousMap.HomotopyEquiv.refl C).isZero_singularHomology_of_isEmpty_cell_gt R h hn

/-- **Singular cohomology of a `d`-dimensional CW complex vanishes above `d`**, over any hereditary
commutative ring `k` (in any universe, including `ℤ`), with no finiteness assumption on cell
counts. -/
theorem isZero_singularCohomology_of_isEmpty_cell_gt (C : Set X) [CWComplex C] {k : Type u}
    [CommRing k] [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] (R M : ModuleCat.{w} k)
    [Module.Projective k R] {d n : ℕ} (h : ∀ m, d < m → IsEmpty (cell C m)) (hn : d < n) :
    IsZero ((TopCat.of C).singularCohomology R k M n) :=
  (ContinuousMap.HomotopyEquiv.refl C).isZero_singularCohomology_of_isEmpty_cell_gt R M h hn

section WholeSpace

variable (X) [CWComplex (univ : Set X)]

/-- Top singular homology `H_d(X; R)` of a space with a CW structure on `Set.univ` having no
`(d + 1)`-cells is projective over any hereditary abelian category. -/
theorem projective_singularHomology_univ_of_isEmpty_cell_succ {A : Type u} [Category.{v} A]
    [HasCoproducts.{w} A] [Abelian A] [∀ V : A, HasProjectiveDimensionLE V 1]
    [∀ m, HasExactColimitsOfShape (Discrete (cell (univ : Set X) m)) A] (R : A) [Projective R]
    (d : ℕ) [IsIso ((skeletonBasePair (univ : Set X) (d + 1)).singularHomologyMap
      (skeletonBasePairToComplex (univ : Set X) (d + 1)) R d)]
    [IsEmpty (cell (univ : Set X) (d + 1))] :
    Projective (((AlgebraicTopology.singularHomologyFunctor.{w} A d).obj R).obj (TopCat.of X)) :=
  ((Homeomorph.Set.univ X).symm.toHomotopyEquiv).projective_singularHomology_of_isEmpty_cell_succ
    R d

/-- Top singular homology `H_d(X; M)` of a space with a CW structure on `Set.univ` having no
`(d + 1)`-cells is free over any principal ideal ring without zero divisors (in any universe,
including `ℤ`), regardless of cell counts. -/
theorem free_singularHomology_univ_of_isEmpty_cell_succ {k : Type u} [CommRing k]
    [NoZeroDivisors k] [IsPrincipalIdealRing k] (M : ModuleCat.{w} k) [Module.Projective k M]
    (d : ℕ) [IsEmpty (cell (univ : Set X) (d + 1))] :
    Module.Free k
      (((AlgebraicTopology.singularHomologyFunctor.{w} (ModuleCat.{w} k) d).obj M).obj
        (TopCat.of X)) :=
  ((Homeomorph.Set.univ X).symm.toHomotopyEquiv).free_singularHomology_of_isEmpty_cell_succ M d

/-- Singular cohomology `H^{d+1}(X; R, M)` of a space with a CW structure on `Set.univ` vanishes
whenever there are no `(d + 1)`-cells, over any hereditary commutative ring `k` (including `ℤ`). -/
theorem isZero_singularCohomology_univ_succ_of_isEmpty_cell {k : Type u} [CommRing k]
    [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] (R M : ModuleCat.{w} k)
    [Module.Projective k R] (d : ℕ) [IsEmpty (cell (univ : Set X) (d + 1))] :
    IsZero ((TopCat.of X).singularCohomology R k M (d + 1)) :=
  ((Homeomorph.Set.univ X).symm.toHomotopyEquiv).isZero_singularCohomology_succ_of_isEmpty_cell
    R M d

/-- Singular homology `Hₙ(X; R)` of a space with a `d`-dimensional CW structure on `Set.univ`
vanishes for all `n > d`. -/
theorem isZero_singularHomology_univ_of_isEmpty_cell_gt {A : Type u} [Category.{v} A]
    [HasCoproducts.{w} A] [Abelian A]
    [∀ m, HasExactColimitsOfShape (Discrete (cell (univ : Set X) m)) A] (R : A) {d n : ℕ}
    (h : ∀ m, d < m → IsEmpty (cell (univ : Set X) m)) (hn : d < n) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor.{w} A n).obj R).obj (TopCat.of X)) :=
  ((Homeomorph.Set.univ X).symm.toHomotopyEquiv).isZero_singularHomology_of_isEmpty_cell_gt R h hn

/-- Singular cohomology `Hⁿ(X; R, M)` of a space with a `d`-dimensional CW structure on `Set.univ`
vanishes for all `n > d` over any hereditary commutative ring `k` (including `ℤ`). -/
theorem isZero_singularCohomology_univ_of_isEmpty_cell_gt {k : Type u} [CommRing k]
    [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1] (R M : ModuleCat.{w} k)
    [Module.Projective k R] {d n : ℕ} (h : ∀ m, d < m → IsEmpty (cell (univ : Set X) m))
    (hn : d < n) :
    IsZero ((TopCat.of X).singularCohomology R k M n) :=
  ((Homeomorph.Set.univ X).symm.toHomotopyEquiv).isZero_singularCohomology_of_isEmpty_cell_gt R M
    h hn

end WholeSpace

end DimensionBound

end TauCeti
