/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.ConnectedComponents
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Finsupp
import TauCeti.Algebra.Category.ModuleCat.Products
import TauCeti.AlgebraicTopology.Singular.Additivity
import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# Betti numbers

The `j`-th Betti number `bettiNumber k X j` of a topological space `X` with coefficients in a ring
`k` is the dimension `Module.finrank k Hⱼ(X; k)` of its `j`-th singular homology with coefficients
in `k`. Following the convention of `Module.finrank`, it is `0` when that homology has infinite
rank; over a division ring this happens exactly when the homology is not finitely generated, but
over a general ring a module that is not finitely generated may still have finite rank (over `ℤ`,
the module `ℤ[1/2]` has rank `1`). Statements reading it as a dimension carry a finiteness
hypothesis, such as compactness of a manifold or finiteness of a CW model. Over `ℤ` it is the
rank of the homology group, which for finitely generated homology is the classical Betti number.

The Betti numbers are invariants of homotopy type
(`ContinuousMap.HomotopyEquiv.bettiNumber_eq`). Over a division ring, or any ring with the strong
rank condition, the zeroth Betti number counts the path components (`TauCeti.bettiNumber_zero`),
again with the junk value `0` when there are infinitely many, and the positive-degree Betti numbers
of a contractible space vanish (`TauCeti.bettiNumber_eq_zero_of_contractibleSpace`). So a point, or
any contractible space, has Betti numbers `1, 0, 0, …` over every division ring
(`TauCeti.bettiNumber_of_contractibleSpace`). A totally disconnected space, such as a
discrete one, has zeroth homology free on its points
(`TauCeti.singularHomologyZeroLinearEquivFinsuppOfTotallyDisconnectedSpace`) and no homology in
positive degrees (`TauCeti.subsingleton_singularHomology_of_totallyDisconnectedSpace`); so `r`
points have Betti numbers `r, 0, 0, …`, while for the discrete space `ℕ` the rank of `H₀` is
`ℵ₀` and the Betti number `b₀(ℕ)` is the junk value `0` (`TauCeti.bettiNumber_zero_nat`). These
rest on Andrew Yang's calculation of the singular homology of totally disconnected spaces in
Mathlib (`AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace`). The Betti
numbers do depend on the coefficients: for example, the real projective plane has first Betti
number `0` over `ℚ` and `1` over `𝔽₂`.

Over a division ring the Betti numbers are additive over a partition of `X` into finitely many
open sets (`TauCeti.bettiNumber_eq_sum`), in particular over the connected components of a locally
connected space with finitely many of them (`TauCeti.bettiNumber_eq_sum_connectedComponents`),
provided the homology of `X` is finite-dimensional in the degree considered. This is the additivity
of singular homology over disjoint open sets (`TauCeti.isColimitCofanSingularHomologyOpens`).

These are the numbers `bⱼ` of the Morse inequalities: on a compact manifold with a Morse function
having `cⱼ` critical points of index `j`, `∑ cⱼ tʲ = ∑ bⱼ tʲ + (1 + t) Q(t)` with `Q` having
natural number coefficients.

## Main declarations

* `TauCeti.bettiNumber`: the `j`-th Betti number of a space with coefficients in `k`.
* `TauCeti.finrank_singularHomology_uLift_eq_bettiNumber`: the Betti numbers read with
  coefficients in `ULift k`.
* `ContinuousMap.HomotopyEquiv.bettiNumber_eq`: Betti numbers are homotopy invariant.
* `TauCeti.bettiNumber_zero`: the zeroth Betti number is the number of path components.
* `TauCeti.rank_singularHomology_zero`: the cardinal rank of the zeroth homology is the cardinal
  number of path components, which stays meaningful when there are infinitely many.
* `TauCeti.rank_singularHomology_zero_of_discreteTopology`: for a discrete space, that rank is
  the cardinal number of points.
* `TauCeti.bettiNumber_zero_eq_one`: a path-connected space has zeroth Betti number one.
* `TauCeti.bettiNumber_eq_zero_of_contractibleSpace`: the positive-degree Betti numbers of a
  contractible space vanish.
* `TauCeti.bettiNumber_of_contractibleSpace`: the Betti numbers of a contractible space are
  `1, 0, 0, …`.
* `TauCeti.singularHomologyZeroLinearEquivFinsuppOfTotallyDisconnectedSpace`,
  `TauCeti.subsingleton_singularHomology_of_totallyDisconnectedSpace`,
  `TauCeti.rank_singularHomology_zero_of_totallyDisconnectedSpace`,
  `TauCeti.bettiNumber_zero_of_totallyDisconnectedSpace` and
  `TauCeti.bettiNumber_eq_zero_of_totallyDisconnectedSpace`: the homology of a totally
  disconnected space.
* `TauCeti.rank_singularHomology_zero_nat` and `TauCeti.bettiNumber_zero_nat`: the infinite rank
  of `H₀(ℕ)` and the resulting junk value of `b₀(ℕ)`.
* `TauCeti.bettiNumber_eq_zero_of_not_finite`, `TauCeti.bettiNumber_eq_rank`: over a division ring,
  the junk value `0` for infinite-dimensional homology and the comparison with `Module.rank`.
* `TauCeti.bettiNumber_eq_sum`, `TauCeti.bettiNumber_eq_sum_connectedComponents`: additivity over
  finite partitions into open sets and over connected components.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1 (Proposition 2.7 for zeroth homology) and Section 2.2 (Betti numbers).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Module
open scoped ContinuousMap

universe u

namespace TauCeti

section Ring

variable (k : Type u) [Ring k] (X : Type u) [TopologicalSpace X]

/-- The `j`-th **Betti number** of a topological space `X` with coefficients in the ring `k`: the
dimension over `k` of the `j`-th singular homology of `X` with coefficients in `k`. It is `0` when
this homology has infinite rank, which over a division ring means that it is not finitely
generated. -/
def bettiNumber (j : ℕ) : ℕ :=
  finrank k (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)).obj
    (TopCat.of X))

/-- The `j`-th Betti number is the dimension of the `j`-th singular homology. -/
theorem bettiNumber_def (j : ℕ) :
    bettiNumber k X j = finrank k
      (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)).obj
        (TopCat.of X)) :=
  (rfl)

/-- **The zeroth homology has rank the number of path components.** Over a ring with the strong
rank condition, `H₀(X; k)` is free on the path components of `X`, so its rank is their cardinal
number, also when there are infinitely many. -/
theorem rank_singularHomology_zero [StrongRankCondition k] :
    Module.rank k (((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj
      (TopCat.of X)) = Cardinal.mk (ZerothHomotopy X) := by
  classical
  let e := (TopCat.singularHomology₀Iso (TopCat.of X) (ModuleCat.of k k) ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv
  rw [e.rank_eq, ← (finsuppLEquivDirectSum k k _).rank_eq, rank_finsupp_self']

/-- **The zeroth Betti number counts path components.** Over a ring with the strong rank
condition, such as a division ring or a nontrivial commutative ring, `b₀(X)` is the number of path
components of `X`, or `0` when there are infinitely many. -/
theorem bettiNumber_zero [StrongRankCondition k] :
    bettiNumber k X 0 = Nat.card (ZerothHomotopy X) := by
  rw [bettiNumber_def, finrank, rank_singularHomology_zero, Nat.card]

/-- **The zeroth homology of a discrete space.** In a discrete space every path is constant, so the
path components are the points and `H₀(X; k)` has rank the cardinal number of `X`. -/
theorem rank_singularHomology_zero_of_discreteTopology [StrongRankCondition k]
    [DiscreteTopology X] :
    Module.rank k (((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj
      (TopCat.of X)) = Cardinal.mk X := by
  have hinj : Function.Injective (ZerothHomotopy.mk : X → ZerothHomotopy X) := fun x y h ↦ by
    obtain ⟨γ⟩ := Quotient.exact h
    simpa using γ.continuous.isConst_of_preconnectedSpace 0 1
  rw [rank_singularHomology_zero,
    Cardinal.mk_congr (Equiv.ofBijective _ ⟨hinj, Quotient.mk_surjective⟩).symm]

variable {X} in
/-- **The zeroth Betti number of a path-connected space is one.** -/
theorem bettiNumber_zero_eq_one [StrongRankCondition k] [PathConnectedSpace X] :
    bettiNumber k X 0 = 1 := by
  rw [bettiNumber_zero, Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, inferInstance⟩

variable {X} in
/-- **The positive-degree Betti numbers of a contractible space vanish.** -/
theorem bettiNumber_eq_zero_of_contractibleSpace [Nontrivial k] [ContractibleSpace X] {j : ℕ}
    (hj : j ≠ 0) :
    bettiNumber k X j = 0 := by
  -- The carrier of `TopCat.of X` is `X` itself.
  have : ContractibleSpace (TopCat.of X) := ‹ContractibleSpace X›
  rw [bettiNumber_def, ModuleCat.finrank_singularHomology_of_contractibleSpace, ite_eq_right hj]

variable {X} in
/-- **The Betti numbers of a contractible space**, such as a point, are `1` in degree zero and `0`
in every positive degree, over a ring with the strong rank condition. -/
theorem bettiNumber_of_contractibleSpace [StrongRankCondition k] [ContractibleSpace X] (j : ℕ) :
    bettiNumber k X j = if j = 0 then 1 else 0 := by
  have : ContractibleSpace (TopCat.of X) := ‹ContractibleSpace X›
  rw [bettiNumber_def, ModuleCat.finrank_singularHomology_of_contractibleSpace]
  simp

/-- The Betti numbers may be read with coefficients in `ULift k`, as for singular homology computed
as twisted homology with constant coefficients. -/
theorem finrank_singularHomology_uLift_eq_bettiNumber (j : ℕ) :
    finrank k (((singularHomologyFunctor (ModuleCat.{u} k) j).obj
        (ModuleCat.of k (ULift.{u} k))).obj (TopCat.of X)) = bettiNumber k X j := by
  rw [bettiNumber_def]
  exact ((((singularHomologyFunctor (ModuleCat.{u} k) j).mapIso
    ULift.moduleEquiv.toModuleIso).app (TopCat.of X)).toLinearEquiv).finrank_eq

end Ring

section TotallyDisconnected

variable (k : Type u) [Ring k] (X : Type u) [TopologicalSpace X] [TotallyDisconnectedSpace X]

/-- The zeroth singular homology of a totally disconnected space is linearly equivalent to the
free module on its points. -/
def singularHomologyZeroLinearEquivFinsuppOfTotallyDisconnectedSpace :
    ((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj (TopCat.of X) ≃ₗ[k]
      (X →₀ k) :=
  -- The carrier of `TopCat.of X` is `X` itself.
  have : TotallyDisconnectedSpace (TopCat.of X) := ‹TotallyDisconnectedSpace X›
  (singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat.{u} k) (ModuleCat.of k k)
      (TopCat.of X)).toLinearEquiv ≪≫ₗ ModuleCat.coprodLinearEquivFinsupp (ModuleCat.of k k) X

/-- **The positive-degree homology of a totally disconnected space vanishes.** Every singular
simplex in `X` is constant, so the singular chain complex is the constant complex on the free
module on `X`, with differentials alternately zero and the identity. -/
theorem subsingleton_singularHomology_of_totallyDisconnectedSpace {j : ℕ} (hj : j ≠ 0) :
    Subsingleton
      (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)).obj
        (TopCat.of X)) :=
  -- The carrier of `TopCat.of X` is `X` itself.
  have : TotallyDisconnectedSpace (TopCat.of X) := ‹TotallyDisconnectedSpace X›
  ModuleCat.isZero_iff_subsingleton.1
    (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ j (ModuleCat.of k k)
      (TopCat.of X) hj)

/-- **The zeroth homology of a totally disconnected space has rank its number of points.** Over a
ring with the strong rank condition, `H₀(X; k)` is free on the points of `X`, so its rank is the
cardinality of `X`, also when `X` is infinite. -/
theorem rank_singularHomology_zero_of_totallyDisconnectedSpace [StrongRankCondition k] :
    Module.rank k
        (((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj
          (TopCat.of X)) =
      Cardinal.mk X := by
  rw [(singularHomologyZeroLinearEquivFinsuppOfTotallyDisconnectedSpace k X).rank_eq,
    rank_finsupp_self']

/-- **The zeroth homology of a totally disconnected space is finitely generated exactly when the
space is finite**, over a nontrivial ring. -/
theorem finite_singularHomology_zero_iff_of_totallyDisconnectedSpace [Nontrivial k] :
    Module.Finite k
        (((singularHomologyFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)).obj
          (TopCat.of X)) ↔
      Finite X := by
  rw [Module.Finite.equiv_iff
      (singularHomologyZeroLinearEquivFinsuppOfTotallyDisconnectedSpace k X),
    Module.finite_finsupp_self_iff]
  simp [not_subsingleton k]

/-- **The zeroth Betti number of a totally disconnected space is its number of points**, or `0`
when it is infinite, over a ring with the strong rank condition. -/
theorem bettiNumber_zero_of_totallyDisconnectedSpace [StrongRankCondition k] :
    bettiNumber k X 0 = Nat.card X := by
  rw [bettiNumber_def, Module.finrank, rank_singularHomology_zero_of_totallyDisconnectedSpace,
    Cardinal.toNat_mk]

/-- **The positive-degree Betti numbers of a totally disconnected space vanish**, since the
homology itself vanishes (`TauCeti.subsingleton_singularHomology_of_totallyDisconnectedSpace`). -/
theorem bettiNumber_eq_zero_of_totallyDisconnectedSpace [Nontrivial k] {j : ℕ} (hj : j ≠ 0) :
    bettiNumber k X j = 0 := by
  have := subsingleton_singularHomology_of_totallyDisconnectedSpace k X hj
  rw [bettiNumber_def, Module.finrank_zero_of_subsingleton]

end TotallyDisconnected

section Nat

variable (k : Type) [Ring k] [StrongRankCondition k]

/-- **The zeroth homology of `ℕ` has countably infinite rank.** The discrete space `ℕ` has one
path component for each natural number, so `H₀(ℕ; k)` is free of rank `ℵ₀`. -/
theorem rank_singularHomology_zero_nat :
    Module.rank k
        (((singularHomologyFunctor (ModuleCat.{0} k) 0).obj (ModuleCat.of k k)).obj
          (TopCat.of ℕ)) =
      Cardinal.aleph0 := by
  rw [rank_singularHomology_zero_of_totallyDisconnectedSpace, Cardinal.mk_nat]

/-- **The zeroth Betti number of `ℕ` is the junk value `0`.** Since `H₀(ℕ; k)` has infinite rank
(`TauCeti.rank_singularHomology_zero_nat`), the dimension-valued Betti number `b₀(ℕ)` is `0`,
although `ℕ` has infinitely many path components. -/
theorem bettiNumber_zero_nat : bettiNumber k ℕ 0 = 0 := by
  rw [bettiNumber_zero_of_totallyDisconnectedSpace, Nat.card_eq_zero_of_infinite]

end Nat

/-- Over a division ring, the Betti number is zero when the singular homology is not
finite-dimensional. -/
@[simp]
theorem bettiNumber_eq_zero_of_not_finite (k : Type u) [DivisionRing k]
    (X : Type u) [TopologicalSpace X] (j : ℕ)
    (h : ¬Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)).obj
        (TopCat.of X))) :
    bettiNumber k X j = 0 := by
  rw [bettiNumber_def]
  exact finrank_of_not_finite h

/-- Over a division ring, for finite-dimensional singular homology, the Betti number casts to its
cardinal rank. -/
@[simp]
theorem bettiNumber_eq_rank (k : Type u) [DivisionRing k]
    (X : Type u) [TopologicalSpace X] (j : ℕ)
    [Module.Finite k
      (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)).obj
        (TopCat.of X))] :
    (bettiNumber k X j : Cardinal) =
      Module.rank k (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)).obj
        (TopCat.of X)) := by
  rw [bettiNumber_def]
  exact finrank_eq_rank ..

section Opens

open Function TopologicalSpace

variable {k : Type u} [DivisionRing k] {X : Type u} [TopologicalSpace X] {ι : Type u} [Fintype ι]

/-- **Betti numbers are additive over a finite partition into open sets.** If `X` is the union of
finitely many pairwise disjoint open sets `s i` and `Hⱼ(X; k)` is finite-dimensional, then
`bⱼ(X; k) = ∑ᵢ bⱼ(s i; k)`. Without the finiteness hypothesis the left side may be the junk value
`0` while some summands on the right are not. -/
theorem bettiNumber_eq_sum (s : ι → Opens X) (hs : Pairwise (Disjoint on s))
    (hX : ⨆ i, s i = ⊤) (j : ℕ)
    [Module.Finite k (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)).obj
      (TopCat.of X))] :
    bettiNumber k X j = ∑ i, bettiNumber k (s i) j := by
  classical
  let F := (singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)
  -- `X` is the union `⨆ i, s i`, whose homology is the coproduct of the homologies of the `s i`.
  let eX : TopCat.of X ≅ TopCat.of ↥(⨆ i, s i) := TopCat.isoOfHomeo
    ((Homeomorph.Set.univ X).symm.trans (Homeomorph.setCongr (by rw [hX, Opens.coe_top])))
  let eS : F.obj (TopCat.of ↥(⨆ i, s i)) ≅ ∐ fun i ↦ F.obj (TopCat.of (s i)) :=
    (isColimitCofanSingularHomologyOpens s (ModuleCat.{u} k) (ModuleCat.of k k) j
      hs).coconePointUniqueUpToIso (colimit.isColimit _)
  let e := (F.mapIso eX ≪≫ eS ≪≫ ModuleCat.coprodIsoDirectSum _).toLinearEquiv
  -- Each summand of a finite-dimensional direct sum is finite-dimensional.
  have : Module.Finite k (DirectSum ι fun i ↦ F.obj (TopCat.of (s i))) := Module.Finite.equiv e
  have (i : ι) : Module.Finite k (F.obj (TopCat.of (s i))) :=
    Module.Finite.of_surjective (DirectSum.component k ι (fun i ↦ F.obj (TopCat.of (s i))) i)
      fun x ↦ ⟨DirectSum.lof k ι _ i x,
        DirectSum.component.lof_self (M := fun i ↦ F.obj (TopCat.of (s i))) k i x⟩
  simp only [bettiNumber_def]
  rw [e.finrank_eq, finrank_directSum]

/-- **Betti numbers are additive over connected components.** In a locally connected space `X`
with finitely many connected components, each of them open, if `Hⱼ(X; k)` is finite-dimensional
then `bⱼ(X; k)` is the sum of the `bⱼ` of the components. -/
theorem bettiNumber_eq_sum_connectedComponents [LocallyConnectedSpace X]
    [Fintype (ConnectedComponents X)] (j : ℕ)
    [Module.Finite k (((singularHomologyFunctor (ModuleCat.{u} k) j).obj (ModuleCat.of k k)).obj
      (TopCat.of X))] :
    bettiNumber k X j = ∑ C : ConnectedComponents X, bettiNumber k C.opens j :=
  bettiNumber_eq_sum _ ConnectedComponents.pairwise_disjoint_opens ConnectedComponents.iSup_opens j

end Opens

end TauCeti

/-- **Betti numbers are homotopy invariant.** Homotopy equivalent spaces have the same Betti
numbers, with coefficients in any ring. -/
theorem ContinuousMap.HomotopyEquiv.bettiNumber_eq {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (k : Type u) [Ring k] (j : ℕ) :
    TauCeti.bettiNumber k X j = TauCeti.bettiNumber k Y j :=
  (e.singularHomologyIso (ModuleCat.of k k) j).toLinearEquiv.finrank_eq
