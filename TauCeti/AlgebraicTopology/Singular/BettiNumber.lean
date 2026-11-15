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
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.DirectSum.Finsupp
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
of a contractible space vanish (`TauCeti.bettiNumber_eq_zero_of_contractibleSpace`). So a point has
Betti numbers `1, 0, 0, …` over every division ring. The Betti numbers do depend on the
coefficients: for example, the real projective plane has first Betti number `0` over `ℚ` and `1`
over `𝔽₂`.

These are the numbers `bⱼ` of the Morse inequalities: on a compact manifold with a Morse function
having `cⱼ` critical points of index `j`, `∑ cⱼ tʲ = ∑ bⱼ tʲ + (1 + t) Q(t)` with `Q` having
natural number coefficients.

## Main declarations

* `TauCeti.bettiNumber`: the `j`-th Betti number of a space with coefficients in `k`.
* `ContinuousMap.HomotopyEquiv.bettiNumber_eq`: Betti numbers are homotopy invariant.
* `TauCeti.bettiNumber_zero`: the zeroth Betti number is the number of path components.
* `TauCeti.bettiNumber_eq_zero_of_contractibleSpace`: the positive-degree Betti numbers of a
  contractible space vanish.
* `TauCeti.bettiNumber_eq_zero_of_not_finite`, `TauCeti.bettiNumber_eq_rank`: over a division ring,
  the junk value `0` for infinite-dimensional homology and the comparison with `Module.rank`.

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

/-- **The zeroth Betti number counts path components.** Over a ring with the strong rank
condition, such as a division ring or a nontrivial commutative ring, `b₀(X)` is the number of path
components of `X`, or `0` when there are infinitely many. -/
theorem bettiNumber_zero [StrongRankCondition k] :
    bettiNumber k X 0 = Nat.card (ZerothHomotopy X) := by
  classical
  let e := (TopCat.singularHomology₀Iso (TopCat.of X) (ModuleCat.of k k) ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv
  rw [bettiNumber_def, e.finrank_eq, ← (finsuppLEquivDirectSum k k _).finrank_eq]
  exact finrank_eq_nat_card_basis Finsupp.basisSingleOne

variable {X} in
/-- **The positive-degree Betti numbers of a contractible space vanish.** -/
theorem bettiNumber_eq_zero_of_contractibleSpace [Nontrivial k] [ContractibleSpace X] {j : ℕ}
    (hj : j ≠ 0) :
    bettiNumber k X j = 0 := by
  -- The carrier of `TopCat.of X` is `X` itself.
  have : ContractibleSpace (TopCat.of X) := ‹ContractibleSpace X›
  rw [bettiNumber_def, ModuleCat.finrank_singularHomology_of_contractibleSpace, ite_eq_right hj]

end Ring

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

end TauCeti

/-- **Betti numbers are homotopy invariant.** Homotopy equivalent spaces have the same Betti
numbers, with coefficients in any ring. -/
theorem ContinuousMap.HomotopyEquiv.bettiNumber_eq {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (k : Type u) [Ring k] (j : ℕ) :
    TauCeti.bettiNumber k X j = TauCeti.bettiNumber k Y j :=
  (e.singularHomologyIso (ModuleCat.of k k) j).toLinearEquiv.finrank_eq
