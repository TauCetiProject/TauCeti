/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient.Field

/-!
# The Euler characteristic from singular cohomology

Over a field `k`, singular cohomology is the dual of singular homology
(`TopCat.singularCohomologyDualEquiv`).  For a space of finite CW type the homology is
finite-dimensional and vanishes in large degrees, so the cohomology is finite-dimensional of the
same dimension in every degree and also vanishes in large degrees.  Hence the Euler characteristic
is also the alternating sum of the dimensions of singular cohomology with coefficients in `k`.

## Main declarations

* `TauCeti.finite_singularCohomology_of_finiteCWType` and
  `TauCeti.eventually_isZero_singularCohomology_of_finiteCWType`: over a field, the singular
  cohomology of a space of finite CW type is finite-dimensional in every degree and vanishes in all
  large degrees.
* `TauCeti.eulerChar_eq_finsum_finrank_singularCohomology`: `eulerChar X` is the alternating sum of
  the dimensions of the singular cohomology of `X` over any field.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44, and Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open CategoryTheory Module AlgebraicTopology

universe w

namespace TauCeti

variable (X : Type w) [TopologicalSpace X] [FiniteCWType X] (k : Type w) [Field k]

/-- Over a field, the singular cohomology of a space of finite CW type is finite-dimensional in
every degree. -/
theorem finite_singularCohomology_of_finiteCWType (n : ℕ) :
    Module.Finite k
      ((TopCat.of X).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) :=
  (TopCat.finite_singularCohomology_iff _ n).2
    (finite_singularHomology_of_finiteCWType X (ModuleCat.of k k) n)

/-- Over a field, the singular cohomology of a space of finite CW type vanishes in all sufficiently
large degrees. -/
theorem eventually_isZero_singularCohomology_of_finiteCWType :
    ∀ᶠ n in Filter.atTop, Limits.IsZero
      ((TopCat.of X).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) n) := by
  filter_upwards [eventually_isZero_singularHomology_of_finiteCWType X (ModuleCat.of k k)] with n hn
  have := ModuleCat.subsingleton_of_isZero hn
  have := ((TopCat.of X).singularCohomologyDualEquiv (k := k) n).subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- **Euler--Poincaré in cohomology** for a space of finite CW type: its Euler characteristic is
the alternating sum of the dimensions of its singular cohomology over any field. -/
theorem eulerChar_eq_finsum_finrank_singularCohomology :
    eulerChar X = ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * finrank k
      ((TopCat.of X).singularCohomology (ModuleCat.of k k) k (ModuleCat.of k k) i) := by
  simp [eulerChar_eq_finsum_finrank_singularHomology X k]

end TauCeti
