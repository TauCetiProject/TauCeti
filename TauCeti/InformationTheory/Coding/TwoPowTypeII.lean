/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.Basic
public import TauCeti.InformationTheory.Coding.EuclideanDual
public import TauCeti.InformationTheory.Coding.Weight.Euclidean
public import Mathlib.Algebra.Module.ZMod

/-!
# Type II codes over `ℤ/2^r`

Following Dougherty, Gulliver, and Harada, a Type II code over `ℤ/2^r` is an additive code which
is self-dual for the `ℤ/2^r` dot product and all of whose Euclidean weights are divisible by
`2^(r+1)`. These are exactly the codes whose Construction A lattices are even and unimodular.

The notion is specific to moduli which are powers of two, so the predicate is stated only for
codes over `ℤ/2^r`; it is not a predicate on codes over an arbitrary `ℤ/m`. The intended range is
`r ≥ 1`: at `r = 0` every code over the trivial ring `ℤ/1` satisfies it, and the theorems which
consume it assume `r ≠ 0`. At `r = 1` it is the binary Type II condition, since binary Euclidean
weights are Hamming weights.

## References

* S. T. Dougherty, T. A. Gulliver, and M. Harada, *Type II self-dual codes over finite rings
  and even unimodular lattices*, J. Algebraic Combin. **9** (1999), 233–250.
-/

public section

namespace TauCeti.TwoPowCode

variable {ι : Type*} [Fintype ι] {r : ℕ} {C : AdditiveCode (ZMod (2 ^ r)) ι}

/-- A **Type II code over `ℤ/2^r`** is an additive code which is Euclidean self-dual and all of
whose Euclidean weights are divisible by `2^(r+1)`. -/
def IsTypeII (r : ℕ) (C : AdditiveCode (ZMod (2 ^ r)) ι) : Prop :=
  AddSubgroup.toZModSubmodule (2 ^ r) C = (AddSubgroup.toZModSubmodule (2 ^ r) C).euclideanDual ∧
    ∀ x ∈ C, 2 ^ (r + 1) ∣ euclideanWeight x

theorem isTypeII_iff :
    IsTypeII r C ↔
      AddSubgroup.toZModSubmodule (2 ^ r) C =
          (AddSubgroup.toZModSubmodule (2 ^ r) C).euclideanDual ∧
        ∀ x ∈ C, 2 ^ (r + 1) ∣ euclideanWeight x :=
  Iff.rfl

/-- A Type II code over `ℤ/2^r` is Euclidean self-dual. -/
theorem IsTypeII.eq_euclideanDual (hC : IsTypeII r C) :
    AddSubgroup.toZModSubmodule (2 ^ r) C =
      (AddSubgroup.toZModSubmodule (2 ^ r) C).euclideanDual :=
  hC.1

/-- A Type II code over `ℤ/2^r` is Euclidean self-orthogonal. -/
theorem IsTypeII.le_euclideanDual (hC : IsTypeII r C) :
    AddSubgroup.toZModSubmodule (2 ^ r) C ≤
      (AddSubgroup.toZModSubmodule (2 ^ r) C).euclideanDual :=
  hC.eq_euclideanDual.le

/-- Every word of a Type II code over `ℤ/2^r` has Euclidean weight divisible by `2^(r+1)`. -/
theorem IsTypeII.two_pow_succ_dvd_euclideanWeight (hC : IsTypeII r C) {x : ι → ZMod (2 ^ r)}
    (hx : x ∈ C) : 2 ^ (r + 1) ∣ euclideanWeight x :=
  hC.2 x hx

end TauCeti.TwoPowCode
