/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Genus
public import TauCeti.AlgebraicGeometry.Curves.Normalization
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness

/-!
# The normalization genus of a curve

Let `X` be a curve over a field `k`: an integral scheme, proper of dimension one over `k`
(`AlgebraicGeometry.Scheme.IsCurveOver`). Its normalization `X^ν` in its function field is again a
curve over `k` (`TauCeti.AlgebraicGeometry.isCurveOver_normalization`), and it is regular, so its
codimension-one local rings are discrete valuation rings and `H¹(X^ν, 𝒪)` is finite-dimensional
over `k`. This file defines the **normalization genus** of `X` as the genus
`dim_k H¹(X^ν, 𝒪)` of `X^ν`.

Over an algebraically closed field, this is the geometric genus of `X`, the genus attached to a
reduced irreducible component of a geometric fibre in the stability conditions for curves and
stable maps. Over an arbitrary field it need not be: when `k' = H⁰(X^ν, 𝒪)` is larger than `k`, the
`k`-dimension counts `[k' : k]` times the `k'`-dimension, and over an imperfect field the genus can
drop after base change to an algebraic closure and renormalization.

## Main declarations

* `AlgebraicGeometry.Scheme.normalizationGenus`: the genus of the normalization of a curve.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.3.8 (normalization) and Chapter IV, §1.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [X.IsCurveOver k]

/-- The **normalization genus** of a curve `X` over a field `k`: the genus `dim_k H¹(X^ν, 𝒪)` of
its normalization `X^ν` in its function field. When `k` is algebraically closed this is the
geometric genus of `X`, the genus of a reduced irreducible component of a geometric fibre used in
stability conditions for curves and maps. -/
noncomputable def normalizationGenus : ℕ :=
  (X.fromSpecStalk (genericPoint X)).normalization.genus k

/-- The normalization genus is the genus of the normalization. -/
theorem normalizationGenus_def :
    X.normalizationGenus k = (X.fromSpecStalk (genericPoint X)).normalization.genus k :=
  normalizationGenus.eq_def k X

end AlgebraicGeometry.Scheme
