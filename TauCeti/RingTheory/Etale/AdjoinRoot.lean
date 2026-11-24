/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.StandardEtale
public import TauCeti.RingTheory.AdjoinRoot.Separable
public import TauCeti.RingTheory.Unramified.AdjoinRoot

/-!
# Adjoining a root of a separable monic polynomial is étale

Let `f` be a monic polynomial over a commutative ring `R` which is separable, that is, coprime to
its derivative. Then `R[X]/(f)` is a standard étale `R`-algebra, hence étale over `R`
(`Polynomial.Monic.isStandardEtale_adjoinRoot`). This is the presentation `R[X][1/g]/(f)` of
Mathlib's `StandardEtalePair` with `g = 1`: the derivative of `f` is already invertible modulo
`f`. Conversely, `Monic.etale_adjoinRoot_iff` shows that étaleness forces this separability
condition.

Typical examples are `X ^ n - 1`, and its factors such as the cyclotomic polynomial `Φ_n`, over a
ring in which `n` is invertible.

## References

* Mathlib's `Mathlib.RingTheory.Etale.StandardEtale`, for `StandardEtalePair` and the
  equivalence `StandardEtalePair.equivAwayAdjoinRoot` of its algebra with `(R[X]/(f))[1/g]`;
  for `g = 1` this localization is `R[X]/(f)` itself by `IsLocalization.atUnit`.
* [Stacks Project, Definition 10.144.1](https://stacks.math.columbia.edu/tag/00UB), for
  standard étale maps.
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] {f : R[X]}

/-- **Adjoining a root of a separable monic polynomial gives a standard étale algebra.** If `f`
is monic and coprime to its derivative, then `R[X]/(f)` is standard étale over `R`; in particular
it is étale. -/
theorem Monic.isStandardEtale_adjoinRoot (hf : f.Monic) (hs : f.Separable) :
    Algebra.IsStandardEtale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := (separable_def' f).mp hs
  -- The standard étale pair `(f, 1)`: the derivative `f'` is already invertible modulo `f`.
  let P : StandardEtalePair R := ⟨f, hf, 1, b, a, 0, by linear_combination hab⟩
  -- Its algebra is `(R[X]/(f))[1/1]`, which is `R[X]/(f)` since `1` is a unit.
  exact .of_equiv <| P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ _ (AdjoinRoot.mk f 1) (by simp)).restrictScalars R).symm

/-- A monic polynomial defines an étale algebra exactly when it is coprime to its derivative. -/
@[simp]
theorem Monic.etale_adjoinRoot_iff (hf : f.Monic) :
    Algebra.Etale R (AdjoinRoot f) ↔ f.Separable :=
  ⟨fun _ ↦ separable_iff_isUnit_mk_derivative.mpr
      f.isUnit_mk_derivative_of_formallyUnramified_adjoinRoot,
    fun hs ↦ have := hf.isStandardEtale_adjoinRoot hs; inferInstance⟩

end Polynomial
