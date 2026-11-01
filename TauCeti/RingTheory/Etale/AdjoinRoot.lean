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

* Mathlib's `Mathlib.RingTheory.Etale.StandardEtale`, for `StandardEtalePair` and its
  universal mapping API.
* [Stacks Project, Definition 10.144.1](https://stacks.math.columbia.edu/tag/00UB), for
  standard étale maps.
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] {f : R[X]}

/-- The standard étale pair `(f, 1)` of a separable monic polynomial `f`. -/
private noncomputable def standardEtalePairOfSeparable (hf : f.Monic) (hs : f.Separable) :
    StandardEtalePair R where
  f := f
  monic_f := hf
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := (separable_def' f).mp hs
    exact ⟨b, a, 0, by rw [pow_zero, ← hab]; ring⟩

/-- **Adjoining a root of a separable monic polynomial gives a standard étale algebra.** If `f`
is monic and coprime to its derivative, then `R[X]/(f)` is standard étale over `R`; in particular
it is étale. -/
theorem Monic.isStandardEtale_adjoinRoot (hf : f.Monic) (hs : f.Separable) :
    Algebra.IsStandardEtale R (AdjoinRoot f) := by
  let P := standardEtalePairOfSeparable hf hs
  have hroot : P.HasMap (AdjoinRoot.root f) :=
    ⟨AdjoinRoot.aeval_eq f ▸ AdjoinRoot.mk_self, by simp [P, standardEtalePairOfSeparable]⟩
  have hX : f.eval₂ (Algebra.ofId R P.Ring : R →+* P.Ring) P.X = 0 := P.hasMap_X.1
  let φ : P.Ring →ₐ[R] AdjoinRoot f := P.lift _ hroot
  let ψ : AdjoinRoot f →ₐ[R] P.Ring := AdjoinRoot.liftAlgHom f (Algebra.ofId R _) P.X hX
  have hψ : ψ (AdjoinRoot.root f) = P.X := AdjoinRoot.liftAlgHom_root f _ _ hX
  have hφψ : φ.comp ψ = AlgHom.id R _ :=
    AdjoinRoot.algHom_ext (by rw [AlgHom.comp_apply, hψ]; exact P.lift_X _ hroot)
  have hψφ : ψ.comp φ = AlgHom.id R _ :=
    P.hom_ext (by rw [AlgHom.comp_apply, P.lift_X, hψ, AlgHom.id_apply])
  have : Algebra.IsStandardEtale R P.Ring := inferInstance
  exact this.of_equiv (AlgEquiv.ofAlgHom φ ψ hφψ hψφ)

/-- A monic polynomial defines an étale algebra exactly when it is coprime to its derivative. -/
@[simp]
theorem Monic.etale_adjoinRoot_iff (hf : f.Monic) :
    Algebra.Etale R (AdjoinRoot f) ↔ f.Separable := by
  constructor
  · intro h
    exact separable_iff_isUnit_mk_derivative.mpr
      (f.isUnit_mk_derivative_of_formallyUnramified_adjoinRoot)
  · intro hs
    have := hf.isStandardEtale_adjoinRoot hs
    infer_instance

end Polynomial
