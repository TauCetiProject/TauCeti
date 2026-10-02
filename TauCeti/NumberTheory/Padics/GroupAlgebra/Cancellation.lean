/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.KrullSchmidt.AdicComplete

/-!
# Krull-Schmidt cancellation over finite `p`-adic group algebras

For a finite monoid `G`, in particular a finite group, finitely generated modules over the group
algebra `ℤ_p[G]` cancel from direct sums: `M × P ≃ N × P` with `P` finitely generated gives
`M ≃ N`. This is the specialization to `R = ℤ_p` and `A = ℤ_p[G]` of
`TauCeti.nonempty_linearEquiv_of_prod_linearEquiv_of_isAdicComplete`; a finitely generated
`ℤ_p[G]`-module is finitely generated over `ℤ_p` because `ℤ_p[G]` is.

⚠ The corresponding statement over `ℤ[G]` fails in general: Swan's stably free, non-free modules
over the integral group rings of generalized quaternion groups. The completeness of `ℤ_p` is what
makes the endomorphism rings of indecomposable `ℤ_p[G]`-modules local.

## Main results

* `TauCeti.nonempty_linearEquiv_of_prod_linearEquiv`: finitely generated `ℤ_p[G]`-modules cancel.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Proposition (5.6.10)(i).
-/

public section

namespace TauCeti

universe u v w x

variable (p : ℕ) [Fact p.Prime] (G : Type u) [Monoid G] [Finite G]

/-- **Krull-Schmidt cancellation over `ℤ_p[G]`** (NSW (5.6.10)(i)). For a finite monoid `G`, in
particular a finite group, a finitely generated `ℤ_p[G]`-module `P` cancels from direct sums: a
linear equivalence `M × P ≃ N × P` induces a linear equivalence `M ≃ N`. No hypothesis is placed
on `M` and `N`. -/
theorem nonempty_linearEquiv_of_prod_linearEquiv (M : Type v) (N : Type w) (P : Type x)
    [AddCommGroup M] [Module (MonoidAlgebra ℤ_[p] G) M]
    [AddCommGroup N] [Module (MonoidAlgebra ℤ_[p] G) N]
    [AddCommGroup P] [Module (MonoidAlgebra ℤ_[p] G) P]
    [Module.Finite (MonoidAlgebra ℤ_[p] G) P]
    (h : Nonempty ((M × P) ≃ₗ[MonoidAlgebra ℤ_[p] G] (N × P))) :
    Nonempty (M ≃ₗ[MonoidAlgebra ℤ_[p] G] N) := by
  -- Give `P` the `ℤ_p`-module structure restricted from `ℤ_p[G]`; then `P` is finite over `ℤ_p`.
  let _ : Module ℤ_[p] P := .compHom P (algebraMap ℤ_[p] (MonoidAlgebra ℤ_[p] G))
  have : IsScalarTower ℤ_[p] (MonoidAlgebra ℤ_[p] G) P :=
    IsScalarTower.of_compHom ℤ_[p] (MonoidAlgebra ℤ_[p] G) P
  have : Module.Finite ℤ_[p] P := .trans (MonoidAlgebra ℤ_[p] G) P
  exact nonempty_linearEquiv_of_prod_linearEquiv_of_isAdicComplete ℤ_[p] h

end TauCeti
