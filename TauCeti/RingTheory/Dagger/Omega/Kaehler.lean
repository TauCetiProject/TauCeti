/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.Basic

/-!
# Comparison with algebraic Kähler differentials

If the algebraic Kähler differentials of an algebra are already finite, passing to
universally finite differentials loses nothing. This applies to every essentially finite-type
algebra, in particular to finite algebras over a field, without separability or reducedness.
The comparison identifies the universal derivations, so algebraic computations of differentials
can be used directly for these dagger algebras.

In contrast, the algebraic Kähler differentials of a Monsky–Washnitzer algebra need not be finite;
the comparison here does not assert injectivity in that case.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §4.1.
* E. Grosse-Klönne, *Finiteness of de Rham cohomology in rigid analysis*,
  Duke Math. J. 113 (2002), §1.2.
-/

public section

namespace TauCeti.Dagger.Omega

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

section Finite

variable [Module.Finite A Ω[A⁄R]]

/-- The canonical map to universally finite differentials is injective when the algebraic
differentials are finite. -/
theorem ofKaehler_injective : Function.Injective (ofKaehler R A) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  simpa only [Submodule.mem_bot] using
    (ofKaehler_eq_zero_iff.mp hx) (⊥ : Submodule A Ω[A⁄R]) inferInstance

/-- Algebraic and universally finite differentials coincide when the algebraic differential
module is finite, for example for an essentially finite-type algebra. -/
noncomputable def ofKaehlerEquiv : Ω[A⁄R] ≃ₗ[A] Omega R A :=
  LinearEquiv.ofBijective (ofKaehler R A)
    ⟨ofKaehler_injective R A, ofKaehler_surjective R A⟩

/-- The comparison is induced by the canonical quotient map on every differential. -/
@[simp]
theorem ofKaehlerEquiv_apply (x : Ω[A⁄R]) :
    ofKaehlerEquiv R A x = ofKaehler R A x :=
  (rfl)

/-- The inverse comparison takes the universally finite differential of `a` to its algebraic
Kähler differential. -/
@[simp]
theorem ofKaehlerEquiv_symm_d (a : A) :
    (ofKaehlerEquiv R A).symm (d R A a) = KaehlerDifferential.D R A a := by
  apply (ofKaehlerEquiv R A).injective
  simp

/-- A differential vanishes in the universally finite module exactly when it vanishes in the
algebraic Kähler module, provided the latter is finite. -/
theorem d_eq_zero_iff (a : A) : d R A a = 0 ↔ KaehlerDifferential.D R A a = 0 := by
  rw [← ofKaehler_D, (ofKaehler_injective R A).eq_iff' (map_zero _)]

end Finite

end TauCeti.Dagger.Omega
