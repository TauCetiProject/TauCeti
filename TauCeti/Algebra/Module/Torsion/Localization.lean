/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Torsion modules are those killed by localization

A module `M` over a commutative semiring `R` is `S`-torsion, for a submonoid `S` of `R`, exactly
when its base change `A ⊗[R] M` to a localization `A` of `R` at `S` vanishes: the base change is
a localization of `M` at `S`, and an element of `M` dies there exactly when some element of `S`
kills it. Taking `S` to be the nonzerodivisors, a module is torsion exactly when its base change to
the total ring of fractions vanishes. For abelian groups this is the classical characterization of
torsion groups as the groups `G` with `ℚ ⊗ G = 0`.

## Main results

* `Module.isTorsion'_iff_subsingleton_tensorProduct`: `M` is `S`-torsion if and only if
  `A ⊗[R] M` is trivial, for a localization `A` of `R` at `S`.
* `Module.isTorsion_iff_subsingleton_tensorProduct`: `M` is torsion if and only if `K ⊗[R] M` is
  trivial, for the total ring of fractions `K` of `R`.
* `isAddTorsion_iff_subsingleton_rat_tensorProduct`: an abelian group `G` is torsion if and only
  if `ℚ ⊗[ℤ] G` is trivial.
-/

public section

open TensorProduct

namespace Module

variable {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]
  [IsLocalization S A] {M : Type*} [AddCommMonoid M] [Module R M]

/-- A module is `S`-torsion if and only if its base change to a localization at `S` is
trivial. -/
theorem isTorsion'_iff_subsingleton_tensorProduct :
    IsTorsion' M S ↔ Subsingleton (A ⊗[R] M) := by
  have : IsLocalizedModule S (TensorProduct.mk R A M 1) :=
    (isLocalizedModule_iff_isBaseChange S A _).2 (TensorProduct.isBaseChange R M A)
  rw [IsLocalizedModule.subsingleton_iff S (TensorProduct.mk R A M 1)]
  simp [IsTorsion', Submonoid.smul_def]

/-- A module is torsion if and only if its base change to the total ring of fractions is
trivial. -/
theorem isTorsion_iff_subsingleton_tensorProduct {R : Type*} [CommRing R] (K : Type*) [CommRing K]
    [Algebra R K] [IsFractionRing R K] {M : Type*} [AddCommMonoid M] [Module R M] :
    IsTorsion R M ↔ Subsingleton (K ⊗[R] M) :=
  isTorsion'_iff_subsingleton_tensorProduct (nonZeroDivisors R) K

end Module

/-- An abelian group `G` is torsion if and only if its rationalization `ℚ ⊗[ℤ] G` is trivial. -/
theorem isAddTorsion_iff_subsingleton_rat_tensorProduct {G : Type*} [AddCommGroup G] :
    IsAddTorsion G ↔ Subsingleton (ℚ ⊗[ℤ] G) :=
  isAddTorsion_iff_isTorsion_int.trans (Module.isTorsion_iff_subsingleton_tensorProduct ℚ)
