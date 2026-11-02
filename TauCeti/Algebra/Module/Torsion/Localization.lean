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

Localizing a torsion module at any submonoid gives a torsion module over the localized ring, since
non-zero-divisors stay non-zero-divisors after localization.

## Main results

* `Submonoid.isTorsion'_iff_subsingleton_tensorProduct`: `M` is `S`-torsion if and only if
  `A ⊗[R] M` is trivial, for a localization `A` of `R` at `S`.
* `TauCeti.Module.isTorsion_iff_subsingleton_tensorProduct`: `M` is torsion if and only if
  `K ⊗[R] M` is trivial, for the total ring of fractions `K` of `R`.
* `TauCeti.isAddTorsion_iff_subsingleton_rat_tensorProduct`: an abelian group `G` is torsion if
  and only if `ℚ ⊗[ℤ] G` is trivial.
* `Module.IsTorsion.localizedModule`: the localization of a torsion module is torsion.
-/

public section

open TensorProduct

namespace Submonoid

variable {R : Type*} [CommSemiring R] (S : Submonoid R) (A : Type*) [CommSemiring A] [Algebra R A]
  [IsLocalization S A] {M : Type*} [AddCommMonoid M] [Module R M]

/-- A module is `S`-torsion if and only if its base change to a localization at `S` is
trivial. -/
theorem isTorsion'_iff_subsingleton_tensorProduct :
    Module.IsTorsion' M S ↔ Subsingleton (A ⊗[R] M) := by
  rw [IsLocalizedModule.subsingleton_iff S (TensorProduct.mk R A M 1)]
  simp [Module.IsTorsion', Submonoid.smul_def]

end Submonoid

namespace TauCeti

/-- A module is torsion if and only if its base change to the total ring of fractions is
trivial. -/
theorem Module.isTorsion_iff_subsingleton_tensorProduct {R : Type*} [CommSemiring R] (K : Type*)
    [CommSemiring K] [Algebra R K] [IsFractionRing R K] {M : Type*} [AddCommMonoid M]
    [Module R M] :
    Module.IsTorsion R M ↔ Subsingleton (K ⊗[R] M) :=
  (nonZeroDivisors R).isTorsion'_iff_subsingleton_tensorProduct K

/-- An abelian group `G` is torsion if and only if its rationalization `ℚ ⊗[ℤ] G` is trivial. -/
theorem isAddTorsion_iff_subsingleton_rat_tensorProduct {G : Type*} [AddCommGroup G] :
    IsAddTorsion G ↔ Subsingleton (ℚ ⊗[ℤ] G) :=
  isAddTorsion_iff_isTorsion_int.trans (Module.isTorsion_iff_subsingleton_tensorProduct ℚ)

end TauCeti

namespace Module.IsTorsion

/-- The localization of a torsion module at a submonoid `S` is torsion over `Localization S`. -/
theorem localizedModule {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]
    (hM : Module.IsTorsion R M) (S : Submonoid R) :
    Module.IsTorsion (Localization S) (LocalizedModule S M) := by
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s =>
    obtain ⟨⟨a, ha⟩, ham⟩ := @hM m
    rw [Submonoid.smul_def] at ham
    refine ⟨⟨algebraMap R _ a,
      IsLocalization.map_nonZeroDivisors_le S _ (Submonoid.mem_map_of_mem _ ha)⟩, ?_⟩
    rw [Submonoid.mk_smul, algebraMap_smul, LocalizedModule.smul'_mk, ham, LocalizedModule.zero_mk]

end Module.IsTorsion
