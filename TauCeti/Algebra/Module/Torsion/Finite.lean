/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Module.Torsion.ScalarAction

/-!
# Finiteness for modules killed by a scalar or ideal

If an `S`-module is killed by `f`, its scalar action factors through `S ⧸ (f)`. Thus a finite
`S`-module killed by `f` is finite over a coefficient semiring `A` whenever `S ⧸ (f)` is finite
over `A`. This transfers quotient-finiteness results to modules annihilated by distinguished
power series.

Similarly, if `π : A →+* k` is a surjective ring homomorphism and `M` is an `A`-module annihilated
by `RingHom.ker π`, then `M` is finite over `k` (via `Module.IsTorsionBySet.moduleOfSurjective`)
if and only if it is finite over `A` (`Module.IsTorsionBySet.finite_iff_of_surjective`).
-/

public section

namespace Module.IsTorsionBy

/-- A finite `S`-module killed by `f` is finite over `A` if `S ⧸ (f)` is finite over `A`. -/
theorem finite_of_finite_quotient {A S M : Type*} [CommSemiring A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M] [Module.Finite S M]
    {f : S} (h : Module.IsTorsionBy S M f) [Module.Finite A (S ⧸ Ideal.span {f})] :
    Module.Finite A M := by
  have hM : Module.IsTorsionBySet S M (Ideal.span {f}) :=
    (Module.isTorsionBySet_span_singleton_iff f).mpr h
  let := hM.module
  have : IsScalarTower A (S ⧸ Ideal.span {f}) M := hM.isScalarTower
  have : Module.Finite (S ⧸ Ideal.span {f}) M := Module.Finite.of_restrictScalars_finite S _ M
  exact Module.Finite.trans (S ⧸ Ideal.span {f}) M

end Module.IsTorsionBy

namespace Module.IsTorsionBySet

/-- An `A`-module annihilated by `RingHom.ker π` for a surjective ring homomorphism `π : A →+* k`
is finite over `k` if and only if it is finite over `A`. -/
theorem finite_iff_of_surjective {A k M : Type*} [Ring A] [Ring k] [AddCommGroup M]
    [Module A M] {π : A →+* k} (hM : Module.IsTorsionBySet A M (RingHom.ker π))
    (hπ : Function.Surjective π) :
    letI := hM.moduleOfSurjective hπ
    Module.Finite A M ↔ Module.Finite k M :=
  letI := hM.moduleOfSurjective hπ
  have : RingHomSurjective π := ⟨hπ⟩
  (hM.semilinearMapOfSurjective hπ).finite_iff_of_bijective Function.bijective_id

/-- An `A`-module annihilated by `RingHom.ker π` for a surjective ring homomorphism `π : A →+* k`
is finite over `k` whenever it is finite over `A`. -/
theorem finite_of_surjective {A k M : Type*} [Ring A] [Ring k] [AddCommGroup M]
    [Module A M] {π : A →+* k} (hM : Module.IsTorsionBySet A M (RingHom.ker π))
    (hπ : Function.Surjective π) [Module.Finite A M] :
    letI := hM.moduleOfSurjective hπ
    Module.Finite k M :=
  letI := hM.moduleOfSurjective hπ
  Module.Finite.of_surjective (hM.semilinearMapOfSurjective hπ) Function.surjective_id

end Module.IsTorsionBySet
