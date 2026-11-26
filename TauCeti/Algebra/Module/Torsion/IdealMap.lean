/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Linear maps on ideal torsion

An `A`-linear map induces an `A ⧸ I`-linear map on the submodules killed by `I`. In particular,
taking the socle at a maximal ideal produces maps over the residue field.
-/

public section

open Submodule

namespace LinearMap

variable {A M N P : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

/-- A linear map preserves the submodule annihilated by a set of scalars. -/
theorem mapsTo_torsionBySet {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (s : Set R) :
    Set.MapsTo f (torsionBySet R M s) (torsionBySet R N s) :=
  fun {_} hx ↦ (mem_torsionBySet_iff _ _).mpr fun a ↦ by
    rw [← map_smul, (mem_torsionBySet_iff _ _).mp hx a, map_zero]

/-- The restriction of a linear map to the submodules annihilated by an ideal, with scalars
in the quotient ring. -/
def torsionByIdeal (f : M →ₗ[A] N) (I : Ideal A) :
    torsionBySet A M I →ₗ[A ⧸ I] torsionBySet A N I :=
  extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    f.restrict fun _ hx ↦ f.mapsTo_torsionBySet I hx

@[simp]
theorem coe_torsionByIdeal_apply (f : M →ₗ[A] N) (I : Ideal A) (x : torsionBySet A M I) :
    (f.torsionByIdeal I x : N) = f x := (rfl)

@[simp]
theorem torsionByIdeal_id (I : Ideal A) :
    (LinearMap.id (R := A) (M := M)).torsionByIdeal I = LinearMap.id :=
  LinearMap.ext fun _ ↦ rfl

@[simp]
theorem torsionByIdeal_comp (g : N →ₗ[A] P) (f : M →ₗ[A] N) (I : Ideal A) :
    (g ∘ₗ f).torsionByIdeal I = g.torsionByIdeal I ∘ₗ f.torsionByIdeal I :=
  LinearMap.ext fun _ ↦ rfl

/-- Injectivity on ideal torsion tests whether the kernel contains any nonzero element killed
by the ideal. -/
theorem injective_torsionByIdeal_iff (f : M →ₗ[A] N) (I : Ideal A) :
    Function.Injective (f.torsionByIdeal I) ↔ Disjoint (torsionBySet A M I) f.ker :=
  injective_restrict_iff (f := f) (p := torsionBySet A M I) (q := torsionBySet A N I)
    (fun _ hx ↦ f.mapsTo_torsionBySet I hx)

end LinearMap
