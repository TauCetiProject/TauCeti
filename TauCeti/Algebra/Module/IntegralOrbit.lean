/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower

/-!
# Integral orbits through algebra representations

For a subring `S` of an `R`-algebra `A`, a representation `ρ : A →ₐ[R] Module.End R V`,
and a set of vectors `X`, `Subring.orbitOfRep S ρ X` is the `ℤ`-span of all `ρ a x`
with `a ∈ S` and `x ∈ X`. It contains `X` and is stable under the represented action of `S`.
This construction lets an integral form act without installing a global `A`-module instance.

If `X` spans `V` over `R`, its integral orbit also spans `V`. When `R` is a commutative ring
and `S` spans `A` over `R`, the `R`-span of the integral orbit agrees with the span of all
translates through `A`. The construction itself only needs a commutative scalar semiring `R`;
the vectors form an additive commutative group so that integral spans are defined.
No finite-generation property is asserted.
-/

public section

universe u v

namespace Subring

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {A : Type u} [Ring A] [Algebra R A]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable (S : Subring A) (ρ : A →ₐ[R] Module.End R V) (X : Set V)

/-- The integral orbit of a set through an algebra representation: the `ℤ`-span of all `ρ a x`
with `a ∈ S` and `x ∈ X`. -/
def orbitOfRep : Submodule ℤ V :=
  Submodule.span ℤ {v | ∃ a ∈ S, ∃ x ∈ X, ρ a x = v}

/-- The represented orbit is the integral span of the images of its generators. -/
theorem orbitOfRep_def :
    orbitOfRep S ρ X = Submodule.span ℤ {v | ∃ a ∈ S, ∃ x ∈ X, ρ a x = v} := (rfl)

/-- A represented translate of a generator belongs to its integral orbit. -/
theorem apply_mem_orbitOfRep {a : A} (ha : a ∈ S) {x : V} (hx : x ∈ X) :
    ρ a x ∈ orbitOfRep S ρ X :=
  Submodule.subset_span ⟨a, ha, x, hx, rfl⟩

/-- The generators themselves belong to their integral orbit. -/
theorem subset_orbitOfRep : X ⊆ (orbitOfRep S ρ X : Set V) := by
  intro x hx
  simpa only [SetLike.mem_coe, map_one, Module.End.one_apply] using
    apply_mem_orbitOfRep S ρ X S.one_mem hx

/-- The elimination principle for a represented integral orbit. -/
theorem orbitOfRep_le_iff (N : Submodule ℤ V) :
    orbitOfRep S ρ X ≤ N ↔ ∀ a ∈ S, ∀ x ∈ X, ρ a x ∈ N := by
  rw [orbitOfRep, Submodule.span_le]
  constructor
  · intro hle a ha x hx
    exact hle ⟨a, ha, x, hx, rfl⟩
  · rintro hle - ⟨a, ha, x, hx, rfl⟩
    exact hle a ha x hx

/-- The represented integral orbit is stable under the subring. -/
theorem apply_mem_orbitOfRep_of_mem {a : A} (ha : a ∈ S) {v : V}
    (hv : v ∈ orbitOfRep S ρ X) : ρ a v ∈ orbitOfRep S ρ X := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hw
      simpa only [map_mul, Module.End.mul_apply] using
        apply_mem_orbitOfRep S ρ X (S.mul_mem ha hb) hx
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_zsmul]; exact Submodule.smul_mem _ c ha

/-- If the supplied vectors span over `R`, their represented integral orbit is full. -/
theorem span_orbitOfRep_eq_top (hX : Submodule.span R X = ⊤) :
    Submodule.span R (orbitOfRep S ρ X : Set V) = ⊤ := by
  apply top_unique
  rw [← hX]
  exact Submodule.span_mono (subset_orbitOfRep S ρ X)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]
variable {A : Type u} [Ring A] [Algebra R A]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable (S : Subring A) (ρ : A →ₐ[R] Module.End R V) (X : Set V)

/-- If `S` spans `A` over `R`, the `R`-span of the represented integral orbit is the span of
all translates through the full algebra. -/
theorem span_orbitOfRep_eq_span (hS : Submodule.span R (S : Set A) = ⊤) :
    Submodule.span R (orbitOfRep S ρ X : Set V) =
      Submodule.span R {v | ∃ a : A, ∃ x ∈ X, ρ a x = v} := by
  rw [orbitOfRep_def, Submodule.span_span_of_tower]
  apply le_antisymm
  · exact Submodule.span_mono fun _ ⟨a, _, x, hx, h⟩ => ⟨a, x, hx, h⟩
  · rw [Submodule.span_le]
    rintro - ⟨a, x, hx, rfl⟩
    have ha : a ∈ Submodule.span R (S : Set A) := hS ▸ Submodule.mem_top
    have himage := Submodule.apply_mem_span_image_of_mem_span
      ((LinearMap.applyₗ (R := R) x).comp ρ.toLinearMap) ha
    apply Submodule.span_mono _ himage
    rintro - ⟨b, hb, rfl⟩
    exact ⟨b, hb, x, hx, rfl⟩

end CommRing

end Subring
