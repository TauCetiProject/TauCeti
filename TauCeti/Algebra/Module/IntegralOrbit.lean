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

If `X` spans `V` over `R`, its integral orbit also spans `V`. When `S` spans `A` over `R`, the
`R`-span of the integral orbit agrees with the span of all translates through `A`. Everything
only needs a commutative scalar semiring `R`; the vectors form an additive commutative group so
that integral spans are defined. No finite-generation property is asserted.
-/

public section

universe u v

namespace Subring

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
  simpa only [SetLike.mem_coe, map_one, one_apply_eq_self] using
    apply_mem_orbitOfRep S ρ X S.one_mem hx

/-- The elimination principle for a represented integral orbit. -/
theorem orbitOfRep_le_iff (N : Submodule ℤ V) :
    orbitOfRep S ρ X ≤ N ↔ ∀ a ∈ S, ∀ x ∈ X, ρ a x ∈ N := by
  rw [orbitOfRep_def, Submodule.span_le]
  exact ⟨fun h a ha x hx => h ⟨a, ha, x, hx, rfl⟩, fun h _ ⟨a, ha, x, hx, hv⟩ => hv ▸ h a ha x hx⟩

/-- The represented integral orbit is stable under the subring. -/
theorem apply_mem_orbitOfRep_of_mem {a : A} (ha : a ∈ S) {v : V}
    (hv : v ∈ orbitOfRep S ρ X) : ρ a v ∈ orbitOfRep S ρ X := by
  have hle := (orbitOfRep_le_iff S ρ X
    ((orbitOfRep S ρ X).comap (ρ a).toAddMonoidHom.toIntLinearMap)).2 fun b hb x hx => by
      simpa only [Submodule.mem_comap, AddMonoidHom.coe_toIntLinearMap,
        LinearMap.toAddMonoidHom_coe, map_mul, mul_apply_eq_comp] using
        apply_mem_orbitOfRep S ρ X (S.mul_mem ha hb) hx
  simpa only [Submodule.mem_comap, AddMonoidHom.coe_toIntLinearMap,
    LinearMap.toAddMonoidHom_coe] using hle hv

/-- If the supplied vectors span over `R`, their represented integral orbit is full. -/
theorem span_orbitOfRep_eq_top (hX : Submodule.span R X = ⊤) :
    Submodule.span R (orbitOfRep S ρ X : Set V) = ⊤ :=
  eq_top_mono (Submodule.span_mono (subset_orbitOfRep S ρ X)) hX

/-- If `S` spans `A` over `R`, the `R`-span of the represented integral orbit is the span of
all translates through the full algebra. -/
theorem span_orbitOfRep_eq_span (hS : Submodule.span R (S : Set A) = ⊤) :
    Submodule.span R (orbitOfRep S ρ X : Set V) =
      Submodule.span R {v | ∃ a : A, ∃ x ∈ X, ρ a x = v} := by
  apply le_antisymm
  · refine Submodule.span_le.2 fun v hv => ?_
    rw [SetLike.mem_coe, orbitOfRep_def, ← Submodule.mem_toAddSubgroup,
      Submodule.span_int_eq_addSubgroupClosure] at hv
    -- An `R`-span need not be closed under negation when `R` is only a semiring, so the
    -- induction treats the negations of the generators as separate cases.
    induction hv using AddSubgroup.closure_induction'' with
    | mem _ h =>
        obtain ⟨a, -, x, hx, rfl⟩ := h
        exact Submodule.subset_span ⟨a, x, hx, rfl⟩
    | neg_mem _ h =>
        obtain ⟨a, -, x, hx, rfl⟩ := h
        exact Submodule.subset_span ⟨-a, x, hx, by simp only [map_neg, LinearMap.neg_apply]⟩
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
  · rw [Submodule.span_le]
    rintro - ⟨a, x, hx, rfl⟩
    have ha : a ∈ Submodule.span R (S : Set A) := hS ▸ Submodule.mem_top
    refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span
      ((LinearMap.applyₗ (R := R) x).comp ρ.toLinearMap) ha)
    rintro - ⟨b, hb, rfl⟩
    exact apply_mem_orbitOfRep S ρ X hb hx

end Subring
