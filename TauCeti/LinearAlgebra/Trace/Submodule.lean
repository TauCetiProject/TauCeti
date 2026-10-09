/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.Exact

/-!
# Inclusion–exclusion for traces on invariant subspaces

For two invariant subspaces, the sum of their traces equals the sum of the traces on their
intersection and sum. This is the trace counterpart of the dimension formula for two subspaces,
and allows character computations on spaces cut out by several linear relations.
-/

public section

namespace TauCeti

open LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Inclusion–exclusion for traces.** If `f` preserves `A` and `B`, its traces on these
subspaces sum to its traces on `A ⊓ B` and `A ⊔ B`. -/
theorem trace_restrict_inf_add_trace_restrict_sup {A B : Submodule K V} (f : V →ₗ[K] V)
    (hA : ∀ x ∈ A, f x ∈ A) (hB : ∀ x ∈ B, f x ∈ B) :
    trace K (A ⊓ B : Submodule K V) (f.restrict fun x hx ↦ ⟨hA x hx.1, hB x hx.2⟩) +
      trace K (A ⊔ B : Submodule K V)
        (f.restrict fun _ hx ↦ (sup_le (fun _ hx ↦ Submodule.mem_sup_left (hA _ hx))
          (fun _ hx ↦ Submodule.mem_sup_right (hB _ hx)) :
            A ⊔ B ≤ (A ⊔ B).comap f) hx) =
      trace K A (f.restrict hA) + trace K B (f.restrict hB) := by
  let i : (A ⊓ B : Submodule K V) →ₗ[K] A × B :=
    (Submodule.inclusion inf_le_left).prod (-Submodule.inclusion inf_le_right)
  let π : (A × B) →ₗ[K] (A ⊔ B : Submodule K V) :=
    (A.subtype.coprod B.subtype).codRestrict _ fun x ↦
      Submodule.add_mem_sup x.1.2 x.2.2
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : A × B ↦ (z.1 : V)) h)
  have hπ : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  have hex : Function.Exact i π := by
    intro x
    constructor
    · intro hx
      have hab : (x.1 : V) + x.2 = 0 := congrArg Subtype.val hx
      refine ⟨⟨x.1, x.1.2, ?_⟩, ?_⟩
      · rw [eq_neg_of_add_eq_zero_left hab]
        exact B.neg_mem x.2.2
      · apply Prod.ext <;> apply Subtype.ext
        · rfl
        · exact neg_eq_iff_add_eq_zero.mpr hab
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      exact add_neg_cancel _
  have h := trace_eq_add_of_exact hi hπ hex
    (f := (f.restrict hA).prodMap (f.restrict hB))
    (fN := f.restrict fun x hx ↦ ⟨hA x hx.1, hB x hx.2⟩)
    (fQ := f.restrict fun _ hx ↦ (sup_le (fun _ hx ↦ Submodule.mem_sup_left (hA _ hx))
      (fun _ hx ↦ Submodule.mem_sup_right (hB _ hx)) :
        A ⊔ B ≤ (A ⊔ B).comap f) hx)
    (by ext x <;> simp [i, restrict])
    (by ext x <;> simp [π, codRestrict, restrict])
  rw [trace_prodMap'] at h
  exact h.symm

end TauCeti
