/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Trace.Exact

/-!
# Inclusion-exclusion for traces on invariant subspaces

When two invariant subspaces span a finite-dimensional vector space, the sum of the traces
on them is the ambient trace plus the trace on their intersection. This is trace additivity
for the exact sequence from the intersection to the product and then to the ambient space.
-/

public section

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Inclusion-exclusion for traces.** If two invariant subspaces span the whole space,
the sum of their traces equals the ambient trace plus the trace on their intersection. -/
theorem trace_restrict_add_trace_restrict_eq_trace_add_trace_restrict_inf
    {A B : Submodule K V} (hAB : Codisjoint A B) (f : V →ₗ[K] V)
    (hA : ∀ x ∈ A, f x ∈ A) (hB : ∀ x ∈ B, f x ∈ B) :
    trace K A (f.restrict hA) + trace K B (f.restrict hB) =
      trace K V f + trace K (A ⊓ B : Submodule K V)
        (f.restrict fun x hx ↦ ⟨hA x hx.1, hB x hx.2⟩) := by
  let i : (A ⊓ B : Submodule K V) →ₗ[K] A × B :=
    (Submodule.inclusion inf_le_left).prod (-Submodule.inclusion inf_le_right)
  let π : A × B →ₗ[K] V := A.subtype.coprod B.subtype
  have hi : Function.Injective i := fun x y h ↦
    Subtype.ext (congrArg (fun z : A × B ↦ (z.1 : V)) h)
  have hπ : Function.Surjective π := by
    intro x
    have hx : x ∈ A ⊔ B := by rw [codisjoint_iff.mp hAB]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  have hex : Function.Exact i π := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x.1, x.1.2, ?_⟩, ?_⟩
      · have h : (x.1 : V) = -(x.2 : V) := eq_neg_of_add_eq_zero_left hx
        rw [h]
        exact B.neg_mem x.2.2
      · apply Prod.ext
        · rfl
        · exact Subtype.ext (neg_eq_of_add_eq_zero_right hx)
    · rintro ⟨x, rfl⟩
      simp [π, i]
  have h := trace_eq_add_of_exact hi hπ hex
    (f := prodMap (f.restrict hA) (f.restrict hB))
    (fN := f.restrict fun x hx ↦ ⟨hA x hx.1, hB x hx.2⟩) (fQ := f)
    (by ext x <;> simp [i, LinearMap.restrict])
    (by ext x <;> simp [π, LinearMap.restrict])
  rw [trace_prodMap'] at h
  exact h.trans (add_comm _ _)

end LinearMap
