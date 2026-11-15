/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Basic

import Mathlib.RingTheory.Artinian.Module

/-!
# Common kernels of functionals with values in a subring

Let `V` be a finite-dimensional vector space over a field `K`, let `R ⊆ K` be a subring, and let
`L ⊆ V` be an additive subgroup that is stable under multiplication by `R` and spans `V` over
`K`. If a family of linear functionals `φ i : V → K` takes values in `R` on `L`, then the common
kernel of the family is spanned over `K` by its intersection with `L`
(`TauCeti.iInf_ker_eq_span_inter`).

Linear conditions with coefficients in `R` on an `R`-structure therefore cut out subspaces
that again have an `R`-structure. For modular forms with integral `q`-expansions, this is how
a space of forms defined by the vanishing of finitely many `q`-coefficients inherits a spanning
set of integral forms from the ambient space.

The proof eliminates one functional at a time (`TauCeti.le_span_inter_inf_ker`): if `φ l₀ ≠ 0`
for some `l₀ ∈ L` in the current subspace, then `v ↦ φ l₀ • v - φ v • l₀` maps that subspace
into its intersection with `ker φ`, keeps `L` inside `L`, and is multiplication by `φ l₀` on
`ker φ`. Finite-dimensionality reduces an arbitrary family to a finite one.
-/

public section

open Submodule

namespace TauCeti

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {R : Subring K}
  {L : Submodule ℤ V}

/-- One elimination step: intersecting with the kernel of a functional that is `R`-valued on
`L` preserves the property of being spanned by elements of `L`. -/
theorem le_span_inter_inf_ker (hL : ∀ r ∈ R, ∀ v ∈ L, r • v ∈ L) {W : Submodule K V}
    (hW : W ≤ span K ((L : Set V) ∩ W)) {φ : V →ₗ[K] K} (hφ : ∀ v ∈ L, φ v ∈ R) :
    W ⊓ LinearMap.ker φ ≤ span K ((L : Set V) ∩ ↑(W ⊓ LinearMap.ker φ)) := by
  by_cases h₀ : ∃ l₀ ∈ L, l₀ ∈ W ∧ φ l₀ ≠ 0
  swap
  · refine inf_le_left.trans (hW.trans (span_mono fun v hv ↦ ⟨hv.1, hv.2, ?_⟩))
    by_contra h
    exact h₀ ⟨v, hv.1, hv.2, h⟩
  obtain ⟨l₀, hl₀L, hl₀W, hl₀⟩ := h₀
  -- `π v = φ l₀ • v - φ v • l₀` maps `L ∩ W` into `L ∩ W ∩ ker φ`.
  let π : V →ₗ[K] V := φ l₀ • LinearMap.id - φ.smulRight l₀
  have hπ : span K ((L : Set V) ∩ W) ≤
      (span K ((L : Set V) ∩ ↑(W ⊓ LinearMap.ker φ))).comap π := by
    refine span_le.mpr fun v hv ↦ subset_span ⟨?_, ?_, ?_⟩
    · exact L.sub_mem (hL _ (hφ _ hl₀L) _ hv.1) (hL _ (hφ _ hv.1) _ hl₀L)
    · exact W.sub_mem (W.smul_mem _ hv.2) (W.smul_mem _ hl₀W)
    · simp [π, mul_comm]
  intro v hv
  have hπv : π v = φ l₀ • v := by
    simp [π, LinearMap.mem_ker.mp hv.2]
  have := hπ (hW hv.1)
  rw [mem_comap, hπv] at this
  simpa [hl₀] using smul_mem _ (φ l₀)⁻¹ this

variable [FiniteDimensional K V]

/-- **Common kernels of `R`-valued functionals are spanned by their `R`-points.** Let `L` be an
additive subgroup of a finite-dimensional `K`-vector space `V` that is stable under a subring
`R ⊆ K` and spans `V`. If every functional `φ i` takes values in `R` on `L`, then the common
kernel of the `φ i` is spanned over `K` by its intersection with `L`. -/
theorem iInf_ker_eq_span_inter (hL : ∀ r ∈ R, ∀ v ∈ L, r • v ∈ L)
    (hspan : span K (L : Set V) = ⊤) {ι : Type*} (φ : ι → V →ₗ[K] K)
    (hφ : ∀ i, ∀ v ∈ L, φ i v ∈ R) :
    ⨅ i, LinearMap.ker (φ i) = span K ((L : Set V) ∩ ↑(⨅ i, LinearMap.ker (φ i))) := by
  classical
  refine le_antisymm ?_ (span_le.mpr Set.inter_subset_right)
  -- A finite subfamily already cuts out the common kernel.
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ := IsArtinian.set_has_minimal
    (Set.range fun s : Finset ι ↦ ⨅ i ∈ s, LinearMap.ker (φ i)) ⟨_, ⟨∅, rfl⟩⟩
  have hseq : ⨅ i ∈ s, LinearMap.ker (φ i) = ⨅ i, LinearMap.ker (φ i) := by
    refine le_antisymm (le_iInf fun j ↦ ?_) (le_iInf₂ fun i _ ↦ iInf_le _ i)
    by_contra hj
    refine hs _ ⟨insert j s, rfl⟩ (lt_of_le_of_ne (le_iInf₂ fun i hi ↦ ?_) fun h ↦ hj ?_)
    · exact iInf₂_le i (Finset.mem_insert_of_mem hi)
    · have h' : ⨅ i ∈ insert j s, LinearMap.ker (φ i) = ⨅ i ∈ s, LinearMap.ker (φ i) := h
      exact h' ▸ iInf₂_le j (Finset.mem_insert_self j s)
  have key (t : Finset ι) : ⨅ i ∈ t, LinearMap.ker (φ i) ≤
      span K ((L : Set V) ∩ ↑(⨅ i ∈ t, LinearMap.ker (φ i))) := by
    induction t using Finset.induction_on with
    | empty => simp [hspan]
    | insert j t _ ih =>
      rw [Finset.iInf_insert, inf_comm]
      exact le_span_inter_inf_ker hL ih (hφ j)
  rw [← hseq]
  exact key s

end TauCeti
