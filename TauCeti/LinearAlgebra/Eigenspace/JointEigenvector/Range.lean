/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.Finiteness.Defs

import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Exists

/-!
# Joint eigenvectors in the range of a commuting endomorphism

Let `A : ι → Module.End K V` be a pairwise-commuting family of endomorphisms of a vector space `V`
over a field `K`, and let `f : Module.End K V` be a nonzero endomorphism commuting with every
`A i`. Then `LinearMap.range f` is a nontrivial `A`-invariant subspace. When each `A i` is
triangularizable (in finite dimension) or when `K` is algebraically closed and `LinearMap.range f`
is finite-dimensional, the family `A` admits a common eigenvector `f v ≠ 0` in the range of `f`.

## Main results

* `TauCeti.exists_jointEigenvector_mem_range_of_pairwise_commute`: common eigenvector in
  `LinearMap.range f` for a pairwise-commuting triangularizable family commuting with `f ≠ 0`.
* `TauCeti.exists_jointEigenvector_mem_range_of_pairwise_commute_of_isAlgClosed`: algebraically
  closed form, requiring only `[FiniteDimensional K (LinearMap.range f)]`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/General/LinearAlgebra/Eigenvalues.lean` (`New.exists_eigenvector_mem_range_of_commute`).
-/

@[expose] public section

open Module

namespace TauCeti

private theorem exists_jointEigenvector_mem_range_aux {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] {A : ι → End K V} (hA : Pairwise fun i j ↦ Commute (A i) (A j)) {f : End K V}
    [FiniteDimensional K (LinearMap.range f)]
    (h_stable : ∀ i, ∀ u ∈ LinearMap.range f, A i u ∈ LinearMap.range f) (hf_ne : f ≠ 0)
    (htri : ∀ i, ⨆ μ : K, End.maxGenEigenspace ((A i).restrict (h_stable i)) μ = ⊤) :
    ∃ (χ : ι → K) (v : V), f v ≠ 0 ∧ ∀ i, A i (f v) = χ i • f v := by
  have : Nontrivial (LinearMap.range f) :=
    Submodule.nontrivial_iff_ne_bot.mpr (mt LinearMap.range_eq_bot.mp hf_ne)
  have h_comm : Pairwise fun i j ↦ Commute ((A i).restrict (h_stable i))
      ((A j).restrict (h_stable j)) := fun i j hij ↦ by
    ext ⟨u, hu⟩
    simpa using LinearMap.congr_fun (hA hij).eq u
  obtain ⟨χ, ⟨_, ⟨v, rfl⟩⟩, hv, hχ⟩ := exists_jointEigenvector_of_pairwise_commute
    (fun i ↦ (A i).restrict (h_stable i)) h_comm htri
  refine ⟨χ, v, Subtype.coe_ne_coe.mpr hv, fun i ↦ ?_⟩
  exact congrArg Subtype.val (End.mem_eigenspace_iff.mp (hχ i))

/-- A pairwise-commuting family `A : ι → Module.End K V` of triangularizable endomorphisms on a
finite-dimensional vector space `V` has a common eigenvector in the range of any nonzero
endomorphism `f : Module.End K V` commuting with every `A i`. -/
theorem exists_jointEigenvector_mem_range_of_pairwise_commute {K V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {A : ι → End K V}
    (hA : Pairwise fun i j ↦ Commute (A i) (A j))
    (htri : ∀ i, ⨆ μ : K, (A i).maxGenEigenspace μ = ⊤)
    {f : End K V} (hf : ∀ i, Commute f (A i)) (hf_ne : f ≠ 0) :
    ∃ (χ : ι → K) (v : V), f v ≠ 0 ∧ ∀ i, A i (f v) = χ i • f v := by
  have h_stable (i : ι) : ∀ u ∈ LinearMap.range f, A i u ∈ LinearMap.range f :=
    Set.forall_mem_range.mpr fun v ↦ ⟨A i v, LinearMap.congr_fun (hf i).eq v⟩
  exact exists_jointEigenvector_mem_range_aux hA h_stable hf_ne fun i ↦
    End.genEigenspace_restrict_eq_top (h_stable i) (htri i)

/-- Over an algebraically closed field `K`, a pairwise-commuting family `A : ι → Module.End K V`
has a common eigenvector in the range of any nonzero finite-rank endomorphism `f : Module.End K V`
commuting with every `A i`. -/
theorem exists_jointEigenvector_mem_range_of_pairwise_commute_of_isAlgClosed {K V ι : Type*}
    [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V] {A : ι → End K V}
    (hA : Pairwise fun i j ↦ Commute (A i) (A j)) {f : End K V}
    [FiniteDimensional K (LinearMap.range f)] (hf : ∀ i, Commute f (A i)) (hf_ne : f ≠ 0) :
    ∃ (χ : ι → K) (v : V), f v ≠ 0 ∧ ∀ i, A i (f v) = χ i • f v := by
  have h_stable (i : ι) : ∀ u ∈ LinearMap.range f, A i u ∈ LinearMap.range f :=
    Set.forall_mem_range.mpr fun v ↦ ⟨A i v, LinearMap.congr_fun (hf i).eq v⟩
  exact exists_jointEigenvector_mem_range_aux hA h_stable hf_ne fun _ ↦
    End.iSup_maxGenEigenspace_eq_top _

end TauCeti
