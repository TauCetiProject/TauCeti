/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.RepresentationTheory.FinitelyGenerated

/-!
# Finitely generated smooth representations

A representation `ρ` of a group `G` on an `A`-module `V` is *finitely generated* when `V` is a
finitely generated module over the group algebra `A[G]`, that is
`Module.Finite A[G] ρ.asModule`. This file proves that a smooth representation of a topological
group is finitely generated exactly when it is a quotient of a finite direct sum
`⊕_{i < n} A[G ⧸ U_i]` of permutation representations on the cosets of open subgroups `U_i`, and,
for a locally profinite group, of compact open subgroups `U_i`.

Both directions are algebraic (`TauCeti.RepresentationTheory.FinitelyGenerated`): generators
`v_i` give a surjection from `⊕_{i < n} A[G ⧸ U_i]` for any subgroups `U_i` fixing `v_i`
(`Representation.exists_surjective_of_finite_asModule`), which for a smooth representation may
be taken open, or compact open; conversely each `A[G ⧸ U]` is finitely generated, and finite
generation passes to finite direct sums and quotients.

## Main results

* `Representation.finite_asModule_iff_exists_surjective`: a smooth representation is finitely
  generated exactly when it is a quotient of `⊕_{i < n} A[G ⧸ U_i]` with `U_i` open.
* `Representation.finite_asModule_iff_exists_surjective_isCompact`: for a locally profinite
  group, the `U_i` may be taken compact open.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.2, Theorem 3 and its proof, p. 13 (over `ℂ`, every smooth
  representation is a quotient of a direct sum of the modules `H(G) e_K ≅ ℂ[G ⧸ K]`).
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {A G V : Type*} [CommSemiring A] [Group G] [AddCommMonoid V] [Module A V]
  {ρ : Representation A G V}

variable [TopologicalSpace G]

/-- **Finitely generated smooth representations are quotients of permutation representations.**
A smooth representation is finitely generated over `A[G]` exactly when it is a quotient of a
finite direct sum `⊕_{i < n} A[G ⧸ U_i]` for open subgroups `U_i`. -/
theorem finite_asModule_iff_exists_surjective [IsSmooth ρ] :
    Module.Finite A[G] ρ.asModule ↔
      ∃ (n : ℕ) (U : Fin n → OpenSubgroup G)
        (f : IntertwiningMap (directSum fun i ↦ ofMulAction A G (G ⧸ (U i : Subgroup G))) ρ),
        Function.Surjective f := by
  refine ⟨fun _ ↦ ?_, fun ⟨n, U, f, hf⟩ ↦ finite_asModule_of_surjective f hf⟩
  obtain ⟨n, U, hU, hf⟩ := exists_surjective_of_finite_asModule (ρ := ρ)
    (P := fun U ↦ IsOpen (U : Set G)) fun v ↦ ⟨ρ.stabilizer v, IsSmooth.isOpen_stabilizer v, le_rfl⟩
  exact ⟨n, fun i ↦ ⟨U i, hU i⟩, hf⟩

/-- For a locally profinite group, a smooth representation is finitely generated over `A[G]`
exactly when it is a quotient of a finite direct sum `⊕_{i < n} A[G ⧸ U_i]` for compact open
subgroups `U_i`. -/
theorem finite_asModule_iff_exists_surjective_isCompact [NonarchimedeanGroup G]
    [WeaklyLocallyCompactSpace G] [IsSmooth ρ] :
    Module.Finite A[G] ρ.asModule ↔
      ∃ (n : ℕ) (U : Fin n → OpenSubgroup G), (∀ i, IsCompact (U i : Set G)) ∧
        ∃ f : IntertwiningMap (directSum fun i ↦ ofMulAction A G (G ⧸ (U i : Subgroup G))) ρ,
          Function.Surjective f := by
  refine ⟨fun _ ↦ ?_, fun ⟨n, U, _, f, hf⟩ ↦ finite_asModule_of_surjective f hf⟩
  obtain ⟨n, U, hU, hf⟩ := exists_surjective_of_finite_asModule (ρ := ρ)
    (P := fun U ↦ IsOpen (U : Set G) ∧ IsCompact (U : Set G)) fun v ↦ by
      obtain ⟨U, hU, hUv⟩ := mem_smoothVectors_iff_exists_isCompact_openSubgroup.1
        (IsSmooth.mem_smoothVectors (ρ := ρ) v)
      exact ⟨U, ⟨U.isOpen, hU⟩, hUv⟩
  exact ⟨n, fun i ↦ ⟨U i, (hU i).1⟩, fun i ↦ (hU i).2, hf⟩

end Representation
