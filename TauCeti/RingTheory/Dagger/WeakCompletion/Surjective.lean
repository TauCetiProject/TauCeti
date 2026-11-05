/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WeakCompletion.Map

/-!
# Weak completion preserves surjections

A surjective map of finitely generated algebras induces a surjection of their
Monsky–Washnitzer weak completions.

In particular, a polynomial presentation of an algebra gives a surjection from the weak
completion of the polynomial algebra. This is the first step in presenting weak completions
as quotients of integral overconvergent power-series rings; identifying the kernel is separate.

The result holds over any commutative base ring, for every parameter, including zero,
units, and nilpotent parameters. Neither flatness nor adic separatedness is required.

## References

* P. Monsky and G. Washnitzer, *Formal cohomology. I*, Ann. of Math. 88 (1968), §2.
* M. van der Put, *The cohomology of Monsky and Washnitzer*, Mém. Soc. Math. France 23
  (1986), §2, (2.1)–(2.2).
-/

public section

namespace TauCeti.Dagger.weakCompletion

open Finset MvPolynomial

variable {O S T : Type*} [CommRing O] [CommRing S] [CommRing T]
  [Algebra O S] [Algebra O T] (π : O)
  [Algebra.FiniteType O S] [Algebra.FiniteType O T]

/-- A surjection of finitely generated algebras induces a surjection of weak completions. -/
theorem map_surjective (f : S →ₐ[O] T) (hf : Function.Surjective f) :
    Function.Surjective (map π f) := by
  -- Lift a finite target generating family and retain the same polynomials and degree bound.
  -- The lifted partial sums form an adic Cauchy sequence whose limit lies in the weak completion.
  classical
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := O) (A := T)
  have ht' : Algebra.adjoin O (Set.range ((↑) : t → T)) = ⊤ := by
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht
  choose x hx using fun i : t ↦ hf (i : T)
  intro z
  obtain ⟨c, P, hP, hz⟩ := (mem_weakCompletion_iff π ht').mp z.property
  obtain ⟨w, hwset, hw⟩ := exists_mem_weakCompletionSet_of_degree_le π x P hP
  have hwmem : w ∈ weakCompletion π S := by
    obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := O) (A := S)
    have hs' : Algebra.adjoin O (Set.range ((↑) : s → S)) = ⊤ := by
      simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hs
    rw [← SetLike.mem_coe, coe_weakCompletion π _ hs']
    apply weakCompletionSet_subset_of_forall_mem_adjoin (x := x)
      (fun _ ↦ hs'.symm ▸ Algebra.mem_top)
    exact hwset
  refine ⟨⟨w, hwmem⟩, Subtype.ext ?_⟩
  apply AdicCompletion.ext_evalₐ
  intro k
  rw [coe_map, AdicCompletion.evalₐ_mapₐ, hw, Ideal.quotientMap_mk, hz]
  congr 1
  simp only [map_sum, map_mul, map_pow, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, f.commutes, comp_aeval_apply, hx]

/-- Every finite polynomial generating family gives a surjection from the weak completion
of its polynomial algebra onto the weak completion of the algebra. -/
theorem map_aeval_surjective {ι : Type*} [Finite ι] (x : ι → S)
    (hx : Algebra.adjoin O (Set.range x) = ⊤) :
    Function.Surjective (map π (aeval x)) := by
  apply map_surjective
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  exact hx

end TauCeti.Dagger.weakCompletion
