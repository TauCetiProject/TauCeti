/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Dominant generators of an integral character lattice

For a finite reduced crystallographic root pairing over `ℤ`, every element of the weight
module is a difference of two dominant elements. Indeed, adding a sufficiently large
nonnegative multiple of the sum of the positive roots makes all simple-coroot pairings
nonnegative: that sum pairs to two with every simple coroot.

Consequently the dominant elements span the whole module over `ℤ`. If the module is finitely
generated, a finite set of dominant elements already spans it. Applied to the actual character
lattice of a reductive root datum, this supplies highest weights for a finite collection of
highest-weight modules whose combined weights generate that lattice. It does not construct
those modules or their integral forms.

No root-spanning hypothesis is needed: central character directions are retained, and the
result also applies to a root-free datum. In particular the weight module
is not replaced by the root lattice or the abstract full weight lattice.

## Main results

* `RootPairing.exists_add_nsmul_twoWeylVector_mem_dominantChamber`: a sufficiently large shift
  by the sum of positive roots is dominant.
* `RootPairing.exists_mem_dominantChamber_sub_eq`: every integral weight is a difference
  of dominant weights.
* `RootPairing.span_dominantChamber_eq_top`: dominant weights generate the integral module.
* `RootPairing.exists_finset_dominantChamber_span_eq_top`: finitely many dominant weights
  generate a finitely generated weight module.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1 (integral highest-weight modules).
-/

public section

namespace RootPairing

open TauCeti

variable {ι M N : Type*} [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N] (P : RootPairing ι ℤ M N)
  [Finite ι] [P.IsReduced] (b : P.Base)

/-- Adding a sufficiently large nonnegative multiple of the sum of positive roots makes
an integral weight dominant. The shift stays in the given weight module. -/
theorem exists_add_nsmul_twoWeylVector_mem_dominantChamber (x : M) :
    ∃ n : ℕ, x + n • twoWeylVector P b ∈ dominantChamber P b := by
  classical
  let n := ∑ i ∈ b.support, (-P.coroot' i x).toNat
  refine ⟨n, ?_⟩
  rw [mem_dominantChamber]
  intro i hi
  have hle : (-P.coroot' i x).toNat ≤ n :=
    Finset.single_le_sum (f := fun j ↦ (-P.coroot' j x).toNat) (fun _ _ ↦ Nat.zero_le _) hi
  have hbound : -P.coroot' i x ≤ ((-P.coroot' i x).toNat : ℤ) := Int.self_le_toNat _
  simp only [map_add, map_nsmul, coroot'_twoWeylVector P b hi, nsmul_eq_mul]
  omega

/-- Every weight in the integral module is a difference of two dominant weights in that
same module, even when roots do not span the module. -/
theorem exists_mem_dominantChamber_sub_eq (x : M) :
    ∃ μ ∈ dominantChamber P b, ∃ ν ∈ dominantChamber P b, μ - ν = x := by
  obtain ⟨n, hn⟩ := P.exists_add_nsmul_twoWeylVector_mem_dominantChamber b x
  refine ⟨x + n • twoWeylVector P b, hn, n • twoWeylVector P b, ?_, by abel⟩
  rw [mem_dominantChamber]
  intro i hi
  simp only [map_nsmul, coroot'_twoWeylVector P b hi, nsmul_eq_mul]
  positivity

/-- The dominant weights span the entire integral weight module, not merely its root span. -/
@[simp]
theorem span_dominantChamber_eq_top :
    Submodule.span ℤ (dominantChamber P b) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨μ, hμ, ν, hν, rfl⟩ := P.exists_mem_dominantChamber_sub_eq b x
  exact Submodule.sub_mem _ (Submodule.subset_span hμ) (Submodule.subset_span hν)

/-- A finitely generated integral weight module has a finite set of dominant generators.
These may be used as highest weights without losing any central or isogeny-lattice directions. -/
theorem exists_finset_dominantChamber_span_eq_top [Module.Finite ℤ M] :
    ∃ s : Finset M, ↑s ⊆ dominantChamber P b ∧ Submodule.span ℤ (s : Set M) = ⊤ := by
  have hfg : (Submodule.span ℤ (dominantChamber P b)).FG := by
    rw [P.span_dominantChamber_eq_top b]
    exact Module.Finite.fg_top
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_span_iff_fg_span_finset_subset _ |>.mp hfg
  exact ⟨s, hs, hspan.symm.trans (P.span_dominantChamber_eq_top b)⟩

end RootPairing
