/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.Idempotents
public import TauCeti.Algebra.MonoidAlgebra.Torsion

/-!
# Connected spectra of group algebras in positive characteristic

For an abelian `p`-group, every element of its group algebra in exponential
characteristic `p` differs from its augmentation by a nilpotent. Thus the group
algebra has connected spectrum whenever the coefficient ring does. Over a field
of characteristic `p`, the converse holds for finite abelian groups.

This detects connected finite diagonalizable group schemes, including the
nonreduced groups of roots of unity of prime-power order.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), §12.

The converse uses Tau Ceti's normalized finite-subgroup averages.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

variable (R : Type*) [CommRing R] {G : Type*} [CommGroup G]
variable (p : ℕ) [ExpChar R p]

/-- In the group algebra of an abelian `p`-group in exponential characteristic `p`,
every element differs from its augmentation by a nilpotent. No finiteness assumption
on the group is needed. -/
theorem isNilpotent_sub_algebraMap_counit_of_isPGroup (hG : IsPGroup p G) (x : R[G]) :
    IsNilpotent (x - algebraMap R R[G] (Coalgebra.counit (R := R) x)) := by
  have _ : ExpChar R[G] p :=
    expChar_of_injective_algebraMap (Bialgebra.algebraMap_injective (R := R) R[G]) p
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add, add_sub_add_comm] using (Commute.all _ _).isNilpotent_add hx hy
  | single g a =>
      obtain ⟨n, hn⟩ := hG.exists_pow_pow_eq_one g
      refine ⟨p ^ n, ?_⟩
      rw [sub_pow_expChar_pow, MonoidAlgebra.single_pow, hn,
        MonoidAlgebra.counit_single, ← map_pow]
      simp [MonoidAlgebra.coe_algebraMap]

/-- An abelian `p`-group has connected group-algebra spectrum over a connected
commutative ring of exponential characteristic `p`. -/
theorem connectedSpace_primeSpectrum_monoidAlgebra_of_isPGroup
    [ConnectedSpace (PrimeSpectrum R)] (hG : IsPGroup p G) :
    ConnectedSpace (PrimeSpectrum R[G]) := by
  let _ : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance
  rw [connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one]
  intro e he
  have hc := he.map (Bialgebra.counitAlgHom R R[G])
  have heq := eq_of_isNilpotent_sub_of_isIdempotentElem
    he (hc.map (algebraMap R R[G]))
    (isNilpotent_sub_algebraMap_counit_of_isPGroup R p hG e)
  rcases eq_zero_or_eq_one_of_isIdempotentElem hc with h | h
  · exact Or.inl (by simpa only [h, map_zero] using heq)
  · exact Or.inr (by simpa only [h, map_one] using heq)

variable (k : Type*) [Field k] (G : Type*) [CommGroup G] [Finite G]
variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A finite abelian group has connected group-algebra spectrum over a field of
characteristic `p` if and only if it is a `p`-group. -/
theorem connectedSpace_primeSpectrum_monoidAlgebra_iff_isPGroup :
    ConnectedSpace (PrimeSpectrum k[G]) ↔ IsPGroup p G := by
  refine ⟨fun hconn => ?_, connectedSpace_primeSpectrum_monoidAlgebra_of_isPGroup k p⟩
  let _ := hconn
  rw [isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero]
  intro q hq
  obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
  have _ : Fact q.Prime := ⟨hqprime⟩
  suffices q = p by simpa [this] using (Nat.mem_primeFactors.mpr
    ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩ : p ∈ p.primeFactors)
  by_contra hqp
  have hqk : (q : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    exact fun h => hqp ((Nat.prime_dvd_prime_iff_eq Fact.out hqprime).mp h).symm
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  let P := Subgroup.zpowers g
  let _ : Fintype P := Fintype.ofFinite P
  have hcard : Fintype.card P = q := by
    simpa only [Nat.card_eq_fintype_card] using (Nat.card_zpowers g).trans hg
  have hnz : (Fintype.card P : k) ≠ 0 := by simpa only [hcard] using hqk
  have hidem := isIdempotentElem_groupAlgebraSubgroupAverage k P hnz
  rcases eq_zero_or_eq_one_of_isIdempotentElem hidem with hzero | hone
  · exact groupAlgebraSubgroupAverage_ne_zero k P hnz hzero
  · exact groupAlgebraSubgroupAverage_ne_one k P ⟨g, Subgroup.mem_zpowers g⟩
      (fun h => hqprime.ne_one (hg.symm.trans (orderOf_eq_one_iff.mpr h))) hone

end TauCeti
