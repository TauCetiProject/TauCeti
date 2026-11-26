/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.GaloisSet.Finite
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount

/-!
# Finitely and infinitely many Galois sets over a local field

Let `K` be a nonarchimedean local field with residue characteristic `p`. A positive integer `m`
that is nonzero in `K` admits only finitely many subextensions of `SeparableClosure K` of degree
`m` (`TauCeti.finite_setOf_finrank_eq`): sorted by residue degree `f`, they are the totally
ramified extensions of degree `m / f` of the unramified extension of degree `f`, finite in number
by Serre's finiteness of `σ_{K_f}(m / f)`. When `m` vanishes in `K`, that is in equal
characteristic `p` with `p ∣ m`, there are infinitely many already among the totally ramified
ones (`TauCeti.infinite_setOf_finrank_eq_iff`).

Since the labelled Galois sets of size `n` are finite in number exactly when the subextensions of
each degree `0 < m ≤ n` are (`TauCeti.finite_galoisSet_iff`), there are infinitely many Galois
sets of size `n` exactly when `K` has equal characteristic `p` and `p ≤ n`
(`TauCeti.infinite_galoisSet_iff`). In that case the étale mass `M_n(K)`, a sum over infinitely
many Galois sets in `ℝ≥0∞`, still has the finite value given by Bhargava's mass formula
`TauCeti.etaleMass_eq`.

## Main results

* `TauCeti.finite_setOf_finrank_eq`: if `m` is nonzero in `K`, there are finitely many
  subextensions of degree `m`.
* `TauCeti.infinite_setOf_finrank_eq_iff`: for `0 < m`, there are infinitely many subextensions
  of degree `m` exactly when `K` has equal characteristic `p` and `p ∣ m`.
* `TauCeti.infinite_galoisSet_iff`: there are infinitely many labelled Galois sets of size `n`
  exactly when `K` has equal characteristic `p` and `p ≤ n`.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, Remarque 1°.
* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, §8.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Finitely many subextensions of a given degree**: if `m` is nonzero in `K`, then
`SeparableClosure K` has only finitely many subextensions of degree `m` over `K`. -/
theorem finite_setOf_finrank_eq {m : ℕ} (hm : (m : K) ≠ 0) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = m}.Finite := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm Nat.cast_zero
  -- Sort the subextensions by their residue degree `f`, a divisor of `m`.
  refine ((Nat.divisors m).finite_toSet.biUnion fun f hf ↦
    finite_setOf_finrank_eq_and_inertiaDegree_eq (e := m / f) (Nat.pos_of_mem_divisors hf).ne'
      fun h ↦ hm ?_).subset fun L (hL : Module.finrank K L = m) ↦ ?_
  · obtain ⟨k, hk⟩ := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hf)
    rw [hk, Nat.cast_mul, h, zero_mul]
  · have hdvd : L.inertiaDegree ∣ m := hL ▸ L.inertiaDegree_dvd_finrank
    exact Set.mem_biUnion (x := L.inertiaDegree) (Nat.mem_divisors.2 ⟨hdvd, hm0⟩)
      ⟨by rw [hL, Nat.mul_div_cancel' hdvd], rfl⟩

/-- **The finiteness dichotomy for subextensions of a given degree**: for `0 < m`,
`SeparableClosure K` has infinitely many subextensions of degree `m` over `K` exactly when `K`
has equal characteristic `p`, the residue characteristic, and `p ∣ m`. -/
theorem infinite_setOf_finrank_eq_iff {m : ℕ} (hm : 0 < m) :
    {L : IntermediateField K (SeparableClosure K) | Module.finrank K L = m}.Infinite ↔
      ringChar K = ringChar 𝓀[K] ∧ ringChar 𝓀[K] ∣ m := by
  refine ⟨fun h ↦ ?_, fun h ↦ ((infinite_totallyRamifiedOfDegree_iff hm).2 h).mono fun L hL ↦
    (mem_totallyRamifiedOfDegree_iff.1 hL).1⟩
  rw [← natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd hm]
  exact not_not.1 fun hmK ↦ h (finite_setOf_finrank_eq hmK)

/-- **The finiteness dichotomy for Galois sets**: there are infinitely many labelled Galois sets
of size `n` over `K` exactly when `K` has equal characteristic `p`, the residue characteristic,
and `p ≤ n`. -/
theorem infinite_galoisSet_iff (n : ℕ) :
    Infinite (GaloisSet K n) ↔ ringChar K = ringChar 𝓀[K] ∧ ringChar 𝓀[K] ≤ n := by
  rw [← not_finite_iff_infinite, finite_galoisSet_iff]
  push Not
  constructor
  · rintro ⟨m, hm, hmn, h⟩
    obtain ⟨hK, hdvd⟩ := (infinite_setOf_finrank_eq_iff hm).1 h
    exact ⟨hK, (Nat.le_of_dvd hm hdvd).trans hmn⟩
  · rintro ⟨hK, hn⟩
    have hp : 0 < ringChar 𝓀[K] := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite _)
    exact ⟨_, hp, hn, (infinite_setOf_finrank_eq_iff hp).2 ⟨hK, dvd_rfl⟩⟩

end TauCeti
