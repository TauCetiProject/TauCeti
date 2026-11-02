/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Table
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Recognizing subgroups with certified coset tables

A certified coset table for `H` supplies a finite cover of `G / H`, even when `G` is not
known to be finite. If `H ≤ K`, testing the table representatives for membership in `K`
can prove `H = K`: every representative belonging to `K` must already belong to `H`.
In particular, a subgroup of a centralizer is the whole centralizer if each representative
commuting with the distinguished element belongs to that subgroup. This identifies the actual
centralizer, rather than merely producing a subgroup with a proposed order.

Distinctness of the named cosets upgrades the table's index bound to an exact index.
Together with an independent order of `H`, this computes the order of a recognized centralizer.
No normality of `H`, finite ambient group, or faithful permutation image is assumed.

## References

* D. F. Holt, B. Eick, E. A. O'Brien, *Handbook of Computational Group Theory*,
  Chapman & Hall/CRC, 2005, Chapter 5 (coset enumeration).
-/

public section

namespace TauCeti.CosetTable

variable {m k : ℕ} {T : CosetTable m k} {G : Type*} [Group G] {g : Fin m → G}
  {H : Subgroup G} {rels stab : List (List (Fin m))}
  {cert : List (Fin k × List (Fin m))}

/-- A certified table identifies an overgroup `K` with `H` if every named representative
belonging to `K` belongs to `H`. Repeated cosets in the table are allowed. -/
theorem eq_of_le_of_check (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H) {K : Subgroup G} (hHK : H ≤ K)
    (hrep : ∀ i, ((T.word i).map g).prod ∈ K → ((T.word i).map g).prod ∈ H) :
    H = K := by
  refine le_antisymm hHK fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := T.surjective_point hg hT hrels hstab (x : G ⧸ H)
  have hcoset : ((T.word i).map g).prod⁻¹ * x ∈ H := by
    apply QuotientGroup.eq.mp
    simpa [point_def, MulAction.Quotient.smul_mk] using hi
  have hword : ((T.word i).map g).prod ∈ K := by
    simpa using K.mul_mem hx (K.inv_mem (hHK hcoset))
  simpa using H.mul_mem (hrep i hword) hcoset

/-- A certified coset table recognizes the centralizer of `x` from a contained subgroup.
The separation tests concern the actual word values in `G`, so an unaccounted kernel in a
permutation image cannot certify this conclusion. -/
theorem eq_centralizer_of_check (hg : Subgroup.closure (Set.range g) = ⊤)
    (hT : T.check rels stab cert = true) (hrels : ∀ r ∈ rels, (r.map g).prod = 1)
    (hstab : ∀ r ∈ stab, (r.map g).prod ∈ H) (x : G)
    (hH : ∀ h ∈ H, h * x = x * h)
    (hrep : ∀ i, ((T.word i).map g).prod * x = x * ((T.word i).map g).prod →
      ((T.word i).map g).prod ∈ H) : H = Subgroup.centralizer {x} := by
  apply eq_of_le_of_check hg hT hrels hstab
  · intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hH h hh)
  · intro i hi
    exact hrep i (Subgroup.mem_centralizer_singleton_iff.mp hi)

end TauCeti.CosetTable
