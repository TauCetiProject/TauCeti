/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
import TauCeti.GroupTheory.QuotientGroup.Map
import Mathlib.FieldTheory.Finite.Basic

/-!
# Principal units are pro-p

Let `K` be a nonarchimedean local field with residue characteristic `p`. This file proves that
every positive-depth subgroup `U(K,m+1)`, in particular the group `U(K,1)` of principal units,
is pro-`p`.

The finite-level input is the unit filtration. Every quotient
`U(K,m+1) / U(K,m+n+1)` has order `q ^ n`, where `q` is the cardinality of the residue field
(`TauCeti.natCard_unitFiltration_succ_quotient_add_succ`).
Since `q` is a power of `p`, these quotients are `p`-groups. The subgroups `U(K,n)` form a
neighbourhood basis of `1`, so every continuous finite quotient of `U(K,m+1)` is a quotient of
one of these finite-level `p`-groups.

## Main results

* `TauCeti.isPGroup_unitFiltration_succ_quotient_add_succ`: every positive-depth finite-level
  quotient `U(K,m+1) / U(K,m+n+1)` is a `p`-group.
* `TauCeti.isProP_unitFiltration_succ`: every positive-depth subgroup `U(K,m+1)` is pro-`p`.
* `TauCeti.unitFiltration_one_isProP`: the principal-unit group is pro-`p`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5, Proposition 5.3.
-/

public section

noncomputable section

open Filter Topology ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Every positive-depth finite-level quotient `U(K,m+1) / U(K,m+n+1)` is a `p`-group when `p`
is the residue characteristic. No primality hypothesis is needed: the residue field is finite,
so its characteristic is automatically prime. -/
theorem isPGroup_unitFiltration_succ_quotient_add_succ (p : ℕ) [CharP 𝓀[K] p] (m n : ℕ) :
    IsPGroup p (unitFiltration K (m + 1) ⧸
      (unitFiltration K (m + n + 1)).subgroupOf (unitFiltration K (m + 1))) := by
  let _ := Fintype.ofFinite 𝓀[K]
  obtain ⟨d, -, hcard⟩ := FiniteField.card 𝓀[K] p
  apply IsPGroup.of_card (n := (d : ℕ) * n)
  rw [natCard_unitFiltration_succ_quotient_add_succ, Nat.card_eq_fintype_card, hcard, pow_mul]

private theorem exists_unitFiltration_subgroupOf_le (m : ℕ)
    (U : OpenNormalSubgroup (unitFiltration K (m + 1))) :
    ∃ n : ℕ, (unitFiltration K (m + n + 1)).subgroupOf (unitFiltration K (m + 1)) ≤
      U.toSubgroup := by
  have hU : (U.toSubgroup : Set (unitFiltration K (m + 1))) ∈
      𝓝 (1 : unitFiltration K (m + 1)) :=
    U.toOpenSubgroup.isOpen.mem_nhds U.toSubgroup.one_mem
  obtain ⟨s, hs, hsU⟩ := (mem_nhds_subtype
    (unitFiltration K (m + 1) : Set Kˣ) (1 : unitFiltration K (m + 1)) U.toSubgroup).mp hU
  obtain ⟨n, -, hn⟩ := (hasBasis_nhds_one_unitFiltration (K := K)).mem_iff.mp hs
  refine ⟨n, fun x hx ↦ hsU (hn ?_)⟩
  exact unitFiltration_antitone (by omega : n ≤ m + n + 1) hx

/-- Every positive-depth unit-filtration subgroup `U(K,m+1)` of a nonarchimedean local field is
pro-`p`, where `p` is the characteristic of the residue field. Equivalently, every continuous
finite quotient of `U(K,m+1)` is a `p`-group. Primality of `p` need not be assumed: it follows
from `CharP 𝓀[K] p`, since the residue field is finite. -/
theorem isProP_unitFiltration_succ (p : ℕ) [CharP 𝓀[K] p] (m : ℕ) :
    IsProP p (unitFiltration K (m + 1)) := by
  rw [isProP_iff]
  intro U
  obtain ⟨n, hn⟩ := exists_unitFiltration_subgroupOf_le m U
  exact (isPGroup_unitFiltration_succ_quotient_add_succ p m n).of_surjective
    (QuotientGroup.mapOfLE hn) (QuotientGroup.mapOfLE_surjective hn)

/-- **The principal units of a nonarchimedean local field are pro-`p`.** Here `p` is the
characteristic of the residue field. Equivalently, every continuous finite quotient of
`U(K,1)` is a `p`-group. This is the depth-one case of `isProP_unitFiltration_succ`. -/
theorem unitFiltration_one_isProP (p : ℕ) (hp : ringChar 𝓀[K] = p) :
    IsProP p (unitFiltration K 1) :=
  have _ : CharP 𝓀[K] p := ringChar.of_eq hp
  isProP_unitFiltration_succ p 0

end TauCeti
