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
the group `U(K,1)` of principal units is pro-`p`.

The finite-level input is the unit filtration. Every quotient
`U(K,m+1) / U(K,m+n+1)` has order `q ^ n`, where `q` is the cardinality of the residue field.
Since `q` is a power of `p`, these quotients are `p`-groups. The subgroups `U(K,n+1)` form a
neighbourhood basis of `1`, so every continuous finite quotient of `U(K,1)` is a quotient of one
of these finite-level `p`-groups.

## Main results

* `TauCeti.relIndex_unitFiltration_add_succ`: the index of `U(K,m+n+1)` in `U(K,m+1)` is
  `q ^ n`.
* `TauCeti.isPGroup_unitFiltration_succ_quotient_add_succ`: every positive-depth finite-level
  quotient `U(K,m+1) / U(K,m+n+1)` is a `p`-group.
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

/-- The index of `U(K,m+n+1)` in `U(K,m+1)` is `q ^ n`, where `q = #𝓀[K]`. -/
theorem relIndex_unitFiltration_add_succ (m n : ℕ) :
    (unitFiltration K (m + n + 1)).relIndex (unitFiltration K (m + 1)) =
      (Nat.card 𝓀[K]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ]
      calc
        (unitFiltration K (m + n + 2)).relIndex (unitFiltration K (m + 1)) =
            (unitFiltration K (m + n + 2)).relIndex (unitFiltration K (m + n + 1)) *
              (unitFiltration K (m + n + 1)).relIndex (unitFiltration K (m + 1)) :=
          (Subgroup.relIndex_mul_relIndex _ _ _
            (unitFiltration_antitone (K := K) (by omega : m + n + 1 ≤ m + n + 2))
            (unitFiltration_antitone (K := K) (by omega : m + 1 ≤ m + n + 1))).symm
        _ = (Nat.card 𝓀[K]) ^ (n + 1) := by
          rw [relIndex_unitFiltration_succ_succ, ih, pow_succ']

/-- Every inclusion `U(K,m+n+1) ≤ U(K,m+1)` has finite relative index. -/
noncomputable instance unitFiltration_add_succ_isFiniteRelIndex_succ (m n : ℕ) :
    (unitFiltration K (m + n + 1)).IsFiniteRelIndex (unitFiltration K (m + 1)) := by
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, relIndex_unitFiltration_add_succ]
  exact pow_ne_zero n Nat.card_pos.ne'

/-- Every `U(K,n+1)` has finite relative index in the principal units `U(K,1)`. -/
noncomputable instance unitFiltration_succ_isFiniteRelIndex_one (n : ℕ) :
    (unitFiltration K (n + 1)).IsFiniteRelIndex (unitFiltration K 1) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
      exact (unitFiltration_add_succ_isFiniteRelIndex_succ n 1).trans ih

/-- The positive-depth finite-level quotient `U(K,m+1) / U(K,m+n+1)` has `q ^ n` elements,
where `q = #𝓀[K]`. -/
theorem natCard_unitFiltration_succ_quotient_add_succ (m n : ℕ) :
    Nat.card (unitFiltration K (m + 1) ⧸
      (unitFiltration K (m + n + 1)).subgroupOf (unitFiltration K (m + 1))) =
        (Nat.card 𝓀[K]) ^ n := by
  rw [← Subgroup.index_eq_card]
  exact relIndex_unitFiltration_add_succ m n

/-- Every positive-depth finite-level quotient `U(K,m+1) / U(K,m+n+1)` is a `p`-group when `p`
is the residue characteristic. No primality hypothesis is needed: the residue field is finite,
so its characteristic is automatically prime. -/
theorem isPGroup_unitFiltration_succ_quotient_add_succ (p m n : ℕ)
    (hp : ringChar 𝓀[K] = p) :
    IsPGroup p (unitFiltration K (m + 1) ⧸
      (unitFiltration K (m + n + 1)).subgroupOf (unitFiltration K (m + 1))) := by
  let _ : CharP 𝓀[K] p := ringChar.of_eq hp
  let _ := Fintype.ofFinite 𝓀[K]
  obtain ⟨d, -, hcard⟩ := FiniteField.card 𝓀[K] p
  apply IsPGroup.of_card (n := (d : ℕ) * n)
  rw [natCard_unitFiltration_succ_quotient_add_succ, Nat.card_eq_fintype_card, hcard, pow_mul]

private theorem exists_unitFiltration_subgroupOf_le
    (U : OpenNormalSubgroup (unitFiltration K 1)) :
    ∃ n : ℕ, (unitFiltration K (n + 1)).subgroupOf (unitFiltration K 1) ≤ U.toSubgroup := by
  have hU : (U.toSubgroup : Set (unitFiltration K 1)) ∈
      𝓝 (1 : unitFiltration K 1) :=
    U.toOpenSubgroup.isOpen.mem_nhds U.toSubgroup.one_mem
  obtain ⟨s, hs, hsU⟩ := (mem_nhds_subtype
    (unitFiltration K 1 : Set Kˣ) (1 : unitFiltration K 1) U.toSubgroup).mp hU
  obtain ⟨n, -, hn⟩ := (hasBasis_nhds_one_unitFiltration (K := K)).mem_iff.mp hs
  refine ⟨n, fun x hx ↦ hsU (hn ?_)⟩
  exact unitFiltration_antitone (Nat.le_succ n) hx

/-- **The principal units of a nonarchimedean local field are pro-`p`.** Here `p` is the
characteristic of the residue field. Equivalently, every continuous finite quotient of
`U(K,1)` is a `p`-group. Primality of `p` need not be assumed: it follows from `hp`, since
the residue field is finite. -/
theorem unitFiltration_one_isProP (p : ℕ) (hp : ringChar 𝓀[K] = p) :
    IsProP p (unitFiltration K 1) := by
  rw [isProP_iff]
  intro U
  obtain ⟨n, hn⟩ := exists_unitFiltration_subgroupOf_le U
  let N := (unitFiltration K (n + 1)).subgroupOf (unitFiltration K 1)
  -- `unitFiltration` is sealed, so transport the generalized level explicitly at `m = 0`.
  have hlevel : unitFiltration K (0 + n + 1) = unitFiltration K (n + 1) :=
    congrArg (unitFiltration K) (by omega)
  have hN : IsPGroup p (unitFiltration K 1 ⧸ N) := by
    change IsPGroup p (unitFiltration K 1 ⧸
      (unitFiltration K (n + 1)).subgroupOf (unitFiltration K 1))
    rw [← hlevel]
    exact isPGroup_unitFiltration_succ_quotient_add_succ p 0 n hp
  exact hN.of_surjective (QuotientGroup.mapOfLE hn) (QuotientGroup.mapOfLE_surjective hn)

end TauCeti
