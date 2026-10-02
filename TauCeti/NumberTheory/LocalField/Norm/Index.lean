/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Graded
import TauCeti.GroupTheory.QuotientGroup.Index
import TauCeti.NumberTheory.LocalField.TamelyRamified

/-!
# Norm indices before and at a ramification break

For a finite Galois extension `L/K`, the cokernel of the graded norm at depth `v` measures the
relative index

`[U(K,v) : N(U(L, ψℕ(v))) · U(K,v+1)]`.

This file identifies these two indices, using the image of the norm in the successive unit
quotient. For an extension of prime degree `ℓ` with an upper break at a natural number `t`,
the relative index is `1` at every depth `v < t`, and is `ℓ` at depth `t`, including the tame
break at zero. These are the finite-step norm indices used in conductor computations.

The product of the two subgroups is written as their join: the unit group is commutative.
The statements concern norms modulo the next unit step; they do not assert surjectivity of the
norm onto an entire step of the unit filtration.

## Main results

* `TauCeti.relIndex_normUnits_unitFiltration_sup_eq_index_range_normGradedMap`: the relative
  index is the index of the image of the graded norm.
* `TauCeti.relIndex_normUnits_unitFiltration_sup_before_break`: the index is `1` before a
  prime-degree break.
* `TauCeti.relIndex_normUnits_unitFiltration_sup_at_break`: the index at the break is the degree.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3, Proposition 5 and its corollaries.
-/

public section
noncomputable section

open TauCeti.LocalFieldsRamification

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

/-- The image of the graded norm is the image, in the successive unit quotient, of the norm
subgroup at the Herbrand-shifted depth. -/
theorem range_normGradedMap (v : ℕ) :
    (normGradedMap K L v).range =
      (((unitFiltration L (psiNat K L v)).map (Algebra.normUnits K)).subgroupOf
        (unitFiltration K v)).map
          (QuotientGroup.mk' ((unitFiltration K (v + 1)).subgroupOf (unitFiltration K v))) := by
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [normGradedMap_mk]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ x.2)
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hx
    refine ⟨QuotientGroup.mk (⟨y, hy⟩ : unitFiltration L (psiNat K L v)), ?_⟩
    rw [normGradedMap_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext hxy)

/-- The cokernel index of the graded norm equals the index in `U(K,v)` of the product of
`N(U(L, ψℕ(v)))` with `U(K,v+1)`. This holds for every finite Galois extension. -/
theorem relIndex_normUnits_unitFiltration_sup_eq_index_range_normGradedMap (v : ℕ) :
    (((unitFiltration L (psiNat K L v)).map (Algebra.normUnits K)) ⊔
      unitFiltration K (v + 1)).relIndex (unitFiltration K v) =
        (normGradedMap K L v).range.index := by
  rw [range_normGradedMap, Subgroup.index_map_mk'_eq_index_sup,
    ← Subgroup.subgroupOf_sup (map_normUnits_unitFiltration_psiNat_le K L v)
      (unitFiltration_antitone v.le_succ)]
  rw [Subgroup.relIndex]

/-- In prime degree, before an upper break at `t`, every unit of depth `v < t` is congruent,
modulo `U(K,v+1)`, to a norm from depth `ψℕ(v)`. Equivalently, the relative norm index is `1`.
This includes depth zero when the break is positive. -/
theorem relIndex_normUnits_unitFiltration_sup_before_break (hℓ : (Module.finrank K L).Prime)
    {v t : ℕ} (hvt : v < t)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    (((unitFiltration L (psiNat K L v)).map (Algebra.normUnits K)) ⊔
      unitFiltration K (v + 1)).relIndex (unitFiltration K v) = 1 := by
  rw [relIndex_normUnits_unitFiltration_sup_eq_index_range_normGradedMap,
    MonoidHom.range_eq_top.2 (normGradedMap_positive_before_break hℓ hvt ht).surjective,
    Subgroup.index_top]

/-- In a Galois extension of prime degree `ℓ` with an upper break at a natural number `t`,
the norms from `U(L, ψℕ(t))`, together with `U(K,t+1)`, have index `ℓ` in `U(K,t)`.
At the tame break `t = 0` this is the residue-unit power map; at a positive break it is the
additive polynomial on the residue field whose kernel and cokernel have order `ℓ`.
Total ramification follows from the existence of the break. -/
theorem relIndex_normUnits_unitFiltration_sup_at_break (hℓ : (Module.finrank K L).Prime)
    {t : ℕ} (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    (((unitFiltration L (psiNat K L t)).map (Algebra.normUnits K)) ⊔
      unitFiltration K (t + 1)).relIndex (unitFiltration K t) = Module.finrank K L := by
  rw [relIndex_normUnits_unitFiltration_sup_eq_index_range_normGradedMap]
  rcases t with _ | t
  · have htotal : IsTotallyRamified K L :=
      (lowerRamificationGroup_zero_eq_top_iff K L).1
        (by simpa using lowerRamificationGroup_natCast_eq_top_of_upperJump K L hℓ ht)
    have htame : IsTamelyRamified K L :=
      (lowerRamificationGroup_one_eq_bot_iff_isTamelyRamified K L).1
        (by simpa using lowerRamificationGroup_natCast_add_one_eq_bot_of_upperJump K L hℓ ht)
    exact (normGradedMap_tame_break_zero htotal htame).2
  · exact (normGradedMap_at_break hℓ t.succ_pos ht).2

end TauCeti
