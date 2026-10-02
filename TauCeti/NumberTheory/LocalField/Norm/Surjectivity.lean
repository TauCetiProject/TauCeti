/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Index

/-!
# Norm surjectivity above a ramification break

Surjectivity of the successive graded norms implies surjectivity on an entire unit-filtration
step. The image of the source step is compact, hence closed, and successive approximation
makes it dense in the target step. Thus no choice of an infinite product is needed.

For a Galois extension of prime degree with upper break `t`, this proves
`N(U(L, ψℕ(v))) = U(K,v)` whenever `t < v`. The depths are the canonical integral inverse
Herbrand values, so the result includes wild extensions without removing the Herbrand shift.

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

/-- Surjectivity of every graded norm at and beyond `v` implies surjectivity of the norm
from `U(L, ψℕ(v))` onto `U(K,v)`. -/
theorem map_normUnits_unitFiltration_eq_of_surjective_normGradedMap (v : ℕ)
    (h : ∀ n, v ≤ n → Function.Surjective (normGradedMap K L n)) :
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v := by
  let S := (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K)
  have hclosed : IsClosed (S : Set Kˣ) :=
    ((isCompact_unitFiltration (K := L) _).image (continuous_normUnits K L)).isClosed
  -- Each successive quotient is exhausted by norms from a subgroup of the fixed source step.
  have hstep (n : ℕ) (hn : v ≤ n) : unitFiltration K n ≤ S ⊔ unitFiltration K (n + 1) := by
    have hindex : (((unitFiltration L (psiNat K L n)).map (Algebra.normUnits K)) ⊔
        unitFiltration K (n + 1)).relIndex (unitFiltration K n) = 1 := by
      rw [relIndex_normUnits_unitFiltration_sup_eq_index_range_normGradedMap,
        MonoidHom.range_eq_top.2 (h n hn), Subgroup.index_top]
    exact (Subgroup.relIndex_eq_one.1 hindex).trans <| sup_le_sup_right
      (Subgroup.map_mono (unitFiltration_antitone ((psiNat_strictMono K L).monotone hn))) _
  exact le_antisymm (map_normUnits_unitFiltration_psiNat_le K L v)
    (unitFiltration_le_of_isClosed_of_le_sup hclosed hstep)

/-- **The norm is surjective on every unit step above a prime-degree break.** For a Galois
extension of prime degree with an upper break at a natural number `t`, the norm maps
`U(L, ψℕ(v))` onto `U(K,v)` whenever `t < v`. -/
theorem map_normUnits_unitFiltration_after_break (hℓ : (Module.finrank K L).Prime)
    {t v : ℕ} (hvt : t < v)
    (ht : UpperJump K L ⟨t, Nat.cast_mem_ramificationIndexDomain t⟩) :
    (unitFiltration L (psiNat K L v)).map (Algebra.normUnits K) = unitFiltration K v :=
  map_normUnits_unitFiltration_eq_of_surjective_normGradedMap v fun _ hn ↦
    (normGradedMap_after_break hℓ (hvt.trans_le hn) ht).surjective

end TauCeti
