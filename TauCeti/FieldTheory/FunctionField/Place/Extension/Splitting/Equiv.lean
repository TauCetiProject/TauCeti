/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Extension.Splitting.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Equiv

/-!
# Complete splitting under field isomorphisms

Complete splitting depends on the extension, not on its presentation as a field carrier.
Transporting the upstairs field over the downstairs field identifies the fibres of place
restriction and preserves the extension degree. This allows a compositum to be placed in a
finite Galois overfield without changing its splitting behaviour.
-/

public section

namespace TauCeti.Place

variable {k F L L' : Type*} [Field k] [Field F] [Field L] [Field L']
variable [Algebra k F] [Algebra k L] [Algebra k L'] [Algebra F L] [Algebra F L']
variable [IsScalarTower k F L] [IsScalarTower k F L']
variable [Algebra.IsIntegral F L] [Algebra.IsIntegral F L']

/-- Complete splitting is invariant under an isomorphism of the upstairs field over the
base field. -/
theorem isSplitCompletely_iff_of_algEquiv (P : Place k F) (e : L ≃ₐ[F] L') :
    P.IsSplitCompletely (k' := k) (F' := L) ↔
      P.IsSplitCompletely (k' := k) (F' := L') := by
  let t := equivOfRingEquiv (RingEquiv.refl k) (e.restrictScalars k).toRingEquiv
    (e.restrictScalars k).commutes
  have hrestrict (Q : Place k L) : (t Q).restrict k F = Q.restrict k F := by
    apply integers_injective
    ext x
    rw [mem_integers_restrict_iff, mem_integers_restrict_iff, mem_integers_iff,
      mem_integers_iff]
    simp [t, valuation_equivOfRingEquiv]
  have hfibre : {Q : Place k L | Q.restrict k F = P} =
      t ⁻¹' {Q : Place k L' | Q.restrict k F = P} := by
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hrestrict]
  have hcard : {Q : Place k L | Q.restrict k F = P}.ncard =
      {Q : Place k L' | Q.restrict k F = P}.ncard := by
    rw [hfibre]
    exact Set.ncard_preimage_of_injective_subset_range t.injective
      (by simp only [t.surjective.range_eq, Set.subset_univ])
  rw [isSplitCompletely_iff, isSplitCompletely_iff, hcard, e.toLinearEquiv.finrank_eq]
  exact and_congr (Module.Finite.equiv_iff e.toLinearEquiv) Iff.rfl

end TauCeti.Place
