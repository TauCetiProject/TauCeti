/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Quaternion.Subgroup

/-!
# Comparing the two Hasse invariants over a local field

Applying the canonical sign isomorphism on the quaternion subgroup of the Brauer group to the
Brauer-valued Hasse invariant gives the local Hasse invariant, since both invariants are products
over pairs of diagonal coefficients. This comparison uses the local classification of quaternion
algebras and requires no cohomological invariant map.

## Main results

* `TauCeti.RegularFormClass.quaternionSubgroupSignEquiv_apply_hasseInvariant`: the comparison of
  Brauer-valued and sign-valued Hasse invariants.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapters V, §3 and VI, §2.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.
-/

public section

noncomputable section

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

namespace RegularFormClass

/-- **The two Hasse invariants agree.** The sign isomorphism on the quaternion subgroup carries
the Brauer-valued Hasse invariant to the local Hasse invariant. -/
@[simp]
theorem quaternionSubgroupSignEquiv_apply_hasseInvariant (q : RegularFormClass K) :
    BrauerGroup.quaternionSubgroupSignEquiv
      ⟨hasseInvariant q, hasseInvariant_mem_quaternionSubgroup q⟩ = localHasse q := by
  induction q using Quotient.inductionOn with
  | h p =>
    let f : Kˣ → Kˣ → BrauerGroup.quaternionSubgroup K := fun a b =>
      ⟨BrauerGroup.quaternionClass a b, BrauerGroup.quaternionClass_mem_quaternionSubgroup K a b⟩
    have hprod :
        (⟨hasseInvariant (Quotient.mk (regularFormSetoid K) p),
          hasseInvariant_mem_quaternionSubgroup _⟩ : BrauerGroup.quaternionSubgroup K) =
          ∏ i, ∏ j ∈ Finset.Ioi i, f (p.2 i) (p.2 j) := by
      apply Subtype.ext
      simp [f]
    rw [hprod, map_prod, localHasse_mk]
    simp only [map_prod, f, BrauerGroup.quaternionSubgroupSignEquiv_apply_quaternionClass]

end RegularFormClass

end TauCeti
