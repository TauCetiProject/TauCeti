/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# The action of a decomposition group on its valuation subring

For a valuation subring `A` of a field `L` and a subfield `K`, Mathlib's
`ValuationSubring.decompositionSubgroup K A` acts on `A` by restricting its action on `L`.
This file records that the restricted action is computed in `L`, and that it is faithful
because `L` is the field of fractions of `A`.

## Main results

* `ValuationSubring.coe_decompositionSubgroup_smul`: the action on `A` is the restriction of the
  action on `L`.
* `ValuationSubring.decompositionSubgroup.ext`: two elements of the decomposition group that agree
  on `A` are equal.
* `ValuationSubring.instFaithfulSMulDecompositionSubgroup`: the decomposition group acts
  faithfully on `A`.
-/

public section

namespace ValuationSubring

universe w w'

variable {K : Type w} {L : Type w'} [Field K] [Field L] [Algebra K L]

/-- The action of a decomposition group on its valuation subring is the restriction of its
action on the fraction field. -/
@[simp]
theorem coe_decompositionSubgroup_smul (A : ValuationSubring L)
    (g : A.decompositionSubgroup K) (x : A) :
    ((g • x : A) : L) = (g : L ≃ₐ[K] L) (x : L) := by
  rw [← AlgEquiv.smul_def, ← Submonoid.smul_def]
  rfl

/-- Two automorphisms in the decomposition group of a valuation subring that agree on the
valuation subring are equal, because its ambient field is its field of fractions. -/
@[ext]
theorem decompositionSubgroup.ext (A : ValuationSubring L)
    {g h : A.decompositionSubgroup K}
    (hgh : ∀ x : A, (g : L ≃ₐ[K] L) x = (h : L ≃ₐ[K] L) x) : g = h :=
  Subtype.ext <| AlgEquiv.ext fun y ↦ DFunLike.congr_fun
    (IsFractionRing.ringHom_ext (A := A) (f1 := ((g : L ≃ₐ[K] L) : L →+* L))
      (f2 := ((h : L ≃ₐ[K] L) : L →+* L)) hgh) y

/-- The decomposition group of a valuation subring acts faithfully on that subring. -/
instance instFaithfulSMulDecompositionSubgroup (A : ValuationSubring L) :
    FaithfulSMul (A.decompositionSubgroup K) A where
  eq_of_smul_eq_smul {g h} heq := decompositionSubgroup.ext A fun x ↦ by
    simpa only [coe_decompositionSubgroup_smul] using congrArg Subtype.val (heq x)

end ValuationSubring
