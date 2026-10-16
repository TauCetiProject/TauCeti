/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration
import TauCeti.LinearAlgebra.Submodule.Quotient

/-!
# The zero-form Clifford filtration

When the quadratic form is zero, its Clifford algebra is the exterior algebra. This file identifies
the Clifford degree filtration with the sum of exterior degrees up to the same bound, then uses the
exterior algebra's internal grading to identify each successive filtration quotient with the
corresponding exterior power.

Transporting these quotient equivalences along a filtration-preserving change of quadratic form
identifies the associated graded of a Clifford algebra with the exterior algebra.

## Main results

* `CliffordAlgebra.exteriorPower_succ_disjoint_zero_form_filtration`: degree `k + 1` is
  disjoint from the lower zero-form filtration.
* `CliffordAlgebra.zeroFormFiltrationQuotientEquivExteriorPower`: the successive
  zero-form filtration quotient is the degree `k + 1` exterior power.
-/

public section

open scoped DirectSum

universe u v

namespace CliffordAlgebra

open TauCeti.Algebra.wordFiltration

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The degree `k + 1` exterior power is disjoint from the lower zero-form filtration. -/
theorem exteriorPower_succ_disjoint_zero_form_filtration (k : ℕ) :
    Disjoint (⋀[R]^(k + 1) M) (filtration (0 : QuadraticForm R M) k) := by
  rw [filtration_eq_iSup_pow (0 : QuadraticForm R M) k]
  rw [iSup_subtype]
  have hind : iSupIndep (fun i : ℕ => ⋀[R]^i M) :=
    (DirectSum.Decomposition.isInternal (fun i : ℕ => ⋀[R]^i M)).submodule_iSupIndep
  simpa only [Set.mem_Iic] using hind.disjoint_biSup (by simp : k + 1 ∉ Set.Iic k)

/-- The successive zero-form Clifford filtration quotient is the degree `k + 1` exterior power. -/
noncomputable def zeroFormFiltrationQuotientEquivExteriorPower (k : ℕ) :
    GradedPiece (ι (0 : QuadraticForm R M)) (k + 1) ≃ₗ[R] ⋀[R]^(k + 1) M :=
  (Submodule.quotEquivOfEq _ _
    (previousRestricted_succ (ι (0 : QuadraticForm R M)) k)).trans
    (Submodule.quotientEquivOfEqSup _ _ _
      ((filtration_succ_eq_sup (0 : QuadraticForm R M) k).trans (sup_comm _ _))
      (exteriorPower_succ_disjoint_zero_form_filtration k))

/-- The inverse quotient equivalence sends a degree `k + 1` exterior element to its canonical
quotient class. -/
@[simp]
theorem zeroFormFiltrationQuotientEquivExteriorPower_symm_apply (k : ℕ)
    (x : ⋀[R]^(k + 1) M) :
    (zeroFormFiltrationQuotientEquivExteriorPower k).symm x =
      Submodule.Quotient.mk
        ⟨x, ι_range_pow_le_filtration (0 : QuadraticForm R M) (k + 1) x.property⟩ := by
  rw [zeroFormFiltrationQuotientEquivExteriorPower, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, Submodule.quotientEquivOfEqSup_symm_apply]
  apply (Submodule.quotEquivOfEq _ _
    (previousRestricted_succ (ι (0 : QuadraticForm R M)) k)).injective
  rw [LinearEquiv.apply_symm_apply, Submodule.quotEquivOfEq_mk]

/-- The quotient equivalence sends the canonical class of a degree `k + 1` exterior element to
that element. -/
@[simp]
theorem zeroFormFiltrationQuotientEquivExteriorPower_apply (k : ℕ)
    (x : ⋀[R]^(k + 1) M) :
    zeroFormFiltrationQuotientEquivExteriorPower k
      (Submodule.Quotient.mk
        ⟨x, ι_range_pow_le_filtration (0 : QuadraticForm R M) (k + 1) x.property⟩) = x := by
  rw [← zeroFormFiltrationQuotientEquivExteriorPower_symm_apply k x,
    LinearEquiv.apply_symm_apply]

end CliffordAlgebra
