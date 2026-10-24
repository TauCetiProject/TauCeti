/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import TauCeti.LinearAlgebra.CliffordAlgebra.VectorNormalizer
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero

/-!
# The Clifford vector normalizer in dimension zero

Every Clifford unit preserves the vector range of a subsingleton module. Thus the vector
normalizer is the full unit group, canonically identified with the scalar units by
`CliffordAlgebra.vectorNormalizerEquivUnitsOfSubsingleton`.

This file combines the general vector normalizer with the basic zero-dimensional Clifford
algebra equivalence without introducing a dependency on Spin theory.
-/

public section

namespace CliffordAlgebra

universe u v

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

/-- In dimension zero every Clifford unit preserves the vector range in both directions. -/
@[simp]
theorem vectorNormalizer_eq_top_of_subsingleton [Subsingleton M] :
    vectorNormalizer Q = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [mem_vectorNormalizer_iff]
  constructor <;> intro m <;> simp [Subsingleton.elim m 0]

/-- The dimension-zero Clifford vector normalizer is the full scalar unit group. -/
noncomputable def vectorNormalizerEquivUnitsOfSubsingleton [Subsingleton M] :
    vectorNormalizer Q ≃* Rˣ :=
  ((MulEquiv.subgroupCongr (vectorNormalizer_eq_top_of_subsingleton Q)).trans
    Subgroup.topEquiv).trans (unitsEquivOfSubsingleton Q)

/-- The dimension-zero normalizer equivalence sends a Clifford unit to its scalar coordinate. -/
@[simp]
theorem vectorNormalizerEquivUnitsOfSubsingleton_apply [Subsingleton M]
    (x : vectorNormalizer Q) :
    vectorNormalizerEquivUnitsOfSubsingleton Q x =
      unitsEquivOfSubsingleton Q (x : (CliffordAlgebra Q)ˣ) := by
  simp only [vectorNormalizerEquivUnitsOfSubsingleton, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply, Subgroup.topEquiv_apply]

/-- The inverse dimension-zero normalizer equivalence sends a scalar unit to its Clifford unit. -/
@[simp]
theorem coe_vectorNormalizerEquivUnitsOfSubsingleton_symm_apply [Subsingleton M] (u : Rˣ) :
    ((vectorNormalizerEquivUnitsOfSubsingleton Q).symm u : (CliffordAlgebra Q)ˣ) =
      (unitsEquivOfSubsingleton Q).symm u := by
  apply (unitsEquivOfSubsingleton Q).injective
  have hx : unitsEquivOfSubsingleton Q
      ((vectorNormalizerEquivUnitsOfSubsingleton Q).symm u : (CliffordAlgebra Q)ˣ) = u := by
    rw [← vectorNormalizerEquivUnitsOfSubsingleton_apply, MulEquiv.apply_symm_apply]
  rw [hx, MulEquiv.apply_symm_apply]

end CliffordAlgebra

end
