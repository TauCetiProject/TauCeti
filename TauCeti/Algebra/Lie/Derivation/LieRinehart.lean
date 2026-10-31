/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.OuterCenter

/-!
# Central coefficients on continuous outer derivations

Continuous derivations of a topological associative algebra `A` form a module over its center.
The actual image of inner derivations is stable under this action: `z • ad b = ad (z * b)`.
Consequently the existing quotient `ContinuousOuterDerivation R A` inherits a center-module
structure, without closing the inner image or changing the quotient topology.

Restriction to the center is the anchor. It is center-linear and satisfies the
Lie–Rinehart identity `⁅D, z • E⁆ = z • ⁅D, E⁆ + anchor(D)(z) • E`, both before and after
passing to outer classes. These identities allow central coefficients in infinitesimal
module deformations; they do not assert that derivations are linear over the center.

## References

* G. S. Rinehart, *Differential forms on general commutative algebras*, Transactions of the
  American Mathematical Society 108 (1963), 195–222.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousConstSMul R A] [SeparatelyContinuousMul A]

namespace continuousDerivationLieAlgebra

/-- Central multiplication preserves continuity of a derivation. -/
instance instSMulCenter : SMul (Subalgebra.center R A) (continuousDerivationLieAlgebra R A) where
  smul z D := ⟨z • (D : derivationLieAlgebra R A),
    mem_continuousDerivationLieAlgebra.mpr
      (derivationLieAlgebra.continuous_center_smul z (continuous D))⟩

@[simp]
theorem coe_center_smul (z : Subalgebra.center R A) (D : continuousDerivationLieAlgebra R A) :
    (z • D : continuousDerivationLieAlgebra R A).val = z • (D : derivationLieAlgebra R A) :=
  (rfl)

/-- Continuous derivations form a module over the center. -/
instance instModuleCenter : Module (Subalgebra.center R A) (continuousDerivationLieAlgebra R A) :=
  Function.Injective.module _
    (continuousDerivationLieAlgebra R A).toSubmodule.subtype.toAddMonoidHom
    Subtype.val_injective (fun _ _ => rfl)

/-- The central multiple of an inner derivation is represented by the central multiple of its
actual defining element, rather than merely a limit of inner derivations. -/
@[simp]
theorem center_smul_innerDerivation (z : Subalgebra.center R A) (b : A) :
    z • continuousInnerDerivation R b = continuousInnerDerivation R ((z : A) * b) := by
  apply Subtype.ext
  simp

/-- The actual inner image is stable under central multiplication. -/
theorem center_smul_mem_innerDerivation_idealRange (z : Subalgebra.center R A)
    {D : continuousDerivationLieAlgebra R A}
    (hD : D ∈ (continuousInnerDerivation R :
      A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange) :
    z • D ∈ (continuousInnerDerivation R :
      A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange := by
  obtain ⟨b, rfl⟩ := mem_continuousInnerDerivation_idealRange_iff.mp hD
  exact mem_continuousInnerDerivation_idealRange_iff.mpr
    ⟨(z : A) * b, (center_smul_innerDerivation z b).symm⟩

/-- The Lie–Rinehart identity for continuous derivations and central coefficients. -/
theorem lie_center_smul (D E : continuousDerivationLieAlgebra R A)
    (z : Subalgebra.center R A) :
    ⁅D, z • E⁆ = z • ⁅D, E⁆ +
      derivationLieAlgebra.restrictCenter R A (D : derivationLieAlgebra R A) z • E :=
  Subtype.ext (derivationLieAlgebra.lie_center_smul _ _ _)

/-- Central multiplication is continuous in the pointwise topology on derivations. -/
instance instContinuousConstSMulCenter :
    ContinuousConstSMul (Subalgebra.center R A) (continuousDerivationLieAlgebra R A) where
  continuous_const_smul z := continuous_iff.mpr fun a => by
    simpa only [coe_center_smul, derivationLieAlgebra.center_smul_apply, Function.comp_def] using
      (continuous_const_mul (z : A)).comp (continuous_apply a)

end continuousDerivationLieAlgebra

namespace ContinuousOuterDerivation

/-- Central multiplication on outer classes is well defined because the actual inner image
is stable under the center action. -/
instance instSMulCenter : SMul (Subalgebra.center R A) (ContinuousOuterDerivation R A) where
  smul z := Quotient.map' (z • ·) fun D E h => by
    apply (Submodule.quotientRel_def _).mpr
    rw [← smul_sub]
    exact continuousDerivationLieAlgebra.center_smul_mem_innerDerivation_idealRange z
      ((Submodule.quotientRel_def _).mp h)

/-- The quotient map respects central multiplication. -/
@[simp↓]
theorem mkQ_center_smul (z : Subalgebra.center R A) (D : continuousDerivationLieAlgebra R A) :
    (LieIdeal.mkQ _ (z • D) : ContinuousOuterDerivation R A) = z • LieIdeal.mkQ _ D :=
  (rfl)

/-- The existing outer-derivation quotient is a module over the center. -/
instance instModuleCenter : Module (Subalgebra.center R A) (ContinuousOuterDerivation R A) :=
  Function.Surjective.module _
    ((continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange.mkQ
      ).toLinearMap.toAddMonoidHom
    (LieIdeal.surjective_mkQ _) mkQ_center_smul

/-- The anchor on outer derivations is linear over the center. -/
@[simp]
theorem restrictCenter_center_smul (z : Subalgebra.center R A)
    (D : ContinuousOuterDerivation R A) :
    restrictCenter R A (z • D) = z • restrictCenter R A D := by
  obtain ⟨D, rfl⟩ := LieIdeal.surjective_mkQ
    (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange D
  rw [← mkQ_center_smul, restrictCenter_mkQ, restrictCenter_mkQ]
  exact derivationLieAlgebra.restrictCenter_center_smul z _

/-- The Lie–Rinehart identity descends to the quotient by the actual inner image. -/
theorem lie_center_smul (D E : ContinuousOuterDerivation R A) (z : Subalgebra.center R A) :
    ⁅D, z • E⁆ = z • ⁅D, E⁆ + restrictCenter R A D z • E := by
  obtain ⟨D, rfl⟩ := LieIdeal.surjective_mkQ
    (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange D
  obtain ⟨E, rfl⟩ := LieIdeal.surjective_mkQ
    (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange E
  simpa only [map_add, mkQ_center_smul, LieHom.map_lie, restrictCenter_mkQ] using
    congrArg (LieIdeal.mkQ (continuousInnerDerivation R :
      A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange)
      (continuousDerivationLieAlgebra.lie_center_smul D E z)

/-- Multiplication by each fixed central element is continuous on outer derivations with the
quotient topology. No separatedness of the quotient is required. -/
instance instContinuousConstSMulCenter :
    ContinuousConstSMul (Subalgebra.center R A) (ContinuousOuterDerivation R A) where
  continuous_const_smul z := by
    apply (LieIdeal.isOpenQuotientMap_mkQ
      (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange
      ).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, ← mkQ_center_smul] using
      (LieIdeal.isOpenQuotientMap_mkQ
        (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange
        ).continuous.comp (continuous_const_smul z)

end ContinuousOuterDerivation

end TauCeti
