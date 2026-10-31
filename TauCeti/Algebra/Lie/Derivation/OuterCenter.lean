/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Center
public import TauCeti.Algebra.Lie.Derivation.Continuous
public import TauCeti.Algebra.Lie.Quotient

/-!
# The action of continuous outer derivations on the center

Restriction of an associative-algebra derivation to the center kills inner derivations.
Consequently the continuous outer derivations act on the center by ordinary commutative
algebra derivations. This is the canonical action used to read the infinitesimal motion of a
central character from an outer class, without choosing its representative.

`ContinuousOuterDerivation.restrictCenter` is a Lie algebra homomorphism, so its action respects
commutators as well as addition and scalars. Each resulting derivation of the center is
continuous. For each central element, evaluation is also continuous in the outer class with
its quotient topology. No separation assumption on the quotient is needed: the construction
uses the actual image of inner derivations, not its closure.

The construction combines `derivationLieAlgebra.restrictCenter`, the quotient by the actual
inner image, and the universal property `LieIdeal.liftQ`.

## References

* N. Jacobson, *Lie Algebras* (1962), Chapter I, §2, for restriction to the center.
* E. Frenkel, *Langlands Correspondence for Loop Groups* (2007), for the action of outer
  derivations on central characters in the critical-level setting.
-/

public section

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousConstSMul R A]

open Topology

namespace continuousDerivationLieAlgebra

variable {R A}

/-- The restriction to the center of a continuous derivation is continuous. -/
@[fun_prop]
theorem continuous_restrictCenter (D : continuousDerivationLieAlgebra R A) :
    Continuous (derivationLieAlgebra.restrictCenter R A (D : derivationLieAlgebra R A)) := by
  apply IsInducing.subtypeVal.continuous_iff.mpr
  simpa only [Function.comp_def, derivationLieAlgebra.coe_restrictCenter_apply] using
    (continuous D).comp continuous_subtype_val

/-- Evaluation of the restricted derivation is continuous in the topology of pointwise
convergence on continuous derivations. -/
@[fun_prop]
theorem continuous_restrictCenter_apply (z : Subalgebra.center R A) :
    Continuous fun D : continuousDerivationLieAlgebra R A =>
      derivationLieAlgebra.restrictCenter R A (D : derivationLieAlgebra R A) z := by
  apply IsInducing.subtypeVal.continuous_iff.mpr
  simpa only [Function.comp_def, derivationLieAlgebra.coe_restrictCenter_apply] using
    continuous_apply (R := R) (z : A)

end continuousDerivationLieAlgebra

variable [SeparatelyContinuousMul A]

namespace ContinuousOuterDerivation

/-- Continuous outer derivations act on the center by ordinary derivations. Inner derivations
vanish on the center, so restriction descends through their actual image. -/
def restrictCenter : ContinuousOuterDerivation R A →ₗ⁅R⁆
    Derivation R (Subalgebra.center R A) (Subalgebra.center R A) :=
  (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange.liftQ
    ((derivationLieAlgebra.restrictCenter R A).comp
      (continuousDerivationLieAlgebra R A).incl) (by
      intro D hD
      obtain ⟨b, rfl⟩ := mem_continuousInnerDerivation_idealRange_iff.mp hD
      simpa only [LieHom.mem_ker, LieHom.comp_apply, LieSubalgebra.coe_incl,
        coe_continuousInnerDerivation] using
          derivationLieAlgebra.restrictCenter_innerDerivation (R := R) b)

variable {R A}

/-- Restricting an outer class to the center is restriction of any continuous representative. -/
@[simp↓]
theorem restrictCenter_mkQ (D : continuousDerivationLieAlgebra R A) :
    restrictCenter R A (LieIdeal.mkQ _ D) =
      derivationLieAlgebra.restrictCenter R A (D : derivationLieAlgebra R A) := by
  unfold restrictCenter
  exact LieHom.congr_fun (LieIdeal.liftQ_mkQ _ _ _) D

/-- The derivation of the center defined by an outer class is continuous. -/
@[fun_prop]
theorem continuous_restrictCenter (D : ContinuousOuterDerivation R A) :
    Continuous (restrictCenter R A D) := by
  obtain ⟨D, rfl⟩ := LieIdeal.surjective_mkQ
    (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange D
  rw [restrictCenter_mkQ]
  exact continuousDerivationLieAlgebra.continuous_restrictCenter D

/-- At each central element, the action depends continuously on the outer class. This uses
the quotient topology, not a Hausdorff quotient or the closure of the inner image. -/
@[fun_prop]
theorem continuous_restrictCenter_apply (z : Subalgebra.center R A) :
    Continuous fun D : ContinuousOuterDerivation R A => restrictCenter R A D z := by
  apply (LieIdeal.isOpenQuotientMap_mkQ
    (continuousInnerDerivation R : A →ₗ⁅R⁆ continuousDerivationLieAlgebra R A).idealRange
      ).isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, restrictCenter_mkQ] using
    continuousDerivationLieAlgebra.continuous_restrictCenter_apply (R := R) z

end ContinuousOuterDerivation

end TauCeti
