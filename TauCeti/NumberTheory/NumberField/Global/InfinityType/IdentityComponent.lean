/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.InfinityType.Basic

/-!
# Infinity types on the identity component

The identity component of the archimedean units does not detect signs at real places. Thus two
continuous infinity types agree there exactly when they differ by a finite-order infinity type.
In particular, algebraicity on the identity component allows a real sign twist; it is weaker
than equality with the continuous type of integer embedding exponents. This comparison is the
archimedean criterion used for algebraic Hecke characters.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields

namespace ContinuousInfinityType

variable {K : Type*} [Field K]

/-- Two infinity types agree on the identity component of the archimedean units when their
modulus exponents and complex angular frequencies agree. Real sign parities are unrestricted. -/
def AgreesOnIdentityComponent (t u : ContinuousInfinityType K) : Prop :=
  t.realExponent = u.realExponent ∧ t.complexExponent = u.complexExponent ∧
    t.complexAngularFrequency = u.complexAngularFrequency

/-- Agreement on the identity component means equality of the two modulus exponents and the
complex angular frequency. -/
theorem agreesOnIdentityComponent_iff (t u : ContinuousInfinityType K) :
    t.AgreesOnIdentityComponent u ↔
      t.realExponent = u.realExponent ∧ t.complexExponent = u.complexExponent ∧
        t.complexAngularFrequency = u.complexAngularFrequency :=
  Iff.rfl

/-- Agreement on the identity component is equivalent to a finite-order sign twist. -/
theorem agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType
    (t u : ContinuousInfinityType K) :
    t.AgreesOnIdentityComponent u ↔
      ∃ ε : FiniteOrderInfinityType K, t = u + FiniteOrderInfinityType.toContinuous ε := by
  constructor
  · rintro ⟨hr, hc, hk⟩
    refine ⟨fun w ↦ t.realParity w - u.realParity w, ?_⟩
    apply ContinuousInfinityType.ext <;> funext w
    · simpa using congrFun hr w
    · simp
    · simpa using congrFun hc w
    · simpa using congrFun hk w
  · rintro ⟨ε, rfl⟩
    constructor
    · funext w
      simp
    constructor
    · funext w
      simp
    · funext w
      simp

/-- Algebraicity of archimedean parameters on the identity component: their restrictions
agree with the parameters of integer exponents at the embeddings into `ℂ`. -/
def IsAlgebraicOnIdentityComponent (t : ContinuousInfinityType K) : Prop :=
  ∃ n : AlgebraicInfinityType K, t.AgreesOnIdentityComponent
    (AlgebraicInfinityType.toContinuous n)

/-- Algebraicity on the identity component is witnessed by integer embedding exponents whose
continuous infinity type agrees there. -/
theorem isAlgebraicOnIdentityComponent_iff_exists_agreesOnIdentityComponent
    (t : ContinuousInfinityType K) :
    t.IsAlgebraicOnIdentityComponent ↔
      ∃ n : AlgebraicInfinityType K,
        t.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n) :=
  Iff.rfl

/-- An infinity type is algebraic on the identity component precisely when it is an algebraic
infinity type times a finite-order real sign type. -/
theorem isAlgebraicOnIdentityComponent_iff (t : ContinuousInfinityType K) :
    t.IsAlgebraicOnIdentityComponent ↔
      ∃ (n : AlgebraicInfinityType K) (ε : FiniteOrderInfinityType K),
        t = AlgebraicInfinityType.toContinuous n + FiniteOrderInfinityType.toContinuous ε := by
  simp only [IsAlgebraicOnIdentityComponent,
    agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType]

/-- The infinity type attached to integer embedding exponents is algebraic on the identity
component. -/
@[simp]
theorem isAlgebraicOnIdentityComponent_toContinuous (n : AlgebraicInfinityType K) :
    (AlgebraicInfinityType.toContinuous n).IsAlgebraicOnIdentityComponent := by
  exact ⟨n, rfl, rfl, rfl⟩

/-- A finite-order sign type is algebraic on the identity component, even if its parity differs
from that of the zero algebraic infinity type. -/
@[simp]
theorem isAlgebraicOnIdentityComponent_finiteOrder (ε : FiniteOrderInfinityType K) :
    (FiniteOrderInfinityType.toContinuous ε).IsAlgebraicOnIdentityComponent := by
  rw [isAlgebraicOnIdentityComponent_iff]
  exact ⟨0, ε, by simp⟩

end ContinuousInfinityType

end TauCeti.GlobalNumberFields
