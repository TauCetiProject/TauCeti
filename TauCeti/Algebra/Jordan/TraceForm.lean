/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.Jordan.Derivation
public import TauCeti.Algebra.Lie.Derivation.Trace

/-!
# The Jordan trace form

The bilinear form `TauCeti.Jordan.traceForm R a b = tr(L_{a * b})` is symmetric and associative
on a commutative Jordan algebra when `2` is invertible. Every derivation is skew for this form.
The trace functional here is unnormalized: on a finite free unital algebra it takes the unit
to the dimension, rather than the Jordan rank. No positivity or formal reality is asserted.

The construction and statements are adapted from `EuclideanJordan/TraceForm.lean` in
Bryan Ehrlich's euclidean-jordan at revision a83407e4dbf73c77c31a2291c02f20b37a5ebbaf.
We use the existing inner derivation theorem to prove associativity: `tr(L_{D a}) = 0`,
applied to `D = [L_c, L_a]`, identifies the two bracketings. This replaces the source's
quadrilinear expansion. Finite dimensionality is unnecessary because Mathlib's trace is total
and vanishes when the module has no finite basis.
-/

noncomputable section

public section

namespace TauCeti

namespace Jordan

variable (R : Type*) {A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- The unnormalized trace functional `a ↦ tr(L_a)` of a non-associative algebra. -/
def mulTrace : A →ₗ[R] R := (LinearMap.trace R A).comp (LinearMap.mul R A)

@[simp]
theorem mulTrace_apply (a : A) : mulTrace R a = LinearMap.trace R A (LinearMap.mulLeft R a) :=
  (rfl)

/-- The unnormalized Jordan trace form `(a, b) ↦ tr(L_{a * b})`. -/
def traceForm : A →ₗ[R] A →ₗ[R] R :=
  (LinearMap.mul R A).compr₂ (mulTrace R)

@[simp]
theorem traceForm_apply (a b : A) : traceForm R a b = mulTrace R (a * b) := (rfl)

/-- Every derivation is skew for the trace form, by the Leibniz rule and cyclicity of trace. -/
theorem traceForm_derivation (D : derivationLieAlgebra R A) (a b : A) :
    traceForm R ((D : Module.End R A) a) b +
      traceForm R a ((D : Module.End R A) b) = 0 := by
  rw [traceForm_apply, traceForm_apply, ← map_add, ← derivationLieAlgebra.leibniz]
  exact derivationLieAlgebra.trace_mulLeft_apply_eq_zero D (a * b)

section Commutative

variable {J : Type*} [NonUnitalNonAssocCommRing J] [Module R J]
  [SMulCommClass R J J] [IsScalarTower R J J]

/-- The Jordan trace form is symmetric. -/
theorem traceForm_comm (a b : J) : traceForm R a b = traceForm R b a := by
  simp only [traceForm_apply, mul_comm]

variable [IsCommJordan J] [Invertible (2 : R)]

/-- The trace functional is associative, since inner derivations have trace-zero values. -/
theorem mulTrace_assoc (a b c : J) : mulTrace R ((a * b) * c) = mulTrace R (a * (b * c)) := by
  have h := derivationLieAlgebra.trace_mulLeft_apply_eq_zero (jordanInnerDerivation R c a) b
  rw [← mulTrace_apply] at h
  rw [jordanInnerDerivation_apply, map_sub, mul_comm c (a * b), mul_comm c b] at h
  exact sub_eq_zero.mp h

/-- The Jordan trace form is associative: left multiplication is self-adjoint for it. -/
theorem traceForm_assoc (a b c : J) : traceForm R (a * b) c = traceForm R b (a * c) := by
  simp only [traceForm_apply]
  rw [mul_comm a b, mulTrace_assoc]

end Commutative

end Jordan

end TauCeti
