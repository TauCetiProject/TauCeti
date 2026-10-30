/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Basic
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.UnitFiber

/-!
# The PBW Rees fibre at one

Specializing the PBW deformation parameter to one recovers the universal enveloping algebra.
We give both the quotient by the central two-sided ideal `(t - 1)` and the actual tensor
base change along evaluation `R[t] → R` at one. The comparison sends `j(x)` to `ι(x)`;
its inverse sends `ι(x)` to the specialized Rees generator.

These comparisons require neither freeness of the Lie algebra nor a characteristic hypothesis.
They use the exhaustive PBW filtration.

## References

* J. Dixmier, *Enveloping Algebras*, for the Rees construction of a filtered enveloping algebra.
-/

public section

open Polynomial
open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- The quotient of the PBW Rees algebra by `t - 1` is the enveloping algebra. -/
noncomputable def quotientReesParameterSubOneEquiv :
    (reesAlgebra R L ⧸ (Ideal.span {reesParameter R L - 1})) ≃ₐ[R] U :=
  (Ideal.quotientEquivAlgOfEq R (by rw [map_one])).trans
    (coeffSubalgebra.quotientSpanXSubAlgebraMapEquiv (pbwFiltration R L)
      (one_mem_pbwFiltration R L 1) (pbwFiltration_mono R L) (iSup_pbwFiltration_eq_top R L)
      isUnit_one)

/-- The quotient comparison evaluates any representative at parameter one. -/
@[simp]
theorem quotientReesParameterSubOneEquiv_mk (p : reesAlgebra R L) :
    quotientReesParameterSubOneEquiv R L (Ideal.Quotient.mk _ p) =
      coeffSubalgebra.evalOne (pbwFiltration R L) p := by
  simp [quotientReesParameterSubOneEquiv, coeffSubalgebra.evalOne_eq_eval]

/-- The inverse quotient comparison takes an enveloping generator to the Rees generator class. -/
-- Rewrite before the simplifier expands the canonical enveloping generator.
@[simp↓]
theorem quotientReesParameterSubOneEquiv_symm_ι (x : L) :
    (quotientReesParameterSubOneEquiv R L).symm (_root_.UniversalEnvelopingAlgebra.ι R x) =
      Ideal.Quotient.mk _ (reesGenerator R L x) := by
  rw [AlgEquiv.symm_apply_eq, quotientReesParameterSubOneEquiv_mk, evalOne_reesGenerator]

/-- Tensor base change of the PBW Rees algebra at one is the enveloping algebra.
The polynomial parameter acts on the left tensor factor by evaluation at one. -/
noncomputable def reesOneFiberEquiv :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    (R ⊗[R[X]] reesAlgebra R L) ≃ₐ[R] U :=
  coeffSubalgebra.baseChangeEvalEquiv (pbwFiltration R L) (one_mem_pbwFiltration R L 1)
    (pbwFiltration_mono R L) (iSup_pbwFiltration_eq_top R L) isUnit_one

/-- The fibre comparison evaluates the Rees factor and multiplies by the scalar factor. -/
@[simp]
theorem reesOneFiberEquiv_tmul (r : R) (p : reesAlgebra R L) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    reesOneFiberEquiv R L (r ⊗ₜ[R[X]] p) =
      r • coeffSubalgebra.evalOne (pbwFiltration R L) p := by
  let := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
  rw [coeffSubalgebra.evalOne_eq_eval]
  exact coeffSubalgebra.baseChangeEvalEquiv_tmul _ _ _ _ _ r p

/-- The inverse fibre comparison takes an enveloping generator to the specialized Rees generator. -/
@[simp↓]
theorem reesOneFiberEquiv_symm_ι (x : L) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    (reesOneFiberEquiv R L).symm (_root_.UniversalEnvelopingAlgebra.ι R x) =
      1 ⊗ₜ[R[X]] reesGenerator R L x := by
  let := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
  rw [AlgEquiv.symm_apply_eq, reesOneFiberEquiv_tmul, one_smul, evalOne_reesGenerator]

end TauCeti.UniversalEnvelopingAlgebra
