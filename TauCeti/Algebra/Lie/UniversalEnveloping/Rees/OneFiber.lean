/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Functoriality
public import TauCeti.RingTheory.GradedAlgebra.CoeffSubalgebra.UnitFiber

/-!
# The PBW Rees fibre at one

Specializing the PBW deformation parameter to one recovers the universal enveloping algebra.
We give both the quotient by the central two-sided ideal `(t - 1)` and the actual tensor
base change along evaluation `R[t] → R` at one. The comparison sends `j(x)` to `ι(x)`;
its inverse sends `ι(x)` to the specialized Rees generator.

These comparisons require neither freeness of the Lie algebra nor a characteristic hypothesis.
They use the exhaustive PBW filtration. They are natural with respect to Lie algebra
homomorphisms via `quotientReesParameterSubOneMap` and `reesMap`.

## References

* J. Dixmier, *Enveloping Algebras*, for the Rees construction of a filtered enveloping algebra.
-/

public section

open Polynomial
open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w x

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

section Functoriality

variable {L} {M : Type w} {N : Type x}
variable [LieRing M] [LieAlgebra R M]
variable [LieRing N] [LieAlgebra R N]

/-- The `R`-algebra map on `t = 1` Rees quotients induced by a Lie algebra homomorphism. -/
noncomputable def quotientReesParameterSubOneMap (f : L →ₗ⁅R⁆ M) :
    (reesAlgebra R L ⧸ Ideal.span {reesParameter R L - 1}) →ₐ[R]
      (reesAlgebra R M ⧸ Ideal.span {reesParameter R M - 1}) :=
  Ideal.quotientMapₐ (Ideal.span {reesParameter R M - 1}) ((reesMap R f).restrictScalars R) <|
    Ideal.span_le.mpr <| by
      rintro p (rfl : p = reesParameter R L - 1)
      simp

@[simp]
theorem quotientReesParameterSubOneMap_mk (f : L →ₗ⁅R⁆ M) (p : reesAlgebra R L) :
    quotientReesParameterSubOneMap R f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (reesMap R f p) :=
  (rfl)

@[simp]
theorem quotientReesParameterSubOneMap_id :
    quotientReesParameterSubOneMap R (LieHom.id : L →ₗ⁅R⁆ L) =
      AlgHom.id R (reesAlgebra R L ⧸ Ideal.span {reesParameter R L - 1}) := by
  ext q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

@[simp]
theorem quotientReesParameterSubOneMap_comp (f : L →ₗ⁅R⁆ M) (g : M →ₗ⁅R⁆ N) :
    quotientReesParameterSubOneMap R (g.comp f) =
      (quotientReesParameterSubOneMap R g).comp (quotientReesParameterSubOneMap R f) := by
  ext q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

@[simp]
theorem quotientReesParameterSubOneEquiv_map (f : L →ₗ⁅R⁆ M)
    (q : reesAlgebra R L ⧸ Ideal.span {reesParameter R L - 1}) :
    quotientReesParameterSubOneEquiv R M (quotientReesParameterSubOneMap R f q) =
      map R f (quotientReesParameterSubOneEquiv R L q) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [coeffSubalgebra.evalOne_eq_eval]

/-- Naturality of the tensor-product `t = 1` fibre `reesOneFiberEquiv`. -/
@[simp]
theorem reesOneFiberEquiv_map (f : L →ₗ⁅R⁆ M) :
    letI := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
    ∀ z : R ⊗[R[X]] reesAlgebra R L,
      reesOneFiberEquiv R M (Algebra.TensorProduct.map (AlgHom.id R R) (reesMap R f) z) =
        map R f (reesOneFiberEquiv R L z) := by
  let := Algebra.compHom R (Polynomial.evalRingHom (1 : R))
  intro z
  exact TensorProduct.inductionOn z
    (fun r p ↦ by simp [reesOneFiberEquiv_tmul, coeffSubalgebra.evalOne_eq_eval])
    (fun x y hx hy ↦ by simp [hx, hy])

end Functoriality

end TauCeti.UniversalEnvelopingAlgebra
