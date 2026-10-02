/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.Algebra.Module.Equiv.Opposite
public import TauCeti.Algebra.Ring.Opposite
import Mathlib.LinearAlgebra.StdBasis

/-!
# Evaluation into the opposite double dual

For a left module `P` over a possibly noncommutative ring `A`, its dual `Hom_A(P, A)`
is a right `A`-module. Dualizing on that side, with values in the right regular module `A`,
returns a left module. Evaluation identifies a finitely generated projective module with
this double dual.

`opDualCodomainEquiv` transports right-linear functionals from the regular codomain `A`
to `Aᵐᵒᵖ`, semilinearly along `A ≃+* Aᵐᵒᵖᵐᵒᵖ`. It commutes with precomposition and
carries its range onto the range computed using the opposite codomain. This compares
evaluation with constructions that use the opposite ring itself as the second dual's codomain.

`unopDualEvalEquiv` gives the right-module version with both duals taking values in `A`,
so that its scalars stay in `Aᵐᵒᵖ` rather than passing to a triple opposite.

This is the reflexivity used when dualizing a projective presentation twice in the
Auslander--Bridger transpose construction. Unlike `Module.evalEquiv`, the evaluation here
changes sides and does not require commutativity of the coefficient ring.
-/

public section

namespace TauCeti

section Codomain

variable (A N : Type*) [Semiring A] [AddCommMonoid N] [Module Aᵐᵒᵖ N]

/-- Changing the codomain of a right-linear functional from `A` to `Aᵐᵒᵖ` identifies
the two dual conventions. Scalars change from `A` to its double opposite. -/
def opDualCodomainEquiv :
    (N →ₗ[Aᵐᵒᵖ] A) ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A)] Module.Dual Aᵐᵒᵖ N where
  __ := (LinearEquiv.refl Aᵐᵒᵖ N).arrowCongrAddEquiv (MulOpposite.opLinearEquiv Aᵐᵒᵖ)
  map_smul' _ _ := by ext; rfl

/-- Codomain transport applies `op` to the value of a functional. -/
@[simp]
theorem opDualCodomainEquiv_apply (F : N →ₗ[Aᵐᵒᵖ] A) (x : N) :
    opDualCodomainEquiv A N F x = MulOpposite.op (F x) := (rfl)

/-- Inverse codomain transport applies `unop` to the value of a functional. -/
@[simp]
theorem opDualCodomainEquiv_symm_apply (F : Module.Dual Aᵐᵒᵖ N) (x : N) :
    (opDualCodomainEquiv A N).symm F x = MulOpposite.unop (F x) := (rfl)

variable {N} {N' : Type*} [AddCommMonoid N'] [Module Aᵐᵒᵖ N']

/-- Codomain transport commutes with precomposition. -/
@[simp]
theorem opDualCodomainEquiv_lcomp (f : N →ₗ[Aᵐᵒᵖ] N') (F : N' →ₗ[Aᵐᵒᵖ] A) :
    opDualCodomainEquiv A N (f.lcomp A A F) =
      f.lcomp Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ (opDualCodomainEquiv A N' F) := by
  ext x
  simp

/-- Codomain transport carries the image of precomposition onto the image of precomposition
with the opposite regular codomain. -/
theorem map_range_opDualCodomainEquiv (f : N →ₗ[Aᵐᵒᵖ] N') :
    (LinearMap.range (f.lcomp A A)).map (opDualCodomainEquiv A N).toLinearMap =
      LinearMap.range (f.lcomp Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ) := by
  have hsquare : (opDualCodomainEquiv A N).toLinearMap ∘ₛₗ f.lcomp A A =
      f.lcomp Aᵐᵒᵖᵐᵒᵖ Aᵐᵒᵖ ∘ₛₗ (opDualCodomainEquiv A N').toLinearMap :=
    LinearMap.ext (opDualCodomainEquiv_lcomp A f)
  rw [← LinearMap.range_comp, hsquare, LinearEquiv.range_comp]

end Codomain

variable (A P : Type*) [Semiring A] [AddCommMonoid P] [Module A P]

/-- Evaluation into the double dual, changing from left to right modules between the two
dualizations. The second dual takes values in the right regular module `A`. -/
def opDualEval : P →ₗ[A] (Module.Dual A P →ₗ[Aᵐᵒᵖ] A) :=
  LinearMap.flip (LinearMap.id : Module.Dual A P →ₗ[Aᵐᵒᵖ] Module.Dual A P)

/-- Evaluation is application of a functional to a vector. -/
@[simp]
theorem opDualEval_apply (x : P) (φ : Module.Dual A P) : opDualEval A P x φ = φ x := (rfl)

variable {A P} {Q : Type*} [AddCommMonoid Q] [Module A Q]

variable (A)

/-- Evaluation commutes with applying a linear map and dualizing it twice. -/
theorem opDualEval_naturality (f : P →ₗ[A] Q) (x : P) :
    opDualEval A Q (f x) =
      (f.lcomp Aᵐᵒᵖ A).lcomp A A (opDualEval A P x) := by
  ext φ
  simp

variable (P)

/-- **A finitely generated projective module is its opposite double dual.** Evaluation is
bijective, with no commutativity hypothesis on the semiring. -/
theorem opDualEval_bijective [Module.Finite A P] [Module.Projective A P] :
    Function.Bijective (opDualEval A P) := by
  classical
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  let b : Fin n → P := fun i => f (Pi.single i 1)
  let φ : Fin n → Module.Dual A P := fun i => (LinearMap.proj i).comp g
  have hsum (x : P) : ∑ i, φ i x • b i = x := by
    have h := (Pi.basisFun A (Fin n)).sum_repr (g x)
    have hf := congrArg f h
    simpa [b, φ, map_sum, map_smul] using
      hf.trans (LinearMap.congr_fun hfg x)
  have hdual (ψ : Module.Dual A P) : ∑ i, MulOpposite.op (ψ (b i)) • φ i = ψ := by
    ext x
    have h := congrArg ψ (hsum x)
    simpa [map_sum, map_smul, MulOpposite.smul_eq_mul_unop] using h
  constructor
  · intro x y h
    calc x = ∑ i, φ i x • b i := (hsum x).symm
      _ = ∑ i, φ i y • b i := by
        congr 1
        ext i
        exact congrArg (fun a => a • b i) (LinearMap.congr_fun h (φ i))
      _ = y := hsum y
  · intro F
    refine ⟨∑ i, F (φ i) • b i, ?_⟩
    ext ψ
    have h := congrArg F (hdual ψ)
    simpa [map_sum, map_smul, MulOpposite.smul_eq_mul_unop] using h

/-- The canonical equivalence of a finitely generated projective left module with the dual
of its right dual. -/
noncomputable def opDualEvalEquiv [Module.Finite A P] [Module.Projective A P] :
    P ≃ₗ[A] (Module.Dual A P →ₗ[Aᵐᵒᵖ] A) :=
  LinearEquiv.ofBijective (opDualEval A P) (opDualEval_bijective A P)

/-- The underlying map of the double-dual equivalence is evaluation. -/
@[simp]
theorem opDualEvalEquiv_toLinearMap [Module.Finite A P] [Module.Projective A P] :
    (opDualEvalEquiv A P).toLinearMap = opDualEval A P := (rfl)

/-- The double-dual equivalence is evaluation. -/
@[simp]
theorem opDualEvalEquiv_apply [Module.Finite A P] [Module.Projective A P]
    (x : P) (φ : Module.Dual A P) : opDualEvalEquiv A P x φ = φ x := (rfl)

/-- The inverse double-dual equivalence recovers the vector represented by a functional. -/
@[simp]
theorem apply_opDualEvalEquiv_symm [Module.Finite A P] [Module.Projective A P]
    (F : Module.Dual A P →ₗ[Aᵐᵒᵖ] A) (φ : Module.Dual A P) :
    φ ((opDualEvalEquiv A P).symm F) = F φ :=
  LinearMap.congr_fun ((opDualEvalEquiv A P).apply_symm_apply F) φ

/-- Taking opposite duals identifies maps into a finite projective module with maps out of
its opposite dual. The source module need not be finite or projective. -/
theorem opDual_lcomp_bijective [Module.Finite A P] [Module.Projective A P] :
    Function.Bijective (fun f : Q →ₗ[A] P ↦ f.lcomp Aᵐᵒᵖ A) := by
  constructor
  · intro f g h
    ext x
    apply (opDualEval_bijective A P).injective
    ext φ
    exact LinearMap.congr_fun (LinearMap.congr_fun h φ) x
  · intro h
    refine ⟨(opDualEvalEquiv A P).symm.toLinearMap ∘ₗ h.lcomp A A ∘ₗ
      opDualEval A Q, ?_⟩
    ext φ x
    simp [LinearMap.lcomp_apply']

variable {P}

/-- Evaluation carries the image of a map onto the image of its opposite double dual when
the source is finitely generated and projective. No hypothesis on the target is needed. -/
theorem map_range_opDualEval [Module.Finite A P] [Module.Projective A P]
    (f : P →ₗ[A] Q) :
    (LinearMap.range f).map (opDualEval A Q) =
      LinearMap.range ((f.lcomp Aᵐᵒᵖ A).lcomp A A) := by
  rw [← LinearMap.range_comp]
  have hsquare : (opDualEval A Q).comp f =
      ((f.lcomp Aᵐᵒᵖ A).lcomp A A).comp (opDualEval A P) := by
    ext x φ
    simp
  rw [hsquare, LinearMap.range_comp]
  simp [LinearMap.range_eq_top.mpr (opDualEval_bijective A P).surjective]

section RightEvaluation

variable (A N : Type*) [Semiring A] [AddCommMonoid N] [Module Aᵐᵒᵖ N]
  [Module.Finite Aᵐᵒᵖ N] [Module.Projective Aᵐᵒᵖ N]

/-- Evaluation identifies a finite projective right module with the left dual of its
right-linear dual taking values in `A`. Both sides have their original right `A`-action. -/
noncomputable def unopDualEvalEquiv :
    N ≃ₗ[Aᵐᵒᵖ] Module.Dual A (N →ₗ[Aᵐᵒᵖ] A) := by
  let e := (opDualCodomainEquiv A N).symm
  let c : Aᵐᵒᵖ ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A).symm] A :=
    { __ := MulOpposite.opAddEquiv.symm, map_smul' := fun _ _ => rfl }
  let t : (Module.Dual Aᵐᵒᵖ N →ₗ[Aᵐᵒᵖᵐᵒᵖ] Aᵐᵒᵖ) ≃ₗ[Aᵐᵒᵖ]
      Module.Dual A (N →ₗ[Aᵐᵒᵖ] A) :=
    { __ := e.arrowCongrAddEquiv c,
      map_smul' := by intros; ext; simp [LinearEquiv.arrowCongrAddEquiv, c] }
  exact (opDualEvalEquiv Aᵐᵒᵖ N).trans t

/-- Right-module bidual evaluation applies a functional to the vector. -/
@[simp]
theorem unopDualEvalEquiv_apply (x : N) (φ : N →ₗ[Aᵐᵒᵖ] A) :
    unopDualEvalEquiv A N x φ = φ x := by
  simp [unopDualEvalEquiv, LinearEquiv.arrowCongrAddEquiv, opDualEvalEquiv]

/-- A functional applied to inverse right-module bidual evaluation recovers its value. -/
@[simp]
theorem apply_unopDualEvalEquiv_symm
    (F : Module.Dual A (N →ₗ[Aᵐᵒᵖ] A)) (φ : N →ₗ[Aᵐᵒᵖ] A) :
    φ ((unopDualEvalEquiv A N).symm F) = F φ := by
  simpa only [unopDualEvalEquiv_apply] using
    LinearMap.congr_fun ((unopDualEvalEquiv A N).apply_symm_apply F) φ

variable {N} {N' : Type*} [AddCommMonoid N'] [Module Aᵐᵒᵖ N']
  [Module.Finite Aᵐᵒᵖ N'] [Module.Projective Aᵐᵒᵖ N']

/-- Right-module bidual evaluation commutes with a linear map and its double dual. -/
theorem unopDualEvalEquiv_naturality (f : N →ₗ[Aᵐᵒᵖ] N') (x : N) :
    unopDualEvalEquiv A N' (f x) =
      (f.lcomp A A).lcomp Aᵐᵒᵖ A (unopDualEvalEquiv A N x) := by
  ext φ
  simp

end RightEvaluation

end TauCeti
