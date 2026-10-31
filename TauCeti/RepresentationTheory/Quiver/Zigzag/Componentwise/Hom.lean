/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Trace
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Projective

/-!
# Shifted projective homomorphisms and the componentwise trace

Evaluation at the vertex idempotent identifies graded maps `P_i ⟶ P_j{s}` with the degree
`-s` part of the corner `e_i Z e_j`. The inverse is right multiplication by the corner vector.
Composition, with the target shift applied to the second map, corresponds to multiplication of
these vectors in the public componentwise zigzag algebra.

The corner trace pairing therefore pairs `Hom(P_i, P_j{s})` perfectly with
`Hom(P_j, P_i{-2-s})`. Its value is the trace of the composed underlying module map evaluated
at the vertex generator. All shifts here are internal grading shifts.

The dictionary uses the existing graded idempotent evaluation equivalence
`TauCeti.GradedModuleCat.ofIdealSpanSingletonHomEquiv` and its corner-piece calculation.
Perfectness is transported from the signed graded corner pairing using Mathlib's
`LinearMap.IsPerfPair.compl₁₂`; the induced dual equivalence is `LinearMap.toPerfPair`.

## References

* Huerfano--Khovanov, *A category for the adjoint representation*, Sections 3 and 4.6.
* Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section
noncomputable section

namespace TauCeti

open CategoryTheory
open scoped Pointwise

universe u w

variable (k : Type w) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "A" => zigzagAlgebraIntegerGrade k G
local notation "P" => zigzagAlgebraGradedProjective k G
local notation "C" => fun (i j : V) (d : ℤ) ↦ cornerSubmodule k (e i) (e j) ⊓ A d
local notation "H" => fun (i j : V) (s : ℤ) ↦ P i ⟶ GradedModuleCat.shiftObj (P j) s

private theorem map_shifted_projective_zero (i j : V) (s : ℤ) :
    (e i • ((P j).shiftObj s).grading.piece 0).map
        ((Ideal.span {e j} : Ideal Z).subtype.restrictScalars k) = C i j (-s) := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  have hpiece : ((P j).shiftObj s).grading.piece 0 = (P j).grading.piece (-s) := by
    ext x
    rw [GradedModuleCat.mem_shiftObj_piece_iff, zero_sub]
  rw [hpiece]
  exact GradedModuleCat.map_subtype_smul_ofIdeal_span_singleton_piece
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)
    (isIdempotentElem_zigzagAlgebraBasis_inl k G j)
    (isHomogeneous_span_zigzagAlgebraBasis_inl k G j) (-s)

/-- Evaluation at the vertex generator identifies maps into internal shift `s` with the signed
degree-`(-s)` corner of the public componentwise algebra. -/
def zigzagAlgebraGradedProjectiveHomEquivCorner (i j : V) (s : ℤ) :
    H i j s ≃ₗ[k] ↥(C i j (-s)) :=
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  (GradedModuleCat.ofIdealSpanSingletonHomEquiv
    (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
    (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)
    (isHomogeneous_span_zigzagAlgebraBasis_inl k G i) ((P j).shiftObj s)).trans
    ((Submodule.equivMapOfInjective
      ((Ideal.span {e j} : Ideal Z).subtype.restrictScalars k)
      (fun _ _ h ↦ Subtype.ext h) _).trans
      (LinearEquiv.ofEq _ _ (map_shifted_projective_zero k G i j s)))

/-- The corner vector of a shifted graded map is its value at the source vertex generator. -/
@[simp]
theorem coe_zigzagAlgebraGradedProjectiveHomEquivCorner_apply (i j : V) (s : ℤ)
    (f : H i j s) :
    (zigzagAlgebraGradedProjectiveHomEquivCorner k G i j s f : Z) =
      (f.hom (spanSingletonGenerator (e i)) : Z) := by
  let _ := zigzagAlgebraIntegerGradedAlgebra k G
  -- Keep the restricted-scalar grading intact while composing the two ambient computations.
  exact (Submodule.coe_equivMapOfInjective_apply
    ((Ideal.span {e j} : Ideal Z).subtype.restrictScalars k) (fun _ _ h ↦ Subtype.ext h)
    (e i • ((P j).shiftObj s).grading.piece 0)
    (GradedModuleCat.ofIdealSpanSingletonHomEquiv
      (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
      (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)
      (isHomogeneous_span_zigzagAlgebraBasis_inl k G i) ((P j).shiftObj s) f)).trans
    (congrArg (fun x : (P j).shiftObj s ↦ (x : Z))
      (GradedModuleCat.coe_ofIdealSpanSingletonHomEquiv_apply
        (isIdempotentElem_zigzagAlgebraBasis_inl k G i)
        (zigzagAlgebraBasis_inl_mem_integerGrade_zero k G i)
        (isHomogeneous_span_zigzagAlgebraBasis_inl k G i) f))

/-- The inverse corner dictionary acts by right multiplication on the vertex ideal. -/
@[simp]
theorem coe_zigzagAlgebraGradedProjectiveHomEquivCorner_symm_apply (i j : V) (s : ℤ)
    (x : C i j (-s)) (a : P i) :
    (((zigzagAlgebraGradedProjectiveHomEquivCorner k G i j s).symm x).hom a : Z) =
      (a : Z) * (x : Z) := by
  rw [coe_apply_eq_mul_apply_generator (isIdempotentElem_zigzagAlgebraBasis_inl k G i)]
  have h := coe_zigzagAlgebraGradedProjectiveHomEquivCorner_apply k G i j s
    ((zigzagAlgebraGradedProjectiveHomEquivCorner k G i j s).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h]

/-- Shifted composition corresponds to multiplication of corner vectors in the same order. -/
theorem coe_zigzagAlgebraGradedProjectiveHomEquivCorner_comp (i j l : V) (s t : ℤ)
    (f : H i j s) (g : H j l t) :
    (zigzagAlgebraGradedProjectiveHomEquivCorner k G i l (t + s)
        (f ≫ (GradedModuleCat.shiftFunctor s).map g ≫
          (GradedModuleCat.shiftFunctorAddIso A t s).hom.app (P l)) : Z) =
      (zigzagAlgebraGradedProjectiveHomEquivCorner k G i j s f : Z) *
        (zigzagAlgebraGradedProjectiveHomEquivCorner k G j l t g : Z) := by
  simp only [coe_zigzagAlgebraGradedProjectiveHomEquivCorner_apply, GradedModuleCat.hom_comp,
    GradedModuleCat.hom_shiftFunctor_map, GradedModuleCat.hom_shiftFunctorAddIso_hom_app,
    LinearMap.comp_apply, LinearMap.id_apply]
  exact coe_apply_eq_mul_apply_generator (isIdempotentElem_zigzagAlgebraBasis_inl k G j)
    g.hom (f.hom (spanSingletonGenerator (e i)))

private def reverseHomEquivCorner (i j : V) (s : ℤ) :
    H j i (-2 - s) ≃ₗ[k] ↥(C j i (2 - -s)) :=
  (zigzagAlgebraGradedProjectiveHomEquivCorner k G j i (-2 - s)).trans
    (LinearEquiv.ofEq _ _ (by congr 1; omega))

/-- The componentwise trace pairs shifted graded projective maps in complementary internal
shifts `s` and `-2-s`. -/
def zigzagAlgebraGradedProjectiveHomTracePairing (i j : V) (s : ℤ) :
    H i j s →ₗ[k] H j i (-2 - s) →ₗ[k] k :=
  (zigzagAlgebraGradedCornerTracePairing k G i j (-s)).compl₁₂
    (zigzagAlgebraGradedProjectiveHomEquivCorner k G i j s) (reverseHomEquivCorner k G i j s)

/-- The Hom pairing is the trace of the product of the two generator images. -/
@[simp]
theorem zigzagAlgebraGradedProjectiveHomTracePairing_apply (i j : V) (s : ℤ)
    (f : H i j s) (g : H j i (-2 - s)) :
    zigzagAlgebraGradedProjectiveHomTracePairing k G i j s f g =
      zigzagAlgebraTrace k G
        ((f.hom (spanSingletonGenerator (e i)) : Z) *
          (g.hom (spanSingletonGenerator (e j)) : Z)) := by
  rw [zigzagAlgebraGradedProjectiveHomTracePairing, LinearMap.compl₁₂_apply,
    zigzagAlgebraGradedCornerTracePairing_apply]
  simp only [LinearEquiv.coe_coe, reverseHomEquivCorner, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, coe_zigzagAlgebraGradedProjectiveHomEquivCorner_apply]

/-- The same pairing evaluates the shifted composite at the source generator and takes its
trace. The composite has internal target shift `(-2-s)+s = -2`. -/
theorem zigzagAlgebraGradedProjectiveHomTracePairing_eq_trace_comp (i j : V) (s : ℤ)
    (f : H i j s) (g : H j i (-2 - s)) :
    zigzagAlgebraGradedProjectiveHomTracePairing k G i j s f g =
      zigzagAlgebraTrace k G
        ((((f ≫ (GradedModuleCat.shiftFunctor s).map g ≫
          (GradedModuleCat.shiftFunctorAddIso A (-2 - s) s).hom.app (P i)) :
            H i i ((-2 - s) + s)).hom
            (spanSingletonGenerator (e i))) : Z) := by
  rw [zigzagAlgebraGradedProjectiveHomTracePairing_apply]
  congr 1
  symm
  simpa only [coe_zigzagAlgebraGradedProjectiveHomEquivCorner_apply] using
    coe_zigzagAlgebraGradedProjectiveHomEquivCorner_comp k G i j i s (-2 - s) f g

/-- Complementary shifted Hom spaces of actual componentwise vertex projectives are in perfect
trace pairing over every commutative coefficient ring. -/
instance zigzagAlgebraGradedProjectiveHomTracePairing_isPerfPair (i j : V) (s : ℤ) :
    (zigzagAlgebraGradedProjectiveHomTracePairing k G i j s).IsPerfPair := by
  dsimp only [zigzagAlgebraGradedProjectiveHomTracePairing]
  infer_instance

end TauCeti
