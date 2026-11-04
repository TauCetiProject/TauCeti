/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Split

/-!
# Coefficient change for circle tensors

Extending scalars in the tensor assigned to a finite circle set gives the circle tensor over
the new coefficient ring. The comparison preserves the enhanced-state basis and commutes with
merges, splits and circle reindexing. It therefore identifies the individual saddle maps after
coefficient extension, including births and deaths (empty fibres).

The comparison also restricts to each quantum degree. Its compatibility with the inclusions of
the homogeneous pieces identifies graded scalar extension with scalar extension of the actual
underlying circle module, rather than merely comparing their ranks.

The Frobenius algebra and saddle conventions follow M. Khovanov,
*A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
The scalar-extension comparisons use Mathlib's `Module.Basis.baseChange`.
-/

public section

noncomputable section

open TensorProduct PiTensorProduct DualNumber

namespace TauCeti.Khovanov

universe u v w

variable (R : Type u) (S : Type v) [CommSemiring R] [CommSemiring S] [Algebra R S]
  (ι : Type w) [Finite ι]

/-- Scalar extension of the circle tensor, preserving the labelling by `1` and `X`. -/
def circleBaseChange : S ⊗[R] CircleTensor R ι ≃ₗ[S] CircleTensor S ι :=
  ((circleBasis R ι).baseChange S).equiv (circleBasis S ι) (Equiv.refl _)

/-- Scalar extension sends a labelled tensor to the same labelled tensor. -/
@[simp↓]
theorem circleBaseChange_one_tmul_circleBasis (l : ι → Bool) :
    circleBaseChange R S ι (1 ⊗ₜ circleBasis R ι l) = circleBasis S ι l := by
  simpa only [circleBaseChange, Module.Basis.baseChange_apply, Equiv.refl_apply] using
    ((circleBasis R ι).baseChange S).equiv_apply l (circleBasis S ι) (Equiv.refl _)

/-- The inverse coefficient comparison preserves each enhanced-state basis vector. -/
@[simp↓]
theorem circleBaseChange_symm_circleBasis (l : ι → Bool) :
    (circleBaseChange R S ι).symm (circleBasis S ι l) = 1 ⊗ₜ circleBasis R ι l := by
  rw [LinearEquiv.symm_apply_eq, circleBaseChange_one_tmul_circleBasis]

/-- Coefficients in the enhanced-state basis extend along the coefficient-ring map. -/
@[simp]
theorem circleBasis_repr_circleBaseChange_tmul (a : S) (x : CircleTensor R ι)
    (l : ι → Bool) :
    (circleBasis S ι).repr (circleBaseChange R S ι (a ⊗ₜ x)) l =
      algebraMap R S ((circleBasis R ι).repr x l) * a := by
  simp [circleBaseChange, Module.Basis.equiv, Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def]

/-- On pure tensors the comparison extends coefficients in each dual-number factor.
The scalar outside the indexed tensor is retained even when the circle set is empty. -/
theorem circleBaseChange_tmul_tprod (a : S) (x : ι → R[ε]) :
    circleBaseChange R S ι (a ⊗ₜ tprod R x) =
      a • tprod S (fun i ↦ dualNumberAlgebraTensorAlgEquiv R S (1 ⊗ₜ x i)) := by
  let _ := Fintype.ofFinite ι
  refine (circleBasis S ι).ext_elem fun l ↦ ?_
  have h (i : ι) :
      (labelBasis S).repr (dualNumberAlgebraTensorAlgEquiv R S (1 ⊗ₜ x i)) (l i) =
        algebraMap R S ((labelBasis R).repr (x i) (l i)) := by
    cases l i <;> simp
  simp [circleBasis_repr_circleBaseChange_tmul, circleBasis_repr_tprod, h, mul_comm]

variable {R S ι}

/-- Reindexing the circles commutes with extension of coefficients. -/
theorem circleBaseChange_reindex {κ : Type*} [Finite κ] (e : ι ≃ κ)
    (x : S ⊗[R] CircleTensor R ι) :
    circleBaseChange R S κ
        ((reindex R (fun _ ↦ R[ε]) e).toLinearMap.baseChange S x) =
      reindex S (fun _ ↦ S[ε]) e (circleBaseChange R S ι x) := by
  have h : (circleBaseChange R S κ).toLinearMap ∘ₗ
        (reindex R (fun _ ↦ R[ε]) e).toLinearMap.baseChange S =
      (reindex S (fun _ ↦ S[ε]) e).toLinearMap ∘ₗ
        (circleBaseChange R S ι).toLinearMap := by
    refine ((circleBasis R ι).baseChange S).ext fun l ↦ ?_
    simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply,
      LinearMap.baseChange_tmul, LinearEquiv.coe_coe, reindex_circleBasis,
      circleBaseChange_one_tmul_circleBasis]
  exact LinearMap.congr_fun h x

variable {σ τ : Type*} [Fintype σ] [DecidableEq τ]

/-- Merges and births commute with scalar extension, retaining every unaffected circle. -/
theorem circleBaseChange_fiberwiseMul [Finite τ] (f : σ → τ)
    (x : S ⊗[R] CircleTensor R σ) :
    circleBaseChange R S τ
        ((fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f).toLinearMap.baseChange S x) =
      fiberwiseMul (R := S) (A := fun _ ↦ S[ε]) f (circleBaseChange R S σ x) := by
  let _ := Fintype.ofFinite τ
  classical
  have h : (circleBaseChange R S τ).toLinearMap ∘ₗ
        (fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f).toLinearMap.baseChange S =
      (fiberwiseMul (R := S) (A := fun _ ↦ S[ε]) f).toLinearMap ∘ₗ
        (circleBaseChange R S σ).toLinearMap := by
    refine ((circleBasis R σ).baseChange S).ext fun l ↦ ?_
    simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply,
      LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe,
      circleBaseChange_one_tmul_circleBasis, fiberwiseMul_circleBasis]
    split_ifs <;> simp only [circleBaseChange_one_tmul_circleBasis, tmul_zero, map_zero]
  exact LinearMap.congr_fun h x

/-- Splits and deaths commute with scalar extension. In particular this holds in
characteristic two without any invertibility assumption on the coefficient map. -/
theorem circleBaseChange_fiberwiseSplit [Fintype τ] (f : σ → τ)
    (x : S ⊗[R] CircleTensor R τ) :
    circleBaseChange R S σ ((fiberwiseSplit (R := R) f).baseChange S x) =
      fiberwiseSplit (R := S) f (circleBaseChange R S τ x) := by
  classical
  have h : (circleBaseChange R S σ).toLinearMap ∘ₗ
        (fiberwiseSplit (R := R) f).baseChange S =
      fiberwiseSplit (R := S) f ∘ₗ (circleBaseChange R S τ).toLinearMap := by
    refine ((circleBasis R τ).baseChange S).ext fun l ↦ ?_
    apply (circleBasis S σ).ext_elem
    intro k
    simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply,
      LinearMap.baseChange_tmul, LinearEquiv.coe_coe, circleBaseChange_one_tmul_circleBasis,
      circleBasis_repr_circleBaseChange_tmul, circleBasis_repr_fiberwiseSplit]
    split_ifs <;> simp [Module.Basis.repr_self, Finsupp.single_apply]
  exact LinearMap.congr_fun h x

end TauCeti.Khovanov

namespace TauCeti.Khovanov

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (ι : Type w) [Fintype ι]

/-- Scalar extension on a single quantum-degree piece, preserving its enhanced-state basis. -/
def circlePieceBaseChange (p : ℤ) :
    S ⊗[R] (circleQuantumGrading R ι).piece p ≃ₗ[S]
      (circleQuantumGrading S ι).piece p :=
  ((circlePieceBasis R ι p).baseChange S).equiv (circlePieceBasis S ι p) (Equiv.refl _)

/-- The homogeneous coefficient comparison preserves the basis labels. -/
@[simp]
theorem circlePieceBaseChange_one_tmul_circlePieceBasis (p : ℤ)
    (l : {l : ι → Bool // labelingQuantumDegree ι l = p}) :
    circlePieceBaseChange R S ι p (1 ⊗ₜ circlePieceBasis R ι p l) =
      circlePieceBasis S ι p l := by
  simpa only [circlePieceBaseChange, Module.Basis.baseChange_apply, Equiv.refl_apply] using
    ((circlePieceBasis R ι p).baseChange S).equiv_apply l
      (circlePieceBasis S ι p) (Equiv.refl _)

/-- The inverse homogeneous coefficient comparison preserves the basis labels. -/
@[simp]
theorem circlePieceBaseChange_symm_circlePieceBasis (p : ℤ)
    (l : {l : ι → Bool // labelingQuantumDegree ι l = p}) :
    (circlePieceBaseChange R S ι p).symm (circlePieceBasis S ι p l) =
      1 ⊗ₜ circlePieceBasis R ι p l := by
  rw [LinearEquiv.symm_apply_eq, circlePieceBaseChange_one_tmul_circlePieceBasis]

/-- The homogeneous comparison agrees with scalar extension on the full circle tensor. -/
@[simp]
theorem subtype_circlePieceBaseChange (p : ℤ)
    (x : S ⊗[R] (circleQuantumGrading R ι).piece p) :
    (circlePieceBaseChange R S ι p x : CircleTensor S ι) =
      circleBaseChange R S ι (((circleQuantumGrading R ι).piece p).subtype.baseChange S x) := by
  have h : ((circleQuantumGrading S ι).piece p).subtype ∘ₗ
        (circlePieceBaseChange R S ι p).toLinearMap =
      (circleBaseChange R S ι).toLinearMap ∘ₗ
        ((circleQuantumGrading R ι).piece p).subtype.baseChange S := by
    refine ((circlePieceBasis R ι p).baseChange S).ext fun l ↦ ?_
    simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, circlePieceBaseChange_one_tmul_circlePieceBasis,
      Submodule.subtype_apply, coe_circlePieceBasis, LinearMap.baseChange_tmul,
      circleBaseChange_one_tmul_circleBasis]
  exact LinearMap.congr_fun h x

end TauCeti.Khovanov
