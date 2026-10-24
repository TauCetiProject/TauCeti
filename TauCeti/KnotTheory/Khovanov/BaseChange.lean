/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.ResolutionSplit

/-!
# Scalar extension of circle tensors

The tensor assigned to a finite set of resolution circles commutes with extension of
coefficients. The comparison sends each enhanced-state basis vector to the same labelling
over the new coefficient semiring. It intertwines reindexing, multiplication along fibres,
and its Frobenius adjoint, including births and deaths (empty fibres). In particular it
intertwines the merge and split maps of actual PD-code resolutions.

No flatness or injectivity of the coefficient map is required. For commutative rings the
comparison also identifies the scalar extension of each quantum-degree piece with the
corresponding piece over the new ring. These are the statewise comparisons needed for
coefficient changes of the bigraded resolution complex.

The construction uses Mathlib's `Module.Basis.baseChange` and the coefficient formulas for
`circleBasis` and `fiberwiseSplit`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
-/

public section

open TensorProduct PiTensorProduct DualNumber

namespace TauCeti.Khovanov

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
  (ι : Type*) [Finite ι]

/-- Scalar extension of a circle tensor, preserving every enhanced-state labelling. -/
noncomputable def circleTensorBaseChange : S ⊗[R] CircleTensor R ι ≃ₗ[S] CircleTensor S ι :=
  ((circleBasis R ι).baseChange S).equiv (circleBasis S ι) (Equiv.refl _)

variable {R S ι}

/-- Scalar extension preserves every labelled basis tensor. -/
@[simp↓]
theorem circleTensorBaseChange_tmul_circleBasis (a : S) (l : ι → Bool) :
    circleTensorBaseChange R S ι (a ⊗ₜ[R] circleBasis R ι l) = a • circleBasis S ι l := by
  have h : circleTensorBaseChange R S ι (1 ⊗ₜ[R] circleBasis R ι l) = circleBasis S ι l := by
    rw [← Module.Basis.baseChange_apply]
    exact Module.Basis.equiv_apply _ _ _ _
  calc
    _ = circleTensorBaseChange R S ι (a • (1 ⊗ₜ[R] circleBasis R ι l)) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    _ = _ := by rw [map_smul, h]

/-- The inverse comparison preserves labelled basis tensors. -/
@[simp↓]
theorem circleTensorBaseChange_symm_circleBasis (l : ι → Bool) :
    (circleTensorBaseChange R S ι).symm (circleBasis S ι l) =
      1 ⊗ₜ[R] circleBasis R ι l := by
  apply (circleTensorBaseChange R S ι).injective
  rw [LinearEquiv.apply_symm_apply, circleTensorBaseChange_tmul_circleBasis, one_smul]

/-- Coordinates of the comparison are the scalar-extended basis coordinates. -/
@[simp]
theorem circleBasis_repr_circleTensorBaseChange (z : S ⊗[R] CircleTensor R ι) :
    (circleBasis S ι).repr (circleTensorBaseChange R S ι z) =
      ((circleBasis R ι).baseChange S).repr z := by
  simp [circleTensorBaseChange, Module.Basis.equiv]

/-- A pure tensor has its old coordinates mapped along the coefficient map and scaled by its
left factor. -/
theorem circleBasis_repr_circleTensorBaseChange_tmul (a : S) (x : CircleTensor R ι)
    (l : ι → Bool) :
    (circleBasis S ι).repr (circleTensorBaseChange R S ι (a ⊗ₜ[R] x)) l =
      a * algebraMap R S ((circleBasis R ι).repr x l) := by
  rw [circleBasis_repr_circleTensorBaseChange, Module.Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def, mul_comm]

/-- On a pure circle tensor, scalar extension applies the native dual-number coefficient
comparison to every factor. -/
theorem circleTensorBaseChange_tmul_tprod (a : S) (x : ι → R[ε]) :
    circleTensorBaseChange R S ι (a ⊗ₜ[R] tprod R x) =
      a • tprod S (fun i ↦ dualNumberAlgebraTensorAlgEquiv R S (1 ⊗ₜ[R] x i)) := by
  classical
  let := Fintype.ofFinite ι
  apply (circleBasis S ι).ext_elem
  intro l
  simp only [circleBasis_repr_circleTensorBaseChange_tmul, map_smul, Finsupp.smul_apply,
    smul_eq_mul, circleBasis_repr_tprod, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases l i <;> simp

/-- The inverse comparison is expansion in the enhanced-state basis, with coefficients placed
in the left tensor factor. -/
theorem circleTensorBaseChange_symm_apply (x : CircleTensor S ι) :
    (circleTensorBaseChange R S ι).symm x =
      ((circleBasis S ι).repr x).sum (fun l a ↦ a ⊗ₜ[R] circleBasis R ι l) := by
  apply (circleTensorBaseChange R S ι).injective
  simp only [LinearEquiv.apply_symm_apply, Finsupp.sum, map_sum,
    circleTensorBaseChange_tmul_circleBasis]
  exact ((circleBasis S ι).linearCombination_repr x).symm

section Maps

variable {σ τ : Type*}

/-- Scalar extension commutes with multiplication along any circle correspondence, including
births on empty fibres. -/
theorem circleTensorBaseChange_fiberwiseMul [Fintype σ] [Finite τ] [DecidableEq τ]
    (f : σ → τ) :
    (circleTensorBaseChange R S τ).toLinearMap.comp
        ((fiberwiseMul (R := R) (A := fun _ ↦ R[ε]) f).toLinearMap.baseChange S) =
      (fiberwiseMul (R := S) (A := fun _ ↦ S[ε]) f).toLinearMap.comp
        (circleTensorBaseChange R S σ).toLinearMap := by
  classical
  let := Fintype.ofFinite τ
  refine ((circleBasis R σ).baseChange S).ext fun l ↦ ?_
  simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, AlgHom.toLinearMap_apply, circleTensorBaseChange_tmul_circleBasis,
    one_smul, fiberwiseMul_circleBasis]
  split_ifs <;> simp only [circleTensorBaseChange_tmul_circleBasis,
    one_smul, tmul_zero, map_zero]

/-- Scalar extension commutes with the Frobenius-adjoint split along any circle correspondence,
including deaths on empty fibres. -/
theorem circleTensorBaseChange_fiberwiseSplit [Fintype σ] [Fintype τ] [DecidableEq τ]
    (f : σ → τ) :
    (circleTensorBaseChange R S σ).toLinearMap.comp ((fiberwiseSplit (R := R) f).baseChange S) =
      (fiberwiseSplit (R := S) f).comp (circleTensorBaseChange R S τ).toLinearMap := by
  classical
  refine ((circleBasis R τ).baseChange S).ext fun l ↦ (circleBasis S σ).ext_elem fun k ↦ ?_
  simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, circleTensorBaseChange_tmul_circleBasis, one_smul,
    circleBasis_repr_circleTensorBaseChange_tmul, one_mul, circleBasis_repr_fiberwiseSplit]
  split_ifs <;> simp only [Module.Basis.repr_self, Finsupp.single_apply,
    apply_ite (algebraMap R S), map_one, map_zero]

end Maps

/-- Scalar extension commutes with every relabelling of the circles. -/
theorem circleTensorBaseChange_reindex {σ τ : Type*} [Finite σ] [Finite τ] (e : σ ≃ τ) :
    (circleTensorBaseChange R S τ).toLinearMap.comp
        ((reindex R (fun _ ↦ R[ε]) e).toLinearMap.baseChange S) =
      (reindex S (fun _ ↦ S[ε]) e).toLinearMap.comp
        (circleTensorBaseChange R S σ).toLinearMap := by
  classical
  refine ((circleBasis R σ).baseChange S).ext fun l ↦ ?_
  simp only [Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, reindex_circleBasis, circleTensorBaseChange_tmul_circleBasis, one_smul]

section Quantum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type*} [Fintype ι]

/-- Extending coefficients of a homogeneous circle tensor preserves its quantum degree. -/
theorem circleTensorBaseChange_tmul_mem {p : ℤ} {x : CircleTensor R ι}
    (hx : x ∈ (circleQuantumGrading R ι).piece p) (a : S) :
    circleTensorBaseChange R S ι (a ⊗ₜ[R] x) ∈ (circleQuantumGrading S ι).piece p := by
  rw [mem_circleQuantumGrading_piece_iff] at hx ⊢
  intro l hl
  apply hx l
  intro hzero
  simp only [circleBasis_repr_circleTensorBaseChange_tmul, hzero, map_zero, mul_zero,
    ne_eq, not_true_eq_false] at hl

/-- Scalar extension identifies each quantum piece with its counterpart over the new ring. -/
theorem map_circleQuantumGrading_baseChange (p : ℤ) :
    Submodule.map (circleTensorBaseChange R S ι).toLinearMap
        (((circleQuantumGrading R ι).piece p).baseChange S) =
      (circleQuantumGrading S ι).piece p := by
  classical
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact circleTensorBaseChange_tmul_mem hx 1
  · intro y hy
    refine ⟨(circleTensorBaseChange R S ι).symm y, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [circleTensorBaseChange_symm_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun l hl ↦ ?_
    have hdegree := (mem_circleQuantumGrading_piece_iff.mp hy) l (Finsupp.mem_support_iff.mp hl)
    exact Submodule.tmul_mem_baseChange_of_mem _
      (hdegree ▸ circleBasis_mem_circleQuantumGrading_piece l)

end Quantum

end TauCeti.Khovanov

namespace TauCeti.PDCode

open Khovanov

variable {n : ℕ} (D : PDCode n) {s t : Fin n → Bool} {c : Fin n}
  (hst : ∀ j, j ≠ c → s j = t j) (hc : s c ≠ t c)
  (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The actual merge block of a resolution commutes with scalar extension, including all
unaffected crossing-free circles. -/
theorem circleTensorBaseChange_resolutionMergeMap (hs : (D.circlesAt s c).card = 2) :
    (circleTensorBaseChange R S (D.ResolvedCircle t)).toLinearMap.comp
        ((D.resolutionMergeMap hst hc hs R).toLinearMap.baseChange S) =
      (D.resolutionMergeMap hst hc hs S).toLinearMap.comp
        (circleTensorBaseChange R S (D.ResolvedCircle s)).toLinearMap := by
  rw [resolutionMergeMap_def, resolutionMergeMap_def]
  exact circleTensorBaseChange_fiberwiseMul _

/-- The actual split block of a resolution commutes with scalar extension, including all
unaffected crossing-free circles. -/
theorem circleTensorBaseChange_resolutionSplitMap (ht : (D.circlesAt t c).card = 2) :
    (circleTensorBaseChange R S (D.ResolvedCircle t)).toLinearMap.comp
        ((D.resolutionSplitMap hst hc ht R).baseChange S) =
      (D.resolutionSplitMap hst hc ht S).comp
        (circleTensorBaseChange R S (D.ResolvedCircle s)).toLinearMap := by
  rw [resolutionSplitMap_def, resolutionSplitMap_def]
  exact circleTensorBaseChange_fiberwiseSplit _

end TauCeti.PDCode
