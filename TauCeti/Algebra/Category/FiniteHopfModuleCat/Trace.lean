/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Pivotal
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical

/-!
# Pivotal traces of finite-dimensional Hopf modules

Let `H` be a Hopf algebra over a field `k` and let `g` be a group-like unit of `H` implementing the
square of the antipode, `S²(a) = g a g⁻¹`. The double dual comparisons `m ↦ (φ ↦ φ(g m))` form
the pivotal structure `pivotalCategory` on finite-dimensional `H`-modules. This file computes its
left and right traces as ordinary traces of linear maps twisted by `g`: for an endomorphism `f`
of a finite-dimensional module `M`,

* `rightTrace f = tr_M(g f)`, and
* `leftTrace f = tr_M(g⁻¹ f)`,

where a scalar `c : k` is identified with the endomorphism `c • 𝟙` of the unit object. In
particular the right and left dimensions of `M` are `tr_M(g)` and `tr_M(g⁻¹)`, and the pivotal
structure is spherical exactly when `tr_M(g⁻¹ f) = tr_M(g f)` for every endomorphism `f` of every
finite-dimensional module.

The right trace is computed directly from the coevaluation `1 ↦ ∑ i, b i ⊗ b^i` and the
evaluation of the contragredient. The left trace is the right trace of the transpose
`fᘁ` on the contragredient, on which `g` acts through `S(g) = g⁻¹`. The statements parallel the
trace formula `FGModuleCat.trace_eq_smul` for finite-dimensional vector spaces.

## Main results

* `TauCeti.FiniteHopfModuleCat.rightTrace_eq_smul` and
  `TauCeti.FiniteHopfModuleCat.leftTrace_eq_smul`: the pivotal traces are `tr_M(g f)` and
  `tr_M(g⁻¹ f)`.
* `TauCeti.FiniteHopfModuleCat.rightDim_eq_smul` and
  `TauCeti.FiniteHopfModuleCat.leftDim_eq_smul`: the pivotal dimensions are `tr_M(g)` and
  `tr_M(g⁻¹)`.
* `TauCeti.FiniteHopfModuleCat.sphericalCategory_iff`: the pivotal structure is spherical exactly
  when the two twisted traces of every module endomorphism agree.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs 205, Section 4.7, for pivotal traces and dimensions.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter XIV, for quantum traces.
-/

public noncomputable section

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]

variable {g : Hˣ} (hg : ∀ a : H, HopfAlgebra.antipode k (HopfAlgebra.antipode k a) = g * a * ↑g⁻¹)
  (hg₁ : IsGroupLikeElem k (g : H))

/-- The right trace of an endomorphism `f` of a finite-dimensional module `M` for the pivotal
structure of the group-like element `g` is the trace of `g f` on `M`. -/
@[simp]
theorem rightTrace_eq_smul {M : FiniteHopfModuleCat k H} (f : M ⟶ M) :
    letI := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
    letI := pivotalCategory hg hg₁
    rightTrace f =
      LinearMap.trace k M (Algebra.lsmul k k M (g : H) ∘ₗ f.hom.hom.restrictScalars k) •
        𝟙 (𝟙_ (FiniteHopfModuleCat k H)) := by
  let := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
  let := pivotalCategory hg hg₁
  refine eq_smul_id_iff.mpr fun r => ?_
  rw [rightTrace_eq_pivotalIsoApp, pivotalIsoApp_pivotalCategory]
  simp only [hom_hom_comp, LinearMap.comp_apply]
  -- Expand the coevaluation `r ↦ ∑ i, r b i ⊗ b^i` and evaluate each term.
  set b := Module.Basis.ofVectorSpace k M
  let ψ : _ → (Mᘁ : FiniteHopfModuleCat k H) := fun i => (dualEquiv k H M).symm (b.coord i)
  have hη : (η_ M Mᘁ).hom.hom r =
      ∑ i, (tmul k H (trivialEquiv k H r • b i) (ψ i) : ↑(M ⊗ Mᘁ)) := by
    -- The coevaluation of the right dual is `dualCoevaluation M`, by definition of the instance.
    rw [show η_ M Mᘁ = dualCoevaluation M from rfl, dualCoevaluation_hom_hom]
    exact dualCoeval_apply_eq_sum k H M r
  rw [hη, map_sum, map_sum, map_sum, map_sum]
  simp only [whiskerRight_tmul, evaluation_tmul, dualEquiv_unitEvalIso_hom_apply,
    LinearEquiv.apply_symm_apply]
  classical
  rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ψ, b, LinearMap.toMatrix_apply, smul_comm (g : H) (trivialEquiv k H r), mul_comm]

/-- The left trace of an endomorphism `f` of a finite-dimensional module `M` for the pivotal
structure of the group-like element `g` is the trace of `g⁻¹ f` on `M`. -/
@[simp]
theorem leftTrace_eq_smul {M : FiniteHopfModuleCat k H} (f : M ⟶ M) :
    letI := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
    letI := pivotalCategory hg hg₁
    leftTrace f =
      LinearMap.trace k M (Algebra.lsmul k k M (↑g⁻¹ : H) ∘ₗ f.hom.hom.restrictScalars k) •
        𝟙 (𝟙_ (FiniteHopfModuleCat k H)) := by
  let := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
  let := pivotalCategory hg hg₁
  -- The left trace of `f` is the right trace of its transpose `fᘁ`.
  rw [← rightTrace_rightAdjointMate, rightTrace_eq_smul hg hg₁]
  congr 1
  have hS : HopfAlgebra.antipode k (g : H) = ↑g⁻¹ :=
    Units.eq_inv_of_mul_eq_one_right hg₁.antipode_mul_cancel
  -- On the native dual, `g fᘁ` is the transpose of `f g⁻¹`, since `g` acts through `S(g) = g⁻¹`.
  have hconj : (dualEquiv k H M).conj (Algebra.lsmul k k (Mᘁ : FiniteHopfModuleCat k H) (g : H) ∘ₗ
      (fᘁ).hom.hom.restrictScalars k) = Module.Dual.transpose (R := k)
        (f.hom.hom.restrictScalars k ∘ₗ Algebra.lsmul k k M (↑g⁻¹ : H)) := by
    have key (ψ : (Mᘁ : FiniteHopfModuleCat k H)) (m : M) :
        dualEquiv k H M ((g : H) • (fᘁ).hom.hom ψ) m =
          dualEquiv k H M ψ (f.hom.hom (((g⁻¹ : Hˣ) : H) • m)) := by
      refine (dualEquiv_smul_apply k H M (g : H) ((fᘁ).hom.hom ψ) m).trans ?_
      rw [dualEquiv_rightAdjointMate_apply, hS]
    ext ψ m
    exact (key ((dualEquiv k H M).symm ψ) m).trans (by simp [Module.Dual.transpose_apply])
  refine (LinearMap.trace_conj' _ (dualEquiv k H M)).symm.trans
    ((congrArg (LinearMap.trace k _) hconj).trans ?_)
  rw [LinearMap.trace_transpose', LinearMap.trace_comp_comm']

/-- The right dimension of a finite-dimensional module `M` for the pivotal structure of the
group-like element `g` is the trace of `g` on `M`. -/
@[simp]
theorem rightDim_eq_smul (M : FiniteHopfModuleCat k H) :
    letI := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
    letI := pivotalCategory hg hg₁
    rightDim M = LinearMap.trace k M (Algebra.lsmul k k M (g : H)) •
      𝟙 (𝟙_ (FiniteHopfModuleCat k H)) := by
  let := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
  let := pivotalCategory hg hg₁
  rw [← rightTrace_id, rightTrace_eq_smul hg hg₁, hom_hom_id, LinearMap.restrictScalars_id,
    LinearMap.comp_id]

/-- The left dimension of a finite-dimensional module `M` for the pivotal structure of the
group-like element `g` is the trace of `g⁻¹` on `M`. -/
@[simp]
theorem leftDim_eq_smul (M : FiniteHopfModuleCat k H) :
    letI := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
    letI := pivotalCategory hg hg₁
    leftDim M = LinearMap.trace k M (Algebra.lsmul k k M (↑g⁻¹ : H)) •
      𝟙 (𝟙_ (FiniteHopfModuleCat k H)) := by
  let := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
  let := pivotalCategory hg hg₁
  rw [← leftTrace_id, leftTrace_eq_smul hg hg₁, hom_hom_id, LinearMap.restrictScalars_id,
    LinearMap.comp_id]

/-- The pivotal structure of the group-like element `g` is spherical exactly when the traces of
`g⁻¹ f` and of `g f` agree for every endomorphism `f` of every finite-dimensional module. -/
theorem sphericalCategory_iff :
    letI := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
    letI := pivotalCategory hg hg₁
    SphericalCategory (FiniteHopfModuleCat k H) ↔
      ∀ (M : FiniteHopfModuleCat k H) (f : M ⟶ M),
        LinearMap.trace k M (Algebra.lsmul k k M (↑g⁻¹ : H) ∘ₗ f.hom.hom.restrictScalars k) =
          LinearMap.trace k M (Algebra.lsmul k k M (g : H) ∘ₗ f.hom.hom.restrictScalars k) := by
  let := rigidCategory (HopfAlgebra.antipode_bijective_of_antipode_antipode hg)
  let := pivotalCategory hg hg₁
  refine ⟨fun h M f => ?_, fun h => ⟨fun f => ?_⟩⟩
  · -- Evaluate the equal scalars `leftTrace f` and `rightTrace f` at the unit of `k`.
    have := eq_smul_id_iff.mp ((leftTrace_eq_smul hg hg₁ f).symm.trans
      ((h.leftTrace_eq_rightTrace f).trans (rightTrace_eq_smul hg hg₁ f)))
      ((trivialEquiv k H).symm 1)
    simpa using this
  · rw [leftTrace_eq_smul hg hg₁, rightTrace_eq_smul hg hg₁, h]

end TauCeti.FiniteHopfModuleCat
