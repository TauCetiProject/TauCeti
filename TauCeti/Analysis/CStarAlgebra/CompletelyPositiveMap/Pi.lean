/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Matrix
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear
import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# Completely positive maps into finite products, and the nuclearity of finite direct sums of
matrix algebras

A family of completely positive maps `φ_i : A → B_i` into finitely many C⋆-algebras assembles to
a completely positive map `a ↦ (φ_i(a))_i` into the product (`CompletelyPositiveMap.pi`): a matrix
over the product is positive exactly when each of its components is
(`CStarMatrix.piStarAlgEquiv`).

Together with the block-diagonal sum `CompletelyPositiveMap.blockDiagonal` and the compressions
`CompletelyPositiveMap.submatrix` to the diagonal blocks, this shows that a finite direct sum
`⊕_i M_{n_i}` of full matrix algebras is nuclear
(`TauCeti.CStarAlgebra.isNuclear_pi_cstarMatrix`): it embeds unitally in `M_N`, `N = Σ n_i`, and
the compression to the diagonal blocks is a completely positive contraction back, so the identity
factors exactly through one matrix algebra.
-/

public section

open scoped CStarAlgebra ComplexOrder

namespace CompletelyPositiveMap

section Pi

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {ι : Type*} [Fintype ι] {B : ι → Type*} [∀ i, NonUnitalCStarAlgebra (B i)]
  [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]

/-- The completely positive map `a ↦ (φ_i(a))_i` into a finite product. -/
def pi (φ : ∀ i, A →CP B i) : A →CP ∀ i, B i where
  toLinearMap := LinearMap.pi fun i ↦ (φ i).toLinearMap
  map_cstarMatrix_nonneg' k M hM := by
    let e := CStarMatrix.piStarAlgEquiv ℂ (Fin k) B
    rw [← map_le_map_iff e, map_zero]
    exact fun i ↦ ((φ i).map_cstarMatrix_nonneg' k M hM).trans_eq (by ext; simp [e])

@[simp]
theorem pi_apply (φ : ∀ i, A →CP B i) (a : A) (i : ι) : pi φ a i = φ i a :=
  (rfl)

/-- `a ↦ (φ_i(a))_i` is contractive when each `φ_i` is. -/
theorem norm_pi_apply_le {φ : ∀ i, A →CP B i} (hφ : ∀ i a, ‖φ i a‖ ≤ ‖a‖) (a : A) :
    ‖pi φ a‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 fun i ↦ hφ i a

end Pi

end CompletelyPositiveMap

namespace TauCeti.CStarAlgebra

open CompletelyPositiveMap

/-- **Finite direct sums of matrix algebras are nuclear.** The product `Π i, M_{n i}(ℂ)` embeds in
`M_{Σ i, n i}(ℂ)` block-diagonally, and the compression to the diagonal blocks is a completely
positive contraction back, so the identity factors exactly through one matrix algebra. -/
instance isNuclear_pi_cstarMatrix {ι : Type*} [Fintype ι] (n : ι → Type*) [∀ i, Fintype (n i)] :
    IsNuclear (∀ i, CStarMatrix (n i) (n i) ℂ) := by
  classical
  let σ : (∀ i, CStarMatrix (n i) (n i) ℂ) →CP CStarMatrix (Σ i, n i) (Σ i, n i) ℂ :=
    blockDiagonal fun i ↦ CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (Pi.evalStarAlgHom ℂ (fun i ↦ CStarMatrix (n i) (n i) ℂ) i)
  let ρ : CStarMatrix (Σ i, n i) (Σ i, n i) ℂ →CP ∀ i, CStarMatrix (n i) (n i) ℂ :=
    pi fun i ↦ submatrix (Sigma.mk i)
  have hσ1 : σ 1 = 1 := blockDiagonal_map_one _ fun i ↦ by simp
  have hσ : ∀ a, ‖σ a‖ ≤ ‖a‖ :=
    (CompletelyPositiveMapClass.norm_map_one_le_one_iff σ).1 (hσ1 ▸ CStarRing.norm_one_le)
  have hρ (x : CStarMatrix (Σ i, n i) (Σ i, n i) ℂ) : ‖ρ x‖ ≤ ‖x‖ := by
    refine norm_pi_apply_le (fun i ↦ (CompletelyPositiveMapClass.norm_map_one_le_one_iff _).1 ?_) x
    rw [submatrix_map_one sigma_mk_injective]
    exact CStarRing.norm_one_le
  refine .of_retract σ ρ hσ hρ fun a ↦ ?_
  ext i j k
  simp [σ, ρ]

end TauCeti.CStarAlgebra
