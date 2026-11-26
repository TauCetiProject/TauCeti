/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Matrix
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Nuclear

/-!
# Completely positive maps into finite products, compressions to submatrices, and the nuclearity
of finite direct sums of matrix algebras

A family of completely positive maps `φ_i : A → B_i` into finitely many C⋆-algebras assembles to
a completely positive map `a ↦ (φ_i(a))_i` into the product (`CompletelyPositiveMap.pi`): a matrix
over the product is positive exactly when each of its components is
(`CStarMatrix.piStarAlgEquiv`). The compression `x ↦ x|_{f × f}` of a matrix to the rows and
columns picked by `f : m → n` is completely positive (`CompletelyPositiveMap.submatrix`).

Together with the block-diagonal sum `CompletelyPositiveMap.blockDiagonal`, these show that a
finite direct sum `⊕_i M_{n_i}` of full matrix algebras is nuclear
(`TauCeti.CStarAlgebra.isNuclear_pi_cstarMatrix`): it embeds unitally in `M_N`, `N = Σ n_i`, and
the compression to the diagonal blocks is a completely positive contraction back, so the identity
factors exactly through one matrix algebra.

## References

The CStarAlgebras roadmap, C6.1, first Check.
-/

public section

open scoped CStarAlgebra ComplexOrder

open CStarMatrix (ofMatrix)

namespace CStarMatrix

variable (R m : Type*) {ι : Type*} (B : ι → Type*) [Fintype m] [∀ i, AddCommMonoid (B i)]
  [∀ i, Mul (B i)] [∀ i, Star (B i)] [∀ i, SMul R (B i)]

/-- A matrix over a product is the family of its components: `M_m(Π B_i) ≃ Π M_m(B_i)`, as a
star algebra isomorphism of C⋆-matrices (`Matrix.piRingEquiv` with the star structure). -/
def piStarAlgEquiv : CStarMatrix m m (∀ i, B i) ≃⋆ₐ[R] ∀ i, CStarMatrix m m (B i) where
  toFun M i := M.map (· i)
  invFun f := ofMatrix (Matrix.of fun j l i ↦ f i j l)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' := (Matrix.piRingEquiv (n := m) (β := B)).map_mul
  map_smul' _ _ := rfl
  map_star' M := by
    ext i j l
    simp [CStarMatrix.star_apply]

variable {R m B}

@[simp]
theorem piStarAlgEquiv_apply (M : CStarMatrix m m (∀ i, B i)) (i : ι) (j l : m) :
    piStarAlgEquiv R m B M i j l = M j l i :=
  (rfl)

end CStarMatrix

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
    exact fun i ↦ (φ i).map_cstarMatrix_nonneg' k M hM

@[simp]
theorem pi_apply (φ : ∀ i, A →CP B i) (a : A) (i : ι) : pi φ a i = φ i a :=
  (rfl)

/-- `a ↦ (φ_i(a))_i` is contractive when each `φ_i` is. -/
theorem norm_pi_apply_le {φ : ∀ i, A →CP B i} (hφ : ∀ i a, ‖φ i a‖ ≤ ‖a‖) (a : A) :
    ‖pi φ a‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2 fun i ↦ hφ i a

end Pi

section Submatrix

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {m n : Type*} [Fintype m] [Fintype n]

/-- The compression `x ↦ x|_{f × f}` of an `n × n` matrix to the rows and columns `f : m → n` is
completely positive. -/
def submatrix (f : m → n) : CStarMatrix n n B →CP CStarMatrix m m B where
  toFun x := ofMatrix ((ofMatrix.symm x).submatrix f f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_cstarMatrix_nonneg' k M hM := by
    let eA := CStarMatrix.compStarAlgEquiv ℂ (Fin k) n B
    let eB := CStarMatrix.compStarAlgEquiv ℂ (Fin k) m B
    have hM' : 0 ≤ eA M := by simpa using (map_le_map_iff eA).mpr hM
    rw [← map_le_map_iff eB, map_zero]
    convert CStarMatrix.submatrix_nonneg (Prod.map id f) hM' using 1
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [eA, eB, CStarMatrix.ofMatrix_apply]
    rfl

@[simp]
theorem submatrix_apply (f : m → n) (x : CStarMatrix n n B) (i j : m) :
    submatrix f x i j = x (f i) (f j) :=
  (rfl)

end Submatrix

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
  have hσ (a : ∀ i, CStarMatrix (n i) (n i) ℂ) : ‖σ a‖ ≤ ‖a‖ := by
    refine (CompletelyPositiveMapClass.norm_apply_le σ a).trans
      (mul_le_of_le_one_left (norm_nonneg a) ?_)
    rw [hσ1]
    rcases isEmpty_or_nonempty (Σ i, n i) with h | h
    · exact (norm_le_zero_iff.2 (CStarMatrix.ext fun j ↦ isEmptyElim j)).trans zero_le_one
    · rw [CStarRing.norm_one]
  have hρ (x : CStarMatrix (Σ i, n i) (Σ i, n i) ℂ) : ‖ρ x‖ ≤ ‖x‖ := by
    refine norm_pi_apply_le (fun i y ↦ ?_) x
    refine (CompletelyPositiveMapClass.norm_apply_le _ y).trans
      (mul_le_of_le_one_left (norm_nonneg y) ?_)
    have h1 : submatrix (B := ℂ) (Sigma.mk i) (1 : CStarMatrix (Σ i, n i) (Σ i, n i) ℂ) = 1 :=
      congrArg ofMatrix (Matrix.submatrix_one _ sigma_mk_injective)
    rw [h1]
    rcases isEmpty_or_nonempty (n i) with h | h
    · exact (norm_le_zero_iff.2 (CStarMatrix.ext fun j ↦ isEmptyElim j)).trans zero_le_one
    · rw [CStarRing.norm_one]
  refine .of_retract σ ρ hσ hρ fun a ↦ ?_
  ext i j k
  simp [σ, ρ]

end TauCeti.CStarAlgebra
