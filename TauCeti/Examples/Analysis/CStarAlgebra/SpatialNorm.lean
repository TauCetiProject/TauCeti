/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Analysis.CStarAlgebra.SpatialNorm
import TauCeti.Analysis.CStarAlgebra.Basic

/-!
# The spatial norm on `M₂(ℂ) ⊙ M₂(ℂ)`

Two checks on the spatial C*-norm `NonUnitalStarSubalgebra.spatialNorm`. Let `b₁, b₂` be an
orthonormal pair in a complex Hilbert space `H` (for instance the standard basis of `ℂ²`), with
matrix units `eᵢⱼ = |bᵢ⟩⟨bⱼ|` in the algebra `B(H)` (`TauCeti.SpatialNormExample.e`), so that for
`H = ℂ²` they span `M₂(ℂ)`.

1. **The spatial norm of a sum is not the sum of cross norms.** The element
   `u = e₁₂ ⊗ e₁₂ + e₂₁ ⊗ e₂₁` exchanges `b₁ ⊗ b₁` and `b₂ ⊗ b₂` and kills `b₁ ⊗ b₂`, `b₂ ⊗ b₁`:
   `u⋆ u = e₂₂ ⊗ e₂₂ + e₁₁ ⊗ e₁₁` is a nonzero projection, so `‖u‖_min = 1`
   (`TauCeti.SpatialNormExample.spatialNorm_u`), whereas the cross norms of its two elementary
   tensors add up to `2` (`TauCeti.SpatialNormExample.spatialNorm_tmul_add_spatialNorm_tmul`).
2. **The spatial norm of `1 ⊗ 1`.** `‖1 ⊗ 1‖_min = ‖1‖ ‖1‖ = 1` for `H ≠ 0`
   (`TauCeti.SpatialNormExample.spatialNorm_one_tmul_one`), an instance of the cross-norm identity
   `NonUnitalStarSubalgebra.spatialNorm_tmul`.

Both are then specialized to the standard basis of `ℂ² = EuclideanSpace ℂ (Fin 2)`. Indices are
`0` and `1` in Lean, so `e₁₂` is `e b 0 1`.
-/

public section

noncomputable section

open TensorProduct UniformSpace InnerProductSpace

namespace TauCeti.SpatialNormExample

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The algebra `B(H)` of all operators on `H`, as a concrete operator algebra. -/
abbrev BH (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    NonUnitalStarSubalgebra ℂ (H →L[ℂ] H) :=
  ⊤

/-- The matrix unit `eᵢⱼ = |bᵢ⟩⟨bⱼ|` of an orthonormal pair `b`. -/
def e (b : Fin 2 → H) (i j : Fin 2) : BH H :=
  ⟨rankOne ℂ (b i) (b j), trivial⟩

/-- A shortcut instance: `simp` times out finding the distributivity of multiplication on
`B(H) ⊗[ℂ] B(H)` by itself. -/
local instance instDistribBHTensor : Distrib (BH H ⊗[ℂ] BH H) :=
  inferInstance

variable {b : Fin 2 → H}

/-- Matrix units multiply as `eᵢⱼ eⱼₗ = eᵢₗ`. -/
theorem e_mul_e (hb : Orthonormal ℂ b) (i j l : Fin 2) : e b i j * e b j l = e b i l :=
  Subtype.ext <| by
    simp [e, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hb.norm_eq_one]

/-- Matrix units multiply as `eᵢⱼ eₖₗ = 0` for `j ≠ k`. -/
theorem e_mul_e_of_ne (hb : Orthonormal ℂ b) (i : Fin 2) {j k : Fin 2} (l : Fin 2) (h : j ≠ k) :
    e b i j * e b k l = 0 :=
  Subtype.ext <| by
    simp [e, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hb.inner_eq_zero h]

/-- The adjoint of `eᵢⱼ` is `eⱼᵢ`. -/
theorem star_e (i j : Fin 2) : star (e b i j) = e b j i :=
  Subtype.ext <| by
    simp [e, ContinuousLinearMap.star_eq_adjoint]

/-- Matrix units have norm `1`. -/
theorem norm_e (hb : Orthonormal ℂ b) (i j : Fin 2) : ‖e b i j‖ = 1 := by
  rw [AddSubgroupClass.coe_norm, e, norm_rankOne, hb.norm_eq_one, hb.norm_eq_one, one_mul]

/-- The element `u = e₁₂ ⊗ e₁₂ + e₂₁ ⊗ e₂₁` of `B(H) ⊙ B(H)`. -/
def u (b : Fin 2 → H) : BH H ⊗[ℂ] BH H :=
  e b 0 1 ⊗ₜ e b 0 1 + e b 1 0 ⊗ₜ e b 1 0

/-- `u⋆ u = e₂₂ ⊗ e₂₂ + e₁₁ ⊗ e₁₁`. -/
theorem star_u_mul_u (hb : Orthonormal ℂ b) :
    star (u b) * u b = e b 1 1 ⊗ₜ e b 1 1 + e b 0 0 ⊗ₜ e b 0 0 := by
  simp [u, star_e, add_mul, mul_add, e_mul_e hb, e_mul_e_of_ne hb]

/-- `e₂₂ ⊗ e₂₂ + e₁₁ ⊗ e₁₁` is a projection. -/
theorem isStarProjection_star_u_mul_u (hb : Orthonormal ℂ b) :
    IsStarProjection (star (u b) * u b) := by
  refine ⟨?_, IsSelfAdjoint.star_mul_self (u b)⟩
  rw [IsIdempotentElem, star_u_mul_u hb]
  simp [add_mul, mul_add, e_mul_e hb, e_mul_e_of_ne hb]

/-- The operator of `u⋆ u` is nonzero: it fixes `b₁ ⊗ b₁`. -/
theorem spatialTensorHom_star_u_mul_u_ne_zero (hb : Orthonormal ℂ b) :
    NonUnitalStarSubalgebra.spatialTensorHom (BH H) (BH H) (star (u b) * u b) ≠ 0 := by
  intro h
  have hv := congrArg
    (fun T ↦ ‖T ((b 0 ⊗ₜ[ℂ] b 0 : H ⊗[ℂ] H) : Completion (H ⊗[ℂ] H))‖) h
  simp only [star_u_mul_u hb, map_add, NonUnitalStarSubalgebra.spatialTensorHom_tmul,
    _root_.add_apply, mapLCompletion_tmul, _root_.zero_apply, norm_zero] at hv
  simp [e, hb.inner_eq_zero one_ne_zero, hb.norm_eq_one] at hv

/-- **`‖u‖_min = 1`**: the spatial norm of `e₁₂ ⊗ e₁₂ + e₂₁ ⊗ e₂₁`. -/
theorem spatialNorm_u (hb : Orthonormal ℂ b) :
    NonUnitalStarSubalgebra.spatialNorm (BH H) (BH H) (u b) = 1 := by
  have hP := (isStarProjection_star_u_mul_u hb).map
    (NonUnitalStarSubalgebra.spatialTensorHom (BH H) (BH H))
  have hp : NonUnitalStarSubalgebra.spatialNorm (BH H) (BH H) (star (u b) * u b) = 1 := by
    rw [NonUnitalStarSubalgebra.spatialNorm_def]
    refine IsStarProjection.norm_eq_one (E := Completion (H ⊗[ℂ] H) →L[ℂ] Completion (H ⊗[ℂ] H))
      hP ?_
    exact spatialTensorHom_star_u_mul_u_ne_zero hb
  rw [NonUnitalStarSubalgebra.spatialNorm_star_mul_self] at hp
  nlinarith [NonUnitalStarSubalgebra.spatialNorm_nonneg (BH H) (BH H) (u b)]

/-- **The cross norms of the two elementary tensors of `u` add up to `2`**, so the spatial norm of a
sum is not the sum of the cross norms. -/
theorem spatialNorm_tmul_add_spatialNorm_tmul (hb : Orthonormal ℂ b) :
    NonUnitalStarSubalgebra.spatialNorm (BH H) (BH H) (e b 0 1 ⊗ₜ e b 0 1) +
      NonUnitalStarSubalgebra.spatialNorm (BH H) (BH H) (e b 1 0 ⊗ₜ e b 1 0) = 2 := by
  simp only [NonUnitalStarSubalgebra.spatialNorm_tmul, norm_e hb]
  norm_num

/-- The identity operator, as an element of `B(H)`. -/
def one (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : BH H :=
  ⟨1, trivial⟩

/-- **`‖1 ⊗ 1‖_min = 1`** for `H ≠ 0`, an instance of the cross-norm identity
`NonUnitalStarSubalgebra.spatialNorm_tmul`. -/
theorem spatialNorm_one_tmul_one [Nontrivial H] :
    NonUnitalStarSubalgebra.spatialNorm (BH H) (BH H) (one H ⊗ₜ one H) = 1 := by
  rw [NonUnitalStarSubalgebra.spatialNorm_tmul, AddSubgroupClass.coe_norm, one, norm_one,
    one_mul]

/-! ### The standard basis of `ℂ²` -/

/-- The standard basis of `ℂ² = EuclideanSpace ℂ (Fin 2)`. -/
abbrev std : Fin 2 → EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.basisFun (Fin 2) ℂ

/-- `‖e₁₂ ⊗ e₁₂ + e₂₁ ⊗ e₂₁‖_min = 1` in `M₂(ℂ) ⊙ M₂(ℂ)`, while the cross norms of its two terms
add up to `2`. -/
example :
    NonUnitalStarSubalgebra.spatialNorm (BH (EuclideanSpace ℂ (Fin 2)))
        (BH (EuclideanSpace ℂ (Fin 2))) (u std) = 1 ∧
      NonUnitalStarSubalgebra.spatialNorm (BH (EuclideanSpace ℂ (Fin 2)))
          (BH (EuclideanSpace ℂ (Fin 2))) (e std 0 1 ⊗ₜ e std 0 1) +
        NonUnitalStarSubalgebra.spatialNorm (BH (EuclideanSpace ℂ (Fin 2)))
          (BH (EuclideanSpace ℂ (Fin 2))) (e std 1 0 ⊗ₜ e std 1 0) = 2 :=
  ⟨spatialNorm_u (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal,
    spatialNorm_tmul_add_spatialNorm_tmul (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal⟩

/-- `‖1 ⊗ 1‖_min = 1` in `M₂(ℂ) ⊙ M₂(ℂ)`. -/
example :
    NonUnitalStarSubalgebra.spatialNorm (BH (EuclideanSpace ℂ (Fin 2)))
      (BH (EuclideanSpace ℂ (Fin 2))) (one _ ⊗ₜ one _) = 1 :=
  spatialNorm_one_tmul_one

end TauCeti.SpatialNormExample
