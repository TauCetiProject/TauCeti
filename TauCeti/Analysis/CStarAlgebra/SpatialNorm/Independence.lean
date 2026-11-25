/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.CStarAlgebra.SpatialNorm
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import TauCeti.Analysis.CStarAlgebra.Matrix.Order
import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Representation independence of the spatial C*-norm

Let `A` and `B` be C*-algebras, and let `π₁ : A → B(H₁)`, `π₂ : B → B(H₂)` be star homomorphisms
into the bounded operators on complex Hilbert spaces. They give the operator
`(π₁ ⊗ π₂)(x) = spatialTensorLinearMap (TensorProduct.map π₁ π₂ x)` on the completed Hilbert
tensor product `H₁ ⊗₂ H₂` for each `x ∈ A ⊗[ℂ] B`. This file proves that the norm of this operator
does not depend on the choice of **faithful** (injective) representations
(`TauCeti.norm_spatialTensorLinearMap_map_eq`), and that faithful representations give the
largest such norm (`TauCeti.norm_spatialTensorLinearMap_map_le`). For concrete C*-algebras
`A ⊆ B(E)` and `B ⊆ B(F)`, the spatial norm `‖x‖_min` of `TauCeti.Analysis.CStarAlgebra.SpatialNorm`
is therefore the norm of `(π₁ ⊗ π₂)(x)` for every pair of faithful representations
(`NonUnitalStarSubalgebra.norm_spatialTensorLinearMap_map_eq_spatialNorm`, Takesaki I,
Theorem IV.4.9), and it bounds that norm for every pair of representations
(`NonUnitalStarSubalgebra.norm_spatialTensorLinearMap_map_le_spatialNorm`).

The proof treats one factor at a time. For `y ∈ A ⊗ B(F)` and a finite orthonormal family
`e₁, …, eₙ` in `F`, slicing the second factor by the vector functionals `b ↦ ⟪eₖ, b eₗ⟫`
(`TauCeti.vectorSlice`) gives a matrix `S ∈ Mₙ(A)`. On vectors `∑ₗ ξₗ ⊗ eₗ` the operator
`(π ⊗ 1)(y)` acts through the operator matrix `π(S) ∈ Mₙ(B(H))`, so
`‖π(S)‖ ≤ ‖(π ⊗ 1)(y)‖`
(`TauCeti.norm_ofMatrix_le_norm_spatialTensorLinearMap_rTensor`), and conversely the norm of
`(π ⊗ 1)(y)` is at most the supremum of these matrix norms, because every pair of vectors of the
algebraic tensor product lies in `H ⊗ V` for a finite-dimensional subspace `V` of `F`
(`TauCeti.norm_spatialTensorLinearMap_rTensor_le_of_forall`). The matrix amplification of a star
homomorphism of C*-algebras is contractive, and isometric when the homomorphism is injective, so
`‖π(S)‖ ≤ ‖S‖ = ‖σ(S)‖` for faithful `σ`. The second factor reduces to the first through the flip
`H ⊗₂ K ≃ K ⊗₂ H` (`TauCeti.norm_spatialTensorLinearMap_comm`).

The norm of an operator matrix `M ∈ Mₙ(B(H))` is its norm acting on `Hⁿ`
(`CStarMatrix.sum_norm_sq_le`, `CStarMatrix.norm_le_of_sum_norm_sq_le`), by the C*-identity and
the description of positive operator matrices by their vector quadratic forms.

## Main declarations

* `TauCeti.norm_spatialTensorLinearMap_map_le`: `‖(π₁ ⊗ π₂)(x)‖ ≤ ‖(σ₁ ⊗ σ₂)(x)‖` when `σ₁` and
  `σ₂` are injective.
* `TauCeti.norm_spatialTensorLinearMap_map_eq`: **representation independence**, the norms agree
  for any two pairs of faithful representations.
* `NonUnitalStarSubalgebra.norm_spatialTensorLinearMap_map_eq_spatialNorm`: for closed concrete
  operator algebras, `‖(π₁ ⊗ π₂)(x)‖ = ‖x‖_min` for faithful `π₁`, `π₂`.
* `NonUnitalStarSubalgebra.norm_spatialTensorLinearMap_map_le_spatialNorm`:
  `‖(π₁ ⊗ π₂)(x)‖ ≤ ‖x‖_min` for arbitrary star homomorphisms `π₁`, `π₂`.

## References

* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4 (Theorem IV.4.9 is the
  representation independence of the spatial norm).
-/

public section

noncomputable section

open UniformSpace TensorProduct ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder

/-! ### Operator matrices -/

namespace CStarMatrix

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The quadratic form of `M⋆ M` on a family of vectors `ξ` is the squared norm of `M ξ`:
`∑ᵢ ∑ⱼ ⟪ξᵢ, (M⋆ M)ᵢⱼ ξⱼ⟫ = ∑ₖ ‖∑ₗ Mₖₗ ξₗ‖²`. -/
theorem sum_inner_star_mul_self_apply [CompleteSpace H] (M : CStarMatrix ι ι (H →L[ℂ] H))
    (ξ : ι → H) :
    ∑ i, ∑ j, ⟪ξ i, (star M * M) i j (ξ j)⟫_ℂ = ∑ k, ((‖∑ l, M k l (ξ l)‖ : ℂ) ^ 2) := by
  have hrew : (∑ i, ∑ j, ⟪ξ i, (star M * M) i j (ξ j)⟫_ℂ) =
        ∑ l, ⟪∑ i, M l i (ξ i), ∑ j, M l j (ξ j)⟫_ℂ := by
    simp_rw [CStarMatrix.mul_apply, CStarMatrix.star_apply, _root_.sum_apply,
      ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.star_eq_adjoint, sum_inner, inner_sum,
      ContinuousLinearMap.adjoint_inner_right]
    exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  rw [hrew]
  exact Finset.sum_congr rfl fun _ _ => inner_self_eq_norm_sq_to_K _

/-- The quadratic form of the scalar matrix `c • 1` is `c ∑ᵢ ‖ξᵢ‖²`. -/
theorem sum_inner_algebraMap_apply [DecidableEq ι] (c : ℝ) (ξ : ι → H) :
    ∑ i, ∑ j, ⟪ξ i, (algebraMap ℝ (CStarMatrix ι ι (H →L[ℂ] H)) c) i j (ξ j)⟫_ℂ =
      (c : ℂ) * ∑ i, ((‖ξ i‖ : ℂ) ^ 2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [CStarMatrix.algebraMap_apply, hj.symm])
    (by simp)]
  simp [CStarMatrix.algebraMap_apply, Algebra.algebraMap_eq_smul_one, inner_self_eq_norm_sq_to_K]

/-- An operator matrix `M` over a Hilbert space `H` acts on families `ξ : ι → H` with norm at
most `‖M‖`: `∑ₖ ‖∑ₗ Mₖₗ ξₗ‖² ≤ ‖M‖² ∑ₗ ‖ξₗ‖²`. -/
theorem sum_norm_sq_le [CompleteSpace H] (M : CStarMatrix ι ι (H →L[ℂ] H))
    (ξ : ι → H) : ∑ k, ‖∑ l, M k l (ξ l)‖ ^ 2 ≤ ‖M‖ ^ 2 * ∑ l, ‖ξ l‖ ^ 2 := by
  classical
  have hP : 0 ≤ star M * M := star_mul_self_nonneg M
  have hle : star M * M ≤ algebraMap ℝ _ ‖star M * M‖ :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hP).1 le_rfl
  have h0 := CStarMatrix.nonneg_iff_forall_sum_inner_nonneg.1 (sub_nonneg.2 hle) ξ
  simp only [CStarMatrix.sub_apply, _root_.sub_apply, inner_sub_right,
    Finset.sum_sub_distrib, sum_inner_algebraMap_apply, sum_inner_star_mul_self_apply] at h0
  have hM : ‖star M * M‖ = ‖M‖ ^ 2 := (CStarRing.norm_star_mul_self (x := M)).trans (sq _).symm
  have : (0 : ℂ) ≤ ((‖star M * M‖ * ∑ l, ‖ξ l‖ ^ 2 - ∑ k, ‖∑ l, M k l (ξ l)‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h0
  rw [← hM]
  exact sub_nonneg.1 (Complex.zero_le_real.1 this)

/-- An operator matrix `M` over a Hilbert space `H` with `∑ₖ ‖∑ₗ Mₖₗ ξₗ‖² ≤ C² ∑ₗ ‖ξₗ‖²` for all
`ξ : ι → H` has norm at most `C`. -/
theorem norm_le_of_sum_norm_sq_le [CompleteSpace H]
    {M : CStarMatrix ι ι (H →L[ℂ] H)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ξ : ι → H, ∑ k, ‖∑ l, M k l (ξ l)‖ ^ 2 ≤ C ^ 2 * ∑ l, ‖ξ l‖ ^ 2) : ‖M‖ ≤ C := by
  classical
  have hP : 0 ≤ star M * M := star_mul_self_nonneg M
  have hle : star M * M ≤ algebraMap ℝ _ (C ^ 2) := by
    rw [← sub_nonneg]
    refine CStarMatrix.nonneg_iff_forall_sum_inner_nonneg.2 fun ξ => ?_
    simp only [CStarMatrix.sub_apply, _root_.sub_apply, inner_sub_right,
      Finset.sum_sub_distrib, sum_inner_algebraMap_apply, sum_inner_star_mul_self_apply]
    have : (0 : ℂ) ≤ ((C ^ 2 * ∑ l, ‖ξ l‖ ^ 2 - ∑ k, ‖∑ l, M k l (ξ l)‖ ^ 2 : ℝ) : ℂ) :=
      Complex.zero_le_real.2 (sub_nonneg.2 (h ξ))
    push_cast at this ⊢; exact this
  have h2 := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg C) hP).2 hle
  have hM : ‖star M * M‖ = ‖M‖ ^ 2 := (CStarRing.norm_star_mul_self (x := M)).trans (sq _).symm
  exact (sq_le_sq₀ (norm_nonneg _) hC).1 (hM ▸ h2)
end CStarMatrix

/-! ### Slicing the second factor by vector functionals -/

namespace TauCeti

variable {A H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The vector `∑ᵢ ξᵢ ⊗ eᵢ` of the completed tensor product. -/
private def tensorSum {ι : Type*} [Fintype ι] (e : ι → F) (ξ : ι → H) :
    Completion (H ⊗[ℂ] F) :=
  ((∑ i, ξ i ⊗ₜ[ℂ] e i : H ⊗[ℂ] F) : Completion (H ⊗[ℂ] F))

private theorem inner_tensorSum {ι : Type*} [Fintype ι] {e : ι → F} (he : Orthonormal ℂ e)
    (ζ ξ : ι → H) : ⟪tensorSum e ζ, tensorSum e ξ⟫_ℂ = ∑ i, ⟪ζ i, ξ i⟫_ℂ := by
  classical
  simp [tensorSum, Completion.inner_coe, sum_inner, inner_sum, orthonormal_iff_ite.1 he]

private theorem norm_tensorSum_sq {ι : Type*} [Fintype ι] {e : ι → F} (he : Orthonormal ℂ e)
    (ξ : ι → H) : ‖tensorSum e ξ‖ ^ 2 = ∑ i, ‖ξ i‖ ^ 2 := by
  have h := inner_tensorSum he ξ ξ
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

private theorem coe_sum_tensor {ι : Type*} [Fintype ι] (s : ι → H ⊗[ℂ] F) :
    ((∑ i, s i : H ⊗[ℂ] F) : Completion (H ⊗[ℂ] F)) = ∑ i, (s i : Completion (H ⊗[ℂ] F)) := by
  have := map_sum (Completion.toComplₗᵢ (𝕜 := ℂ) (E := H ⊗[ℂ] F)) s Finset.univ
  rwa [Completion.coe_toComplₗᵢ] at this

variable [AddCommGroup A] [Module ℂ A]

/-- The **vector slice** `A ⊗ B(F) → A`, `a ⊗ b ↦ ⟪f, b g⟫ • a`: the identity on the first factor
tensored with the vector functional `b ↦ ⟪f, b g⟫` on the second. -/
def vectorSlice (f g : F) : A ⊗[ℂ] (F →L[ℂ] F) →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ
    ((vectorFunctional g f : (F →L[ℂ] F) →L[ℂ] ℂ) : (F →L[ℂ] F) →ₗ[ℂ] ℂ).lTensor A

/-- Unfolding `TauCeti.vectorSlice`. -/
theorem vectorSlice_def (f g : F) :
    vectorSlice (A := A) f g = (TensorProduct.rid ℂ A).toLinearMap ∘ₗ
      ((vectorFunctional g f : (F →L[ℂ] F) →L[ℂ] ℂ) : (F →L[ℂ] F) →ₗ[ℂ] ℂ).lTensor A :=
  (rfl)

/-- The vector slice sends `a ⊗ b` to `⟪f, b g⟫ • a`. -/
@[simp]
theorem vectorSlice_tmul (f g : F) (a : A) (b : F →L[ℂ] F) :
    vectorSlice f g (a ⊗ₜ b) = ⟪f, b g⟫_ℂ • a := by
  simp [vectorSlice, vectorFunctional_apply]

/-- The matrix coefficient of `(π ⊗ 1)(y)` between `η ⊗ f` and `ξ ⊗ g` is that of `π` applied to
the vector slice of `y` at `(f, g)`. -/
theorem inner_spatialTensorLinearMap_rTensor (π : A →ₗ[ℂ] H →L[ℂ] H)
    (y : A ⊗[ℂ] (F →L[ℂ] F)) (η ξ : H) (f g : F) :
    ⟪((η ⊗ₜ f : H ⊗[ℂ] F) : Completion (H ⊗[ℂ] F)),
        spatialTensorLinearMap ℂ H F H F (π.rTensor _ y)
          ((ξ ⊗ₜ g : H ⊗[ℂ] F) : Completion (H ⊗[ℂ] F))⟫_ℂ =
      ⟪η, π (vectorSlice f g y) ξ⟫_ℂ := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, add_apply, inner_add_right, hx, hy]
  | tmul a b =>
    simp [Completion.inner_coe, mul_comm]


private theorem inner_tensorSum_spatialTensorLinearMap_rTensor {ι : Type*} [Fintype ι] {e : ι → F}
    (he : Orthonormal ℂ e) (π : A →ₗ[ℂ] H →L[ℂ] H) (y : A ⊗[ℂ] (F →L[ℂ] F)) (ζ ξ : ι → H) :
    ⟪tensorSum e ζ, spatialTensorLinearMap ℂ H F H F (π.rTensor _ y) (tensorSum e ξ)⟫_ℂ =
      ⟪tensorSum e ζ, tensorSum e fun k ↦ ∑ l, π (vectorSlice (e k) (e l) y) (ξ l)⟫_ℂ := by
  rw [inner_tensorSum he]
  simp only [tensorSum, coe_sum_tensor, map_sum, sum_inner, inner_sum,
    inner_spatialTensorLinearMap_rTensor]
  exact Finset.sum_comm

/-- For an orthonormal family `e`, the operator matrix `[π (vectorSlice (eₖ) (eₗ) y)]ₖₗ` is a
compression of `(π ⊗ 1)(y)`, so its norm is at most `‖(π ⊗ 1)(y)‖`. -/
theorem norm_ofMatrix_le_norm_spatialTensorLinearMap_rTensor [CompleteSpace H] {ι : Type*}
    [Fintype ι] {e : ι → F} (he : Orthonormal ℂ e) (π : A →ₗ[ℂ] H →L[ℂ] H)
    (y : A ⊗[ℂ] (F →L[ℂ] F)) :
    ‖CStarMatrix.ofMatrix fun k l ↦ π (vectorSlice (e k) (e l) y)‖ ≤
      ‖spatialTensorLinearMap ℂ H F H F (π.rTensor _ y)‖ := by
  refine CStarMatrix.norm_le_of_sum_norm_sq_le (norm_nonneg _) fun ξ ↦ ?_
  set T := spatialTensorLinearMap ℂ H F H F (π.rTensor _ y)
  set ζ : ι → H := fun k ↦ ∑ l, π (vectorSlice (e k) (e l) y) (ξ l)
  have h := inner_tensorSum_spatialTensorLinearMap_rTensor he π y ζ ξ
  rw [inner_self_eq_norm_sq_to_K] at h
  have h1 : ‖tensorSum e ζ‖ ^ 2 ≤ ‖tensorSum e ζ‖ * (‖T‖ * ‖tensorSum e ξ‖) := by
    have := norm_inner_le_norm (𝕜 := ℂ) (tensorSum e ζ) (T (tensorSum e ξ))
    rw [h] at this
    simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _))
  have h2 : ‖tensorSum e ζ‖ ≤ ‖T‖ * ‖tensorSum e ξ‖ := by
    rcases (norm_nonneg (tensorSum e ζ)).eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · nlinarith
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, norm_tensorSum_sq he, norm_tensorSum_sq he] at h3
  exact h3

omit [AddCommGroup A] [Module ℂ A] in
/-- An operator `T` on the completed tensor product `H ⊗₂ F` with
`‖⟪z, T x⟫‖ ≤ C ‖z‖ ‖x‖` for all `z`, `x` in the algebraic tensor product has norm at most
`C`. -/
theorem opNorm_le_of_forall_inner_coe_le
    (T : Completion (H ⊗[ℂ] F) →L[ℂ] Completion (H ⊗[ℂ] F)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z x : H ⊗[ℂ] F, ‖⟪(z : Completion (H ⊗[ℂ] F)), T x⟫_ℂ‖ ≤ C * ‖z‖ * ‖x‖) :
    ‖T‖ ≤ C := by
  have h' : ∀ u w : Completion (H ⊗[ℂ] F), ‖⟪u, T w⟫_ℂ‖ ≤ C * ‖u‖ * ‖w‖ := fun u w ↦ by
    induction u, w using Completion.induction_on₂ with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih z x => simpa only [Completion.norm_coe] using h z x
  refine T.opNorm_le_bound hC fun w ↦ ?_
  have h1 := h' (T w) w
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at h1
  rcases (norm_nonneg (T w)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith

omit [AddCommGroup A] [Module ℂ A] in
/-- Every element of `H ⊗ V` for a finite-dimensional subspace `V` of `F` is `∑ᵢ ξᵢ ⊗ eᵢ` along
an orthonormal basis `e` of `V`. -/
private theorem exists_eq_sum_tmul {V : Submodule ℂ F} {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ V)
    (w : H ⊗[ℂ] V) : ∃ ξ : Fin n → H, V.subtype.lTensor H w = ∑ i, ξ i ⊗ₜ (b i : F) := by
  induction w using TensorProduct.inductionOn with
  | tmul h v =>
    refine ⟨fun i ↦ b.repr v i • h, ?_⟩
    have hv : (v : F) = ∑ i, b.repr v i • (b i : F) := by
      conv_lhs => rw [← b.sum_repr v]
      simp
    simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, hv, tmul_sum, smul_tmul]
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨ξ₁, h₁⟩ := h₁
    obtain ⟨ξ₂, h₂⟩ := h₂
    exact ⟨ξ₁ + ξ₂, by simp [h₁, h₂, add_tmul, Finset.sum_add_distrib]⟩

/-- The norm of `(π ⊗ 1)(y)` is at most any bound `C` on the norms of the operator matrices
`[π (vectorSlice (eₖ) (eₗ) y)]ₖₗ` over all finite orthonormal families `e` in `F`. -/
theorem norm_spatialTensorLinearMap_rTensor_le_of_forall [CompleteSpace H]
    (π : A →ₗ[ℂ] H →L[ℂ] H) (y : A ⊗[ℂ] (F →L[ℂ] F)) {C : ℝ}
    (h : ∀ (n : ℕ) (e : Fin n → F), Orthonormal ℂ e →
      ‖CStarMatrix.ofMatrix fun k l ↦ π (vectorSlice (e k) (e l) y)‖ ≤ C) :
    ‖spatialTensorLinearMap ℂ H F H F (π.rTensor _ y)‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (h 0 Fin.elim0 ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩)
  refine opNorm_le_of_forall_inner_coe_le _ hC fun z x ↦ ?_
  obtain ⟨V, hV, hs⟩ := exists_finite_submodule_right_of_setFinite ({z, x} : Set (H ⊗[ℂ] F))
    (Set.toFinite _)
  obtain ⟨z', rfl⟩ := hs (Set.mem_insert _ _)
  obtain ⟨x', rfl⟩ := hs (Set.mem_insert_of_mem _ rfl)
  let b := stdOrthonormalBasis ℂ V
  set e : Fin _ → F := fun i ↦ (b i : F)
  have he : Orthonormal ℂ e := b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  obtain ⟨ζ, hζ⟩ := exists_eq_sum_tmul b z'
  obtain ⟨ξ, hξ⟩ := exists_eq_sum_tmul b x'
  have hz : ((V.subtype.lTensor H z' : H ⊗[ℂ] F) : Completion (H ⊗[ℂ] F)) = tensorSum e ζ := by
    rw [hζ]; rfl
  have hx : ((V.subtype.lTensor H x' : H ⊗[ℂ] F) : Completion (H ⊗[ℂ] F)) = tensorSum e ξ := by
    rw [hξ]; rfl
  rw [← Completion.norm_coe (V.subtype.lTensor H z'),
    ← Completion.norm_coe (V.subtype.lTensor H x'), hz, hx,
    inner_tensorSum_spatialTensorLinearMap_rTensor he]
  set M := CStarMatrix.ofMatrix fun k l ↦ π (vectorSlice (e k) (e l) y)
  have hM : ‖tensorSum e fun k ↦ ∑ l, π (vectorSlice (e k) (e l) y) (ξ l)‖ ≤
      ‖M‖ * ‖tensorSum e ξ‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow, norm_tensorSum_sq he, norm_tensorSum_sq he]
    exact CStarMatrix.sum_norm_sq_le M ξ
  calc _ ≤ ‖tensorSum e ζ‖ * ‖tensorSum e fun k ↦ ∑ l, π (vectorSlice (e k) (e l) y) (ξ l)‖ :=
        norm_inner_le_norm _ _
    _ ≤ ‖tensorSum e ζ‖ * (C * ‖tensorSum e ξ‖) := by
        gcongr
        exact hM.trans (mul_le_mul_of_nonneg_right (h _ e he) (norm_nonneg _))
    _ = C * ‖tensorSum e ζ‖ * ‖tensorSum e ξ‖ := by ring


/-! ### The flip -/

section Flip

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

/-- The flip of completed tensor products intertwines `spatialTensorLinearMap` and its flipped
version. -/
theorem spatialTensorLinearMap_comm_apply (x : (E →L[𝕜] E') ⊗[𝕜] (F →L[𝕜] F'))
    (u : Completion (E ⊗[𝕜] F)) :
    spatialTensorLinearMap 𝕜 F E F' E' (TensorProduct.comm 𝕜 _ _ x)
        ((commIsometry 𝕜 E F).completion u) =
      (commIsometry 𝕜 E' F').completion (spatialTensorLinearMap 𝕜 E F E' F' x u) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simpa using mapLCompletion_commIsometry_completion a b u
  | add x y hx hy => simp only [map_add, add_apply, hx, hy]

/-- The flip does not increase the norm of `spatialTensorLinearMap`. -/
theorem norm_spatialTensorLinearMap_comm_le (x : (E →L[𝕜] E') ⊗[𝕜] (F →L[𝕜] F')) :
    ‖spatialTensorLinearMap 𝕜 F E F' E' (TensorProduct.comm 𝕜 _ _ x)‖ ≤
      ‖spatialTensorLinearMap 𝕜 E F E' F' x‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  obtain ⟨u, rfl⟩ := (commIsometry 𝕜 E F).completion.surjective v
  rw [spatialTensorLinearMap_comm_apply, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]
  exact le_opNorm _ _

/-- **Flip invariance**: `‖(b ⊗ a)‖ = ‖(a ⊗ b)‖` for the spatial operator of a tensor and of its
flip. -/
theorem norm_spatialTensorLinearMap_comm (x : (E →L[𝕜] E') ⊗[𝕜] (F →L[𝕜] F')) :
    ‖spatialTensorLinearMap 𝕜 F E F' E' (TensorProduct.comm 𝕜 _ _ x)‖ =
      ‖spatialTensorLinearMap 𝕜 E F E' F' x‖ := by
  refine (norm_spatialTensorLinearMap_comm_le x).antisymm ?_
  simpa using norm_spatialTensorLinearMap_comm_le (TensorProduct.comm 𝕜 _ _ x)

end Flip

/-! ### Representation independence -/

variable {A B H K F : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **One-sided comparison**: for a star homomorphism `π` and an injective star homomorphism `σ`
of a C*-algebra `A`, `‖(π ⊗ 1)(y)‖ ≤ ‖(σ ⊗ 1)(y)‖` for all `y ∈ A ⊗ B(F)`. -/
theorem norm_spatialTensorLinearMap_rTensor_le (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hσ : Function.Injective σ) (y : A ⊗[ℂ] (F →L[ℂ] F)) :
    ‖spatialTensorLinearMap ℂ H F H F ((π : A →ₗ[ℂ] H →L[ℂ] H).rTensor _ y)‖ ≤
      ‖spatialTensorLinearMap ℂ K F K F ((σ : A →ₗ[ℂ] K →L[ℂ] K).rTensor _ y)‖ := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  refine norm_spatialTensorLinearMap_rTensor_le_of_forall _ y fun n e he ↦ ?_
  let S : CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrix fun k l ↦ vectorSlice (e k) (e l) y
  calc ‖CStarMatrix.mapₙₐ π S‖ ≤ ‖S‖ := NonUnitalStarAlgHom.norm_apply_le _ _
    _ = ‖CStarMatrix.mapₙₐ σ S‖ :=
        (NonUnitalStarAlgHom.norm_map _ (CStarMatrix.map_injective hσ) S).symm
    _ ≤ _ := norm_ofMatrix_le_norm_spatialTensorLinearMap_rTensor he _ y

/-- **One-sided comparison in the second factor**: for a star homomorphism `π` and an injective
star homomorphism `σ` of a C*-algebra `B`, `‖(1 ⊗ π)(y)‖ ≤ ‖(1 ⊗ σ)(y)‖` for all
`y ∈ B(E) ⊗ B`. -/
theorem norm_spatialTensorLinearMap_lTensor_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hσ : Function.Injective σ) (y : (E →L[ℂ] E) ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ E H E H ((π : B →ₗ[ℂ] H →L[ℂ] H).lTensor _ y)‖ ≤
      ‖spatialTensorLinearMap ℂ E K E K ((σ : B →ₗ[ℂ] K →L[ℂ] K).lTensor _ y)‖ := by
  calc _ = ‖spatialTensorLinearMap ℂ H E H E
        ((π : B →ₗ[ℂ] H →L[ℂ] H).rTensor _ (TensorProduct.comm ℂ _ _ y))‖ := by
        rw [LinearMap.rTensor_comm, norm_spatialTensorLinearMap_comm]
    _ ≤ ‖spatialTensorLinearMap ℂ K E K E
        ((σ : B →ₗ[ℂ] K →L[ℂ] K).rTensor _ (TensorProduct.comm ℂ _ _ y))‖ :=
        norm_spatialTensorLinearMap_rTensor_le π σ hσ _
    _ = _ := by rw [LinearMap.rTensor_comm, norm_spatialTensorLinearMap_comm]

variable {H₁ H₂ K₁ K₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-- Faithful representations give the **largest** spatial operator norm: for star homomorphisms
`π₁`, `π₂` and injective star homomorphisms `σ₁`, `σ₂` of C*-algebras `A`, `B`,
`‖(π₁ ⊗ π₂)(x)‖ ≤ ‖(σ₁ ⊗ σ₂)(x)‖` for all `x ∈ A ⊗ B`. -/
theorem norm_spatialTensorLinearMap_map_le (π₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁))
    (π₂ : B →⋆ₙₐ[ℂ] (H₂ →L[ℂ] H₂)) (σ₁ : A →⋆ₙₐ[ℂ] (K₁ →L[ℂ] K₁))
    (σ₂ : B →⋆ₙₐ[ℂ] (K₂ →L[ℂ] K₂)) (hσ₁ : Function.Injective σ₁)
    (hσ₂ : Function.Injective σ₂) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H₁ H₂ H₁ H₂ (map (π₁ : A →ₗ[ℂ] H₁ →L[ℂ] H₁)
        (π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂) x)‖ ≤
      ‖spatialTensorLinearMap ℂ K₁ K₂ K₁ K₂ (map (σ₁ : A →ₗ[ℂ] K₁ →L[ℂ] K₁)
        (σ₂ : B →ₗ[ℂ] K₂ →L[ℂ] K₂) x)‖ := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply,
    ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  calc _ ≤ ‖spatialTensorLinearMap ℂ K₁ H₂ K₁ H₂ ((σ₁ : A →ₗ[ℂ] K₁ →L[ℂ] K₁).rTensor _
          ((π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂).lTensor _ x))‖ :=
        norm_spatialTensorLinearMap_rTensor_le π₁ σ₁ hσ₁ _
    _ = ‖spatialTensorLinearMap ℂ K₁ H₂ K₁ H₂ ((π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂).lTensor _
          ((σ₁ : A →ₗ[ℂ] K₁ →L[ℂ] K₁).rTensor _ x))‖ := by
        congr 2
        rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.comp_apply,
          LinearMap.lTensor_comp_rTensor]
    _ ≤ _ := norm_spatialTensorLinearMap_lTensor_le π₂ σ₂ hσ₂ _

/-- **Representation independence of the spatial norm** (Takesaki I, Theorem IV.4.9): for
faithful representations `π₁`, `σ₁` of `A` and `π₂`, `σ₂` of `B`,
`‖(π₁ ⊗ π₂)(x)‖ = ‖(σ₁ ⊗ σ₂)(x)‖` for all `x ∈ A ⊗ B`. -/
theorem norm_spatialTensorLinearMap_map_eq (π₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁))
    (π₂ : B →⋆ₙₐ[ℂ] (H₂ →L[ℂ] H₂)) (σ₁ : A →⋆ₙₐ[ℂ] (K₁ →L[ℂ] K₁))
    (σ₂ : B →⋆ₙₐ[ℂ] (K₂ →L[ℂ] K₂)) (hπ₁ : Function.Injective π₁)
    (hπ₂ : Function.Injective π₂) (hσ₁ : Function.Injective σ₁)
    (hσ₂ : Function.Injective σ₂) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H₁ H₂ H₁ H₂ (map (π₁ : A →ₗ[ℂ] H₁ →L[ℂ] H₁)
        (π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂) x)‖ =
      ‖spatialTensorLinearMap ℂ K₁ K₂ K₁ K₂ (map (σ₁ : A →ₗ[ℂ] K₁ →L[ℂ] K₁)
        (σ₂ : B →ₗ[ℂ] K₂ →L[ℂ] K₂) x)‖ :=
  (norm_spatialTensorLinearMap_map_le π₁ π₂ σ₁ σ₂ hσ₁ hσ₂ x).antisymm
    (norm_spatialTensorLinearMap_map_le σ₁ σ₂ π₁ π₂ hπ₁ hπ₂ x)

end TauCeti

namespace NonUnitalStarSubalgebra

open TauCeti

variable {E F H₁ H₂ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  (A : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E)) (B : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F))
  [IsClosed (A : Set (E →L[ℂ] E))] [IsClosed (B : Set (F →L[ℂ] F))]

/-- The spatial norm of closed concrete operator algebras bounds `‖(π₁ ⊗ π₂)(x)‖` for all star
homomorphisms `π₁`, `π₂`. -/
theorem norm_spatialTensorLinearMap_map_le_spatialNorm (π₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁))
    (π₂ : B →⋆ₙₐ[ℂ] (H₂ →L[ℂ] H₂)) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H₁ H₂ H₁ H₂ (TensorProduct.map (π₁ : A →ₗ[ℂ] H₁ →L[ℂ] H₁)
        (π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂) x)‖ ≤ spatialNorm A B x := by
  rw [spatialNorm_def, spatialTensorHom_apply]
  exact norm_spatialTensorLinearMap_map_le π₁ π₂ (NonUnitalStarSubalgebraClass.subtype A)
    (NonUnitalStarSubalgebraClass.subtype B) Subtype.val_injective Subtype.val_injective x

/-- **Representation independence of the spatial norm** (Takesaki I, Theorem IV.4.9): for closed
concrete operator algebras `A ⊆ B(E)`, `B ⊆ B(F)` and faithful representations `π₁` of `A` and
`π₂` of `B`, `‖(π₁ ⊗ π₂)(x)‖ = ‖x‖_min`. -/
theorem norm_spatialTensorLinearMap_map_eq_spatialNorm (π₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁))
    (π₂ : B →⋆ₙₐ[ℂ] (H₂ →L[ℂ] H₂)) (hπ₁ : Function.Injective π₁)
    (hπ₂ : Function.Injective π₂) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H₁ H₂ H₁ H₂ (TensorProduct.map (π₁ : A →ₗ[ℂ] H₁ →L[ℂ] H₁)
        (π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂) x)‖ = spatialNorm A B x := by
  rw [spatialNorm_def, spatialTensorHom_apply]
  exact norm_spatialTensorLinearMap_map_eq π₁ π₂ (NonUnitalStarSubalgebraClass.subtype A)
    (NonUnitalStarSubalgebraClass.subtype B) hπ₁ hπ₂ Subtype.val_injective
    Subtype.val_injective x

end NonUnitalStarSubalgebra
