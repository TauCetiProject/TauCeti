/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.House
import Mathlib.LinearAlgebra.Matrix.Bilinear
import TauCeti.LinearAlgebra.Basis.Submodule
import TauCeti.RingTheory.Trace.EmbeddingsMatrix

/-!
# Integer combinations of a rational basis and their conjugate configurations

Let `K` be a number field and `α : ι → 𝓞 K` a family of algebraic integers. An integer matrix
`u : Matrix ι σ ℤ` gives the tuple of algebraic integers

  `κ_j(u) = ∑ᵢ u i j • α i`,  `j ∈ σ`,

the integral parameter family `TauCeti.NumberField.parameterTuple α u`. Placing the conjugates
of this tuple side by side gives, for each complex embedding `τ : K →+* ℂ`, a point
`(τ (κ_j(u)))_j` of `ℂ^σ`. Allowing complex parameters, this is the `ℂ`-linear map

  `conjugateConfiguration α : Matrix ι σ ℂ →ₗ[ℂ] ((K →+* ℂ) → σ → ℂ)`,
  `v ↦ (τ, j) ↦ ∑ᵢ v i j * τ (α i)`,

which transforms each column of `v` by the embedding matrix `(τ (α i))_{τ, i}`.

When the `α i` form a `ℚ`-basis of `K`, not necessarily an integral basis, the embedding matrix is
invertible, so `conjugateConfiguration α` is a linear equivalence between the `[K : ℚ] * |σ|`
dimensional space of complex parameters and the space of embedding-indexed configurations
(`conjugateConfigurationEquiv`). Its inverse need not have integral entries. This lets a nonzero
polynomial condition on configurations be pulled back to a nonzero polynomial in the parameters,
whose nonvanishing on a box of integers then gives integral generators with that condition. When
also every `α i` has house at most `c` and every `|u i j|` is at most `D`, each `κ_j(u)` has house
at most `[K : ℚ] * D * c`.

## Main definitions

* `TauCeti.NumberField.parameterTuple α`: the `ℤ`-linear map `u ↦ (∑ᵢ u i j • α i)_j`.
* `TauCeti.NumberField.conjugateConfiguration α`: the `ℂ`-linear map
  `v ↦ (∑ᵢ v i j * τ (α i))_{τ, j}`.
* `TauCeti.NumberField.conjugateConfigurationEquiv b`: the same map for a `ℚ`-basis `b` of `K`,
  as a linear equivalence.

## Main results

* `TauCeti.NumberField.map_parameterTuple_apply` and
  `TauCeti.NumberField.conjugateConfiguration_intCast`: a complex embedding `τ` sends `κ_j(u)` to
  `∑ᵢ u i j * τ (α i)`, so on integer parameters the configuration map gives the conjugates of the
  parameter tuple.
* `TauCeti.NumberField.linearIndependent_canonicalEmbedding_comp_iff`: the conjugate vectors of
  a family are `ℂ`-linearly independent if and only if the family is `ℚ`-linearly independent.
* `TauCeti.NumberField.finrank_span_canonicalEmbedding_image` and
  `TauCeti.NumberField.span_canonicalEmbedding_image_eq_top_iff`: the conjugate vectors of a
  `ℚ`-subspace `W` of `K` span a complex subspace of dimension `finrank ℚ W`, which is everything
  if and only if `W = ⊤`.
* `TauCeti.NumberField.conjugateConfiguration_injective_iff` and
  `TauCeti.NumberField.conjugateConfiguration_bijective`: the configuration map is injective
  for a `ℚ`-linearly independent family, and for nonempty `σ` only then, and bijective for a
  `ℚ`-basis.
* `TauCeti.NumberField.house_parameterTuple_le_mul`: the bound `house κ_j ≤ |ι| * D * c`.
* `TauCeti.NumberField.parameterTuple_comp_symm` and
  `TauCeti.NumberField.parameterTuple_sum_smul_inv`: reindexing and integral changes of the
  family.

## References

* J.-M. Couveignes, *Enumerating number fields*, Ann. of Math. 192 (2020), 487–497, §3,
  pp. 491–492.
-/

public section

open Module NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] {ι ι' σ : Type*} [Fintype ι]

/-! ### The integral parameter family -/

/-- The integral parameter family of a family `α` of algebraic integers: an integer matrix `u`
gives the tuple `j ↦ ∑ᵢ u i j • α i` of algebraic integers. -/
noncomputable def parameterTuple (α : ι → 𝓞 K) : Matrix ι σ ℤ →ₗ[ℤ] σ → 𝓞 K where
  toFun u j := ∑ i, u i j • α i
  map_add' u v := by ext j; simp [add_smul, Finset.sum_add_distrib]
  map_smul' c u := by ext j; simp [mul_smul, Finset.smul_sum]

@[simp]
theorem parameterTuple_apply (α : ι → 𝓞 K) (u : Matrix ι σ ℤ) (j : σ) :
    parameterTuple α u j = ∑ i, u i j • α i := (rfl)

theorem coe_parameterTuple_apply (α : ι → 𝓞 K) (u : Matrix ι σ ℤ) (j : σ) :
    (parameterTuple α u j : K) = ∑ i, (u i j : K) * α i := by
  simp [zsmul_eq_mul]

/-- A ring homomorphism out of `K`, such as a complex embedding, sends the `j`-th entry of the
parameter tuple to `∑ᵢ u i j * f (α i)`. -/
theorem map_parameterTuple_apply {R : Type*} [Ring R] (f : K →+* R) (α : ι → 𝓞 K)
    (u : Matrix ι σ ℤ) (j : σ) :
    f (parameterTuple α u j : K) = ∑ i, (u i j : R) * f (α i) := by
  simp

/-- Reindexing the family `α` and the rows of the parameter matrix `u` together leaves the
parameter tuple unchanged. -/
theorem parameterTuple_comp_symm [Fintype ι'] (α : ι → 𝓞 K) (e : ι ≃ ι') (u : Matrix ι σ ℤ) :
    parameterTuple (α ∘ e.symm) (u.submatrix e.symm id) = parameterTuple α u := by
  funext j
  simp only [parameterTuple_apply, Matrix.submatrix_apply, Function.comp_apply, id_eq]
  exact e.symm.sum_comp fun i ↦ u i j • α i

/-- Changing the family `α` by an integer matrix `A`, to `α' i = ∑ₖ A i k • α k`, changes the
parameters by the transpose of `A`: the tuple of `α'` at `u` is the tuple of `α` at `Aᵀ * u`. -/
theorem parameterTuple_sum_smul (α : ι → 𝓞 K) (A : Matrix ι ι ℤ) (u : Matrix ι σ ℤ) :
    parameterTuple (fun i ↦ ∑ k, A i k • α k) u = parameterTuple α (A.transpose * u) := by
  ext j
  simp only [parameterTuple_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp_rw [mul_comm]

/-- An invertible integral change `α' i = ∑ₖ A i k • α k` of the family acts on parameters by the
inverse transpose: the tuple of `α'` at `(A⁻¹)ᵀ * v` is the tuple of `α` at `v`. -/
theorem parameterTuple_sum_smul_inv [DecidableEq ι] (α : ι → 𝓞 K) {A : Matrix ι ι ℤ}
    (hA : IsUnit A.det) (v : Matrix ι σ ℤ) :
    parameterTuple (fun i ↦ ∑ k, A i k • α k) (A⁻¹.transpose * v) = parameterTuple α v := by
  rw [parameterTuple_sum_smul, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul A hA, Matrix.transpose_one, Matrix.one_mul]

/-! ### The house of the parameter tuple -/

variable [NumberField K]

/-- The house of `∑ᵢ u i j • α i` is at most `∑ᵢ |u i j| * house (α i)`. -/
theorem house_parameterTuple_le (α : ι → 𝓞 K) (u : Matrix ι σ ℤ) (j : σ) :
    house (parameterTuple α u j : K) ≤ ∑ i, |(u i j : ℝ)| * house (α i : K) := by
  rw [coe_parameterTuple_apply]
  refine (house_sum_le_sum_house _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  simpa using house_mul_le (u i j : K) (α i : K)

/-- If every entry of the column `j` of `u` has absolute value at most `D` and every `α i` has
house at most `c`, then the `j`-th entry of the parameter tuple has house at most `|ι| * D * c`. -/
theorem house_parameterTuple_le_mul (α : ι → 𝓞 K) {u : Matrix ι σ ℤ} {D c : ℝ} {j : σ}
    (hu : ∀ i, |(u i j : ℝ)| ≤ D) (hα : ∀ i, house (α i : K) ≤ c) :
    house (parameterTuple α u j : K) ≤ Fintype.card ι * D * c := by
  calc house (parameterTuple α u j : K) ≤ ∑ i, |(u i j : ℝ)| * house (α i : K) :=
        house_parameterTuple_le α u j
    _ ≤ ∑ _ : ι, D * c := Finset.sum_le_sum fun i _ ↦
        mul_le_mul (hu i) (hα i) (house_nonneg _) ((abs_nonneg _).trans (hu i))
    _ = Fintype.card ι * D * c := by simp [mul_assoc]

/-! ### The conjugate configuration map -/

omit [NumberField K] in
/-- The conjugate configuration map of a family `α` in `K`: a complex parameter matrix `v` goes to
the configuration whose point at the complex embedding `τ` is `(∑ᵢ v i j * τ (α i))_j`. Each
column of `v` is transformed by the embedding matrix `(τ (α i))_{τ, i}`. -/
noncomputable def conjugateConfiguration (α : ι → K) :
    Matrix ι σ ℂ →ₗ[ℂ] (K →+* ℂ) → σ → ℂ :=
  mulLeftLinearMap σ ℂ (Matrix.of fun (τ : K →+* ℂ) i ↦ τ (α i))

omit [NumberField K] in
@[simp]
theorem conjugateConfiguration_apply (α : ι → K) (v : Matrix ι σ ℂ) (τ : K →+* ℂ) (j : σ) :
    conjugateConfiguration α v τ j = ∑ i, v i j * τ (α i) :=
  -- The configuration is the matrix product `(τ (α i))_{τ, i} * v`, read as a function.
  Matrix.mul_apply.trans (Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _)

omit [NumberField K] in
/-- On integer parameters, the conjugate configuration map gives the conjugates of the parameter
tuple: its point at `τ` is `(τ (κ_j(u)))_j`. -/
theorem conjugateConfiguration_intCast (α : ι → 𝓞 K) (u : Matrix ι σ ℤ) (τ : K →+* ℂ) (j : σ) :
    conjugateConfiguration (fun i ↦ (α i : K)) (u.map (Int.cast : ℤ → ℂ)) τ j =
      τ (parameterTuple α u j : K) := by
  simp

omit [Fintype ι] in
/-- The vectors of conjugates `(τ (α i))_τ` of a family `α` in a number field are linearly
independent over `ℂ` if and only if `α` is linearly independent over `ℚ`. -/
theorem linearIndependent_canonicalEmbedding_comp_iff {α : ι → K} :
    LinearIndependent ℂ (canonicalEmbedding K ∘ α) ↔ LinearIndependent ℚ α := by
  have hcard : Nat.card (K →ₐ[ℚ] ℂ) = finrank ℚ K := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  rw [← Algebra.linearIndependent_embeddingsMatrix_row_iff (F := ℚ) (Ω := ℂ) hcard]
  -- The conjugate vectors are the rows of the embeddings matrix, read through
  -- `K →+* ℂ ≃ K →ₐ[ℚ] ℂ`.
  let e := LinearEquiv.funCongrLeft ℂ ℂ (RingHom.equivRatAlgHom K ℂ)
  have he : e ∘ (Algebra.embeddingsMatrix ℚ ℂ α).row = canonicalEmbedding K ∘ α := by
    ext i τ
    simp [e, canonicalEmbedding.apply_at]
  rw [← e.toLinearMap.linearIndependent_iff (LinearEquiv.ker e), LinearEquiv.coe_coe, he]

/-- The vectors of conjugates `(τ x)_τ` of the elements `x` of a `ℚ`-subspace `W` of a number
field span a complex subspace of dimension `finrank ℚ W`. -/
theorem finrank_span_canonicalEmbedding_image {W : Submodule ℚ K} :
    finrank ℂ (Submodule.span ℂ (canonicalEmbedding K '' W)) = finrank ℚ W := by
  let b := Module.finBasis ℚ W
  -- The conjugate vectors of `W` and of its basis `b` have the same complex span.
  have hspan : Submodule.span ℂ (canonicalEmbedding K '' W) =
      Submodule.span ℂ (Set.range (canonicalEmbedding K ∘ W.subtype ∘ b)) :=
    b.span_image (canonicalEmbedding K).toRatAlgHom.toLinearMap
  have hli : LinearIndependent ℂ (canonicalEmbedding K ∘ W.subtype ∘ b) :=
    linearIndependent_canonicalEmbedding_comp_iff.mpr
      (b.linearIndependent.map' W.subtype (Submodule.ker_subtype W))
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin, finrank_eq_card_basis b]

/-- The conjugate vectors of the elements of a `ℚ`-subspace `W` of a number field span the
complex space of embedding-indexed families if and only if `W` is the whole field. -/
theorem span_canonicalEmbedding_image_eq_top_iff {W : Submodule ℚ K} :
    Submodule.span ℂ (canonicalEmbedding K '' W) = ⊤ ↔ W = ⊤ := by
  have hK : finrank ℂ ((K →+* ℂ) → ℂ) = finrank ℚ K := by
    rw [finrank_fintype_fun_eq_card, Embeddings.card]
  refine ⟨fun h ↦ Submodule.eq_top_of_finrank_eq ?_, fun h ↦ Submodule.eq_top_of_finrank_eq ?_⟩
  · rw [← finrank_span_canonicalEmbedding_image, h, finrank_top, hK]
  · rw [finrank_span_canonicalEmbedding_image, h, finrank_top, hK]

/-- The conjugate configuration map of a `ℚ`-linearly independent family is injective. -/
theorem conjugateConfiguration_injective {α : ι → K} (hα : LinearIndependent ℚ α) :
    Function.Injective (conjugateConfiguration (σ := σ) α) := by
  have h := Fintype.linearIndependent_iff.mp (linearIndependent_canonicalEmbedding_comp_iff.mpr hα)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  ext i j
  refine h (fun i ↦ v i j) ?_ i
  ext τ
  simpa using congr_fun (congr_fun hv τ) j

/-- For a nonempty index type `σ`, the conjugate configuration map of `α` is injective if and only
if `α` is linearly independent over `ℚ`. -/
theorem conjugateConfiguration_injective_iff [Nonempty σ] {α : ι → K} :
    Function.Injective (conjugateConfiguration (σ := σ) α) ↔ LinearIndependent ℚ α := by
  refine ⟨fun h ↦ ?_, conjugateConfiguration_injective⟩
  rw [← linearIndependent_canonicalEmbedding_comp_iff, Fintype.linearIndependent_iff]
  intro g hg i
  -- The parameter matrix whose every column is `g` is sent to zero.
  have hv : conjugateConfiguration (σ := σ) α (Matrix.of fun i _ ↦ g i) = 0 := by
    ext τ j
    rw [conjugateConfiguration_apply]
    simpa using congr_fun hg τ
  rw [← map_zero (conjugateConfiguration α)] at hv
  exact congr_fun (congr_fun (h hv) i) (Classical.arbitrary σ)

/-- The conjugate configuration map of a `ℚ`-linearly independent family of `[K : ℚ]` elements is
bijective. -/
theorem conjugateConfiguration_bijective {α : ι → K} (hα : LinearIndependent ℚ α)
    (hcard : Fintype.card ι = finrank ℚ K) :
    Function.Bijective (conjugateConfiguration (σ := σ) α) := by
  refine ⟨conjugateConfiguration_injective hα, fun w ↦ ?_⟩
  -- The conjugate vectors of `α` form a `ℂ`-basis of `(K →+* ℂ) → ℂ`; expand each column of `w`.
  have hli := linearIndependent_canonicalEmbedding_comp_iff.mpr hα
  let B := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' <| by
    rw [Module.finrank_fintype_fun_eq_card, Embeddings.card, hcard]).ge
  refine ⟨Matrix.of fun i j ↦ B.repr (fun τ ↦ w τ j) i, ?_⟩
  ext τ j
  simpa [B, mul_comm] using congr_fun (B.sum_repr fun τ ↦ w τ j) τ

/-- The conjugate configuration map of a `ℚ`-basis `b` of `K`, as a linear equivalence between
complex parameter matrices and embedding-indexed configurations. The basis need not consist of
algebraic integers, and the inverse need not have integral entries. -/
noncomputable def conjugateConfigurationEquiv (b : Basis ι ℚ K) :
    Matrix ι σ ℂ ≃ₗ[ℂ] (K →+* ℂ) → σ → ℂ :=
  LinearEquiv.ofBijective (conjugateConfiguration b)
    (conjugateConfiguration_bijective b.linearIndependent (finrank_eq_card_basis b).symm)

@[simp]
theorem conjugateConfigurationEquiv_apply (b : Basis ι ℚ K) (v : Matrix ι σ ℂ) :
    conjugateConfigurationEquiv b v = conjugateConfiguration b v := (rfl)

end TauCeti.NumberField
