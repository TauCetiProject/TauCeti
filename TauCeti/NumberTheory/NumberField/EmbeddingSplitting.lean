/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.RingTheory.TensorProduct.Free
public import TauCeti.Algebra.TensorProduct.Module
public import TauCeti.RingTheory.Idempotents.Module
import TauCeti.Algebra.Algebra.Pi
import TauCeti.NumberTheory.NumberField.Discriminant.OfIntegralBasis

/-!
# The embedding splitting of `R ⊗ 𝓞 L` and embedding eigenspaces

Let `L` be a number field with discriminant `d_L`, and let `K` be a field of characteristic zero
receiving all `[L : ℚ]` embeddings of `L`, such as a Galois closure of `L`. For a commutative
`𝓞 K`-algebra `R` in which `d_L` is a unit, that is, an `𝓞 K[1/d_L]`-algebra, the map
`r ⊗ ℓ ↦ (r σ(ℓ))_σ` is an isomorphism of `R`-algebras

`R ⊗[ℤ] 𝓞 L ≃ ∏_{σ : L →+* K} R`.

For a `ℤ`-basis `(bⱼ)` of `𝓞 L`, the matrix of the splitting from the basis `(1 ⊗ bⱼ)` to the
coordinate basis of `∏_σ R` is `(σ(bⱼ))_{σ, j}`, whose determinant squares to `d_L`. The
idempotents of the product split every `R`-module `M` with a commuting action of `𝓞 L` as an
internal direct sum `M = ⨁_σ M(σ)`, where `M(σ)` is the largest submodule on which `𝓞 L` acts
through `σ`; they act on `M` through `TauCeti.tensorToModuleEnd R (𝓞 L) M`. The
splitting is functorial in `R`-linear maps commuting with the `𝓞 L`-actions and commutes with
tensoring by an `R`-module: for an `R`-module `N`, with `𝓞 L` acting on `M ⊗[R] N` through the
factor `M`, `(M ⊗[R] N)(σ)` is the image of `M(σ) ⊗[R] N`.

## Main definitions

* `TauCeti.NumberField.embeddingEval L K R σ`: the `R`-algebra map `R ⊗[ℤ] 𝓞 L →ₐ[R] R`,
  `r ⊗ ℓ ↦ r σ(ℓ)`.
* `TauCeti.NumberField.embeddingSplitting L K R`: the product of these maps,
  `R ⊗[ℤ] 𝓞 L →ₐ[R] ((L →+* K) → R)`.
* `TauCeti.NumberField.embeddingSplittingEquiv`: the splitting as an isomorphism, when `K`
  receives all embeddings of `L` and `d_L` is a unit of `R`.
* `TauCeti.NumberField.embeddingIdempotent`: the idempotent of `R ⊗[ℤ] 𝓞 L` at an embedding,
  the preimage of a coordinate idempotent.
* `TauCeti.NumberField.embeddingEigenspace L K R M σ`: the submodule `M(σ)` of `m` with
  `ℓ • m = σ(ℓ) • m` for all `ℓ : 𝓞 L`.

## Main results

* `TauCeti.NumberField.embeddingSplitting_bijective`: the splitting is bijective.
* `TauCeti.NumberField.completeOrthogonalIdempotents_embeddingIdempotent`: the preimages of the
  coordinate idempotents form a complete orthogonal family.
* `TauCeti.NumberField.isInternal_embeddingEigenspace`: `M = ⨁_σ M(σ)`.
* `TauCeti.NumberField.embeddingEigenspace_le_comap`: an `R`-linear map commuting with the
  `𝓞 L`-actions sends `M(σ)` into `N(σ)`.
* `TauCeti.NumberField.embeddingEigenspace_tensorProduct`: for an `R`-module `N`, with `𝓞 L`
  acting on `M ⊗[R] N` through the factor `M`, `(M ⊗[R] N)(σ)` is the image of `M(σ) ⊗[R] N`.

## References

* G. Kings and J. Sprang, *Eisenstein-Kronecker classes, integrality of critical values of Hecke
  L-functions and p-adic interpolation*, Ann. of Math. 202 (2025); arXiv:1912.03657v4, §1.1,
  the splitting of `O_L ⊗ R`, p. 6.
-/

public section

open scoped NumberField TensorProduct Pointwise
open NumberField Module

namespace TauCeti.NumberField

variable (L K : Type*) [Field L] [Field K] (R : Type*) [CommRing R] [Algebra (𝓞 K) R]

section Splitting

/-- The ring map `𝓞 L →+* R` induced by an embedding `σ : L →+* K`, through `𝓞 K`. -/
noncomputable def embeddingRingHom (σ : L →+* K) : 𝓞 L →+* R :=
  (algebraMap (𝓞 K) R).comp (RingOfIntegers.mapRingHom σ)

@[simp]
theorem embeddingRingHom_apply (σ : L →+* K) (ℓ : 𝓞 L) :
    embeddingRingHom L K R σ ℓ = algebraMap (𝓞 K) R (RingOfIntegers.mapRingHom σ ℓ) :=
  (rfl)

/-- Evaluation at an embedding `σ : L →+* K`: the `R`-algebra map `R ⊗[ℤ] 𝓞 L →ₐ[R] R` sending
`r ⊗ ℓ` to `r σ(ℓ)`. -/
noncomputable def embeddingEval (σ : L →+* K) : R ⊗[ℤ] 𝓞 L →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R) (embeddingRingHom L K R σ).toIntAlgHom
    fun _ _ ↦ Commute.all _ _

@[simp]
theorem embeddingEval_tmul (σ : L →+* K) (r : R) (ℓ : 𝓞 L) :
    embeddingEval L K R σ (r ⊗ₜ ℓ) = r * embeddingRingHom L K R σ ℓ := by
  simp [embeddingEval]

/-- The **embedding splitting** `R ⊗[ℤ] 𝓞 L →ₐ[R] ∏_σ R`, `r ⊗ ℓ ↦ (r σ(ℓ))_σ`. -/
noncomputable def embeddingSplitting : R ⊗[ℤ] 𝓞 L →ₐ[R] ((L →+* K) → R) :=
  AlgHom.pi (embeddingEval L K R)

@[simp]
theorem embeddingSplitting_apply (x : R ⊗[ℤ] 𝓞 L) (σ : L →+* K) :
    embeddingSplitting L K R x σ = embeddingEval L K R σ x := by
  simp [embeddingSplitting]

end Splitting

section Eigenspace

variable (M : Type*) [AddCommMonoid M] [Module R M] [Module (𝓞 L) M] [SMulCommClass (𝓞 L) R M]

/-- The **embedding eigenspace** `M(σ)`: the largest `R`-submodule of `M` on which `𝓞 L` acts
through `σ`, namely the `m` with `ℓ • m = σ(ℓ) • m` for all `ℓ : 𝓞 L`. -/
def embeddingEigenspace (σ : L →+* K) : Submodule R M where
  carrier := {m | ∀ ℓ : 𝓞 L, ℓ • m = embeddingRingHom L K R σ ℓ • m}
  add_mem' {m n} hm hn ℓ := by simp [smul_add, hm ℓ, hn ℓ]
  zero_mem' ℓ := by simp
  smul_mem' r m hm ℓ := by simp [smul_comm ℓ r m, hm ℓ, smul_smul, mul_comm]

variable {L K R M}

@[simp]
theorem mem_embeddingEigenspace {σ : L →+* K} {m : M} :
    m ∈ embeddingEigenspace L K R M σ ↔ ∀ ℓ : 𝓞 L, ℓ • m = embeddingRingHom L K R σ ℓ • m :=
  Iff.rfl

/-- **Functoriality**: an `R`-linear map commuting with the `𝓞 L`-actions sends `M(σ)` into
`N(σ)`. -/
theorem embeddingEigenspace_le_comap {N : Type*} [AddCommMonoid N] [Module R N] [Module (𝓞 L) N]
    [SMulCommClass (𝓞 L) R N] (f : M →ₗ[R] N) (hf : ∀ (ℓ : 𝓞 L) (m : M), f (ℓ • m) = ℓ • f m)
    (σ : L →+* K) :
    embeddingEigenspace L K R M σ ≤ (embeddingEigenspace L K R N σ).comap f :=
  fun m hm ℓ ↦ by rw [← hf, hm ℓ, map_smul]

/-- On `M(σ)`, the algebra `R ⊗[ℤ] 𝓞 L` acts through evaluation at `σ`. -/
theorem tensorToModuleEnd_apply_of_mem_embeddingEigenspace {σ : L →+* K} {m : M}
    (hm : m ∈ embeddingEigenspace L K R M σ) (t : R ⊗[ℤ] 𝓞 L) :
    tensorToModuleEnd R (𝓞 L) M t m = embeddingEval L K R σ t • m := by
  induction t using TensorProduct.inductionOn with
  | tmul r ℓ => rw [tensorToModuleEnd_tmul, hm ℓ, embeddingEval_tmul, smul_smul]
  | add s t hs ht => rw [map_add, LinearMap.add_apply, hs, ht, map_add, add_smul]

end Eigenspace

section Bijective

variable [NumberField L] [CharZero K] {L K R}

variable (hK : Fintype.card (L →+* K) = finrank ℚ L)
include hK

variable (hd : IsUnit (discr L : R))
include hd

/-- **The embedding splitting is bijective** when `K` receives all `[L : ℚ]` embeddings of `L`
and `d_L` is a unit of `R`. -/
theorem embeddingSplitting_bijective : Function.Bijective (embeddingSplitting L K R) := by
  classical
  -- On the basis `1 ⊗ bⱼ` of `R ⊗[ℤ] 𝓞 L`, the splitting has matrix `(σ(bⱼ))`, whose
  -- determinant squares to `d_L`.
  let e : (L →+* K) ≃ Free.ChooseBasisIndex ℤ (𝓞 L) := Fintype.equivOfCardEq <| by
    rw [hK, ← RingOfIntegers.rank, finrank_eq_card_chooseBasisIndex]
  let bR : Basis (L →+* K) R (R ⊗[ℤ] 𝓞 L) :=
    (Algebra.TensorProduct.basis R (RingOfIntegers.basis L)).reindex e.symm
  refine AlgHom.pi_bijective_of_isUnit_det bR ?_
  have h := congrArg (algebraMap (𝓞 K) R)
    (sq_det_mapRingHom_basis_eq_discr hK (RingOfIntegers.basis L) e)
  rw [map_pow, RingHom.map_det, map_intCast] at h
  have hM : (Matrix.of fun σ τ ↦ embeddingEval L K R σ (bR τ)) = (algebraMap (𝓞 K) R).mapMatrix
      (Matrix.of fun σ τ ↦ RingOfIntegers.mapRingHom σ (RingOfIntegers.basis L (e τ))) := by
    ext σ τ
    simp [bR]
  rw [hM]
  exact (isUnit_pow_iff two_ne_zero).mp (h ▸ hd)

/-- The embedding splitting `R ⊗[ℤ] 𝓞 L ≃ₐ[R] ∏_σ R`, when `K` receives all `[L : ℚ]` embeddings
of `L` and `d_L` is a unit of `R`. -/
noncomputable def embeddingSplittingEquiv : R ⊗[ℤ] 𝓞 L ≃ₐ[R] ((L →+* K) → R) :=
  AlgEquiv.ofBijective (embeddingSplitting L K R) (embeddingSplitting_bijective hK hd)

@[simp]
theorem embeddingSplittingEquiv_apply (x : R ⊗[ℤ] 𝓞 L) :
    embeddingSplittingEquiv hK hd x = embeddingSplitting L K R x := by
  simp [embeddingSplittingEquiv]

/-- The idempotent of `R ⊗[ℤ] 𝓞 L` at an embedding `σ`: the preimage of the coordinate
idempotent at `σ` under the embedding splitting. -/
noncomputable def embeddingIdempotent (σ : L →+* K) : R ⊗[ℤ] 𝓞 L :=
  open scoped Classical in (embeddingSplittingEquiv hK hd).symm (Pi.single σ 1)

@[simp]
theorem embeddingSplitting_embeddingIdempotent [DecidableEq (L →+* K)] (σ : L →+* K) :
    embeddingSplitting L K R (embeddingIdempotent hK hd σ) = Pi.single σ 1 := by
  rw [← embeddingSplittingEquiv_apply hK hd, embeddingIdempotent, AlgEquiv.apply_symm_apply]
  congr!

@[simp]
theorem embeddingEval_embeddingIdempotent_self (σ : L →+* K) :
    embeddingEval L K R σ (embeddingIdempotent hK hd σ) = 1 := by
  classical
  rw [← embeddingSplitting_apply, embeddingSplitting_embeddingIdempotent, Pi.single_eq_same]

@[simp]
theorem embeddingEval_embeddingIdempotent_of_ne {σ τ : L →+* K} (h : τ ≠ σ) :
    embeddingEval L K R τ (embeddingIdempotent hK hd σ) = 0 := by
  classical
  rw [← embeddingSplitting_apply, embeddingSplitting_embeddingIdempotent, Pi.single_eq_of_ne h]

@[simp]
theorem embeddingSplittingEquiv_symm_single [DecidableEq (L →+* K)] (σ : L →+* K) :
    (embeddingSplittingEquiv hK hd).symm (Pi.single σ 1) = embeddingIdempotent hK hd σ := by
  rw [AlgEquiv.symm_apply_eq, embeddingSplittingEquiv_apply,
    embeddingSplitting_embeddingIdempotent]

/-- The inverse of the embedding splitting sends `f` to `∑_σ f(σ) eσ`. -/
theorem embeddingSplittingEquiv_symm_apply (f : (L →+* K) → R) :
    (embeddingSplittingEquiv hK hd).symm f = ∑ σ, f σ • embeddingIdempotent hK hd σ := by
  rw [AlgEquiv.symm_apply_eq]
  ext τ
  rw [embeddingSplittingEquiv_apply, embeddingSplitting_apply, map_sum, Finset.sum_eq_single τ]
  · simp
  · intro σ _ h
    simp [embeddingEval_embeddingIdempotent_of_ne hK hd (Ne.symm h)]
  · simp

/-- The idempotents at the embeddings form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_embeddingIdempotent :
    CompleteOrthogonalIdempotents (embeddingIdempotent (R := R) hK hd) := by
  classical
  convert (CompleteOrthogonalIdempotents.single fun _ : L →+* K ↦ R).map
    (embeddingSplittingEquiv hK hd).symm.toAlgHom.toRingHom using 1
  funext σ
  simp only [Function.comp_apply, embeddingIdempotent]
  congr!

/-- In `R ⊗[ℤ] 𝓞 L`, an element `1 ⊗ ℓ` acts on the idempotent at `σ` as the scalar `σ(ℓ)`. -/
theorem one_tmul_mul_embeddingIdempotent (σ : L →+* K) (ℓ : 𝓞 L) :
    (1 ⊗ₜ ℓ) * embeddingIdempotent hK hd σ =
      algebraMap R _ (embeddingRingHom L K R σ ℓ) * embeddingIdempotent hK hd σ := by
  apply (embeddingSplitting_bijective hK hd).injective
  ext τ
  simp only [map_mul, embeddingSplitting_apply, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, embeddingEval_tmul, one_mul]
  rcases eq_or_ne τ σ with rfl | h
  · simp [embeddingEval_embeddingIdempotent_self]
  · simp [embeddingEval_embeddingIdempotent_of_ne hK hd h]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module (𝓞 L) M] [SMulCommClass (𝓞 L) R M]

/-- The idempotent at `σ` acts on `M` with range `M(σ)`. -/
theorem tensorToModuleEnd_embeddingIdempotent_smul_top (σ : L →+* K) :
    tensorToModuleEnd R (𝓞 L) M (embeddingIdempotent hK hd σ) •
        (⊤ : Submodule R M) = embeddingEigenspace L K R M σ := by
  rw [Module.End.smul_top_eq_range]
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩ ℓ
    have h := congrArg (fun t ↦ tensorToModuleEnd R (𝓞 L) M t m)
      (one_tmul_mul_embeddingIdempotent hK hd σ ℓ)
    simp only [map_mul, AlgHom.commutes, Module.End.mul_eq_comp, LinearMap.comp_apply,
      Module.algebraMap_end_apply] at h
    rw [← h, tensorToModuleEnd_tmul, one_smul]
  · intro m hm
    refine ⟨m, ?_⟩
    rw [tensorToModuleEnd_apply_of_mem_embeddingEigenspace hm,
      embeddingEval_embeddingIdempotent_self, one_smul]

/-- **The embedding eigenspace decomposition** `M = ⨁_σ M(σ)`, when `K` receives all `[L : ℚ]`
embeddings of `L` and `d_L` is a unit of `R`. -/
theorem isInternal_embeddingEigenspace [DecidableEq (L →+* K)] :
    DirectSum.IsInternal (embeddingEigenspace L K R M) := by
  have h := TauCeti.isInternal_smul_top (S := R) (M := M)
    ((completeOrthogonalIdempotents_embeddingIdempotent hK hd).map
      (tensorToModuleEnd R (𝓞 L) M).toRingHom)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Function.comp_def,
    tensorToModuleEnd_embeddingIdempotent_smul_top hK hd] at h
  exact h

/-- **Tensoring the eigenspaces with an `R`-module**: for an `R`-module `N`, the eigenspace
`(M ⊗[R] N)(σ)`, with `𝓞 L` acting on the first factor, is the image of `M(σ) ⊗[R] N`. -/
theorem embeddingEigenspace_tensorProduct [SMulCommClass R (𝓞 L) M]
    (N : Type*) [AddCommMonoid N] [Module R N] (σ : L →+* K) :
    embeddingEigenspace L K R (M ⊗[R] N) σ =
      LinearMap.range ((embeddingEigenspace L K R M σ).subtype.rTensor N) := by
  apply le_antisymm
  · intro v hv
    have hv' : v = LinearMap.rTensor N
        (tensorToModuleEnd R (𝓞 L) M (embeddingIdempotent hK hd σ)) v := by
      rw [← tensorToModuleEnd_rTensor, tensorToModuleEnd_apply_of_mem_embeddingEigenspace hv,
        embeddingEval_embeddingIdempotent_self, one_smul]
    have hrange : LinearMap.range
        (tensorToModuleEnd R (𝓞 L) M (embeddingIdempotent hK hd σ)) ≤
          embeddingEigenspace L K R M σ := by
      rw [← Module.End.smul_top_eq_range, tensorToModuleEnd_embeddingIdempotent_smul_top hK hd]
    let g := (tensorToModuleEnd R (𝓞 L) M (embeddingIdempotent hK hd σ)).codRestrict
      (embeddingEigenspace L K R M σ) fun m ↦ hrange ⟨m, rfl⟩
    refine ⟨g.rTensor N v, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.subtype_comp_codRestrict]
    exact hv'.symm
  · rintro _ ⟨w, rfl⟩
    induction w using TensorProduct.inductionOn with
    | tmul m n =>
      intro ℓ
      simp [TensorProduct.smul_tmul', m.property ℓ]
    | add s t hs ht => rw [map_add]; exact add_mem hs ht

end Bijective

end TauCeti.NumberField
