/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Hyperbolic

/-!
# Gram determinants of signed hermitian spaces

For a basis `b` of a signed hermitian space `(V, h)` over a commutative ring with involution `σ`,
the Gram matrix `G_b = (h (bᵢ) (bⱼ))` is Mathlib's `LinearMap.toMatrix₂ b b h`. A change of basis
by the matrix `P` turns it into `σ(P)ᵀ G_b P`, so the Gram determinant changes by the norm
`σ (det P) * det P` of the unit `det P`
(`TauCeti.SignedHermitianSpace.det_toMatrix₂_basis_change`). The class of `det G_b` modulo norms
of units is therefore attached to the space: it does not depend on the basis, it is an isometry
invariant (`TauCeti.SignedHermitianSpace.Equivalent.exists_det_eq`), and it is multiplicative
under orthogonal sums (`TauCeti.SignedHermitianSpace.det_toMatrix₂_prod`). For a hermitian space
the Gram determinant is fixed by `σ`, so for a quadratic extension `E/F` this is the determinant
class `det V ∈ F^×/N(E^×)`. The hyperbolic space `H^ι` has Gram determinant `(-ε) ^ |ι|`
(`TauCeti.SignedHermitianSpace.det_toMatrix₂_hyperbolic`); in particular the hyperbolic plane has
Gram determinant `-ε`.

## Main statements

* `TauCeti.SignedHermitianSpace.toMatrix₂_basis_change`: `G_c = σ(P)ᵀ G_b P` for `P` the matrix
  of `c` in `b`.
* `TauCeti.SignedHermitianSpace.det_toMatrix₂_basis_change`:
  `det G_c = σ (det P) * det P * det G_b`.
* `TauCeti.SignedHermitianSpace.Equivalent.exists_det_eq`: Gram determinants of isometric spaces
  differ by the norm of a unit.
* `TauCeti.SignedHermitianSpace.det_toMatrix₂_prod`: Gram determinants multiply under orthogonal
  sums.
* `TauCeti.SignedHermitianSpace.apply_det_toMatrix₂`: `σ (det G_b) = ε ^ n • det G_b`.
* `TauCeti.SignedHermitianSpace.det_toMatrix₂_hyperbolic`: `det H^ι = (-ε) ^ |ι|`.
-/

public section

open Module Matrix

namespace TauCeti

namespace SignedHermitianSpace

variable {K V V₁ V₂ : Type*} [CommRing K] {σ : K →+* K} {ε : ℤˣ} [AddCommGroup V] [Module K V]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Change of basis for the Gram matrix.** If `P` is the matrix of the basis `c` in the basis
`b`, then the Gram matrix of `h` in `c` is `σ(P)ᵀ G_b P`. -/
theorem toMatrix₂_basis_change (H : SignedHermitianSpace K V σ ε) (b c : Basis ι K V) :
    LinearMap.toMatrix₂ c c H.form =
      ((b.toMatrix c).map σ)ᵀ * LinearMap.toMatrix₂ b b H.form * b.toMatrix c := by
  ext i j
  rw [LinearMap.toMatrix₂_apply, ← b.sum_toMatrix_smul_self c i, ← b.sum_toMatrix_smul_self c j]
  simp only [Matrix.mul_apply, transpose_apply, map_apply, LinearMap.toMatrix₂_apply, map_sum,
    map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- **The Gram determinant changes by a norm.** If `P` is the matrix of the basis `c` in the basis
`b`, then `det G_c = σ (det P) * det P * det G_b`, where `det P` is a unit. -/
theorem det_toMatrix₂_basis_change (H : SignedHermitianSpace K V σ ε) (b c : Basis ι K V) :
    (LinearMap.toMatrix₂ c c H.form).det =
      σ (b.toMatrix c).det * (b.toMatrix c).det * (LinearMap.toMatrix₂ b b H.form).det := by
  rw [toMatrix₂_basis_change H b, det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  ring

/-- The Gram matrix of a transported basis: an isometric equivalence `e` carries the Gram matrix
of `b` to that of `e ∘ b`. -/
theorem IsometryEquiv.toMatrix₂_map {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} (e : IsometryEquiv H₁ H₂) (b : Basis ι K V₁) :
    LinearMap.toMatrix₂ (b.map e.toLinearEquiv) (b.map e.toLinearEquiv) H₂.form =
      LinearMap.toMatrix₂ b b H₁.form := by
  ext i j
  simp [e.map_app]

/-- **The Gram determinant is an isometry invariant up to norms.** For bases `b₁`, `b₂` of
isometric signed hermitian spaces, `det G_{b₂} = σ u * u * det G_{b₁}` for a unit `u`. -/
theorem Equivalent.exists_det_eq {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} (h : Equivalent H₁ H₂) (b₁ : Basis ι K V₁)
    (b₂ : Basis ι K V₂) :
    ∃ u : Kˣ, (LinearMap.toMatrix₂ b₂ b₂ H₂.form).det =
      σ u * u * (LinearMap.toMatrix₂ b₁ b₁ H₁.form).det := by
  obtain ⟨e⟩ := h.nonempty
  let b := b₁.map e.toLinearEquiv
  let _ := b.invertibleToMatrix b₂
  refine ⟨(isUnit_det_of_invertible (b.toMatrix b₂)).unit, ?_⟩
  rw [det_toMatrix₂_basis_change H₂ b b₂, e.toMatrix₂_map, IsUnit.unit_spec]

/-- **Gram determinants multiply under orthogonal sums.** -/
theorem det_toMatrix₂_prod (H₁ : SignedHermitianSpace K V₁ σ ε)
    (H₂ : SignedHermitianSpace K V₂ σ ε) (b₁ : Basis ι K V₁) (b₂ : Basis κ K V₂) :
    (LinearMap.toMatrix₂ (b₁.prod b₂) (b₁.prod b₂) (H₁.prod H₂).form).det =
      (LinearMap.toMatrix₂ b₁ b₁ H₁.form).det * (LinearMap.toMatrix₂ b₂ b₂ H₂.form).det := by
  have : LinearMap.toMatrix₂ (b₁.prod b₂) (b₁.prod b₂) (H₁.prod H₂).form =
      fromBlocks (LinearMap.toMatrix₂ b₁ b₁ H₁.form) 0 0 (LinearMap.toMatrix₂ b₂ b₂ H₂.form) := by
    ext (i | i) (j | j) <;> simp
  rw [this, det_fromBlocks_zero₂₁]

/-- The Gram determinant of an `ε`-hermitian form satisfies `σ (det G) = ε ^ n • det G`: for a
hermitian form it is fixed by the involution. -/
theorem apply_det_toMatrix₂ (H : SignedHermitianSpace K V σ ε) (b : Basis ι K V) :
    σ (LinearMap.toMatrix₂ b b H.form).det =
      ((ε ^ Fintype.card ι : ℤˣ) : ℤ) • (LinearMap.toMatrix₂ b b H.form).det := by
  have : (LinearMap.toMatrix₂ b b H.form).map σ =
      ((ε : ℤ) : K) • (LinearMap.toMatrix₂ b b H.form)ᵀ := by
    ext i j
    simp [LinearMap.toMatrix₂_apply, H.form_swap (b i) (b j), Int.units_smul_eq_cast_mul,
      ← mul_assoc, Int.cast_units_mul_self]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, this, det_smul, det_transpose, zsmul_eq_mul]
  push_cast
  ring

/-- **The Gram determinant of the hyperbolic space `H^ι` is `(-ε) ^ |ι|`**, in its standard
basis. Grouping the basis vectors `(eᵢ, 0)`, `(0, eᵢ)` by `i` makes the Gram matrix block
diagonal, with `|ι|` blocks `[[0, 1], [ε, 0]]`. -/
theorem det_toMatrix₂_hyperbolic [RingHomInvPair σ σ] (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (LinearMap.toMatrix₂ ((Pi.basisFun K ι).prod (Pi.basisFun K ι))
      ((Pi.basisFun K ι).prod (Pi.basisFun K ι)) (hyperbolic K σ ε ι).form).det =
        (-((ε : ℤ) : K)) ^ Fintype.card ι := by
  -- Index the basis by `Fin 2 × ι`: `(0, i)` is `(eᵢ, 0)` and `(1, i)` is `(0, eᵢ)`.
  let e : Fin 2 × ι ≃ ι ⊕ ι := (finTwoEquiv.prodCongr (Equiv.refl ι)).trans
    (Equiv.boolProdEquivSum ι)
  have he₀ (i : ι) : e (0, i) = Sum.inl i := rfl
  have he₁ (i : ι) : e (1, i) = Sum.inr i := rfl
  rw [← det_reindex_self e.symm]
  have : reindex e.symm e.symm
      (LinearMap.toMatrix₂ ((Pi.basisFun K ι).prod (Pi.basisFun K ι))
        ((Pi.basisFun K ι).prod (Pi.basisFun K ι)) (hyperbolic K σ ε ι).form) =
      blockDiagonal fun _ ↦ !![0, 1; ((ε : ℤ) : K), 0] := by
    ext ⟨a, i⟩ ⟨b, j⟩
    fin_cases a <;> fin_cases b <;>
      simp [he₀, he₁, blockDiagonal_apply, Pi.single_apply, eq_comm, Int.units_smul_eq_cast_mul]
  rw [this, det_blockDiagonal, det_fin_two_of, Finset.prod_const, Finset.card_univ]
  ring

end SignedHermitianSpace

end TauCeti
