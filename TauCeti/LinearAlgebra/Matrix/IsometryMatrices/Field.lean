/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Matrices preserving a symmetric matrix over a field

Let `A` be a symmetric matrix over a field of characteristic different from two. The matrices `X`
with `Xᵀ * A * X = A`, which form `Matrix.isometryMatrices A`, act transitively on the vectors `x`
with a given nonzero value of `xᵀ A x`, by the reflection transport
`QuadraticMap.reflectionTransport`. When `A` is moreover nondegenerate, these matrices are
identified with the isometry group `TauCeti.BilinForm.isometryGroup` of the bilinear form with
Gram matrix `A`, so the orbit–stabilizer theorem `MulAction.orbitProdStabilizerEquivGroup` gives
`#O(A) = N(c) · #Stab(e)` for any `e` with `eᵀ A e = c ≠ 0`, where `N(c)` is the number of
solutions of `xᵀ A x = c`. When `A` is block diagonal with last block the `1 × 1` matrix `(c)` and
`e` is the last basis vector, the stabilizer of `e` is the orthogonal group of the first block.

## Main results

* `Matrix.IsSymm.exists_mem_isometryMatrices_mulVec_eq`: transitivity on the vectors with a given
  nonzero value of `xᵀ A x`.
* `Matrix.IsSymm.natCard_isometryMatrices_eq_mul_natCard_stabilizer`: the orbit count
  `#O(A) = N(c) · #Stab(e)`.
* `Matrix.natCard_isometryMatrices_fromBlocks`: splitting off a `1 × 1` block.

## References

* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter III, for the transitivity of the
  orthogonal group on vectors of a given nonzero norm.
-/

public section

namespace Matrix

variable {F ι κ : Type*} [Field F] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

namespace IsSymm

/-- **Transitivity on a level set.** Over a field of characteristic different from two, the
matrices preserving a symmetric matrix `A` act transitively on the vectors `x` with a given nonzero
value of `xᵀ A x`. -/
theorem exists_mem_isometryMatrices_mulVec_eq [NeZero (2 : F)] {A : Matrix ι ι F} (hA : A.IsSymm)
    {x y : ι → F} (hxy : x ⬝ᵥ A *ᵥ x = y ⬝ᵥ A *ᵥ y) (hy : y ⬝ᵥ A *ᵥ y ≠ 0) :
    ∃ X ∈ isometryMatrices A, X *ᵥ x = y := by
  set B := Matrix.toBilin' A
  have hQ (v : ι → F) : B.toQuadraticMap v = v ⬝ᵥ A *ᵥ v := by
    simp [B, Matrix.toBilin'_apply']
  have hB : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hA
  set g := B.toQuadraticMap.reflectionTransport x y (by rw [hQ, hQ, hxy]) (by rwa [hQ])
  set G : (ι → F) ≃ₗ[F] (ι → F) := g.1
  refine ⟨LinearMap.toMatrix' G, ?_, ?_⟩
  · -- `G` preserves the polar form `2 B`, hence `B` itself, and `B` has Gram matrix `A`.
    have hiso : TauCeti.BilinForm.IsIsometry B G.toLinearMap :=
      TauCeti.BilinForm.isIsometry_iff.mpr fun u v => by
        have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup g.2 u v
        rw [LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.BilinMap.polar_toQuadraticMap,
          hB.eq (G v) (G u), hB.eq v u, ← two_mul, ← two_mul] at h
        exact mul_left_cancel₀ (NeZero.ne 2) h
    have h := (TauCeti.BilinForm.isIsometry_toLin_iff_mem_isometryMatrices (B := B)
      (Pi.basisFun F ι) (X := LinearMap.toMatrix' G.toLinearMap)).mp
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at h
    refine h ?_
    rwa [Matrix.toLin_eq_toLin', Matrix.toLin'_toMatrix']
  · rw [LinearMap.toMatrix'_mulVec]
    exact QuadraticMap.reflectionTransport_apply _ x y _ _

/-- **Counting an orbit.** Over a field of characteristic different from two, if `A` is
symmetric and nondegenerate and `e` has `eᵀ A e ≠ 0`, the number of matrices preserving `A` is the
number of vectors `x` with `xᵀ A x = eᵀ A e` times the number of those fixing `e`. -/
theorem natCard_isometryMatrices_eq_mul_natCard_stabilizer [NeZero (2 : F)]
    {A : Matrix ι ι F} (hA : A.IsSymm) (hdet : A.det ≠ 0) {e : ι → F}
    (he : e ⬝ᵥ A *ᵥ e ≠ 0) :
    Nat.card (isometryMatrices A) =
      Nat.card {x : ι → F // x ⬝ᵥ A *ᵥ x = e ⬝ᵥ A *ᵥ e} *
        Nat.card {X : isometryMatrices A // (X : Matrix ι ι F) *ᵥ e = e} := by
  set B := Matrix.toBilin' A
  have hB : B.SeparatingLeft :=
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet).1
  have hmem (X : Matrix ι ι F) :
      TauCeti.BilinForm.IsIsometry B (toLin' X) ↔ X ∈ isometryMatrices A := by
    rw [← Matrix.toLin_eq_toLin', TauCeti.BilinForm.isIsometry_toLin_iff_mem_isometryMatrices,
      LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']
  -- `X ↦ toLin' X` identifies the matrices preserving `A` with the isometry group of `B`, which
  -- acts on the coordinate vectors.
  let φ : isometryMatrices A ≃ TauCeti.BilinForm.isometryGroup B :=
    { toFun X := ((hmem X).mpr X.2).toIsometryGroup hB
      invFun g := ⟨LinearMap.toMatrix' (g : (ι → F) →ₗ[F] (ι → F)),
        (hmem _).mp (by simpa using TauCeti.BilinForm.mem_isometryGroup.mp g.2)⟩
      left_inv X := Subtype.ext (by simp)
      right_inv g := Subtype.ext (LinearEquiv.toLinearMap_injective (by simp)) }
  have hφ (X : isometryMatrices A) (x : ι → F) : φ X • x = (X : Matrix ι ι F) *ᵥ x := by
    simp [φ, Subgroup.smul_def, LinearEquiv.smul_def]
  rw [Nat.card_congr φ, ← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ e),
    Nat.card_prod]
  congr 1
  · -- By transitivity, the orbit of `e` is the level set of `xᵀ A x` through `e`.
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [MulAction.mem_orbit_iff, φ.surjective.exists]
    simp only [hφ]
    constructor
    · rintro ⟨X, rfl⟩
      exact mulVec_dotProduct_mulVec_mulVec_of_mem_isometryMatrices X.2 e e
    · intro hx
      obtain ⟨X, hX, hXe⟩ :=
        hA.exists_mem_isometryMatrices_mulVec_eq hx.symm (by rw [hx]; exact he)
      exact ⟨⟨X, hX⟩, hXe⟩
  · exact (Nat.card_congr (φ.subtypeEquiv fun X => by
      rw [MulAction.mem_stabilizer_iff, hφ])).symm

end IsSymm

/-- If `c ≠ 0`, a matrix preserving `fromBlocks A' 0 0 (diagonal (fun _ ↦ c))` and fixing the last
basis vector of `κ ⊕ Unit` is block diagonal, `fromBlocks Y 0 0 1`. -/
private theorem eq_fromBlocks_of_mem_isometryMatrices {A' : Matrix κ κ F} {c : F} (hc : c ≠ 0)
    {X : Matrix (κ ⊕ Unit) (κ ⊕ Unit) F}
    (hX : X ∈ isometryMatrices (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c)))
    (he : X *ᵥ Pi.single (Sum.inr ()) 1 = Pi.single (Sum.inr ()) 1) :
    X = fromBlocks X.toBlocks₁₁ 0 0 1 := by
  set A := fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c)
  set e : κ ⊕ Unit → F := Pi.single (Sum.inr ()) 1
  have hAe : A *ᵥ e = c • e := by
    ext (i | i) <;> simp [A, e]
  -- Applying `Xᵀ A X = A` to `e` shows that `Xᵀ` also fixes `e`.
  have hte : Xᵀ *ᵥ e = e := by
    have h : Xᵀ *ᵥ (A *ᵥ (X *ᵥ e)) = A *ᵥ e := by
      rw [mulVec_mulVec, mulVec_mulVec, mem_isometryMatrices.mp hX]
    rw [he, hAe, mulVec_smul] at h
    exact smul_right_injective _ hc h
  have hcol (i : κ ⊕ Unit) : X i (Sum.inr ()) = e i := by
    simpa [e, mulVec_single_one] using congrFun he i
  have hrow (j : κ ⊕ Unit) : X (Sum.inr ()) j = e j := by
    simpa [e, mulVec_single_one] using congrFun hte j
  conv_lhs => rw [← fromBlocks_toBlocks X]
  congr 1
  · ext i j
    simpa [e, toBlocks₁₂] using hcol (Sum.inl i)
  · ext i j
    simpa [e, toBlocks₂₁] using hrow (Sum.inl j)
  · ext i j
    simpa [e, toBlocks₂₂, one_apply] using hcol (Sum.inr i)

/-- A block diagonal matrix `fromBlocks Y 0 0 1` preserves
`fromBlocks A' 0 0 (diagonal (fun _ ↦ c))` exactly when `Y` preserves `A'`. -/
private theorem fromBlocks_mem_isometryMatrices_iff {A' Y : Matrix κ κ F} {c : F} :
    fromBlocks Y 0 0 1 ∈ isometryMatrices (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c)) ↔
      Y ∈ isometryMatrices A' := by
  simp [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj]

/-- **Splitting off a `1 × 1` block.** Over a field of characteristic different from two,
if `A'` is symmetric and nondegenerate and `c ≠ 0`, the number of matrices preserving
`A = fromBlocks A' 0 0 (diagonal (fun _ ↦ c))` is the number of solutions of `xᵀ A x = c` times
the number of matrices preserving `A'`. -/
theorem natCard_isometryMatrices_fromBlocks [NeZero (2 : F)] {A' : Matrix κ κ F}
    (hA' : A'.IsSymm) (hdet : A'.det ≠ 0) {c : F} (hc : c ≠ 0) :
    Nat.card (isometryMatrices (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c))) =
      Nat.card {x : κ ⊕ Unit → F //
        x ⬝ᵥ fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c) *ᵥ x = c} *
        Nat.card (isometryMatrices A') := by
  set A := fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c)
  set e : κ ⊕ Unit → F := Pi.single (Sum.inr ()) 1
  have hee : e ⬝ᵥ A *ᵥ e = c := by
    simp [A, e]
  have hA : A.IsSymm := hA'.fromBlocks (by simp) (by simp [IsSymm])
  have hAdet : A.det ≠ 0 := by
    simpa [A, det_fromBlocks_zero₂₁] using mul_ne_zero hdet hc
  rw [hA.natCard_isometryMatrices_eq_mul_natCard_stabilizer hAdet (hee ▸ hc), hee]
  congr 1
  refine Nat.card_congr
    { toFun := fun X => ⟨(X.1 : Matrix (κ ⊕ Unit) (κ ⊕ Unit) F).toBlocks₁₁, ?_⟩
      invFun := fun Y => ⟨⟨fromBlocks Y.1 0 0 1, fromBlocks_mem_isometryMatrices_iff.mpr Y.2⟩, ?_⟩
      left_inv := fun X => Subtype.ext (Subtype.ext ?_)
      right_inv := fun Y => Subtype.ext ?_ }
  · rw [← fromBlocks_mem_isometryMatrices_iff (c := c), ← eq_fromBlocks_of_mem_isometryMatrices hc
      X.1.2 X.2]
    exact X.1.2
  · ext (i | i) <;> simp [e]
  · exact (eq_fromBlocks_of_mem_isometryMatrices hc X.1.2 X.2).symm
  · simp

end Matrix
