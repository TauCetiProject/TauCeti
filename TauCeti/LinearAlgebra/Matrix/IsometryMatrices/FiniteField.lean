/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.Quadric
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization

/-!
# Orders of finite orthogonal groups

Let `F` be a finite field of odd characteristic with `q` elements and quadratic character `χ`, and
let `A` be a nondegenerate symmetric matrix over `F` indexed by a type with `n` elements. The
matrices `X` with `Xᵀ * A * X = A`, which form `Matrix.isometryMatrices A`, are the orthogonal
group of the quadratic space with Gram matrix `A`, and their number is

```text
n = 2m + 1:  #O(A) = 2 q^{m²} ∏_{i=1}^{m} (q^{2i} - 1),
n = 2m + 2:  #O(A) = 2 q^{m(m+1)} (q^{m+1} - ε) ∏_{i=1}^{m} (q^{2i} - 1),  ε = χ((-1)^{m+1} det A).
```

In even rank the sign `ε` is read off the determinant twisted by `(-1)^{m+1}`, not off the
determinant itself; it is `+1` for an orthogonal sum of hyperbolic planes. For `q = p` prime,
these orders divided by `p^{n(n-1)/2}` are the local densities of an integral lattice at the primes
not dividing twice its determinant.

The proof counts an orbit. Over any field of characteristic different from two, the matrices
preserving a symmetric `A` act transitively on the vectors `x` with a given nonzero value of
`xᵀ A x`, by the reflection transport `QuadraticMap.reflectionTransport`, so
`#O(A) = N(c) · #Stab(e)` for any `e` with `eᵀ A e = c ≠ 0`, where `N(c)` is the number of
solutions of `xᵀ A x = c`. When `A` is block diagonal with last block the `1 × 1` matrix `(c)` and
`e` is the last basis vector, the stabilizer of `e` is the orthogonal group of the first block.
Since `A` is congruent to a diagonal matrix, induction on the rank with the point counts
`Matrix.IsSymm.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_one` and
`Matrix.IsSymm.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_two` gives the formulas.

## Main results

* `Matrix.IsSymm.exists_mem_isometryMatrices_mulVec_eq`: transitivity on the vectors with a given
  nonzero value of `xᵀ A x`, over a field of characteristic different from two.
* `Matrix.IsSymm.natCard_isometryMatrices_eq_mul_natCard_stabilizer`: the orbit count
  `#O(A) = N(c) · #Stab(e)`.
* `Matrix.natCard_isometryMatrices_fromBlocks`: splitting off a `1 × 1` block.
* `Matrix.IsSymm.natCard_isometryMatrices_eq_of_card_eq_two_mul_add_one`,
  `Matrix.IsSymm.natCard_isometryMatrices_eq_of_card_eq_two_mul_add_two`: the orders in odd and in
  even rank.

## References

* L. E. Dickson, *Linear Groups, with an Exposition of the Galois Field Theory*, Teubner (1901).
* L. C. Grove, *Classical Groups and Geometric Algebra*, Graduate Studies in Mathematics 39,
  American Mathematical Society (2002).
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter III, for the transitivity of the
  orthogonal group on vectors of a given nonzero norm.
-/

public section

open Finset

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
  have hunit (X : isometryMatrices A) : IsUnit (X : Matrix ι ι F).det :=
    isUnit_det_of_mem_isometryMatrices (isUnit_iff_ne_zero.mpr hdet) X.2
  -- A chosen element `g x` of `O(A)` carrying `e` to each vector `x` of the level set.
  have hg (x : ι → F) : ∃ X : isometryMatrices A,
      x ⬝ᵥ A *ᵥ x = e ⬝ᵥ A *ᵥ e → (X : Matrix ι ι F) *ᵥ e = x := by
    by_cases hx : x ⬝ᵥ A *ᵥ x = e ⬝ᵥ A *ᵥ e
    · obtain ⟨X, hX, hXe⟩ :=
        hA.exists_mem_isometryMatrices_mulVec_eq hx.symm (by rw [hx]; exact he)
      exact ⟨⟨X, hX⟩, fun _ ↦ hXe⟩
    · exact ⟨1, fun h ↦ absurd h hx⟩
  choose g hge using hg
  have hinv_mem (X : isometryMatrices A) : (X : Matrix ι ι F)⁻¹ ∈ isometryMatrices A := by
    have hX := mem_isometryMatrices.mp X.2
    rw [mem_isometryMatrices]
    calc (X : Matrix ι ι F)⁻¹ᵀ * A * (X : Matrix ι ι F)⁻¹
        = (X : Matrix ι ι F)⁻¹ᵀ * ((X : Matrix ι ι F)ᵀ * A * X) * (X : Matrix ι ι F)⁻¹ := by
          rw [hX]
      _ = ((X : Matrix ι ι F) * (X : Matrix ι ι F)⁻¹)ᵀ * A *
            ((X : Matrix ι ι F) * (X : Matrix ι ι F)⁻¹) := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = A := by rw [mul_nonsing_inv _ (hunit X), transpose_one, Matrix.one_mul, Matrix.mul_one]
  have hlevel (X : isometryMatrices A) :
      (X : Matrix ι ι F) *ᵥ e ⬝ᵥ A *ᵥ ((X : Matrix ι ι F) *ᵥ e) = e ⬝ᵥ A *ᵥ e :=
    mulVec_dotProduct_mulVec_mulVec_of_mem_isometryMatrices X.2 e e
  have hstab (X : isometryMatrices A) :
      ((g ((X : Matrix ι ι F) *ᵥ e) : Matrix ι ι F)⁻¹ * (X : Matrix ι ι F)) *ᵥ e = e := by
    calc _ = (g ((X : Matrix ι ι F) *ᵥ e) : Matrix ι ι F)⁻¹ *ᵥ
          ((g ((X : Matrix ι ι F) *ᵥ e) : Matrix ι ι F) *ᵥ e) := by
          rw [hge _ (hlevel X), mulVec_mulVec]
      _ = e := by rw [mulVec_mulVec, nonsing_inv_mul _ (hunit _), one_mulVec]
  -- The level set times the stabilizer of `e` parametrizes `O(A)` by `(x, Y) ↦ g x * Y`.
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun X => (⟨_, hlevel X⟩,
        ⟨⟨(g ((X : Matrix ι ι F) *ᵥ e) : Matrix ι ι F)⁻¹ * (X : Matrix ι ι F),
          (isometryMatrices A).mul_mem (hinv_mem _) X.2⟩, hstab X⟩)
      invFun := fun p => g p.1 * p.2.1
      left_inv := fun X => Subtype.ext ?_
      right_inv := fun p => ?_ }
  · rw [Submonoid.coe_mul, ← Matrix.mul_assoc, mul_nonsing_inv _ (hunit _), Matrix.one_mul]
  · have hx : ((g p.1 * p.2.1 : isometryMatrices A) : Matrix ι ι F) *ᵥ e = p.1 := by
      rw [Submonoid.coe_mul, ← mulVec_mulVec, p.2.2, hge _ p.1.2]
    refine Prod.ext (Subtype.ext hx) (Subtype.ext (Subtype.ext ?_))
    -- Unfold the second component of `toFun` at `g p.1 * p.2.1`, to rewrite its argument by `hx`.
    change ((g (((g p.1 * p.2.1 : isometryMatrices A) : Matrix ι ι F) *ᵥ e) :
      Matrix ι ι F)⁻¹ * ((g p.1 * p.2.1 : isometryMatrices A) : Matrix ι ι F)) = p.2.1
    rw [hx, Submonoid.coe_mul, ← Matrix.mul_assoc, nonsing_inv_mul _ (hunit _), Matrix.one_mul]

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

/-- A nondegenerate symmetric matrix over a field in which `2` is invertible is congruent to a
block diagonal matrix `fromBlocks A' 0 0 (diagonal (fun _ ↦ c))` indexed by
`{i // i ≠ i₀} ⊕ Unit`, with `A'` nondegenerate symmetric, `c ≠ 0`, and `det A' · c` in the square
class of `det A`; the two matrices are preserved by equally many matrices. -/
private theorem exists_natCard_isometryMatrices_eq_fromBlocks [Invertible (2 : F)]
    {A : Matrix ι ι F} (hA : A.IsSymm) (hdet : A.det ≠ 0) (i₀ : ι) :
    ∃ (A' : Matrix {i // i ≠ i₀} {i // i ≠ i₀} F) (c : F), A'.IsSymm ∧ A'.det ≠ 0 ∧ c ≠ 0 ∧
      (∃ s ≠ 0, A'.det * c = s ^ 2 * A.det) ∧
      Nat.card (isometryMatrices A) =
        Nat.card (isometryMatrices (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c))) := by
  obtain ⟨P, d, hP, hPAP⟩ := hA.exists_isUnit_transpose_mul_mul_eq_diagonal
  have hPdet : P.det ≠ 0 := ((isUnit_iff_isUnit_det P).mp hP).ne_zero
  have hprod : (diagonal d).det = P.det ^ 2 * A.det := by
    rw [← hPAP, det_mul, det_mul, det_transpose]
    ring
  have hd (i : ι) : d i ≠ 0 := by
    have h : (diagonal d).det ≠ 0 := hprod ▸ mul_ne_zero (pow_ne_zero 2 hPdet) hdet
    rw [det_diagonal] at h
    exact prod_ne_zero_iff.mp h i (mem_univ i)
  let e : ι ≃ {i // i ≠ i₀} ⊕ Unit :=
    (Equiv.optionSubtypeNe i₀).symm.trans (Equiv.optionEquivSumPUnit _)
  have hreindex : reindex e e (diagonal d) =
      fromBlocks (diagonal fun i : {i // i ≠ i₀} ↦ d i) 0 0 (diagonal fun _ : Unit ↦ d i₀) := by
    ext (i | i) (j | j)
    · simp [e, diagonal_apply, Subtype.ext_iff]
    · simp [e, i.2]
    · simp [e, Ne.symm j.2]
    · simp [e]
  refine ⟨diagonal fun i : {i // i ≠ i₀} ↦ d i, d i₀, isSymm_diagonal _, ?_, hd i₀,
    ⟨P.det, hPdet, ?_⟩, ?_⟩
  · rw [det_diagonal]
    exact prod_ne_zero_iff.mpr fun i _ ↦ hd i
  · rw [← hprod, ← det_reindex_self e (diagonal d), hreindex, det_fromBlocks_zero₂₁, det_diagonal]
    simp
  · rw [← hreindex, natCard_isometryMatrices_reindex, ← hPAP,
      natCard_isometryMatrices_transpose_mul_mul ((isUnit_iff_isUnit_det P).mp hP)]

variable [Fintype F]

/-- The orders in odd rank `2m + 1` and in even rank `2m + 2`, proved together by induction on `m`
for all index types in one universe. -/
private theorem natCard_isometryMatrices_aux [DecidableEq F] (hF : ringChar F ≠ 2) (m : ℕ) :
    (∀ (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 →
      Fintype.card ι = 2 * m + 1 →
      (Nat.card (isometryMatrices A) : ℤ) =
        2 * (Fintype.card F : ℤ) ^ (m ^ 2) *
          ∏ i ∈ range m, ((Fintype.card F : ℤ) ^ (2 * (i + 1)) - 1)) ∧
    (∀ (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 →
      Fintype.card ι = 2 * m + 2 →
      (Nat.card (isometryMatrices A) : ℤ) =
        2 * (Fintype.card F : ℤ) ^ (m * (m + 1)) *
          ((Fintype.card F : ℤ) ^ (m + 1) - quadraticChar F ((-1) ^ (m + 1) * A.det)) *
          ∏ i ∈ range m, ((Fintype.card F : ℤ) ^ (2 * (i + 1)) - 1)) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have : NeZero (2 : F) := ⟨h2⟩
  have : Invertible (2 : F) := invertibleOfNonzero h2
  set q : ℤ := (Fintype.card F : ℤ)
  have hcardι (ι : Type u_2) [Fintype ι] [DecidableEq ι] (i₀ : ι) :
      Fintype.card {i // i ≠ i₀} + 1 = Fintype.card ι := by
    rw [← Fintype.card_option, Fintype.card_congr (Equiv.optionSubtypeNe i₀)]
  -- Splitting off a `1 × 1` block: `#O(A) = N(c) · #O(A')`.
  have step (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : A.IsSymm)
      (hdet : A.det ≠ 0) (i₀ : ι) :
      ∃ (A' : Matrix {i // i ≠ i₀} {i // i ≠ i₀} F) (c : F), A'.IsSymm ∧ A'.det ≠ 0 ∧ c ≠ 0 ∧
        (∃ s ≠ 0, A'.det * c = s ^ 2 * A.det) ∧
        (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c)).IsSymm ∧
        (fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c)).det = A'.det * c ∧
        (Nat.card (isometryMatrices A) : ℤ) =
          #{x : {i // i ≠ i₀} ⊕ Unit → F |
            x ⬝ᵥ fromBlocks A' 0 0 (diagonal fun _ : Unit ↦ c) *ᵥ x = c} *
          Nat.card (isometryMatrices A') := by
    obtain ⟨A', c, hA', hdet', hc, hs, hcard⟩ :=
      exists_natCard_isometryMatrices_eq_fromBlocks hA hdet i₀
    refine ⟨A', c, hA', hdet', hc, hs, hA'.fromBlocks (by simp) (by simp [IsSymm]),
      by simp [det_fromBlocks_zero₂₁], ?_⟩
    rw [hcard, natCard_isometryMatrices_fromBlocks hA' hdet' hc, Nat.card_eq_fintype_card,
      Fintype.card_subtype, Nat.cast_mul]
  -- Odd rank `2n + 1`, from rank `2n`.
  have odd_step (n : ℕ) (hO : ∀ (κ : Type u_2) [Fintype κ] [DecidableEq κ] (A' : Matrix κ κ F),
      A'.IsSymm → A'.det ≠ 0 → Fintype.card κ = 2 * n →
      q ^ n * ((Nat.card (isometryMatrices A') : ℤ) *
        (q ^ n + quadraticChar F ((-1) ^ n * A'.det))) =
        2 * q ^ (n ^ 2) * ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1))
      (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : A.IsSymm)
      (hdet : A.det ≠ 0) (hι : Fintype.card ι = 2 * n + 1) :
      (Nat.card (isometryMatrices A) : ℤ) =
        2 * q ^ (n ^ 2) * ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1) := by
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨A', c, hA', hdet', hc, -, hB, hBdet, hcard⟩ := step ι A hA hdet i₀
    have hκ : Fintype.card {i // i ≠ i₀} = 2 * n := by have := hcardι ι i₀; omega
    rw [hcard, hB.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_one hF
      (by rw [hBdet]; exact mul_ne_zero hdet' hc) (m := n) (by simp [hκ]) c, hBdet,
      ← hO _ A' hA' hdet' hκ, show (-1) ^ n * (A'.det * c) * c = (-1) ^ n * A'.det * c ^ 2 by ring,
      map_mul, quadraticChar_sq_one' hc, mul_one]
    ring
  -- Even rank `2n + 2`, from rank `2n + 1`.
  have even_step (n : ℕ) (hO : ∀ (κ : Type u_2) [Fintype κ] [DecidableEq κ] (A' : Matrix κ κ F),
      A'.IsSymm → A'.det ≠ 0 → Fintype.card κ = 2 * n + 1 →
      (Nat.card (isometryMatrices A') : ℤ) =
        2 * q ^ (n ^ 2) * ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1))
      (ι : Type u_2) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) (hA : A.IsSymm)
      (hdet : A.det ≠ 0) (hι : Fintype.card ι = 2 * n + 2) :
      (Nat.card (isometryMatrices A) : ℤ) =
        2 * q ^ (n * (n + 1)) * (q ^ (n + 1) - quadraticChar F ((-1) ^ (n + 1) * A.det)) *
          ∏ i ∈ range n, (q ^ (2 * (i + 1)) - 1) := by
    obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨A', c, hA', hdet', hc, ⟨s, hs, hsdet⟩, hB, hBdet, hcard⟩ := step ι A hA hdet i₀
    have hκ : Fintype.card {i // i ≠ i₀} = 2 * n + 1 := by have := hcardι ι i₀; omega
    rw [hcard, hB.card_dotProduct_mulVec_eq_of_card_eq_two_mul_add_two hF
      (by rw [hBdet]; exact mul_ne_zero hdet' hc) (m := n) (by simp [hκ]) c, hBdet, hsdet,
      hO _ A' hA' hdet' hκ, mul_left_comm _ (s ^ 2), map_mul, quadraticChar_sq_one' hs, one_mul]
    simp only [hc, ↓reduceIte]
    ring
  have odd_zero := odd_step 0 fun κ _ _ A' _ _ hκ ↦ by
    have : IsEmpty κ := Fintype.card_eq_zero_iff.mp hκ
    rw [Nat.card_of_subsingleton (⟨1, (isometryMatrices A').one_mem⟩ : isometryMatrices A'),
      det_isEmpty]
    simp
  induction m with
  | zero => exact ⟨odd_zero, even_step 0 odd_zero⟩
  | succ m ih =>
    have hodd := odd_step (m + 1) fun κ _ _ A' hA' hdet' hκ ↦ by
      have hε := quadraticChar_sq_one
        (mul_ne_zero (pow_ne_zero (m + 1) (neg_ne_zero.mpr one_ne_zero)) hdet')
      rw [ih.2 κ A' hA' hdet' (by omega), prod_range_succ]
      linear_combination
        (-2 * q ^ (m * (m + 1)) * q ^ (m + 1) * ∏ i ∈ range m, (q ^ (2 * (i + 1)) - 1)) * hε
    exact ⟨hodd, even_step (m + 1) hodd⟩

namespace IsSymm

variable (hF : ringChar F ≠ 2) {A : Matrix ι ι F}
include hF

/-- **The order of an orthogonal group over a finite field in odd rank.** Over a finite field of
odd characteristic with `q` elements, if `A` is a nondegenerate symmetric matrix indexed by a type
with `2m + 1` elements, then exactly `2 q^{m²} ∏_{i=1}^{m} (q^{2i} - 1)` matrices `X` satisfy
`Xᵀ * A * X = A`. -/
theorem natCard_isometryMatrices_eq_of_card_eq_two_mul_add_one (hA : A.IsSymm) (hdet : A.det ≠ 0)
    {m : ℕ} (hι : Fintype.card ι = 2 * m + 1) :
    (Nat.card (isometryMatrices A) : ℤ) =
      2 * (Fintype.card F : ℤ) ^ (m ^ 2) *
        ∏ i ∈ range m, ((Fintype.card F : ℤ) ^ (2 * (i + 1)) - 1) := by
  classical
  exact (natCard_isometryMatrices_aux hF m).1 ι A hA hdet hι

/-- **The order of an orthogonal group over a finite field in even rank.** Over a finite field of
odd characteristic with `q` elements and quadratic character `χ`, if `A` is a nondegenerate
symmetric matrix indexed by a type with `2m + 2` elements, then exactly
`2 q^{m(m+1)} (q^{m+1} - ε) ∏_{i=1}^{m} (q^{2i} - 1)` matrices `X` satisfy `Xᵀ * A * X = A`, where
`ε = χ((-1)^{m+1} det A)`. -/
theorem natCard_isometryMatrices_eq_of_card_eq_two_mul_add_two [DecidableEq F] (hA : A.IsSymm)
    (hdet : A.det ≠ 0) {m : ℕ} (hι : Fintype.card ι = 2 * m + 2) :
    (Nat.card (isometryMatrices A) : ℤ) =
      2 * (Fintype.card F : ℤ) ^ (m * (m + 1)) *
        ((Fintype.card F : ℤ) ^ (m + 1) - quadraticChar F ((-1) ^ (m + 1) * A.det)) *
        ∏ i ∈ range m, ((Fintype.card F : ℤ) ^ (2 * (i + 1)) - 1) :=
  (natCard_isometryMatrices_aux hF m).2 ι A hA hdet hι

end IsSymm

end Matrix
