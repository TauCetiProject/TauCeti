/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.LinearAlgebra.Matrix.Alternating
public import TauCeti.LinearAlgebra.Matrix.IdealEntries
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# Matrices preserving a Gram matrix

For a square matrix `A` over a commutative semiring, `Matrix.isometryMatrices A` is the submonoid
of matrices `X` with `Xᵀ * A * X = A`, the endomorphisms of the coordinate module that preserve
the bilinear form with Gram matrix `A`. Counting these matrices over the finite rings
`ZMod (p ^ r)` is how the local density of a quadratic lattice is defined, and the two results
here are what that count needs.

* A change of basis `A ↦ Pᵀ * A * P` by an invertible `P` conjugates the submonoid by `P`, so its
  cardinality does not depend on the basis.
* Let `f : R →+* S` be surjective with square-zero kernel, let `2` be a unit of `R`, and let `A`
  be symmetric with unit determinant. Then every solution over `S` lifts to a solution over `R`,
  and the solutions over `R` lying above a fixed one correspond to the skew-symmetric matrices
  with entries in the kernel. Hence, as an identity of `Nat.card`s, the count over `R` is
  `Nat.card (ker f) ^ (k.choose 2)` times the count over `S`, for `k` the size of the index
  type; when `R` is finite these are the actual numbers of solutions. This is the infinitesimal
  lifting property behind the smoothness of the orthogonal group of a nondegenerate form away
  from `2`, with its relative dimension `k (k - 1) / 2`.

The lift corrects an arbitrary preimage `M` of the solution: with error `E = A - Mᵀ * A * M`,
the matrix `M * (1 + ½ A⁻¹ E)` is a solution, since all quadratic terms in the error vanish.

## Main results

* `Matrix.natCard_isometryMatrices_transpose_mul_mul`: the count is invariant under
  `A ↦ Pᵀ * A * P` for invertible `P`.
* `Matrix.exists_map_eq_of_mem_isometryMatrices_map`: solutions lift across a surjection with
  square-zero kernel.
* `Matrix.isometryMatricesFiberEquiv`: the solutions congruent to a given one modulo a
  square-zero ideal correspond to the skew-symmetric matrices with entries in the ideal.
* `Matrix.natCard_isometryMatrices_eq_pow_mul`: the count across such a surjection.

## References

* C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36
  (1935), where the local densities are defined by these counts.
-/

public section

namespace Matrix

variable {n R S : Type*} [Fintype n] [DecidableEq n]

section CommSemiring

variable [CommSemiring R] [CommSemiring S]

/-- The submonoid of matrices `X` with `Xᵀ * A * X = A`, the endomorphisms of the coordinate
module that preserve the bilinear form with Gram matrix `A`. -/
def isometryMatrices (A : Matrix n n R) : Submonoid (Matrix n n R) where
  carrier := {X | Xᵀ * A * X = A}
  one_mem' := by simp
  mul_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq] at *
    calc (X * Y)ᵀ * A * (X * Y) = Yᵀ * (Xᵀ * A * X) * Y := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = A := by rw [hX, hY]

/-- Membership in `isometryMatrices A` is the equation `Xᵀ * A * X = A`. -/
@[simp]
theorem mem_isometryMatrices {A X : Matrix n n R} :
    X ∈ isometryMatrices A ↔ Xᵀ * A * X = A :=
  Iff.rfl

/-- A ring homomorphism carries solutions of `Xᵀ * A * X = A` to solutions for the image of
`A`. -/
theorem map_mem_isometryMatrices_map (f : R →+* S) {A X : Matrix n n R}
    (hX : X ∈ isometryMatrices A) : X.map f ∈ isometryMatrices (A.map f) := by
  rw [mem_isometryMatrices] at *
  rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hX]

end CommSemiring

variable [CommRing R] [CommRing S]

/-- **The square-zero expansion of the isometry equation.** If `X` preserves a symmetric Gram
matrix `A` and the entries of `D` lie in a square-zero ideal, then the quadratic term of
`(X + D)ᵀ * A * (X + D)` vanishes, leaving `A + K + Kᵀ` for `K = Xᵀ * A * D`. -/
theorem add_transpose_mul_mul_add_of_sq_eq_bot {I : Ideal R} (hI : I ^ 2 = ⊥)
    {A X D : Matrix n n R} (hA : Aᵀ = A) (hX : X ∈ isometryMatrices A) (hD : ∀ i j, D i j ∈ I) :
    (X + D)ᵀ * A * (X + D) = A + Xᵀ * A * D + (Xᵀ * A * D)ᵀ := by
  classical
  have hDD : Dᵀ * (A * D) = 0 :=
    mul_eq_zero_of_sq_eq_bot hI (fun i j => hD j i) ((I.matrix n).mul_mem_left A hD)
  calc (X + D)ᵀ * A * (X + D)
      = Xᵀ * A * X + Xᵀ * A * D + Dᵀ * A * X + Dᵀ * (A * D) := by
        rw [transpose_add]; noncomm_ring
    _ = A + Xᵀ * A * D + (Xᵀ * A * D)ᵀ := by
        rw [mem_isometryMatrices.mp hX, hDD, add_zero, transpose_mul, transpose_mul,
          transpose_transpose, hA]
        simp only [Matrix.mul_assoc]

/-- A matrix preserving a Gram matrix with unit determinant has unit determinant, its square
being `1`. -/
theorem isUnit_det_of_mem_isometryMatrices {A X : Matrix n n R} (hA : IsUnit A.det)
    (hX : X ∈ isometryMatrices A) : IsUnit X.det := by
  have h := congrArg det (mem_isometryMatrices.mp hX)
  rw [det_mul, det_mul, det_transpose] at h
  have h' : X.det * X.det * A.det = 1 * A.det := by linear_combination h
  exact IsUnit.of_mul_eq_one _ (hA.mul_left_injective h')

/-- **The count of matrices preserving a Gram matrix does not depend on the basis**: for an
invertible `P`, conjugation by `P` matches the solutions for `Pᵀ * A * P` with those for `A`. -/
theorem natCard_isometryMatrices_transpose_mul_mul {A P : Matrix n n R} (hP : IsUnit P.det) :
    Nat.card (isometryMatrices (Pᵀ * A * P)) = Nat.card (isometryMatrices A) := by
  have hPQ : P * P⁻¹ = 1 := mul_nonsing_inv P hP
  have hQP : P⁻¹ * P = 1 := nonsing_inv_mul P hP
  refine Nat.card_congr
    { toFun := fun X => ⟨P * X.1 * P⁻¹, ?_⟩
      invFun := fun Y => ⟨P⁻¹ * Y.1 * P, ?_⟩
      left_inv := fun X => Subtype.ext ?_
      right_inv := fun Y => Subtype.ext ?_ }
  · have hX := mem_isometryMatrices.mp X.2
    rw [mem_isometryMatrices]
    calc (P * X.1 * P⁻¹)ᵀ * A * (P * X.1 * P⁻¹)
        = P⁻¹ᵀ * (X.1ᵀ * (Pᵀ * A * P) * X.1) * P⁻¹ := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = (P * P⁻¹)ᵀ * A * (P * P⁻¹) := by
          rw [hX]
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = A := by rw [hPQ, transpose_one, Matrix.one_mul, Matrix.mul_one]
  · have hY := mem_isometryMatrices.mp Y.2
    rw [mem_isometryMatrices]
    calc (P⁻¹ * Y.1 * P)ᵀ * (Pᵀ * A * P) * (P⁻¹ * Y.1 * P)
        = Pᵀ * (Y.1ᵀ * ((P * P⁻¹)ᵀ * A * (P * P⁻¹)) * Y.1) * P := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = Pᵀ * A * P := by
          rw [hPQ, transpose_one, Matrix.one_mul, Matrix.mul_one, hY, Matrix.mul_assoc]
  · simp only [← Matrix.mul_assoc, hQP, Matrix.one_mul]
    rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
  · simp only [← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    rw [Matrix.mul_assoc, hPQ, Matrix.mul_one]

section SquareZero

variable {f : R →+* S}

/-- **Matrices preserving a Gram matrix lift across a square-zero extension.** Let `f` be a
surjective ring homomorphism whose kernel squares to zero, let `2` be a unit, and let `A` be
symmetric with unit determinant. Then every solution of `Yᵀ * A * Y = A` over the target is the
image of a solution over the source. -/
theorem exists_map_eq_of_mem_isometryMatrices_map (hf : Function.Surjective f)
    (hker : RingHom.ker f ^ 2 = ⊥) (h2 : IsUnit (2 : R)) {A : Matrix n n R} (hA : Aᵀ = A)
    (hdet : IsUnit A.det) {Y : Matrix n n S} (hY : Y ∈ isometryMatrices (A.map f)) :
    ∃ X ∈ isometryMatrices A, X.map f = Y := by
  obtain ⟨M, rfl⟩ : ∃ M : Matrix n n R, M.map f = Y :=
    ⟨of fun i j => (hf (Y i j)).choose, by ext i j; exact (hf (Y i j)).choose_spec⟩
  obtain ⟨c, hc⟩ : ∃ c : R, c * 2 = 1 := ⟨↑h2.unit⁻¹, h2.val_inv_mul⟩
  set E : Matrix n n R := A - Mᵀ * A * M with hE_def
  have hE : ∀ i j, E i j ∈ RingHom.ker f := by
    rw [forall_mem_ker_iff_map_eq_zero, hE_def, Matrix.map_sub f (map_sub f), Matrix.map_mul,
      Matrix.map_mul, transpose_map, mem_isometryMatrices.mp hY, sub_self]
  have hEt : Eᵀ = E := by
    rw [hE_def, transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hA,
      Matrix.mul_assoc]
  set Z : Matrix n n R := c • (A⁻¹ * E) with hZ_def
  have hZ : ∀ i j, Z i j ∈ RingHom.ker f := fun i j => by
    rw [hZ_def, smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (((RingHom.ker f).matrix n).mul_mem_left A⁻¹ hE i j)
  have hcE : ∀ i j, (c • E) i j ∈ RingHom.ker f := fun i j => by
    rw [smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hE i j)
  have hAZ : A * Z = c • E := by
    rw [hZ_def, Matrix.mul_smul, ← Matrix.mul_assoc, mul_nonsing_inv A hdet, Matrix.one_mul]
  have hZA : Zᵀ * A = c • E :=
    calc Zᵀ * A = (A * Z)ᵀ := by rw [transpose_mul, hA]
      _ = c • E := by rw [hAZ, transpose_smul, hEt]
  have hEE : c • E + c • E = E := by
    rw [← add_smul, ← two_mul, mul_comm, hc, one_smul]
  have hZt : ∀ i j, Zᵀ i j ∈ RingHom.ker f := fun i j => hZ j i
  have h₁ : Zᵀ * (A * Z) = 0 := by rw [hAZ]; exact mul_eq_zero_of_sq_eq_bot hker hZt hcE
  have h₂ : E * Z = 0 := mul_eq_zero_of_sq_eq_bot hker hE hZ
  have h₃ : Zᵀ * E = 0 := mul_eq_zero_of_sq_eq_bot hker hZt hE
  refine ⟨M * (1 + Z), ?_, ?_⟩
  · rw [mem_isometryMatrices]
    have hME : Mᵀ * A * M = A - E := by rw [hE_def, sub_sub_cancel]
    calc (M * (1 + Z))ᵀ * A * (M * (1 + Z))
        = (1 + Zᵀ) * (Mᵀ * A * M) * (1 + Z) := by
          simp only [transpose_mul, transpose_add, transpose_one, Matrix.mul_assoc]
      _ = A - E + A * Z + Zᵀ * A + Zᵀ * (A * Z) - E * Z - Zᵀ * E - Zᵀ * E * Z := by
          rw [hME]; noncomm_ring
      _ = A := by
          rw [h₁, hAZ, hZA, h₂, h₃, Matrix.zero_mul, add_assoc (A - E), hEE]
          abel
  · rw [Matrix.map_mul, Matrix.map_add f (map_add f), Matrix.map_one f f.map_zero f.map_one,
      forall_mem_ker_iff_map_eq_zero.mp hZ, add_zero, Matrix.mul_one]

/-- **The solutions congruent to a given one modulo a square-zero ideal form a torsor under the
skew-symmetric matrices with entries in the ideal.** Let `A` be symmetric with unit determinant
and let `X₀` preserve `A`. The solutions `X` with `X - X₀` having entries in a square-zero
ideal `I` correspond to the skew-symmetric `K` with entries in `I`, via
`K = X₀ᵀ * A * (X - X₀)` and `X = X₀ + (X₀ᵀ * A)⁻¹ * K`. -/
noncomputable def isometryMatricesFiberEquiv {I : Ideal R} (hI : I ^ 2 = ⊥) {A X₀ : Matrix n n R}
    (hA : Aᵀ = A) (hdet : IsUnit A.det) (hX₀ : X₀ ∈ isometryMatrices A) :
    {X : isometryMatrices A // ∀ i j, X.1 i j - X₀ i j ∈ I} ≃
      {K : Matrix n n R // (∀ i j, K i j ∈ I) ∧ Kᵀ = -K} :=
  have hB : IsUnit (X₀ᵀ * A).det := by
    rw [det_mul, det_transpose]
    exact (isUnit_det_of_mem_isometryMatrices hdet hX₀).mul hdet
  have hinv : ∀ K : Matrix n n R, (∀ i j, K i j ∈ I) → ∀ i j, ((X₀ᵀ * A)⁻¹ * K) i j ∈ I :=
    fun _ hK => (I.matrix n).mul_mem_left _ hK
  { toFun := fun X => ⟨X₀ᵀ * A * (X.1.1 - X₀), (I.matrix n).mul_mem_left _ X.2, by
      have h := add_transpose_mul_mul_add_of_sq_eq_bot (D := X.1.1 - X₀) hI hA hX₀ X.2
      rw [add_sub_cancel, mem_isometryMatrices.mp X.1.2, add_assoc, left_eq_add] at h
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h⟩
    invFun := fun K => ⟨⟨X₀ + (X₀ᵀ * A)⁻¹ * K.1, by
      rw [mem_isometryMatrices, add_transpose_mul_mul_add_of_sq_eq_bot hI hA hX₀ (hinv _ K.2.1),
        ← Matrix.mul_assoc, mul_nonsing_inv _ hB, Matrix.one_mul, K.2.2, add_neg_cancel_right]⟩,
      fun i j => by simpa only [add_apply, add_sub_cancel_left] using hinv _ K.2.1 i j⟩
    left_inv := fun X => by
      ext : 2
      dsimp only
      rw [← Matrix.mul_assoc, nonsing_inv_mul _ hB, Matrix.one_mul, add_sub_cancel]
    right_inv := fun K => by
      ext : 1
      dsimp only
      rw [add_sub_cancel_left, ← Matrix.mul_assoc, mul_nonsing_inv _ hB, Matrix.one_mul] }

/-- `Matrix.isometryMatricesFiberEquiv` sends a solution `X` to `X₀ᵀ * A * (X - X₀)`. -/
@[simp]
theorem isometryMatricesFiberEquiv_apply_coe {I : Ideal R} (hI : I ^ 2 = ⊥)
    {A X₀ : Matrix n n R} (hA : Aᵀ = A) (hdet : IsUnit A.det) (hX₀ : X₀ ∈ isometryMatrices A)
    (X : {X : isometryMatrices A // ∀ i j, X.1 i j - X₀ i j ∈ I}) :
    (isometryMatricesFiberEquiv hI hA hdet hX₀ X : Matrix n n R) = X₀ᵀ * A * (X.1.1 - X₀) :=
  -- `(rfl)` opts out of exporting the definitional equality, so the equivalence can remain
  -- opaque while this theorem and the next provide its rewriting interface.
  (rfl)

/-- The inverse of `Matrix.isometryMatricesFiberEquiv` sends a skew-symmetric `K` to
`X₀ + (X₀ᵀ * A)⁻¹ * K`. -/
@[simp]
theorem isometryMatricesFiberEquiv_symm_apply_coe_coe {I : Ideal R} (hI : I ^ 2 = ⊥)
    {A X₀ : Matrix n n R} (hA : Aᵀ = A) (hdet : IsUnit A.det) (hX₀ : X₀ ∈ isometryMatrices A)
    (K : {K : Matrix n n R // (∀ i j, K i j ∈ I) ∧ Kᵀ = -K}) :
    (((isometryMatricesFiberEquiv hI hA hdet hX₀).symm K : isometryMatrices A) : Matrix n n R) =
      X₀ + (X₀ᵀ * A)⁻¹ * K.1 :=
  (rfl)

/-- **Counting matrices preserving a Gram matrix across a square-zero extension.** Let `f` be a
surjective ring homomorphism whose kernel squares to zero, let `2` be a unit, and let `A` be
symmetric with unit determinant. The solutions over the source lying above a solution over the
target are a torsor under the skew-symmetric matrices with entries in `ker f`
(`Matrix.isometryMatricesFiberEquiv`), so the `Nat.card` of the solutions over the source is
`Nat.card (ker f) ^ (k.choose 2)` times that over the target, for `k` the size of the index
type. -/
theorem natCard_isometryMatrices_eq_pow_mul (hf : Function.Surjective f)
    (hker : RingHom.ker f ^ 2 = ⊥) (h2 : IsUnit (2 : R)) {A : Matrix n n R} (hA : Aᵀ = A)
    (hdet : IsUnit A.det) :
    Nat.card (isometryMatrices A) =
      Nat.card (RingHom.ker f) ^ (Fintype.card n).choose 2 *
        Nat.card (isometryMatrices (A.map f)) := by
  choose s hs hsf using fun Y : isometryMatrices (A.map f) =>
    exists_map_eq_of_mem_isometryMatrices_map hf hker h2 hA hdet Y.2
  let red : isometryMatrices A → isometryMatrices (A.map f) :=
    fun X => ⟨X.1.map f, map_mem_isometryMatrices_map f X.2⟩
  have hfiber : ∀ (Y) (X : isometryMatrices A),
      red X = Y ↔ ∀ i j, X.1 i j - s Y i j ∈ RingHom.ker f := fun Y X => by
    refine Iff.trans ?_ (forall_mem_ker_iff_map_eq_zero (f := f) (D := X.1 - s Y)).symm
    rw [Matrix.map_sub f (map_sub f), hsf, sub_eq_zero, Subtype.ext_iff]
  have h2' : ∀ x : R, x + x = 0 → x = 0 := fun x hx => by
    rw [← two_mul] at hx
    exact (h2.mul_right_eq_zero).mp hx
  have hskew : Nat.card {K : Matrix n n R // (∀ i j, K i j ∈ RingHom.ker f) ∧ Kᵀ = -K} =
      Nat.card (RingHom.ker f) ^ (Fintype.card n).choose 2 :=
    natCard_transpose_eq_neg (RingHom.ker f).toAddSubgroup h2'
  rw [mul_comm, ← hskew, ← Nat.card_prod]
  -- group the solutions by their reduction; each fibre is a torsor under `hskew`'s matrices
  exact Nat.card_congr <| (Equiv.sigmaFiberEquiv red).symm.trans <|
    (Equiv.sigmaCongrRight fun Y => (Equiv.subtypeEquivRight (hfiber Y)).trans
      (isometryMatricesFiberEquiv hker hA hdet (hs Y))).trans
    (Equiv.sigmaEquivProd _ _)

end SquareZero

end Matrix
