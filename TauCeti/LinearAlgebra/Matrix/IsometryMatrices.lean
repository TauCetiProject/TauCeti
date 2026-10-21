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

For a square matrix `A` over a commutative ring, `Matrix.isometryMatrices A` is the set of
matrices `X` with `Xᵀ * A * X = A`, the endomorphisms of the coordinate module that preserve the
bilinear form with Gram matrix `A`. Counting these matrices over the finite rings
`ZMod (p ^ r)` is how the local density of a quadratic lattice is defined, and the two results
here are what that count needs.

* A change of basis `A ↦ Pᵀ * A * P` by an invertible `P` conjugates the set by `P`, so its
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
* `Matrix.natCard_isometryMatrices_eq_pow_mul`: the count across such a surjection.

## References

* C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36
  (1935), where the local densities are defined by these counts.
-/

public section

namespace Matrix

variable {n R S : Type*} [Fintype n] [CommRing R] [CommRing S]

/-- The matrices `X` with `Xᵀ * A * X = A`, the endomorphisms of the coordinate module that
preserve the bilinear form with Gram matrix `A`. -/
def isometryMatrices (A : Matrix n n R) : Set (Matrix n n R) :=
  {X | Xᵀ * A * X = A}

/-- Membership in `isometryMatrices A` is the equation `Xᵀ * A * X = A`. -/
@[simp]
theorem mem_isometryMatrices {A X : Matrix n n R} :
    X ∈ isometryMatrices A ↔ Xᵀ * A * X = A :=
  Iff.rfl

/-- The identity matrix preserves every Gram matrix. -/
theorem one_mem_isometryMatrices [DecidableEq n] (A : Matrix n n R) : 1 ∈ isometryMatrices A := by
  simp

/-- The matrices preserving a Gram matrix are closed under multiplication. -/
theorem mul_mem_isometryMatrices {A X Y : Matrix n n R} (hX : X ∈ isometryMatrices A)
    (hY : Y ∈ isometryMatrices A) : X * Y ∈ isometryMatrices A := by
  rw [mem_isometryMatrices] at *
  calc (X * Y)ᵀ * A * (X * Y) = Yᵀ * (Xᵀ * A * X) * Y := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = A := by rw [hX, hY]

/-- A ring homomorphism carries solutions of `Xᵀ * A * X = A` to solutions for the image of
`A`. -/
theorem map_mem_isometryMatrices_map (f : R →+* S) {A X : Matrix n n R}
    (hX : X ∈ isometryMatrices A) : X.map f ∈ isometryMatrices (A.map f) := by
  rw [mem_isometryMatrices] at *
  rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hX]

variable [DecidableEq n]

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

/-- **Counting matrices preserving a Gram matrix across a square-zero extension.** Let `f` be a
surjective ring homomorphism whose kernel squares to zero, let `2` be a unit, and let `A` be
symmetric with unit determinant. The solutions over the source lying above a solution over the
target are a torsor under the skew-symmetric matrices with entries in `ker f`, so the `Nat.card`
of the solutions over the source is `Nat.card (ker f) ^ (k.choose 2)` times that over the target,
for `k` the size of the index type. When the source is finite, above each solution over the
target lie exactly `Nat.card (ker f) ^ (k.choose 2)` solutions over the source. -/
theorem natCard_isometryMatrices_eq_pow_mul (hf : Function.Surjective f)
    (hker : RingHom.ker f ^ 2 = ⊥) (h2 : IsUnit (2 : R)) {A : Matrix n n R} (hA : Aᵀ = A)
    (hdet : IsUnit A.det) :
    Nat.card (isometryMatrices A) =
      Nat.card (RingHom.ker f) ^ (Fintype.card n).choose 2 *
        Nat.card (isometryMatrices (A.map f)) := by
  choose s hs hsf using fun Y : isometryMatrices (A.map f) =>
    exists_map_eq_of_mem_isometryMatrices_map hf hker h2 hA hdet Y.2
  have hB : ∀ Y, IsUnit ((s Y)ᵀ * A).det := fun Y => by
    rw [det_mul, det_transpose]
    exact (isUnit_det_of_mem_isometryMatrices hdet (hs Y)).mul hdet
  have hBB : ∀ Y, ((s Y)ᵀ * A) * ((s Y)ᵀ * A)⁻¹ = 1 := fun Y => mul_nonsing_inv _ (hB Y)
  have hBB' : ∀ Y, ((s Y)ᵀ * A)⁻¹ * ((s Y)ᵀ * A) = 1 := fun Y => nonsing_inv_mul _ (hB Y)
  -- Writing a solution as `s Y + D` above its image `Y`, the matrix `K = (s Y)ᵀ * A * D` is
  -- skew-symmetric, because the quadratic term `Dᵀ * A * D` vanishes.
  have hexpand : ∀ (X₀ D : Matrix n n R), X₀ ∈ isometryMatrices A →
      (∀ i j, D i j ∈ RingHom.ker f) →
      (X₀ + D)ᵀ * A * (X₀ + D) = A + X₀ᵀ * A * D + (X₀ᵀ * A * D)ᵀ := by
    intro X₀ D hX₀ hD
    have hDD : Dᵀ * (A * D) = 0 :=
      mul_eq_zero_of_sq_eq_bot hker (fun i j => hD j i)
        (((RingHom.ker f).matrix n).mul_mem_left A hD)
    calc (X₀ + D)ᵀ * A * (X₀ + D)
        = X₀ᵀ * A * X₀ + X₀ᵀ * A * D + Dᵀ * A * X₀ + Dᵀ * (A * D) := by
          rw [transpose_add]; noncomm_ring
      _ = A + X₀ᵀ * A * D + (X₀ᵀ * A * D)ᵀ := by
          rw [mem_isometryMatrices.mp hX₀, hDD, add_zero, transpose_mul, transpose_mul,
            transpose_transpose, hA]
          simp only [Matrix.mul_assoc]
  have hsub : ∀ X : isometryMatrices A, ∀ i j,
      (X.1 - s ⟨X.1.map f, map_mem_isometryMatrices_map f X.2⟩) i j ∈ RingHom.ker f :=
    fun X => forall_mem_ker_iff_map_eq_zero.mpr <| by
      rw [Matrix.map_sub f (map_sub f), hsf, sub_self]
  have hinv : ∀ Y (K : Matrix n n R), (∀ i j, K i j ∈ RingHom.ker f) →
      ∀ i j, (((s Y)ᵀ * A)⁻¹ * K) i j ∈ RingHom.ker f :=
    fun Y K hK => ((RingHom.ker f).matrix n).mul_mem_left _ hK
  have h2' : ∀ x : R, x + x = 0 → x = 0 := fun x hx => by
    rw [← two_mul] at hx
    exact (h2.mul_right_eq_zero).mp hx
  have hskew : Nat.card {K : Matrix n n R // (∀ i j, K i j ∈ RingHom.ker f) ∧ Kᵀ = -K} =
      Nat.card (RingHom.ker f) ^ (Fintype.card n).choose 2 :=
    natCard_transpose_eq_neg (RingHom.ker f).toAddSubgroup h2'
  rw [mul_comm, ← hskew, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun X =>
        (⟨X.1.map f, map_mem_isometryMatrices_map f X.2⟩,
          ⟨(s ⟨X.1.map f, map_mem_isometryMatrices_map f X.2⟩)ᵀ * A *
            (X.1 - s ⟨X.1.map f, map_mem_isometryMatrices_map f X.2⟩),
            ((RingHom.ker f).matrix n).mul_mem_left _ (hsub X), ?_⟩)
      invFun := fun YK => ⟨s YK.1 + ((s YK.1)ᵀ * A)⁻¹ * YK.2.1, ?_⟩
      left_inv := fun X => Subtype.ext ?_
      right_inv := fun YK => ?_ }
  · -- the correction of a solution is skew-symmetric
    have h := hexpand (s ⟨X.1.map f, map_mem_isometryMatrices_map f X.2⟩)
      (X.1 - s ⟨X.1.map f, map_mem_isometryMatrices_map f X.2⟩) (hs _) (hsub X)
    rw [add_sub_cancel, mem_isometryMatrices.mp X.2, add_assoc, left_eq_add] at h
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h
  · -- a skew-symmetric correction gives a solution
    rw [mem_isometryMatrices, hexpand _ _ (hs _) (hinv _ _ YK.2.2.1), ← Matrix.mul_assoc,
      hBB, Matrix.one_mul, YK.2.2.2, add_neg_cancel_right]
  · dsimp only
    rw [← Matrix.mul_assoc, hBB', Matrix.one_mul, add_sub_cancel]
  · obtain ⟨Y, K, hK, hKt⟩ := YK
    have hmap : (s Y + ((s Y)ᵀ * A)⁻¹ * K).map f = Y := by
      rw [Matrix.map_add f (map_add f), hsf, forall_mem_ker_iff_map_eq_zero.mp (hinv Y K hK),
        add_zero]
    have hY : (⟨(s Y + ((s Y)ᵀ * A)⁻¹ * K).map f,
        map_mem_isometryMatrices_map f (by
          rw [mem_isometryMatrices, hexpand _ _ (hs _) (hinv _ _ hK), ← Matrix.mul_assoc, hBB,
            Matrix.one_mul, hKt, add_neg_cancel_right])⟩ : isometryMatrices (A.map f)) = Y :=
      Subtype.ext hmap
    refine Prod.ext hY (Subtype.ext ?_)
    dsimp only
    rw [hY, add_sub_cancel_left, ← Matrix.mul_assoc, hBB, Matrix.one_mul]

end SquareZero

end Matrix
