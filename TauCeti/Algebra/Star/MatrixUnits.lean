/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.Algebra.Star.PartialIsometry
public import TauCeti.Algebra.Star.Projection.Family
import Mathlib.Data.Matrix.Basis

/-!
# Systems of matrix units in a star ring

Multi-block **systems of matrix units** `e : ∀ r : κ, n r → n r → R` parameterize `⋆`-homomorphisms
(and embeddings when each nonempty block has `e r i i ≠ 0`) from `⨁ᵣ M_{n(r)}(ℂ)` into a C⋆-algebra,
governing AF algebras and operator K-theory. Partial-isometry families with block-constant initial
projections and pairwise-orthogonal final projections generate matrix units `v r i * star (v r j)`,
and over a characteristic-zero field `𝕜`, `z = matrixUnitIntertwiner 𝕜 e f` satisfies
`f r i j * z = z * e r i j` with `z = 1` when `e = f`.

## Main results

* `TauCeti.IsMatrixUnitSystem`, `TauCeti.IsUnitalMatrixUnitSystem`, `TauCeti.matrixUnitSupport`,
  `TauCeti.matrixUnitBlockSupport`, `TauCeti.matrixUnitIntertwiner`,
  `TauCeti.IsMatrixUnitSystem.of_partialIsometry`,
  `TauCeti.isUnitalMatrixUnitSystem_piSingle_matrixSingle`,
  `TauCeti.IsMatrixUnitSystem.matrixUnitIntertwiner_self`,
  `TauCeti.IsMatrixUnitSystem.mul_matrixUnitIntertwiner_eq_matrixUnitIntertwiner_mul`.

## References

* B. Blackadar, *Operator Algebras*, Springer (2006), Proposition II.8.3.23.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge Univ. Press (1998), Ch. III.
-/

public section

open Function

namespace TauCeti
variable {κ : Type*} {n : κ → Type*} {R S : Type*}
/-- A multi-block **system of matrix units** in `R` with multiplication, zero, and star. -/
@[mk_iff]
structure IsMatrixUnitSystem [Mul R] [Zero R] [Star R] (e : ∀ r : κ, n r → n r → R) : Prop where
  /-- Taking the star transposes indices within each block. -/
  star_eq (r : κ) (i j : n r) : star (e r i j) = e r j i
  /-- Composable entries within a block multiply by contracting the middle index. -/
  mul_same (r : κ) (i j l : n r) : e r i j * e r j l = e r i l
  /-- Non-composable entries within a block multiply to `0`. -/
  mul_eq_zero_of_ne (r : κ) (i : n r) {j k : n r} (l : n r) : j ≠ k → e r i j * e r k l = 0
  /-- Entries from distinct blocks multiply to `0`. -/
  mul_eq_zero_of_block_ne {r s : κ} : r ≠ s → ∀ (i j : n r) (k l : n s), e r i j * e s k l = 0

namespace IsMatrixUnitSystem
section
variable [Mul R] [Zero R] [Star R] {e : ∀ r : κ, n r → n r → R}
/-- Kronecker-delta form of multiplication within a single block `r`. -/
theorem mul_eq_ite (he : IsMatrixUnitSystem e) (r : κ) [DecidableEq (n r)] (i j k l : n r) :
    e r i j * e r k l = if j = k then e r i l else 0 := by
  split_ifs with h; exacts [h ▸ he.mul_same r i j l, he.mul_eq_zero_of_ne r i l h]
/-- Every diagonal entry `e r i i` is a star projection. -/
theorem isStarProjection_diag (he : IsMatrixUnitSystem e) (r : κ) (i : n r) :
    IsStarProjection (e r i i) := ⟨he.mul_same r i i i, he.star_eq r i i⟩
/-- The final projection `e r i j * star (e r i j)` of `e r i j` is `e r i i`. -/
theorem mul_star_self (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    e r i j * star (e r i j) = e r i i := by rw [he.star_eq, he.mul_same]
/-- The initial projection `star (e r i j) * e r i j` of `e r i j` is `e r j j`. -/
theorem star_mul_self (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    star (e r i j) * e r i j = e r j j := by rw [he.star_eq, he.mul_same]
/-- Every entry `e r i j` of a system of matrix units is a partial isometry. -/
theorem isPartialIsometry (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    IsPartialIsometry (e r i j) := by rw [isPartialIsometry_iff, he.mul_star_self, he.mul_same]
/-- Any star-preserving multiplicative zero-preserving map preserves `IsMatrixUnitSystem`. -/
theorem map [Mul S] [Zero S] [Star S] {F : Type*} [FunLike F R S] [MulHomClass F R S]
    [ZeroHomClass F R S] [StarHomClass F R S] (he : IsMatrixUnitSystem e) (φ : F) :
    IsMatrixUnitSystem (fun r i j ↦ φ (e r i j)) :=
  ⟨fun r i j ↦ by rw [← map_star, he.star_eq], fun r i j l ↦ by rw [← map_mul, he.mul_same],
   fun r i _ _ l h ↦ by rw [← map_mul, he.mul_eq_zero_of_ne r i l h, map_zero],
   fun hrs i j k l ↦ by rw [← map_mul, he.mul_eq_zero_of_block_ne hrs i j k l, map_zero]⟩
end

/-- The zero family is a system of matrix units. -/
@[simp] theorem zero [NonUnitalNonAssocSemiring R] [StarAddMonoid R] :
    IsMatrixUnitSystem (0 : ∀ r : κ, n r → n r → R) :=
  ⟨fun _ _ _ ↦ star_zero R, fun _ _ _ _ ↦ mul_zero 0,
   fun _ _ _ _ _ _ ↦ mul_zero 0, fun _ _ _ _ _ ↦ mul_zero 0⟩
/-- The diagonal projections `(r, i) ↦ e r i i` are pairwise star-orthogonal. -/
theorem pairwise_isStarOrtho_diag [NonUnitalSemiring R] [StarRing R]
    {e : ∀ r : κ, n r → n r → R} (he : IsMatrixUnitSystem e) :
    Pairwise (IsStarOrtho on fun x : Σ r, n r ↦ e x.1 x.2 x.2) := by
  rintro ⟨r, i⟩ ⟨s, k⟩ hxy
  rw [onFun, (he.isStarProjection_diag r i).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero
    (he.isStarProjection_diag s k).isSelfAdjoint]
  by_cases hrs : r = s
  · subst hrs; exact he.mul_eq_zero_of_ne r i k fun hik ↦ hxy (congrArg (Sigma.mk r) hik)
  · exact he.mul_eq_zero_of_block_ne hrs i i k k
/-- Construct `e r i j = v r i * star (v r j)` from partial isometries with block-constant initial
projections and pairwise-orthogonal final projections. -/
theorem of_partialIsometry [SemigroupWithZero R] [StarMul R] {v : ∀ r : κ, n r → R}
    (hv : ∀ r i, IsPartialIsometry (v r i))
    (hinit : ∀ r i j, star (v r i) * v r i = star (v r j) * v r j)
    (hortho : Pairwise ((fun a b : R ↦ a * b = 0) on fun x : Σ r, n r ↦
      v x.1 x.2 * star (v x.1 x.2))) : IsMatrixUnitSystem (fun r i j ↦ v r i * star (v r j)) := by
  have hsm {x y : Σ r, n r} (hxy : x ≠ y) : star (v x.1 x.2) * v y.1 y.2 = 0 := by
    rw [← (hv x.1 x.2).star.mul_star_mul_self, star_star, ← (hv y.1 y.2).mul_star_mul_self]
    simpa [mul_assoc] using congrArg (star (v x.1 x.2) * · * v y.1 y.2) (hortho hxy)
  have hzero {x y : Σ r, n r} (hxy : x ≠ y) (a b : R) :
      a * star (v x.1 x.2) * (v y.1 y.2 * b) = 0 := by
    rw [mul_assoc, ← mul_assoc (star (v x.1 x.2)), hsm hxy, zero_mul, mul_zero]
  exact ⟨fun _ _ _ ↦ by simp [star_mul], fun r i j _ ↦ by
      rw [mul_assoc, ← mul_assoc (star (v r j)), hinit r j i, ← mul_assoc, ← mul_assoc,
        (hv r i).mul_star_mul_self],
    fun r _ {j k} _ hjk ↦ hzero (x := ⟨r, j⟩) (y := ⟨r, k⟩) (by simpa using hjk) _ _,
    fun {r s} hrs _ j k _ ↦ hzero (x := ⟨r, j⟩) (y := ⟨s, k⟩) (fun h ↦ hrs (by cases h; rfl)) _ _⟩
end IsMatrixUnitSystem

section
variable [∀ r, Fintype (n r)]
section
variable [AddCommMonoid R]
/-- The **block diagonal sum** `∑ i : n r, e r i i` (a star projection for matrix-unit systems). -/
def matrixUnitBlockSupport (e : ∀ r : κ, n r → n r → R) (r : κ) : R := ∑ i : n r, e r i i
/-- The **total diagonal sum** `∑ r, matrixUnitBlockSupport e r`. -/
def matrixUnitSupport [Fintype κ] (e : ∀ r : κ, n r → n r → R) : R :=
  ∑ r : κ, matrixUnitBlockSupport e r
/-- Unfold `TauCeti.matrixUnitBlockSupport`. -/
theorem matrixUnitBlockSupport_def (e : ∀ r : κ, n r → n r → R) (r : κ) :
    matrixUnitBlockSupport e r = ∑ i : n r, e r i i := (rfl)
/-- Express `TauCeti.matrixUnitSupport` as the sum of `TauCeti.matrixUnitBlockSupport`. -/
theorem matrixUnitSupport_eq_sum_blockSupport [Fintype κ] (e : ∀ r : κ, n r → n r → R) :
    matrixUnitSupport e = ∑ r : κ, matrixUnitBlockSupport e r := (rfl)
/-- Unfold `TauCeti.matrixUnitSupport` to the double diagonal sum `∑ r, ∑ i, e r i i`. -/
theorem matrixUnitSupport_def [Fintype κ] (e : ∀ r : κ, n r → n r → R) :
    matrixUnitSupport e = ∑ r : κ, ∑ i : n r, e r i i := (rfl)
/-- The block support of the zero family is `0`. -/
@[simp] theorem matrixUnitBlockSupport_zero (r : κ) :
    matrixUnitBlockSupport (0 : ∀ r, n r → n r → R) r = 0 := by simp [matrixUnitBlockSupport_def]
/-- The total support of the zero family is `0`. -/
@[simp] theorem matrixUnitSupport_zero [Fintype κ] :
    matrixUnitSupport (0 : ∀ r, n r → n r → R) = 0 := by simp [matrixUnitSupport_def]
/-- `matrixUnitBlockSupport e r` lies in any additive submonoid containing block `r`'s diagonal. -/
theorem matrixUnitBlockSupport_mem {T : Type*} [SetLike T R] [AddSubmonoidClass T R] {s : T}
    {e : ∀ r : κ, n r → n r → R} {r : κ} (he : ∀ i, e r i i ∈ s) :
    matrixUnitBlockSupport e r ∈ s := sum_mem fun i _ ↦ he i
/-- `matrixUnitSupport e` lies in any additive submonoid containing all diagonal entries of `e`. -/
theorem matrixUnitSupport_mem [Fintype κ] {T : Type*} [SetLike T R] [AddSubmonoidClass T R] {s : T}
    {e : ∀ r : κ, n r → n r → R} (he : ∀ r i, e r i i ∈ s) :
    matrixUnitSupport e ∈ s := sum_mem fun r _ ↦ matrixUnitBlockSupport_mem (he r)
/-- Additive monoid homomorphisms preserve `TauCeti.matrixUnitBlockSupport`. -/
theorem map_matrixUnitBlockSupport [AddCommMonoid S] {F : Type*} [FunLike F R S]
    [AddMonoidHomClass F R S] (φ : F) (e : ∀ r : κ, n r → n r → R) (r : κ) :
    φ (matrixUnitBlockSupport e r) = matrixUnitBlockSupport (fun r i j ↦ φ (e r i j)) r := by
  simp [matrixUnitBlockSupport_def]
/-- Additive monoid homomorphisms preserve `TauCeti.matrixUnitSupport`. -/
theorem map_matrixUnitSupport [AddCommMonoid S] [Fintype κ] {F : Type*} [FunLike F R S]
    [AddMonoidHomClass F R S] (φ : F) (e : ∀ r : κ, n r → n r → R) :
    φ (matrixUnitSupport e) = matrixUnitSupport (fun r i j ↦ φ (e r i j)) := by
  simp [matrixUnitSupport_def]
end

/-- A finite system of matrix units is **unital** if its total support projection equals `1`. -/
@[mk_iff]
structure IsUnitalMatrixUnitSystem [Semiring R] [Star R] [Fintype κ]
    (e : ∀ r : κ, n r → n r → R) : Prop extends IsMatrixUnitSystem e where
  /-- The diagonal projections sum to `1`. -/
  support_eq_one : matrixUnitSupport e = 1

namespace IsMatrixUnitSystem
variable [NonUnitalSemiring R] [StarRing R] {e : ∀ r : κ, n r → n r → R}
/-- Each block support `matrixUnitBlockSupport e r` is a star projection. -/
theorem isStarProjection_blockSupport (he : IsMatrixUnitSystem e) (r : κ) :
    IsStarProjection (matrixUnitBlockSupport e r) :=
  IsStarProjection.sum (fun i _ ↦ he.isStarProjection_diag r i) fun i _ j _ hij ↦
    he.pairwise_isStarOrtho_diag (i := ⟨r, i⟩) (j := ⟨r, j⟩) (by simpa using hij)
/-- The block support projections `matrixUnitBlockSupport e` are pairwise star-orthogonal. -/
theorem pairwise_isStarOrtho_blockSupport (he : IsMatrixUnitSystem e) :
    Pairwise (IsStarOrtho on matrixUnitBlockSupport e) := fun r s hrs ↦ by
  rw [onFun, (he.isStarProjection_blockSupport r).isSelfAdjoint.isStarOrtho_iff_mul_eq_zero
    (he.isStarProjection_blockSupport s).isSelfAdjoint]
  simp [matrixUnitBlockSupport_def, Finset.sum_mul, Finset.mul_sum, he.mul_eq_zero_of_block_ne hrs]
/-- For finite `κ`, the total support `matrixUnitSupport e` is a star projection. -/
theorem isStarProjection_support [Fintype κ] (he : IsMatrixUnitSystem e) :
    IsStarProjection (matrixUnitSupport e) :=
  IsStarProjection.sum (fun r _ ↦ he.isStarProjection_blockSupport r)
    (he.pairwise_isStarOrtho_blockSupport.set_pairwise _)
/-- Right-multiplying `e r i j` by its own block support leaves `e r i j` fixed. -/
theorem mul_blockSupport (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    e r i j * matrixUnitBlockSupport e r = e r i j := by
  classical simp [matrixUnitBlockSupport_def, Finset.mul_sum, he.mul_eq_ite]
/-- Left-multiplying `e r i j` by its own block support leaves `e r i j` fixed. -/
theorem blockSupport_mul (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    matrixUnitBlockSupport e r * e r i j = e r i j := by
  classical simp [matrixUnitBlockSupport_def, Finset.sum_mul, he.mul_eq_ite]
/-- Entries from block `r` annihilate block supports from any distinct block `s`. -/
theorem mul_blockSupport_eq_zero_of_ne (he : IsMatrixUnitSystem e) {r s : κ} (hrs : r ≠ s)
    (i j : n r) : e r i j * matrixUnitBlockSupport e s = 0 := by
  simp [matrixUnitBlockSupport_def, Finset.mul_sum, he.mul_eq_zero_of_block_ne hrs]
/-- Block supports from block `r` annihilate entries from any distinct block `s`. -/
theorem blockSupport_mul_eq_zero_of_ne (he : IsMatrixUnitSystem e) {r s : κ} (hrs : r ≠ s)
    (i j : n s) : matrixUnitBlockSupport e r * e s i j = 0 := by
  simp [matrixUnitBlockSupport_def, Finset.sum_mul, he.mul_eq_zero_of_block_ne hrs]
/-- Right-multiplying `e r i j` by `matrixUnitSupport e` leaves `e r i j` fixed. -/
theorem mul_support [Fintype κ] (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    e r i j * matrixUnitSupport e = e r i j := by
  rw [matrixUnitSupport_eq_sum_blockSupport, Finset.mul_sum, Finset.sum_eq_single_of_mem r
    (Finset.mem_univ r) fun _ _ h ↦ he.mul_blockSupport_eq_zero_of_ne h.symm i j,
    he.mul_blockSupport]
/-- Left-multiplying `e r i j` by `matrixUnitSupport e` leaves `e r i j` fixed. -/
theorem support_mul [Fintype κ] (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    matrixUnitSupport e * e r i j = e r i j := by
  rw [matrixUnitSupport_eq_sum_blockSupport, Finset.sum_mul, Finset.sum_eq_single_of_mem r
    (Finset.mem_univ r) fun _ _ h ↦ he.blockSupport_mul_eq_zero_of_ne h i j, he.blockSupport_mul]
end IsMatrixUnitSystem

namespace IsUnitalMatrixUnitSystem
variable [Semiring R] [Fintype κ] {e : ∀ r : κ, n r → n r → R}
/-- Any unital star-ring homomorphism preserves `TauCeti.IsUnitalMatrixUnitSystem`. -/
theorem map [Star R] [Semiring S] [Star S] {F : Type*} [FunLike F R S] [RingHomClass F R S]
    [StarHomClass F R S] (he : IsUnitalMatrixUnitSystem e) (φ : F) :
    IsUnitalMatrixUnitSystem (fun r i j ↦ φ (e r i j)) :=
  ⟨he.toIsMatrixUnitSystem.map φ, by rw [← map_matrixUnitSupport, he.support_eq_one, map_one]⟩
/-- Block supports of a unital matrix-unit system form a complete orthogonal projection family. -/
theorem isCompleteOrthogonalProjectionFamily [StarRing R] (he : IsUnitalMatrixUnitSystem e) :
    IsCompleteOrthogonalProjectionFamily (matrixUnitBlockSupport e) :=
  ⟨⟨⟨fun r ↦ (he.isStarProjection_blockSupport r).isIdempotentElem, fun _ s hrs ↦
      (he.pairwise_isStarOrtho_blockSupport hrs).mul_eq_zero'
        (he.isStarProjection_blockSupport s).isSelfAdjoint⟩, he.support_eq_one⟩,
    fun r ↦ (he.isStarProjection_blockSupport r).isSelfAdjoint⟩
end IsUnitalMatrixUnitSystem

/-- Standard multi-block matrix units `(r, i, j) ↦ Pi.single r (Matrix.single i j 1)` in
`∀ r : κ, Matrix (n r) (n r) R` form a unital system of matrix units. -/
theorem isUnitalMatrixUnitSystem_piSingle_matrixSingle (R : Type*) [Semiring R] [StarRing R]
    [DecidableEq κ] [∀ r, DecidableEq (n r)] [Fintype κ] :
    IsUnitalMatrixUnitSystem (fun r (i j : n r) ↦ Pi.single r (Matrix.single i j (1 : R)) :
      ∀ r : κ, n r → n r → ∀ s : κ, Matrix (n s) (n s) R) where
  star_eq _ _ _ := by simp [Pi.star_single, Matrix.star_eq_conjTranspose]
  mul_same _ _ _ _ := by rw [← Pi.single_mul, Matrix.single_mul_single_same, mul_one]
  mul_eq_zero_of_ne _ _ {_ _} _ hjk := by simp [← Pi.single_mul, hjk]
  mul_eq_zero_of_block_ne hrs _ _ _ _ := by simp [← Pi.single_mul_left, Pi.single_eq_of_ne hrs]
  support_eq_one := by
    funext s; simp only [matrixUnitSupport_def, Pi.one_apply, Finset.sum_apply,
      ← AddMonoidHom.single_apply (f := fun r ↦ Matrix (n r) (n r) R), ← map_sum,
      Matrix.sum_single_one]; simp [AddMonoidHom.single_apply]

section
variable (𝕜 : Type*) [Field 𝕜] [Ring R] [Algebra 𝕜 R] [Fintype κ]
/-- The **canonical multi-block intertwiner**
`(1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) +`
`∑ r, (card (n r) : 𝕜)⁻¹ • ∑ a, ∑ b, f r a b * e r b a`. -/
def matrixUnitIntertwiner (e f : ∀ r : κ, n r → n r → R) : R :=
  (1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) +
    ∑ r : κ, (Fintype.card (n r) : 𝕜)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a
/-- Unfold `TauCeti.matrixUnitIntertwiner`. -/
theorem matrixUnitIntertwiner_def (e f : ∀ r : κ, n r → n r → R) :
    matrixUnitIntertwiner 𝕜 e f = (1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) +
      ∑ r : κ, (Fintype.card (n r) : 𝕜)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a := (rfl)
/-- With `0` on the left, `matrixUnitIntertwiner 𝕜 0 f = 1 - matrixUnitSupport f`. -/
@[simp] theorem matrixUnitIntertwiner_zero_left (f : ∀ r : κ, n r → n r → R) :
    matrixUnitIntertwiner 𝕜 0 f = 1 - matrixUnitSupport f := by simp [matrixUnitIntertwiner_def]
/-- With `0` on the right, `matrixUnitIntertwiner 𝕜 e 0 = 1 - matrixUnitSupport e`. -/
@[simp] theorem matrixUnitIntertwiner_zero_right (e : ∀ r : κ, n r → n r → R) :
    matrixUnitIntertwiner 𝕜 e 0 = 1 - matrixUnitSupport e := by simp [matrixUnitIntertwiner_def]
/-- `matrixUnitIntertwiner 𝕜 e f` belongs to any unital `𝕜`-subring containing `e` and `f`. -/
theorem matrixUnitIntertwiner_mem {T : Type*} [SetLike T R] [SubringClass T R] [SMulMemClass T 𝕜 R]
    {s : T} {e f : ∀ r : κ, n r → n r → R} (he : ∀ r i j, e r i j ∈ s) (hf : ∀ r i j, f r i j ∈ s) :
    matrixUnitIntertwiner 𝕜 e f ∈ s :=
  add_mem (mul_mem (sub_mem (one_mem s) (matrixUnitSupport_mem fun _ _ ↦ hf _ _ _))
      (sub_mem (one_mem s) (matrixUnitSupport_mem fun _ _ ↦ he _ _ _)))
    (sum_mem fun _ _ ↦ SMulMemClass.smul_mem _ <| sum_mem fun _ _ ↦ sum_mem fun _ _ ↦ mul_mem
      (hf _ _ _) (he _ _ _))
/-- Unital `𝕜`-algebra homomorphisms preserve `TauCeti.matrixUnitIntertwiner`. -/
theorem map_matrixUnitIntertwiner [Ring S] [Algebra 𝕜 S] {F : Type*} [FunLike F R S]
    [AlgHomClass F 𝕜 R S] (φ : F) (e f : ∀ r : κ, n r → n r → R) :
    φ (matrixUnitIntertwiner 𝕜 e f) =
      matrixUnitIntertwiner 𝕜 (fun r i j ↦ φ (e r i j)) (fun r i j ↦ φ (f r i j)) := by
  simp [matrixUnitIntertwiner_def, map_matrixUnitSupport]

namespace IsMatrixUnitSystem
variable [StarRing R] {e f : ∀ r : κ, n r → n r → R}
/-- In characteristic zero, the canonical intertwiner of `e` with itself is `1`. -/
@[simp] theorem matrixUnitIntertwiner_self [CharZero 𝕜] (he : IsMatrixUnitSystem e) :
    matrixUnitIntertwiner 𝕜 e e = 1 := by
  rw [matrixUnitIntertwiner_def, (he.isStarProjection_support.one_sub).isIdempotentElem.eq]
  suffices (∑ r : κ, (Fintype.card (n r) : 𝕜)⁻¹ • ∑ a : n r, ∑ b : n r, e r a b * e r b a) =
      matrixUnitSupport e by rw [this, sub_add_cancel]
  refine Finset.sum_congr rfl fun r _ ↦ ?_; by_cases hcard : Fintype.card (n r) = 0
  · have := Fintype.card_eq_zero_iff.mp hcard; simp [matrixUnitBlockSupport_def]
  · simp_rw [he.mul_same, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜,
      ← Finset.smul_sum, ← matrixUnitBlockSupport_def, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero (R := 𝕜).mpr hcard), one_smul]
/-- Left-multiplying `matrixUnitIntertwiner 𝕜 e f` by `f r i j` extracts the `(r, i, j)` sum. -/
theorem mul_matrixUnitIntertwiner (hf : IsMatrixUnitSystem f) (e : ∀ r : κ, n r → n r → R) (r : κ)
    (i j : n r) : f r i j * matrixUnitIntertwiner 𝕜 e f =
      (Fintype.card (n r) : 𝕜)⁻¹ • ∑ b : n r, f r i b * e r b j := by
  classical
  have hcomp : f r i j * ((1 - matrixUnitSupport f) * (1 - matrixUnitSupport e)) = 0 := by
    simp [← mul_assoc, mul_sub, hf.mul_support]
  have hblock : ∀ s ≠ r, f r i j *
      ((Fintype.card (n s) : 𝕜)⁻¹ • ∑ a : n s, ∑ b : n s, f s a b * e s b a) = 0 := fun s hsr ↦ by
    simp [Finset.mul_sum, ← mul_assoc, hf.mul_eq_zero_of_block_ne hsr.symm]
  rw [matrixUnitIntertwiner_def, mul_add, hcomp, zero_add, Finset.mul_sum,
    Finset.sum_eq_single_of_mem r (Finset.mem_univ r) fun s _ hsr ↦ hblock s hsr]
  simp [Finset.mul_sum, ← mul_assoc, hf.mul_eq_ite]
/-- Right-multiplying `matrixUnitIntertwiner 𝕜 e f` by `e r i j` extracts the `(r, i, j)` sum. -/
theorem matrixUnitIntertwiner_mul (he : IsMatrixUnitSystem e) (f : ∀ r : κ, n r → n r → R) (r : κ)
    (i j : n r) : matrixUnitIntertwiner 𝕜 e f * e r i j =
      (Fintype.card (n r) : 𝕜)⁻¹ • ∑ b : n r, f r i b * e r b j := by
  classical
  have hcomp : (1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) * e r i j = 0 := by
    simp [mul_assoc, sub_mul, he.support_mul]
  have hblock : ∀ s ≠ r,
      ((Fintype.card (n s) : 𝕜)⁻¹ • ∑ a : n s, ∑ b : n s, f s a b * e s b a) * e r i j = 0 :=
    fun s hsr ↦ by simp [Finset.sum_mul, mul_assoc, he.mul_eq_zero_of_block_ne hsr]
  rw [matrixUnitIntertwiner_def, add_mul, hcomp, zero_add, Finset.sum_mul,
    Finset.sum_eq_single_of_mem r (Finset.mem_univ r) fun s _ hsr ↦ hblock s hsr]
  simp [Finset.sum_mul, mul_assoc, he.mul_eq_ite]
/-- **Intertwining**: `f r i j * z = z * e r i j` for `z = matrixUnitIntertwiner 𝕜 e f`. -/
theorem mul_matrixUnitIntertwiner_eq_matrixUnitIntertwiner_mul (he : IsMatrixUnitSystem e)
    (hf : IsMatrixUnitSystem f) (r : κ) (i j : n r) :
    f r i j * matrixUnitIntertwiner 𝕜 e f = matrixUnitIntertwiner 𝕜 e f * e r i j := by
  rw [hf.mul_matrixUnitIntertwiner 𝕜, he.matrixUnitIntertwiner_mul 𝕜]
/-- Taking the star of `matrixUnitIntertwiner 𝕜 e f` swaps `e` and `f`. -/
theorem star_matrixUnitIntertwiner (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f) :
    star (matrixUnitIntertwiner 𝕜 e f) = matrixUnitIntertwiner 𝕜 f e := by
  simp only [matrixUnitIntertwiner_def, star_add, star_mul, star_sum, star_inv_natCast_smul,
    (he.isStarProjection_support.one_sub).isSelfAdjoint.star_eq,
    (hf.isStarProjection_support.one_sub).isSelfAdjoint.star_eq, he.star_eq, hf.star_eq]
/-- Adjoint intertwining: `star z * f r i j = e r i j * star z` for `matrixUnitIntertwiner`. -/
theorem star_matrixUnitIntertwiner_mul_eq_mul_star_matrixUnitIntertwiner (he : IsMatrixUnitSystem e)
    (hf : IsMatrixUnitSystem f) (r : κ) (i j : n r) :
    star (matrixUnitIntertwiner 𝕜 e f) * f r i j = e r i j * star (matrixUnitIntertwiner 𝕜 e f) :=
  he.star_matrixUnitIntertwiner 𝕜 hf ▸
    (hf.mul_matrixUnitIntertwiner_eq_matrixUnitIntertwiner_mul 𝕜 he r i j).symm
end IsMatrixUnitSystem

namespace IsUnitalMatrixUnitSystem
variable [Star R] {e f : ∀ r : κ, n r → n r → R}
/-- When `e` is unital, the complementary-support term in `matrixUnitIntertwiner 𝕜 e f` vanishes. -/
theorem matrixUnitIntertwiner_eq_of_left (he : IsUnitalMatrixUnitSystem e)
    (f : ∀ r : κ, n r → n r → R) : matrixUnitIntertwiner 𝕜 e f =
    ∑ r : κ, (Fintype.card (n r) : 𝕜)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a := by
  simp [matrixUnitIntertwiner_def, he.support_eq_one]
/-- When `f` is unital, the complementary-support term in `matrixUnitIntertwiner 𝕜 e f` vanishes. -/
theorem matrixUnitIntertwiner_eq_of_right (hf : IsUnitalMatrixUnitSystem f)
    (e : ∀ r : κ, n r → n r → R) : matrixUnitIntertwiner 𝕜 e f =
    ∑ r : κ, (Fintype.card (n r) : 𝕜)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a := by
  simp [matrixUnitIntertwiner_def, hf.support_eq_one]
end IsUnitalMatrixUnitSystem
end
end
end TauCeti
