/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.Orthogonal
public import Mathlib.Data.Fintype.Card
public import TauCeti.Algebra.Star.PartialIsometry

/-!
# Systems of matrix units in a star ring

A multi-block **system of matrix units** in a star ring `R`, indexed by a block type `κ` and block
index types `n : κ → Type*`, is a family `e : ∀ r : κ, n r → n r → R` satisfying
`star (e r i j) = e r j i`, `e r i j * e r j l = e r i l`, `e r i j * e r k l = 0` for `j ≠ k`,
and `e r i j * e s k l = 0` for `r ≠ s`. In a C⋆-algebra, a finite system of matrix units with
nonempty blocks spans a finite-dimensional C⋆-subalgebra isomorphic to a finite direct sum of full
matrix algebras.

Every diagonal entry `e r i i` is a star projection, the diagonal entries `(r, i) ↦ e r i i` are
pairwise star-orthogonal, and every entry `e r i j` is a partial isometry with initial projection
`e r j j` and final projection `e r i i`. Conversely, any family of partial isometries
`v : ∀ r : κ, n r → R` whose initial projections agree within each block and whose final
projections are pairwise orthogonal generates a system of matrix units
`e r i j = v r i * star (v r j)`.

When `κ` and each `n r` are finite and `R` is a unital star algebra over a characteristic-zero
field `𝕜`, two systems of matrix units `e` and `f` of the same shape admit the canonical
intertwiner

`(1 - E_f) * (1 - E_e) + ∑ r, (card (n r) : 𝕜)⁻¹ • ∑ a, ∑ b, f r a b * e r b a`

where `E_e` and `E_f` are the total support projections. This element satisfies
`matrixUnitIntertwiner 𝕜 e e = 1`,
`star (matrixUnitIntertwiner 𝕜 e f) = matrixUnitIntertwiner 𝕜 f e`,
and `f r i j * matrixUnitIntertwiner 𝕜 e f = matrixUnitIntertwiner 𝕜 e f * e r i j` for every
`r`, `i`, `j`.

## Main definitions

* `TauCeti.IsMatrixUnitSystem e`: `e : ∀ r : κ, n r → n r → R` satisfies the multi-block matrix-unit
  relations.
* `TauCeti.matrixUnitBlockSupport e r` and `TauCeti.matrixUnitSupport e`: the block and total
  support projections `∑ i, e r i i` and `∑ r, ∑ i, e r i i`.
* `TauCeti.IsUnitalMatrixUnitSystem e`: a finite system of matrix units whose total support is `1`.
* `TauCeti.matrixUnitIntertwiner 𝕜 e f`: the canonical intertwiner between two finite systems of
  matrix units of the same shape.

## Main statements

* `TauCeti.IsMatrixUnitSystem.of_partialIsometry`: constructing a system of matrix units from
  partial isometries with block-constant initial projections and pairwise-orthogonal final
  projections.
* `TauCeti.IsMatrixUnitSystem.isStarProjection_support`: the total support of a finite system of
  matrix units is a star projection.
* `TauCeti.IsMatrixUnitSystem.matrixUnitIntertwiner_self` and
  `TauCeti.IsMatrixUnitSystem.intertwine_matrixUnitIntertwiner`: normalization and intertwining
  properties of `TauCeti.matrixUnitIntertwiner`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  Encyclopaedia of Mathematical Sciences **122**, Springer (2006), II.8.3.23.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications **5**,
  Cambridge University Press (1998), §4.6.
-/

public section

open Function

namespace TauCeti

section MulZeroStar

variable {κ : Type*} {n : κ → Type*} {R S : Type*}

/-- A multi-block **system of matrix units** in a type `R` with multiplication, zero, and star:
`star (e r i j) = e r j i`, `e r i j * e r j l = e r i l`, `e r i j * e r k l = 0` for `j ≠ k`,
and `e r i j * e s k l = 0` for `r ≠ s`. -/
structure IsMatrixUnitSystem [Mul R] [Zero R] [Star R] (e : ∀ r : κ, n r → n r → R) : Prop where
  /-- Taking the star transposes indices within each block. -/
  star_eq (r : κ) (i j : n r) : star (e r i j) = e r j i
  /-- Composable entries within a block multiply by contracting the middle index. -/
  mul_same (r : κ) (i j l : n r) : e r i j * e r j l = e r i l
  /-- Non-composable entries within a block multiply to `0`. -/
  mul_ne (r : κ) (i : n r) {j k : n r} (l : n r) : j ≠ k → e r i j * e r k l = 0
  /-- Entries from distinct blocks multiply to `0`. -/
  mul_block_ne {r s : κ} : r ≠ s → ∀ (i j : n r) (k l : n s), e r i j * e s k l = 0

namespace IsMatrixUnitSystem

section Basic

variable [Mul R] [Zero R] [Star R] {e : ∀ r : κ, n r → n r → R}

/-- Kronecker-delta form of multiplication within a single block `r`. -/
theorem mul_eq_ite (he : IsMatrixUnitSystem e) (r : κ) [DecidableEq (n r)] (i j k l : n r) :
    e r i j * e r k l = if j = k then e r i l else 0 := by
  split_ifs with h
  · exact h ▸ he.mul_same r i j l
  · exact he.mul_ne r i l h

/-- Every diagonal entry `e r i i` is idempotent. -/
theorem isIdempotentElem_diag (he : IsMatrixUnitSystem e) (r : κ) (i : n r) :
    IsIdempotentElem (e r i i) :=
  he.mul_same r i i i

/-- Every diagonal entry `e r i i` is self-adjoint. -/
theorem isSelfAdjoint_diag (he : IsMatrixUnitSystem e) (r : κ) (i : n r) :
    IsSelfAdjoint (e r i i) :=
  he.star_eq r i i

/-- Every diagonal entry `e r i i` is a star projection. -/
theorem isStarProjection_diag (he : IsMatrixUnitSystem e) (r : κ) (i : n r) :
    IsStarProjection (e r i i) :=
  ⟨he.isIdempotentElem_diag r i, he.isSelfAdjoint_diag r i⟩

/-- The final projection `e r i j * star (e r i j)` of `e r i j` is `e r i i`. -/
theorem mul_star_self (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    e r i j * star (e r i j) = e r i i := by
  rw [he.star_eq, he.mul_same]

/-- The initial projection `star (e r i j) * e r i j` of `e r i j` is `e r j j`. -/
theorem star_mul_self (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    star (e r i j) * e r i j = e r j j := by
  rw [he.star_eq, he.mul_same]

/-- Every entry `e r i j` of a system of matrix units is a partial isometry. -/
theorem isPartialIsometry (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    IsPartialIsometry (e r i j) := by
  rw [isPartialIsometry_iff, he.mul_star_self, he.mul_same]

/-- Any star-preserving multiplicative zero-preserving map sends a system of matrix units to a
system of matrix units. -/
theorem map [Mul S] [Zero S] [Star S] {F : Type*} [FunLike F R S] [MulHomClass F R S]
    [ZeroHomClass F R S] [StarHomClass F R S] (he : IsMatrixUnitSystem e) (φ : F) :
    IsMatrixUnitSystem (fun r i j ↦ φ (e r i j)) where
  star_eq r i j := by rw [← map_star, he.star_eq]
  mul_same r i j l := by rw [← map_mul, he.mul_same]
  mul_ne r i {_ _} l h := by rw [← map_mul, he.mul_ne r i l h, map_zero]
  mul_block_ne hrs i j k l := by rw [← map_mul, he.mul_block_ne hrs i j k l, map_zero]

/-- Two diagonal entries `e r i i` and `e s k k` with `(r, i) ≠ (s, k)` multiply to `0`. -/
theorem diag_mul_diag_of_ne (he : IsMatrixUnitSystem e) {x y : Σ r, n r} (hxy : x ≠ y) :
    e x.1 x.2 x.2 * e y.1 y.2 y.2 = 0 := by
  rcases x with ⟨r, i⟩
  rcases y with ⟨s, k⟩
  by_cases hrs : r = s
  · subst hrs
    exact he.mul_ne r i k fun hik ↦ hxy (congrArg (Sigma.mk r) hik)
  · exact he.mul_block_ne hrs i i k k

end Basic

/-- The diagonal projections `(r, i) ↦ e r i i` of a system of matrix units are pairwise
star-orthogonal. -/
theorem pairwise_isStarOrtho_diag [NonUnitalSemiring R] [StarRing R]
    {e : ∀ r : κ, n r → n r → R} (he : IsMatrixUnitSystem e) :
    Pairwise (IsStarOrtho on fun x : Σ r, n r ↦ e x.1 x.2 x.2) := by
  intro x y hxy
  simp only [onFun, isStarOrtho_iff, (he.isSelfAdjoint_diag y.1 y.2).star_eq]
  exact ⟨he.diag_mul_diag_of_ne hxy, he.diag_mul_diag_of_ne hxy.symm⟩

/-- Construct a system of matrix units `e r i j = v r i * star (v r j)` from partial isometries
`v : ∀ r : κ, n r → R` whose initial projections `star (v r i) * v r i` depend only on the block
`r` and whose final projections `v r i * star (v r i)` are pairwise orthogonal across all blocks
and indices. -/
theorem of_partialIsometry [NonUnitalSemiring R] [StarRing R] {v : ∀ r : κ, n r → R}
    (hv : ∀ r i, IsPartialIsometry (v r i))
    (hinit : ∀ r i j, star (v r i) * v r i = star (v r j) * v r j)
    (hortho : Pairwise ((fun a b : R ↦ a * b = 0) on fun x : Σ r, n r ↦
      v x.1 x.2 * star (v x.1 x.2))) :
    IsMatrixUnitSystem (fun r i j ↦ v r i * star (v r j)) := by
  have hstar_mul : ∀ {x y : Σ r, n r}, x ≠ y → star (v x.1 x.2) * v y.1 y.2 = 0 := by
    intro x y hxy
    have hqx : star (v x.1 x.2) = star (v x.1 x.2) * (v x.1 x.2 * star (v x.1 x.2)) := by
      simpa [star_mul, star_star, mul_assoc] using
        congrArg star (hv x.1 x.2).mul_star_mul_self.symm
    rw [hqx, ← (hv y.1 y.2).mul_star_mul_self]
    calc star (v x.1 x.2) * (v x.1 x.2 * star (v x.1 x.2)) *
            (v y.1 y.2 * star (v y.1 y.2) * v y.1 y.2)
        = star (v x.1 x.2) *
            ((v x.1 x.2 * star (v x.1 x.2)) * (v y.1 y.2 * star (v y.1 y.2))) * v y.1 y.2 := by
          simp only [mul_assoc]
      _ = 0 := by rw [hortho hxy, mul_zero, zero_mul]
  refine
    { star_eq := fun r i j ↦ by simp [star_mul]
      mul_same := fun r i j l ↦ ?_
      mul_ne := fun r i {j k} l hjk ↦ ?_
      mul_block_ne := fun {r s} hrs i j k l ↦ ?_ }
  · calc (v r i * star (v r j)) * (v r j * star (v r l))
        = v r i * (star (v r j) * v r j) * star (v r l) := by simp only [mul_assoc]
      _ = (v r i * star (v r i) * v r i) * star (v r l) := by
          rw [hinit r j i]; simp only [mul_assoc]
      _ = v r i * star (v r l) := by rw [(hv r i).mul_star_mul_self]
  · have hne : (⟨r, j⟩ : Σ r, n r) ≠ ⟨r, k⟩ := fun h ↦ hjk (eq_of_heq (Sigma.mk.inj h).2)
    calc (v r i * star (v r j)) * (v r k * star (v r l))
        = v r i * (star (v r j) * v r k) * star (v r l) := by simp only [mul_assoc]
      _ = 0 := by rw [hstar_mul hne, mul_zero, zero_mul]
  · have hne : (⟨r, j⟩ : Σ r, n r) ≠ ⟨s, k⟩ := fun h ↦ hrs (congrArg Sigma.fst h)
    calc (v r i * star (v r j)) * (v s k * star (v s l))
        = v r i * (star (v r j) * v s k) * star (v s l) := by simp only [mul_assoc]
      _ = 0 := by rw [hstar_mul hne, mul_zero, zero_mul]

end IsMatrixUnitSystem

/-- A single `1 × 1` block with entry `p` is a system of matrix units if and only if `p` is a star
projection. -/
@[simp]
theorem isMatrixUnitSystem_single_iff [Mul R] [Zero R] [Star R] {p : R} :
    IsMatrixUnitSystem (fun _ : Unit ↦ fun _ _ : Unit ↦ p) ↔ IsStarProjection p := by
  refine ⟨fun h ↦ h.isStarProjection_diag () (), fun hp ↦ ?_⟩
  refine
    { star_eq := fun _ _ _ ↦ hp.isSelfAdjoint.star_eq
      mul_same := fun _ _ _ _ ↦ hp.isIdempotentElem.eq
      mul_ne := fun _ _ {_ _} _ h ↦ (h (Subsingleton.elim _ _)).elim
      mul_block_ne := fun h _ _ _ _ ↦ (h (Subsingleton.elim _ _)).elim }

end MulZeroStar

section Support

variable {κ : Type*} {n : κ → Type*} {R : Type*}

/-- The **block support projection** `∑ i : n r, e r i i` of block `r` in a family `e`. -/
def matrixUnitBlockSupport [AddCommMonoid R] [∀ r, Fintype (n r)]
    (e : ∀ r : κ, n r → n r → R) (r : κ) : R :=
  ∑ i : n r, e r i i

/-- The **total support projection** `∑ r : κ, ∑ i : n r, e r i i` of a finite family `e`. -/
def matrixUnitSupport [AddCommMonoid R] [Fintype κ] [∀ r, Fintype (n r)]
    (e : ∀ r : κ, n r → n r → R) : R :=
  ∑ r : κ, matrixUnitBlockSupport e r

/-- Unfold `TauCeti.matrixUnitBlockSupport`. -/
theorem matrixUnitBlockSupport_def [AddCommMonoid R] [∀ r, Fintype (n r)]
    (e : ∀ r : κ, n r → n r → R) (r : κ) :
    matrixUnitBlockSupport e r = ∑ i : n r, e r i i :=
  (rfl)

/-- Unfold `TauCeti.matrixUnitSupport`. -/
theorem matrixUnitSupport_def [AddCommMonoid R] [Fintype κ] [∀ r, Fintype (n r)]
    (e : ∀ r : κ, n r → n r → R) :
    matrixUnitSupport e = ∑ r : κ, ∑ i : n r, e r i i :=
  (rfl)

/-- A finite system of matrix units in a unital star ring is **unital** if its total support
projection equals `1`. -/
structure IsUnitalMatrixUnitSystem [Semiring R] [Star R] [Fintype κ] [∀ r, Fintype (n r)]
    (e : ∀ r : κ, n r → n r → R) : Prop extends IsMatrixUnitSystem e where
  /-- The diagonal projections sum to `1`. -/
  support_eq_one : matrixUnitSupport e = 1

namespace IsMatrixUnitSystem

section NonUnitalSemiring

variable [NonUnitalSemiring R] [StarRing R] [∀ r, Fintype (n r)]
  {e : ∀ r : κ, n r → n r → R}

/-- Each block support `matrixUnitBlockSupport e r` is a star projection. -/
theorem isStarProjection_blockSupport (he : IsMatrixUnitSystem e) (r : κ) :
    IsStarProjection (matrixUnitBlockSupport e r) := by
  refine IsStarProjection.sum (fun i _ ↦ he.isStarProjection_diag r i) ?_
  intro i _ j _ hij
  exact he.pairwise_isStarOrtho_diag (i := ⟨r, i⟩) (j := ⟨r, j⟩)
    (fun h ↦ hij (eq_of_heq (Sigma.mk.inj h).2))

/-- Right-multiplying `e r i j` by `matrixUnitBlockSupport e r` leaves `e r i j` fixed. -/
theorem mul_blockSupport_same (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    e r i j * matrixUnitBlockSupport e r = e r i j := by
  classical
  simp [matrixUnitBlockSupport_def, Finset.mul_sum, he.mul_eq_ite]

/-- Left-multiplying `e r i j` by `matrixUnitBlockSupport e r` leaves `e r i j` fixed. -/
theorem blockSupport_mul_same (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    matrixUnitBlockSupport e r * e r i j = e r i j := by
  classical
  simp [matrixUnitBlockSupport_def, Finset.sum_mul, he.mul_eq_ite]

/-- Right-multiplying `e r i j` by the support of a distinct block `s` gives `0`. -/
theorem mul_blockSupport_ne (he : IsMatrixUnitSystem e) {r s : κ} (hrs : r ≠ s) (i j : n r) :
    e r i j * matrixUnitBlockSupport e s = 0 := by
  simp [matrixUnitBlockSupport_def, Finset.mul_sum, he.mul_block_ne hrs]

/-- Left-multiplying `e s i j` by the support of a distinct block `r` gives `0`. -/
theorem blockSupport_mul_ne (he : IsMatrixUnitSystem e) {r s : κ} (hrs : r ≠ s) (i j : n s) :
    matrixUnitBlockSupport e r * e s i j = 0 := by
  simp [matrixUnitBlockSupport_def, Finset.sum_mul, he.mul_block_ne hrs]

/-- For a finite block index type `κ`, the total support `matrixUnitSupport e` is a star
projection. -/
theorem isStarProjection_support [Fintype κ] (he : IsMatrixUnitSystem e) :
    IsStarProjection (matrixUnitSupport e) := by
  have hsum : matrixUnitSupport e = ∑ x : Σ r, n r, e x.1 x.2 x.2 := by
    rw [matrixUnitSupport_def, Fintype.sum_sigma]
  rw [hsum]
  exact IsStarProjection.sum (fun x _ ↦ he.isStarProjection_diag x.1 x.2)
    (he.pairwise_isStarOrtho_diag.set_pairwise _)

/-- Right-multiplying `e r i j` by `matrixUnitSupport e` leaves `e r i j` fixed. -/
theorem mul_support [Fintype κ] (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    e r i j * matrixUnitSupport e = e r i j := by
  classical
  rw [matrixUnitSupport, Finset.mul_sum]
  rw [Finset.sum_eq_single r]
  · exact he.mul_blockSupport_same r i j
  · intro s _ hsr
    exact he.mul_blockSupport_ne hsr.symm i j
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

/-- Left-multiplying `e r i j` by `matrixUnitSupport e` leaves `e r i j` fixed. -/
theorem support_mul [Fintype κ] (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    matrixUnitSupport e * e r i j = e r i j := by
  classical
  rw [matrixUnitSupport, Finset.sum_mul]
  rw [Finset.sum_eq_single r]
  · exact he.blockSupport_mul_same r i j
  · intro s _ hsr
    exact he.blockSupport_mul_ne hsr i j
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

end NonUnitalSemiring

section Ring

variable [Ring R] [StarRing R] [Fintype κ] [∀ r, Fintype (n r)]
  {e : ∀ r : κ, n r → n r → R}

/-- Right-multiplying `e r i j` by `1 - matrixUnitSupport e` gives `0`. -/
theorem mul_one_sub_support (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    e r i j * (1 - matrixUnitSupport e) = 0 := by
  rw [mul_sub, mul_one, he.mul_support, sub_self]

/-- Left-multiplying `e r i j` by `1 - matrixUnitSupport e` gives `0`. -/
theorem one_sub_support_mul (he : IsMatrixUnitSystem e) (r : κ) (i j : n r) :
    (1 - matrixUnitSupport e) * e r i j = 0 := by
  rw [sub_mul, one_mul, he.support_mul, sub_self]

end Ring

end IsMatrixUnitSystem

end Support

section Intertwiner

variable (𝕜 : Type*) {κ : Type*} {n : κ → Type*} {R : Type*}
  [Field 𝕜] [Ring R] [Algebra 𝕜 R] [Fintype κ] [∀ r, Fintype (n r)]

/-- The **canonical multi-block intertwiner** between two finite families
`e, f : ∀ r : κ, n r → n r → R`, equal to
`(1 - matrixUnitSupport f) * (1 - matrixUnitSupport e)` plus
`∑ r, (card (n r) : 𝕜)⁻¹ • ∑ a, ∑ b, f r a b * e r b a`.
When `e` and `f` are systems of matrix units and `𝕜` has characteristic zero, this equals `1` for
`f = e` and intertwines `e` with `f`. -/
def matrixUnitIntertwiner (e f : ∀ r : κ, n r → n r → R) : R :=
  (1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) +
    ∑ r : κ, (Fintype.card (n r) : 𝕜)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a

/-- Unfold `TauCeti.matrixUnitIntertwiner`. -/
theorem matrixUnitIntertwiner_def (e f : ∀ r : κ, n r → n r → R) :
    matrixUnitIntertwiner 𝕜 e f =
      (1 - matrixUnitSupport f) * (1 - matrixUnitSupport e) +
        ∑ r : κ, (Fintype.card (n r) : 𝕜)⁻¹ • ∑ a : n r, ∑ b : n r, f r a b * e r b a :=
  (rfl)

namespace IsMatrixUnitSystem

variable {e f : ∀ r : κ, n r → n r → R}

/-- In characteristic zero, the canonical intertwiner of a system of matrix units with itself is
`1`. -/
theorem matrixUnitIntertwiner_self [StarRing R] [CharZero 𝕜] (he : IsMatrixUnitSystem e) :
    matrixUnitIntertwiner 𝕜 e e = 1 := by
  rw [matrixUnitIntertwiner_def, (he.isStarProjection_support.one_sub).isIdempotentElem.eq]
  have hsum :
      (∑ r : κ, (Fintype.card (n r) : 𝕜)⁻¹ • ∑ a : n r, ∑ b : n r, e r a b * e r b a) =
        matrixUnitSupport e := by
    rw [matrixUnitSupport]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    by_cases hcard : Fintype.card (n r) = 0
    · have : IsEmpty (n r) := Fintype.card_eq_zero_iff.mp hcard
      simp [matrixUnitBlockSupport_def]
    · have hcast : (Fintype.card (n r) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hcard
      have inner : (∑ a : n r, ∑ b : n r, e r a b * e r b a) =
          (Fintype.card (n r) : 𝕜) • matrixUnitBlockSupport e r := by
        simp_rw [he.mul_same, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜,
          ← Finset.smul_sum, matrixUnitBlockSupport_def]
      rw [inner, smul_smul, inv_mul_cancel₀ hcast, one_smul]
  rw [hsum, sub_add_cancel]

/-- Left-multiplying `matrixUnitIntertwiner 𝕜 e f` by `f r i j` extracts the single sum
`(card (n r) : 𝕜)⁻¹ • ∑ b, f r i b * e r b j`. -/
theorem mul_matrixUnitIntertwiner [StarRing R] (hf : IsMatrixUnitSystem f)
    (e : ∀ r : κ, n r → n r → R) (r : κ) (i j : n r) :
    f r i j * matrixUnitIntertwiner 𝕜 e f =
      (Fintype.card (n r) : 𝕜)⁻¹ • ∑ b : n r, f r i b * e r b j := by
  classical
  rw [matrixUnitIntertwiner_def, mul_add, ← mul_assoc, hf.mul_one_sub_support, zero_mul, zero_add,
    Finset.mul_sum]
  rw [Finset.sum_eq_single r]
  · rw [mul_smul_comm, Finset.mul_sum, Finset.sum_eq_single j]
    · rw [Finset.mul_sum]
      refine congrArg _ (Finset.sum_congr rfl fun b _ ↦ ?_)
      rw [← mul_assoc, hf.mul_same]
    · intro a _ haj
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun b _ ↦ by rw [← mul_assoc, hf.mul_ne r i b haj.symm, zero_mul]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro s _ hsr
    rw [mul_smul_comm, Finset.mul_sum]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ ↦ ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun b _ ↦ by
      rw [← mul_assoc, hf.mul_block_ne hsr.symm i j a b, zero_mul]
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

/-- Right-multiplying `matrixUnitIntertwiner 𝕜 e f` by `e r i j` extracts the single sum
`(card (n r) : 𝕜)⁻¹ • ∑ b, f r i b * e r b j`. -/
theorem matrixUnitIntertwiner_mul [StarRing R] (he : IsMatrixUnitSystem e)
    (f : ∀ r : κ, n r → n r → R) (r : κ) (i j : n r) :
    matrixUnitIntertwiner 𝕜 e f * e r i j =
      (Fintype.card (n r) : 𝕜)⁻¹ • ∑ b : n r, f r i b * e r b j := by
  classical
  rw [matrixUnitIntertwiner_def, add_mul, mul_assoc, he.one_sub_support_mul, mul_zero, zero_add,
    Finset.sum_mul]
  rw [Finset.sum_eq_single r]
  · rw [smul_mul_assoc, Finset.sum_mul, Finset.sum_eq_single i]
    · rw [Finset.sum_mul]
      refine congrArg _ (Finset.sum_congr rfl fun b _ ↦ ?_)
      rw [mul_assoc, he.mul_same]
    · intro a _ hai
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun b _ ↦ by rw [mul_assoc, he.mul_ne r b j hai, mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  · intro s _ hsr
    rw [smul_mul_assoc, Finset.sum_mul]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ ↦ ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun b _ ↦ by rw [mul_assoc, he.mul_block_ne hsr b a i j, mul_zero]
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

/-- **Intertwining identity** for `TauCeti.matrixUnitIntertwiner`:
`f r i j * matrixUnitIntertwiner 𝕜 e f = matrixUnitIntertwiner 𝕜 e f * e r i j`. -/
theorem intertwine_matrixUnitIntertwiner [StarRing R] (he : IsMatrixUnitSystem e)
    (hf : IsMatrixUnitSystem f) (r : κ) (i j : n r) :
    f r i j * matrixUnitIntertwiner 𝕜 e f = matrixUnitIntertwiner 𝕜 e f * e r i j := by
  rw [hf.mul_matrixUnitIntertwiner 𝕜, he.matrixUnitIntertwiner_mul 𝕜]

/-- Taking the star of `matrixUnitIntertwiner 𝕜 e f` swaps `e` and `f`. -/
theorem star_matrixUnitIntertwiner [StarRing R]
    (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f) :
    star (matrixUnitIntertwiner 𝕜 e f) = matrixUnitIntertwiner 𝕜 f e := by
  rw [matrixUnitIntertwiner_def, matrixUnitIntertwiner_def, star_add, star_mul,
    (he.isStarProjection_support.one_sub).isSelfAdjoint.star_eq,
    (hf.isStarProjection_support.one_sub).isSelfAdjoint.star_eq, star_sum]
  refine congrArg ((1 - matrixUnitSupport e) * (1 - matrixUnitSupport f) + ·)
    (Finset.sum_congr rfl fun r _ ↦ ?_)
  rw [star_inv_natCast_smul]
  refine congrArg ((Fintype.card (n r) : 𝕜)⁻¹ • ·) ?_
  rw [star_sum]
  simp_rw [star_sum, star_mul, he.star_eq, hf.star_eq]

/-- Adjoint intertwining identity:
`star (matrixUnitIntertwiner 𝕜 e f) * f r i j = e r i j * star (matrixUnitIntertwiner 𝕜 e f)`. -/
theorem star_matrixUnitIntertwiner_mul [StarRing R]
    (he : IsMatrixUnitSystem e) (hf : IsMatrixUnitSystem f) (r : κ) (i j : n r) :
    star (matrixUnitIntertwiner 𝕜 e f) * f r i j =
      e r i j * star (matrixUnitIntertwiner 𝕜 e f) := by
  rw [he.star_matrixUnitIntertwiner 𝕜 hf, (hf.intertwine_matrixUnitIntertwiner 𝕜 he r i j).symm]

end IsMatrixUnitSystem

end Intertwiner

end TauCeti
