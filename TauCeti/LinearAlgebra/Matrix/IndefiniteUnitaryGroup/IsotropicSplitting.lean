/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Isotropic splittings of a hermitian form, and the Levi and unipotent elements

Let `R` be a commutative ring with an involution and `A` a hermitian matrix on `n`, the Gram matrix
of the form `⟨y, z⟩ = yᴴ A z` on `R^n`. An **isotropic splitting** of `A` over a Gram matrix `A₀`
on `n₀` along `p` (`TauCeti.IsotropicSplitting A A₀ p`) is a Witt decomposition
`R^n = l R^p ⊕ ι R^{n₀} ⊕ k R^p` given by matrices `k, l : Matrix n p R` and `ι : Matrix n n₀ R`
with

```text
kᴴ A k = 0,   lᴴ A l = 0,   lᴴ A k = 1,   ιᴴ A ι = A₀,   ιᴴ A k = 0,   ιᴴ A l = 0,
```

`A₀` invertible and `|n| = |n₀| + 2 |p|`. The columns of `k` and of `l` span dual isotropic
subspaces and `ι` embeds the form `A₀` into their orthogonal complement. Every vector `y` is then
uniquely `y = l a + ι w + k b`, with coordinates `a = kᴴ A y`, `w = A₀⁻¹ ιᴴ A y` and `b = lᴴ A y`
(`TauCeti.IsotropicSplitting.lCoord`, `ιCoord`, `kCoord`).

The stabilizer of the isotropic subspace `k R^p` in the unitary group `Matrix.unitaryGroupOf A` is
the parabolic subgroup attached to the splitting. This file constructs its two kinds of elements.

* The **Levi element** `m(a, g₀)` (`TauCeti.IsotropicSplitting.levi`), for `a ∈ GL_p(R)` and
  `g₀` in the unitary group of `A₀`, acts by `a` on the frame `k`, by `g₀` on the core `ι` and by
  `(a⁻¹)ᴴ` on the frame `l`; `levi` is an injective group homomorphism.
* The **unipotent element** `n(c, b)` (`TauCeti.IsotropicSplitting.unipotent`), for
  `c : Matrix n₀ p R` and `b : Matrix p p R`, fixes `k`, sends `ι` to `ι + k cᴴ A₀` and `l` to
  `l - ι c - k ⅟2 (j⁻¹ (b + bᴴ) + cᴴ A₀ c)`. Here `j` is a fixed unit with `star j = -j` (for
  instance a purely imaginary element of a CM field) and `2` is invertible in `R`; only the
  hermitian part of `b` matters (`TauCeti.IsotropicSplitting.unipotent_eq_unipotent_iff`).

The main results are the laws of these elements:

* `TauCeti.IsotropicSplitting.unipotent_mul_unipotent`:
  `n(c, b) n(c', b') = n(c + c', b + j cᴴ A₀ c' + b')`;
* `TauCeti.IsotropicSplitting.levi_mul_unipotent_mul_inv_levi`:
  `m(a, g₀) n(c, b) m(a, g₀)⁻¹ = n(g₀ c aᴴ, a b aᴴ)`;
* the **Levi decomposition** `TauCeti.IsotropicSplitting.exists_eq_unipotent_mul_levi`: an element
  `g` of the unitary group with `g k = k a` is `n(c, b) m(a, g₀)`, where `g₀ = A₀⁻¹ ιᴴ A g ι` is its
  block on the core;
* `TauCeti.IsotropicSplitting.exists_eq_unipotent_iff`: the unipotent elements are exactly the
  elements fixing `k` pointwise with core block `1`, the unipotent radical of the parabolic.

The parabolic subgroup itself is `TauCeti.IsotropicSplitting.parabolic`, the elements `g` with
`g k = k a` for some `a ∈ GL_p(R)`; its elements are exactly the products `n(c, b) m(a, g₀)`
(`TauCeti.IsotropicSplitting.mem_parabolic_iff_exists_unipotent_mul_levi`). Exchanging the frames
`k` and `l` gives the splitting `TauCeti.IsotropicSplitting.swap`, whose parabolic subgroup is the
opposite parabolic. The **shear** `TauCeti.IsotropicSplitting.shear` by a skew-hermitian
`X : Matrix p p R` is the element `1 + k X lCoord`; it fixes `k` and `ι`, sends `l` to `l + k X`,
and needs no inverse of `2`. The shears form a group, lie in the parabolic subgroup, and are the
unipotent elements `n(0, -j X)` when `2` is invertible
(`TauCeti.IsotropicSplitting.shear_eq_unipotent`).

The Siegel parabolic of a doubled space, the case of a frame without core in polarization
coordinates, is treated in module form in
`TauCeti.LinearAlgebra.SesquilinearForm.Doubling.SiegelParabolic`, and the stabilizer of an
isotropic subspace of a symplectic form in a fixed basis in `TauCeti.IsotropicParabolic`.

These are the algebraic laws of the parabolic subgroups of unitary groups used in the mixed models
of the Weil representation along a Witt decomposition. They are stated over any commutative ring
with involution (in which `2` is invertible, for the unipotent elements), so the same statements
apply to a hermitian space over a CM field and, in standard coordinates given by an adelic frame,
to its adelic points.

## Provenance

The definitions of the splitting, of its coordinates and of the Levi and unipotent elements, the
group law and the Levi decomposition follow `New.Space.Splitting`,
`New.Space.Splitting.levi`, `New.Space.Splitting.radicalElement`,
`New.Space.Splitting.radicalElement_mul`, `New.Space.Splitting.levi_conj_radicalElement`,
`New.Space.Splitting.exists_eq_radicalElement_mul_levi` and
`New.Space.Splitting.exists_eq_radicalElement_iff` (file
`grh/src/Lib/Weil/MixedModel/IsotropicSplitting.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where they are
stated for adelic frames over a CM field with Weil data. Here they are stated for an arbitrary
hermitian Gram matrix over a commutative ring with involution.

## References

* M.-A. Knus, *Quadratic and Hermitian forms over rings* (1991), the Witt decomposition of a
  hermitian space.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R] [StarRing R]
  {n n₀ p : Type*} [Fintype n] [Fintype n₀] [Fintype p] [DecidableEq n₀] [DecidableEq p]

/-- An **isotropic splitting** of the hermitian Gram matrix `A` on `n` over the invertible Gram
matrix `A₀` on `n₀`, along `p`: frames `k, l : Matrix n p R` spanning dual isotropic subspaces
(`kᴴ A k = 0`, `lᴴ A l = 0`, `lᴴ A k = 1`) and a matrix `ι : Matrix n n₀ R` embedding `A₀`
(`ιᴴ A ι = A₀`) orthogonally to both, with `|n| = |n₀| + 2 |p|`, so that
`R^n = l R^p ⊕ ι R^{n₀} ⊕ k R^p`. -/
structure IsotropicSplitting (A : Matrix n n R) (A₀ : Matrix n₀ n₀ R) (p : Type*) [Fintype p]
    [DecidableEq p] where
  /-- The isotropic frame `k`. -/
  k : Matrix n p R
  /-- The isotropic frame `l`, dual to `k`. -/
  l : Matrix n p R
  /-- The embedding of the core `A₀`. -/
  ι : Matrix n n₀ R
  /-- The ambient Gram matrix is hermitian. -/
  isHermitian : A.IsHermitian
  /-- The Gram matrix of the core is invertible. -/
  isUnit_core : IsUnit A₀
  /-- `k` is isotropic. -/
  gram_kk : kᴴ * A * k = 0
  /-- `l` is isotropic. -/
  gram_ll : lᴴ * A * l = 0
  /-- `l` and `k` are dual. -/
  gram_lk : lᴴ * A * k = 1
  /-- `ι` embeds the form `A₀`. -/
  gram_ιι : ιᴴ * A * ι = A₀
  /-- The core is orthogonal to `k`. -/
  gram_ιk : ιᴴ * A * k = 0
  /-- The core is orthogonal to `l`. -/
  gram_ιl : ιᴴ * A * l = 0
  /-- The rank of the ambient space is the rank of the core plus twice the size of the frames. -/
  card_eq : Fintype.card n = Fintype.card n₀ + 2 * Fintype.card p

namespace IsotropicSplitting

variable {A : Matrix n n R} {A₀ : Matrix n₀ n₀ R} (D : IsotropicSplitting A A₀ p)

/-! ### The remaining relations and the coordinates -/

/-- `k` and `l` are dual. -/
theorem gram_kl : D.kᴴ * A * D.l = 1 := by
  rw [← conjTranspose_one, ← D.gram_lk]
  simp [Matrix.mul_assoc, D.isHermitian.eq]

/-- `k` is orthogonal to the core. -/
theorem gram_kι : D.kᴴ * A * D.ι = 0 := by
  rw [← conjTranspose_zero, ← D.gram_ιk]
  simp [Matrix.mul_assoc, D.isHermitian.eq]

/-- `l` is orthogonal to the core. -/
theorem gram_lι : D.lᴴ * A * D.ι = 0 := by
  rw [← conjTranspose_zero, ← D.gram_ιl]
  simp [Matrix.mul_assoc, D.isHermitian.eq]

include D in
/-- The Gram matrix of the core is hermitian. -/
theorem isHermitian_core : A₀.IsHermitian := by
  rw [IsHermitian, ← D.gram_ιι]
  simp [Matrix.mul_assoc, D.isHermitian.eq]

/-- The coordinate along `k`, `kCoord = lᴴ A`: it sends `l a + ι w + k b` to `b`. -/
def kCoord : Matrix p n R := D.lᴴ * A

/-- The coordinate along `l`, `lCoord = kᴴ A`: it sends `l a + ι w + k b` to `a`. -/
def lCoord : Matrix p n R := D.kᴴ * A

/-- The coordinate along the core, `ιCoord = A₀⁻¹ ιᴴ A`: it sends `l a + ι w + k b` to `w`. -/
def ιCoord : Matrix n₀ n R := A₀⁻¹ * D.ιᴴ * A

theorem kCoord_def : D.kCoord = D.lᴴ * A := (rfl)

theorem lCoord_def : D.lCoord = D.kᴴ * A := (rfl)

theorem ιCoord_def : D.ιCoord = A₀⁻¹ * D.ιᴴ * A := (rfl)

@[simp]
theorem conjTranspose_l_mul : D.lᴴ * A = D.kCoord := (rfl)

@[simp]
theorem conjTranspose_k_mul : D.kᴴ * A = D.lCoord := (rfl)

@[simp]
theorem conjTranspose_l_mul_mul {m : Type*} (X : Matrix n m R) :
    D.lᴴ * (A * X) = D.kCoord * X := by
  rw [← Matrix.mul_assoc, conjTranspose_l_mul]

@[simp]
theorem conjTranspose_k_mul_mul {m : Type*} (X : Matrix n m R) :
    D.kᴴ * (A * X) = D.lCoord * X := by
  rw [← Matrix.mul_assoc, conjTranspose_k_mul]

/-- `ιᴴ A = A₀ ιCoord`. -/
@[simp]
theorem conjTranspose_ι_mul : D.ιᴴ * A = A₀ * D.ιCoord := by
  rw [ιCoord_def, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det A₀).mp D.isUnit_core), Matrix.one_mul]

@[simp]
theorem conjTranspose_ι_mul_mul {m : Type*} (X : Matrix n m R) :
    D.ιᴴ * (A * X) = A₀ * (D.ιCoord * X) := by
  rw [← Matrix.mul_assoc, conjTranspose_ι_mul, Matrix.mul_assoc]

/-! The coordinates are dual to the frames. -/

@[simp] theorem kCoord_mul_k : D.kCoord * D.k = 1 := D.gram_lk

@[simp] theorem kCoord_mul_l : D.kCoord * D.l = 0 := D.gram_ll

@[simp] theorem kCoord_mul_ι : D.kCoord * D.ι = 0 := D.gram_lι

@[simp] theorem lCoord_mul_k : D.lCoord * D.k = 0 := D.gram_kk

@[simp] theorem lCoord_mul_l : D.lCoord * D.l = 1 := D.gram_kl

@[simp] theorem lCoord_mul_ι : D.lCoord * D.ι = 0 := D.gram_kι

/-- The coordinate along the core of a matrix `X` is `A₀⁻¹` times its pairing `ιᴴ A X` with the
core. -/
theorem ιCoord_mul {m : Type*} (X : Matrix n m R) : D.ιCoord * X = A₀⁻¹ * (D.ιᴴ * A * X) := by
  simp only [ιCoord_def, Matrix.mul_assoc]

@[simp]
theorem ιCoord_mul_k : D.ιCoord * D.k = 0 := by
  rw [ιCoord_mul, D.gram_ιk, Matrix.mul_zero]

@[simp]
theorem ιCoord_mul_l : D.ιCoord * D.l = 0 := by
  rw [ιCoord_mul, D.gram_ιl, Matrix.mul_zero]

@[simp]
theorem ιCoord_mul_ι : D.ιCoord * D.ι = 1 := by
  rw [ιCoord_mul, D.gram_ιι, nonsing_inv_mul _ ((isUnit_iff_isUnit_det A₀).mp D.isUnit_core)]

@[simp] theorem kCoord_mul_k_mul {m : Type*} (X : Matrix p m R) : D.kCoord * (D.k * X) = X := by
  rw [← Matrix.mul_assoc, kCoord_mul_k, Matrix.one_mul]

@[simp] theorem kCoord_mul_l_mul {m : Type*} (X : Matrix p m R) : D.kCoord * (D.l * X) = 0 := by
  rw [← Matrix.mul_assoc, kCoord_mul_l, Matrix.zero_mul]

@[simp] theorem kCoord_mul_ι_mul {m : Type*} (X : Matrix n₀ m R) :
    D.kCoord * (D.ι * X) = 0 := by
  rw [← Matrix.mul_assoc, kCoord_mul_ι, Matrix.zero_mul]

@[simp] theorem lCoord_mul_k_mul {m : Type*} (X : Matrix p m R) : D.lCoord * (D.k * X) = 0 := by
  rw [← Matrix.mul_assoc, lCoord_mul_k, Matrix.zero_mul]

@[simp] theorem lCoord_mul_l_mul {m : Type*} (X : Matrix p m R) : D.lCoord * (D.l * X) = X := by
  rw [← Matrix.mul_assoc, lCoord_mul_l, Matrix.one_mul]

@[simp] theorem lCoord_mul_ι_mul {m : Type*} (X : Matrix n₀ m R) :
    D.lCoord * (D.ι * X) = 0 := by
  rw [← Matrix.mul_assoc, lCoord_mul_ι, Matrix.zero_mul]

@[simp] theorem ιCoord_mul_k_mul {m : Type*} (X : Matrix p m R) : D.ιCoord * (D.k * X) = 0 := by
  rw [← Matrix.mul_assoc, ιCoord_mul_k, Matrix.zero_mul]

@[simp] theorem ιCoord_mul_l_mul {m : Type*} (X : Matrix p m R) : D.ιCoord * (D.l * X) = 0 := by
  rw [← Matrix.mul_assoc, ιCoord_mul_l, Matrix.zero_mul]

@[simp] theorem ιCoord_mul_ι_mul {m : Type*} (X : Matrix n₀ m R) :
    D.ιCoord * (D.ι * X) = X := by
  rw [← Matrix.mul_assoc, ιCoord_mul_ι, Matrix.one_mul]

/-! ### Exchanging the frames -/

/-- The splitting obtained by **exchanging the frames** `k` and `l`, with the same core
embedding `ι`. Its parabolic subgroup (`TauCeti.IsotropicSplitting.parabolic`) stabilizes the
span of `l`: it is the parabolic subgroup opposite to that of the original splitting. -/
def swap : IsotropicSplitting A A₀ p where
  k := D.l
  l := D.k
  ι := D.ι
  isHermitian := D.isHermitian
  isUnit_core := D.isUnit_core
  gram_kk := D.gram_ll
  gram_ll := D.gram_kk
  gram_lk := D.gram_kl
  gram_ιι := D.gram_ιι
  gram_ιk := D.gram_ιl
  gram_ιl := D.gram_ιk
  card_eq := D.card_eq

@[simp] theorem swap_k : D.swap.k = D.l := (rfl)

@[simp] theorem swap_l : D.swap.l = D.k := (rfl)

@[simp] theorem swap_ι : D.swap.ι = D.ι := (rfl)

@[simp] theorem swap_kCoord : D.swap.kCoord = D.lCoord := (rfl)

@[simp] theorem swap_lCoord : D.swap.lCoord = D.kCoord := (rfl)

@[simp] theorem swap_ιCoord : D.swap.ιCoord = D.ιCoord := (rfl)

@[simp] theorem swap_swap : D.swap.swap = D := (rfl)

variable [DecidableEq n]

/-- **The frames span**: `k kCoord + ι ιCoord + l lCoord = 1`, that is every vector is
`y = l a + ι w + k b` with `a = lCoord y`, `w = ιCoord y`, `b = kCoord y`. -/
theorem k_mul_kCoord_add_ι_mul_ιCoord_add_l_mul_lCoord :
    D.k * D.kCoord + D.ι * D.ιCoord + D.l * D.lCoord = 1 := by
  -- The coordinates, stacked as rows, are a left inverse of the frames, stacked as columns; both
  -- are square by `card_eq`, so they are also a right inverse.
  have h_card : Fintype.card ((p ⊕ n₀) ⊕ p) = Fintype.card n := by
    simp only [Fintype.card_sum, D.card_eq]
    ring
  have h :
      fromRows (fromRows D.kCoord D.ιCoord) D.lCoord * fromCols (fromCols D.k D.ι) D.l = 1 := by
    rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
    simp
  rwa [mul_eq_one_comm_of_card_eq _ _ _ h_card, fromCols_mul_fromRows, fromCols_mul_fromRows] at h

omit [DecidableEq n] in
/-- Every matrix `M` with `n` rows is `k (kCoord M) + ι (ιCoord M) + l (lCoord M)`. -/
theorem k_mul_kCoord_mul_add_ι_mul_ιCoord_mul_add_l_mul_lCoord_mul {m : Type*}
    (M : Matrix n m R) :
    D.k * (D.kCoord * M) + D.ι * (D.ιCoord * M) + D.l * (D.lCoord * M) = M := by
  classical
  simp only [← Matrix.mul_assoc, ← Matrix.add_mul, k_mul_kCoord_add_ι_mul_ιCoord_add_l_mul_lCoord,
    Matrix.one_mul]

/-- **The frames span when the core is trivial**: for an empty `n₀`, `k kCoord + l lCoord = 1`,
that is every vector is `y = l a + k b` with `a = lCoord y` and `b = kCoord y`. -/
theorem k_mul_kCoord_add_l_mul_lCoord [IsEmpty n₀] : D.k * D.kCoord + D.l * D.lCoord = 1 := by
  -- A product through the empty index type `n₀` vanishes.
  have h : D.ι * D.ιCoord = 0 := by
    ext
    simp [Matrix.mul_apply]
  simpa [h] using D.k_mul_kCoord_add_ι_mul_ιCoord_add_l_mul_lCoord

omit [DecidableEq n] in
/-- For an empty `n₀`, every matrix `M` with `n` rows is `k (kCoord M) + l (lCoord M)`. -/
theorem k_mul_kCoord_mul_add_l_mul_lCoord_mul [IsEmpty n₀] {m : Type*} (M : Matrix n m R) :
    D.k * (D.kCoord * M) + D.l * (D.lCoord * M) = M := by
  classical
  simp only [← Matrix.mul_assoc, ← Matrix.add_mul, k_mul_kCoord_add_l_mul_lCoord, Matrix.one_mul]

include D in
/-- The ambient Gram matrix of a splitting is invertible. -/
theorem isUnit : IsUnit A := by
  refine IsUnit.of_mul_eq_one_right (D.k * D.lᴴ + D.ι * (A₀⁻¹ * D.ιᴴ) + D.l * D.kᴴ) ?_
  rw [← D.k_mul_kCoord_add_ι_mul_ιCoord_add_l_mul_lCoord]
  simp only [Matrix.add_mul, Matrix.mul_assoc, kCoord_def, ιCoord_def, lCoord_def]

omit [DecidableEq n] in
/-- Two matrices are equal when they agree on the frames `k`, `ι` and `l`. -/
theorem ext_mul {m : Type*} {M N : Matrix m n R} (hk : M * D.k = N * D.k)
    (hι : M * D.ι = N * D.ι) (hl : M * D.l = N * D.l) : M = N := by
  classical
  rw [← M.mul_one, ← N.mul_one, ← D.k_mul_kCoord_add_ι_mul_ιCoord_add_l_mul_lCoord]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, hk, hι, hl]

omit [DecidableEq n] in
/-- Two matrices are equal when they agree after multiplication on the left by `kᴴ`, `ιᴴ` and
`lᴴ`. -/
theorem ext_conjTranspose_mul {m : Type*} {M N : Matrix n m R} (hk : D.kᴴ * M = D.kᴴ * N)
    (hι : D.ιᴴ * M = D.ιᴴ * N) (hl : D.lᴴ * M = D.lᴴ * N) : M = N := by
  rw [← conjTranspose_conjTranspose M, ← conjTranspose_conjTranspose N]
  congr 1
  refine D.ext_mul ?_ ?_ ?_
  · simpa using congrArg conjTranspose hk
  · simpa using congrArg conjTranspose hι
  · simpa using congrArg conjTranspose hl

omit [DecidableEq n] in
/-- A matrix `X` preserves the form `A` as soon as the images `X k`, `X ι`, `X l` of the frames
satisfy the relations of a splitting. -/
theorem conjTranspose_mul_mul_eq_of_frames {X : Matrix n n R}
    (hkk : (X * D.k)ᴴ * A * (X * D.k) = 0) (hll : (X * D.l)ᴴ * A * (X * D.l) = 0)
    (hlk : (X * D.l)ᴴ * A * (X * D.k) = 1) (hιι : (X * D.ι)ᴴ * A * (X * D.ι) = A₀)
    (hιk : (X * D.ι)ᴴ * A * (X * D.k) = 0) (hιl : (X * D.ι)ᴴ * A * (X * D.l) = 0) :
    Xᴴ * A * X = A := by
  classical
  -- The relations with the frames in the other order follow by conjugate transposition.
  have hkl : (X * D.k)ᴴ * A * (X * D.l) = 1 := by
    simpa [Matrix.mul_assoc, D.isHermitian.eq] using congrArg conjTranspose hlk
  have hkι : (X * D.k)ᴴ * A * (X * D.ι) = 0 := by
    simpa [Matrix.mul_assoc, D.isHermitian.eq] using congrArg conjTranspose hιk
  have hlι : (X * D.l)ᴴ * A * (X * D.ι) = 0 := by
    simpa [Matrix.mul_assoc, D.isHermitian.eq] using congrArg conjTranspose hιl
  simp only [conjTranspose_mul, Matrix.mul_assoc] at hkk hll hlk hιι hιk hιl hkl hkι hlι
  -- Test both sides on the frames, on the right and (after conjugate transposition) on the left.
  refine D.ext_mul ?_ ?_ ?_ <;> refine D.ext_conjTranspose_mul ?_ ?_ ?_ <;>
    simp only [Matrix.mul_assoc, hkk, hll, hlk, hιι, hιk, hιl, hkl, hkι, hlι] <;> simp

/-! ### Levi elements -/

/-- The matrix of the Levi element of `(a, g₀)`: `k a kCoord + ι g₀ ιCoord + l (a⁻¹)ᴴ lCoord`. -/
private def leviMatrix (a : GL p R) (g₀ : Matrix n₀ n₀ R) : Matrix n n R :=
  D.k * (a : Matrix p p R) * D.kCoord + D.ι * g₀ * D.ιCoord +
    D.l * (a : Matrix p p R)⁻¹ᴴ * D.lCoord

omit [DecidableEq n] in
private theorem leviMatrix_mul_k (a : GL p R) (g₀ : Matrix n₀ n₀ R) :
    D.leviMatrix a g₀ * D.k = D.k * (a : Matrix p p R) := by
  simp [leviMatrix, Matrix.add_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
private theorem leviMatrix_mul_ι (a : GL p R) (g₀ : Matrix n₀ n₀ R) :
    D.leviMatrix a g₀ * D.ι = D.ι * g₀ := by
  simp [leviMatrix, Matrix.add_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
private theorem leviMatrix_mul_l (a : GL p R) (g₀ : Matrix n₀ n₀ R) :
    D.leviMatrix a g₀ * D.l = D.l * (a : Matrix p p R)⁻¹ᴴ := by
  simp [leviMatrix, Matrix.add_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
private theorem leviMatrix_mem (a : GL p R) (g₀ : unitaryGroupOf A₀) :
    star (D.leviMatrix a (g₀ : GL n₀ R)) * A * D.leviMatrix a (g₀ : GL n₀ R) = A := by
  rw [star_eq_conjTranspose]
  refine D.conjTranspose_mul_mul_eq_of_frames ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [leviMatrix_mul_k, leviMatrix_mul_ι, leviMatrix_mul_l, Matrix.mul_assoc,
      unitaryGroupOf.conjTranspose_mul_mul_cancel]

/-- The **Levi homomorphism** `m : GL_p(R) × U(A₀) →* U(A)` of a splitting: `m(a, g₀)` acts by `a`
on the frame `k`, by `g₀` on the core `ι` and by `(a⁻¹)ᴴ` on the frame `l`. -/
def levi : GL p R × unitaryGroupOf A₀ →* unitaryGroupOf A :=
  MonoidHom.mk' (fun x ↦ unitaryGroupOf.ofMatrix D.isUnit (D.leviMatrix x.1 (x.2 : GL n₀ R))
    (D.leviMatrix_mem x.1 x.2)) fun x y ↦ by
    refine unitaryGroupOf.ext (D.ext_mul ?_ ?_ ?_) <;>
      simp only [Subgroup.coe_mul, Units.val_mul, Prod.fst_mul, Prod.snd_mul,
        unitaryGroupOf.val_ofMatrix, Matrix.mul_assoc, leviMatrix_mul_k, leviMatrix_mul_ι,
        leviMatrix_mul_l, Matrix.mul_inv_rev, conjTranspose_mul] <;>
      simp only [← Matrix.mul_assoc, leviMatrix_mul_k, leviMatrix_mul_ι, leviMatrix_mul_l]

private theorem val_levi_eq_leviMatrix (x : GL p R × unitaryGroupOf A₀) :
    ((D.levi x : GL n R) : Matrix n n R) = D.leviMatrix x.1 (x.2 : GL n₀ R) :=
  unitaryGroupOf.val_ofMatrix _ _ _

/-- The matrix of the Levi element of `(a, g₀)` is `k a kCoord + ι g₀ ιCoord + l (a⁻¹)ᴴ lCoord`. -/
theorem val_levi (x : GL p R × unitaryGroupOf A₀) :
    ((D.levi x : GL n R) : Matrix n n R) =
      D.k * (x.1 : Matrix p p R) * D.kCoord + D.ι * ((x.2 : GL n₀ R) : Matrix n₀ n₀ R) * D.ιCoord +
        D.l * (x.1 : Matrix p p R)⁻¹ᴴ * D.lCoord := by
  rw [val_levi_eq_leviMatrix, leviMatrix]

/-- The Levi element of `(a, g₀)` acts on the frame `k` by `a`. -/
@[simp]
theorem levi_mul_k (x : GL p R × unitaryGroupOf A₀) :
    ((D.levi x : GL n R) : Matrix n n R) * D.k = D.k * (x.1 : Matrix p p R) :=
  D.val_levi_eq_leviMatrix x ▸ D.leviMatrix_mul_k x.1 _

/-- The Levi element of `(a, g₀)` acts on the core by `g₀`. -/
@[simp]
theorem levi_mul_ι (x : GL p R × unitaryGroupOf A₀) :
    ((D.levi x : GL n R) : Matrix n n R) * D.ι = D.ι * ((x.2 : GL n₀ R) : Matrix n₀ n₀ R) :=
  D.val_levi_eq_leviMatrix x ▸ D.leviMatrix_mul_ι x.1 _

/-- The Levi element of `(a, g₀)` acts on the frame `l` by `(a⁻¹)ᴴ`. -/
@[simp]
theorem levi_mul_l (x : GL p R × unitaryGroupOf A₀) :
    ((D.levi x : GL n R) : Matrix n n R) * D.l = D.l * (x.1 : Matrix p p R)⁻¹ᴴ :=
  D.val_levi_eq_leviMatrix x ▸ D.leviMatrix_mul_l x.1 _

/-- The Levi homomorphism is injective. -/
theorem levi_injective : Function.Injective D.levi := by
  intro x y h
  have h' := congrArg (fun g : unitaryGroupOf A ↦ ((g : GL n R) : Matrix n n R)) h
  have hk := congrArg (fun M ↦ D.kCoord * (M * D.k)) h'
  have hι := congrArg (fun M ↦ D.ιCoord * (M * D.ι)) h'
  simp only [levi_mul_k, levi_mul_ι, kCoord_mul_k_mul, ιCoord_mul_ι_mul] at hk hι
  exact Prod.ext (Units.ext hk) (unitaryGroupOf.ext hι)

/-! ### Shears along the frame `k` -/

/-- The matrix `1 + k X lCoord` of the shear along `k` by `X`. -/
private def shearMatrix (X : Matrix p p R) : Matrix n n R := 1 + D.k * X * D.lCoord

private theorem shearMatrix_mul_k (X : Matrix p p R) : D.shearMatrix X * D.k = D.k := by
  simp [shearMatrix, Matrix.add_mul, Matrix.mul_assoc]

private theorem shearMatrix_mul_ι (X : Matrix p p R) : D.shearMatrix X * D.ι = D.ι := by
  simp [shearMatrix, Matrix.add_mul, Matrix.mul_assoc]

private theorem shearMatrix_mul_l (X : Matrix p p R) :
    D.shearMatrix X * D.l = D.l + D.k * X := by
  simp [shearMatrix, Matrix.add_mul, Matrix.mul_assoc]

private theorem shearMatrix_mem {X : Matrix p p R} (hX : Xᴴ = -X) :
    star (D.shearMatrix X) * A * D.shearMatrix X = A := by
  rw [star_eq_conjTranspose]
  refine D.conjTranspose_mul_mul_eq_of_frames ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [shearMatrix_mul_k, shearMatrix_mul_ι, shearMatrix_mul_l, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc, hX]

/-- The **shear** along the frame `k` by a skew-hermitian `X` (`Xᴴ = -X`): the element
`1 + k X lCoord` of the unitary group of `A`. It fixes the frame `k` and the core `ι` and sends the
frame `l` to `l + k X`. Unlike the unipotent elements `n(c, b)`, it needs no inverse of `2`; when
`2` is invertible it is `n(0, -j X)` (`TauCeti.IsotropicSplitting.shear_eq_unipotent`). -/
def shear (X : Matrix p p R) (hX : Xᴴ = -X) : unitaryGroupOf A :=
  unitaryGroupOf.ofMatrix D.isUnit (D.shearMatrix X) (D.shearMatrix_mem hX)

private theorem val_shear_eq_shearMatrix (X : Matrix p p R) (hX : Xᴴ = -X) :
    ((D.shear X hX : GL n R) : Matrix n n R) = D.shearMatrix X :=
  unitaryGroupOf.val_ofMatrix _ _ _

/-- The matrix of the shear by `X` is `1 + k X lCoord`. -/
theorem val_shear (X : Matrix p p R) (hX : Xᴴ = -X) :
    ((D.shear X hX : GL n R) : Matrix n n R) = 1 + D.k * X * D.lCoord := by
  rw [val_shear_eq_shearMatrix, shearMatrix]

/-- The shear by `X` fixes the frame `k`. -/
@[simp]
theorem shear_mul_k (X : Matrix p p R) (hX : Xᴴ = -X) :
    ((D.shear X hX : GL n R) : Matrix n n R) * D.k = D.k := by
  rw [val_shear_eq_shearMatrix, shearMatrix_mul_k]

/-- The shear by `X` fixes the core `ι`. -/
@[simp]
theorem shear_mul_ι (X : Matrix p p R) (hX : Xᴴ = -X) :
    ((D.shear X hX : GL n R) : Matrix n n R) * D.ι = D.ι := by
  rw [val_shear_eq_shearMatrix, shearMatrix_mul_ι]

/-- The shear by `X` sends the frame `l` to `l + k X`. -/
@[simp]
theorem shear_mul_l (X : Matrix p p R) (hX : Xᴴ = -X) :
    ((D.shear X hX : GL n R) : Matrix n n R) * D.l = D.l + D.k * X := by
  rw [val_shear_eq_shearMatrix, shearMatrix_mul_l]

/-- The shear by `X` changes the coordinate along `k` by `X` times the coordinate along `l`. -/
@[simp]
theorem kCoord_mul_shear (X : Matrix p p R) (hX : Xᴴ = -X) :
    D.kCoord * ((D.shear X hX : GL n R) : Matrix n n R) = D.kCoord + X * D.lCoord := by
  simp [val_shear, Matrix.mul_add, Matrix.mul_assoc]

/-- The shear by `X` preserves the coordinate along `l`. -/
@[simp]
theorem lCoord_mul_shear (X : Matrix p p R) (hX : Xᴴ = -X) :
    D.lCoord * ((D.shear X hX : GL n R) : Matrix n n R) = D.lCoord := by
  simp [val_shear, Matrix.mul_add, Matrix.mul_assoc]

/-- The shear by `X` preserves the coordinate along the core. -/
@[simp]
theorem ιCoord_mul_shear (X : Matrix p p R) (hX : Xᴴ = -X) :
    D.ιCoord * ((D.shear X hX : GL n R) : Matrix n n R) = D.ιCoord := by
  simp [val_shear, Matrix.mul_add, Matrix.mul_assoc]

/-- The shear by `0` is the identity. -/
@[simp]
theorem shear_zero (h : (0 : Matrix p p R)ᴴ = -0) : D.shear 0 h = 1 :=
  unitaryGroupOf.ext (by simp [val_shear])

/-- **The shears form a group**: the shear by `X` followed by the shear by `Y` is the shear by
`X + Y`. -/
theorem shear_mul_shear {X Y : Matrix p p R} (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    D.shear X hX * D.shear Y hY =
      D.shear (X + Y) (by rw [conjTranspose_add, hX, hY, neg_add]) := by
  -- `(1 + k X lCoord) (1 + k Y lCoord) = 1 + k (X + Y) lCoord`, as `lCoord k = 0`.
  refine unitaryGroupOf.ext ?_
  simp only [Subgroup.coe_mul, Units.val_mul, val_shear]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, add_assoc]

/-! The shears of the swapped splitting are the shears along the frame `l`. -/

/-- A shear along the frame `l` (a shear of the swapped splitting) fixes `l`. -/
@[simp]
theorem swap_shear_mul_l (Y : Matrix p p R) (hY : Yᴴ = -Y) :
    ((D.swap.shear Y hY : GL n R) : Matrix n n R) * D.l = D.l := by
  simpa using D.swap.shear_mul_k Y hY

/-- A shear along the frame `l` by `Y` sends `k` to `k + l Y`. -/
@[simp]
theorem swap_shear_mul_k (Y : Matrix p p R) (hY : Yᴴ = -Y) :
    ((D.swap.shear Y hY : GL n R) : Matrix n n R) * D.k = D.k + D.l * Y := by
  simpa using D.swap.shear_mul_l Y hY

/-- A shear along the frame `l` preserves the coordinate along `k`. -/
@[simp]
theorem kCoord_mul_swap_shear (Y : Matrix p p R) (hY : Yᴴ = -Y) :
    D.kCoord * ((D.swap.shear Y hY : GL n R) : Matrix n n R) = D.kCoord := by
  simpa using D.swap.lCoord_mul_shear Y hY

/-- A shear along the frame `l` by `Y` changes the coordinate along `l` by `Y` times the
coordinate along `k`. -/
@[simp]
theorem lCoord_mul_swap_shear (Y : Matrix p p R) (hY : Yᴴ = -Y) :
    D.lCoord * ((D.swap.shear Y hY : GL n R) : Matrix n n R) = D.lCoord + Y * D.kCoord := by
  simpa using D.swap.kCoord_mul_shear Y hY

/-! ### The parabolic subgroup -/

/-- The **parabolic subgroup** of the splitting: the elements `g` of the unitary group of `A`
stabilizing the isotropic subspace spanned by the frame `k`, that is `g k = k a` for some
`a ∈ GL_p(R)`. For an empty core it is a Siegel parabolic subgroup. -/
def parabolic : Subgroup (unitaryGroupOf A) where
  carrier := {g | ∃ a : GL p R, ((g : GL n R) : Matrix n n R) * D.k = D.k * (a : Matrix p p R)}
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hb]
    rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    -- `g⁻¹ k = g⁻¹ (g k) a⁻¹ = k a⁻¹`.
    have hk : D.k = (((g : GL n R)⁻¹ : GL n R) : Matrix n n R) * D.k * (a : Matrix p p R) := by
      rw [Matrix.mul_assoc, ← ha, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Subgroup.coe_inv]
    conv_rhs => rw [hk]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

/-- Membership in the parabolic subgroup: `g k = k a` for some `a ∈ GL_p(R)`. -/
theorem mem_parabolic_iff {g : unitaryGroupOf A} :
    g ∈ D.parabolic ↔
      ∃ a : GL p R, ((g : GL n R) : Matrix n n R) * D.k = D.k * (a : Matrix p p R) :=
  Iff.rfl

/-- The Levi elements lie in the parabolic subgroup. -/
theorem levi_mem_parabolic (x : GL p R × unitaryGroupOf A₀) : D.levi x ∈ D.parabolic :=
  ⟨x.1, D.levi_mul_k x⟩

/-- The shears lie in the parabolic subgroup. -/
theorem shear_mem_parabolic (X : Matrix p p R) (hX : Xᴴ = -X) : D.shear X hX ∈ D.parabolic :=
  ⟨1, by simp⟩

/-! ### Unipotent elements -/

variable [Invertible (2 : R)] {j : Rˣ} (hj : star (j : R) = -j)

variable (j) in
/-- The corner `⅟2 (j⁻¹ (b + bᴴ) + cᴴ A₀ c)` of the unipotent element `n(c, b)`: its image of `l`
has component `-unipotentCorner j c b` along `k`. -/
private def unipotentCorner (c : Matrix n₀ p R) (b : Matrix p p R) : Matrix p p R :=
  ⅟(2 : R) • ((↑j⁻¹ : R) • (b + bᴴ) + cᴴ * A₀ * c)

omit [DecidableEq n] in
include D hj in
/-- The hermitian part of the corner is `cᴴ A₀ c / 2`, the condition for `n(c, b)` to preserve
the form. -/
private theorem unipotentCorner_add_conjTranspose (c : Matrix n₀ p R) (b : Matrix p p R) :
    unipotentCorner (A₀ := A₀) j c b + (unipotentCorner (A₀ := A₀) j c b)ᴴ = cᴴ * A₀ * c := by
  have h₀ : A₀ᴴ = A₀ := D.isHermitian_core.eq
  -- `star j⁻¹ = (star j)⁻¹ = (-j)⁻¹ = -j⁻¹`.
  have hj' : star (↑j⁻¹ : R) = -↑j⁻¹ := by
    rw [← Units.coe_star_inv, show star j = -j from Units.ext (by rw [Units.coe_star, hj,
      Units.val_neg]), inv_neg, Units.val_neg]
  simp only [unipotentCorner, conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
    conjTranspose_conjTranspose, h₀, star_invOf, star_ofNat, hj',
    Matrix.mul_assoc]
  rw [← smul_add, neg_smul, add_comm (bᴴ) b]
  rw [show ∀ x y : Matrix p p R, x + y + (-x + y) = (2 : R) • y by intro x y; module,
    smul_smul, invOf_mul_self, one_smul]

variable (j) in
/-- The matrix of the unipotent element `n(c, b)`. -/
private def unipotentMatrix (c : Matrix n₀ p R) (b : Matrix p p R) : Matrix n n R :=
  1 - D.ι * c * D.lCoord + D.k * (cᴴ * A₀) * D.ιCoord -
    D.k * unipotentCorner (A₀ := A₀) j c b * D.lCoord

private theorem unipotentMatrix_mul_k (c : Matrix n₀ p R) (b : Matrix p p R) :
    D.unipotentMatrix j c b * D.k = D.k := by
  simp [unipotentMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc]

private theorem unipotentMatrix_mul_ι (c : Matrix n₀ p R) (b : Matrix p p R) :
    D.unipotentMatrix j c b * D.ι = D.ι + D.k * (cᴴ * A₀) := by
  simp [unipotentMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc]

private theorem unipotentMatrix_mul_l (c : Matrix n₀ p R) (b : Matrix p p R) :
    D.unipotentMatrix j c b * D.l = D.l - D.ι * c - D.k * unipotentCorner (A₀ := A₀) j c b := by
  simp [unipotentMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc]

include hj in
private theorem unipotentMatrix_mem (c : Matrix n₀ p R) (b : Matrix p p R) :
    star (D.unipotentMatrix j c b) * A * D.unipotentMatrix j c b = A := by
  have h₀ : A₀ᴴ = A₀ := D.isHermitian_core.eq
  -- The hermitian part of the corner, the condition for the isotropy of the image of `l`.
  have hZ :
      (unipotentCorner (A₀ := A₀) j c b)ᴴ = cᴴ * (A₀ * c) - unipotentCorner (A₀ := A₀) j c b := by
    rw [← Matrix.mul_assoc, ← D.unipotentCorner_add_conjTranspose hj c b, add_sub_cancel_left]
  rw [star_eq_conjTranspose]
  refine D.conjTranspose_mul_mul_eq_of_frames ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [unipotentMatrix_mul_k, unipotentMatrix_mul_ι, unipotentMatrix_mul_l, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h₀, hZ]

/-- The **unipotent element** `n(c, b)` of a splitting, for `c : Matrix n₀ p R` and
`b : Matrix p p R`: it fixes the frame `k`, sends the core `ι` to `ι + k cᴴ A₀` and the frame `l` to
`l - ι c - k ⅟2 (j⁻¹ (b + bᴴ) + cᴴ A₀ c)`. Here `j` is a unit with `star j = -j`. -/
def unipotent (c : Matrix n₀ p R) (b : Matrix p p R) : unitaryGroupOf A :=
  unitaryGroupOf.ofMatrix D.isUnit (D.unipotentMatrix j c b) (D.unipotentMatrix_mem hj c b)

private theorem val_unipotent_eq_unipotentMatrix (c : Matrix n₀ p R) (b : Matrix p p R) :
    ((D.unipotent hj c b : GL n R) : Matrix n n R) = D.unipotentMatrix j c b :=
  unitaryGroupOf.val_ofMatrix _ _ _

/-- The matrix of the unipotent element `n(c, b)`. -/
theorem val_unipotent (c : Matrix n₀ p R) (b : Matrix p p R) :
    ((D.unipotent hj c b : GL n R) : Matrix n n R) =
      1 - D.ι * c * D.lCoord + D.k * (cᴴ * A₀) * D.ιCoord -
        D.k * (⅟(2 : R) • ((↑j⁻¹ : R) • (b + bᴴ) + cᴴ * A₀ * c)) * D.lCoord := by
  rw [val_unipotent_eq_unipotentMatrix, unipotentMatrix, unipotentCorner]

/-- The unipotent element `n(c, b)` fixes the frame `k`. -/
@[simp]
theorem unipotent_mul_k (c : Matrix n₀ p R) (b : Matrix p p R) :
    ((D.unipotent hj c b : GL n R) : Matrix n n R) * D.k = D.k := by
  rw [val_unipotent_eq_unipotentMatrix, unipotentMatrix_mul_k]

/-- The unipotent element `n(c, b)` sends the core `ι` to `ι + k cᴴ A₀`. -/
@[simp]
theorem unipotent_mul_ι (c : Matrix n₀ p R) (b : Matrix p p R) :
    ((D.unipotent hj c b : GL n R) : Matrix n n R) * D.ι = D.ι + D.k * (cᴴ * A₀) := by
  rw [val_unipotent_eq_unipotentMatrix, unipotentMatrix_mul_ι]

/-- The unipotent element `n(c, b)` sends the frame `l` to
`l - ι c - k ⅟2 (j⁻¹ (b + bᴴ) + cᴴ A₀ c)`. -/
@[simp]
theorem unipotent_mul_l (c : Matrix n₀ p R) (b : Matrix p p R) :
    ((D.unipotent hj c b : GL n R) : Matrix n n R) * D.l =
      D.l - D.ι * c - D.k * (⅟(2 : R) • ((↑j⁻¹ : R) • (b + bᴴ) + cᴴ * A₀ * c)) := by
  rw [val_unipotent_eq_unipotentMatrix, unipotentMatrix_mul_l, unipotentCorner]

/-- **Only the hermitian part of `b` matters**: `n(c, b) = n(c', b')` exactly when `c = c'` and
`b + bᴴ = b' + b'ᴴ`. -/
theorem unipotent_eq_unipotent_iff {c c' : Matrix n₀ p R} {b b' : Matrix p p R} :
    D.unipotent hj c b = D.unipotent hj c' b' ↔ c = c' ∧ b + bᴴ = b' + b'ᴴ := by
  constructor
  · intro h
    have hl := congrArg (fun g : unitaryGroupOf A ↦ ((g : GL n R) : Matrix n n R) * D.l) h
    simp only [unipotent_mul_l] at hl
    have hc : c = c' := by
      simpa [Matrix.mul_sub] using congrArg (D.ιCoord * ·) hl
    subst hc
    -- Read off the `k`-coordinate of the image of `l`, and multiply by `2 j`.
    have hb := congrArg (fun M ↦ (2 : R) • (j : R) • (-(D.kCoord * M))) hl
    have h2 : (2 : R) * ((j : R) * (⅟2 * ↑j⁻¹)) = 1 := by
      calc (2 : R) * ((j : R) * (⅟2 * ↑j⁻¹)) = (2 * ⅟2) * ((j : R) * ↑j⁻¹) := by ring
        _ = 1 := by simp
    simp only [Matrix.mul_sub, kCoord_mul_l, kCoord_mul_ι_mul, kCoord_mul_k_mul, zero_sub,
      sub_zero, neg_neg, smul_add, smul_smul, add_left_inj, h2, one_smul] at hb
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, h⟩
    refine unitaryGroupOf.ext (D.ext_mul ?_ ?_ ?_) <;> simp [h]

/-- The unipotent element `n(0, 0)` is the identity. -/
@[simp]
theorem unipotent_zero_zero : D.unipotent hj 0 0 = 1 :=
  unitaryGroupOf.ext (D.ext_mul (by simp) (by simp) (by simp))

/-! ### The laws of the unipotent and Levi elements -/

omit [DecidableEq n] in
include D hj in
/-- The corners multiply as in a Heisenberg group. -/
private theorem unipotentCorner_add (c c' : Matrix n₀ p R) (b b' : Matrix p p R) :
    unipotentCorner (A₀ := A₀) j c b + cᴴ * A₀ * c' + unipotentCorner (A₀ := A₀) j c' b' =
      unipotentCorner (A₀ := A₀) j (c + c') (b + (j : R) • (cᴴ * A₀ * c') + b') := by
  have h₀ : A₀ᴴ = A₀ := D.isHermitian_core.eq
  have hjj : (↑j⁻¹ : R) * j = 1 := Units.inv_mul j
  simp only [unipotentCorner, conjTranspose_add, conjTranspose_smul, conjTranspose_mul,
    conjTranspose_conjTranspose, h₀, hj, Matrix.add_mul, Matrix.mul_add, smul_add, neg_smul,
    smul_neg, smul_smul, hjj, one_smul, Matrix.mul_assoc]
  rw [← sub_eq_zero]
  have h2 : (⅟2 : R) + ⅟2 = 1 := invOf_two_add_invOf_two
  linear_combination (norm := module) -(h2 • (cᴴ * (A₀ * c') : Matrix p p R))

omit [DecidableEq n] in
/-- The corners transform under the Levi elements by congruence. -/
private theorem unipotentCorner_conj (a : GL p R) (g₀ : unitaryGroupOf A₀) (c : Matrix n₀ p R)
    (b : Matrix p p R) :
    unipotentCorner (A₀ := A₀) j (((g₀ : GL n₀ R) : Matrix n₀ n₀ R) * c * (a : Matrix p p R)ᴴ)
        ((a : Matrix p p R) * b * (a : Matrix p p R)ᴴ) =
      (a : Matrix p p R) * unipotentCorner (A₀ := A₀) j c b * (a : Matrix p p R)ᴴ := by
  simp only [unipotentCorner, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
    unitaryGroupOf.conjTranspose_mul_mul_mul_cancel, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul]

/-- **The group law of the unipotent elements**:
`n(c, b) n(c', b') = n(c + c', b + j cᴴ A₀ c' + b')`. -/
theorem unipotent_mul_unipotent (c c' : Matrix n₀ p R) (b b' : Matrix p p R) :
    D.unipotent hj c b * D.unipotent hj c' b' =
      D.unipotent hj (c + c') (b + (j : R) • (cᴴ * A₀ * c') + b') := by
  refine unitaryGroupOf.ext (D.ext_mul ?_ ?_ ?_) <;>
    simp only [Subgroup.coe_mul, Units.val_mul, val_unipotent_eq_unipotentMatrix, Matrix.mul_assoc,
      unipotentMatrix_mul_k, unipotentMatrix_mul_ι, unipotentMatrix_mul_l, Matrix.mul_add,
      Matrix.mul_sub]
  · simp only [← Matrix.mul_assoc, unipotentMatrix_mul_k, conjTranspose_add,
      Matrix.add_mul, Matrix.mul_add]
    abel
  · simp only [← Matrix.mul_assoc, unipotentMatrix_mul_k, unipotentMatrix_mul_ι]
    rw [← D.unipotentCorner_add hj]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel

/-- The inverse of the unipotent element `n(c, b)` is `n(-c, -b)`. -/
theorem unipotent_inv (c : Matrix n₀ p R) (b : Matrix p p R) :
    (D.unipotent hj c b)⁻¹ = D.unipotent hj (-c) (-b) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [unipotent_mul_unipotent, ← D.unipotent_zero_zero hj, unipotent_eq_unipotent_iff]
  have h₀ : A₀ᴴ = A₀ := D.isHermitian_core.eq
  refine ⟨add_neg_cancel c, ?_⟩
  simp [conjTranspose_smul, hj, h₀, Matrix.mul_assoc]

/-- **The Levi elements normalize the unipotent elements**:
`m(a, g₀) n(c, b) = n(g₀ c aᴴ, a b aᴴ) m(a, g₀)`. -/
theorem levi_mul_unipotent (x : GL p R × unitaryGroupOf A₀) (c : Matrix n₀ p R)
    (b : Matrix p p R) :
    D.levi x * D.unipotent hj c b =
      D.unipotent hj (((x.2 : GL n₀ R) : Matrix n₀ n₀ R) * c * (x.1 : Matrix p p R)ᴴ)
          ((x.1 : Matrix p p R) * b * (x.1 : Matrix p p R)ᴴ) * D.levi x := by
  refine unitaryGroupOf.ext (D.ext_mul ?_ ?_ ?_) <;>
    simp only [Subgroup.coe_mul, Units.val_mul, val_unipotent_eq_unipotentMatrix,
      val_levi_eq_leviMatrix, Matrix.mul_assoc, unipotentMatrix_mul_k, unipotentMatrix_mul_ι,
      unipotentMatrix_mul_l, leviMatrix_mul_k, leviMatrix_mul_ι, leviMatrix_mul_l, Matrix.mul_add,
      Matrix.mul_sub] <;>
    simp only [← Matrix.mul_assoc, unipotentMatrix_mul_k, unipotentMatrix_mul_ι,
      unipotentMatrix_mul_l, leviMatrix_mul_k, leviMatrix_mul_ι]
  · simp only [Matrix.add_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      unitaryGroupOf.conjTranspose_mul_mul_cancel]
  · have ha : (x.1 : Matrix p p R)ᴴ * (x.1 : Matrix p p R)⁻¹ᴴ = 1 := by
      rw [← conjTranspose_mul, nonsing_inv_mul _ (isUnits_det_units x.1), conjTranspose_one]
    rw [unipotentCorner_conj]
    simp only [Matrix.sub_mul, Matrix.mul_assoc, ha, Matrix.mul_one]

/-- **Conjugation of a unipotent element by a Levi element**:
`m(a, g₀) n(c, b) m(a, g₀)⁻¹ = n(g₀ c aᴴ, a b aᴴ)`. -/
theorem levi_mul_unipotent_mul_inv_levi (x : GL p R × unitaryGroupOf A₀) (c : Matrix n₀ p R)
    (b : Matrix p p R) :
    D.levi x * D.unipotent hj c b * (D.levi x)⁻¹ =
      D.unipotent hj (((x.2 : GL n₀ R) : Matrix n₀ n₀ R) * c * (x.1 : Matrix p p R)ᴴ)
        ((x.1 : Matrix p p R) * b * (x.1 : Matrix p p R)ᴴ) := by
  rw [levi_mul_unipotent, mul_inv_cancel_right]

/-! ### The Levi decomposition -/

omit [Invertible (2 : R)] in
/-- An element of the unitary group acting on the frame `k` by `t` acts on the coordinate along
`l` by `(t⁻¹)ᴴ`. -/
private theorem lCoord_mul_of_mul_k (g : unitaryGroupOf A) (t : GL p R)
    (hk : ((g : GL n R) : Matrix n n R) * D.k = D.k * (t : Matrix p p R)) :
    D.lCoord * ((g : GL n R) : Matrix n n R) = (t : Matrix p p R)⁻¹ᴴ * D.lCoord := by
  set G := ((g : GL n R) : Matrix n n R)
  -- `k = G k t⁻¹`, so `kᴴ A G = (t⁻¹)ᴴ (G k)ᴴ A G = (t⁻¹)ᴴ kᴴ A`.
  have hk' : D.k = G * D.k * (t : Matrix p p R)⁻¹ := by
    rw [hk, Matrix.mul_assoc, mul_nonsing_inv _ (isUnits_det_units t), Matrix.mul_one]
  calc D.lCoord * G = (G * D.k * (t : Matrix p p R)⁻¹)ᴴ * A * (G * 1) := by
        rw [← hk', lCoord_def, Matrix.mul_one]
    _ = (t : Matrix p p R)⁻¹ᴴ * ((G * D.k)ᴴ * A * (G * 1)) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (t : Matrix p p R)⁻¹ᴴ * D.lCoord := by
      rw [conjTranspose_mul_mul_mul_of_star_mul_mul_eq (R := R)
          (mem_unitaryGroupOf_iff.mp g.property),
        Matrix.mul_one, conjTranspose_k_mul]

omit [DecidableEq n] [Fintype p] [DecidableEq n₀] [DecidableEq p] in
include hj in
/-- The corner of the unipotent element that undoes the `l`-column `l + ι Y + k X` of an element of
the unitary group fixing `k`: the isotropy relation `X + Yᴴ A₀ Y + Xᴴ = 0` makes it `-X`. -/
private theorem unipotentCorner_neg_neg_smul {X : Matrix p p R} {Y : Matrix n₀ p R}
    (h : X + Yᴴ * (A₀ * Y) + Xᴴ = 0) :
    unipotentCorner (A₀ := A₀) j (-Y) (-((j : R) • X)) = -X := by
  have hjj : (↑j⁻¹ : R) * j = 1 := Units.inv_mul j
  have h' : Yᴴ * A₀ * Y = -X - Xᴴ := by
    rw [Matrix.mul_assoc, ← sub_eq_zero, ← h]
    abel
  simp only [unipotentCorner, conjTranspose_neg, conjTranspose_smul, hj, neg_smul, neg_neg,
    Matrix.neg_mul, Matrix.mul_neg, h', smul_add, smul_neg, smul_smul, hjj, one_smul]
  have h2 : (⅟2 : R) + ⅟2 = 1 := invOf_two_add_invOf_two
  linear_combination (norm := module) -(h2 • X)

/-- **The unipotent elements form the unipotent radical of the parabolic**: an element `g` of the
unitary group of `A` is a unipotent element `n(c, b)` exactly when it fixes the frame `k` pointwise
and has core block `ιCoord g ι = 1`. -/
theorem exists_eq_unipotent_iff (g : unitaryGroupOf A) :
    (∃ (c : Matrix n₀ p R) (b : Matrix p p R), g = D.unipotent hj c b) ↔
      ((g : GL n R) : Matrix n n R) * D.k = D.k ∧
        D.ιCoord * ((g : GL n R) : Matrix n n R) * D.ι = 1 := by
  constructor
  · rintro ⟨c, b, rfl⟩
    refine ⟨D.unipotent_mul_k hj c b, ?_⟩
    rw [Matrix.mul_assoc, unipotent_mul_ι]
    simp [Matrix.mul_add]
  rintro ⟨hk, hι⟩
  set G := ((g : GL n R) : Matrix n n R)
  have hlG : D.lCoord * G = D.lCoord := by
    simpa using D.lCoord_mul_of_mul_k g 1 (by simpa using hk)
  -- Write `G = k X + ι Y + l lCoord` with `X = kCoord G` and `Y = ιCoord G`.
  have hGι : G * D.ι = D.k * (D.kCoord * G * D.ι) + D.ι := by
    conv_lhs => rw [← D.k_mul_kCoord_mul_add_ι_mul_ιCoord_mul_add_l_mul_lCoord_mul G, hlG]
    simp [Matrix.add_mul, Matrix.mul_assoc, hι]
  have hGl : G * D.l = D.k * (D.kCoord * G * D.l) + D.ι * (D.ιCoord * G * D.l) + D.l := by
    conv_lhs => rw [← D.k_mul_kCoord_mul_add_ι_mul_ιCoord_mul_add_l_mul_lCoord_mul G, hlG]
    simp [Matrix.add_mul, Matrix.mul_assoc]
  -- `G` preserves the pairings of `l` with `ι` and with itself.
  have hg := mem_unitaryGroupOf_iff.mp g.property
  have h1 := conjTranspose_mul_mul_mul_of_star_mul_mul_eq hg D.l D.ι
  have h2 := conjTranspose_mul_mul_mul_of_star_mul_mul_eq hg D.l D.l
  -- Name the blocks of `G` that occur.
  generalize D.kCoord * G * D.ι = Xι at hGι
  generalize D.kCoord * G * D.l = Xl at hGl
  generalize D.ιCoord * G * D.l = Yl at hGl
  rw [hGι, hGl] at h1
  rw [hGl] at h2
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, conjTranspose_k_mul_mul, conjTranspose_ι_mul_mul, conjTranspose_l_mul_mul,
    lCoord_mul_k_mul, lCoord_mul_ι_mul, ιCoord_mul_k_mul, ιCoord_mul_ι_mul, kCoord_mul_k_mul,
    kCoord_mul_ι_mul, lCoord_mul_l, ιCoord_mul_l, kCoord_mul_l, lCoord_mul_ι, ιCoord_mul_ι,
    kCoord_mul_ι, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add] at h1 h2
  -- `h1 : Xι + Ylᴴ A₀ = 0` and `h2 : Xl + Ylᴴ A₀ Yl + Xlᴴ = 0`.
  refine ⟨-Yl, -((j : R) • Xl), unitaryGroupOf.ext (D.ext_mul ?_ ?_ ?_)⟩
  · rw [hk, unipotent_mul_k]
  · rw [hGι, unipotent_mul_ι, eq_neg_of_add_eq_zero_left h1]
    simp [add_comm]
  · rw [hGl, val_unipotent_eq_unipotentMatrix, unipotentMatrix_mul_l,
      unipotentCorner_neg_neg_smul hj h2]
    simp only [Matrix.mul_neg, sub_neg_eq_add]
    abel

omit [Invertible (2 : R)] in
/-- The block on the core of an element of the unitary group that maps the span of `k` to itself
lies in the unitary group of `A₀`. -/
private theorem core_mem_of_mul_k (g : unitaryGroupOf A) (t : GL p R)
    (hk : ((g : GL n R) : Matrix n n R) * D.k = D.k * (t : Matrix p p R)) :
    star (D.ιCoord * ((g : GL n R) : Matrix n n R) * D.ι) * A₀ *
      (D.ιCoord * ((g : GL n R) : Matrix n n R) * D.ι) = A₀ := by
  set G := ((g : GL n R) : Matrix n n R)
  -- `G ι = k (kCoord G ι) + ι (ιCoord G ι)`: its coordinate along `l` vanishes.
  have hGι : G * D.ι = D.k * (D.kCoord * G * D.ι) + D.ι * (D.ιCoord * G * D.ι) := by
    conv_lhs => rw [← D.k_mul_kCoord_mul_add_ι_mul_ιCoord_mul_add_l_mul_lCoord_mul (G * D.ι),
      ← Matrix.mul_assoc D.lCoord, D.lCoord_mul_of_mul_k g t hk]
    simp [Matrix.mul_assoc]
  -- `G` preserves the Gram matrix `ιᴴ A ι = A₀` of the core.
  have h := conjTranspose_mul_mul_mul_of_star_mul_mul_eq (R := R)
    (mem_unitaryGroupOf_iff.mp g.property) D.ι D.ι
  rw [hGι, D.gram_ιι] at h
  generalize D.kCoord * G * D.ι = X at h
  generalize D.ιCoord * G * D.ι = Y at h ⊢
  rw [star_eq_conjTranspose]
  conv_rhs => rw [← h]
  simp [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]

/-- **The Levi decomposition**: an element `g` of the unitary group of `A` that acts on the frame
`k` by a matrix `a` (`g k = k a`) is a product `n(c, b) m(a, g₀)` of a unipotent element and a Levi
element, where `g₀ = ιCoord g ι` is the block of `g` on the core. -/
theorem exists_eq_unipotent_mul_levi (g : unitaryGroupOf A) {a : Matrix p p R}
    (hk : ((g : GL n R) : Matrix n n R) * D.k = D.k * a) :
    ∃ (c : Matrix n₀ p R) (b : Matrix p p R) (x : GL p R × unitaryGroupOf A₀),
      g = D.unipotent hj c b * D.levi x ∧ (x.1 : Matrix p p R) = a ∧
        ((x.2 : GL n₀ R) : Matrix n₀ n₀ R) = D.ιCoord * ((g : GL n R) : Matrix n n R) * D.ι := by
  set G := ((g : GL n R) : Matrix n n R)
  -- `a` is invertible, with left inverse `kCoord g⁻¹ k`.
  obtain ⟨t, rfl⟩ : IsUnit a := by
    refine IsUnit.of_mul_eq_one_right (D.kCoord * ((g⁻¹ : GL n R) : Matrix n n R) * D.k) ?_
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hk, ← Matrix.mul_assoc _ G, Units.inv_mul,
      Matrix.one_mul, kCoord_mul_k]
  let g₀ : unitaryGroupOf A₀ :=
    unitaryGroupOf.ofMatrix D.isUnit_core _ (D.core_mem_of_mul_k g t hk)
  have hg₀ : ((g₀ : GL n₀ R) : Matrix n₀ n₀ R) = D.ιCoord * G * D.ι :=
    unitaryGroupOf.val_ofMatrix _ _ _
  -- `g m(t, g₀)⁻¹` fixes `k` and has core block `1`, so it is a unipotent element.
  obtain ⟨c, b, hcb⟩ := (D.exists_eq_unipotent_iff hj (g * (D.levi (t, g₀))⁻¹)).mpr <| by
    rw [← map_inv]
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, levi_mul_k, levi_mul_ι,
      Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv]
    refine ⟨?_, ?_⟩
    · rw [← Matrix.mul_assoc, hk, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    · rw [← Matrix.mul_assoc D.ιCoord G, ← Matrix.mul_assoc, ← hg₀, Units.mul_inv]
  exact ⟨c, b, (t, g₀), mul_inv_eq_iff_eq_mul.mp hcb, rfl, hg₀⟩

/-! ### The parabolic subgroup and the unipotent elements -/

/-- The unipotent elements lie in the parabolic subgroup. -/
theorem unipotent_mem_parabolic (c : Matrix n₀ p R) (b : Matrix p p R) :
    D.unipotent hj c b ∈ D.parabolic :=
  ⟨1, by simp⟩

/-- **The Levi decomposition of the parabolic subgroup**: its elements are exactly the products
`n(c, b) m(x)` of a unipotent element and a Levi element. -/
theorem mem_parabolic_iff_exists_unipotent_mul_levi {g : unitaryGroupOf A} :
    g ∈ D.parabolic ↔
      ∃ (c : Matrix n₀ p R) (b : Matrix p p R) (x : GL p R × unitaryGroupOf A₀),
        g = D.unipotent hj c b * D.levi x := by
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, ?_⟩
  · obtain ⟨c, b, x, hg, -⟩ := D.exists_eq_unipotent_mul_levi hj g ha
    exact ⟨c, b, x, hg⟩
  · rintro ⟨c, b, x, rfl⟩
    exact mul_mem (D.unipotent_mem_parabolic hj c b) (D.levi_mem_parabolic x)

/-- When `2` is invertible, the shear by a skew-hermitian `X` is the unipotent element
`n(0, -j X)`. -/
theorem shear_eq_unipotent {X : Matrix p p R} (hX : Xᴴ = -X) :
    D.shear X hX = D.unipotent hj 0 (-((j : R) • X)) := by
  have hjj : (↑j⁻¹ : R) * j = 1 := Units.inv_mul j
  -- The corner of `n(0, -j X)` is `⅟2 (j⁻¹ (-j X - j X)) = -X`.
  have hcorner : ⅟(2 : R) • ((↑j⁻¹ : R) • (-((j : R) • X) + (-((j : R) • X))ᴴ) +
      (0 : Matrix n₀ p R)ᴴ * A₀ * (0 : Matrix n₀ p R)) = -X := by
    simp only [conjTranspose_neg, conjTranspose_smul, conjTranspose_zero, hj, hX,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, neg_smul, smul_neg, neg_neg, smul_add,
      smul_smul, hjj, one_smul]
    rw [← neg_add, ← add_smul, invOf_two_add_invOf_two, one_smul]
  refine unitaryGroupOf.ext (D.ext_mul ?_ ?_ ?_)
  · simp
  · simp
  · rw [shear_mul_l, unipotent_mul_l, hcorner]
    simp [sub_eq_add_neg]

end IsotropicSplitting

end TauCeti
