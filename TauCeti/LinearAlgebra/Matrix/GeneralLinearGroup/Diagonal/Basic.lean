/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL` and `Matrix.GeneralLinearGroup.det` occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- Permutation matrices provide the canonical normalizer action on diagonal matrices.
public import Mathlib.LinearAlgebra.Matrix.Permutation
-- `MulEquiv.piUnits` identifies the units of a product with the product of the units, and is what
-- makes the diagonal embedding a homomorphism.
public import Mathlib.Algebra.Group.Pi.Units
-- `Subgroup.centralizer` and its maximal-commutative-subgroup API occur below.
public import TauCeti.Algebra.Group.Subgroup.Centralizer
-- `Matrix.IsDiag` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.IsDiag
-- `Nat.card` occurs in the statement of `TauCeti.natCard_diagonalTorus`.
public import Mathlib.SetTheory.Cardinal.Finite
-- `Nat.card_units`, the number of units of a `GroupWithZero`.
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Diagonal elements of the general linear group, and the diagonal torus

A family of units indexed by a finite type `ι` is the diagonal of an invertible diagonal matrix,
and this assignment is an injective group homomorphism `TauCeti.diagGL : (ι → kˣ) →* GL ι k`.
Its entries, trace and determinant are recorded here, together with the fact that the diagonal
entries of an invertible diagonal matrix are units.

The image of `diagGL` is the **diagonal torus**

`TauCeti.diagonalTorus k n = (TauCeti.diagGL : (Fin n → kˣ) →* GL (Fin n) k).range`

of `GL n k`, for which three descriptions are given. As the range of an injective homomorphism
it is isomorphic to the coordinatewise units `Fin n → kˣ` (`TauCeti.diagonalTorusEquiv`), whence
its order `(q - 1)ⁿ` over a division semiring with `q` elements
(`TauCeti.natCard_diagonalTorus`). An invertible matrix lies in it exactly when it is diagonal
(`TauCeti.mem_diagonalTorus_iff`). And over a commutative semiring with cancellation by nonzero
elements and at least two units it is its own centralizer (`TauCeti.centralizer_diagonalTorus`),
hence a maximal abelian subgroup of `GL n k`.

The hypothesis that `kˣ` is nontrivial cannot be dropped: over a semiring with a single unit,
such as `𝔽₂`, the torus is trivial (`TauCeti.diagonalTorus_eq_bot`) while its centralizer is the
whole of `GL n k` (`TauCeti.centralizer_diagonalTorus_eq_top`).

A scalar matrix is central in `GL ι k` over any commutative semiring
(`TauCeti.scalar_mem_center`), and `diagGL` sends a constant family to the corresponding scalar
element (`TauCeti.diagGL_const`).

## Main definitions

* `TauCeti.diagGL` embeds a family of units as an invertible diagonal matrix.
* `TauCeti.diagonalTorus`: the subgroup of invertible diagonal matrices in `GL n k`.
* `TauCeti.diagonalTorusEquiv`: the identification `(Fin n → kˣ) ≃* diagonalTorus k n`.
* `TauCeti.detOneRescale`: the explicit rescaling of the first column of an invertible matrix
  that makes its determinant one.

## Main statements

* `TauCeti.isUnit_apply_of_isDiag`: the diagonal entries of an invertible diagonal matrix are
  units.
* `TauCeti.exists_det_eq_one_mul_map_eq_map_mul_diagGL`: a matrix intertwining another matrix with
  a diagonal matrix can be normalized to have determinant one while preserving the equation.
* `TauCeti.mem_diagonalTorus_iff`: membership in the torus is diagonality of the matrix.
* `TauCeti.mul_diagGL_of_coe_eq_permMatrix`: a permutation matrix moves past a diagonal by
  relabelling its entries.
* `TauCeti.natCard_diagonalTorus`: the torus has `(q - 1)ⁿ` elements over a division semiring
  with `q` elements.
* `TauCeti.centralizer_diagonalTorus`: the diagonal torus is its own centralizer.
* `TauCeti.mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL` and
  `TauCeti.mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL`: inside any subgroup, an element
  centralizes a family of diagonal elements exactly when its entries vanish between the
  coordinates the family separates; for a family separating all coordinates, exactly when it is
  diagonal.
* `TauCeti.centralizer_diagonalTorus_eq_top`: over a semiring with a single unit the centralizer
  is instead the whole group.
* `TauCeti.scalar_mem_center` and `TauCeti.centralizer_scalar`: a scalar matrix is central, so its
  centralizer is the whole group.
* `TauCeti.diagGL_const` and `TauCeti.notMem_range_scalar_diagGL`: the diagonal embedding sends a
  constant family to the corresponding scalar element, and it is scalar *only* there.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

section Semiring

variable [Semiring k]

/-- Coordinatewise units embed in a general linear group as diagonal matrices. -/
def diagGL : (ι → kˣ) →* GL ι k :=
  (Units.map (Matrix.diagonalRingHom ι k).toMonoidHom).comp
    (MulEquiv.piUnits).symm.toMonoidHom

/-- The matrix underlying `diagGL t` is the diagonal matrix with entries `t i`. -/
@[simp]
theorem diagGL_coe (t : ι → kˣ) :
    (diagGL t : Matrix ι ι k) = Matrix.diagonal fun i => (t i : k) := by
  rfl

/-- The entries of `diagGL t` vanish off the diagonal and equal `t i` on it. -/
@[simp]
theorem diagGL_apply (t : ι → kˣ) (i j : ι) :
    diagGL t i j = if i = j then (t i : k) else 0 := by
  rw [diagGL_coe, Matrix.diagonal_apply]

/-- The trace of a diagonal element of the general linear group is the sum of its diagonal
entries. -/
theorem trace_diagGL (t : ι → kˣ) :
    (diagGL t : Matrix ι ι k).trace = ∑ i, (t i : k) := by
  rw [diagGL_coe, Matrix.trace_diagonal]

/-- The diagonal embedding is injective. -/
theorem diagGL_injective : Function.Injective (diagGL (k := k) (ι := ι)) := fun t s h =>
  funext fun i => Units.ext <| by
    simpa using congrArg (fun g : GL ι k ↦ (g : Matrix ι ι k) i i) h

/-- **A constant family of units embeds as the corresponding scalar element** of the general linear
group. Together with `TauCeti.notMem_range_scalar_diagGL` this says that the diagonal embedding is
scalar exactly on the constant families. -/
@[simp]
theorem diagGL_const (a : kˣ) :
    diagGL (fun _ : ι => a) = Matrix.GeneralLinearGroup.scalar ι a :=
  Units.ext <| by rw [diagGL_coe, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- An invertible diagonal matrix with two distinct diagonal entries is not scalar. -/
theorem notMem_range_scalar_diagGL {t : ι → kˣ} {i j : ι} (ht : t i ≠ t j) :
    (diagGL t : Matrix ι ι k) ∉ Set.range (Matrix.scalar ι) := by
  rintro ⟨c, hc⟩
  refine ht (Units.ext ?_)
  have hi : c = (t i : k) := by simpa using congrFun (congrFun hc i) i
  have hj : c = (t j : k) := by simpa using congrFun (congrFun hc j) j
  rw [← hi, ← hj]

/-- A general-linear element whose underlying matrix is the permutation matrix of `π` moves
past a diagonal matrix by relabelling its diagonal entries along `π`. -/
theorem mul_diagGL_of_coe_eq_permMatrix
    (g : GL ι k) (π : Equiv.Perm ι) (hg : (g : Matrix ι ι k) = π.permMatrix k)
    (d : ι → kˣ) :
    g * diagGL d = diagGL (d ∘ π) * g := by
  ext i j
  simp only [Units.val_mul, diagGL_coe, hg, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul, Matrix.submatrix_apply, Matrix.diagonal_apply]
  grind

/-- The diagonal entries of an invertible diagonal matrix are units. Unlike Mathlib's
`Matrix.isUnit_diagonal`, this assumes no commutativity of `k`. -/
theorem isUnit_apply_of_isDiag {g : GL ι k} (hg : (g : Matrix ι ι k).IsDiag) (i : ι) :
    IsUnit ((g : Matrix ι ι k) i i) := by
  have h₁ := congrFun (congrFun g.mul_inv i) i
  have h₂ := congrFun (congrFun g.inv_mul i) i
  rw [← hg.diagonal_diag, Matrix.diagonal_mul, Matrix.one_apply_eq] at h₁
  rw [← hg.diagonal_diag, Matrix.mul_diagonal, Matrix.one_apply_eq] at h₂
  exact ⟨⟨_, _, h₁, h₂⟩, rfl⟩

/-- The **diagonal torus** of `GL n k`: the image of the coordinatewise units under `diagGL`. -/
def diagonalTorus (k : Type u) [Semiring k] (n : ℕ) : Subgroup (GL (Fin n) k) :=
  MonoidHom.range (diagGL (k := k) (ι := Fin n))

/-- Membership in the diagonal torus, read off its definition as a range: an element lies in it
exactly when it is `diagGL t` for a family of units `t`. -/
theorem mem_diagonalTorus_iff_exists_diagGL {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ ∃ t : Fin n → kˣ, diagGL t = g :=
  MonoidHom.mem_range

/-- An invertible matrix lies in the diagonal torus exactly when it is a diagonal matrix. -/
@[simp]
theorem mem_diagonalTorus_iff {g : GL (Fin n) k} :
    g ∈ diagonalTorus k n ↔ (g : Matrix (Fin n) (Fin n) k).IsDiag := by
  refine ⟨?_, fun hg => ⟨fun i => (isUnit_apply_of_isDiag hg i).unit, Units.ext ?_⟩⟩
  · rintro ⟨t, rfl⟩
    rw [diagGL_coe]
    exact Matrix.isDiag_diagonal _
  · rw [diagGL_coe]
    simp only [IsUnit.unit_spec]
    exact hg.diagonal_diag

/-- The diagonal torus is the group of coordinatewise units. -/
noncomputable def diagonalTorusEquiv (k : Type u) [Semiring k] (n : ℕ) :
    (Fin n → kˣ) ≃* diagonalTorus k n :=
  MonoidHom.ofInjective diagGL_injective

/-- The torus element attached to a family of units is `diagGL t`. -/
@[simp]
theorem coe_diagonalTorusEquiv_apply (t : Fin n → kˣ) :
    ((diagonalTorusEquiv k n t : diagonalTorus k n) : GL (Fin n) k) = diagGL t :=
  MonoidHom.ofInjective_apply diagGL_injective

/-- The `i`-th coordinate character of a torus element is its `(i, i)` matrix entry. -/
@[simp]
theorem coe_diagonalTorusEquiv_symm_apply (g : diagonalTorus k n) (i : Fin n) :
    (((diagonalTorusEquiv k n).symm g i : kˣ) : k) =
      ((g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i := by
  have h : diagGL ((diagonalTorusEquiv k n).symm g) = (g : GL (Fin n) k) :=
    MonoidHom.apply_ofInjective_symm diagGL_injective g
  conv_rhs => rw [← h, diagGL_coe]
  rw [Matrix.diagonal_apply_eq]

/-- **The order of the diagonal torus**: over a division semiring with `q` elements it has
`(q - 1)ⁿ` elements, one invertible scalar per diagonal entry. Over an infinite division semiring
both sides vanish when `n > 0`. -/
theorem natCard_diagonalTorus (k : Type u) [DivisionSemiring k] (n : ℕ) :
    Nat.card (diagonalTorus k n) = (Nat.card k - 1) ^ n := by
  rw [← Nat.card_congr (diagonalTorusEquiv k n).toEquiv, Nat.card_fun, Nat.card_units,
    Nat.card_fin]

/-- An element centralizing the diagonal torus commutes, as a matrix, with every diagonal matrix
of units. -/
theorem commute_diagonal_of_mem_centralizer {g : GL (Fin n) k}
    (hg : g ∈ Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k))) (t : Fin n → kˣ) :
    Commute (Matrix.diagonal fun i => (t i : k)) (g : Matrix (Fin n) (Fin n) k) := by
  have h := congrArg Units.val <|
    Subgroup.mem_centralizer_iff.mp hg _ (mem_diagonalTorus_iff_exists_diagGL.mpr ⟨t, rfl⟩)
  rwa [Units.val_mul, Units.val_mul, diagGL_coe] at h

section Subsingleton

variable [Subsingleton kˣ]

/-- Over a semiring with only one unit, such as `𝔽₂`, the diagonal torus is trivial. -/
theorem diagonalTorus_eq_bot : diagonalTorus k n = ⊥ := by
  refine eq_bot_iff.mpr ?_
  rintro - ⟨t, rfl⟩
  rw [Subgroup.mem_bot, Subsingleton.elim t 1, map_one]

/-- Over a semiring with only one unit the centralizer of the diagonal torus is the whole group,
while the torus itself is trivial by `TauCeti.diagonalTorus_eq_bot`. So the hypothesis
`Nontrivial kˣ` of `TauCeti.centralizer_diagonalTorus` cannot simply be dropped: the two
subgroups differ as soon as `GL n k` is nontrivial, as it is over `𝔽₂` for `n ≥ 2`. -/
theorem centralizer_diagonalTorus_eq_top :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = ⊤ := by
  simp [diagonalTorus_eq_bot, Subgroup.centralizer_eq_top_iff_subset]

end Subsingleton

end Semiring

section CommSemiring

variable [CommSemiring k]

/-- The diagonal torus is commutative. -/
instance instIsMulCommutativeDiagonalTorus : IsMulCommutative (diagonalTorus k n) :=
  Subgroup.range_isMulCommutative _

section Scalar

/-- **A scalar matrix is central in `GL ι k`**. Mathlib's
`Matrix.GeneralLinearGroup.scalar_commute` asks for a commutative ring. -/
theorem scalar_mem_center (u : kˣ) :
    Matrix.GeneralLinearGroup.scalar ι u ∈ Subgroup.center (GL ι k) :=
  Subgroup.mem_center_iff.mpr fun g => Units.ext
    ((Matrix.scalar_commute (u : k) (fun _ => Commute.all _ _) (g : Matrix ι ι k)).symm.eq)

/-- **The centralizer of a scalar matrix is everything**, scalar matrices being central. The size of
its conjugacy class is `TauCeti.ncard_carrier_mk_scalar`, in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer`. -/
@[simp]
theorem centralizer_scalar (u : kˣ) :
    Subgroup.centralizer {Matrix.GeneralLinearGroup.scalar ι u} = ⊤ :=
  Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr (scalar_mem_center u))

end Scalar

section IsLeftCancelMulZero

variable [IsLeftCancelMulZero k] [Nontrivial kˣ]

/-- **The diagonal torus is its own centralizer**, hence a maximal abelian subgroup of `GL n k`. -/
theorem centralizer_diagonalTorus :
    Subgroup.centralizer (diagonalTorus k n : Set (GL (Fin n) k)) = diagonalTorus k n := by
  refine le_antisymm (fun g hg => mem_diagonalTorus_iff.mpr fun i j hij => ?_)
    (Subgroup.le_centralizer _)
  obtain ⟨u, v, huv⟩ := exists_pair_ne kˣ
  refine apply_eq_zero_of_commute_diagonal
    (commute_diagonal_of_mem_centralizer hg fun m => if m = i then u else v) ?_
  rw [ite_eq_left rfl, ite_eq_right (Ne.symm hij)]
  exact fun h => huv (Units.ext h)

/-- A commutative subgroup of `GL n k` containing the diagonal torus equals it: this is the
maximality of the torus among abelian subgroups. -/
theorem eq_diagonalTorus_of_le_of_isMulCommutative (H : Subgroup (GL (Fin n) k))
    [IsMulCommutative H] (hle : diagonalTorus k n ≤ H) :
    H = diagonalTorus k n :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative centralizer_diagonalTorus hle

end IsLeftCancelMulZero

section FamilyCentralizer

variable [IsLeftCancelMulZero k] {X : Type*} {P : Subgroup (GL ι k)} {T : X → P}
  {f : X → ι → kˣ}

/-- **The centralizer of a family of diagonal elements.** Suppose `T` sends each `x` to an element
of a subgroup `P` of `GL ι k` whose matrix is diagonal with entries `f x`. An element of `P`
commutes with every `T x` exactly when its `(i, j)` entry vanishes whenever some `f x` takes
different values at `i` and `j`. -/
theorem mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL
    (hT : ∀ x, (T x : GL ι k) = diagGL (f x)) (g : P) :
    g ∈ Subgroup.centralizer (Set.range T) ↔
      ∀ i j, (∃ x, f x i ≠ f x j) → ((g : GL ι k) : Matrix ι ι k) i j = 0 := by
  constructor
  · rintro hg i j ⟨x, hx⟩
    have hcomm := congrArg (fun y : P ↦ ((y : GL ι k) : Matrix ι ι k))
      (Subgroup.mem_centralizer_iff.mp hg (T x) ⟨x, rfl⟩)
    simp only [Subgroup.coe_mul, Units.val_mul, hT, diagGL_coe] at hcomm
    exact apply_eq_zero_of_commute_diagonal hcomm fun h ↦ hx (Units.ext h)
  · intro hg
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hT, diagGL_coe]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : f x i = f x j
    · rw [hij, mul_comm]
    · rw [hg i j ⟨x, hij⟩, mul_zero, zero_mul]

/-- **An element centralizing a separating family of diagonal elements is diagonal.** If every
pair of distinct coordinates is separated by some `f x`, an element of `P` commutes with every
`T x` exactly when its matrix is diagonal. -/
theorem mem_centralizer_range_iff_isDiag_of_coe_eq_diagGL
    (hT : ∀ x, (T x : GL ι k) = diagGL (f x))
    (hf : Pairwise fun i j ↦ ∃ x, f x i ≠ f x j) (g : P) :
    g ∈ Subgroup.centralizer (Set.range T) ↔ ((g : GL ι k) : Matrix ι ι k).IsDiag := by
  rw [mem_centralizer_range_iff_apply_eq_zero_of_coe_eq_diagGL hT]
  refine ⟨fun h i j hij ↦ h i j (hf hij), fun h i j ⟨x, hx⟩ ↦ h ?_⟩
  rintro rfl
  exact hx rfl

end FamilyCentralizer

end CommSemiring

variable [CommRing k]

/-- The determinant of a diagonal matrix is the product of its diagonal entries. -/
@[simp]
theorem det_diagGL (t : ι → kˣ) :
    Matrix.GeneralLinearGroup.det (diagGL t) = ∏ i, t i := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]

/-- Mapping the entries of `diagGL t` along a ring homomorphism gives the diagonal matrix of the
mapped units. -/
@[simp]
theorem map_diagGL {S : Type*} [CommRing S] (f : k →+* S) (t : ι → kˣ) :
    Matrix.GeneralLinearGroup.map f (diagGL t) = diagGL fun i ↦ Units.map (f : k →* S) (t i) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, Units.coe_map,
    MonoidHom.coe_ofClass]
  split_ifs <;> simp

/-- Rescaling one column makes an invertible matrix have determinant one. For an empty index
type, every invertible matrix already has determinant one. -/
theorem exists_det_mul_diagGL_eq_one (P : GL ι k) :
    ∃ u : ι → kˣ, Matrix.GeneralLinearGroup.det (P * diagGL u) = 1 := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · exact ⟨1, Units.ext <| by simp [Matrix.GeneralLinearGroup.val_det_apply]⟩
  refine ⟨Pi.mulSingle i (Matrix.GeneralLinearGroup.det P)⁻¹, ?_⟩
  rw [map_mul, det_diagGL, Fintype.prod_pi_mulSingle' i, mul_inv_cancel]

/-- Rescale the first column of an invertible matrix by the inverse of its determinant. The
result has determinant one (`TauCeti.det_detOneRescale`), and the operation is the identity on
determinant-one matrices (`TauCeti.detOneRescale_of_det_eq_one`).

Unlike `TauCeti.exists_det_mul_diagGL_eq_one`, the rescaling is an explicit formula, so it
commutes with entrywise ring homomorphisms (`TauCeti.map_detOneRescale`): it is a morphism of
schemes `GLₙ → SLₙ`. In rank zero it is the identity. -/
def detOneRescale (g : GL (Fin n) k) : GL (Fin n) k :=
  g * diagGL fun i : Fin n ↦ if (i : ℕ) = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1

/-- The determinant-one rescaling multiplies on the right by the diagonal matrix
`diag((det g)⁻¹, 1, …, 1)`. -/
theorem detOneRescale_def (g : GL (Fin n) k) :
    detOneRescale g =
      g * diagGL fun i : Fin n ↦ if (i : ℕ) = 0 then (Matrix.GeneralLinearGroup.det g)⁻¹ else 1 :=
  (rfl)

/-- The determinant-one rescaling has determinant one. -/
@[simp]
theorem det_detOneRescale (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (detOneRescale g) = 1 := by
  rw [detOneRescale, map_mul, det_diagGL]
  cases n with
  | zero =>
    rw [Fin.prod_univ_zero, mul_one]
    exact Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply])
  | succ m =>
    rw [Fin.prod_univ_succ]
    simp

/-- The determinant-one rescaling fixes matrices of determinant one. -/
theorem detOneRescale_of_det_eq_one {g : GL (Fin n) k}
    (hg : Matrix.GeneralLinearGroup.det g = 1) : detOneRescale g = g := by
  rw [detOneRescale, hg, inv_one]
  simp

/-- The determinant-one rescaling commutes with mapping the entries along a ring
homomorphism. -/
theorem map_detOneRescale {S : Type*} [CommRing S] (f : k →+* S) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.map f (detOneRescale g) =
      detOneRescale (Matrix.GeneralLinearGroup.map f g) := by
  rw [detOneRescale, detOneRescale, map_mul, map_diagGL, Matrix.GeneralLinearGroup.map_det]
  congr 2
  funext i
  split_ifs <;> simp

/-- If `P` intertwines `M` with a diagonal matrix, there is an intertwining matrix of determinant
one, obtained in the nonempty case by rescaling one of the columns of `P`. -/
theorem exists_det_eq_one_mul_map_eq_map_mul_diagGL {Q : Type*} [CommRing Q]
    (f : k →+* Q) (M : GL ι Q) (P : GL ι k) (t : ι → Qˣ)
    (h : M * Matrix.GeneralLinearGroup.map f P =
      Matrix.GeneralLinearGroup.map f P * diagGL t) :
    ∃ P' : GL ι k, Matrix.GeneralLinearGroup.det P' = 1 ∧
      M * Matrix.GeneralLinearGroup.map f P' =
        Matrix.GeneralLinearGroup.map f P' * diagGL t := by
  obtain ⟨u, hu⟩ := exists_det_mul_diagGL_eq_one P
  have hcomm : Commute (diagGL t) (Matrix.GeneralLinearGroup.map f (diagGL u)) := by
    rw [map_diagGL]
    exact (Commute.all _ _).map diagGL
  refine ⟨P * diagGL u, hu, ?_⟩
  rw [map_mul, ← mul_assoc, h, mul_assoc, hcomm.eq, ← mul_assoc]

/-- The determinant of an element of the diagonal torus is the product of its diagonal entries. -/
theorem det_of_mem_diagonalTorus {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) :
    (Matrix.GeneralLinearGroup.det g : k) = ∏ i, (g : Matrix (Fin n) (Fin n) k) i i := by
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    ← (mem_diagonalTorus_iff.mp hg).diagonal_diag, Matrix.det_diagonal]
  simp [Matrix.diag]

end TauCeti
