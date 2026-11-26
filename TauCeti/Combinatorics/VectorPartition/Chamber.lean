/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.VectorPartition.Basic
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Basic
public import TauCeti.Geometry.Convex.Cone.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.Analysis.Convex.Cone.Caratheodory
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.MulVec
import TauCeti.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Baire.Lemmas

/-!
# Column bases and chambers of vector partition functions

Let `A` be an integer matrix with rows indexed by `κ` and columns by `ι`. A *column basis* of `A`
(`Matrix.ColumnBasis`) chooses a column `e k` for every row index `k` so that the square submatrix
`A_e` on these columns is invertible. Its columns form a basis of `κ → ℝ`
(`Matrix.ColumnBasis.basis`), the coordinates of `b` in this basis are `(A_e)⁻¹ *ᵥ b`
(`Matrix.ColumnBasis.basisCoordinates`), and putting them on the columns of `e` and `0` elsewhere
gives the *basic solution* of `A *ᵥ x = b` (`Matrix.ColumnBasis.basicSolution`), the only solution
supported on these columns. It is nonnegative exactly when `b` lies in the *basis cone* spanned by
the columns of `e` (`Matrix.ColumnBasis.basisCone`). When `A_e` has determinant `±1`, the basis
coordinates of integer vectors are integers. If `A` has linearly independent rows, Carathéodory's
theorem shows that the basis cones cover the cone spanned by all columns
(`Matrix.exists_mem_basisCone_iff`).

The *chamber arrangement* of `A` (`Matrix.chamberArrangement`) is the finite family of all basis
coordinates `b ↦ ((A_e)⁻¹ *ᵥ b) k`. A *chamber* (`Matrix.Chamber`) is the closure of a
full-dimensional cell of this arrangement lying in some basis cone. Chambers are recorded by their
sign patterns and are convex polyhedra with nonempty interior. They are the common refinement of the
basis cones: a chamber either lies in a basis cone or its interior misses it
(`Matrix.Chamber.subset_basisCone_or_disjoint_interior`). If `A` has linearly independent rows,
the chambers cover the cone spanned by the columns (`Matrix.iUnion_chamber`): a vector of this cone
is a limit of vectors of a basis cone avoiding every wall of the arrangement.

On the interior of a chamber, the column bases whose basic solution is nonnegative are therefore
the same for every right-hand side. This is the chamber decomposition on which, for unimodular
`A`, the vector partition function is a polynomial on each chamber (De Loera–Sturmfels,
Theorem 1.1).

## Main definitions

* `Matrix.ColumnBasis A`: the column bases of `A`.
* `Matrix.ColumnBasis.basisCoordinates`, `Matrix.ColumnBasis.basicSolution`,
  `Matrix.ColumnBasis.basisCone`: basis coordinates, basic solutions and basis cones.
* `Matrix.chamberArrangement A`: the arrangement of all basis coordinates.
* `Matrix.Chamber A`: the chambers of `A`, as sets of vectors.

## Main results

* `Matrix.ColumnBasis.eq_basicSolution_iff`: basic solutions are the solutions supported on a
  column basis.
* `Matrix.ColumnBasis.basicSolution_mem_partitionPolyhedron_iff`: the basic solution is feasible
  exactly on the basis cone.
* `Matrix.ColumnBasis.basisCoordinates_intCast_of_isUnit`: integral basis coordinates.
* `Matrix.exists_mem_basisCone_iff`: the basis cones cover the column cone.
* `Matrix.Chamber.isConvexPolyhedron`, `Matrix.Chamber.nonempty_interior`: chambers are
  full-dimensional convex polyhedra.
* `Matrix.Chamber.subset_basisCone_or_disjoint_interior`: chambers refine the basis cones.
* `Matrix.iUnion_chamber`: the chambers cover the column cone.

## References

* B. Sturmfels, *On vector partition functions*, J. Combin. Theory Ser. A **72** (1995), 302–309.
* J. A. De Loera and B. Sturmfels, *Algebraic unimodular counting*, Math. Program. **96** (2003),
  183–203, §§1 and 3.
* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley, 1986, §8.5 (basic solutions).
-/

public section

open Function TauCeti.Convex

namespace Matrix

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ]

/-- A *column basis* of an integer matrix `A` with rows indexed by `κ`: a choice of a column
`e k` of `A` for every row index `k` such that the square submatrix of `A` on these columns has
nonzero determinant. Its columns form a basis of `κ → ℝ`. The columns are listed in the order
given by `κ`, so each set of columns forming a basis is presented by `Fintype.card κ !` column
bases. -/
@[ext]
structure ColumnBasis (A : Matrix κ ι ℤ) where
  /-- The column chosen for each row index. -/
  toFun : κ → ι
  det_ne_zero : (A.submatrix id toFun).det ≠ 0

namespace ColumnBasis

variable {A : Matrix κ ι ℤ}

instance : FunLike A.ColumnBasis κ ι where
  coe := toFun
  coe_injective _ _ := ColumnBasis.ext

@[simp] theorem toFun_eq_coe (e : A.ColumnBasis) : e.toFun = ⇑e := (rfl)

theorem det_submatrix_ne_zero (e : A.ColumnBasis) : (A.submatrix id e).det ≠ 0 := e.det_ne_zero

instance [Finite ι] : Finite A.ColumnBasis :=
  Finite.of_injective _ DFunLike.coe_injective

/-- The columns of a column basis are distinct. -/
theorem injective (e : A.ColumnBasis) : Injective e := by
  intro k l hkl
  by_contra hne
  exact e.det_submatrix_ne_zero (det_zero_of_column_eq hne fun i => by simp [hkl])

/-- The real square matrix of a column basis is invertible. -/
theorem isUnit_det_map (e : A.ColumnBasis) :
    IsUnit ((A.map (Int.cast : ℤ → ℝ)).submatrix id e).det := by
  rw [submatrix_map]
  exact isUnit_det_map_intCast e.det_submatrix_ne_zero

/-- The coordinates of a real vector `b` in the basis of `κ → ℝ` formed by the columns of a column
basis `e`: the unique `t` with `∑ k, t k • A.col (e k) = b`, given by Cramer's rule as
`(A_e)⁻¹ *ᵥ b` for the square submatrix `A_e` of `A` on the columns of `e`. -/
noncomputable def basisCoordinates (e : A.ColumnBasis) (b : κ → ℝ) : κ → ℝ :=
  ((A.map (Int.cast : ℤ → ℝ)).submatrix id e)⁻¹ *ᵥ b

theorem basisCoordinates_def (e : A.ColumnBasis) (b : κ → ℝ) :
    e.basisCoordinates b = ((A.map (Int.cast : ℤ → ℝ)).submatrix id e)⁻¹ *ᵥ b := (rfl)

/-- The basis coordinates of `b` recombine the columns of the basis to `b`. -/
@[simp] theorem submatrix_mulVec_basisCoordinates (e : A.ColumnBasis) (b : κ → ℝ) :
    (A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ e.basisCoordinates b = b := by
  rw [basisCoordinates_def, mulVec_mulVec, mul_nonsing_inv _ e.isUnit_det_map, one_mulVec]

/-- The basis coordinates of a combination of the columns of the basis are its coefficients. -/
@[simp] theorem basisCoordinates_submatrix_mulVec (e : A.ColumnBasis) (t : κ → ℝ) :
    e.basisCoordinates ((A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ t) = t := by
  rw [basisCoordinates_def, mulVec_mulVec, nonsing_inv_mul _ e.isUnit_det_map, one_mulVec]

/-- The basis coordinates of `b` are the unique coefficients recombining the columns to `b`. -/
theorem basisCoordinates_eq_iff (e : A.ColumnBasis) {b t : κ → ℝ} :
    e.basisCoordinates b = t ↔ (A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ t = b := by
  constructor
  · rintro rfl
    exact e.submatrix_mulVec_basisCoordinates b
  · rintro rfl
    exact e.basisCoordinates_submatrix_mulVec t

@[simp] theorem basisCoordinates_add (e : A.ColumnBasis) (b b' : κ → ℝ) :
    e.basisCoordinates (b + b') = e.basisCoordinates b + e.basisCoordinates b' :=
  mulVec_add _ _ _

@[simp] theorem basisCoordinates_smul (e : A.ColumnBasis) (c : ℝ) (b : κ → ℝ) :
    e.basisCoordinates (c • b) = c • e.basisCoordinates b :=
  mulVec_smul _ _ _

/-- **Integral basis coordinates.** If the square submatrix of a column basis has determinant `±1`,
the basis coordinates of an integer vector are the integers given by the integer inverse
matrix. -/
theorem basisCoordinates_intCast_of_isUnit (e : A.ColumnBasis)
    (he : IsUnit (A.submatrix id e).det) (b : κ → ℤ) :
    e.basisCoordinates (fun i => (b i : ℝ)) = fun k => (((A.submatrix id e)⁻¹ *ᵥ b) k : ℝ) := by
  have h1 : (A.submatrix id e).map (Int.castRingHom ℝ) *
      (A.submatrix id e)⁻¹.map (Int.castRingHom ℝ) = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ he, Matrix.map_one _ (map_zero _) (map_one _)]
  simp only [Int.coe_castRingHom] at h1
  rw [basisCoordinates_eq_iff, submatrix_map, ← map_intCast_mulVec, mulVec_mulVec, h1, one_mulVec]

/-- The *basic solution* of a column basis `e` for the right-hand side `b`: the vector with the
basis coordinates of `b` on the columns of `e` and `0` on all other columns. -/
noncomputable def basicSolution (e : A.ColumnBasis) (b : κ → ℝ) : ι → ℝ :=
  extend e (e.basisCoordinates b) 0

@[simp] theorem basicSolution_apply_self (e : A.ColumnBasis) (b : κ → ℝ) (k : κ) :
    e.basicSolution b (e k) = e.basisCoordinates b k :=
  e.injective.extend_apply _ _ k

theorem basicSolution_apply_of_notMem_range (e : A.ColumnBasis) (b : κ → ℝ) {j : ι}
    (hj : j ∉ Set.range e) : e.basicSolution b j = 0 :=
  extend_apply' _ _ _ hj

/-- The columns of a column basis, as a basis of `κ → ℝ`; the coordinates of a vector in this basis
are its basis coordinates. -/
noncomputable def basis (e : A.ColumnBasis) : Module.Basis κ ℝ (κ → ℝ) :=
  .ofEquivFun
    { toFun := e.basisCoordinates
      invFun := ((A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ ·)
      map_add' := e.basisCoordinates_add
      map_smul' := e.basisCoordinates_smul
      left_inv := e.submatrix_mulVec_basisCoordinates
      right_inv := e.basisCoordinates_submatrix_mulVec }

theorem basis_apply (e : A.ColumnBasis) (k : κ) :
    e.basis k = fun i => (A i (e k) : ℝ) := by
  simp only [basis, Module.Basis.coe_ofEquivFun, LinearEquiv.coe_symm_mk', mulVec_single_one]
  rfl

@[simp] theorem basis_repr_apply (e : A.ColumnBasis) (b : κ → ℝ) (k : κ) :
    e.basis.repr b k = e.basisCoordinates b k := by
  simp [basis]

/-- The basis coordinates of the column `e k` are those of the `k`-th standard basis vector. -/
@[simp] theorem basisCoordinates_basis (e : A.ColumnBasis) (k : κ) :
    e.basisCoordinates (e.basis k) = Pi.single k 1 := by
  ext l
  rw [← basis_repr_apply, e.basis.repr_self]
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The *basis cone* of a column basis: the cone spanned by its columns. -/
noncomputable def basisCone (e : A.ColumnBasis) : PointedCone ℝ (κ → ℝ) :=
  PointedCone.hull ℝ (Set.range fun k i => (A i (e k) : ℝ))

/-- A vector lies in the basis cone of `e` exactly when its basis coordinates are nonnegative. -/
theorem mem_basisCone_iff (e : A.ColumnBasis) {b : κ → ℝ} :
    b ∈ e.basisCone ↔ 0 ≤ e.basisCoordinates b := by
  have hb : ⇑e.basis = fun k i => (A i (e k) : ℝ) := funext e.basis_apply
  rw [basisCone, ← hb, e.basis.mem_pointedCone_hull_range_iff, Pi.le_def]
  simp

variable [Fintype ι]

/-- A vector supported on the columns of `e` is mapped by `A` as its restriction to these columns is
mapped by the square submatrix. -/
private theorem mulVec_eq_submatrix_mulVec_comp (e : A.ColumnBasis) {x : ι → ℝ}
    (hx : ∀ j ∉ Set.range e, x j = 0) :
    A.map (Int.cast : ℤ → ℝ) *ᵥ x = (A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ (x ∘ e) := by
  funext i
  simp only [mulVec, dotProduct, submatrix_apply, id_eq]
  exact (Fintype.sum_of_injective e e.injective _ _ (fun j hj => by simp [hx j hj])
    fun k => rfl).symm

/-- The basic solution of `e` for `b` solves `A *ᵥ x = b`. -/
@[simp] theorem mulVec_basicSolution (e : A.ColumnBasis) (b : κ → ℝ) :
    A.map (Int.cast : ℤ → ℝ) *ᵥ e.basicSolution b = b := by
  rw [mulVec_eq_submatrix_mulVec_comp e fun j hj => e.basicSolution_apply_of_notMem_range b hj]
  convert e.submatrix_mulVec_basisCoordinates b using 2
  funext k
  simp

/-- The basic solution of `e` for `b` is the only solution of `A *ᵥ x = b` supported on the columns
of `e`. -/
theorem eq_basicSolution_iff (e : A.ColumnBasis) {b : κ → ℝ} {x : ι → ℝ}
    (hx : ∀ j ∉ Set.range e, x j = 0) :
    x = e.basicSolution b ↔ A.map (Int.cast : ℤ → ℝ) *ᵥ x = b := by
  refine ⟨fun h => h ▸ e.mulVec_basicSolution b, fun h => funext fun j => ?_⟩
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k, rfl⟩ := hj
    rw [basicSolution_apply_self]
    rw [mulVec_eq_submatrix_mulVec_comp e hx, ← basisCoordinates_eq_iff] at h
    exact congrFun h.symm k
  · rw [hx j hj, e.basicSolution_apply_of_notMem_range b hj]

/-- The basic solution of `e` for `b` lies in the partition polyhedron of `b` exactly when `b` lies
in the basis cone of `e`. -/
theorem basicSolution_mem_partitionPolyhedron_iff (e : A.ColumnBasis) {b : κ → ℝ} :
    e.basicSolution b ∈ A.partitionPolyhedron b ↔ b ∈ e.basisCone := by
  rw [mem_partitionPolyhedron, e.mem_basisCone_iff, and_iff_left (e.mulVec_basicSolution b)]
  refine ⟨fun h k => by simpa using h (e k), fun h j => ?_⟩
  by_cases hj : j ∈ Set.range e
  · obtain ⟨k, rfl⟩ := hj
    simpa using h k
  · simp [e.basicSolution_apply_of_notMem_range b hj]

/-- Every vector of a basis cone lies in the cone spanned by all columns. -/
theorem nonempty_partitionPolyhedron_of_mem_basisCone (e : A.ColumnBasis) {b : κ → ℝ}
    (hb : b ∈ e.basisCone) : (A.partitionPolyhedron b).Nonempty :=
  ⟨_, e.basicSolution_mem_partitionPolyhedron_iff.2 hb⟩

end ColumnBasis

/-- **Basic solutions.** If `A` has linearly independent rows, the cone spanned by its columns is
the union of the basis cones of its column bases: whenever `A *ᵥ x = b` has a nonnegative solution,
some basic solution is nonnegative. -/
theorem exists_mem_basisCone_iff [Fintype ι] {A : Matrix κ ι ℤ} (hA : LinearIndependent ℤ A.row)
    {b : κ → ℝ} : (∃ e : A.ColumnBasis, b ∈ e.basisCone) ↔ (A.partitionPolyhedron b).Nonempty := by
  classical
  refine ⟨fun ⟨e, he⟩ => e.nonempty_partitionPolyhedron_of_mem_basisCone he, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨hx, hxb⟩ := mem_partitionPolyhedron.1 hx
  -- A nonnegative solution with linearly independent support, by Carathéodory's theorem.
  obtain ⟨y, hy, -, hsum, hli⟩ :=
    TauCeti.exists_nonneg_sum_smul_eq_and_linearIndepOn (A.map (Int.cast : ℤ → ℝ)).col hx
  have hyb : A.map (Int.cast : ℤ → ℝ) *ᵥ y = b := by
    rw [← hxb]
    simpa only [mulVec_eq_sum, op_smul_eq_smul, col_def] using hsum
  have hrow : LinearIndependent ℝ (A.map (Int.cast : ℤ → ℝ)).row := by
    simpa using (linearIndependent_map_algebraMap_row_iff (S := ℝ)).2 hA
  -- Its support extends to a column basis `e`, whose basic solution it is.
  obtain ⟨f, hyf, hdet⟩ := exists_det_submatrix_ne_zero_of_linearIndepOn hrow hli
  let e : A.ColumnBasis := ⟨f, det_submatrix_ne_zero_of_map (Int.castRingHom ℝ) hdet⟩
  have hye : y = e.basicSolution b :=
    (e.eq_basicSolution_iff fun j hj => by_contra fun hyj => hj (hyf hyj)).2 hyb
  exact ⟨e, e.basicSolution_mem_partitionPolyhedron_iff.1
    (hye ▸ mem_partitionPolyhedron.2 ⟨hy, hyb⟩)⟩

/-! ### Chambers -/

omit [Fintype κ] [DecidableEq κ] in
/-- Moving from `b` in the direction `w` for a short positive time stays close to `b`. -/
private theorem tendsto_add_smul_nhdsGT (b w : κ → ℝ) :
    Filter.Tendsto (fun t : ℝ => b + t • w) (nhdsWithin 0 (Set.Ioi 0)) (nhds b) :=
  tendsto_nhdsWithin_of_tendsto_nhds <| by
    have hcont : Continuous fun t : ℝ => b + t • w := by fun_prop
    simpa using hcont.tendsto 0

/-- The *chamber arrangement* of `A`: the family of all basis coordinates `b ↦ (A_e)⁻¹ *ᵥ b`,
indexed by a column basis `e` and a row index `k`, as continuous affine functions of `b`. The
signs of these functions cut `κ → ℝ` into cells, whose full-dimensional members inside the column
cone are the chambers of `A`. -/
noncomputable def chamberArrangement (A : Matrix κ ι ℤ) (p : A.ColumnBasis × κ) :
    (κ → ℝ) →ᴬ[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap ((LinearMap.proj p.2).comp
    ((A.map (Int.cast : ℤ → ℝ)).submatrix id p.1)⁻¹.mulVecLin)).toContinuousAffineMap

@[simp] theorem chamberArrangement_apply (A : Matrix κ ι ℤ) (p : A.ColumnBasis × κ) (b : κ → ℝ) :
    A.chamberArrangement p b = p.1.basisCoordinates b p.2 := (rfl)

/-- A *chamber* of the integer matrix `A`: a full-dimensional cell of the chamber arrangement
inside the cone spanned by the columns of `A`. It is recorded by its sign pattern `sign`, which
prescribes no zero sign, is realized by some vector, and is positive on all coordinates of some
column basis. As a set (`Matrix.Chamber.coe_def`) the chamber is closed: it consists of the
vectors whose basis coordinates have the weak signs prescribed by `sign`. -/
@[ext]
structure Chamber (A : Matrix κ ι ℤ) where
  /-- The sign of each basis coordinate on the interior of the chamber. -/
  sign : A.ColumnBasis × κ → SignType
  sign_ne_zero : ∀ p, sign p ≠ 0
  nonempty_signCell : (signCell A.chamberArrangement sign).Nonempty
  exists_forall_sign_eq_one : ∃ e, ∀ k, sign (e, k) = 1

namespace Chamber

variable {A : Matrix κ ι ℤ}

/-- The open cell of a chamber is open. -/
theorem isOpen_signCell [Finite ι] (D : A.Chamber) :
    IsOpen (signCell A.chamberArrangement D.sign) :=
  TauCeti.Convex.isOpen_signCell D.sign_ne_zero

/-- The closed chamber is the closure of the cell of its sign pattern. -/
theorem closure_signCell (D : A.Chamber) :
    closure (signCell A.chamberArrangement D.sign) = weakSignCell A.chamberArrangement D.sign :=
  TauCeti.Convex.closure_signCell D.nonempty_signCell

/-- Distinct chambers have distinct closed cells, since their open cells are disjoint. -/
theorem weakSignCell_injective [Finite ι] :
    Injective fun D : A.Chamber => weakSignCell A.chamberArrangement D.sign := by
  intro D D' h
  replace h : weakSignCell A.chamberArrangement D.sign =
    weakSignCell A.chamberArrangement D'.sign := h
  by_contra hne
  have hσ : D.sign ≠ D'.sign := fun h' => hne (Chamber.ext h')
  obtain ⟨x, hx⟩ := D.nonempty_signCell
  have hx' : x ∈ closure (signCell A.chamberArrangement D'.sign) := by
    rw [D'.closure_signCell]
    exact h ▸ signCell_subset_weakSignCell _ _ hx
  obtain ⟨y, hy, hy'⟩ :=
    mem_closure_iff.1 hx' _ D.isOpen_signCell hx
  exact Set.disjoint_left.1 (signCell_disjoint hσ) hy hy'

noncomputable instance [Finite ι] : SetLike A.Chamber (κ → ℝ) where
  coe D := weakSignCell A.chamberArrangement D.sign
  coe_injective := weakSignCell_injective

theorem coe_def [Finite ι] (D : A.Chamber) :
    (D : Set (κ → ℝ)) = weakSignCell A.chamberArrangement D.sign := (rfl)

/-- A vector lies in a chamber exactly when each of its basis coordinates is nonnegative where the
chamber prescribes the sign `1` and nonpositive where it prescribes `-1`. -/
theorem mem_iff [Finite ι] (D : A.Chamber) {b : κ → ℝ} :
    b ∈ D ↔ ∀ e k, (D.sign (e, k) = 1 → 0 ≤ e.basisCoordinates b k) ∧
      (D.sign (e, k) = -1 → e.basisCoordinates b k ≤ 0) := by
  rw [← SetLike.mem_coe, coe_def, mem_weakSignCell, Prod.forall]
  refine forall₂_congr fun e k => ?_
  simp only [chamberArrangement_apply]
  cases hs : D.sign (e, k) with
  | zero => exact absurd hs (D.sign_ne_zero _)
  | neg => simp
  | pos => simp

/-- The open cell of a chamber lies in the chamber. -/
theorem signCell_subset [Finite ι] (D : A.Chamber) :
    signCell A.chamberArrangement D.sign ⊆ D :=
  signCell_subset_weakSignCell _ _

instance [Finite ι] : Finite A.Chamber :=
  Finite.of_injective _ fun _ _ => Chamber.ext

/-- Every chamber is a convex polyhedron. -/
theorem isConvexPolyhedron [Finite ι] (D : A.Chamber) :
    TauCeti.IsConvexPolyhedron (D : Set (κ → ℝ)) :=
  isConvexPolyhedron_weakSignCell _ _

/-- Every chamber is full-dimensional: it has nonempty interior. -/
theorem nonempty_interior [Finite ι] (D : A.Chamber) : (interior (D : Set (κ → ℝ))).Nonempty :=
  D.nonempty_signCell.mono (interior_maximal D.signCell_subset D.isOpen_signCell)

/-- A chamber lies in the basis cone of every column basis whose coordinates it prescribes to be
positive. -/
theorem subset_basisCone [Finite ι] (D : A.Chamber) {e : A.ColumnBasis}
    (he : ∀ k, D.sign (e, k) = 1) : (D : Set (κ → ℝ)) ⊆ e.basisCone := fun _ hb =>
  e.mem_basisCone_iff.2 fun k => ((D.mem_iff.1 hb e k).1 (he k))

/-- Every chamber lies in the basis cone of some column basis. -/
theorem exists_subset_basisCone [Finite ι] (D : A.Chamber) :
    ∃ e : A.ColumnBasis, (D : Set (κ → ℝ)) ⊆ e.basisCone :=
  D.exists_forall_sign_eq_one.imp fun _ he => D.subset_basisCone he

/-- Every chamber lies in the cone spanned by the columns of `A`. -/
theorem nonempty_partitionPolyhedron [Fintype ι] (D : A.Chamber) {b : κ → ℝ} (hb : b ∈ D) :
    (A.partitionPolyhedron b).Nonempty := by
  obtain ⟨e, he⟩ := D.exists_subset_basisCone
  exact e.nonempty_partitionPolyhedron_of_mem_basisCone (he hb)

/-- **The chambers refine the basis cones.** A chamber either lies in the basis cone of a column
basis `e`, or its interior is disjoint from that cone, which it then meets only along the wall
where some coordinate of `e` vanishes. -/
theorem subset_basisCone_or_disjoint_interior [Finite ι] (D : A.Chamber) (e : A.ColumnBasis) :
    (D : Set (κ → ℝ)) ⊆ e.basisCone ∨ Disjoint (interior (D : Set (κ → ℝ))) e.basisCone := by
  by_cases he : ∀ k, D.sign (e, k) = 1
  · exact Or.inl (D.subset_basisCone he)
  right
  obtain ⟨k, hk⟩ := not_forall.1 he
  have hneg : D.sign (e, k) = -1 := by
    cases hs : D.sign (e, k) with
    | zero => exact absurd hs (D.sign_ne_zero _)
    | neg => rfl
    | pos => exact absurd hs hk
  rw [Set.disjoint_left]
  intro b hb hbe
  -- Moving from `b` along the column `e k` stays in the chamber for a short positive time, and
  -- makes the `k`-th coordinate of `e` positive.
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), b + t • e.basis k ∈ D :=
    (tendsto_add_smul_nhdsGT b (e.basis k)).eventually (mem_interior_iff_mem_nhds.1 hb)
  obtain ⟨t, ht, htD⟩ := (hev.and self_mem_nhdsWithin).exists
  have h1 := (D.mem_iff.1 ht e k).2 hneg
  have h2 : 0 ≤ e.basisCoordinates b k := e.mem_basisCone_iff.1 hbe k
  simp only [ColumnBasis.basisCoordinates_add, ColumnBasis.basisCoordinates_smul,
    ColumnBasis.basisCoordinates_basis, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
    smul_eq_mul, mul_one] at h1
  exact (Set.mem_Ioi.1 htD).not_ge (by linarith)

end Chamber

/-- The vectors at which a given basis coordinate does not vanish are dense. -/
private theorem dense_setOf_basisCoordinates_ne_zero {A : Matrix κ ι ℤ} (e : A.ColumnBasis)
    (k : κ) : Dense {b : κ → ℝ | e.basisCoordinates b k ≠ 0} := by
  intro b
  by_cases hb : e.basisCoordinates b k = 0
  · refine mem_closure_of_tendsto (tendsto_add_smul_nhdsGT b (e.basis k)) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [ColumnBasis.basisCoordinates_add, ColumnBasis.basisCoordinates_smul, hb,
      (Set.mem_Ioi.1 ht).ne']
  · exact subset_closure hb

/-- **The chambers cover the column cone.** If `A` has linearly independent rows, every vector of
the cone spanned by the columns of `A` lies in some chamber, and the chambers lie in that cone. -/
theorem iUnion_chamber [Fintype ι] {A : Matrix κ ι ℤ} (hA : LinearIndependent ℤ A.row) :
    ⋃ D : A.Chamber, (D : Set (κ → ℝ)) = {b | (A.partitionPolyhedron b).Nonempty} := by
  refine Set.Subset.antisymm
    (Set.iUnion_subset fun D _ hb => D.nonempty_partitionPolyhedron hb) fun b hb => ?_
  obtain ⟨e, he⟩ := (exists_mem_basisCone_iff hA).2 hb
  -- `U` is the interior of the basis cone of `e`, and `G` the complement of all walls.
  set U := {y : κ → ℝ | ∀ k, 0 < e.basisCoordinates y k}
  set G := ⋂ p : A.ColumnBasis × κ, {y : κ → ℝ | p.1.basisCoordinates y p.2 ≠ 0}
  have hU : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt continuous_const (A.chamberArrangement (e, k)).continuous
  have hG : Dense G := by
    simp only [G, ← Set.sInter_range]
    exact (Set.finite_range _).dense_sInter
      (Set.forall_mem_range.2 fun p =>
        isOpen_ne_fun (A.chamberArrangement p).continuous continuous_const)
      (Set.forall_mem_range.2 fun p => dense_setOf_basisCoordinates_ne_zero p.1 p.2)
  -- `b` is a limit of points of `U`, moving into the basis cone along `∑ k, A.col (e k)`.
  have hbU : b ∈ closure U := by
    set w := (A.map (Int.cast : ℤ → ℝ)).submatrix id e *ᵥ fun _ => 1
    refine mem_closure_of_tendsto (tendsto_add_smul_nhdsGT b w) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht k
    have := e.mem_basisCone_iff.1 he k
    simp only [ColumnBasis.basisCoordinates_add, ColumnBasis.basisCoordinates_smul, w,
      ColumnBasis.basisCoordinates_submatrix_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mul_one, Pi.zero_apply] at this ⊢
    linarith [Set.mem_Ioi.1 ht]
  -- Every point of `U ∩ G` lies in the open cell of a chamber.
  have hsub : U ∩ G ⊆ ⋃ D : A.Chamber, (D : Set (κ → ℝ)) := by
    rintro y ⟨hyU, hyG⟩
    let D : A.Chamber :=
      { sign := fun p => SignType.sign (A.chamberArrangement p y)
        sign_ne_zero := fun p => by simpa using Set.mem_iInter.1 hyG p
        nonempty_signCell := ⟨y, mem_signCell.2 fun _ => rfl⟩
        exists_forall_sign_eq_one := ⟨e, fun k => sign_eq_one_iff.2 (hyU k)⟩ }
    exact Set.mem_iUnion.2 ⟨D, D.signCell_subset (mem_signCell.2 fun _ => rfl)⟩
  have hclosed : IsClosed (⋃ D : A.Chamber, (D : Set (κ → ℝ))) :=
    isClosed_iUnion_of_finite fun _ => isClosed_weakSignCell _ _
  have hUG : closure U ⊆ closure (U ∩ G) :=
    closure_minimal (hG.open_subset_closure_inter hU) isClosed_closure
  exact closure_minimal hsub hclosed (hUG hbU)

end Matrix
