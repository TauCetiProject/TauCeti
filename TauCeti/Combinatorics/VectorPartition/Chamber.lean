/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.VectorPartition.Basic
public import TauCeti.Analysis.Convex.Polyhedron.SignCell.Basic
public import TauCeti.LinearAlgebra.Matrix.ColumnBasis
import TauCeti.Topology.Algebra.Module.AddSMul
import Mathlib.Topology.Baire.Lemmas

/-!
# Basis cones and chambers of vector partition functions

Let `A` be an integer matrix with rows indexed by `κ` and columns by `ι`, and let `e` be a column
basis of `A` (`Matrix.ColumnBasis`, in `TauCeti.LinearAlgebra.Matrix.ColumnBasis`). The basic
solution of `A *ᵥ x = b` for `e` is nonnegative exactly when `b` lies in the basis cone of `e`
(`Matrix.ColumnBasis.basicSolution_mem_partitionPolyhedron_iff`). If `A` has linearly independent
rows, Carathéodory's theorem shows that the basis cones cover the cone spanned by all columns
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

* `Matrix.chamberArrangement A`: the arrangement of all basis coordinates.
* `Matrix.Chamber A`: the chambers of `A`, as sets of vectors.

## Main results

* `Matrix.ColumnBasis.basicSolution_mem_partitionPolyhedron_iff`: the basic solution is feasible
  exactly on the basis cone.
* `Matrix.exists_mem_basisCone_iff`: the basis cones cover the column cone.
* `Matrix.Chamber.isConvexPolyhedron`, `Matrix.Chamber.nonempty_interior`: chambers are
  full-dimensional convex polyhedra.
* `Matrix.Chamber.subset_basisCone_or_disjoint_interior`: chambers refine the basis cones.
* `Matrix.iUnion_chamber`: the chambers cover the column cone.

## References

* B. Sturmfels, *On vector partition functions*, J. Combin. Theory Ser. A **72** (1995), 302–309.
* J. A. De Loera and B. Sturmfels, *Algebraic unimodular counting*, Math. Program. **96** (2003),
  183–203, §§1 and 3.
-/

public section

open Function TauCeti.Convex

namespace Matrix

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ]

namespace ColumnBasis

variable {A : Matrix κ ι ℤ} [Fintype ι]

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
  refine ⟨fun ⟨e, he⟩ => e.nonempty_partitionPolyhedron_of_mem_basisCone he, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨hx, hxb⟩ := mem_partitionPolyhedron.1 hx
  obtain ⟨e, z, hz, hzb⟩ := exists_columnBasis_submatrix_mulVec_eq_of_nonneg hA hx
  rw [hxb, ← e.basisCoordinates_eq_iff] at hzb
  exact ⟨e, e.mem_basisCone_iff.2 (hzb ▸ hz)⟩

/-! ### Chambers -/

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

/-- A chamber prescribes the sign `-1` or `1` to every basis coordinate. -/
theorem sign_eq_neg_one_or_eq_one (D : A.Chamber) (p : A.ColumnBasis × κ) :
    D.sign p = -1 ∨ D.sign p = 1 := by
  cases hs : D.sign p with
  | zero => exact absurd hs (D.sign_ne_zero p)
  | neg => exact Or.inl rfl
  | pos => exact Or.inr rfl

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
  rcases D.sign_eq_neg_one_or_eq_one (e, k) with hs | hs <;> simp [hs]

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
  have hneg : D.sign (e, k) = -1 := (D.sign_eq_neg_one_or_eq_one _).resolve_right hk
  rw [Set.disjoint_left]
  intro b hb hbe
  -- Moving from `b` along the column `e k` stays in the chamber for a short positive time, and
  -- makes the `k`-th coordinate of `e` positive.
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), b + t • e.basis k ∈ D :=
    (TauCeti.tendsto_add_smul_nhdsWithin_zero (Set.Ioi (0 : ℝ)) b (e.basis k)).eventually
      (mem_interior_iff_mem_nhds.1 hb)
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
  · refine mem_closure_of_tendsto
      (TauCeti.tendsto_add_smul_nhdsWithin_zero (Set.Ioi (0 : ℝ)) b (e.basis k)) ?_
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
    refine mem_closure_of_tendsto
      (TauCeti.tendsto_add_smul_nhdsWithin_zero (Set.Ioi (0 : ℝ)) b w) ?_
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
