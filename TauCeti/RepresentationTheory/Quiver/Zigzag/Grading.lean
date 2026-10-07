/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Graded.ExtendByZero
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.TwoSidedIdeal.Homogeneous
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basis

/-!
# The zigzag relations are homogeneous and the induced grading

Every zigzag relator of a simple graph is homogeneous for the path-length grading of the path
algebra of the doubled quiver: the two quadratic families sit in degree two, and each long
generator is a single path, homogeneous of its own length. Consequently both relation ideals of
`TauCeti.RepresentationTheory.Quiver.Zigzag.Relations` are homogeneous ideals.

Because the relation ideals are homogeneous, the generic descent
`TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient` applies to them: the relation quotient
carries the induced grading `TauCeti.zigzagGrade`, this file packages its graded-algebra
structure, and it computes the concrete pieces.

## Main definitions

* `TauCeti.zigzagGrade`: the induced degree-`n` piece on the relation quotient, the descent of
  `TauCeti.PathAlgebra.grade` along the quotient map.
* `TauCeti.zigzagIntegerGrade`: the same grading extended by zero to integer degrees.
* `TauCeti.zigzagGradedAlgebra`: **the zigzag relation quotient is a graded algebra** for the
  induced path-length grading.
* `TauCeti.zigzagIntegerGradedAlgebra`: the same graded-algebra structure after extension to
  integer degrees.

## Main results

* `TauCeti.DoubledQuiver.backtrackElem_mem_grade_two`: a backtrack has degree two.
* `TauCeti.IsZigzagRelator.isHomogeneousElem` and
  `TauCeti.IsQuadraticZigzagRelator.mem_grade_two`: the relators are homogeneous, the quadratic
  ones in degree two.
* `TauCeti.isHomogeneous_zigzagIdeal` and `TauCeti.isHomogeneous_quadraticZigzagIdeal`: **the
  relation ideals are homogeneous.**
* `TauCeti.mem_zigzagGrade_iff`: a graded piece consists of the classes of the homogeneous
  elements of its degree.
* `TauCeti.isInternal_zigzagGrade`: **the quotient is the internal direct sum of its graded
  pieces**, the comparison of the direct-sum graded algebra with the ungraded quotient asked for
  by the roadmap.
* `TauCeti.zigzagGrade_zero_eq_span_range_vertexIdempotent`,
  `TauCeti.zigzagGrade_one_eq_span_range_ofArrow` and
  `TauCeti.zigzagGrade_two_eq_span_range_zigzagVolume`: the concrete pieces, spanned by the
  vertex idempotent classes, the arrow classes, and the volume classes respectively.
* `TauCeti.zigzagGrade_eq_bot_of_three_le`: every piece of degree at least three vanishes.
* `TauCeti.isInternal_zigzagIntegerGrade`: the extension by zero to integer degrees is still an
  internal direct sum, so it is an integer grading of the quotient.
* `TauCeti.zigzagBasis_coord_dart_eq_zero_of_mem_zigzagIntegerGrade`: an arrow coordinate vanishes
  on every piece of degree other than one.

## References

This is the grading clause of Layer 0 of `TauCetiRoadmap/ZigzagPreprojective/README.md`, which
asks for the relation ideal to be homogeneous for the path-length grading and for the induced
nonnegative grading on the quotient to be compared with the ungraded quotient rather than
postulated as an unrelated graded copy. See Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3.
-/

public section

namespace TauCeti

open PathAlgebra

universe u w

/-- A backtrack element has degree two: it is the basis element of a single length-two path. -/
theorem DoubledQuiver.backtrackElem_mem_grade_two (k : Type w) [Semiring k] {V : Type u}
    (G : SimpleGraph V) {i j : V} (h : G.Adj i j) :
    DoubledQuiver.backtrackElem G k h ∈ grade k (DoubledQuiver G) 2 := by
  rw [DoubledQuiver.backtrackElem_eq_ofPath]
  exact ofPath_mem_grade_of_length (DoubledQuiver.length_backtrackPath G h)

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)

/-- **The quadratic zigzag relators sit in degree two**: a non-returning length-two path is a
single basis path of length two, and a difference of two length-two backtracks is a difference of
two such. -/
theorem IsQuadraticZigzagRelator.mem_grade_two {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsQuadraticZigzagRelator k G x) : x ∈ grade k (DoubledQuiver G) 2 := by
  cases hx with
  | nonreturn p hp _ => exact ofPath_mem_grade_of_length hp
  | equal_backtracks p q hp hq =>
    exact Submodule.sub_mem _ (ofPath_mem_grade_of_length hp) (ofPath_mem_grade_of_length hq)

/-- The quadratic zigzag relators are homogeneous. -/
theorem IsQuadraticZigzagRelator.isHomogeneousElem {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsQuadraticZigzagRelator k G x) :
    SetLike.IsHomogeneousElem (grade k (DoubledQuiver G)) x :=
  ⟨2, IsQuadraticZigzagRelator.mem_grade_two k G hx⟩

/-- **The uniform zigzag relators are homogeneous**: the quadratic ones in degree two, and each
long generator in the degree its own length names. -/
theorem IsZigzagRelator.isHomogeneousElem {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsZigzagRelator k G x) : SetLike.IsHomogeneousElem (grade k (DoubledQuiver G)) x := by
  cases hx with
  | quadratic h => exact IsQuadraticZigzagRelator.isHomogeneousElem k G h
  | long_path y _ => exact ⟨y.2.2.length, ofPath_mem_grade y⟩

variable [Finite V]

/-- **The quadratic relation ideal is homogeneous** for the path-length grading. -/
theorem isHomogeneous_quadraticZigzagIdeal :
    (quadraticZigzagIdeal k G).asIdeal.IsHomogeneous (grade k (DoubledQuiver G)) := by
  rw [quadraticZigzagIdeal_eq_span]
  exact TwoSidedIdeal.homogeneous_span _ fun _ hx =>
    IsQuadraticZigzagRelator.isHomogeneousElem k G hx

/-- **The uniform relation ideal is homogeneous** for the path-length grading. This is the
condition needed to descend the grading to the zigzag quotient. -/
theorem isHomogeneous_zigzagIdeal :
    (zigzagIdeal k G).asIdeal.IsHomogeneous (grade k (DoubledQuiver G)) := by
  rw [zigzagIdeal_eq_span]
  exact TwoSidedIdeal.homogeneous_span _ fun _ hx => IsZigzagRelator.isHomogeneousElem k G hx

/-! ### The induced grading on the relation quotient -/

open DoubledQuiver

/-- **The induced grading on the zigzag relation quotient**: the degree-`n` piece is the image of
the degree-`n` piece of the path-length grading of the path algebra of the doubled quiver under
the quotient map. Multiplication adds degrees for any relation ideal
(`TauCeti.GradedAlgebra.quotientPiece_mul_quotientPiece_le`); because the relation ideal is
homogeneous (`TauCeti.isHomogeneous_zigzagIdeal`), `TauCeti.isInternal_zigzagGrade` also holds,
comparing the direct sum of the pieces with the quotient itself rather than with a separate graded
copy. -/
noncomputable def zigzagGrade (n : ℕ) : Submodule k (nonisolatedZigzagQuotient k G) :=
  TauCeti.GradedAlgebra.quotientPiece (grade k (DoubledQuiver G)) (zigzagIdeal k G).asIdeal n

/-- A homogeneous element lands in the piece its degree names. -/
@[simp]
theorem zigzagMk_mem_zigzagGrade {n : ℕ} {y : pathAlgebra k (DoubledQuiver G)}
    (hy : y ∈ grade k (DoubledQuiver G) n) : zigzagMk k G y ∈ zigzagGrade k G n := by
  rw [zigzagGrade, zigzagMk_apply]
  exact TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _ hy

/-- Membership in a graded piece is being the class of a homogeneous element of that degree. -/
theorem mem_zigzagGrade_iff {n : ℕ} {x : nonisolatedZigzagQuotient k G} :
    x ∈ zigzagGrade k G n ↔ ∃ y ∈ grade k (DoubledQuiver G) n, zigzagMk k G y = x := by
  simp only [zigzagGrade, TauCeti.GradedAlgebra.mem_quotientPiece_iff, zigzagMk_apply]

/-- **The quotient is the internal direct sum of its graded pieces**: this is the comparison of
the direct-sum graded algebra with the ungraded quotient asked for by the roadmap, in the
internal sense in which the pieces are submodules of the quotient itself rather than a separate
graded copy. -/
theorem isInternal_zigzagGrade :
    DirectSum.IsInternal (zigzagGrade k G) :=
  TauCeti.GradedAlgebra.isInternal_quotientPiece (grade k (DoubledQuiver G))
    (zigzagIdeal k G).asIdeal (isHomogeneous_zigzagIdeal k G)

/-- Multiplication adds degrees in the induced grading: the product of a degree-`m` class and a
degree-`n` class lies in degree `m + n`. -/
theorem mul_mem_zigzagGrade {m n : ℕ} {x y : nonisolatedZigzagQuotient k G}
    (hx : x ∈ zigzagGrade k G m) (hy : y ∈ zigzagGrade k G n) :
    x * y ∈ zigzagGrade k G (m + n) :=
  TauCeti.GradedAlgebra.mul_mem_quotientPiece _ _ hx hy

/-- **The zigzag relation quotient is a graded algebra** for the induced path-length grading.
This is kept as a definition rather than an instance so that callers choose when to introduce it
locally; see `TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece`. -/
@[instance_reducible]
noncomputable def zigzagGradedAlgebra : GradedAlgebra (zigzagGrade k G) :=
  TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece (grade k (DoubledQuiver G))
    (zigzagIdeal k G).asIdeal (isHomogeneous_zigzagIdeal k G)

/-- **Degree zero is spanned by the vertex idempotent classes.** -/
theorem zigzagGrade_zero_eq_span_range_vertexIdempotent :
    zigzagGrade k G 0 =
      Submodule.span k
        (Set.range fun i : V => zigzagMk k G (vertexIdempotent k (vertex G i))) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine TauCeti.GradedAlgebra.mem_span_of_mem_quotientPiece
      (grade k (DoubledQuiver G)) (zigzagIdeal k G).asIdeal (i := 0)
      (PathAlgebra.grade_zero_eq_span_range_vertexIdempotent k (DoubledQuiver G)) ?_ hw
    rintro z ⟨v, rfl⟩
    rw [← zigzagMk_apply k G]
    exact Submodule.subset_span ⟨(vertexEquiv G).symm v, by simp⟩
  · rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.vertexIdempotent_mem_grade_zero _)

/-- **Degree one is spanned by the arrow classes**, one for each dart of the graph. -/
theorem zigzagGrade_one_eq_span_range_ofArrow :
    zigzagGrade k G 1 =
      Submodule.span k (Set.range fun d : G.Dart =>
        zigzagMk k G (ofArrow (arrow G d.adj))) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine TauCeti.GradedAlgebra.mem_span_of_mem_quotientPiece
      (grade k (DoubledQuiver G)) (zigzagIdeal k G).asIdeal (i := 1)
      (PathAlgebra.grade_one_eq_span_range_ofArrow) ?_ hw
    rintro z ⟨⟨a, b, e⟩, rfl⟩
    rw [← zigzagMk_apply k G]
    obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
      ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = vertex G j :=
      ⟨(vertexEquiv G).symm b, (vertexEquiv_symm_apply G b).symm⟩
    have hadj : G.Adj i j := (nonempty_hom_iff G).mp ⟨e⟩
    have heq : arrow G (⟨(i, j), hadj⟩ : G.Dart).adj = e := Subsingleton.elim _ _
    -- the spanning-family element is a beta-redex; reduce it to `zigzagMk k G (ofArrow e)`
    dsimp only
    exact Submodule.subset_span ⟨⟨(i, j), hadj⟩, by dsimp only; rw [heq]⟩
  · rw [Submodule.span_le]
    rintro e ⟨d, rfl⟩
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.ofArrow_mem_grade_one _)

/-- **Degree two is spanned by the volume classes**: every length-two path either does not return,
and dies, or returns to its source, and equals a backtrack there. -/
theorem zigzagGrade_two_eq_span_range_zigzagVolume :
    zigzagGrade k G 2 =
      Submodule.span k (Set.range fun i : V => zigzagVolume k G i) := by
  refine le_antisymm ?_ ?_
  · intro w hw
    refine TauCeti.GradedAlgebra.mem_span_of_mem_quotientPiece
      (grade k (DoubledQuiver G)) (zigzagIdeal k G).asIdeal (i := 2)
      (PathAlgebra.grade_eq_span_image_basis k (DoubledQuiver G) 2) ?_ hw
    rintro z ⟨t, ht, rfl⟩
    rw [← zigzagMk_apply k G]
    simp only [coe_pathAlgebraBasis]
    obtain ⟨a, b, p⟩ := t
    have ht' : p.length = 2 := ht
    obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
      ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
    rcases eq_or_ne b (vertex G i) with rfl | hne
    · obtain ⟨m, h, hp⟩ := exists_eq_backtrackPath G p ht'
      rw [hp, ← backtrackElem_eq_ofPath, zigzagMk_backtrackElem_eq_zigzagVolume]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [zigzagMk_ofPath_eq_zero_of_ne k G p ht' (Ne.symm hne)]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    -- membership in the spanned range only needs beta reduction here
    change zigzagVolume k G i ∈ zigzagGrade k G 2
    by_cases hi : ∃ j, G.Adj i j
    · obtain ⟨j, hj⟩ := hi
      rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj]
      exact zigzagMk_mem_zigzagGrade k G (backtrackElem_mem_grade_two k G hj)
    · have hiso : G.IsIsolated i := fun w hw => hi ⟨w, hw⟩
      rw [zigzagVolume_eq_zero_of_isIsolated k G hiso]
      exact Submodule.zero_mem _

/-- Every piece of degree at least three vanishes: all long paths are relations. -/
theorem zigzagGrade_eq_bot_of_three_le {n : ℕ} (hn : 3 ≤ n) : zigzagGrade k G n = ⊥ := by
  have hle : PathAlgebra.grade k (DoubledQuiver G) n ≤
      Submodule.restrictScalars k ((zigzagIdeal k G).asIdeal) := by
    rw [PathAlgebra.grade_eq_span_image_basis, Submodule.span_le]
    rintro z ⟨t, ht, rfl⟩
    have ht' : t.2.2.length = n := ht
    simp only [coe_pathAlgebraBasis]
    exact TwoSidedIdeal.mem_asIdeal.mpr
      (mem_zigzagIdeal_of_isZigzagRelator k G (IsZigzagRelator.long_path t (hn.trans ht'.symm.le)))
  refine TauCeti.GradedAlgebra.quotientPiece_eq_bot_of_le (grade k (DoubledQuiver G))
    (zigzagIdeal k G).asIdeal fun y hy => ?_
  exact hle hy

/-! ### Integer-indexed grading -/

/-- The path-length grading of the zigzag relation quotient, extended by zero from `ℕ` to `ℤ`.
This signed indexing is needed to state every internal grading shift. -/
noncomputable def zigzagIntegerGrade (d : ℤ) :
    Submodule k (nonisolatedZigzagQuotient k G) :=
  Graded.extendByZero (zigzagGrade k G) d

@[simp]
theorem zigzagIntegerGrade_ofNat (d : ℕ) :
    zigzagIntegerGrade k G d = zigzagGrade k G d :=
  Graded.extendByZero_natCast _ d

/-- The integer extension of the path-length grading vanishes in negative degrees. -/
theorem zigzagIntegerGrade_eq_bot_of_neg {d : ℤ} (hd : d < 0) :
    zigzagIntegerGrade k G d = ⊥ :=
  Graded.extendByZero_of_neg _ hd

/-- **The integer extension of the path-length grading is an internal direct sum**: the pieces
in nonnegative degrees are those of `TauCeti.zigzagGrade`, and those in negative degrees vanish. -/
theorem isInternal_zigzagIntegerGrade : DirectSum.IsInternal (zigzagIntegerGrade k G) :=
  Graded.isInternal_extendByZero (isInternal_zigzagGrade k G)

/-- **The zigzag relation quotient is an integer-graded algebra** for the path-length grading
indexed by `ℤ`, extended by zero in negative degrees. -/
@[instance_reducible]
noncomputable def zigzagIntegerGradedAlgebra : GradedAlgebra (zigzagIntegerGrade k G) :=
  let _ := zigzagGradedAlgebra k G
  { (isInternal_zigzagIntegerGrade k G).chooseDecomposition with
    one_mem := (zigzagIntegerGrade_ofNat k G 0).ge SetLike.GradedOne.one_mem
    mul_mem := fun _ _ _ _ hx hy ↦
      Graded.mul_mem_extendByZero (fun hx' hy' ↦ SetLike.GradedMul.mul_mem hx' hy') hx hy }

/-- **An arrow coordinate vanishes off degree one**: the pieces of degree other than one are
spanned by vertex idempotents and volume classes, which have no arrow component. -/
theorem zigzagBasis_coord_dart_eq_zero_of_mem_zigzagIntegerGrade (hns : ∀ i : V, ∃ j, G.Adj i j)
    (d : G.Dart) {e : ℤ} (he : e ≠ 1) {x : nonisolatedZigzagQuotient k G}
    (hx : x ∈ zigzagIntegerGrade k G e) :
    (zigzagBasis k G hns).coord (.inr (.inl d)) x = 0 := by
  classical
  suffices hle : zigzagIntegerGrade k G e ≤
      LinearMap.ker ((zigzagBasis k G hns).coord (.inr (.inl d))) from hle hx
  rcases lt_or_ge e 0 with h | h
  · simp [zigzagIntegerGrade_eq_bot_of_neg k G h]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
  rw [zigzagIntegerGrade_ofNat]
  match n, he with
  | 0, _ =>
    rw [zigzagGrade_zero_eq_span_range_vertexIdempotent, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [← zigzagBasisFun_inl, ← zigzagBasis_apply k G hns, zigzagBasis_coord_apply]
    simp
  | 1, he => exact absurd rfl he
  | 2, _ =>
    rw [zigzagGrade_two_eq_span_range_zigzagVolume, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [← zigzagBasisFun_inr_inr, ← zigzagBasis_apply k G hns, zigzagBasis_coord_apply]
    simp
  | n + 3, _ =>
    rw [zigzagGrade_eq_bot_of_three_le k G (by omega)]
    exact bot_le

/-- Multiplication adds signed degrees in the integer extension of the path-length grading. -/
theorem mul_mem_zigzagIntegerGrade {m n : ℤ}
    {x y : nonisolatedZigzagQuotient k G} (hx : x ∈ zigzagIntegerGrade k G m)
    (hy : y ∈ zigzagIntegerGrade k G n) : x * y ∈ zigzagIntegerGrade k G (m + n) :=
  Graded.mul_mem_extendByZero (mul_mem_zigzagGrade k G) hx hy

end TauCeti
