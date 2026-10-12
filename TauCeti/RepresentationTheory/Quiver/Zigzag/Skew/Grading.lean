/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Cohomology
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Grading
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Isomorphism

/-!
# The path-length grading of a skew-zigzag relation quotient

Every skew-zigzag relator of a simple graph is homogeneous for the path-length grading of the path
algebra of the doubled quiver: a non-returning length-two path and the scalar relation
`backtrack(h) - ratio(h, h') • backtrack(h')` between two backtracks at one vertex sit in degree
two, and each long generator is a single path. So the skew relation ideal is homogeneous, and the
skew-zigzag relation quotient `Z_k(G, c)` carries the induced grading, in which the vertex
idempotents have degree `0`, the arrows degree `1`, and the backtracks degree `2`.

The comparison isomorphisms between skew-zigzag quotients are graded: the gauge isomorphism
rescales arrows, the relabelling along a graph isomorphism preserves path length, and the
comparison of the constant parameter with the ordinary zigzag relation quotient is the identity on
representatives. Consequently the vertex-fixing classification from Couture's setting extends here
to finite graphs over commutative rings, with **vertex-fixing graded isomorphisms**: two parameters
are gauge equivalent, equivalently have the same class in `H¹(G, kˣ)`, exactly when their relation
quotients are isomorphic by a graded isomorphism fixing every vertex idempotent. A graded
isomorphism `φ : Z_k(G, c) ≃ₐ[k] Z_k(G, c')` is spelled out as an algebra isomorphism such that
`φ x` lies in the degree-`n` piece of `Z_k(G, c')` exactly when `x` lies in the degree-`n` piece of
`Z_k(G, c)`, for every `n`.

## Main definitions

* `TauCeti.skewZigzagGrade`: the induced degree-`n` piece of the skew-zigzag relation quotient,
  the descent of `TauCeti.PathAlgebra.grade` along `TauCeti.skewZigzagMk`.
* `TauCeti.skewZigzagGradedAlgebra`: **the skew-zigzag relation quotient is a graded algebra** for
  the induced path-length grading.

## Main results

* `TauCeti.isHomogeneous_skewZigzagIdeal`: **the skew relation ideal is homogeneous.**
* `TauCeti.isInternal_skewZigzagGrade`: the quotient is the internal direct sum of its graded
  pieces.
* `TauCeti.skewZigzagGrade_zero_eq_span_range_vertexIdempotent`,
  `TauCeti.skewZigzagGrade_one_eq_span_range_ofArrow`,
  `TauCeti.skewZigzagGrade_two_eq_span_range_backtrackElem` and
  `TauCeti.skewZigzagGrade_eq_bot_of_three_le`: the pieces are spanned by the vertex idempotents,
  the arrows, and the backtracks, and vanish from degree three on.
* `TauCeti.skewZigzagQuotientGaugeEquiv_mem_skewZigzagGrade_iff`,
  `TauCeti.skewZigzagQuotientEquiv_mem_skewZigzagGrade_iff` and
  `TauCeti.skewZigzagQuotientOneEquiv_mem_zigzagGrade_iff`: the gauge, relabelling and
  constant-parameter isomorphisms are graded.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_iff_exists_graded_vertexFixing_algEquiv` and
  `TauCeti.SkewZigzagParameter.cohomologyClass_eq_iff_exists_graded_vertexFixing_algEquiv`:
  **the vertex-fixing graded isomorphism classes are the gauge classes, and hence the classes in
  `H¹(G, kˣ)`.**

## References

C. Couture, *Skew-Zigzag Algebras*, Section 3 for the grading and Section 4, Theorem 4.8, for
the vertex-fixing classification of connected graphs over fields containing square roots,
https://arxiv.org/abs/1509.08405. The graded classification here extends that result to finite
graphs over commutative rings.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u v w

/-! ### Homogeneity of the skew relators -/

section Homogeneous

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) (c : SkewZigzagParameter k G)

/-- **The skew-zigzag relators are homogeneous**: the non-returning quadratic paths and the scalar
backtrack relators in degree two, and each long generator in the degree its own length names. -/
theorem IsSkewZigzagRelator.isHomogeneousElem {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsSkewZigzagRelator k G c x) :
    SetLike.IsHomogeneousElem (grade k (DoubledQuiver G)) x := by
  cases hx with
  | nonreturn p hp _ => exact ⟨2, ofPath_mem_grade_of_length hp⟩
  | backtrack_ratio h h' =>
    exact ⟨2, Submodule.sub_mem _ (backtrackElem_mem_grade_two k G h)
      (Submodule.smul_mem _ _ (backtrackElem_mem_grade_two k G h'))⟩
  | long_path y _ => exact ⟨y.2.2.length, ofPath_mem_grade y⟩

variable [Finite V]

/-- **The skew relation ideal is homogeneous** for the path-length grading. This is the condition
needed to descend the grading to the skew-zigzag quotient. -/
theorem isHomogeneous_skewZigzagIdeal :
    (skewZigzagIdeal k G c).asIdeal.IsHomogeneous (grade k (DoubledQuiver G)) := by
  rw [skewZigzagIdeal_eq_span]
  exact TwoSidedIdeal.homogeneous_span _ fun _ hx =>
    IsSkewZigzagRelator.isHomogeneousElem k G c hx

end Homogeneous

/-! ### The induced grading on the skew relation quotient -/

section Grade

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (c : SkewZigzagParameter k G)

/-- **The induced grading on the skew-zigzag relation quotient**: the degree-`n` piece is the image
of the degree-`n` piece of the path-length grading of the doubled path algebra under the quotient
map. By `TauCeti.isInternal_skewZigzagGrade` these pieces form an internal direct sum
decomposition of the quotient itself. -/
noncomputable def skewZigzagGrade (n : ℕ) : Submodule k (skewZigzagQuotient k G c) :=
  TauCeti.GradedAlgebra.quotientPiece (grade k (DoubledQuiver G)) (skewZigzagIdeal k G c).asIdeal n

/-- Membership in a graded piece is being the class of a homogeneous element of that degree. -/
theorem mem_skewZigzagGrade_iff {n : ℕ} {x : skewZigzagQuotient k G c} :
    x ∈ skewZigzagGrade k G c n ↔
      ∃ y ∈ grade k (DoubledQuiver G) n, skewZigzagMk k G c y = x := by
  simp only [skewZigzagGrade, TauCeti.GradedAlgebra.mem_quotientPiece_iff,
    skewZigzagMk_apply]

/-- A homogeneous element lands in the piece its degree names. -/
@[simp]
theorem skewZigzagMk_mem_skewZigzagGrade {n : ℕ} {y : pathAlgebra k (DoubledQuiver G)}
    (hy : y ∈ grade k (DoubledQuiver G) n) : skewZigzagMk k G c y ∈ skewZigzagGrade k G c n :=
  (mem_skewZigzagGrade_iff k G c).2 ⟨y, hy, rfl⟩

/-- **The skew-zigzag quotient is the internal direct sum of its graded pieces.** -/
theorem isInternal_skewZigzagGrade : DirectSum.IsInternal (skewZigzagGrade k G c) :=
  TauCeti.GradedAlgebra.isInternal_quotientPiece (grade k (DoubledQuiver G))
    (skewZigzagIdeal k G c).asIdeal (isHomogeneous_skewZigzagIdeal k G c)

/-- Multiplication adds degrees in the induced grading. -/
theorem mul_mem_skewZigzagGrade {m n : ℕ} {x y : skewZigzagQuotient k G c}
    (hx : x ∈ skewZigzagGrade k G c m) (hy : y ∈ skewZigzagGrade k G c n) :
    x * y ∈ skewZigzagGrade k G c (m + n) :=
  TauCeti.GradedAlgebra.mul_mem_quotientPiece _ _ hx hy

/-- **The skew-zigzag relation quotient is a graded algebra** for the induced path-length grading.
This is kept as a definition rather than an instance so that callers choose when to introduce it
locally; see `TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece`. -/
@[instance_reducible]
noncomputable def skewZigzagGradedAlgebra : GradedAlgebra (skewZigzagGrade k G c) :=
  TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece (grade k (DoubledQuiver G))
    (skewZigzagIdeal k G c).asIdeal (isHomogeneous_skewZigzagIdeal k G c)

/-! ### The graded pieces -/

/-- **Degree zero is spanned by the vertex idempotent classes.** -/
theorem skewZigzagGrade_zero_eq_span_range_vertexIdempotent :
    skewZigzagGrade k G c 0 =
      Submodule.span k
        (Set.range fun i : V => skewZigzagMk k G c (vertexIdempotent k (vertex G i))) := by
  refine le_antisymm (fun w hw => ?_) ?_
  · refine TauCeti.GradedAlgebra.mem_span_of_mem_quotientPiece
      (grade k (DoubledQuiver G)) (skewZigzagIdeal k G c).asIdeal (i := 0)
      (PathAlgebra.grade_zero_eq_span_range_vertexIdempotent k (DoubledQuiver G)) ?_ hw
    rintro z ⟨v, rfl⟩
    rw [← skewZigzagMk_apply k G c]
    exact Submodule.subset_span ⟨(vertexEquiv G).symm v, by simp⟩
  · rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    exact skewZigzagMk_mem_skewZigzagGrade k G c (PathAlgebra.vertexIdempotent_mem_grade_zero _)

/-- **Degree one is spanned by the arrow classes**, one for each dart of the graph. -/
theorem skewZigzagGrade_one_eq_span_range_ofArrow :
    skewZigzagGrade k G c 1 =
      Submodule.span k (Set.range fun d : G.Dart =>
        skewZigzagMk k G c (ofArrow (arrow G d.adj))) := by
  refine le_antisymm (fun w hw => ?_) ?_
  · refine TauCeti.GradedAlgebra.mem_span_of_mem_quotientPiece
      (grade k (DoubledQuiver G)) (skewZigzagIdeal k G c).asIdeal (i := 1)
      PathAlgebra.grade_one_eq_span_range_ofArrow ?_ hw
    rintro z ⟨⟨a, b, e⟩, rfl⟩
    rw [← skewZigzagMk_apply k G c]
    obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i := ⟨_, (vertexEquiv_symm_apply G a).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = vertex G j := ⟨_, (vertexEquiv_symm_apply G b).symm⟩
    have hadj : G.Adj i j := (nonempty_hom_iff G).mp ⟨e⟩
    obtain rfl : e = arrow G hadj := Subsingleton.elim _ _
    exact Submodule.subset_span ⟨⟨(i, j), hadj⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro z ⟨d, rfl⟩
    exact skewZigzagMk_mem_skewZigzagGrade k G c (PathAlgebra.ofArrow_mem_grade_one _)

/-- **Degree two is spanned by the backtrack classes**, one for each dart of the graph: every
length-two path either does not return, and dies, or returns to its source and is a backtrack.
The backtracks at one vertex agree only up to the unit ratios of the parameter, so the family is
indexed by darts rather than by one volume class per vertex. -/
theorem skewZigzagGrade_two_eq_span_range_backtrackElem :
    skewZigzagGrade k G c 2 =
      Submodule.span k (Set.range fun d : G.Dart =>
        skewZigzagMk k G c (backtrackElem G k d.adj)) := by
  refine le_antisymm (fun w hw => ?_) ?_
  · refine TauCeti.GradedAlgebra.mem_span_of_mem_quotientPiece
      (grade k (DoubledQuiver G)) (skewZigzagIdeal k G c).asIdeal (i := 2)
      (PathAlgebra.grade_eq_span_image_basis k (DoubledQuiver G) 2) ?_ hw
    rintro z ⟨⟨a, b, p⟩, hp, rfl⟩
    rw [← skewZigzagMk_apply k G c, coe_pathAlgebraBasis]
    obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i := ⟨_, (vertexEquiv_symm_apply G a).symm⟩
    rcases eq_or_ne b (vertex G i) with rfl | hne
    · obtain ⟨j, h, rfl⟩ := exists_eq_backtrackPath G p hp
      exact Submodule.subset_span ⟨⟨(i, j), h⟩, by simp only [backtrackElem_eq_ofPath]⟩
    · rw [skewZigzagMk_ofPath_eq_zero_of_ne k G c p hp hne.symm]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro z ⟨d, rfl⟩
    exact skewZigzagMk_mem_skewZigzagGrade k G c (backtrackElem_mem_grade_two k G d.adj)

/-- Every piece of degree at least three vanishes: all long paths are relations. -/
theorem skewZigzagGrade_eq_bot_of_three_le {n : ℕ} (hn : 3 ≤ n) : skewZigzagGrade k G c n = ⊥ := by
  refine TauCeti.GradedAlgebra.quotientPiece_eq_bot_of_le (grade k (DoubledQuiver G))
    (skewZigzagIdeal k G c).asIdeal fun y hy => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← skewZigzagMk_apply, skewZigzagMk_eq_zero_iff]
  rw [PathAlgebra.grade_eq_span_image_basis] at hy
  refine (Submodule.span_le (p := (skewZigzagIdeal k G c).asIdeal.restrictScalars k)).2 ?_ hy
  rintro z ⟨t, ht, rfl⟩
  rw [coe_pathAlgebraBasis]
  exact mem_skewZigzagIdeal_of_isSkewZigzagRelator k G c
    (IsSkewZigzagRelator.long_path t (hn.trans (le_of_eq ht.symm)))

end Grade

/-! ### The comparison isomorphisms are graded -/

section GradedEquiv

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-- **The gauge isomorphism is graded**: it and its inverse are arrow rescalings, which preserve
path length. -/
@[simp]
theorem skewZigzagQuotientGaugeEquiv_mem_skewZigzagGrade_iff (c c' : SkewZigzagParameter k G)
    (u : ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ) (hc : c' = c.gauge u) {n : ℕ}
    {x : skewZigzagQuotient k G c} :
    skewZigzagQuotientGaugeEquiv k G c c' u hc x ∈ skewZigzagGrade k G c' n ↔
      x ∈ skewZigzagGrade k G c n := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := (mem_skewZigzagGrade_iff k G c').1 hx
    rw [← (skewZigzagQuotientGaugeEquiv k G c c' u hc).symm_apply_apply x, ← hxy,
      skewZigzagQuotientGaugeEquiv_symm_skewZigzagMk]
    exact skewZigzagMk_mem_skewZigzagGrade k G c (rescale_mem_grade _ hy)
  · obtain ⟨y, hy, rfl⟩ := (mem_skewZigzagGrade_iff k G c).1 hx
    rw [skewZigzagQuotientGaugeEquiv_skewZigzagMk]
    exact skewZigzagMk_mem_skewZigzagGrade k G c' (rescale_mem_grade _ hy)

/-- **The comparison of the constant parameter with the ordinary zigzag relation quotient is
graded**: it matches the skew-zigzag grading at the constant parameter with the ordinary zigzag
grading. -/
@[simp]
theorem skewZigzagQuotientOneEquiv_mem_zigzagGrade_iff {n : ℕ} {x : skewZigzagQuotient k G 1} :
    skewZigzagQuotientOneEquiv k G x ∈ zigzagGrade k G n ↔ x ∈ skewZigzagGrade k G 1 n := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := (mem_zigzagGrade_iff k G).1 hx
    rw [← (skewZigzagQuotientOneEquiv k G).symm_apply_apply x, ← hxy,
      skewZigzagQuotientOneEquiv_symm_zigzagMk]
    exact skewZigzagMk_mem_skewZigzagGrade k G 1 hy
  · obtain ⟨y, hy, rfl⟩ := (mem_skewZigzagGrade_iff k G 1).1 hx
    rw [skewZigzagQuotientOneEquiv_skewZigzagMk]
    exact zigzagMk_mem_zigzagGrade k G hy

variable {W : Type v} [Finite W] {H : SimpleGraph W}

/-- **The relabelling isomorphism along a graph isomorphism is graded**: it and its inverse are
induced by relabellings of the doubled path algebras, which preserve path length. -/
@[simp]
theorem skewZigzagQuotientEquiv_mem_skewZigzagGrade_iff (e : G ≃g H)
    (c : SkewZigzagParameter k G) {n : ℕ} {x : skewZigzagQuotient k G c} :
    skewZigzagQuotientEquiv k e c x ∈ skewZigzagGrade k H (c.relabel e) n ↔
      x ∈ skewZigzagGrade k G c n := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := (mem_skewZigzagGrade_iff k H (c.relabel e)).1 hx
    have hsymm : (skewZigzagQuotientEquiv k e c).symm (skewZigzagMk k H (c.relabel e) y) =
        skewZigzagMk k G c ((pathAlgebraEquiv k e).symm y) := by
      rw [AlgEquiv.symm_apply_eq, skewZigzagQuotientEquiv_skewZigzagMk, AlgEquiv.apply_symm_apply]
    rw [← (skewZigzagQuotientEquiv k e c).symm_apply_apply x, ← hxy, hsymm]
    refine skewZigzagMk_mem_skewZigzagGrade k G c ?_
    rwa [← pathAlgebraEquiv_mem_grade_iff k e, AlgEquiv.apply_symm_apply]
  · obtain ⟨y, hy, rfl⟩ := (mem_skewZigzagGrade_iff k G c).1 hx
    rw [skewZigzagQuotientEquiv_skewZigzagMk]
    exact skewZigzagMk_mem_skewZigzagGrade k H _ ((pathAlgebraEquiv_mem_grade_iff k e).2 hy)

end GradedEquiv

/-! ### Vertex-fixing graded classification extending Couture's result -/

namespace SkewZigzagParameter

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {c c' : SkewZigzagParameter k G}

/-- **Gauge classes are vertex-fixing graded isomorphism classes.** Two skew-zigzag parameters over
a commutative ring are gauge equivalent exactly when their relation quotients are isomorphic by a
graded algebra isomorphism fixing every vertex idempotent. The gauge isomorphism is graded, and
conversely every vertex-fixing isomorphism, graded or not, forces gauge equivalence
(`AlgEquiv.isGaugeEquivalent_of_vertexFixing`). -/
theorem isGaugeEquivalent_iff_exists_graded_vertexFixing_algEquiv :
    c.IsGaugeEquivalent c' ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        (∀ (n : ℕ) (x : skewZigzagQuotient k G c),
          φ x ∈ skewZigzagGrade k G c' n ↔ x ∈ skewZigzagGrade k G c n) ∧
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
          skewZigzagMk k G c' (vertexIdempotent k (vertex G i)) := by
  refine ⟨fun h => ?_, fun ⟨φ, _, hφ⟩ => φ.isGaugeEquivalent_of_vertexFixing hφ⟩
  obtain ⟨u, hu⟩ := isGaugeEquivalent_iff.mp h
  exact ⟨skewZigzagQuotientGaugeEquiv k G c c' u hu,
    fun _ _ => skewZigzagQuotientGaugeEquiv_mem_skewZigzagGrade_iff k G c c' u hu,
    fun i => by rw [skewZigzagQuotientGaugeEquiv_skewZigzagMk, rescale_vertexIdempotent]⟩

/-- **Vertex-fixing graded classification extending Couture's result**: over a commutative ring,
two skew-zigzag parameters of a finite graph have the same cohomology class in `H¹(G, kˣ)` exactly
when their relation quotients are isomorphic by a graded algebra isomorphism fixing every vertex
idempotent. Couture's Theorem 4.8 treats connected graphs over fields containing square roots. -/
theorem cohomologyClass_eq_iff_exists_graded_vertexFixing_algEquiv :
    cohomologyClass k G c = cohomologyClass k G c' ↔
      ∃ φ : skewZigzagQuotient k G c ≃ₐ[k] skewZigzagQuotient k G c',
        (∀ (n : ℕ) (x : skewZigzagQuotient k G c),
          φ x ∈ skewZigzagGrade k G c' n ↔ x ∈ skewZigzagGrade k G c n) ∧
        ∀ i : V, φ (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) =
          skewZigzagMk k G c' (vertexIdempotent k (vertex G i)) :=
  cohomologyClass_eq_iff.trans isGaugeEquivalent_iff_exists_graded_vertexFixing_algEquiv

end SkewZigzagParameter

end TauCeti
