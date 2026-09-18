/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Combinatorics.Quiver.PathWeight
public import TauCeti.RepresentationTheory.Quiver.Radical

/-!
# Gradings of a path algebra by arrow weights

The path algebra `kQ` is free on the paths of `Q`. Give every arrow `e` a weight `wt e` in an
additive monoid `M`, and give a path the sum `Quiver.Path.addWeight wt` of the weights of its
arrows. Concatenating paths adds their weights, so the span `TauCeti.PathAlgebra.gradeBy k wt m` of
the paths of weight `m` makes `kQ` an `M`-graded `k`-algebra once `M` is commutative. This file
constructs that grading in the internal sense: the graded pieces are submodules of `kQ` itself and
the decomposition compares them with `kQ`, rather than with a separate graded copy of it.

The **path-length grading** `TauCeti.PathAlgebra.grade k Q` is the case of the constant weight
`1 : ℕ`. Degree `0` is the span of the vertex idempotents and degree `1` is the span of the
arrows. Each piece is free on the paths of that length, and each sits inside the corresponding step
`TauCeti.pathSpan k Q n` of the length filtration of
`TauCeti.RepresentationTheory.Quiver.Radical`, which spans the paths of length *at least* `n`.

Other weights give the underlying gradings of DG path algebras. The (uncompleted) Ginzburg DG
algebra has as underlying graded algebra the path algebra of a quiver whose added loops sit in a
negative cohomological degree, and its Adams grading is a second, independent weight on the same
arrows (Etgü--Lekili; Keller); the standard construction further completes this graded path
algebra and equips it with a differential, neither of which is part of `gradeBy`.

## Main definitions

* `TauCeti.PathAlgebra.gradeBy`: the degree-`m` piece of the grading by an arrow weight, the span
  of the paths of weight `m`.
* `TauCeti.PathAlgebra.gradeByBasis`: the paths of weight `m` as a `k`-basis of that piece.
* `TauCeti.PathAlgebra.decomposeAlgHom`: the algebra homomorphism to the direct sum decomposing
  elements by weight, which is `DirectSum.decompose` for the grading below.
* `TauCeti.PathAlgebra.grade`: the degree-`n` piece of the path-length grading, the span of the
  paths of length `n`.
* `TauCeti.PathAlgebra.gradeBasis`: the paths of length `n` as a `k`-basis of that piece.

## Main results

* `TauCeti.PathAlgebra.gradeBy.gradedAlgebra`: **the grading by an arrow weight**, the
  `GradedAlgebra` instance on `TauCeti.PathAlgebra.gradeBy`. Its multiplicative half,
  `TauCeti.PathAlgebra.gradeBy_mul_gradeBy_le`, is the statement that multiplication adds
  weights, and `TauCeti.PathAlgebra.isInternal_gradeBy` is the comparison of the direct sum of the
  pieces with `kQ` itself.
* `TauCeti.PathAlgebra.mem_gradeBy_iff`: an element is homogeneous of weight `m` exactly when its
  path coordinates are supported on the paths of weight `m`.
* `TauCeti.PathAlgebra.ofArrow_mem_gradeBy`: an arrow is homogeneous of its own weight, and
  `TauCeti.PathAlgebra.ofArrow_mem_gradeBy_iff` and
  `TauCeti.PathAlgebra.vertexIdempotent_mem_gradeBy_iff` read off the degree of an arrow and of a
  vertex idempotent.
* `TauCeti.PathAlgebra.gradedAlgebra`: **the path-length grading**, the `GradedAlgebra` instance
  on `TauCeti.PathAlgebra.grade`, with `TauCeti.PathAlgebra.grade_mul_grade_le` and
  `TauCeti.PathAlgebra.isInternal_grade` its two halves.
* `TauCeti.PathAlgebra.grade_zero_eq_span_range_vertexIdempotent` and
  `TauCeti.PathAlgebra.grade_one_eq_span_range_ofArrow`: the vertex idempotents span degree `0`
  and the arrows span degree `1`.
* `TauCeti.PathAlgebra.grade_le_pathSpan`: the degree-`n` piece lies in the `n`-th step of the
  length filtration.

## Implementation notes

The grading is constructed from `TauCeti.PathAlgebra.decomposeAlgHom`, built from the universal
property `TauCeti.PathAlgebra.liftAlgHom` in the same way as
`AddMonoidAlgebra.gradeBy.gradedAlgebra` is built from the universal property of an additive monoid
algebra: an assignment of a homogeneous summand to each basis path is an algebra map to the direct
sum as soon as it respects the three defining products of `kQ`. It is what
`GradedAlgebra.ofAlgHom` installs as `DirectSum.decompose`; the two maps are definitionally equal.
As for `AddMonoidAlgebra.grade` and `AddMonoidAlgebra.gradeBy`, the length grading is the weight
grading at one particular weight, so its graded-algebra structure is that of
`TauCeti.PathAlgebra.gradeBy`.

The unit of `kQ` is the sum of the vertex idempotents, which exists only for a finite vertex type,
so the graded *pieces* are defined for every quiver while the grading itself asks for `[Finite Q]`.

## References

* Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
  Ch. II, for the path-length grading.
* T. Etgü and Y. Lekili, *Koszul duality patterns in Floer theory*, and B. Keller, *Deformed
  Calabi--Yau completions*, for Ginzburg DG algebras, path algebras graded by arrow degrees.
-/

public section

namespace TauCeti

open DirectSum

universe u v w

namespace PathAlgebra

/-! ### The pieces of the grading by an arrow weight -/

section GradeBy

variable (k : Type w) [Semiring k] {Q : Type u} [Quiver.{v} Q] {M : Type*} [AddMonoid M]
  (wt : ∀ {a b : Q}, (a ⟶ b) → M)

/-- The degree-`m` piece of the grading of the path algebra by the arrow weight `wt`: the `k`-span
of the paths whose arrows have weights summing to `m`. -/
noncomputable def gradeBy (m : M) : Submodule k (pathAlgebra k Q) :=
  Submodule.span k
    ((fun x : Quiver.TotalPath Q => (ofPath x : pathAlgebra k Q)) ''
      {x : Quiver.TotalPath Q | x.2.2.addWeight wt = m})

/-- The degree-`m` piece is the span of the image of the weight-`m` paths under the path basis.
This is the form the `Module.Basis` API reads. -/
theorem gradeBy_eq_span_image_basis (m : M) :
    gradeBy k wt m = Submodule.span k
      (⇑(pathAlgebraBasis k Q) '' {x : Quiver.TotalPath Q | x.2.2.addWeight wt = m}) := by
  simp only [gradeBy, coe_pathAlgebraBasis]

/-- The degree-`m` piece is the span of the weight-`m` paths, indexed by the subtype they form. -/
theorem gradeBy_eq_span_range (m : M) :
    gradeBy k wt m = Submodule.span k
      (Set.range fun x : {x : Quiver.TotalPath Q // x.2.2.addWeight wt = m} =>
        (ofPath x.1 : pathAlgebra k Q)) := by
  simp only [gradeBy, Set.image_eq_range]
  -- `↥{x | x.2.2.addWeight wt = m}` and `{x // x.2.2.addWeight wt = m}` are the same type by
  -- definition.
  rfl

variable {k wt}

/-- **Homogeneity is a condition on path coordinates**: an element has weight `m` exactly when
every path carrying a nonzero coordinate has weight `m`. -/
theorem mem_gradeBy_iff {m : M} {f : pathAlgebra k Q} :
    f ∈ gradeBy k wt m ↔
      ∀ x ∈ ((pathAlgebraBasis k Q).repr f).support, x.2.2.addWeight wt = m := by
  rw [gradeBy_eq_span_image_basis, Module.Basis.mem_span_image]
  exact ⟨fun h _ hx => h hx, fun h _ hx => h _ hx⟩

variable (wt) in
/-- A basis path is homogeneous of its own weight. -/
theorem ofPath_mem_gradeBy (x : Quiver.TotalPath Q) :
    (ofPath x : pathAlgebra k Q) ∈ gradeBy k wt (x.2.2.addWeight wt) :=
  Submodule.subset_span ⟨x, rfl, rfl⟩

/-- A path of weight `m` is homogeneous of degree `m`. -/
theorem ofPath_mem_gradeBy_of_addWeight {m : M} {x : Quiver.TotalPath Q}
    (hx : x.2.2.addWeight wt = m) : (ofPath x : pathAlgebra k Q) ∈ gradeBy k wt m :=
  hx ▸ ofPath_mem_gradeBy wt x

/-- **A basis path has degree `m` exactly when its weight is `m`.** -/
@[simp]
theorem ofPath_mem_gradeBy_iff [Nontrivial k] {m : M} {x : Quiver.TotalPath Q} :
    (ofPath x : pathAlgebra k Q) ∈ gradeBy k wt m ↔ x.2.2.addWeight wt = m := by
  refine ⟨fun hx => mem_gradeBy_iff.1 hx x ?_, ofPath_mem_gradeBy_of_addWeight⟩
  rw [ofPath_eq_single, pathAlgebraBasis_repr_single, Finsupp.mem_support_iff,
    Finsupp.single_eq_same]
  exact one_ne_zero

/-- A scaled basis path is homogeneous of the weight of that path. -/
theorem single_mem_gradeBy_of_addWeight {m : M} {x : Quiver.TotalPath Q}
    (hx : x.2.2.addWeight wt = m) (c : k) : (single x c : pathAlgebra k Q) ∈ gradeBy k wt m := by
  rw [single_eq_smul_ofPath]
  exact Submodule.smul_mem _ c (ofPath_mem_gradeBy_of_addWeight hx)

variable (wt) in
/-- A vertex idempotent is homogeneous of degree `0`. -/
theorem vertexIdempotent_mem_gradeBy_zero (v : Q) :
    (vertexIdempotent k v : pathAlgebra k Q) ∈ gradeBy k wt 0 := by
  rw [vertexIdempotent_eq_ofPath]
  exact ofPath_mem_gradeBy_of_addWeight (_root_.Quiver.Path.addWeight_nil wt v)

variable (wt) in
/-- **An arrow is homogeneous of its own weight.** -/
theorem ofArrow_mem_gradeBy {a b : Q} (e : a ⟶ b) :
    (ofArrow e : pathAlgebra k Q) ∈ gradeBy k wt (wt e) := by
  rw [ofArrow_eq_ofPath]
  exact ofPath_mem_gradeBy_of_addWeight (by simp [Quiver.Hom.toPath])

/-- **A vertex idempotent has degree `m` exactly when `m = 0`.** -/
@[simp]
theorem vertexIdempotent_mem_gradeBy_iff [Nontrivial k] {m : M} (v : Q) :
    (vertexIdempotent k v : pathAlgebra k Q) ∈ gradeBy k wt m ↔ m = 0 := by
  rw [vertexIdempotent_eq_ofPath, ofPath_mem_gradeBy_iff, _root_.Quiver.Path.addWeight_nil,
    eq_comm]

/-- **An arrow has degree `m` exactly when its weight is `m`.** -/
theorem ofArrow_mem_gradeBy_iff [Nontrivial k] {m : M} {a b : Q} (e : a ⟶ b) :
    (ofArrow e : pathAlgebra k Q) ∈ gradeBy k wt m ↔ wt e = m := by
  rw [ofArrow_eq_ofPath, ofPath_mem_gradeBy_iff]
  simp [Quiver.Hom.toPath]

variable (k wt)

/-- The paths of weight `m` are a `k`-basis of the degree-`m` piece: every graded piece is free. -/
noncomputable def gradeByBasis (m : M) :
    Module.Basis {x : Quiver.TotalPath Q // x.2.2.addWeight wt = m} k (gradeBy k wt m) :=
  (Module.Basis.span
      (linearIndependent_ofPath k Q fun x : Quiver.TotalPath Q => x.2.2.addWeight wt = m)).map
    (LinearEquiv.ofEq _ _ (gradeBy_eq_span_range k wt m).symm)

variable {k wt}

/-- The basis of the degree-`m` piece consists of the paths of weight `m`. -/
@[simp]
theorem coe_gradeByBasis_apply {m : M}
    (x : {x : Quiver.TotalPath Q // x.2.2.addWeight wt = m}) :
    (gradeByBasis k wt m x : pathAlgebra k Q) = ofPath x.1 := by
  rw [gradeByBasis, Module.Basis.map_apply, Module.Basis.span_apply, LinearEquiv.coe_ofEq_apply]

end GradeBy

section GradeByComm

variable {k : Type w} {Q : Type u} [Semiring k] [Quiver.{v} Q] {M : Type*} [AddCommMonoid M]
  {wt : ∀ {a b : Q}, (a ⟶ b) → M}

/-- **Two paths multiply in the sum of their weights**, whether or not they are composable. -/
theorem ofPath_mul_ofPath_mem_gradeBy (x y : Quiver.TotalPath Q) :
    (ofPath x * ofPath y : pathAlgebra k Q) ∈
      gradeBy k wt (x.2.2.addWeight wt + y.2.2.addWeight wt) := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases hda : d = a
  · subst hda
    rw [ofPath_mul_ofPath_of_comp]
    exact ofPath_mem_gradeBy_of_addWeight
      (by rw [_root_.Quiver.Path.addWeight_comp, add_comm])
  · rw [ofPath_mul_ofPath_of_not_composable hda]
    exact Submodule.zero_mem _

end GradeByComm

section GradeByMul

variable {k : Type w} {Q : Type u} [CommSemiring k] [Quiver.{v} Q] {M : Type*} [AddCommMonoid M]
  {wt : ∀ {a b : Q}, (a ⟶ b) → M}

/-- **Multiplication adds weights.** -/
theorem gradeBy_mul_gradeBy_le [Finite Q] (i j : M) :
    gradeBy k wt i * gradeBy k wt j ≤ gradeBy k wt (i + j) := by
  simp only [gradeBy, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
  replace hx : x.2.2.addWeight wt = i := hx
  replace hy : y.2.2.addWeight wt = j := hy
  subst hx
  subst hy
  exact SetLike.mem_coe.2 (ofPath_mul_ofPath_mem_gradeBy x y)

end GradeByMul

/-! ### The graded algebra structure of an arrow weight -/

section GradedAlgebra

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q] [Finite Q] {M : Type*}
  [AddCommMonoid M] (wt : ∀ {a b : Q}, (a ⟶ b) → M)

/-- The graded pieces form a graded monoid: the unit is the degree-zero sum of the vertex
idempotents, and multiplication adds weights. -/
noncomputable instance gradeBy.gradedMonoid : SetLike.GradedMonoid (gradeBy k wt) where
  one_mem := by
    let _ := Fintype.ofFinite Q
    rw [one_def]
    exact Submodule.sum_mem _ fun v _ => vertexIdempotent_mem_gradeBy_zero wt v
  mul_mem _ _ _ _ hf hg := gradeBy_mul_gradeBy_le _ _ (Submodule.mul_mem_mul hf hg)

omit [Finite Q] in
/-- Two graded-monoid points of the graded pieces agree once their degrees and their underlying
path-algebra elements do. Private: it only removes the dependent rewriting from the products
below. -/
private theorem gradedMonoid_mk_eq {i j : M} {f : gradeBy k wt i} {g : gradeBy k wt j}
    (hij : i = j) (hfg : (f : pathAlgebra k Q) = g) :
    GradedMonoid.mk (A := fun m => gradeBy k wt m) i f = GradedMonoid.mk j g := by
  subst hij
  exact congrArg _ (Subtype.ext hfg)

variable [DecidableEq M]

/-- The summand of the direct sum attached to a basis path: the path itself, in the degree its
weight names. This is the assignment the decomposition map lifts. -/
private noncomputable def gradeBySummand (x : Quiver.TotalPath Q) : ⨁ m, gradeBy k wt m :=
  DirectSum.of (fun m => gradeBy k wt m) (x.2.2.addWeight wt)
    ⟨ofPath x, ofPath_mem_gradeBy wt x⟩

private theorem gradeBySummand_mul_gradeBySummand {a b c : Q} (p : _root_.Quiver.Path a b)
    (q : _root_.Quiver.Path c a) :
    gradeBySummand k wt ⟨a, b, p⟩ * gradeBySummand k wt ⟨c, a, q⟩
      = gradeBySummand k wt ⟨c, b, q.comp p⟩ := by
  rw [gradeBySummand, gradeBySummand, gradeBySummand, DirectSum.of_mul_of]
  refine DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_mk_eq k wt ?_ ?_)
  · rw [_root_.Quiver.Path.addWeight_comp]
    exact add_comm _ _
  · exact ofPath_mul_ofPath_of_comp p q

private theorem gradeBySummand_mul_gradeBySummand_of_not_composable
    {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    gradeBySummand k wt x * gradeBySummand k wt y = 0 := by
  rw [gradeBySummand, gradeBySummand, DirectSum.of_mul_of]
  refine (DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_mk_eq k wt
    (j := x.2.2.addWeight wt + y.2.2.addWeight wt) (g := 0) rfl ?_)).trans (map_zero _)
  exact ofPath_mul_ofPath_of_not_composable h

private theorem sum_gradeBySummand_nil :
    letI := Fintype.ofFinite Q
    ∑ v : Q, gradeBySummand k wt ⟨v, v, _root_.Quiver.Path.nil⟩ = 1 := by
  let _ := Fintype.ofFinite Q
  have hv : ∀ v : Q, gradeBySummand k wt ⟨v, v, _root_.Quiver.Path.nil⟩
      = DirectSum.of (fun m => gradeBy k wt m) 0
        ⟨vertexIdempotent k v, vertexIdempotent_mem_gradeBy_zero wt v⟩ := fun v =>
    DirectSum.of_eq_of_gradedMonoid_eq
      (gradedMonoid_mk_eq k wt (_root_.Quiver.Path.addWeight_nil wt v)
        (vertexIdempotent_eq_ofPath k v).symm)
  have hsum : ∑ v : Q, DirectSum.of (fun m => gradeBy k wt m) 0
        ⟨vertexIdempotent k v, vertexIdempotent_mem_gradeBy_zero wt v⟩
      = DirectSum.of (fun m => gradeBy k wt m) 0
        (∑ v : Q, ⟨vertexIdempotent k v, vertexIdempotent_mem_gradeBy_zero wt v⟩) :=
    (map_sum _ _ _).symm
  rw [Finset.sum_congr rfl fun v _ => hv v, hsum, DirectSum.one_def]
  refine congrArg _ (Subtype.ext ?_)
  rw [AddSubmonoidClass.coe_finsetSum]
  exact (one_def (k := k) (Q := Q)).symm

/-- The algebra homomorphism into the direct sum of graded pieces that decomposes elements by
weight. This is the map `GradedAlgebra.ofAlgHom` installs as `DirectSum.decompose` for the grading
below, as `AddMonoidAlgebra.decomposeAux` is for the grading of a monoid algebra; the two maps are
definitionally equal. -/
noncomputable def decomposeAlgHom : pathAlgebra k Q →ₐ[k] ⨁ m, gradeBy k wt m :=
  liftAlgHom k (gradeBySummand k wt) (gradeBySummand_mul_gradeBySummand k wt)
    (gradeBySummand_mul_gradeBySummand_of_not_composable k wt) (sum_gradeBySummand_nil k wt)

/-- The decomposition map sends a basis path to the summand its weight names. -/
theorem decomposeAlgHom_ofPath (x : Quiver.TotalPath Q) :
    decomposeAlgHom k wt (ofPath x)
      = DirectSum.of (fun m => gradeBy k wt m) (x.2.2.addWeight wt)
        ⟨ofPath x, ofPath_mem_gradeBy wt x⟩ := by
  rw [decomposeAlgHom, liftAlgHom_ofPath k (gradeBySummand k wt)
    (gradeBySummand_mul_gradeBySummand k wt)
    (gradeBySummand_mul_gradeBySummand_of_not_composable k wt) (sum_gradeBySummand_nil k wt),
    gradeBySummand]

/-- The span induction behind `decomposeAlgHom_of_mem`: on the span of the weight-`m` paths the
decomposition map is the inclusion of the degree-`m` summand. The membership hypothesis is
quantified inside the conclusion so that the motive of the induction does not mention a fixed
membership proof; each step supplies its own. -/
private theorem decomposeAlgHom_apply_aux {m : M} {f : pathAlgebra k Q}
    (hf : f ∈ Submodule.span k
      (Set.range fun x : {x : Quiver.TotalPath Q // x.2.2.addWeight wt = m} =>
        (ofPath x.1 : pathAlgebra k Q))) :
    ∀ h : f ∈ gradeBy k wt m,
      decomposeAlgHom k wt f = DirectSum.of (fun m' => gradeBy k wt m') m ⟨f, h⟩ := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hg
    subst hx
    exact fun _ => decomposeAlgHom_ofPath k wt x
  | zero => exact fun _ => (map_zero _).trans (map_zero _).symm
  | add g g' hg hg' ihg ihg' =>
    refine fun _ => ?_
    rw [map_add, ihg ((gradeBy_eq_span_range k wt m).ge hg),
      ihg' ((gradeBy_eq_span_range k wt m).ge hg'), ← map_add, AddMemClass.mk_add_mk]
  | smul c g hg ih =>
    refine fun _ => ?_
    rw [map_smul, ih ((gradeBy_eq_span_range k wt m).ge hg), ← DirectSum.of_smul,
      SetLike.mk_smul_mk]

/-- The decomposition map is the identity on a homogeneous element, placing it in the summand its
degree names. -/
theorem decomposeAlgHom_of_mem {m : M} {f : pathAlgebra k Q} (hf : f ∈ gradeBy k wt m) :
    decomposeAlgHom k wt f = DirectSum.of (fun m' => gradeBy k wt m') m ⟨f, hf⟩ :=
  decomposeAlgHom_apply_aux k wt ((gradeBy_eq_span_range k wt m).le hf) hf

/-- **The grading by an arrow weight**: the path algebra of a finite quiver is `M`-graded by the
weight `wt`, with the span of the paths of weight `m` in degree `m`. -/
noncomputable instance gradeBy.gradedAlgebra : GradedAlgebra (gradeBy k wt) :=
  .ofAlgHom _ (decomposeAlgHom k wt)
    (AlgHom.toLinearMap_injective <| (pathAlgebraBasis k Q).ext fun x => by
      simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
        AlgHom.toLinearMap_apply, coe_pathAlgebraBasis, decomposeAlgHom_ofPath,
        DirectSum.coeAlgHom_of, AlgHom.coe_id, id_eq])
    fun _ f => decomposeAlgHom_of_mem k wt f.2

/-- **The path algebra is the internal direct sum of its weight pieces**: the direct-sum graded
algebra is compared with `kQ` itself, not with a separate graded copy. -/
theorem isInternal_gradeBy : DirectSum.IsInternal (gradeBy k wt) :=
  DirectSum.Decomposition.isInternal _

/-- The decomposition sends a basis path to the summand its weight names. -/
@[simp]
theorem decompose_ofPath_gradeBy (x : Quiver.TotalPath Q) :
    DirectSum.decompose (gradeBy k wt) (ofPath x : pathAlgebra k Q)
      = DirectSum.of (fun m => gradeBy k wt m) (x.2.2.addWeight wt)
        ⟨ofPath x, ofPath_mem_gradeBy wt x⟩ :=
  DirectSum.decompose_of_mem _ (ofPath_mem_gradeBy wt x)

end GradedAlgebra

/-! ### The path-length grading -/

section Grade

variable (k : Type w) (Q : Type u) [Semiring k] [Quiver.{v} Q]

/-- The degree-`n` piece of the path-length grading of the path algebra: the `k`-span of the paths
of length `n`. It is the grading by the constant arrow weight `1`. -/
noncomputable def grade (n : ℕ) : Submodule k (pathAlgebra k Q) :=
  gradeBy k (Q := Q) (fun _ => 1) n

/-- The path-length grading is the grading by the constant arrow weight `1`. -/
theorem gradeBy_const_one : gradeBy k (Q := Q) (fun _ => 1) = grade k Q :=
  (rfl)

/-- The degree-`n` piece is the span of the image of the length-`n` paths under the path basis.
This is the form the `Module.Basis` API reads. -/
theorem grade_eq_span_image_basis (n : ℕ) :
    grade k Q n = Submodule.span k
      (⇑(pathAlgebraBasis k Q) '' {x : Quiver.TotalPath Q | x.2.2.length = n}) := by
  simp only [← gradeBy_const_one, gradeBy_eq_span_image_basis,
    _root_.Quiver.Path.addWeight_const, smul_eq_mul, mul_one]

/-- The degree-`n` piece is the span of the length-`n` paths, indexed by the subtype they form. -/
theorem grade_eq_span_range (n : ℕ) :
    grade k Q n = Submodule.span k
      (Set.range fun x : {x : Quiver.TotalPath Q // x.2.2.length = n} =>
        (ofPath x.1 : pathAlgebra k Q)) := by
  simp only [grade_eq_span_image_basis, coe_pathAlgebraBasis, Set.image_eq_range]
  -- `↥{x | x.2.2.length = n}` and `{x // x.2.2.length = n}` are the same type by definition.
  rfl

variable {k Q}

/-- **Homogeneity is a condition on path coordinates**: an element has degree `n` exactly when
every path carrying a nonzero coordinate has length `n`. -/
theorem mem_grade_iff {n : ℕ} {f : pathAlgebra k Q} :
    f ∈ grade k Q n ↔ ∀ x ∈ ((pathAlgebraBasis k Q).repr f).support, x.2.2.length = n := by
  rw [grade_eq_span_image_basis, Module.Basis.mem_span_image]
  exact ⟨fun h _ hx => h hx, fun h _ hx => h _ hx⟩

/-- A path of length `n` is homogeneous of degree `n`. -/
theorem ofPath_mem_grade_of_length {n : ℕ} {x : Quiver.TotalPath Q} (hx : x.2.2.length = n) :
    (ofPath x : pathAlgebra k Q) ∈ grade k Q n :=
  ofPath_mem_gradeBy_of_addWeight (by rw [_root_.Quiver.Path.addWeight_const, smul_eq_mul,
    mul_one, hx])

/-- A basis path is homogeneous of its own length. -/
theorem ofPath_mem_grade (x : Quiver.TotalPath Q) :
    (ofPath x : pathAlgebra k Q) ∈ grade k Q x.2.2.length :=
  ofPath_mem_grade_of_length rfl

/-- **A basis path has degree `n` exactly when its length is `n`.** -/
@[simp]
theorem ofPath_mem_grade_iff [Nontrivial k] {n : ℕ} {x : Quiver.TotalPath Q} :
    (ofPath x : pathAlgebra k Q) ∈ grade k Q n ↔ x.2.2.length = n := by
  rw [← gradeBy_const_one, ofPath_mem_gradeBy_iff, _root_.Quiver.Path.addWeight_const,
    smul_eq_mul, mul_one]

/-- A scaled basis path is homogeneous of the length of that path. -/
theorem single_mem_grade_of_length {n : ℕ} {x : Quiver.TotalPath Q} (hx : x.2.2.length = n)
    (c : k) : (single x c : pathAlgebra k Q) ∈ grade k Q n := by
  rw [single_eq_smul_ofPath]
  exact Submodule.smul_mem _ c (ofPath_mem_grade_of_length hx)

/-- A vertex idempotent is homogeneous of degree `0`. -/
theorem vertexIdempotent_mem_grade_zero (v : Q) :
    (vertexIdempotent k v : pathAlgebra k Q) ∈ grade k Q 0 :=
  vertexIdempotent_mem_gradeBy_zero _ v

/-- **Two paths multiply in the sum of their degrees**, whether or not they are composable. -/
theorem ofPath_mul_ofPath_mem_grade (x y : Quiver.TotalPath Q) :
    (ofPath x * ofPath y : pathAlgebra k Q) ∈ grade k Q (x.2.2.length + y.2.2.length) := by
  have h := ofPath_mul_ofPath_mem_gradeBy (k := k) (wt := fun {_ _ : Q} _ => 1) x y
  rwa [_root_.Quiver.Path.addWeight_const, _root_.Quiver.Path.addWeight_const, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one] at h

variable (k Q)

/-- The paths of length `n` are a `k`-basis of the degree-`n` piece: every graded piece is free. -/
noncomputable def gradeBasis (n : ℕ) :
    Module.Basis {x : Quiver.TotalPath Q // x.2.2.length = n} k (grade k Q n) :=
  (Module.Basis.span
      (linearIndependent_ofPath k Q fun x : Quiver.TotalPath Q => x.2.2.length = n)).map
    (LinearEquiv.ofEq _ _ (grade_eq_span_range k Q n).symm)

variable {k Q}

/-- The basis of the degree-`n` piece consists of the paths of length `n`. -/
@[simp]
theorem coe_gradeBasis_apply {n : ℕ} (x : {x : Quiver.TotalPath Q // x.2.2.length = n}) :
    (gradeBasis k Q n x : pathAlgebra k Q) = ofPath x.1 := by
  rw [gradeBasis, Module.Basis.map_apply, Module.Basis.span_apply, LinearEquiv.coe_ofEq_apply]

variable (k Q)

/-- **Degree `0` is the span of the vertex idempotents**: the trivial paths are exactly the paths
of length zero. -/
theorem grade_zero_eq_span_range_vertexIdempotent : grade k Q 0
    = Submodule.span k (Set.range (vertexIdempotent k)) := by
  rw [grade_eq_span_image_basis, coe_pathAlgebraBasis]
  refine congrArg (Submodule.span k) (Set.ext fun f => ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b, p⟩, hp, rfl⟩
    replace hp : p.length = 0 := hp
    obtain rfl := p.eq_of_length_zero hp
    obtain rfl := p.eq_nil_of_length_zero hp
    exact ⟨a, vertexIdempotent_eq_ofPath k a⟩
  · rintro ⟨v, rfl⟩
    exact ⟨⟨v, v, _root_.Quiver.Path.nil⟩, rfl, (vertexIdempotent_eq_ofPath k v).symm⟩

/-- **The degree-`n` piece lies in the `n`-th step of the length filtration**: a path of length
exactly `n` is in particular a path of length at least `n`. -/
theorem grade_le_pathSpan (n : ℕ) : grade k Q n ≤ pathSpan k Q n := by
  rw [grade_eq_span_image_basis, coe_pathAlgebraBasis]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ofPath_mem_pathSpan hx.ge

variable {k Q}

/-- An arrow is homogeneous of degree `1`. -/
theorem ofArrow_mem_grade_one {a b : Q} (e : a ⟶ b) :
    (ofArrow e : pathAlgebra k Q) ∈ grade k Q 1 :=
  ofArrow_mem_gradeBy _ e

/-- **Degree `1` is the span of the arrows**: the length-one paths are exactly the arrows. -/
theorem grade_one_eq_span_range_ofArrow : grade k Q 1 = Submodule.span k
    (Set.range fun e : Σ a b : Q, a ⟶ b => (ofArrow e.2.2 : pathAlgebra k Q)) := by
  rw [grade_eq_span_image_basis, coe_pathAlgebraBasis]
  refine congrArg (Submodule.span k) (Set.ext fun f => ⟨?_, ?_⟩)
  · rintro ⟨⟨a, b, p⟩, hp, rfl⟩
    obtain ⟨c, e, q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ (n := 0) (by simpa using hp)
    obtain rfl := q.eq_of_length_zero hq
    obtain rfl := q.eq_nil_of_length_zero hq
    exact ⟨⟨a, c, e⟩, ofArrow_eq_ofPath e⟩
  · rintro ⟨⟨a, b, e⟩, rfl⟩
    exact ⟨⟨a, b, e.toPath⟩, rfl, (ofArrow_eq_ofPath e).symm⟩

end Grade

section GradeComm

variable {k : Type w} {Q : Type u} [CommSemiring k] [Quiver.{v} Q]

/-- **Multiplication adds degrees.** -/
theorem grade_mul_grade_le [Finite Q] (i j : ℕ) :
    grade k Q i * grade k Q j ≤ grade k Q (i + j) :=
  gradeBy_mul_gradeBy_le i j

end GradeComm

section GradedAlgebra

variable (k : Type w) (Q : Type u) [CommSemiring k] [Quiver.{v} Q] [Finite Q]

/-- The length pieces form a graded monoid, transported from the graded monoid of the constant
weight `1` along `TauCeti.PathAlgebra.gradeBy_const_one`. -/
instance gradedMonoid : SetLike.GradedMonoid (grade k Q) :=
  gradeBy_const_one k Q ▸ gradeBy.gradedMonoid k (Q := Q) fun _ => 1

/-- **The path-length grading**: the path algebra of a finite quiver is `ℕ`-graded by path length,
with the span of the paths of length `n` in degree `n`. It is the grading by the constant weight
`1`, transported along `TauCeti.PathAlgebra.gradeBy_const_one`. -/
noncomputable instance gradedAlgebra : GradedAlgebra (grade k Q) :=
  gradeBy_const_one k Q ▸ gradeBy.gradedAlgebra k (Q := Q) fun _ => 1

/-- **The path algebra is the internal direct sum of its graded pieces**: the direct-sum graded
algebra is compared with `kQ` itself, not with a separate graded copy. -/
theorem isInternal_grade : DirectSum.IsInternal (grade k Q) :=
  DirectSum.Decomposition.isInternal _

/-- The decomposition sends a basis path to the summand indexed by its length. -/
@[simp]
theorem decompose_ofPath (x : Quiver.TotalPath Q) :
    DirectSum.decompose (grade k Q) (ofPath x : pathAlgebra k Q)
      = DirectSum.of (fun n => grade k Q n) x.2.2.length ⟨ofPath x, ofPath_mem_grade x⟩ :=
  DirectSum.decompose_of_mem _ (ofPath_mem_grade x)

end GradedAlgebra

end PathAlgebra

end TauCeti
