/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Derivation
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Map
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Grading

/-!
# The two-dimensional Ginzburg differential graded algebra of a quiver

Let `Q` be a finite quiver.  The **Ginzburg quiver** `TauCeti.GinzburgQuiver Q` has the vertices of
`Q`, the arrows of the doubled quiver `Quiver.Symmetrify Q`, and one further loop `t_i` at every
vertex `i`.  Its path algebra carries two gradings: a cohomological one in which doubled arrows have
degree `0` and the loops degree `-1`, and an Adams (path) grading in which doubled arrows have
degree `1` and the loops degree `2`.

The **two-dimensional Ginzburg differential** is the degree `+1` graded derivation which kills
every doubled arrow and sends `t_i` to the local preprojective relator

```text
ρ_i = ∑_{head a = i} a a* - ∑_{tail a = i} a* a
```

of `TauCeti.localPreprojectiveRelator`, read inside the Ginzburg path algebra.  The resulting
differential graded algebra is the non-completed two-dimensional Ginzburg algebra `Π₂(Q)`; its
differential has bidegree `(1, 0)`, raising the cohomological degree by one and preserving the Adams
degree.

## Main definitions

* `TauCeti.GinzburgQuiver`: the Ginzburg quiver of `Q`, with arrows `TauCeti.GinzburgHom`.
* `TauCeti.ginzburgOf`: the inclusion of the doubled quiver, and `TauCeti.ginzburgMap` the induced
  homomorphism of path algebras.
* `TauCeti.ginzburgOriginalMap`: the inclusion of the path algebra of `Q` in the Ginzburg path
  algebra, as the original arrows.
* `TauCeti.ginzburgTwoArrowRelator`: the prescribed values of the differential on the arrows.
* `TauCeti.ginzburgTwoDegree` and `TauCeti.ginzburgTwoAdamsDegree`: the two arrow weights.
* `TauCeti.ginzburgTwoDifferential`: the two-dimensional Ginzburg differential.

## Main results

* `TauCeti.ginzburgTwoDifferential_ofArrow_loop`: the differential of the loop at `i` is the local
  preprojective relator at `i`, while `TauCeti.ginzburgTwoDifferential_ginzburgMap` says that
  the whole doubled path algebra consists of cycles.
* `TauCeti.isDGAlgebra_ginzburgTwoDifferential`: **the two-dimensional Ginzburg differential graded
  algebra**, for the cohomological grading, with `TauCeti.ginzburgTwoDifferential_mul` and
  `TauCeti.ginzburgTwoDifferential_sq_zero` its Leibniz rule and vanishing square.
* `TauCeti.ginzburgTwoDifferential_mem_gradeBy_ginzburgTwoAdamsDegree`: **the differential preserves
  the Adams grading**, so that together with the previous result it has bidegree `(1, 0)`.

## References

* V. Ginzburg, *Calabi--Yau algebras*, Section 4.2.
* B. Keller, *Deformed Calabi--Yau completions*, Section 6.5.
* T. Etgü and Y. Lekili, *Koszul duality patterns in Floer theory*, Section 4, for the bigraded,
  non-completed two-dimensional model used here.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

/-- The arrows of the Ginzburg quiver of `Q`: the arrows of the doubled quiver
`Quiver.Symmetrify Q`, together with one extra loop at every vertex. -/
inductive GinzburgHom (Q : Type u) [Quiver.{v} Q] : Q → Q → Type _
  /-- An arrow of the doubled quiver, whose arrows `i ⟶ j` are by definition the arrows of `Q` in
  either direction.  `TauCeti.ginzburgOf` is the resulting inclusion of `Quiver.Symmetrify Q`. -/
  | double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) : GinzburgHom Q i j
  /-- The extra loop at a vertex. -/
  | loop (i : Q) : GinzburgHom Q i i

/-- The **Ginzburg quiver** of `Q`: the doubled quiver with one extra loop adjoined at every
vertex.  Its vertices are those of `Q`, and its arrows are `TauCeti.GinzburgHom`. -/
@[expose]
def GinzburgQuiver (Q : Type u) : Type u := Q

variable {Q : Type u} [Quiver.{v} Q]

instance instQuiverGinzburgQuiver : Quiver (GinzburgQuiver Q) := ⟨GinzburgHom Q⟩

instance instFiniteGinzburgQuiver [Finite Q] : Finite (GinzburgQuiver Q) :=
  inferInstanceAs (Finite Q)

/-- The inclusion of the doubled quiver in the Ginzburg quiver, the identity on vertices. -/
@[expose]
def ginzburgOf : Symmetrify Q ⥤q GinzburgQuiver Q where
  obj v := v
  map a := GinzburgHom.double a

@[simp]
theorem ginzburgOf_map {i j : Symmetrify Q} (a : i ⟶ j) :
    ginzburgOf.map a = GinzburgHom.double a := rfl

/-- The doubled-quiver inclusion is the identity on vertices. -/
@[simp]
theorem ginzburgOf_obj (v : Symmetrify Q) : ginzburgOf.obj v = v := rfl

/-- The inclusion of the doubled quiver in the Ginzburg quiver is bijective on vertices. -/
theorem ginzburgOf_obj_bijective : Function.Bijective (ginzburgOf (Q := Q)).obj :=
  Function.bijective_id

/-- The **cohomological degree** of an arrow of the Ginzburg quiver: the doubled arrows sit in
degree `0` and the adjoined loops in degree `-1`. -/
def ginzburgTwoDegree : ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → ℤ
  | _, _, .double _ => 0
  | _, _, .loop _ => -1

/-- The **Adams degree** of an arrow of the Ginzburg quiver: the doubled arrows sit in degree `1`
and the adjoined loops in degree `2`, the degrees for which the differential below is homogeneous
of degree `0`. -/
def ginzburgTwoAdamsDegree : ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → ℕ
  | _, _, .double _ => 1
  | _, _, .loop _ => 2

@[simp]
theorem ginzburgTwoDegree_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgTwoDegree (GinzburgHom.double a) = 0 := by
  simp [ginzburgTwoDegree]

@[simp]
theorem ginzburgTwoDegree_loop (i : Q) : ginzburgTwoDegree (GinzburgHom.loop i) = -1 := by
  simp [ginzburgTwoDegree]

@[simp]
theorem ginzburgTwoAdamsDegree_double {i j : Q}
    (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgTwoAdamsDegree (GinzburgHom.double a) = 1 := by
  simp [ginzburgTwoAdamsDegree]

@[simp]
theorem ginzburgTwoAdamsDegree_loop (i : Q) : ginzburgTwoAdamsDegree (GinzburgHom.loop i) = 2 := by
  simp [ginzburgTwoAdamsDegree]

/-- The cohomological degree pulled back along `TauCeti.ginzburgOf` is the constant weight `0`.
This is `TauCeti.ginzburgTwoDegree_double` for an arrow of `Quiver.Symmetrify Q`, whose type is
only definitionally the sum type that lemma is stated for. -/
private theorem ginzburgTwoDegree_ginzburgOf_map {a b : Symmetrify Q} (e : a ⟶ b) :
    ginzburgTwoDegree (ginzburgOf.map e) = 0 :=
  ginzburgTwoDegree_double e

/-- The Adams degree pulled back along `TauCeti.ginzburgOf` is the constant weight `1`.  This is
`TauCeti.ginzburgTwoAdamsDegree_double` for an arrow of `Quiver.Symmetrify Q`, whose type is only
definitionally the sum type that lemma is stated for. -/
private theorem ginzburgTwoAdamsDegree_ginzburgOf_map {a b : Symmetrify Q} (e : a ⟶ b) :
    ginzburgTwoAdamsDegree (ginzburgOf.map e) = 1 :=
  ginzburgTwoAdamsDegree_double e

section Map

variable (k : Type w) [CommSemiring k] [Finite Q]

/-- The homomorphism from the doubled path algebra to the Ginzburg path algebra induced by
`TauCeti.ginzburgOf`. -/
noncomputable def ginzburgMap :
    pathAlgebra k (Symmetrify Q) →ₐ[k] pathAlgebra k (GinzburgQuiver Q) :=
  mapAlgHom k ginzburgOf ginzburgOf_obj_bijective

/-- The induced homomorphism sends a doubled-quiver arrow to the corresponding doubled arrow of
the Ginzburg quiver. -/
theorem ginzburgMap_ofArrow {i j : Symmetrify Q} (a : i ⟶ j) :
    ginzburgMap k (ofArrow a) = ofArrow (GinzburgHom.double a) := by
  rw [ginzburgMap, mapAlgHom_ofArrow, ginzburgOf_map]
  rfl

/-- The induced homomorphism sends a doubled-quiver path to its image in the Ginzburg quiver. -/
@[simp]
theorem ginzburgMap_ofPath (x : Quiver.TotalPath (Symmetrify Q)) :
    ginzburgMap k (ofPath x) = ofPath (ginzburgOf.mapTotalPath x) := by
  rw [ginzburgMap, mapAlgHom_ofPath]

@[simp]
theorem ginzburgMap_doubledVertexIdempotent (v : Q) :
    ginzburgMap k (doubledVertexIdempotent k v) =
      vertexIdempotent (Q := GinzburgQuiver Q) k v := by
  rw [doubledVertexIdempotent_def, ginzburgMap, mapAlgHom_vertexIdempotent, ginzburgOf_obj,
    symmetrify_of_obj]

/-- The inclusion of the path algebra of `Q` in the path algebra of the Ginzburg quiver, sending
every arrow of `Q` to the corresponding original arrow. -/
noncomputable def ginzburgOriginalMap : pathAlgebra k Q →ₐ[k] pathAlgebra k (GinzburgQuiver Q) :=
  (ginzburgMap k).comp (mapAlgHom k Symmetrify.of symmetrify_of_obj_bijective)

/-- The inclusion sends an arrow of `Q` to the corresponding original arrow of the Ginzburg
quiver. Deliberately not a `simp` lemma: `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already normalizes
its left-hand side, and `TauCeti.ginzburgOriginalMap_ofPath_toPath` is the `simp` form. -/
theorem ginzburgOriginalMap_ofArrow {i j : Q} (a : i ⟶ j) :
    ginzburgOriginalMap k (ofArrow a) = ofArrow (GinzburgHom.double (Sum.inl a)) := by
  rw [ginzburgOriginalMap, AlgHom.comp_apply, mapAlgHom_ofArrow, ginzburgMap_ofArrow,
    Symmetrify.of_map]
  rfl

/-- The inclusion sends the one-arrow path to the corresponding original arrow. -/
@[simp]
theorem ginzburgOriginalMap_ofPath_toPath {i j : Q} (a : i ⟶ j) :
    ginzburgOriginalMap k (ofPath ⟨i, j, a.toPath⟩) =
      ofArrow (GinzburgHom.double (Sum.inl a)) := by
  simpa only [ofArrow_eq_ofPath] using ginzburgOriginalMap_ofArrow k a

@[simp]
theorem ginzburgOriginalMap_vertexIdempotent (v : Q) :
    ginzburgOriginalMap k (vertexIdempotent k v) =
      vertexIdempotent (Q := GinzburgQuiver Q) k v := by
  rw [ginzburgOriginalMap, AlgHom.comp_apply, mapAlgHom_vertexIdempotent,
    ← doubledVertexIdempotent_def, ginzburgMap_doubledVertexIdempotent]

/-! ### The doubled path algebra mapped to the Ginzburg path algebra -/

/-- **The doubled path algebra lands in cohomological degree `0`**: it is generated by the arrows
of the doubled quiver, all of which are of degree `0`. -/
theorem ginzburgMap_mem_gradeBy_ginzburgTwoDegree (x : pathAlgebra k (Symmetrify Q)) :
    ginzburgMap k x ∈ gradeBy k ginzburgTwoDegree 0 := by
  apply mapAlgHom_mem_gradeBy k ginzburgOf ginzburgOf_obj_bijective ginzburgTwoDegree
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => exact add_mem hx hy
  | single y c =>
      obtain ⟨a, b, p⟩ := y
      exact single_mem_gradeBy_of_addWeight
        (by simp only [ginzburgTwoDegree_ginzburgOf_map, _root_.Quiver.Path.addWeight_const,
          smul_zero]) c

/-- **The doubled path algebra keeps its length grading as the Adams grading.** -/
theorem ginzburgMap_mem_gradeBy_ginzburgTwoAdamsDegree {n : ℕ}
    {x : pathAlgebra k (Symmetrify Q)} (hx : x ∈ PathAlgebra.grade k (Symmetrify Q) n) :
    ginzburgMap k x ∈ gradeBy k ginzburgTwoAdamsDegree n := by
  apply mapAlgHom_mem_gradeBy k ginzburgOf ginzburgOf_obj_bijective ginzburgTwoAdamsDegree
  simp only [ginzburgTwoAdamsDegree_ginzburgOf_map, gradeBy_const_one]
  exact hx

end Map

section Differential

variable (k : Type w) [CommRing k] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]

/-- The relator assigned to an arrow in the two-dimensional Ginzburg differential: it is zero on
doubled arrows and the local preprojective relator at the vertex of an adjoined loop. -/
noncomputable def ginzburgTwoArrowRelator :
    ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → pathAlgebra k (GinzburgQuiver Q)
  | _, _, .double _ => 0
  | _, _, .loop i => ginzburgMap k (localPreprojectiveRelator k i)

@[simp]
theorem ginzburgTwoArrowRelator_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgTwoArrowRelator k (GinzburgHom.double a) = 0 := by
  simp [ginzburgTwoArrowRelator]

@[simp]
theorem ginzburgTwoArrowRelator_loop (i : Q) :
    ginzburgTwoArrowRelator k (GinzburgHom.loop i) =
      ginzburgMap k (localPreprojectiveRelator k i) := by
  simp [ginzburgTwoArrowRelator]

private theorem vertexIdempotent_mul_ginzburgTwoArrowRelator {i j : Q}
    (e : GinzburgHom Q i j) :
    (vertexIdempotent k j : pathAlgebra k (GinzburgQuiver Q)) * ginzburgTwoArrowRelator k e =
      ginzburgTwoArrowRelator k e := by
  cases e with
  | double a => simp [ginzburgTwoArrowRelator]
  | loop =>
      have h := congrArg (ginzburgMap (Q := Q) k)
        (doubledVertexIdempotent_mul_localPreprojectiveRelator (Q := Q) k i)
      rw [map_mul, ginzburgMap_doubledVertexIdempotent (Q := Q)] at h
      simpa [ginzburgTwoArrowRelator] using h

private theorem ginzburgTwoArrowRelator_mul_vertexIdempotent {i j : Q}
    (e : GinzburgHom Q i j) :
    ginzburgTwoArrowRelator k e * (vertexIdempotent k i : pathAlgebra k (GinzburgQuiver Q)) =
      ginzburgTwoArrowRelator k e := by
  cases e with
  | double a => simp [ginzburgTwoArrowRelator]
  | loop =>
      have h := congrArg (ginzburgMap (Q := Q) k)
        (localPreprojectiveRelator_mul_doubledVertexIdempotent (Q := Q) k i)
      rw [map_mul, ginzburgMap_doubledVertexIdempotent (Q := Q)] at h
      simpa [ginzburgTwoArrowRelator] using h

/-- **The two-dimensional Ginzburg differential** of `Q`: the degree `+1` graded derivation which
kills the doubled arrows and sends the loop `t_i` to the local preprojective relator `ρ_i`. -/
noncomputable def ginzburgTwoDifferential :
    pathAlgebra k (GinzburgQuiver Q) →ₗ[k] pathAlgebra k (GinzburgQuiver Q) :=
  liftDerivation k ginzburgTwoDegree (ginzburgTwoArrowRelator k)

@[simp]
theorem ginzburgTwoDifferential_vertexIdempotent (v : GinzburgQuiver Q) :
    ginzburgTwoDifferential k (vertexIdempotent k v) = 0 := by
  rw [ginzburgTwoDifferential, liftDerivation_vertexIdempotent]

/-- The differential of an arrow is the value prescribed by
`TauCeti.ginzburgTwoArrowRelator`. -/
theorem ginzburgTwoDifferential_ofArrow {i j : GinzburgQuiver Q} (e : i ⟶ j) :
    ginzburgTwoDifferential k (ofArrow e) = ginzburgTwoArrowRelator k e := by
  rw [ginzburgTwoDifferential]
  exact liftDerivation_ofArrow k _ _ (ginzburgTwoArrowRelator_mul_vertexIdempotent k) e

/-- **The two-dimensional Ginzburg Leibniz rule against an arrow.** -/
theorem ginzburgTwoDifferential_ofArrow_mul {i j : GinzburgQuiver Q} (e : i ⟶ j)
    (z : pathAlgebra k (GinzburgQuiver Q)) :
    ginzburgTwoDifferential k (ofArrow e * z) =
      ginzburgTwoArrowRelator k e * z +
        (ginzburgTwoDegree e).negOnePow • (ofArrow e * ginzburgTwoDifferential k z) := by
  rw [ginzburgTwoDifferential]
  exact liftDerivation_ofArrow_mul k _ _ (vertexIdempotent_mul_ginzburgTwoArrowRelator k)
    (ginzburgTwoArrowRelator_mul_vertexIdempotent k) e z

/-- **The doubled arrows are cycles** of the two-dimensional Ginzburg differential graded algebra.
Deliberately not a `simp` lemma: `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already normalizes its
left-hand side. -/
theorem ginzburgTwoDifferential_ofArrow_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgTwoDifferential k (ofArrow (GinzburgHom.double a)) = 0 :=
  (ginzburgTwoDifferential_ofArrow k _).trans (ginzburgTwoArrowRelator_double k a)

/-- **The differential of the adjoined loop `t_i` is the local preprojective relator `ρ_i`**, the
defining equation of the two-dimensional Ginzburg differential graded algebra. Deliberately not a
`simp` lemma: `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already normalizes its left-hand side. -/
theorem ginzburgTwoDifferential_ofArrow_loop (i : Q) :
    ginzburgTwoDifferential k (ofArrow (GinzburgHom.loop i)) =
      ginzburgMap k (localPreprojectiveRelator k i) :=
  (ginzburgTwoDifferential_ofArrow k _).trans (ginzburgTwoArrowRelator_loop k i)

/-! ### The differential graded algebra -/

private theorem ginzburgTwoArrowRelator_mem_gradeBy_ginzburgTwoDegree {i j : Q}
    (e : GinzburgHom Q i j) :
    ginzburgTwoArrowRelator k e ∈
      gradeBy k ginzburgTwoDegree (ginzburgTwoDegree e + 1) := by
  cases e with
  | double a => simp [ginzburgTwoArrowRelator]
  | loop =>
      simpa [ginzburgTwoArrowRelator, ginzburgTwoDegree] using
        ginzburgMap_mem_gradeBy_ginzburgTwoDegree k (localPreprojectiveRelator k i)

/-- **The doubled path algebra consists of cycles**: the differential kills every doubled arrow,
hence every path in them. -/
@[simp]
theorem ginzburgTwoDifferential_ginzburgMap (x : pathAlgebra k (Symmetrify Q)) :
    ginzburgTwoDifferential k (ginzburgMap k x) = 0 := by
  have hpath : ∀ {a b : Symmetrify Q} (p : _root_.Quiver.Path a b),
      ginzburgTwoDifferential k
        (ofPath ⟨ginzburgOf.obj a, ginzburgOf.obj b, ginzburgOf.mapPath p⟩) = 0 := by
    intro a b p
    induction p with
    | nil =>
        rw [Prefunctor.mapPath_nil, ← vertexIdempotent_eq_ofPath,
          ginzburgTwoDifferential_vertexIdempotent]
    | cons p e ih =>
        rw [Prefunctor.mapPath_cons, ← ofArrow_mul_ofPath,
          ginzburgTwoDifferential_ofArrow_mul, ih, mul_zero, smul_zero, add_zero]
        exact mul_eq_zero_of_left (ginzburgTwoArrowRelator_double k e) _
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single y c =>
      obtain ⟨a, b, p⟩ := y
      rw [ginzburgMap, mapAlgHom_single, Prefunctor.mapTotalPath_mk,
        single_eq_smul_ofPath, map_smul, hpath, smul_zero]

private theorem ginzburgTwoDifferential_ginzburgTwoArrowRelator {i j : Q}
    (e : GinzburgHom Q i j) :
    ginzburgTwoDifferential k (ginzburgTwoArrowRelator k e) = 0 := by
  cases e with
  | double a => simp [ginzburgTwoArrowRelator]
  | loop => simp [ginzburgTwoArrowRelator]

/-- **The two-dimensional Ginzburg differential graded algebra** `Π₂(Q)`: the path algebra of the
Ginzburg quiver, graded by the cohomological degree, with the Ginzburg differential. -/
theorem isDGAlgebra_ginzburgTwoDifferential :
    IsDGAlgebra (gradeBy k ginzburgTwoDegree) (ginzburgTwoDifferential (Q := Q) k) := by
  rw [ginzburgTwoDifferential]
  exact isDGAlgebra_liftDerivation k _ _ (vertexIdempotent_mul_ginzburgTwoArrowRelator k)
    (ginzburgTwoArrowRelator_mul_vertexIdempotent k)
    (ginzburgTwoArrowRelator_mem_gradeBy_ginzburgTwoDegree k)
    (ginzburgTwoDifferential_ginzburgTwoArrowRelator k)

/-- **The Leibniz rule for the Ginzburg differential** on a left factor homogeneous of
cohomological degree `m`. -/
theorem ginzburgTwoDifferential_mul {m : ℤ} {x : pathAlgebra k (GinzburgQuiver Q)}
    (hx : x ∈ gradeBy k ginzburgTwoDegree m) (y : pathAlgebra k (GinzburgQuiver Q)) :
    ginzburgTwoDifferential k (x * y) =
      ginzburgTwoDifferential k x * y + m.negOnePow • (x * ginzburgTwoDifferential k y) :=
  (isDGAlgebra_ginzburgTwoDifferential k).leibniz hx y

/-- **The square of the Ginzburg differential vanishes.** -/
@[simp]
theorem ginzburgTwoDifferential_sq_zero (x : pathAlgebra k (GinzburgQuiver Q)) :
    ginzburgTwoDifferential k (ginzburgTwoDifferential k x) = 0 :=
  (isDGAlgebra_ginzburgTwoDifferential k).sq_zero x

/-! ### The Adams grading -/

private theorem ginzburgTwoArrowRelator_mem_gradeBy_ginzburgTwoAdamsDegree
    {i j : Q} (e : GinzburgHom Q i j) :
    ginzburgTwoArrowRelator k e ∈
      gradeBy k ginzburgTwoAdamsDegree (ginzburgTwoAdamsDegree e + 0) := by
  cases e with
  | double a => simp [ginzburgTwoArrowRelator]
  | loop =>
      simpa [ginzburgTwoArrowRelator, ginzburgTwoAdamsDegree] using
        ginzburgMap_mem_gradeBy_ginzburgTwoAdamsDegree k
          (localPreprojectiveRelator_mem_grade_two k i)

/-- **The Ginzburg differential preserves the Adams grading.**  Together with
`TauCeti.isDGAlgebra_ginzburgTwoDifferential` this says that it has bidegree `(1, 0)`. -/
theorem ginzburgTwoDifferential_mem_gradeBy_ginzburgTwoAdamsDegree {n : ℕ}
    {x : pathAlgebra k (GinzburgQuiver Q)} (hx : x ∈ gradeBy k ginzburgTwoAdamsDegree n) :
    ginzburgTwoDifferential k x ∈ gradeBy k ginzburgTwoAdamsDegree n := by
  rw [ginzburgTwoDifferential]
  simpa using liftDerivation_mem_gradeBy k ginzburgTwoDegree (ginzburgTwoArrowRelator k)
    ginzburgTwoAdamsDegree 0 (ginzburgTwoArrowRelator_mem_gradeBy_ginzburgTwoAdamsDegree k) hx

end Differential

end TauCeti
