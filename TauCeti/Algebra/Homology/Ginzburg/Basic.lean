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

The **Ginzburg differential** is the degree `+1` graded derivation which kills every doubled arrow
and sends `t_i` to the local preprojective relator

```text
ρ_i = ∑_{head a = i} a a* - ∑_{tail a = i} a* a
```

of `TauCeti.localPreprojectiveRelator`, read inside the Ginzburg path algebra.  The resulting
differential graded algebra is the non-completed two-dimensional Ginzburg algebra `Π₂(Q)`; its
differential has bidegree `(1, 0)`, raising the cohomological degree by one and preserving the Adams
degree.

## Main definitions

* `TauCeti.GinzburgQuiver`: the Ginzburg quiver of `Q`, with arrows `TauCeti.GinzburgHom`.
* `TauCeti.ginzburgOf`: the inclusion of the doubled quiver, and `TauCeti.ginzburgInclusion` the
  induced homomorphism of path algebras.
* `TauCeti.ginzburgDifferentialArrow`: the prescribed values of the differential on the arrows.
* `TauCeti.ginzburgDegree` and `TauCeti.ginzburgAdamsDegree`: the two arrow weights.
* `TauCeti.ginzburgDifferential`: the Ginzburg differential.

## Main results

* `TauCeti.ginzburgDifferential_ofArrow_loop`: the differential of the loop at `i` is the local
  preprojective relator at `i`, while `TauCeti.ginzburgDifferential_ginzburgInclusion` says that
  the whole doubled path algebra consists of cycles.
* `TauCeti.isDGAlgebra_ginzburgDifferential`: **the Ginzburg differential graded algebra**, for the
  cohomological grading, with `TauCeti.ginzburgDifferential_mul` and
  `TauCeti.ginzburgDifferential_ginzburgDifferential` its Leibniz rule and its vanishing square.
* `TauCeti.ginzburgDifferential_mem_gradeBy_ginzburgAdamsDegree`: **the differential preserves the
  Adams grading**, so that together with the previous result it has bidegree `(1, 0)`.

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

/-- The inclusion of the doubled quiver in the Ginzburg quiver is bijective on vertices. -/
theorem ginzburgOf_obj_bijective : Function.Bijective (ginzburgOf (Q := Q)).obj :=
  Function.bijective_id

/-- The **cohomological degree** of an arrow of the Ginzburg quiver: the doubled arrows sit in
degree `0` and the adjoined loops in degree `-1`. -/
def ginzburgDegree : ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → ℤ
  | _, _, .double _ => 0
  | _, _, .loop _ => -1

/-- The **Adams degree** of an arrow of the Ginzburg quiver: the doubled arrows sit in degree `1`
and the adjoined loops in degree `2`, the degrees for which the differential below is homogeneous
of degree `0`. -/
def ginzburgAdamsDegree : ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → ℕ
  | _, _, .double _ => 1
  | _, _, .loop _ => 2

@[simp]
theorem ginzburgDegree_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgDegree (GinzburgHom.double a) = 0 := by
  simp [ginzburgDegree]

@[simp]
theorem ginzburgDegree_loop (i : Q) : ginzburgDegree (GinzburgHom.loop i) = -1 := by
  simp [ginzburgDegree]

@[simp]
theorem ginzburgAdamsDegree_double {i j : Q}
    (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgAdamsDegree (GinzburgHom.double a) = 1 := by
  simp [ginzburgAdamsDegree]

@[simp]
theorem ginzburgAdamsDegree_loop (i : Q) : ginzburgAdamsDegree (GinzburgHom.loop i) = 2 := by
  simp [ginzburgAdamsDegree]

section Inclusion

variable (k : Type w) [CommRing k] [Finite Q]

/-- The homomorphism from the doubled path algebra to the Ginzburg path algebra induced by the
inclusion of the doubled quiver. -/
noncomputable def ginzburgInclusion :
    pathAlgebra k (Symmetrify Q) →ₐ[k] pathAlgebra k (GinzburgQuiver Q) :=
  mapAlgHom k ginzburgOf ginzburgOf_obj_bijective

/-- The inclusion carries a doubled arrow to the corresponding arrow of the Ginzburg quiver.
Deliberately not a `simp` lemma: `TauCeti.PathAlgebra.ofArrow_eq_ofPath` already normalizes its
left-hand side. -/
theorem ginzburgInclusion_ofArrow {i j : Symmetrify Q} (a : i ⟶ j) :
    ginzburgInclusion k (ofArrow a) = ofArrow (ginzburgOf.map a) :=
  mapAlgHom_ofArrow k _ _ a

@[simp]
theorem ginzburgInclusion_doubledVertexIdempotent (v : Q) :
    ginzburgInclusion k (doubledVertexIdempotent k v) =
      vertexIdempotent k (ginzburgOf.obj (Symmetrify.of.obj v)) := by
  rw [doubledVertexIdempotent_def, ginzburgInclusion, mapAlgHom_vertexIdempotent]

/-! ### The doubled path algebra inside the Ginzburg path algebra -/

omit [Finite Q] in
private theorem addWeight_mapPath_ginzburgDegree {a b : Symmetrify Q}
    (p : _root_.Quiver.Path a b) : (ginzburgOf.mapPath p).addWeight ginzburgDegree = 0 := by
  induction p with
  | nil => simp
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, _root_.Quiver.Path.addWeight_cons, ih, ginzburgOf_map]
      exact (zero_add _).trans (ginzburgDegree_double e)

omit [Finite Q] in
private theorem addWeight_mapPath_ginzburgAdamsDegree {a b : Symmetrify Q}
    (p : _root_.Quiver.Path a b) :
    (ginzburgOf.mapPath p).addWeight ginzburgAdamsDegree = p.length := by
  induction p with
  | nil => simp
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, _root_.Quiver.Path.addWeight_cons, ih, ginzburgOf_map,
        _root_.Quiver.Path.length_cons]
      exact congrArg (p.length + ·) (ginzburgAdamsDegree_double e)

/-- **The doubled path algebra lands in cohomological degree `0`**: it is generated by the arrows
of the doubled quiver, all of which are of degree `0`. -/
theorem ginzburgInclusion_mem_gradeBy_ginzburgDegree (x : pathAlgebra k (Symmetrify Q)) :
    ginzburgInclusion k x ∈ gradeBy k ginzburgDegree 0 := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | single y c =>
      obtain ⟨a, b, p⟩ := y
      rw [ginzburgInclusion, mapAlgHom_single, Prefunctor.mapTotalPath_mk]
      exact single_mem_gradeBy_of_addWeight (addWeight_mapPath_ginzburgDegree p) c

/-- **The doubled path algebra keeps its length grading as the Adams grading.** -/
theorem ginzburgInclusion_mem_gradeBy_ginzburgAdamsDegree {n : ℕ}
    {x : pathAlgebra k (Symmetrify Q)} (hx : x ∈ PathAlgebra.grade k (Symmetrify Q) n) :
    ginzburgInclusion k x ∈ gradeBy k ginzburgAdamsDegree n := by
  rw [grade_eq_span_range] at hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨⟨⟨a, b, p⟩, hy⟩, rfl⟩ := hu
      rw [ginzburgInclusion, mapAlgHom_ofPath, Prefunctor.mapTotalPath_mk]
      exact ofPath_mem_gradeBy_of_addWeight
        ((addWeight_mapPath_ginzburgAdamsDegree p).trans hy)
  | zero => simp
  | add u v _ _ ihu ihv => rw [map_add]; exact add_mem ihu ihv
  | smul c u _ ih => rw [map_smul]; exact Submodule.smul_mem _ c ih

end Inclusion

section Differential

variable (k : Type w) [CommRing k] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]

/-- The value of the Ginzburg differential on an arrow: it kills the doubled arrows and sends the
loop at `i` to the local preprojective relator at `i`. -/
noncomputable def ginzburgDifferentialArrow :
    ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → pathAlgebra k (GinzburgQuiver Q)
  | _, _, .double _ => 0
  | _, _, .loop i => ginzburgInclusion k (localPreprojectiveRelator k i)

@[simp]
theorem ginzburgDifferentialArrow_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgDifferentialArrow k (GinzburgHom.double a) = 0 := by
  simp [ginzburgDifferentialArrow]

@[simp]
theorem ginzburgDifferentialArrow_loop (i : Q) :
    ginzburgDifferentialArrow k (GinzburgHom.loop i) =
      ginzburgInclusion k (localPreprojectiveRelator k i) := by
  simp [ginzburgDifferentialArrow]

private theorem vertexIdempotent_mul_ginzburgDifferentialArrow {i j : Q}
    (e : GinzburgHom Q i j) :
    (vertexIdempotent k j : pathAlgebra k (GinzburgQuiver Q)) * ginzburgDifferentialArrow k e =
      ginzburgDifferentialArrow k e := by
  cases e with
  | double a => simp [ginzburgDifferentialArrow]
  | loop =>
      have h := congrArg (ginzburgInclusion k)
        (doubledVertexIdempotent_mul_localPreprojectiveRelator (Q := Q) k i)
      rw [map_mul, ginzburgInclusion_doubledVertexIdempotent] at h
      simpa [ginzburgDifferentialArrow, ginzburgOf] using h

private theorem ginzburgDifferentialArrow_mul_vertexIdempotent {i j : Q}
    (e : GinzburgHom Q i j) :
    ginzburgDifferentialArrow k e * (vertexIdempotent k i : pathAlgebra k (GinzburgQuiver Q)) =
      ginzburgDifferentialArrow k e := by
  cases e with
  | double a => simp [ginzburgDifferentialArrow]
  | loop =>
      have h := congrArg (ginzburgInclusion k)
        (localPreprojectiveRelator_mul_doubledVertexIdempotent (Q := Q) k i)
      rw [map_mul, ginzburgInclusion_doubledVertexIdempotent] at h
      simpa [ginzburgDifferentialArrow, ginzburgOf] using h

/-- **The Ginzburg differential** of `Q`: the degree `+1` graded derivation of the Ginzburg path
algebra which kills the doubled arrows and sends the loop `t_i` to the local preprojective relator
`ρ_i`. -/
noncomputable def ginzburgDifferential :
    pathAlgebra k (GinzburgQuiver Q) →ₗ[k] pathAlgebra k (GinzburgQuiver Q) :=
  liftDerivation k ginzburgDegree (ginzburgDifferentialArrow k)

@[simp]
theorem ginzburgDifferential_vertexIdempotent (v : GinzburgQuiver Q) :
    ginzburgDifferential k (vertexIdempotent k v) = 0 := by
  rw [ginzburgDifferential, liftDerivation_vertexIdempotent]

/-- The differential of an arrow is the value prescribed by
`TauCeti.ginzburgDifferentialArrow`. -/
theorem ginzburgDifferential_ofArrow {i j : GinzburgQuiver Q} (e : i ⟶ j) :
    ginzburgDifferential k (ofArrow e) = ginzburgDifferentialArrow k e := by
  rw [ginzburgDifferential]
  exact liftDerivation_ofArrow k _ _ (ginzburgDifferentialArrow_mul_vertexIdempotent k) e

/-- **The doubled arrows are cycles** of the Ginzburg differential graded algebra. -/
@[simp]
theorem ginzburgDifferential_ofArrow_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgDifferential k (ofArrow (GinzburgHom.double a)) = 0 :=
  (ginzburgDifferential_ofArrow k _).trans (ginzburgDifferentialArrow_double k a)

/-- **The differential of the adjoined loop `t_i` is the local preprojective relator `ρ_i`**, the
defining equation of the two-dimensional Ginzburg differential graded algebra. -/
@[simp]
theorem ginzburgDifferential_ofArrow_loop (i : Q) :
    ginzburgDifferential k (ofArrow (GinzburgHom.loop i)) =
      ginzburgInclusion k (localPreprojectiveRelator k i) :=
  (ginzburgDifferential_ofArrow k _).trans (ginzburgDifferentialArrow_loop k i)

/-! ### The differential graded algebra -/

private theorem ginzburgDifferentialArrow_mem_gradeBy_ginzburgDegree {i j : Q}
    (e : GinzburgHom Q i j) :
    ginzburgDifferentialArrow k e ∈ gradeBy k ginzburgDegree (ginzburgDegree e + 1) := by
  cases e with
  | double a => simp [ginzburgDifferentialArrow]
  | loop =>
      simpa [ginzburgDifferentialArrow, ginzburgDegree] using
        ginzburgInclusion_mem_gradeBy_ginzburgDegree k (localPreprojectiveRelator k i)

/-- **The doubled path algebra consists of cycles**: the differential kills every doubled arrow,
hence every path in them. -/
@[simp]
theorem ginzburgDifferential_ginzburgInclusion (x : pathAlgebra k (Symmetrify Q)) :
    ginzburgDifferential k (ginzburgInclusion k x) = 0 := by
  have hpath : ∀ {a b : Symmetrify Q} (p : _root_.Quiver.Path a b),
      ginzburgDifferential k
        (ofPath ⟨ginzburgOf.obj a, ginzburgOf.obj b, ginzburgOf.mapPath p⟩) = 0 := by
    intro a b p
    induction p with
    | nil =>
        rw [Prefunctor.mapPath_nil, ← vertexIdempotent_eq_ofPath,
          ginzburgDifferential_vertexIdempotent]
    | cons p e ih =>
        rw [Prefunctor.mapPath_cons, ← ofArrow_mul_ofPath, ginzburgDifferential,
          liftDerivation_ofArrow_mul k _ _ (vertexIdempotent_mul_ginzburgDifferentialArrow k)
            (ginzburgDifferentialArrow_mul_vertexIdempotent k), ← ginzburgDifferential, ih,
          mul_zero, smul_zero, add_zero]
        exact mul_eq_zero_of_left (ginzburgDifferentialArrow_double k e) _
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single y c =>
      obtain ⟨a, b, p⟩ := y
      rw [ginzburgInclusion, mapAlgHom_single, Prefunctor.mapTotalPath_mk,
        single_eq_smul_ofPath, map_smul, hpath, smul_zero]

private theorem ginzburgDifferential_ginzburgDifferentialArrow {i j : Q}
    (e : GinzburgHom Q i j) : ginzburgDifferential k (ginzburgDifferentialArrow k e) = 0 := by
  cases e with
  | double a => simp [ginzburgDifferentialArrow]
  | loop => simp [ginzburgDifferentialArrow]

/-- **The two-dimensional Ginzburg differential graded algebra** `Π₂(Q)`: the path algebra of the
Ginzburg quiver, graded by the cohomological degree, with the Ginzburg differential. -/
theorem isDGAlgebra_ginzburgDifferential :
    IsDGAlgebra (gradeBy k ginzburgDegree) (ginzburgDifferential (Q := Q) k) := by
  rw [ginzburgDifferential]
  exact isDGAlgebra_liftDerivation k _ _ (vertexIdempotent_mul_ginzburgDifferentialArrow k)
    (ginzburgDifferentialArrow_mul_vertexIdempotent k)
    (ginzburgDifferentialArrow_mem_gradeBy_ginzburgDegree k)
    (ginzburgDifferential_ginzburgDifferentialArrow k)

/-- **The Leibniz rule for the Ginzburg differential** on a left factor homogeneous of
cohomological degree `m`. -/
theorem ginzburgDifferential_mul {m : ℤ} {x : pathAlgebra k (GinzburgQuiver Q)}
    (hx : x ∈ gradeBy k ginzburgDegree m) (y : pathAlgebra k (GinzburgQuiver Q)) :
    ginzburgDifferential k (x * y) =
      ginzburgDifferential k x * y + m.negOnePow • (x * ginzburgDifferential k y) :=
  (isDGAlgebra_ginzburgDifferential k).leibniz hx y

/-- **The square of the Ginzburg differential vanishes.** -/
@[simp]
theorem ginzburgDifferential_ginzburgDifferential (x : pathAlgebra k (GinzburgQuiver Q)) :
    ginzburgDifferential k (ginzburgDifferential k x) = 0 :=
  (isDGAlgebra_ginzburgDifferential k).sq_zero x

/-! ### The Adams grading -/

private theorem ginzburgDifferentialArrow_mem_gradeBy_ginzburgAdamsDegree
    {i j : Q} (e : GinzburgHom Q i j) :
    ginzburgDifferentialArrow k e ∈ gradeBy k ginzburgAdamsDegree (ginzburgAdamsDegree e + 0) := by
  cases e with
  | double a => simp [ginzburgDifferentialArrow]
  | loop =>
      simpa [ginzburgDifferentialArrow, ginzburgAdamsDegree] using
        ginzburgInclusion_mem_gradeBy_ginzburgAdamsDegree k
          (localPreprojectiveRelator_mem_grade_two k i)

/-- **The Ginzburg differential preserves the Adams grading.**  Together with
`TauCeti.isDGAlgebra_ginzburgDifferential` this is the statement that it has bidegree `(1, 0)`. -/
theorem ginzburgDifferential_mem_gradeBy_ginzburgAdamsDegree {n : ℕ}
    {x : pathAlgebra k (GinzburgQuiver Q)} (hx : x ∈ gradeBy k ginzburgAdamsDegree n) :
    ginzburgDifferential k x ∈ gradeBy k ginzburgAdamsDegree n := by
  rw [ginzburgDifferential]
  simpa using liftDerivation_mem_gradeBy k ginzburgDegree (ginzburgDifferentialArrow k)
    ginzburgAdamsDegree 0 (ginzburgDifferentialArrow_mem_gradeBy_ginzburgAdamsDegree k) hx

end Differential

end TauCeti
