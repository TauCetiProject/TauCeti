/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ginzburg.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.CyclicDerivative

/-!
# The three-dimensional Ginzburg differential graded algebra of a quiver with potential

Let `Q` be a finite quiver and `W ∈ kQ` a *potential*, typically a linear combination of cycles;
only its cycles matter, since the cyclic derivative of a path which is not a cycle vanishes.  The
**three-dimensional Ginzburg differential graded algebra** `Γ₃(Q, W)` is the path algebra of the
Ginzburg quiver `TauCeti.GinzburgQuiver Q` (the doubled quiver of `Q` with one extra loop `t_i` at
every vertex), graded cohomologically by putting

* the original arrows `a` of `Q` in degree `0`,
* their formal reverses `a*` in degree `-1`, and
* the adjoined loops `t_i` in degree `-2`,

with the degree `+1` graded derivation `d` given on the arrows by

```text
d a = 0,    d a* = ∂_a W,    d t_i = ρ_i = ∑_{head a = i} a a* - ∑_{tail a = i} a* a,
```

where `∂_a` is the cyclic derivative `TauCeti.PathAlgebra.cyclicDerivative` and `ρ_i` the local
preprojective relator `TauCeti.localPreprojectiveRelator`.  The words `a a*` and `a* a` are read in
Tau Ceti's later-factor-first convention, as in the two-dimensional Ginzburg algebra of
`TauCeti.Algebra.Homology.Ginzburg.Basic`.

The quiver is the one of the two-dimensional Ginzburg algebra `Π₂(Q)`, but the grading and the
differential differ, so the two differential graded algebras are distinct.  The square of `d`
vanishes on `a` and on `a*` because the path algebra of `Q` consists of cycles of `d`; on `t_i`,

```text
d (d t_i) = ∑_{head a = i} a ∂_a W - ∑_{tail a = i} ∂_a W a,
```

which vanishes by the local cyclic identity
`TauCeti.PathAlgebra.sum_ofArrow_mul_cyclicDerivative_eq_sum_cyclicDerivative_mul_ofArrow`.

## Main definitions

* `TauCeti.ginzburgThreeDegree`: the cohomological degrees of the arrows of the Ginzburg quiver.
* `TauCeti.ginzburgThreeArrowRelator`: the prescribed values of the differential on the arrows.
* `TauCeti.ginzburgThreeDifferential`: the three-dimensional Ginzburg differential of `(Q, W)`.

## Main results

* `TauCeti.ginzburgThreeDifferential_ofArrow_reverse` and
  `TauCeti.ginzburgThreeDifferential_ofArrow_loop`: the differential of a reverse arrow `a*` is the
  cyclic derivative `∂_a W`, and that of the loop `t_i` is the local preprojective relator `ρ_i`.
* `TauCeti.ginzburgThreeDifferential_ginzburgOriginalMap`: the path algebra of `Q` consists of
  cycles.
* `TauCeti.isDGAlgebra_ginzburgThreeDifferential`: **the three-dimensional Ginzburg differential
  graded algebra** `Γ₃(Q, W)`, with `TauCeti.ginzburgThreeDifferential_mul` and
  `TauCeti.ginzburgThreeDifferential_sq_zero` its Leibniz rule and vanishing square.
* `TauCeti.ginzburgThreeDifferential_add_mul_sub_mul`: the differential only depends on the
  potential up to cyclic equivalence.

## References

* V. Ginzburg, *Calabi--Yau algebras*, Section 4.2.
* B. Keller, *Deformed Calabi--Yau completions*, Section 6.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable {Q : Type u} [Quiver.{v} Q]

/-- The **cohomological degree** of an arrow of the Ginzburg quiver in the three-dimensional
Ginzburg algebra: the original arrows of `Q` sit in degree `0`, their formal reverses in degree
`-1`, and the adjoined loops in degree `-2`. -/
def ginzburgThreeDegree : ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → ℤ
  | _, _, .double (.inl _) => 0
  | _, _, .double (.inr _) => -1
  | _, _, .loop _ => -2

@[simp]
theorem ginzburgThreeDegree_double_inl {i j : Q} (a : i ⟶ j) :
    ginzburgThreeDegree (GinzburgHom.double (Sum.inl a) : GinzburgHom Q i j) = 0 := by
  simp [ginzburgThreeDegree]

@[simp]
theorem ginzburgThreeDegree_double_inr {i j : Q} (a : j ⟶ i) :
    ginzburgThreeDegree (GinzburgHom.double (Sum.inr a) : GinzburgHom Q i j) = -1 := by
  simp [ginzburgThreeDegree]

@[simp]
theorem ginzburgThreeDegree_loop (i : Q) : ginzburgThreeDegree (GinzburgHom.loop i) = -2 := by
  simp [ginzburgThreeDegree]

section Map

variable {k : Type w} [CommSemiring k] [Finite Q]

omit [Finite Q] in
/-- An original arrow has cohomological degree `0`. -/
private theorem ofArrow_double_inl_mem_gradeBy {i j : Q} (a : i ⟶ j) :
    (ofArrow (GinzburgHom.double (Sum.inl a) : GinzburgHom Q i j) :
      pathAlgebra k (GinzburgQuiver Q)) ∈ gradeBy k ginzburgThreeDegree 0 := by
  have h := ofArrow_mem_gradeBy (k := k) ginzburgThreeDegree
    (GinzburgHom.double (Sum.inl a) : GinzburgHom Q i j)
  rwa [ginzburgThreeDegree_double_inl] at h

omit [Finite Q] in
/-- The reverse of an arrow has cohomological degree `-1`. -/
private theorem ofArrow_double_inr_mem_gradeBy {i j : Q} (a : j ⟶ i) :
    (ofArrow (GinzburgHom.double (Sum.inr a) : GinzburgHom Q i j) :
      pathAlgebra k (GinzburgQuiver Q)) ∈ gradeBy k ginzburgThreeDegree (-1) := by
  have h := ofArrow_mem_gradeBy (k := k) ginzburgThreeDegree
    (GinzburgHom.double (Sum.inr a) : GinzburgHom Q i j)
  rwa [ginzburgThreeDegree_double_inr] at h

/-- **The path algebra of `Q` lands in cohomological degree `0`**: it is generated by the original
arrows, all of which have degree `0`. -/
theorem ginzburgOriginalMap_mem_gradeBy_ginzburgThreeDegree (x : pathAlgebra k Q) :
    ginzburgOriginalMap k x ∈ gradeBy k ginzburgThreeDegree 0 := by
  have hpath : ∀ {a b : Q} (p : _root_.Quiver.Path a b),
      ginzburgOriginalMap k (ofPath ⟨a, b, p⟩) ∈ gradeBy k ginzburgThreeDegree 0 := by
    intro a b p
    induction p with
    | nil =>
        rw [← vertexIdempotent_eq_ofPath, ginzburgOriginalMap_vertexIdempotent]
        exact vertexIdempotent_mem_gradeBy_zero _ _
    | cons p e ih =>
        rw [← ofArrow_mul_ofPath, map_mul, ginzburgOriginalMap_ofArrow, ← zero_add 0]
        exact gradeBy_mul_gradeBy_le _ _
          (Submodule.mul_mem_mul (ofArrow_double_inl_mem_gradeBy e) ih)
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | single y c =>
      rw [single_eq_smul_ofPath, map_smul]
      exact Submodule.smul_mem _ c (hpath y.2.2)

/-- The image of the head backtrack `a a*` is the product of the original arrow and its reverse. -/
private theorem ginzburgMap_headBacktrackElem {i j : Q} (a : i ⟶ j) :
    ginzburgMap k (headBacktrackElem k a) =
      ginzburgOriginalMap k (ofArrow a) *
        ofArrow (GinzburgHom.double (Sum.inr a) : GinzburgHom Q j i) := by
  rw [← ofArrow_mul_ofArrow_reverse_eq_headBacktrackElem, map_mul, ginzburgMap_ofArrow,
    ginzburgMap_ofArrow, ginzburgOriginalMap_ofArrow]
  rfl

/-- The image of the tail backtrack `a* a` is the product of the reverse and the original arrow. -/
private theorem ginzburgMap_tailBacktrackElem {i j : Q} (a : i ⟶ j) :
    ginzburgMap k (tailBacktrackElem k a) =
      ofArrow (GinzburgHom.double (Sum.inr a) : GinzburgHom Q j i) *
        ginzburgOriginalMap k (ofArrow a) := by
  rw [← ofArrow_reverse_mul_ofArrow_eq_tailBacktrackElem, map_mul, ginzburgMap_ofArrow,
    ginzburgMap_ofArrow, ginzburgOriginalMap_ofArrow]
  rfl

end Map

section Differential

variable (k : Type w) [CommRing k] [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]
  (W : pathAlgebra k Q)

/-- The relator assigned to an arrow in the three-dimensional Ginzburg differential of `(Q, W)`:
zero on the original arrows, the cyclic derivative `∂_a W` on the reverse `a*` of an arrow `a`,
and the local preprojective relator at the vertex of an adjoined loop. -/
noncomputable def ginzburgThreeArrowRelator :
    ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → pathAlgebra k (GinzburgQuiver Q)
  | _, _, .double (.inl _) => 0
  | _, _, .double (.inr a) => ginzburgOriginalMap k (cyclicDerivative k a W)
  | _, _, .loop i => ginzburgMap k (localPreprojectiveRelator k i)

@[simp]
theorem ginzburgThreeArrowRelator_double_inl {i j : Q} (a : i ⟶ j) :
    ginzburgThreeArrowRelator k W (GinzburgHom.double (Sum.inl a) : GinzburgHom Q i j) = 0 := by
  simp [ginzburgThreeArrowRelator]

@[simp]
theorem ginzburgThreeArrowRelator_double_inr {i j : Q} (a : j ⟶ i) :
    ginzburgThreeArrowRelator k W (GinzburgHom.double (Sum.inr a) : GinzburgHom Q i j) =
      ginzburgOriginalMap k (cyclicDerivative k a W) := by
  simp [ginzburgThreeArrowRelator]

@[simp]
theorem ginzburgThreeArrowRelator_loop (i : Q) :
    ginzburgThreeArrowRelator k W (GinzburgHom.loop i) =
      ginzburgMap k (localPreprojectiveRelator k i) := by
  simp [ginzburgThreeArrowRelator]

private theorem vertexIdempotent_mul_ginzburgThreeArrowRelator {i j : Q}
    (e : GinzburgHom Q i j) :
    (vertexIdempotent k j : pathAlgebra k (GinzburgQuiver Q)) * ginzburgThreeArrowRelator k W e =
      ginzburgThreeArrowRelator k W e := by
  rcases e with (a | a) | i
  · simp
  · rw [ginzburgThreeArrowRelator_double_inr, ← ginzburgOriginalMap_vertexIdempotent, ← map_mul,
      vertexIdempotent_mul_cyclicDerivative]
  · have h := congrArg (ginzburgMap (Q := Q) k)
      (doubledVertexIdempotent_mul_localPreprojectiveRelator (Q := Q) k i)
    rw [map_mul, ginzburgMap_doubledVertexIdempotent (Q := Q)] at h
    simpa using h

private theorem ginzburgThreeArrowRelator_mul_vertexIdempotent {i j : Q}
    (e : GinzburgHom Q i j) :
    ginzburgThreeArrowRelator k W e * (vertexIdempotent k i : pathAlgebra k (GinzburgQuiver Q)) =
      ginzburgThreeArrowRelator k W e := by
  rcases e with (a | a) | i
  · simp
  · rw [ginzburgThreeArrowRelator_double_inr, ← ginzburgOriginalMap_vertexIdempotent, ← map_mul,
      cyclicDerivative_mul_vertexIdempotent]
  · have h := congrArg (ginzburgMap (Q := Q) k)
      (localPreprojectiveRelator_mul_doubledVertexIdempotent (Q := Q) k i)
    rw [map_mul, ginzburgMap_doubledVertexIdempotent (Q := Q)] at h
    simpa using h

/-- **The three-dimensional Ginzburg differential** of `(Q, W)`: the degree `+1` graded derivation
which kills the original arrows, sends the reverse `a*` of an arrow `a` to the cyclic derivative
`∂_a W`, and sends the loop `t_i` to the local preprojective relator `ρ_i`. -/
noncomputable def ginzburgThreeDifferential :
    pathAlgebra k (GinzburgQuiver Q) →ₗ[k] pathAlgebra k (GinzburgQuiver Q) :=
  liftDerivation k ginzburgThreeDegree (ginzburgThreeArrowRelator k W)

@[simp]
theorem ginzburgThreeDifferential_vertexIdempotent (v : GinzburgQuiver Q) :
    ginzburgThreeDifferential k W (vertexIdempotent k v) = 0 := by
  rw [ginzburgThreeDifferential, liftDerivation_vertexIdempotent]

/-- The differential of an arrow is the value prescribed by
`TauCeti.ginzburgThreeArrowRelator`. -/
theorem ginzburgThreeDifferential_ofArrow {i j : GinzburgQuiver Q} (e : i ⟶ j) :
    ginzburgThreeDifferential k W (ofArrow e) = ginzburgThreeArrowRelator k W e := by
  rw [ginzburgThreeDifferential]
  exact liftDerivation_ofArrow k _ _ (ginzburgThreeArrowRelator_mul_vertexIdempotent k W) e

/-- **The three-dimensional Ginzburg Leibniz rule against an arrow.** -/
theorem ginzburgThreeDifferential_ofArrow_mul {i j : GinzburgQuiver Q} (e : i ⟶ j)
    (z : pathAlgebra k (GinzburgQuiver Q)) :
    ginzburgThreeDifferential k W (ofArrow e * z) =
      ginzburgThreeArrowRelator k W e * z +
        (ginzburgThreeDegree e).negOnePow • (ofArrow e * ginzburgThreeDifferential k W z) := by
  rw [ginzburgThreeDifferential]
  exact liftDerivation_ofArrow_mul k _ _ (vertexIdempotent_mul_ginzburgThreeArrowRelator k W)
    (ginzburgThreeArrowRelator_mul_vertexIdempotent k W) e z

/-- **The original arrows are cycles** of the three-dimensional Ginzburg differential. -/
@[simp]
theorem ginzburgThreeDifferential_ofArrow_original {i j : Q} (a : i ⟶ j) :
    ginzburgThreeDifferential k W
        (ofArrow (GinzburgHom.double (Sum.inl a) : GinzburgHom Q i j)) = 0 :=
  (ginzburgThreeDifferential_ofArrow k W _).trans (ginzburgThreeArrowRelator_double_inl k W a)

/-- **The differential of the reverse `a*` of an arrow `a` is the cyclic derivative `∂_a W`.** -/
@[simp]
theorem ginzburgThreeDifferential_ofArrow_reverse {i j : Q} (a : j ⟶ i) :
    ginzburgThreeDifferential k W
        (ofArrow (GinzburgHom.double (Sum.inr a) : GinzburgHom Q i j)) =
      ginzburgOriginalMap k (cyclicDerivative k a W) :=
  (ginzburgThreeDifferential_ofArrow k W _).trans (ginzburgThreeArrowRelator_double_inr k W a)

/-- **The differential of the adjoined loop `t_i` is the local preprojective relator `ρ_i`.** -/
@[simp]
theorem ginzburgThreeDifferential_ofArrow_loop (i : Q) :
    ginzburgThreeDifferential k W (ofArrow (GinzburgHom.loop i)) =
      ginzburgMap k (localPreprojectiveRelator k i) :=
  (ginzburgThreeDifferential_ofArrow k W _).trans (ginzburgThreeArrowRelator_loop k W i)

/-- **The path algebra of `Q` consists of cycles**: the differential kills every original arrow,
hence every path in them. -/
@[simp]
theorem ginzburgThreeDifferential_ginzburgOriginalMap (x : pathAlgebra k Q) :
    ginzburgThreeDifferential k W (ginzburgOriginalMap k x) = 0 := by
  have hpath : ∀ {a b : Q} (p : _root_.Quiver.Path a b),
      ginzburgThreeDifferential k W (ginzburgOriginalMap k (ofPath ⟨a, b, p⟩)) = 0 := by
    intro a b p
    induction p with
    | nil =>
        rw [← vertexIdempotent_eq_ofPath, ginzburgOriginalMap_vertexIdempotent]
        exact ginzburgThreeDifferential_vertexIdempotent k W _
    | cons p e ih =>
        rw [← ofArrow_mul_ofPath, map_mul, ginzburgOriginalMap_ofArrow]
        refine (ginzburgThreeDifferential_ofArrow_mul k W _ _).trans ?_
        rw [ih, mul_zero, smul_zero, add_zero]
        exact mul_eq_zero_of_left (ginzburgThreeArrowRelator_double_inl k W e) _
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | single y c => rw [single_eq_smul_ofPath, map_smul, map_smul, hpath, smul_zero]

/-! ### The differential graded algebra -/

private theorem ginzburgThreeArrowRelator_mem_gradeBy {i j : Q} (e : GinzburgHom Q i j) :
    ginzburgThreeArrowRelator k W e ∈
      gradeBy k ginzburgThreeDegree (ginzburgThreeDegree e + 1) := by
  rcases e with (a | a) | i
  · simp
  · simpa using ginzburgOriginalMap_mem_gradeBy_ginzburgThreeDegree (cyclicDerivative k a W)
  · -- Both backtracks of an arrow consist of an arrow of degree `0` and one of degree `-1`.
    have hhead : ∀ {i j : Q} (a : i ⟶ j), ginzburgMap k (headBacktrackElem k a) ∈
        gradeBy k ginzburgThreeDegree (-1) := fun a => by
      rw [ginzburgMap_headBacktrackElem, ← zero_add (-1 : ℤ)]
      exact gradeBy_mul_gradeBy_le _ _ (Submodule.mul_mem_mul
        (ginzburgOriginalMap_mem_gradeBy_ginzburgThreeDegree _) (ofArrow_double_inr_mem_gradeBy a))
    have htail : ∀ {i j : Q} (a : i ⟶ j), ginzburgMap k (tailBacktrackElem k a) ∈
        gradeBy k ginzburgThreeDegree (-1) := fun a => by
      rw [ginzburgMap_tailBacktrackElem, ← add_zero (-1 : ℤ)]
      exact gradeBy_mul_gradeBy_le _ _ (Submodule.mul_mem_mul
        (ofArrow_double_inr_mem_gradeBy a) (ginzburgOriginalMap_mem_gradeBy_ginzburgThreeDegree _))
    rw [ginzburgThreeArrowRelator_loop, ginzburgThreeDegree_loop, localPreprojectiveRelator_def,
      map_sub, map_sum, map_sum]
    norm_num only
    exact sub_mem (Submodule.sum_mem _ fun i _ => by
      rw [map_sum]; exact Submodule.sum_mem _ fun a _ => hhead a)
      (Submodule.sum_mem _ fun j _ => by
        rw [map_sum]; exact Submodule.sum_mem _ fun a _ => htail a)

/-- **The square of the differential vanishes on the adjoined loops**: `d (d t_i)` is
`∑_{head a = i} a ∂_a W - ∑_{tail a = i} ∂_a W a`, which vanishes by the local cyclic identity. -/
private theorem ginzburgThreeDifferential_ginzburgMap_localPreprojectiveRelator (i : Q) :
    ginzburgThreeDifferential k W (ginzburgMap k (localPreprojectiveRelator k i)) = 0 := by
  have hhead : ∀ {i j : Q} (a : i ⟶ j), ginzburgThreeDifferential k W
      (ginzburgMap k (headBacktrackElem k a)) =
        ginzburgOriginalMap k (ofArrow a * cyclicDerivative k a W) := fun a => by
    rw [ginzburgMap_headBacktrackElem, ginzburgOriginalMap_ofArrow]
    refine (ginzburgThreeDifferential_ofArrow_mul k W _ _).trans ?_
    rw [ginzburgThreeArrowRelator_double_inl, zero_mul, zero_add, ginzburgThreeDegree_double_inl,
      Int.negOnePow_zero, one_smul,
      ginzburgThreeDifferential_ofArrow_reverse, map_mul, ginzburgOriginalMap_ofArrow]
  have htail : ∀ {i j : Q} (a : i ⟶ j), ginzburgThreeDifferential k W
      (ginzburgMap k (tailBacktrackElem k a)) =
        ginzburgOriginalMap k (cyclicDerivative k a W * ofArrow a) := fun a => by
    rw [ginzburgMap_tailBacktrackElem]
    refine (ginzburgThreeDifferential_ofArrow_mul k W _ _).trans ?_
    rw [ginzburgThreeArrowRelator_double_inr, ginzburgThreeDifferential_ginzburgOriginalMap,
      mul_zero, smul_zero, add_zero, map_mul]
  rw [localPreprojectiveRelator_def, map_sub, map_sub]
  simp only [map_sum, hhead, htail]
  rw [sub_eq_zero]
  simpa only [map_sum] using congrArg (ginzburgOriginalMap k)
    (sum_ofArrow_mul_cyclicDerivative_eq_sum_cyclicDerivative_mul_ofArrow W i)

private theorem ginzburgThreeDifferential_ginzburgThreeArrowRelator {i j : Q}
    (e : GinzburgHom Q i j) :
    ginzburgThreeDifferential k W (ginzburgThreeArrowRelator k W e) = 0 := by
  rcases e with (a | a) | i
  · simp
  · simp
  · rw [ginzburgThreeArrowRelator_loop,
      ginzburgThreeDifferential_ginzburgMap_localPreprojectiveRelator]

/-- **The three-dimensional Ginzburg differential graded algebra** `Γ₃(Q, W)`: the path algebra of
the Ginzburg quiver, graded by `TauCeti.ginzburgThreeDegree`, with the Ginzburg differential of the
potential `W`. -/
theorem isDGAlgebra_ginzburgThreeDifferential :
    IsDGAlgebra (gradeBy k ginzburgThreeDegree) (ginzburgThreeDifferential (Q := Q) k W) := by
  rw [ginzburgThreeDifferential]
  exact isDGAlgebra_liftDerivation k _ _ (vertexIdempotent_mul_ginzburgThreeArrowRelator k W)
    (ginzburgThreeArrowRelator_mul_vertexIdempotent k W)
    (ginzburgThreeArrowRelator_mem_gradeBy k W)
    (ginzburgThreeDifferential_ginzburgThreeArrowRelator k W)

/-- **The Leibniz rule for the three-dimensional Ginzburg differential** on a left factor
homogeneous of cohomological degree `m`. -/
theorem ginzburgThreeDifferential_mul {m : ℤ} {x : pathAlgebra k (GinzburgQuiver Q)}
    (hx : x ∈ gradeBy k ginzburgThreeDegree m) (y : pathAlgebra k (GinzburgQuiver Q)) :
    ginzburgThreeDifferential k W (x * y) =
      ginzburgThreeDifferential k W x * y + m.negOnePow • (x * ginzburgThreeDifferential k W y) :=
  (isDGAlgebra_ginzburgThreeDifferential k W).leibniz hx y

/-- **The square of the three-dimensional Ginzburg differential vanishes.** -/
@[simp]
theorem ginzburgThreeDifferential_sq_zero (x : pathAlgebra k (GinzburgQuiver Q)) :
    ginzburgThreeDifferential k W (ginzburgThreeDifferential k W x) = 0 :=
  (isDGAlgebra_ginzburgThreeDifferential k W).sq_zero x

/-- **The three-dimensional Ginzburg differential only depends on the potential up to cyclic
equivalence**: adding a commutator `x y - y x` to `W` does not change it. -/
theorem ginzburgThreeDifferential_add_mul_sub_mul (x y : pathAlgebra k Q) :
    ginzburgThreeDifferential k (W + (x * y - y * x)) = ginzburgThreeDifferential k W := by
  have hrel : ∀ {i j : Q} (e : GinzburgHom Q i j),
      ginzburgThreeArrowRelator k (W + (x * y - y * x)) e = ginzburgThreeArrowRelator k W e := by
    intro i j e
    rcases e with (a | a) | i
    · rw [ginzburgThreeArrowRelator_double_inl, ginzburgThreeArrowRelator_double_inl]
    · rw [ginzburgThreeArrowRelator_double_inr, ginzburgThreeArrowRelator_double_inr, map_add,
        map_sub, cyclicDerivative_mul_comm, sub_self, add_zero]
    · rw [ginzburgThreeArrowRelator_loop, ginzburgThreeArrowRelator_loop]
  exact (liftDerivation_unique k ginzburgThreeDegree _
    (vertexIdempotent_mul_ginzburgThreeArrowRelator k _)
    (ginzburgThreeArrowRelator_mul_vertexIdempotent k _) (ginzburgThreeDifferential k W)
    (ginzburgThreeDifferential_vertexIdempotent k W) (ginzburgThreeDifferential_mul k W)
    fun e => (ginzburgThreeDifferential_ofArrow k W e).trans (hrel e).symm).symm

end Differential

end TauCeti
