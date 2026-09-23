/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ginzburg.Basic

/-!
# The loop-count grading of the two-dimensional Ginzburg path algebra

The Ginzburg quiver of a quiver `Q` consists of the doubled arrows and one additional loop `t_i`
at every vertex.  Its cohomological grading gives doubled arrows degree `0` and the loops degree
`-1`.  This file introduces the companion natural-number weight
`TauCeti.ginzburgLoopCount`, which gives the same arrows weights `0` and `1` respectively.

The two path weights contain exactly the same information: the cohomological degree of a path is
the negative of its loop count.  Consequently the cohomological degree `-n` piece is literally the
loop-count degree `n` piece, not merely isomorphic to it, and every positive cohomological piece
vanishes.  In particular, degree zero is spanned precisely by paths containing no adjoined loop.
This is the path decomposition needed to identify the zeroth cohomology of the two-dimensional
Ginzburg DG algebra with the additive preprojective algebra. The image of
`TauCeti.ginzburgMap` is exactly cohomological degree zero, and
`TauCeti.ginzburgRetraction` kills adjoined loops and inverts that map on degree zero.

## Main results

* `Quiver.Path.addWeight_ginzburgTwoDegree_eq_neg_addWeight_ginzburgLoopCount`: the two weights
  of a Ginzburg path differ by sign.
* `TauCeti.gradeBy_ginzburgTwoDegree_neg_eq_gradeBy_ginzburgLoopCount`: the degree `-n`
  cohomological piece is the piece containing exactly `n` adjoined loops.
* `TauCeti.gradeBy_ginzburgTwoDegree_eq_bot_of_pos`: positive cohomological pieces vanish.
* `TauCeti.ginzburgRetraction`: the retraction onto the doubled path algebra.
* `TauCeti.mem_gradeBy_ginzburgTwoDegree_zero_iff`: degree zero is the image of the doubled path
  algebra.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6.5.
* T. Etgü and Y. Lekili, *Koszul duality patterns in Floer theory*, Section 4.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable {Q : Type u} [Quiver.{v} Q]

/-- The number of adjoined Ginzburg loops contributed by an arrow.  A doubled arrow contributes
zero and a loop `t_i` contributes one. -/
def ginzburgLoopCount : ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → ℕ
  | _, _, .double _ => 0
  | _, _, .loop _ => 1

@[simp]
theorem ginzburgLoopCount_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgLoopCount (GinzburgHom.double a) = 0 := by
  simp [ginzburgLoopCount]

@[simp]
theorem ginzburgLoopCount_loop (i : Q) : ginzburgLoopCount (GinzburgHom.loop i) = 1 := by
  simp [ginzburgLoopCount]

/-- On every Ginzburg arrow, cohomological degree is the negative of loop count. -/
theorem ginzburgTwoDegree_eq_neg_ginzburgLoopCount :
    ∀ {i j : GinzburgQuiver Q} (e : i ⟶ j),
      ginzburgTwoDegree e = -((ginzburgLoopCount e : ℕ) : ℤ)
  | _, _, .double a => by
      rw [ginzburgTwoDegree_double (Q := Q), ginzburgLoopCount_double (Q := Q)]
      simp
  | _, _, .loop i => by
      rw [ginzburgTwoDegree_loop (Q := Q), ginzburgLoopCount_loop (Q := Q)]
      simp

/-- The cohomological degree of a Ginzburg path is the negative of its number of adjoined loops. -/
theorem _root_.Quiver.Path.addWeight_ginzburgTwoDegree_eq_neg_addWeight_ginzburgLoopCount
    {i j : GinzburgQuiver Q} (p : Path i j) :
    p.addWeight ginzburgTwoDegree = -((p.addWeight ginzburgLoopCount : ℕ) : ℤ) := by
  induction p with
  | nil => rw [Path.addWeight_nil, Path.addWeight_nil]; rfl
  | cons p e ih =>
      rw [Path.addWeight_cons, Path.addWeight_cons, ih,
        ginzburgTwoDegree_eq_neg_ginzburgLoopCount e]
      push_cast
      omega

/-- A Ginzburg path has cohomological degree `-n` exactly when it contains `n` adjoined loops. -/
@[simp]
theorem _root_.Quiver.Path.addWeight_ginzburgTwoDegree_eq_neg_iff {i j : GinzburgQuiver Q}
    (p : Path i j) (n : ℕ) :
    p.addWeight ginzburgTwoDegree = -(n : ℤ) ↔ p.addWeight ginzburgLoopCount = n := by
  rw [p.addWeight_ginzburgTwoDegree_eq_neg_addWeight_ginzburgLoopCount]
  exact neg_inj.trans Int.ofNat_inj

/-- A Ginzburg path has cohomological degree zero exactly when it contains no adjoined loop. -/
@[simp]
theorem _root_.Quiver.Path.addWeight_ginzburgTwoDegree_eq_zero_iff {i j : GinzburgQuiver Q}
    (p : Path i j) :
    p.addWeight ginzburgTwoDegree = 0 ↔ p.addWeight ginzburgLoopCount = 0 := by
  simpa using p.addWeight_ginzburgTwoDegree_eq_neg_iff 0

/-- Every Ginzburg path has nonpositive cohomological degree. -/
theorem _root_.Quiver.Path.addWeight_ginzburgTwoDegree_nonpos {i j : GinzburgQuiver Q}
    (p : Path i j) :
    p.addWeight ginzburgTwoDegree ≤ 0 := by
  rw [p.addWeight_ginzburgTwoDegree_eq_neg_addWeight_ginzburgLoopCount]
  exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- The loop count pulled back along `TauCeti.ginzburgOf` is the constant weight `0`.  This is
`TauCeti.ginzburgLoopCount_double` for an arrow of `Quiver.Symmetrify Q`, whose type is
definitionally the sum type but does not match it syntactically. -/
private theorem ginzburgLoopCount_ginzburgOf_map {a b : Symmetrify Q} (e : a ⟶ b) :
    ginzburgLoopCount (ginzburgOf.map e) = 0 :=
  ginzburgLoopCount_double e

/-- The inclusion of the doubled quiver contributes no adjoined loops to a path. -/
@[simp]
theorem _root_.Quiver.Path.addWeight_ginzburgLoopCount_mapPath {i j : Symmetrify Q}
    (p : Path i j) :
    (ginzburgOf.mapPath p).addWeight ginzburgLoopCount = 0 := by
  simp only [ginzburgOf.addWeight_mapPath, ginzburgLoopCount_ginzburgOf_map,
    Quiver.Path.addWeight_const, smul_zero]

section Pieces

variable (k : Type w) [Semiring k]

/-- The cohomological degree `-n` part of the Ginzburg path algebra is exactly its loop-count
degree `n` part. -/
theorem gradeBy_ginzburgTwoDegree_neg_eq_gradeBy_ginzburgLoopCount (n : ℕ) :
    gradeBy (Q := GinzburgQuiver Q) k ginzburgTwoDegree (-(n : ℤ)) =
      gradeBy (Q := GinzburgQuiver Q) k ginzburgLoopCount n := by
  ext x
  simp only [mem_gradeBy_iff]
  constructor
  · intro hx p hp
    exact (p.2.2.addWeight_ginzburgTwoDegree_eq_neg_iff n).mp (hx p hp)
  · intro hx p hp
    exact (p.2.2.addWeight_ginzburgTwoDegree_eq_neg_iff n).mpr (hx p hp)

/-- The degree-zero cohomological piece consists exactly of linear combinations of paths with no
adjoined loop. -/
theorem gradeBy_ginzburgTwoDegree_zero_eq_gradeBy_ginzburgLoopCount_zero :
    gradeBy (Q := GinzburgQuiver Q) k ginzburgTwoDegree 0 =
      gradeBy (Q := GinzburgQuiver Q) k ginzburgLoopCount 0 := by
  simpa using gradeBy_ginzburgTwoDegree_neg_eq_gradeBy_ginzburgLoopCount k 0

/-- Every positive cohomological piece of the two-dimensional Ginzburg path algebra vanishes. -/
theorem gradeBy_ginzburgTwoDegree_eq_bot_of_pos {m : ℤ} (hm : 0 < m) :
    gradeBy (Q := GinzburgQuiver Q) k ginzburgTwoDegree m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_gradeBy_iff] at hx
  apply (pathAlgebraBasis k (GinzburgQuiver Q)).repr.injective
  ext p
  by_cases hp : p ∈ ((pathAlgebraBasis k (GinzburgQuiver Q)).repr x).support
  · have hdegree := hx p hp
    have hnonpos := p.2.2.addWeight_ginzburgTwoDegree_nonpos
    omega
  · rw [Finsupp.notMem_support_iff.mp hp]
    simp

end Pieces

section Differential

variable (k : Type w)

/-- The doubled path algebra lands in loop-count degree zero inside the Ginzburg path algebra. -/
theorem ginzburgMap_mem_gradeBy_ginzburgLoopCount_zero [CommSemiring k] [Finite Q]
    (x : pathAlgebra k (Symmetrify Q)) :
    ginzburgMap k x ∈ gradeBy (Q := GinzburgQuiver Q) k ginzburgLoopCount 0 := by
  rw [← gradeBy_ginzburgTwoDegree_zero_eq_gradeBy_ginzburgLoopCount_zero]
  exact ginzburgMap_mem_gradeBy_ginzburgTwoDegree k x

/-- Every cohomological degree-zero element is a cycle in the two-dimensional Ginzburg DG
algebra. -/
theorem ginzburgTwoDifferential_eq_zero_of_mem_gradeBy_zero [CommRing k] [Fintype Q]
    [∀ i j : Q, Fintype (i ⟶ j)] {x : pathAlgebra k (GinzburgQuiver Q)}
    (hx : x ∈ gradeBy (Q := GinzburgQuiver Q) k ginzburgTwoDegree 0) :
    ginzburgTwoDifferential k x = 0 := by
  have hmem := (isDGAlgebra_ginzburgTwoDifferential k).map_mem hx
  rw [gradeBy_ginzburgTwoDegree_eq_bot_of_pos k (by omega)] at hmem
  exact (Submodule.mem_bot k).mp hmem

end Differential

/-! ### Killing the adjoined loops -/

section Retraction

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q]

/-- The image in the doubled path algebra of an arrow of the Ginzburg quiver: the same arrow when
it is a doubled arrow, and zero when it is an adjoined loop. -/
private noncomputable def ginzburgRetractArrow :
    {a b : Q} → GinzburgHom Q a b → pathAlgebra k (Symmetrify Q)
  | _, _, .double e => ofArrow (Q := Symmetrify Q) e
  | _, _, .loop _ => 0

/-- The image in the doubled path algebra of a path of the Ginzburg quiver: the same path when it
uses no adjoined loop, and zero once it does. -/
private noncomputable def ginzburgRetractPath :
    {a b : GinzburgQuiver Q} → Path a b → pathAlgebra k (Symmetrify Q)
  | a, _, .nil => vertexIdempotent (Q := Symmetrify Q) k a
  | _, _, .cons p e => ginzburgRetractArrow k e * ginzburgRetractPath p

-- The vertices of a Ginzburg arrow are terms of `Q`, which the doubled path algebra reads as
-- vertices of `Quiver.Symmetrify Q`; rewriting cannot see through that synonym, so the corner
-- identities of a doubled arrow are supplied below as terms with their quiver named.
/-- The image of a Ginzburg arrow lies in the corner of its target. -/
private theorem vertexIdempotent_mul_ginzburgRetractArrow {a b : Q} (e : GinzburgHom Q a b) :
    vertexIdempotent (Q := Symmetrify Q) k b * ginzburgRetractArrow k e =
      ginzburgRetractArrow k e := by
  cases e with
  | double e =>
    rw [ginzburgRetractArrow]
    exact (congrArg _ (ofArrow_eq_ofPath (Q := Symmetrify Q) e)).trans
      ((vertexIdempotent_mul_ofPath (k := k) (Q := Symmetrify Q)
        (Hom.toPath (V := Symmetrify Q) e)).trans (ofArrow_eq_ofPath (Q := Symmetrify Q) e).symm)
  | loop => rw [ginzburgRetractArrow, mul_zero]

/-- The image of a Ginzburg arrow lies in the corner of its source. -/
private theorem ginzburgRetractArrow_mul_vertexIdempotent {a b : Q} (e : GinzburgHom Q a b) :
    ginzburgRetractArrow k e * vertexIdempotent (Q := Symmetrify Q) k a =
      ginzburgRetractArrow k e := by
  cases e with
  | double e =>
    rw [ginzburgRetractArrow]
    exact (congrArg (· * _) (ofArrow_eq_ofPath (Q := Symmetrify Q) e)).trans
      ((ofPath_mul_vertexIdempotent (k := k) (Q := Symmetrify Q)
        (Hom.toPath (V := Symmetrify Q) e)).trans (ofArrow_eq_ofPath (Q := Symmetrify Q) e).symm)
  | loop => rw [ginzburgRetractArrow, zero_mul]

/-- The image of a Ginzburg path lies in the corner of its target. -/
private theorem vertexIdempotent_mul_ginzburgRetractPath {a b : GinzburgQuiver Q} (p : Path a b) :
    vertexIdempotent (Q := Symmetrify Q) k b * ginzburgRetractPath k p =
      ginzburgRetractPath k p := by
  cases p with
  | nil =>
    rw [ginzburgRetractPath]
    exact vertexIdempotent_mul_self (k := k) (Q := Symmetrify Q) _
  | cons p e =>
    rw [ginzburgRetractPath, ← mul_assoc]
    exact congrArg (· * _) (vertexIdempotent_mul_ginzburgRetractArrow k e)

/-- The image of a Ginzburg path lies in the corner of its source. -/
private theorem ginzburgRetractPath_mul_vertexIdempotent {a b : GinzburgQuiver Q} (p : Path a b) :
    ginzburgRetractPath k p * vertexIdempotent (Q := Symmetrify Q) k a =
      ginzburgRetractPath k p := by
  induction p with
  | nil =>
    rw [ginzburgRetractPath]
    exact vertexIdempotent_mul_self (k := k) (Q := Symmetrify Q) _
  | cons p e ih => rw [ginzburgRetractPath, mul_assoc, ih]

/-- Concatenation of Ginzburg paths becomes multiplication, later factor first. -/
private theorem ginzburgRetractPath_comp {a b c : GinzburgQuiver Q} (p : Path a b)
    (q : Path c a) :
    ginzburgRetractPath k p * ginzburgRetractPath k q = ginzburgRetractPath k (q.comp p) := by
  induction p with
  | nil => rw [Path.comp_nil, ginzburgRetractPath, vertexIdempotent_mul_ginzburgRetractPath]
  | cons p e ih => rw [Path.comp_cons, ginzburgRetractPath, ginzburgRetractPath, mul_assoc, ih]

/-- A doubled path, viewed in the Ginzburg quiver, goes back to itself. -/
private theorem ginzburgRetractPath_mapPath {a b : Symmetrify Q} (p : Path a b) :
    ginzburgRetractPath k (ginzburgOf.mapPath p) = ofPath ⟨a, b, p⟩ := by
  induction p with
  | nil =>
    rw [Prefunctor.mapPath_nil, ginzburgRetractPath]
    exact vertexIdempotent_eq_ofPath (Q := Symmetrify Q) k a
  | cons p e ih =>
    rw [Prefunctor.mapPath_cons, ginzburgRetractPath, ih]
    exact ofArrow_mul_ofPath e p

variable [Finite Q]

private theorem ginzburgRetractPath_hzero {x y : Quiver.TotalPath (GinzburgQuiver Q)}
    (h : y.2.1 ≠ x.1) :
    ginzburgRetractPath k x.2.2 * ginzburgRetractPath k y.2.2 = 0 := by
  rw [← ginzburgRetractPath_mul_vertexIdempotent k x.2.2,
    ← vertexIdempotent_mul_ginzburgRetractPath k y.2.2, mul_assoc,
    ← mul_assoc (vertexIdempotent (Q := Symmetrify Q) k x.1),
    vertexIdempotent_mul_vertexIdempotent_of_ne (Q := Symmetrify Q) (Ne.symm h), zero_mul,
    mul_zero]

private theorem ginzburgRetractPath_hone :
    letI := Fintype.ofFinite (GinzburgQuiver Q)
    ∑ v : GinzburgQuiver Q, ginzburgRetractPath k (Path.nil : Path v v) = 1 := by
  let _ := Fintype.ofFinite (Symmetrify Q)
  exact (Finset.sum_congr rfl fun v _ => by rw [ginzburgRetractPath]).trans
    (one_def (k := k) (Q := Symmetrify Q)).symm

/-- The algebra homomorphism from the Ginzburg path algebra to the doubled path algebra which fixes
the vertex idempotents and the doubled arrows and kills every adjoined loop `t_i`.  A Ginzburg path
goes to itself when it uses no loop, and to zero otherwise. -/
noncomputable def ginzburgRetraction :
    pathAlgebra k (GinzburgQuiver Q) →ₐ[k] pathAlgebra k (Symmetrify Q) :=
  liftAlgHom k (fun x => ginzburgRetractPath k x.2.2) (ginzburgRetractPath_comp k)
    (ginzburgRetractPath_hzero k) (ginzburgRetractPath_hone k)

/-- The retraction fixes every vertex idempotent. -/
@[simp]
theorem ginzburgRetraction_vertexIdempotent (v : GinzburgQuiver Q) :
    ginzburgRetraction k (vertexIdempotent k v) = vertexIdempotent (Q := Symmetrify Q) k v := by
  rw [vertexIdempotent_eq_ofPath, ginzburgRetraction, liftAlgHom_ofPath, ginzburgRetractPath]

/-- The retraction on an arrow of the Ginzburg quiver. -/
private theorem ginzburgRetraction_ofArrow {a b : GinzburgQuiver Q} (e : a ⟶ b) :
    ginzburgRetraction k (ofArrow e) = ginzburgRetractArrow k e := by
  rw [ofArrow_eq_ofPath, ginzburgRetraction, liftAlgHom_ofPath, ← Path.nil_comp (Hom.toPath e),
    Path.comp_toPath_eq_cons, ginzburgRetractPath, ginzburgRetractPath]
  exact ginzburgRetractArrow_mul_vertexIdempotent k e

/-- The retraction kills every adjoined loop. -/
@[simp]
theorem ginzburgRetraction_ofArrow_loop (i : Q) :
    ginzburgRetraction k (ofArrow (GinzburgHom.loop i)) = 0 :=
  ginzburgRetraction_ofArrow k _

/-- **The retraction is a left inverse of the inclusion** of the doubled path algebra. -/
@[simp]
theorem ginzburgRetraction_comp_ginzburgMap :
    (ginzburgRetraction k).comp (ginzburgMap k) = AlgHom.id k (pathAlgebra k (Symmetrify Q)) :=
  algHom_ext k fun x => by
    obtain ⟨a, b, p⟩ := x
    rw [AlgHom.comp_apply, ginzburgMap_ofPath, Prefunctor.mapTotalPath_mk, ginzburgRetraction,
      liftAlgHom_ofPath, ginzburgRetractPath_mapPath, AlgHom.id_apply]

/-- The retraction undoes the inclusion of the doubled path algebra. -/
@[simp]
theorem ginzburgRetraction_ginzburgMap (x : pathAlgebra k (Symmetrify Q)) :
    ginzburgRetraction k (ginzburgMap k x) = x := by
  rw [← AlgHom.comp_apply, ginzburgRetraction_comp_ginzburgMap, AlgHom.id_apply]

/-- The retraction fixes every doubled arrow. -/
@[simp]
theorem ginzburgRetraction_ofArrow_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgRetraction k (ofArrow (GinzburgHom.double a)) =
      ofArrow (Q := Symmetrify Q) (a := i) (b := j) a :=
  (congrArg _ (ginzburgMap_ofArrow k a).symm).trans (ginzburgRetraction_ginzburgMap k _)

/-- The retraction kills an adjoined loop in the path basis. -/
@[simp]
theorem ginzburgRetraction_ofPath_loop (i : Q) :
    ginzburgRetraction k
      (ofPath (Q := GinzburgQuiver Q)
        ⟨i, i, Hom.toPath (V := GinzburgQuiver Q) (GinzburgHom.loop i)⟩) = 0 := by
  rw [← ofArrow_eq_ofPath (k := k) (Q := GinzburgQuiver Q) (GinzburgHom.loop i)]
  exact ginzburgRetraction_ofArrow_loop k i

/-- The retraction sends a doubled arrow to the corresponding doubled path. -/
@[simp]
theorem ginzburgRetraction_ofPath_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgRetraction k
      (ofPath (Q := GinzburgQuiver Q)
        ⟨i, j, Hom.toPath (V := GinzburgQuiver Q) (GinzburgHom.double a)⟩) =
      ofPath (Q := Symmetrify Q) ⟨i, j, Hom.toPath (V := Symmetrify Q) a⟩ := by
  rw [← ofArrow_eq_ofPath (k := k) (Q := GinzburgQuiver Q) (GinzburgHom.double a),
    ← ofArrow_eq_ofPath (k := k) (Q := Symmetrify Q) a]
  exact ginzburgRetraction_ofArrow_double k a

/-- The inclusion of the doubled path algebra in the Ginzburg path algebra is injective. -/
theorem ginzburgMap_injective : Function.Injective (ginzburgMap (Q := Q) k) :=
  Function.LeftInverse.injective (ginzburgRetraction_ginzburgMap k)

/-- A doubled Ginzburg arrow is the image of the doubled arrow it came from. -/
private theorem ginzburgMap_ginzburgRetractArrow {a b : Q} (e : GinzburgHom Q a b)
    (he : ginzburgLoopCount e = 0) :
    ginzburgMap k (ginzburgRetractArrow k e) = ofArrow e := by
  cases e with
  | double e => exact ginzburgMap_ofArrow k e
  | loop => simp at he

/-- A loop-free Ginzburg path is the image of the doubled path obtained by killing its loops. -/
private theorem ginzburgMap_ginzburgRetractPath {a b : GinzburgQuiver Q} (p : Path a b)
    (hp : p.addWeight ginzburgLoopCount = 0) :
    ginzburgMap k (ginzburgRetractPath k p) = ofPath ⟨a, b, p⟩ := by
  induction p with
  | nil =>
    rw [ginzburgRetractPath]
    exact (congrArg (ginzburgMap k) (doubledVertexIdempotent_def (Q := Q) k a).symm).trans
      ((ginzburgMap_doubledVertexIdempotent (Q := Q) k a).trans
        (vertexIdempotent_eq_ofPath (Q := GinzburgQuiver Q) k a))
  | cons p e ih =>
    rw [Path.addWeight_cons, Nat.add_eq_zero_iff] at hp
    rw [ginzburgRetractPath, map_mul, ih hp.1]
    exact (congrArg (· * _) (ginzburgMap_ginzburgRetractArrow k e hp.2)).trans
      (ofArrow_mul_ofPath e p)

/-- **The retraction is a right inverse of the inclusion on cohomological degree `0`.** -/
theorem ginzburgMap_ginzburgRetraction_of_mem {x : pathAlgebra k (GinzburgQuiver Q)}
    (hx : x ∈ gradeBy k ginzburgTwoDegree 0) :
    ginzburgMap k (ginzburgRetraction k x) = x := by
  rw [gradeBy_ginzburgTwoDegree_zero_eq_gradeBy_ginzburgLoopCount_zero, gradeBy_eq_span_range]
    at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨⟨a, b, p⟩, hp⟩, rfl⟩ := hy
    rw [ginzburgRetraction, liftAlgHom_ofPath]
    exact ginzburgMap_ginzburgRetractPath k p hp
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul c y _ hy => rw [map_smul, map_smul, hy]

/-- **Cohomological degree `0` of the Ginzburg path algebra is the doubled path algebra**: an
element has degree `0` exactly when it is the image of an element of the doubled path algebra. -/
theorem mem_gradeBy_ginzburgTwoDegree_zero_iff {x : pathAlgebra k (GinzburgQuiver Q)} :
    x ∈ gradeBy k ginzburgTwoDegree 0 ↔ ∃ y, ginzburgMap k y = x :=
  ⟨fun hx => ⟨_, ginzburgMap_ginzburgRetraction_of_mem k hx⟩,
    fun ⟨y, hy⟩ => hy ▸ ginzburgMap_mem_gradeBy_ginzburgTwoDegree k y⟩

end Retraction

end TauCeti
