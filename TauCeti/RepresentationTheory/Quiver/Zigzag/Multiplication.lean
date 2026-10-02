/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Bilinear
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basis

/-!
# The multiplication table of a zigzag algebra

The zigzag relation quotient `TauCeti.nonisolatedZigzagQuotient` of a simple graph `G` is spanned by
the vertex idempotents `e_i`, the oriented edges `a_d` of the darts of `G`, and the volume classes
`x_i`; `TauCeti.zigzagBasis` shows these are a basis when no vertex is isolated. This file computes
every product of two of them, which is what makes the algebra explicit.

The table is short. The idempotents are orthogonal and act as the local units they are; an arrow is
absorbed by the idempotent at its head on the left and by the one at its tail on the right; a volume
class is absorbed by the idempotent at its base on either side. Two arrows multiply to a volume
class exactly when the later factor is the reverse dart of the earlier one, since a length-two path
survives the relations only if it returns to its source. Everything else vanishes: a product landing
in path length at least three is killed by the long generators, and a product of two paths that do
not meet is already zero in the path algebra.

In Tau Ceti's *later-factor-first* convention the product `a_d * a_e` traverses `e` first, so it is
nonzero exactly when `e = d.symm`, and then it is the volume class at `d.snd`, the vertex where the
composite begins and ends.

All the statements are unconditional: at an isolated vertex the volume class is the junk value `0`,
and each identity below degenerates to a true statement about `0` there.

## Main results

* `TauCeti.zigzagMk_ofArrow_mul_ofArrow_symm` and `TauCeti.zigzagMk_ofArrow_mul_ofArrow_of_ne`: two
  arrows multiply to a volume class when the second is the reverse of the first, and to zero
  otherwise.
* `TauCeti.zigzagMk_ofArrow_mul`: left multiplication by an arrow reads off two coordinates in the
  vertex-arrow-volume basis.
* `TauCeti.zigzagMk_vertexIdempotent_mul_zigzagVolume` and its three companions: the idempotent at
  the base of a volume class is a two-sided unit for it, and the other idempotents kill it.
* `TauCeti.zigzagMk_ofArrow_mul_zigzagVolume`, `TauCeti.zigzagVolume_mul_zigzagMk_ofArrow` and
  `TauCeti.zigzagVolume_mul_zigzagVolume`: every product reaching path length three vanishes.
* `TauCeti.zigzagBasis_mul`: the whole table, as products of basis vectors.
* `TauCeti.zigzagBasis_coord_dart_mul`: the arrow coordinates of a product, which only see the
  idempotents at the two ends of the arrow.
* `TauCeti.zigzagVolume_mul` and `TauCeti.mul_zigzagVolume`: a volume class absorbs only the
  idempotent coordinate at its base.

## References

This is the multiplication table asked for by the first clause of Layer 2 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3, and Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*,
Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

open Classical in
/-- The product index for the vertex--dart--volume basis of the public componentwise
zigzag algebra. `none` denotes a zero product in that algebra. In the nonisolated
relation quotient, a returned volume index at an isolated vertex still denotes
the zero junk value. The left factor is traversed second. -/
noncomputable def zigzagBasisMul : ZigzagBasisIndex G → ZigzagBasisIndex G →
    Option (ZigzagBasisIndex G)
  | .inl i, .inl j => if i = j then some (.inl i) else none
  | .inl i, .inr (.inl d) => if i = d.snd then some (.inr (.inl d)) else none
  | .inl i, .inr (.inr j) => if i = j then some (.inr (.inr j)) else none
  | .inr (.inl d), .inl i => if i = d.fst then some (.inr (.inl d)) else none
  | .inr (.inl d), .inr (.inl e) =>
      if e = d.symm then some (.inr (.inr d.snd)) else none
  | .inr (.inl _), .inr (.inr _) => none
  | .inr (.inr i), .inl j => if i = j then some (.inr (.inr i)) else none
  | .inr (.inr _), .inr (.inl _) => none
  | .inr (.inr _), .inr (.inr _) => none

omit [Finite V] in
open Classical in
/-- The product index of two vertex vectors. -/
@[simp]
theorem zigzagBasisMul_vertex_vertex (i j : V) :
    zigzagBasisMul G (.inl i) (.inl j) =
      (if i = j then some (.inl i) else none : Option (ZigzagBasisIndex G)) := by rfl

omit [Finite V] in
open Classical in
/-- The product index of a vertex vector and a dart vector. -/
@[simp]
theorem zigzagBasisMul_vertex_dart (i : V) (d : G.Dart) :
    zigzagBasisMul G (.inl i) (.inr (.inl d)) =
      (if i = d.snd then some (.inr (.inl d)) else none : Option (ZigzagBasisIndex G)) := by rfl

omit [Finite V] in
open Classical in
/-- The product index of a vertex vector and a volume vector. -/
@[simp]
theorem zigzagBasisMul_vertex_volume (i j : V) :
    zigzagBasisMul G (.inl i) (.inr (.inr j)) =
      (if i = j then some (.inr (.inr j)) else none : Option (ZigzagBasisIndex G)) := by rfl

omit [Finite V] in
open Classical in
/-- The product index of a dart vector and a vertex vector. -/
@[simp]
theorem zigzagBasisMul_dart_vertex (d : G.Dart) (i : V) :
    zigzagBasisMul G (.inr (.inl d)) (.inl i) =
      (if i = d.fst then some (.inr (.inl d)) else none : Option (ZigzagBasisIndex G)) := by rfl

omit [Finite V] in
open Classical in
/-- The product index of two dart vectors. -/
@[simp]
theorem zigzagBasisMul_dart_dart (d e : G.Dart) :
    zigzagBasisMul G (.inr (.inl d)) (.inr (.inl e)) =
      (if e = d.symm then some (.inr (.inr d.snd)) else none :
        Option (ZigzagBasisIndex G)) := by rfl

omit [Finite V] in
/-- A dart vector followed by a volume vector has zero product index. -/
@[simp]
theorem zigzagBasisMul_dart_volume (d : G.Dart) (i : V) :
    zigzagBasisMul G (.inr (.inl d)) (.inr (.inr i)) = none := by rfl

omit [Finite V] in
open Classical in
/-- The product index of a volume vector and a vertex vector. -/
@[simp]
theorem zigzagBasisMul_volume_vertex (i j : V) :
    zigzagBasisMul G (.inr (.inr i)) (.inl j) =
      (if i = j then some (.inr (.inr i)) else none : Option (ZigzagBasisIndex G)) := by rfl

omit [Finite V] in
/-- A volume vector followed by a dart vector has zero product index. -/
@[simp]
theorem zigzagBasisMul_volume_dart (i : V) (d : G.Dart) :
    zigzagBasisMul G (.inr (.inr i)) (.inr (.inl d)) = none := by rfl

omit [Finite V] in
/-- Two volume vectors have zero product index. -/
@[simp]
theorem zigzagBasisMul_volume_volume (i j : V) :
    zigzagBasisMul G (.inr (.inr i)) (.inr (.inr j)) = none := by rfl

/-- The volume class of a vertex with no neighbour is zero: it carries no backtrack. This is the
form of `TauCeti.zigzagVolume_eq_zero_of_isIsolated` that the case splits below produce. -/
private theorem zigzagVolume_eq_zero_of_not_exists_adj {i : V} (h : ¬∃ j, G.Adj i j) :
    zigzagVolume k G i = 0 :=
  zigzagVolume_eq_zero_of_isIsolated k G fun w hw => h ⟨w, hw⟩

/-! ### Products of vertex idempotents -/

/-- A vertex idempotent is idempotent in the zigzag quotient. -/
@[simp]
theorem zigzagMk_vertexIdempotent_mul_self (i : V) :
    zigzagMk k G (vertexIdempotent k (vertex G i)) * zigzagMk k G (vertexIdempotent k (vertex G i))
      = zigzagMk k G (vertexIdempotent k (vertex G i)) := by
  rw [← map_mul, vertexIdempotent_mul_self]

/-- Distinct vertex idempotents are orthogonal in the zigzag quotient. -/
@[simp]
theorem zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne {i j : V} (h : i ≠ j) :
    zigzagMk k G (vertexIdempotent k (vertex G i)) * zigzagMk k G (vertexIdempotent k (vertex G j))
      = 0 := by
  rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne ((vertex_injective G).ne h),
    map_zero]

/-! ### Products of a vertex idempotent and an arrow -/

/-- The vertex idempotent at the head of a dart is a left unit for its arrow. -/
theorem zigzagMk_vertexIdempotent_mul_ofArrow (d : G.Dart) :
    zigzagMk k G (vertexIdempotent k (vertex G d.snd)) * zigzagMk k G (ofArrow (arrow G d.adj))
      = zigzagMk k G (ofArrow (arrow G d.adj)) := by
  rw [← map_mul, vertexIdempotent_mul_ofArrow]

/-- A vertex idempotent away from the head of a dart kills its arrow on the left. -/
theorem zigzagMk_vertexIdempotent_mul_ofArrow_of_ne {v : V} (d : G.Dart) (h : v ≠ d.snd) :
    zigzagMk k G (vertexIdempotent k (vertex G v)) * zigzagMk k G (ofArrow (arrow G d.adj))
      = 0 := by
  rw [← map_mul, vertexIdempotent_mul_ofArrow_of_ne _ _ d.adj h, map_zero]

/-- The vertex idempotent at the tail of a dart is a right unit for its arrow. -/
theorem zigzagMk_ofArrow_mul_vertexIdempotent (d : G.Dart) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagMk k G (vertexIdempotent k (vertex G d.fst))
      = zigzagMk k G (ofArrow (arrow G d.adj)) := by
  rw [← map_mul, ofArrow_mul_vertexIdempotent]

/-- A vertex idempotent away from the tail of a dart kills its arrow on the right. -/
theorem zigzagMk_ofArrow_mul_vertexIdempotent_of_ne {v : V} (d : G.Dart) (h : v ≠ d.fst) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagMk k G (vertexIdempotent k (vertex G v))
      = 0 := by
  rw [← map_mul, ofArrow_mul_vertexIdempotent_of_ne _ _ d.adj h, map_zero]

/-! ### Products of a vertex idempotent and a volume class -/

/-- The vertex idempotent at the base of a volume class is a left unit for it. -/
@[simp]
theorem zigzagMk_vertexIdempotent_mul_zigzagVolume (i : V) :
    zigzagMk k G (vertexIdempotent k (vertex G i)) * zigzagVolume k G i = zigzagVolume k G i := by
  rcases em (∃ j, G.Adj i j) with ⟨j, h⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G h, ← map_mul, vertexIdempotent_mul_backtrackElem]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, mul_zero]

/-- A vertex idempotent away from the base of a volume class kills it on the left. -/
@[simp]
theorem zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne {v i : V} (h : v ≠ i) :
    zigzagMk k G (vertexIdempotent k (vertex G v)) * zigzagVolume k G i = 0 := by
  rcases em (∃ j, G.Adj i j) with ⟨j, hj⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj, ← map_mul,
      vertexIdempotent_mul_backtrackElem_of_ne _ _ hj h, map_zero]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, mul_zero]

/-- The vertex idempotent at the base of a volume class is a right unit for it. -/
@[simp]
theorem zigzagVolume_mul_zigzagMk_vertexIdempotent (i : V) :
    zigzagVolume k G i * zigzagMk k G (vertexIdempotent k (vertex G i)) = zigzagVolume k G i := by
  rcases em (∃ j, G.Adj i j) with ⟨j, h⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G h, ← map_mul, backtrackElem_mul_vertexIdempotent]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, zero_mul]

/-- A vertex idempotent away from the base of a volume class kills it on the right. -/
@[simp]
theorem zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne {v i : V} (h : v ≠ i) :
    zigzagVolume k G i * zigzagMk k G (vertexIdempotent k (vertex G v)) = 0 := by
  rcases em (∃ j, G.Adj i j) with ⟨j, hj⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj, ← map_mul,
      backtrackElem_mul_vertexIdempotent_of_ne _ _ hj h, map_zero]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, zero_mul]

/-! ### Products of two arrows -/

/-- **Traversing a dart and returning is its volume class.** In the later-factor-first convention
the reverse dart is traversed first, so the composite is the backtrack based at the head of `d`. -/
theorem zigzagMk_ofArrow_mul_ofArrow_symm (d : G.Dart) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagMk k G (ofArrow (arrow G d.symm.adj))
      = zigzagVolume k G d.snd := by
  have key : (ofArrow (arrow G d.adj) : pathAlgebra k (DoubledQuiver G))
      * ofArrow (arrow G d.symm.adj) = backtrackElem G k d.symm.adj :=
    ofArrow_symm_mul_ofArrow G k d.symm.adj
  rw [← map_mul, key, zigzagMk_backtrackElem_eq_zigzagVolume]
  -- the backtrack is based at the tail of the reverse dart, which is the head of `d`
  simp

/-- **Two arrows that are not reverse to one another multiply to zero.** Either they do not meet, in
which case the product already vanishes in the path algebra, or they meet and the composite is a
length-two path with distinct endpoints, which the zigzag relations kill. -/
theorem zigzagMk_ofArrow_mul_ofArrow_of_ne {d e : G.Dart} (h : e ≠ d.symm) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagMk k G (ofArrow (arrow G e.adj)) = 0 := by
  obtain ⟨⟨i, j⟩, hd⟩ := d
  obtain ⟨⟨a, b⟩, he⟩ := e
  rcases eq_or_ne b i with rfl | hbi
  · have hne : a ≠ j := fun hab => h (SimpleGraph.Dart.ext _ _ (by simp [hab]))
    rw [← map_mul]
    exact (zigzagMk_eq_zero_iff k G).2 (quadraticZigzagIdeal_le_zigzagIdeal k G
      (ofArrow_mul_ofArrow_mem_quadraticZigzagIdeal k G he hd hne))
  · rw [← map_mul, ofArrow_mul_ofArrow_of_ne G k he hd (Ne.symm hbi), map_zero]

/-! ### Products reaching path length three -/

/-- A product of two path classes vanishes when their total path length is at least three. -/
theorem zigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le
    (x y : Quiver.TotalPath (DoubledQuiver G))
    (h : 3 ≤ x.2.2.length + y.2.2.length) :
    zigzagMk k G (ofPath x * ofPath y) = 0 := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  rcases eq_or_ne d a with rfl | hda
  · rw [ofPath_mul_ofPath_of_comp]
    exact zigzagMk_ofPath_eq_zero_of_three_le k G _
      (by simpa only [_root_.Quiver.Path.length_comp, Nat.add_comm] using h)
  · rw [ofPath_mul_ofPath_of_not_composable hda, map_zero]

/-- An arrow times a volume class vanishes: the composite has path length three. -/
theorem zigzagMk_ofArrow_mul_zigzagVolume (d : G.Dart) (i : V) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * zigzagVolume k G i = 0 := by
  rcases em (∃ j, G.Adj i j) with ⟨j, hj⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj, ← map_mul, backtrackElem_eq_ofPath,
      ofArrow_eq_ofPath_arrowPath]
    exact zigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G _ _
      (by simp [length_backtrackPath, length_arrowPath])
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, mul_zero]

/-- A volume class times an arrow vanishes: the composite has path length three. -/
theorem zigzagVolume_mul_zigzagMk_ofArrow (i : V) (d : G.Dart) :
    zigzagVolume k G i * zigzagMk k G (ofArrow (arrow G d.adj)) = 0 := by
  rcases em (∃ j, G.Adj i j) with ⟨j, hj⟩ | hn
  · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hj, ← map_mul, backtrackElem_eq_ofPath,
      ofArrow_eq_ofPath_arrowPath]
    exact zigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G _ _
      (by simp [length_backtrackPath, length_arrowPath])
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, zero_mul]

/-- Two volume classes multiply to zero: they either do not meet or compose to path length four. -/
@[simp]
theorem zigzagVolume_mul_zigzagVolume (i j : V) :
    zigzagVolume k G i * zigzagVolume k G j = 0 := by
  rcases em (∃ l, G.Adj i l) with ⟨l, hl⟩ | hn
  · rcases em (∃ m, G.Adj j m) with ⟨m, hm⟩ | hn'
    · rw [zigzagVolume_eq_zigzagMk_backtrackElem k G hl,
        zigzagVolume_eq_zigzagMk_backtrackElem k G hm, ← map_mul, backtrackElem_eq_ofPath,
        backtrackElem_eq_ofPath]
      exact zigzagMk_ofPath_mul_ofPath_eq_zero_of_three_le k G _ _
        (by simp [length_backtrackPath])
    · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn', mul_zero]
  · rw [zigzagVolume_eq_zero_of_not_exists_adj k G hn, zero_mul]

/-! ### Left multiplication by an arrow -/

section

variable {k G}

/-- **Left multiplication by an arrow reads off two coordinates.**  Multiplying by the arrow of a
dart `d` keeps only the idempotent at the tail of `d`, which returns the arrow itself, and the
reverse arrow, which returns the volume class at the head of `d`. -/
theorem zigzagMk_ofArrow_mul (hns : ∀ i : V, ∃ j, G.Adj i j) (d : G.Dart)
    (x : nonisolatedZigzagQuotient k G) :
    zigzagMk k G (ofArrow (arrow G d.adj)) * x =
      (zigzagBasis k G hns).coord (.inl d.fst) x • zigzagBasis k G hns (.inr (.inl d)) +
        (zigzagBasis k G hns).coord (.inr (.inl d.symm)) x •
          zigzagBasis k G hns (.inr (.inr d.snd)) := by
  classical
  have key : LinearMap.mulLeft k (zigzagMk k G (ofArrow (arrow G d.adj))) =
      LinearMap.smulRight ((zigzagBasis k G hns).coord (.inl d.fst))
          (zigzagBasis k G hns (.inr (.inl d))) +
        LinearMap.smulRight ((zigzagBasis k G hns).coord (.inr (.inl d.symm)))
          (zigzagBasis k G hns (.inr (.inr d.snd))) := by
    refine (zigzagBasis k G hns).ext fun b => ?_
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.mulLeft_apply,
      zigzagBasis_coord_apply]
    rcases b with j | e | j
    · rcases eq_or_ne j d.fst with rfl | hj
      · rw [ite_eq_left rfl, ite_eq_right (by simp)]
        simp only [zigzagBasis_apply, zigzagBasisFun_inl, zigzagBasisFun_inr_inl,
          zigzagBasisFun_inr_inr, one_smul, zero_smul, add_zero]
        exact zigzagMk_ofArrow_mul_vertexIdempotent k G d
      · rw [ite_eq_right (by simpa using hj), ite_eq_right (by simp)]
        simp only [zigzagBasis_apply, zigzagBasisFun_inl, zigzagBasisFun_inr_inl,
          zigzagBasisFun_inr_inr, zero_smul, add_zero]
        exact zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G d hj
    · rcases eq_or_ne e d.symm with rfl | he
      · rw [ite_eq_right (by simp), ite_eq_left rfl]
        simp only [zigzagBasis_apply, zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr,
          one_smul, zero_smul, zero_add]
        exact zigzagMk_ofArrow_mul_ofArrow_symm k G d
      · rw [ite_eq_right (by simp), ite_eq_right (by simpa using he)]
        simp only [zigzagBasis_apply, zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr,
          zero_smul, add_zero]
        exact zigzagMk_ofArrow_mul_ofArrow_of_ne k G he
    · rw [ite_eq_right (by simp), ite_eq_right (by simp)]
      simp only [zigzagBasis_apply, zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr,
        zero_smul, add_zero]
      exact zigzagMk_ofArrow_mul_zigzagVolume k G d j
  simpa only [LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.mulLeft_apply]
    using congrArg (fun f => f x) key

/-! ### Products and coordinates in the vertex-arrow-volume basis -/

/-- **The multiplication table in the vertex-arrow-volume basis**: the product of two basis
vectors is the basis vector indexed by `TauCeti.zigzagBasisMul`, or zero when that index is
`none`. -/
theorem zigzagBasis_mul (hns : ∀ i : V, ∃ j, G.Adj i j) (b c : ZigzagBasisIndex G) :
    zigzagBasis k G hns b * zigzagBasis k G hns c =
      (zigzagBasisMul G b c).elim 0 (zigzagBasis k G hns) := by
  rcases b with i | d | i <;> rcases c with j | e | j
  all_goals simp only [zigzagBasisMul_vertex_vertex, zigzagBasisMul_vertex_dart,
    zigzagBasisMul_vertex_volume, zigzagBasisMul_dart_vertex, zigzagBasisMul_dart_dart,
    zigzagBasisMul_dart_volume, zigzagBasisMul_volume_vertex, zigzagBasisMul_volume_dart,
    zigzagBasisMul_volume_volume]
  all_goals try split_ifs
  all_goals simp only [Option.elim_some, Option.elim_none, zigzagBasis_apply, zigzagBasisFun_inl,
    zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr]
  all_goals try subst_vars
  all_goals first
    | exact zigzagMk_vertexIdempotent_mul_self k G _
    | exact zigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G (by assumption)
    | exact zigzagMk_vertexIdempotent_mul_ofArrow k G _
    | exact zigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G _ (by assumption)
    | exact zigzagMk_ofArrow_mul_vertexIdempotent k G _
    | exact zigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G _ (by assumption)
    | exact zigzagMk_vertexIdempotent_mul_zigzagVolume k G _
    | exact zigzagMk_vertexIdempotent_mul_zigzagVolume_of_ne k G (by assumption)
    | exact zigzagVolume_mul_zigzagMk_vertexIdempotent k G _
    | exact zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G (Ne.symm (by assumption))
    | exact zigzagMk_ofArrow_mul_ofArrow_symm k G _
    | exact zigzagMk_ofArrow_mul_ofArrow_of_ne k G (by assumption)
    | exact zigzagMk_ofArrow_mul_zigzagVolume k G _ _
    | exact zigzagVolume_mul_zigzagMk_ofArrow k G _ _
    | exact zigzagVolume_mul_zigzagVolume k G _ _

/-- **The arrow coordinates of a product.** The coefficient of the arrow of a dart `d` in `x * y`
pairs the idempotent coordinate of `x` at the head of `d` with the `d`-coordinate of `y`, and the
`d`-coordinate of `x` with the idempotent coordinate of `y` at the tail of `d`: an arrow is a
product only of itself with the idempotents at its two ends. -/
theorem zigzagBasis_coord_dart_mul (hns : ∀ i : V, ∃ j, G.Adj i j) (d : G.Dart)
    (x y : nonisolatedZigzagQuotient k G) :
    (zigzagBasis k G hns).coord (.inr (.inl d)) (x * y) =
      (zigzagBasis k G hns).coord (.inl d.snd) x * (zigzagBasis k G hns).coord (.inr (.inl d)) y +
        (zigzagBasis k G hns).coord (.inr (.inl d)) x *
          (zigzagBasis k G hns).coord (.inl d.fst) y := by
  classical
  have key : (LinearMap.mul k (nonisolatedZigzagQuotient k G)).compr₂
        ((zigzagBasis k G hns).coord (.inr (.inl d))) =
      (LinearMap.mul k k).compl₁₂ ((zigzagBasis k G hns).coord (.inl d.snd))
          ((zigzagBasis k G hns).coord (.inr (.inl d))) +
        (LinearMap.mul k k).compl₁₂ ((zigzagBasis k G hns).coord (.inr (.inl d)))
          ((zigzagBasis k G hns).coord (.inl d.fst)) := by
    refine LinearMap.ext_basis (zigzagBasis k G hns) (zigzagBasis k G hns) fun b c => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.add_apply,
      LinearMap.compl₁₂_apply, zigzagBasis_mul, zigzagBasis_coord_apply]
    rcases b with i | e | i <;> rcases c with j | f | j <;>
      simp only [zigzagBasisMul_vertex_vertex, zigzagBasisMul_vertex_dart,
        zigzagBasisMul_vertex_volume, zigzagBasisMul_dart_vertex, zigzagBasisMul_dart_dart,
        zigzagBasisMul_dart_volume, zigzagBasisMul_volume_vertex, zigzagBasisMul_volume_dart,
        zigzagBasisMul_volume_volume] <;>
      split_ifs <;>
      simp only [Option.elim_some, Option.elim_none, map_zero, zigzagBasis_coord_apply] <;>
      simp_all
  simpa only [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.add_apply,
    LinearMap.compl₁₂_apply] using LinearMap.congr_fun₂ key x y

/-- A volume class absorbs, from the left, only the idempotent at its base vertex. -/
theorem zigzagVolume_mul (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V)
    (y : nonisolatedZigzagQuotient k G) :
    zigzagVolume k G i * y = (zigzagBasis k G hns).coord (.inl i) y • zigzagVolume k G i := by
  classical
  have hv : zigzagVolume k G i = zigzagBasis k G hns (.inr (.inr i)) := by simp
  have key : LinearMap.mulLeft k (zigzagVolume k G i) =
      ((zigzagBasis k G hns).coord (.inl i)).smulRight (zigzagVolume k G i) := by
    refine (zigzagBasis k G hns).ext fun c => ?_
    rw [LinearMap.mulLeft_apply, LinearMap.smulRight_apply, hv, zigzagBasis_mul,
      zigzagBasis_coord_apply]
    rcases c with j | e | j <;>
      simp only [zigzagBasisMul_volume_vertex, zigzagBasisMul_volume_dart,
        zigzagBasisMul_volume_volume] <;>
      split_ifs <;>
      simp only [Option.elim_some, Option.elim_none] <;>
      simp_all
  simpa only [LinearMap.mulLeft_apply, LinearMap.smulRight_apply] using
    LinearMap.congr_fun key y

/-- A volume class absorbs, from the right, only the idempotent at its base vertex. -/
theorem mul_zigzagVolume (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V)
    (x : nonisolatedZigzagQuotient k G) :
    x * zigzagVolume k G i = (zigzagBasis k G hns).coord (.inl i) x • zigzagVolume k G i := by
  classical
  have hv : zigzagVolume k G i = zigzagBasis k G hns (.inr (.inr i)) := by simp
  have key : LinearMap.mulRight k (zigzagVolume k G i) =
      ((zigzagBasis k G hns).coord (.inl i)).smulRight (zigzagVolume k G i) := by
    refine (zigzagBasis k G hns).ext fun b => ?_
    rw [LinearMap.mulRight_apply, LinearMap.smulRight_apply, hv, zigzagBasis_mul,
      zigzagBasis_coord_apply]
    rcases b with j | e | j <;>
      simp only [zigzagBasisMul_vertex_volume, zigzagBasisMul_dart_volume,
        zigzagBasisMul_volume_volume] <;>
      split_ifs <;>
      simp only [Option.elim_some, Option.elim_none] <;>
      simp_all
  simpa only [LinearMap.mulRight_apply, LinearMap.smulRight_apply] using
    LinearMap.congr_fun key x

/-- A volume class has no arrow component. -/
theorem zigzagBasis_coord_dart_zigzagVolume (hns : ∀ i : V, ∃ j, G.Adj i j) (d : G.Dart)
    (i : V) : (zigzagBasis k G hns).coord (.inr (.inl d)) (zigzagVolume k G i) = 0 := by
  classical
  rw [← zigzagBasisFun_inr_inr, ← zigzagBasis_apply k G hns, zigzagBasis_coord_apply]
  simp

end

end TauCeti
