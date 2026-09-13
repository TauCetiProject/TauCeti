/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basis
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Basic

/-!
# The basis and dimension of a skew-zigzag relation quotient

A skew-zigzag parameter `c` labels each ordered pair of incident edges of a finite simple graph by
a unit-valued ratio, and `TauCeti.skewZigzagQuotient` imposes `backtrack(h) = c.ratio h h' •
backtrack(h')` on top of the relations killing non-returning quadratic paths and paths of length at
least three. This file proves that the resulting algebra has the same vertex, arrow and volume
basis as the ordinary zigzag relation quotient, and hence the same dimension `2|V| + 2|E|`.

Unlike the ordinary relation quotient, a skew quotient has no canonical volume class: the
backtracks based at a vertex are unit multiples of one another rather than equal. Every statement
below therefore carries a choice `t` of one incident edge at every vertex, and the third block of
the basis is the class of the backtrack along the chosen edge.

The proof does not repeat the ordinary independence argument. Instead it rescales the path basis:
the linear map fixing every path except the backtrack of a dart `d`, which it multiplies by the
ratio from `d` to the edge chosen at the base of `d`, carries the skew relation ideal into the
ordinary zigzag relation ideal, because it turns the skew backtrack relator at a vertex into a unit
multiple of the ordinary one. The rescaling fixes each of the three blocks of basis paths — the
chosen backtrack has ratio one with itself — so a vanishing combination of the skew classes is a
vanishing combination of the ordinary ones, and
`TauCeti.linearIndependent_zigzagBasisFun` finishes the argument. Spanning is immediate from the
skew relations, as in the ordinary case.

Two consequences worth naming: no backtrack dies in a skew quotient, whatever the parameter, and
the skew quotient is linearly isomorphic to the ordinary one by a map matching the two bases. The
isomorphism is only linear; identifying the two *algebras* is the separate classification question
which Couture's `H¹(G, kˣ)` theorem answers.

## Main definitions

* `TauCeti.skewZigzagVolume`: the volume class of a vertex relative to a chosen incident edge.
* `TauCeti.skewZigzagBasisFun`: the vertex, arrow and chosen-volume family.
* `TauCeti.skewZigzagBasis`: that family, as a basis of the skew-zigzag relation quotient.
* `TauCeti.skewZigzagQuotientLinearEquiv`: the induced linear isomorphism with the ordinary zigzag
  relation quotient.

## Main results

* `TauCeti.linearIndependent_skewZigzagBasisFun` and
  `TauCeti.span_range_skewZigzagBasisFun_eq_top`: the family is independent and spans.
* `TauCeti.skewZigzagMk_backtrackElem_ne_zero` and `TauCeti.skewZigzagVolume_ne_zero`: no backtrack
  class vanishes.
* `TauCeti.finrank_skewZigzagQuotient`: the dimension is `2|V| + 2|E|`, as in the ordinary case.

## References

This is the skew half of the basis and dimension clauses of Layer 2 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`, which asks for the basis, centre and trace
calculations to be extended to skew parameters. See C. Couture, *Skew-Zigzag Algebras*, Section 3,
https://arxiv.org/abs/1509.08405, and S. Huerfano and M. Khovanov, *A category for the adjoint
representation*, Section 3, https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V)
  (c : SkewZigzagParameter k G) (t : ∀ i : V, {j : V // G.Adj i j})

/-! ### The backtracks of darts -/

/-- The backtrack along a dart, as an indexed path of the doubled quiver. -/
private def dartBacktrack (d : G.Dart) : Quiver.TotalPath (DoubledQuiver G) :=
  ⟨vertex G d.fst, vertex G d.fst, backtrackPath G d.adj⟩

private theorem length_dartBacktrack (d : G.Dart) : (dartBacktrack G d).2.2.length = 2 :=
  length_backtrackPath G d.adj

private theorem dartBacktrack_injective : Function.Injective (dartBacktrack G) := by
  rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, ha'b'⟩ hxy
  simp only [dartBacktrack] at hxy
  have h1 : a = a' := by simpa using congrArg Sigma.fst hxy
  subst h1
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hxy
  have h2 : b = b' := eq_of_backtrackPath_eq G hxy
  subst h2
  rfl

/-- The dart chosen at a vertex by a choice of incident edges. -/
private def baseDart (i : V) : G.Dart := ⟨(i, (t i).1), (t i).2⟩

/-! ### The rescaling of the path basis -/

/-- The scalar by which the rescaling multiplies the backtrack along a dart: the ratio from that
backtrack to the one chosen at its base vertex. -/
private def dartScale (d : G.Dart) : kˣ := c.ratio d.adj (t d.fst).2

open scoped Classical in
/-- The scalar by which the rescaling multiplies a path of the doubled quiver: the dart scale on
the backtrack of a dart, and one on every other path. -/
private noncomputable def pathScale (x : Quiver.TotalPath (DoubledQuiver G)) : kˣ :=
  if h : ∃ d : G.Dart, x = dartBacktrack G d then dartScale k G c t h.choose else 1

private theorem pathScale_dartBacktrack (d : G.Dart) :
    pathScale k G c t (dartBacktrack G d) = dartScale k G c t d := by
  have hex : ∃ d' : G.Dart, dartBacktrack G d = dartBacktrack G d' := ⟨d, rfl⟩
  rw [pathScale, dite_eq_left hex]
  exact congrArg (dartScale k G c t) (dartBacktrack_injective G hex.choose_spec).symm

private theorem dartScale_baseDart (i : V) : dartScale k G c t (baseDart G t i) = 1 := by
  rw [dartScale]
  exact c.ratio_self _

private theorem pathScale_eq_one (x : Quiver.TotalPath (DoubledQuiver G))
    (hx : ∀ d : G.Dart, x ≠ dartBacktrack G d) : pathScale k G c t x = 1 := by
  rw [pathScale, dite_eq_right (not_exists.mpr hx)]

variable [Finite V]

/-- The value on a path of the rescaling below: the path scaled by its path scale. -/
private noncomputable def pathCoord (x : Quiver.TotalPath (DoubledQuiver G)) :
    pathAlgebra k (DoubledQuiver G) :=
  (pathScale k G c t x : k) • ofPath x

/-- The rescaling of the path basis of the doubled path algebra which turns the skew relations into
the ordinary ones. -/
private noncomputable def skewRescale :
    pathAlgebra k (DoubledQuiver G) →ₗ[k] pathAlgebra k (DoubledQuiver G) :=
  liftLinear k (pathCoord k G c t)

private theorem skewRescale_ofPath (x : Quiver.TotalPath (DoubledQuiver G)) :
    skewRescale k G c t (ofPath x) = (pathScale k G c t x : k) • ofPath x := by
  rw [skewRescale, liftLinear_ofPath, pathCoord]

private theorem skewRescale_ofPath_of_forall_ne (x : Quiver.TotalPath (DoubledQuiver G))
    (hx : ∀ d : G.Dart, x ≠ dartBacktrack G d) :
    skewRescale k G c t (ofPath x) = ofPath x := by
  rw [skewRescale_ofPath, pathScale_eq_one k G c t x hx, Units.val_one, one_smul]

private theorem skewRescale_ofPath_of_length_ne_two {a b : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (hp : p.length ≠ 2) :
    skewRescale k G c t (ofPath ⟨a, b, p⟩) = ofPath ⟨a, b, p⟩ :=
  skewRescale_ofPath_of_forall_ne k G c t _ fun d hd => hp (by
    have hlen := congrArg (fun z : Quiver.TotalPath (DoubledQuiver G) => z.2.2.length) hd
    rw [length_dartBacktrack] at hlen
    exact hlen)

private theorem skewRescale_ofPath_of_ne {a b : DoubledQuiver G} (p : _root_.Quiver.Path a b)
    (hne : b ≠ a) : skewRescale k G c t (ofPath ⟨a, b, p⟩) = ofPath ⟨a, b, p⟩ := by
  refine skewRescale_ofPath_of_forall_ne k G c t _ fun d hd => hne ?_
  have h1 : a = vertex G d.fst := congrArg Sigma.fst hd
  have h2 : b = vertex G d.fst :=
    congrArg (fun z : Quiver.TotalPath (DoubledQuiver G) => z.2.1) hd
  rw [h1, h2]

private theorem skewRescale_backtrackPath {i j : V} (h : G.Adj i j) :
    skewRescale k G c t (ofPath ⟨vertex G i, vertex G i, backtrackPath G h⟩)
      = (c.ratio h (t i).2 : k) •
        (ofPath ⟨vertex G i, vertex G i, backtrackPath G h⟩ : pathAlgebra k (DoubledQuiver G)) := by
  have hx : (⟨vertex G i, vertex G i, backtrackPath G h⟩ :
      Quiver.TotalPath (DoubledQuiver G)) = dartBacktrack G ⟨(i, j), h⟩ := rfl
  rw [hx, skewRescale_ofPath, pathScale_dartBacktrack, dartScale]

omit [Finite V] in
/-- Sandwiching between two trivial paths changes nothing. -/
private theorem ofPath_sandwich_of_length_zero {a b m n : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r : _root_.Quiver.Path m a) (q : _root_.Quiver.Path n m)
    (hp : p.length = 0) (hq : q.length = 0) :
    (ofPath ⟨a, b, p⟩ * ofPath ⟨m, a, r⟩ * ofPath ⟨n, m, q⟩ : pathAlgebra k (DoubledQuiver G))
      = ofPath ⟨m, a, r⟩ := by
  obtain rfl := p.eq_of_length_zero hp
  obtain rfl := p.eq_nil_of_length_zero hp
  obtain rfl := q.eq_of_length_zero hq
  obtain rfl := q.eq_nil_of_length_zero hq
  rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp, _root_.Quiver.Path.comp_nil,
    _root_.Quiver.Path.nil_comp]

/-! ### The rescaling carries the skew relations to the ordinary ones -/

private theorem smul_mem_zigzagIdeal {x : pathAlgebra k (DoubledQuiver G)} (a : k)
    (hx : x ∈ zigzagIdeal k G) : a • x ∈ zigzagIdeal k G := by
  rw [Algebra.smul_def]
  exact TwoSidedIdeal.mul_mem_left _ _ _ hx

private theorem skewRescale_mem_of_three_le {a b : DoubledQuiver G} (p : _root_.Quiver.Path a b)
    (hp : 3 ≤ p.length) : skewRescale k G c t (ofPath ⟨a, b, p⟩) ∈ zigzagIdeal k G := by
  rw [skewRescale_ofPath_of_length_ne_two k G c t p (by omega)]
  exact mem_zigzagIdeal_of_isZigzagRelator k G (IsZigzagRelator.long_path ⟨a, b, p⟩ hp)

/-- A path of length at least two sandwiched between two composable paths of positive total length
is a path of length at least three, which the rescaling fixes and the zigzag relations kill. -/
private theorem skewRescale_sandwich_of_pos {a b m n : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r : _root_.Quiver.Path m a) (q : _root_.Quiver.Path n m)
    (hr : 2 ≤ r.length) (hpq : 0 < p.length + q.length) :
    skewRescale k G c t (ofPath ⟨a, b, p⟩ * ofPath ⟨m, a, r⟩ * ofPath ⟨n, m, q⟩)
      ∈ zigzagIdeal k G := by
  rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp]
  refine skewRescale_mem_of_three_le k G c t _ ?_
  rw [_root_.Quiver.Path.length_comp, _root_.Quiver.Path.length_comp]
  omega

/-- Sandwiching between two paths a path of length at least two whose rescaling already lies in the
zigzag relation ideal lands in that ideal again. -/
private theorem skewRescale_sandwich_ofPath {a b m n e f : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r : _root_.Quiver.Path m n) (q : _root_.Quiver.Path e f)
    (hr : 2 ≤ r.length) (hmem : skewRescale k G c t (ofPath ⟨m, n, r⟩) ∈ zigzagIdeal k G) :
    skewRescale k G c t (ofPath ⟨a, b, p⟩ * ofPath ⟨m, n, r⟩ * ofPath ⟨e, f, q⟩)
      ∈ zigzagIdeal k G := by
  by_cases hna : n = a
  · subst hna
    by_cases hfm : f = m
    · subst hfm
      rcases Nat.eq_zero_or_pos (p.length + q.length) with hlen | hlen
      · rw [ofPath_sandwich_of_length_zero k G p r q (by omega) (by omega)]
        exact hmem
      · exact skewRescale_sandwich_of_pos k G c t p r q hr hlen
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_not_composable hfm, map_zero]
      exact zero_mem _
  · rw [ofPath_mul_ofPath_of_not_composable hna, zero_mul, map_zero]
    exact zero_mem _

private theorem skewRescale_sandwich_nonreturn {a b m n e f : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r : _root_.Quiver.Path m n) (q : _root_.Quiver.Path e f)
    (hr : r.length = 2) (hmn : m ≠ n) :
    skewRescale k G c t (ofPath ⟨a, b, p⟩ * ofPath ⟨m, n, r⟩ * ofPath ⟨e, f, q⟩)
      ∈ zigzagIdeal k G :=
  skewRescale_sandwich_ofPath k G c t p r q hr.ge <| by
    rw [skewRescale_ofPath_of_ne k G c t r (Ne.symm hmn)]
    exact mem_zigzagIdeal_of_isZigzagRelator k G
      (IsZigzagRelator.quadratic (IsQuadraticZigzagRelator.nonreturn r hr hmn))

private theorem skewRescale_sandwich_long {a b m n e f : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (r : _root_.Quiver.Path m n) (q : _root_.Quiver.Path e f)
    (hr : 3 ≤ r.length) :
    skewRescale k G c t (ofPath ⟨a, b, p⟩ * ofPath ⟨m, n, r⟩ * ofPath ⟨e, f, q⟩)
      ∈ zigzagIdeal k G :=
  skewRescale_sandwich_ofPath k G c t p r q (by omega) (skewRescale_mem_of_three_le k G c t r hr)

/-- **The rescaling turns a skew backtrack relator into an ordinary one.** Sandwiched between two
trivial paths the relator becomes a unit multiple of the difference of the two backtracks, by the
cocycle identity for the ratios; sandwiched between anything longer both of its terms become paths
of length at least three. -/
private theorem skewRescale_sandwich_backtrack {a b e f : DoubledQuiver G}
    (p : _root_.Quiver.Path a b) (q : _root_.Quiver.Path e f) {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') :
    skewRescale k G c t (ofPath ⟨a, b, p⟩ *
        (backtrackElem G k h - (c.ratio h h' : k) • backtrackElem G k h') * ofPath ⟨e, f, q⟩)
      ∈ zigzagIdeal k G := by
  rw [backtrackElem_eq_ofPath, backtrackElem_eq_ofPath, mul_sub, mul_smul_comm, sub_mul,
    smul_mul_assoc, map_sub, map_smul]
  by_cases hai : vertex G i = a
  · subst hai
    by_cases hfi : f = vertex G i
    · subst hfi
      rcases Nat.eq_zero_or_pos (p.length + q.length) with hlen | hlen
      · rw [ofPath_sandwich_of_length_zero k G p (backtrackPath G h) q (by omega) (by omega),
          ofPath_sandwich_of_length_zero k G p (backtrackPath G h') q (by omega) (by omega),
          skewRescale_backtrackPath, skewRescale_backtrackPath, smul_smul, ← Units.val_mul,
          SkewZigzagParameter.ratio_mul_ratio, ← smul_sub, ← backtrackElem_eq_ofPath,
          ← backtrackElem_eq_ofPath]
        exact smul_mem_zigzagIdeal k G _ (quadraticZigzagIdeal_le_zigzagIdeal k G
          (backtrackElem_sub_backtrackElem_mem_quadraticZigzagIdeal k G h h'))
      · exact sub_mem (skewRescale_sandwich_of_pos k G c t p (backtrackPath G h) q
          (length_backtrackPath G h).ge hlen)
          (smul_mem_zigzagIdeal k G _ (skewRescale_sandwich_of_pos k G c t p
            (backtrackPath G h') q (length_backtrackPath G h').ge hlen))
    · rw [ofPath_mul_ofPath_of_comp, ofPath_mul_ofPath_of_comp,
        ofPath_mul_ofPath_of_not_composable hfi, ofPath_mul_ofPath_of_not_composable hfi,
        map_zero, smul_zero, sub_zero]
      exact zero_mem _
  · rw [ofPath_mul_ofPath_of_not_composable hai, ofPath_mul_ofPath_of_not_composable hai,
      zero_mul, map_zero, smul_zero, sub_zero]
    exact zero_mem _

private theorem skewRescale_ofPath_mul_relator_mul_ofPath {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsSkewZigzagRelator k G c x) (pu pv : Quiver.TotalPath (DoubledQuiver G)) :
    skewRescale k G c t (ofPath pu * x * ofPath pv) ∈ zigzagIdeal k G := by
  obtain ⟨a, b, p⟩ := pu
  obtain ⟨e, f, q⟩ := pv
  cases hx with
  | nonreturn r hlen hij => exact skewRescale_sandwich_nonreturn k G c t p r q hlen hij
  | backtrack_ratio h h' => exact skewRescale_sandwich_backtrack k G c t p q h h'
  | long_path z hz =>
    obtain ⟨m, n, r⟩ := z
    exact skewRescale_sandwich_long k G c t p r q hz

private theorem skewRescale_mul_relator_mul {x : pathAlgebra k (DoubledQuiver G)}
    (hx : IsSkewZigzagRelator k G c x) (u v : pathAlgebra k (DoubledQuiver G)) :
    skewRescale k G c t (u * x * v) ∈ zigzagIdeal k G := by
  induction u using PathAlgebra.induction_linear with
  | zero => rw [zero_mul, zero_mul, map_zero]; exact zero_mem _
  | add u₁ u₂ hu₁ hu₂ => rw [add_mul, add_mul, map_add]; exact add_mem hu₁ hu₂
  | single pu cu =>
    induction v using PathAlgebra.induction_linear with
    | zero => rw [mul_zero, map_zero]; exact zero_mem _
    | add v₁ v₂ hv₁ hv₂ => rw [mul_add, map_add]; exact add_mem hv₁ hv₂
    | single pv cv =>
      rw [single_eq_smul_ofPath, single_eq_smul_ofPath, smul_mul_assoc, smul_mul_assoc,
        mul_smul_comm, map_smul, map_smul]
      exact smul_mem_zigzagIdeal k G _ (smul_mem_zigzagIdeal k G _
        (skewRescale_ofPath_mul_relator_mul_ofPath k G c t hx pu pv))

/-- **The rescaling carries the skew relation ideal into the ordinary one.** -/
private theorem skewRescale_mem_zigzagIdeal {x : pathAlgebra k (DoubledQuiver G)}
    (hx : x ∈ skewZigzagIdeal k G c) : skewRescale k G c t x ∈ zigzagIdeal k G := by
  rw [skewZigzagIdeal_eq_span, TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨w, hw, v, -, rfl⟩ := hy
    obtain ⟨u, -, r, hr, rfl⟩ := hw
    exact skewRescale_mul_relator_mul k G c t hr u v
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

/-! ### The volume classes -/

/-- The volume class of a vertex in a skew-zigzag relation quotient, relative to a choice of an
incident edge at every vertex: the class of the backtrack along the chosen edge. Unlike the
ordinary volume class of `TauCeti.zigzagVolume` it genuinely depends on that choice, the backtracks
at a vertex being unit multiples of one another rather than equal. -/
noncomputable def skewZigzagVolume (i : V) : skewZigzagQuotient k G c :=
  skewZigzagMk k G c (backtrackElem G k (t i).2)

/-- The volume class of a vertex is the class of the backtrack along the chosen incident edge. -/
theorem skewZigzagVolume_eq_skewZigzagMk_backtrackElem (i : V) :
    skewZigzagVolume k G c t i = skewZigzagMk k G c (backtrackElem G k (t i).2) := (rfl)

/-- The class of any backtrack is the prescribed unit multiple of the volume class of its base
vertex. -/
theorem skewZigzagMk_backtrackElem_eq_smul_skewZigzagVolume {i j : V} (h : G.Adj i j) :
    skewZigzagMk k G c (backtrackElem G k h)
      = (c.ratio h (t i).2 : k) • skewZigzagVolume k G c t i :=
  skewZigzagMk_backtrackElem_eq_smul k G c h (t i).2

/-! ### The basis -/

/-- The paths underlying the basis family: the trivial path at a vertex, the arrow of a dart, and
the backtrack along the chosen edge at a vertex. -/
private def skewBasisPath : ZigzagBasisIndex G → Quiver.TotalPath (DoubledQuiver G)
  | .inl i => ⟨vertex G i, vertex G i, _root_.Quiver.Path.nil⟩
  | .inr (.inl d) => ⟨vertex G d.fst, vertex G d.snd, arrowPath G d.adj⟩
  | .inr (.inr i) => dartBacktrack G (baseDart G t i)

/-- The vertex, arrow and volume family of a skew-zigzag relation quotient: the class of a vertex
idempotent, the class of the arrow of a dart, and the volume class of a vertex relative to the
chosen incident edge. -/
noncomputable def skewZigzagBasisFun : ZigzagBasisIndex G → skewZigzagQuotient k G c
  | .inl i => skewZigzagMk k G c (vertexIdempotent k (vertex G i))
  | .inr (.inl d) => skewZigzagMk k G c (ofArrow (arrow G d.adj))
  | .inr (.inr i) => skewZigzagVolume k G c t i

@[simp]
theorem skewZigzagBasisFun_inl (i : V) :
    skewZigzagBasisFun k G c t (.inl i) = skewZigzagMk k G c (vertexIdempotent k (vertex G i)) :=
  (rfl)

@[simp]
theorem skewZigzagBasisFun_inr_inl (d : G.Dart) :
    skewZigzagBasisFun k G c t (.inr (.inl d)) = skewZigzagMk k G c (ofArrow (arrow G d.adj)) :=
  (rfl)

@[simp]
theorem skewZigzagBasisFun_inr_inr (i : V) :
    skewZigzagBasisFun k G c t (.inr (.inr i)) = skewZigzagVolume k G c t i := (rfl)

private theorem skewZigzagMk_ofPath_skewBasisPath (b : ZigzagBasisIndex G) :
    skewZigzagMk k G c (ofPath (skewBasisPath G t b)) = skewZigzagBasisFun k G c t b := by
  rcases b with i | d | i
  · simp only [skewBasisPath, skewZigzagBasisFun_inl, vertexIdempotent_eq_single, ofPath_eq_single]
  · simp only [skewBasisPath, skewZigzagBasisFun_inr_inl, ofArrow_eq_ofPath_arrowPath]
  · rw [skewBasisPath, skewZigzagBasisFun_inr_inr, skewZigzagVolume_eq_skewZigzagMk_backtrackElem,
      backtrackElem_eq_ofPath]
    rfl

private theorem zigzagMk_ofPath_skewBasisPath (b : ZigzagBasisIndex G) :
    zigzagMk k G (ofPath (skewBasisPath G t b)) = zigzagBasisFun k G b := by
  rcases b with i | d | i
  · simp only [skewBasisPath, zigzagBasisFun_inl, vertexIdempotent_eq_single, ofPath_eq_single]
  · simp only [skewBasisPath, zigzagBasisFun_inr_inl, ofArrow_eq_ofPath_arrowPath]
  · rw [skewBasisPath, zigzagBasisFun_inr_inr,
      show (ofPath (dartBacktrack G (baseDart G t i)) : pathAlgebra k (DoubledQuiver G))
        = backtrackElem G k (t i).2 from (backtrackElem_eq_ofPath G k (t i).2).symm,
      zigzagMk_backtrackElem_eq_zigzagVolume]

/-- The rescaling fixes every basis path: the chosen backtrack has ratio one with itself. -/
private theorem skewRescale_ofPath_skewBasisPath (b : ZigzagBasisIndex G) :
    skewRescale k G c t (ofPath (skewBasisPath G t b)) = ofPath (skewBasisPath G t b) := by
  rcases b with i | d | i
  · exact skewRescale_ofPath_of_length_ne_two k G c t _ (by simp)
  · exact skewRescale_ofPath_of_length_ne_two k G c t _ (by simp)
  · rw [skewBasisPath, skewRescale_ofPath, pathScale_dartBacktrack, dartScale_baseDart,
      Units.val_one, one_smul]

/-- **The vertex, arrow and volume classes of a skew-zigzag quotient are independent.** -/
theorem linearIndependent_skewZigzagBasisFun :
    LinearIndependent k (skewZigzagBasisFun k G c t) := by
  rw [linearIndependent_iff]
  intro l hl
  have hcomp : skewZigzagBasisFun k G c t = ⇑(skewZigzagMk k G c).toLinearMap ∘
      fun b : ZigzagBasisIndex G => (ofPath (skewBasisPath G t b)) := by
    funext b
    rw [Function.comp_apply, AlgHom.toLinearMap_apply, skewZigzagMk_ofPath_skewBasisPath k G c t b]
  rw [hcomp, ← Finsupp.apply_linearCombination, AlgHom.toLinearMap_apply] at hl
  have hzz := skewRescale_mem_zigzagIdeal k G c t ((skewZigzagMk_eq_zero_iff k G c).mp hl)
  rw [Finsupp.apply_linearCombination] at hzz
  have hfix : (Finsupp.linearCombination k (⇑(skewRescale k G c t) ∘
      fun b : ZigzagBasisIndex G => (ofPath (skewBasisPath G t b))) l)
      = Finsupp.linearCombination k
        (fun b : ZigzagBasisIndex G => (ofPath (skewBasisPath G t b))) l :=
    congrArg (fun f => Finsupp.linearCombination k f l)
      (funext fun b => skewRescale_ofPath_skewBasisPath k G c t b)
  rw [hfix] at hzz
  refine linearIndependent_iff.mp
    (linearIndependent_zigzagBasisFun k G fun i => ⟨(t i).1, (t i).2⟩) l ?_
  have hcomp' : zigzagBasisFun k G = ⇑(zigzagMk k G).toLinearMap ∘
      fun b : ZigzagBasisIndex G => (ofPath (skewBasisPath G t b)) := by
    funext b
    rw [Function.comp_apply, AlgHom.toLinearMap_apply, zigzagMk_ofPath_skewBasisPath k G t b]
  rw [hcomp', ← Finsupp.apply_linearCombination, AlgHom.toLinearMap_apply]
  exact (zigzagMk_eq_zero_iff k G).mpr hzz

/-- **The vertex, arrow and volume classes of a skew-zigzag quotient span.** -/
theorem span_range_skewZigzagBasisFun_eq_top :
    Submodule.span k (Set.range (skewZigzagBasisFun k G c t)) = ⊤ := by
  have key : ∀ x : Quiver.TotalPath (DoubledQuiver G), skewZigzagMk k G c (ofPath x) ∈
      Submodule.span k (Set.range (skewZigzagBasisFun k G c t)) := by
    rintro ⟨a, b, p⟩
    obtain ⟨i, rfl⟩ : ∃ i, a = vertex G i :=
      ⟨(vertexEquiv G).symm a, (vertexEquiv_symm_apply G a).symm⟩
    obtain ⟨j, rfl⟩ : ∃ j, b = vertex G j :=
      ⟨(vertexEquiv G).symm b, (vertexEquiv_symm_apply G b).symm⟩
    rcases Nat.lt_or_ge p.length 3 with hlt | hge
    · have hcases : p.length = 0 ∨ p.length = 1 ∨ p.length = 2 := by omega
      rcases hcases with hp | hp | hp
      · obtain rfl : i = j := (vertex_inj G).mp (p.eq_of_length_zero hp)
        obtain rfl : p = _root_.Quiver.Path.nil := p.eq_nil_of_length_zero hp
        refine Submodule.subset_span ⟨.inl i, ?_⟩
        rw [skewZigzagBasisFun_inl, vertexIdempotent_eq_single, ofPath_eq_single]
      · obtain ⟨h, rfl⟩ := exists_eq_arrowPath G p hp
        refine Submodule.subset_span ⟨.inr (.inl ⟨(i, j), h⟩), ?_⟩
        rw [skewZigzagBasisFun_inr_inl, ofArrow_eq_ofPath_arrowPath]
      · rcases eq_or_ne i j with rfl | hij
        · obtain ⟨j', h, rfl⟩ := exists_eq_backtrackPath G p hp
          rw [← backtrackElem_eq_ofPath,
            skewZigzagMk_backtrackElem_eq_smul_skewZigzagVolume k G c t h]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.inr (.inr i), (rfl)⟩)
        · rw [skewZigzagMk_ofPath_eq_zero_of_ne k G c p hp ((vertex_injective G).ne hij)]
          exact Submodule.zero_mem _
    · rw [skewZigzagMk_ofPath_eq_zero_of_three_le k G c ⟨_, _, p⟩ hge]
      exact Submodule.zero_mem _
  have htop : Submodule.span k (Set.range fun x : Quiver.TotalPath (DoubledQuiver G) =>
      (skewZigzagMk k G c).toLinearMap (ofPath x)) = ⊤ := by
    have hsurj : Function.Surjective ⇑(skewZigzagMk k G c).toLinearMap := fun y => by
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨f, skewZigzagMk_apply k G c f⟩
    have hmap : Submodule.map (skewZigzagMk k G c).toLinearMap ⊤ = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
    rw [← hmap, ← (pathAlgebraBasis k (DoubledQuiver G)).span_eq, Submodule.map_span,
      coe_pathAlgebraBasis, ← Set.range_comp]
    rfl
  rw [eq_top_iff, ← htop]
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun x => SetLike.mem_coe.2 (key x))

/-- **The basis of a skew-zigzag relation quotient.** For a finite simple graph with a choice of an
incident edge at every vertex, the vertex idempotents, the oriented edges, and the volume classes
of the chosen edges are a basis of the skew-zigzag relation quotient, whatever the parameter. -/
noncomputable def skewZigzagBasis :
    Module.Basis (ZigzagBasisIndex G) k (skewZigzagQuotient k G c) :=
  Module.Basis.mk (linearIndependent_skewZigzagBasisFun k G c t)
    (span_range_skewZigzagBasisFun_eq_top k G c t).ge

@[simp]
theorem skewZigzagBasis_apply (b : ZigzagBasisIndex G) :
    skewZigzagBasis k G c t b = skewZigzagBasisFun k G c t b :=
  Module.Basis.mk_apply _ _ _

/-- The volume class of a vertex relative to a chosen incident edge is nonzero. -/
theorem skewZigzagVolume_ne_zero [Nontrivial k] (i : V) : skewZigzagVolume k G c t i ≠ 0 := by
  have := (skewZigzagBasis k G c t).ne_zero (Sum.inr (Sum.inr i))
  rwa [skewZigzagBasis_apply, skewZigzagBasisFun_inr_inr] at this

include t in
/-- **No backtrack dies in a skew-zigzag relation quotient**, whatever the parameter. The choice
`t` enters only as a witness that the graph has no isolated vertex, which the basis needs. -/
theorem skewZigzagMk_backtrackElem_ne_zero [Nontrivial k] {i j : V} (hij : G.Adj i j) :
    skewZigzagMk k G c (backtrackElem G k hij) ≠ 0 := by
  rw [skewZigzagMk_backtrackElem_eq_smul_skewZigzagVolume k G c t hij, ne_eq,
    (c.ratio hij (t i).2).isUnit.smul_eq_zero]
  exact skewZigzagVolume_ne_zero k G c t i

/-! ### The dimension and the comparison with the ordinary quotient -/

/-- **The dimension of a skew-zigzag relation quotient.** A finite simple graph with no isolated
vertex has `dim = 2|V| + 2|E|` for every skew parameter, as in the ordinary case. -/
theorem finrank_skewZigzagQuotient [Nontrivial k] [Fintype V] [DecidableRel G.Adj]
    (hns : ∀ i : V, ∃ j, G.Adj i j) :
    Module.finrank k (skewZigzagQuotient k G c)
      = 2 * Fintype.card V + 2 * G.edgeFinset.card := by
  classical
  rw [Module.finrank_eq_card_basis
    (skewZigzagBasis k G c fun i => ⟨(hns i).choose, (hns i).choose_spec⟩)]
  simp only [ZigzagBasisIndex, Fintype.card_sum, G.dart_card_eq_twice_card_edges]
  ring

/-- **The dimension of a skew-zigzag quotient of a preconnected graph.** -/
theorem finrank_skewZigzagQuotient_of_preconnected [Nontrivial k] [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] (hconn : G.Preconnected) :
    Module.finrank k (skewZigzagQuotient k G c)
      = 2 * Fintype.card V + 2 * G.edgeFinset.card :=
  finrank_skewZigzagQuotient k G c fun i =>
    SimpleGraph.exists_adj_iff_not_isIsolated.mpr (hconn.not_isIsolated i)

/-- **A skew-zigzag relation quotient is a linear twist of the ordinary one**: the linear
isomorphism matching the two vertex, arrow and volume bases. It is an isomorphism of the underlying
modules only; the algebras are generally not isomorphic, which is what the monodromy of
`TauCeti.SkewZigzagParameter.monodromy` measures. -/
noncomputable def skewZigzagQuotientLinearEquiv :
    skewZigzagQuotient k G c ≃ₗ[k] nonisolatedZigzagQuotient k G :=
  (skewZigzagBasis k G c t).equiv (zigzagBasis k G fun i => ⟨(t i).1, (t i).2⟩) (Equiv.refl _)

@[simp]
theorem skewZigzagQuotientLinearEquiv_skewZigzagBasisFun (b : ZigzagBasisIndex G) :
    skewZigzagQuotientLinearEquiv k G c t (skewZigzagBasisFun k G c t b)
      = zigzagBasisFun k G b := by
  rw [← skewZigzagBasis_apply, skewZigzagQuotientLinearEquiv, Module.Basis.equiv_apply,
    Equiv.refl_apply, zigzagBasis_apply]

end TauCeti
