/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Finset.Sum
public import TauCeti.Combinatorics.Network.Excess
public import TauCeti.Combinatorics.Network.MinimumCut.Basic
public import TauCeti.Combinatorics.Network.Walk

/-!
# Auxiliary terminals

The standard reduction of flow and cut problems between two vertex sets `A` and `B` to problems
between two single vertices adds a fresh source `σ` with an arrow to every vertex of `A`, and a
fresh sink `τ` with an arrow from every vertex of `B`. Here the new vertices live on the sum type
`V ⊕ Bool`: `Sum.inl v` is the original vertex `v`, `Sum.inr false` is `σ` and `Sum.inr true` is
`τ`. Every original arrow is retained with its identity, and the capacities of the new arrows are
arbitrary parameters. The sets `A` and `B` are arbitrary, and may be empty or overlap.

A `σ`–`τ` cut `S` is determined by its original vertices `S.toLeft`, and its capacity is the
capacity of the new arrows it crosses plus the original capacity leaving `S.toLeft`. A minimum
`σ`–`τ` cut need not contain all of `A`, so `S.toLeft` need not be a cut between `A` and `B`. The
vertex set `(S.toLeft ∪ A) \ B` avoids `B`, and when `A` and `B` are disjoint it also contains `A`,
so it is a cut between `A` and `B`. If the original capacities are nonnegative, each arrow `σ → a`
has capacity at least the total capacity leaving `a`, and each arrow `b → τ` at least the total
capacity entering `b`, then this *normalization* of `S` has original cut capacity at most the
capacity of `S`, for arbitrary `A` and `B`.

A walk from `σ` to `τ` factors uniquely into one source arrow, an original walk from `A` to `B`,
and one sink arrow. Lifting and projection retain vertex order and every arrow occurrence,
including loops, parallel arrows and repetitions, and preserve and reflect simplicity. When
`A` and `B` overlap, the original segment may have length zero. Projection does not trim further
visits to `A ∪ B`; trimming to a set-to-set path is a separate, non-invertible operation. Deleting
a set of original vertices separates `σ` from `τ` exactly when it separates `A` from `B`.

## Main definitions

* `TauCeti.AuxTerminalHom Q A B`: the arrow family of `Q` with the auxiliary terminals added.
* `TauCeti.AuxTerminalHom.original`, `TauCeti.AuxTerminalHom.source` and
  `TauCeti.AuxTerminalHom.sink`: its three kinds of arrows.
* `TauCeti.AuxTerminalHom.originalEquiv`: the arrows between original vertices are exactly the
  original arrows.
* `TauCeti.auxTerminalCapacity cap cσ cτ`: the capacities `cap` on original arrows, `cσ a` on
  `σ → a` and `cτ b` on `b → τ`.
* `TauCeti.auxTerminalRestrict g`: the restriction of an assignment to the original arrows.
* `TauCeti.setFlowCapacity cap A B`: the auxiliary capacities whose new arrows carry the total
  capacity leaving each `a ∈ A` and entering each `b ∈ B`.

## Main results

* `TauCeti.AuxTerminalHom.forall_iff`: a property of all arrows with auxiliary terminals reduces to
  the original arrows, the arrows from `σ` and the arrows to `τ`.
* `TauCeti.arrowSum_auxTerminalCapacity`: the capacity of a `σ`–`τ` cut.
* `TauCeti.TerminalCut.IsAdmissible.arrowSum_auxTerminalCapacity`: a vertex set containing `A`
  and avoiding `B`, together with `σ`, has the same cut capacity as in the original network.
* `TauCeti.arrowSum_union_sdiff_le_arrowSum_auxTerminalCapacity`: the normalization lemma.
* `TauCeti.TerminalCut.IsMinimum.isMinimum_union_sdiff` and
  `TauCeti.TerminalCut.IsMinimum.arrowSum_union_sdiff`: normalizing a minimum `σ`–`τ` cut gives a
  minimum cut between `A` and `B` of the same capacity.
* `TauCeti.AuxTerminalHom.walkEquiv`: the exact correspondence between original walks with
  endpoints in `A` and `B` and walks between the auxiliary terminals, preserving arrow identities,
  vertex lists and simplicity. Projection does not trim visits to further terminal vertices.
* `TauCeti.reachableAvoiding_auxTerminalHom_iff`: reachability between the auxiliary terminals
  after deleting vertices is reachability from `A` to `B`.
* `TauCeti.AuxTerminalHom.excessAt_inl` and `TauCeti.AuxTerminalHom.excessAt_inr_true`: the excess
  of an assignment at an original vertex and at the fresh sink.

## References

* L. R. Ford, D. R. Fulkerson, *Flows in Networks*, Princeton University Press, 1962.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003.
-/

public section

namespace TauCeti

open Finset Sum

universe u v w

variable {V : Type u} (Q : V → V → Type v) (A B : Finset V)

/-- The arrow family of `Q` with auxiliary terminals for the vertex sets `A` and `B`, on the
vertex type `V ⊕ Bool`. The arrows between original vertices `Sum.inl v` and `Sum.inl w` are those
of `Q v w`; the fresh source `σ = Sum.inr false` has one arrow to each `Sum.inl a` with `a ∈ A`; the
fresh sink `τ = Sum.inr true` has one arrow from each `Sum.inl b` with `b ∈ B`; and there are no
other arrows. -/
@[expose] def AuxTerminalHom : V ⊕ Bool → V ⊕ Bool → Type v
  | inl v, inl w => Q v w
  | inr false, inl a => {_u : PUnit.{v + 1} // a ∈ A}
  | inl b, inr true => {_u : PUnit.{v + 1} // b ∈ B}
  | _, _ => PEmpty

instance AuxTerminalHom.instFintype [DecidableEq V] [∀ v w, Fintype (Q v w)] :
    ∀ x y, Fintype (AuxTerminalHom Q A B x y)
  | inl v, inl w => inferInstanceAs (Fintype (Q v w))
  | inr false, inl a => inferInstanceAs (Fintype {_u : PUnit.{v + 1} // a ∈ A})
  | inl b, inr true => inferInstanceAs (Fintype {_u : PUnit.{v + 1} // b ∈ B})
  | inl _, inr false => inferInstanceAs (Fintype PEmpty)
  | inr false, inr _ => inferInstanceAs (Fintype PEmpty)
  | inr true, _ => inferInstanceAs (Fintype PEmpty)

namespace AuxTerminalHom

variable {Q A B}

/-- An original arrow `e : Q v w`, as an arrow from `Sum.inl v` to `Sum.inl w`. -/
def original {v w : V} (e : Q v w) : AuxTerminalHom Q A B (inl v) (inl w) :=
  e

/-- The arrow from the fresh source `Sum.inr false` to a vertex `Sum.inl a` with `a ∈ A`. -/
def source {a : V} (ha : a ∈ A) : AuxTerminalHom Q A B (inr false) (inl a) :=
  ⟨PUnit.unit, ha⟩

/-- The arrow from a vertex `Sum.inl b` with `b ∈ B` to the fresh sink `Sum.inr true`. -/
def sink {b : V} (hb : b ∈ B) : AuxTerminalHom Q A B (inl b) (inr true) :=
  ⟨PUnit.unit, hb⟩

/-- The arrows from `Sum.inl v` to `Sum.inl w` are exactly the original arrows `Q v w`. -/
def originalEquiv {v w : V} : Q v w ≃ AuxTerminalHom Q A B (inl v) (inl w) :=
  Equiv.refl _

@[simp]
theorem originalEquiv_apply {v w : V} (e : Q v w) :
    originalEquiv (A := A) (B := B) e = original e :=
  (rfl)

@[simp]
theorem originalEquiv_symm_original {v w : V} (e : Q v w) :
    originalEquiv.symm (original (A := A) (B := B) e) = e :=
  (rfl)

@[simp]
theorem original_originalEquiv_symm {v w : V} (e : AuxTerminalHom Q A B (inl v) (inl w)) :
    original (originalEquiv.symm e) = e :=
  (rfl)

theorem original_injective {v w : V} :
    Function.Injective (original (A := A) (B := B) : Q v w → _) :=
  originalEquiv.injective

@[simp]
theorem original_inj {v w : V} {e e' : Q v w} :
    original (A := A) (B := B) e = original e' ↔ e = e' :=
  original_injective.eq_iff

/-- The fresh source has an arrow to `Sum.inl a` only when `a ∈ A`. -/
theorem mem_of_source {a : V} (e : AuxTerminalHom Q A B (inr false) (inl a)) : a ∈ A :=
  e.2

/-- The fresh sink has an arrow from `Sum.inl b` only when `b ∈ B`. -/
theorem mem_of_sink {b : V} (e : AuxTerminalHom Q A B (inl b) (inr true)) : b ∈ B :=
  e.2

/-- Every arrow from the fresh source to `Sum.inl a` is `source`. -/
theorem eq_source {a : V} (e : AuxTerminalHom Q A B (inr false) (inl a)) :
    e = source (mem_of_source e) :=
  (rfl)

/-- Every arrow from `Sum.inl b` to the fresh sink is `sink`. -/
theorem eq_sink {b : V} (e : AuxTerminalHom Q A B (inl b) (inr true)) :
    e = sink (mem_of_sink e) :=
  (rfl)

/-- A property holds for every arrow with auxiliary terminals exactly when it holds for every
original arrow, every arrow from the fresh source and every arrow to the fresh sink. -/
theorem forall_iff {P : ∀ ⦃x y⦄, AuxTerminalHom Q A B x y → Prop} :
    (∀ ⦃x y⦄ (e : AuxTerminalHom Q A B x y), P e) ↔
      (∀ ⦃v w⦄ (e : Q v w), P (original e)) ∧ (∀ ⦃a⦄ (ha : a ∈ A), P (source ha)) ∧
        ∀ ⦃b⦄ (hb : b ∈ B), P (sink hb) := by
  refine ⟨fun h ↦ ⟨fun _ _ _ ↦ h _, fun _ _ ↦ h _, fun _ _ ↦ h _⟩, ?_⟩
  rintro ⟨horig, hsrc, hsink⟩ (v | (_ | _)) (w | (_ | _)) e
  all_goals first | exact e.elim | exact horig e | exact hsrc e.2 | exact hsink e.2

instance instSubsingletonSource (a : V) :
    Subsingleton (AuxTerminalHom Q A B (inr false) (inl a)) :=
  ⟨fun e e' ↦ (eq_source e).trans (eq_source e').symm⟩

instance instSubsingletonSink (b : V) : Subsingleton (AuxTerminalHom Q A B (inl b) (inr true)) :=
  ⟨fun e e' ↦ (eq_sink e).trans (eq_sink e').symm⟩

/-- No arrow enters the fresh source. -/
instance instIsEmptyToSource : ∀ x, IsEmpty (AuxTerminalHom Q A B x (inr false))
  | inl _ => inferInstanceAs (IsEmpty PEmpty)
  | inr false => inferInstanceAs (IsEmpty PEmpty)
  | inr true => inferInstanceAs (IsEmpty PEmpty)

/-- No arrow leaves the fresh sink. -/
instance instIsEmptyFromSink : ∀ y, IsEmpty (AuxTerminalHom Q A B (inr true) y)
  | inl _ => inferInstanceAs (IsEmpty PEmpty)
  | inr _ => inferInstanceAs (IsEmpty PEmpty)

/-- No arrow goes directly from the fresh source to the fresh sink. -/
instance instIsEmptySourceSink : IsEmpty (AuxTerminalHom Q A B (inr false) (inr true)) :=
  inferInstanceAs (IsEmpty PEmpty)

end AuxTerminalHom

variable {Q A B} {K : Type w}

/-- The capacities on the arrow family with auxiliary terminals: `cap e` on an original arrow
`e`, `cσ a` on the arrow from the fresh source to `a`, and `cτ b` on the arrow from `b` to the
fresh sink. -/
def auxTerminalCapacity (cap : Assignment Q K) (cσ cτ : V → K) :
    Assignment (AuxTerminalHom Q A B) K
  | inl _, inl _, e => cap e
  | inr false, inl a, _ => cσ a
  | inl b, inr true, _ => cτ b
  | inl _, inr false, e => e.elim
  | inr false, inr _, e => e.elim
  | inr true, _, e => e.elim

/-- The restriction of an assignment with auxiliary terminals to the original arrows. -/
def auxTerminalRestrict (g : Assignment (AuxTerminalHom Q A B) K) : Assignment Q K :=
  fun _ _ e ↦ g (AuxTerminalHom.original e)

@[simp]
theorem auxTerminalRestrict_apply (g : Assignment (AuxTerminalHom Q A B) K) {v w : V}
    (e : Q v w) : auxTerminalRestrict g e = g (AuxTerminalHom.original e) :=
  (rfl)

section Capacity

variable (cap : Assignment Q K) (cσ cτ : V → K)

@[simp]
theorem auxTerminalRestrict_auxTerminalCapacity :
    auxTerminalRestrict (auxTerminalCapacity (A := A) (B := B) cap cσ cτ) = cap :=
  (rfl)

@[simp]
theorem auxTerminalCapacity_original {v w : V} (e : Q v w) :
    auxTerminalCapacity cap cσ cτ (AuxTerminalHom.original (A := A) (B := B) e) = cap e :=
  (rfl)

@[simp]
theorem auxTerminalCapacity_source {a : V} (ha : a ∈ A) :
    auxTerminalCapacity (B := B) cap cσ cτ (AuxTerminalHom.source ha) = cσ a :=
  (rfl)

@[simp]
theorem auxTerminalCapacity_sink {b : V} (hb : b ∈ B) :
    auxTerminalCapacity (A := A) cap cσ cτ (AuxTerminalHom.sink hb) = cτ b :=
  (rfl)

/-- The capacities with auxiliary terminals are nonnegative when the original capacities and the
capacities of the new arrows are. -/
theorem auxTerminalCapacity_nonneg [Zero K] [Preorder K] {cap : Assignment Q K} {cσ cτ : V → K}
    (hcap : 0 ≤ cap) (hσ : ∀ a ∈ A, 0 ≤ cσ a) (hτ : ∀ b ∈ B, 0 ≤ cτ b) :
    0 ≤ auxTerminalCapacity (A := A) (B := B) cap cσ cτ :=
  AuxTerminalHom.forall_iff.2 ⟨fun _ _ e ↦ hcap _ _ e, fun _ ha ↦ hσ _ ha, fun _ hb ↦ hτ _ hb⟩

end Capacity

section Cut

variable [AddCommMonoid K] [Fintype V] [DecidableEq V] [∀ v w, Fintype (Q v w)]

omit [Fintype V] in
/-- A sum over the arrows between two original vertices is a sum over the original arrows. -/
theorem AuxTerminalHom.sum_inl_inl {x y : V} (g : AuxTerminalHom Q A B (inl x) (inl y) → K) :
    ∑ e, g e = ∑ e : Q x y, g (original e) :=
  (Fintype.sum_equiv originalEquiv _ _ fun _ ↦ rfl).symm

omit [Fintype V] in
/-- A sum over the arrows from the fresh source to `Sum.inl a`, for `a ∈ A`, is the value on
`source`. -/
theorem AuxTerminalHom.sum_source {a : V} (ha : a ∈ A)
    (g : AuxTerminalHom Q A B (inr false) (inl a) → K) : ∑ e, g e = g (source ha) :=
  Fintype.sum_subsingleton g _

omit [Fintype V] in
/-- There is no arrow from the fresh source to `Sum.inl a` for `a ∉ A`. -/
theorem AuxTerminalHom.sum_source_of_notMem {a : V} (ha : a ∉ A)
    (g : AuxTerminalHom Q A B (inr false) (inl a) → K) : ∑ e, g e = 0 :=
  Fintype.sum_eq_zero _ fun e ↦ (ha (mem_of_source e)).elim

omit [Fintype V] in
/-- A sum over the arrows from `Sum.inl b` to the fresh sink, for `b ∈ B`, is the value on
`sink`. -/
theorem AuxTerminalHom.sum_sink {b : V} (hb : b ∈ B)
    (g : AuxTerminalHom Q A B (inl b) (inr true) → K) : ∑ e, g e = g (sink hb) :=
  Fintype.sum_subsingleton g _

omit [Fintype V] in
/-- There is no arrow from `Sum.inl b` to the fresh sink for `b ∉ B`. -/
theorem AuxTerminalHom.sum_sink_of_notMem {b : V} (hb : b ∉ B)
    (g : AuxTerminalHom Q A B (inl b) (inr true) → K) : ∑ e, g e = 0 :=
  Fintype.sum_eq_zero _ fun e ↦ (hb (mem_of_sink e)).elim

omit [Fintype V] in
/-- The total capacity of the arrows from the fresh source to `Sum.inl a` is `cσ a` for `a ∈ A`,
and zero otherwise. -/
theorem sum_auxTerminalCapacity_source (cap : Assignment Q K) (cσ cτ : V → K) (a : V) :
    ∑ e : AuxTerminalHom Q A B (inr false) (inl a), auxTerminalCapacity cap cσ cτ e =
      if a ∈ A then cσ a else 0 := by
  split_ifs with ha
  · rw [AuxTerminalHom.sum_source ha, auxTerminalCapacity_source]
  · exact AuxTerminalHom.sum_source_of_notMem ha _

omit [Fintype V] in
/-- The total capacity of the arrows from `Sum.inl b` to the fresh sink is `cτ b` for `b ∈ B`,
and zero otherwise. -/
theorem sum_auxTerminalCapacity_sink (cap : Assignment Q K) (cσ cτ : V → K) (b : V) :
    ∑ e : AuxTerminalHom Q A B (inl b) (inr true), auxTerminalCapacity cap cσ cτ e =
      if b ∈ B then cτ b else 0 := by
  split_ifs with hb
  · rw [AuxTerminalHom.sum_sink hb, auxTerminalCapacity_sink]
  · exact AuxTerminalHom.sum_sink_of_notMem hb _

omit [Fintype V] in
/-- The total capacity with auxiliary terminals of the arrows between two original vertices is
their original total capacity. -/
theorem sum_auxTerminalCapacity_inl_inl (cap : Assignment Q K) (cσ cτ : V → K) (x y : V) :
    ∑ e : AuxTerminalHom Q A B (inl x) (inl y), auxTerminalCapacity cap cσ cτ e =
      ∑ e : Q x y, cap e :=
  (Fintype.sum_equiv AuxTerminalHom.originalEquiv _ _ fun _ ↦ rfl).symm

/-- The capacity of a cut `S` separating the fresh source from the fresh sink is the capacity
`cσ a` of each `a ∈ A` outside `S`, plus the capacity `cτ b` of each `b ∈ B` inside `S`, plus the
original capacity of the arrows leaving the original vertices of `S`. -/
theorem arrowSum_auxTerminalCapacity (cap : Assignment Q K) (cσ cτ : V → K)
    {S : Finset (V ⊕ Bool)} (hσ : inr false ∈ S) (hτ : inr true ∉ S) :
    arrowSum (auxTerminalCapacity (A := A) (B := B) cap cσ cτ) S Sᶜ =
      ∑ a ∈ A \ S.toLeft, cσ a + ∑ b ∈ B ∩ S.toLeft, cτ b +
        arrowSum cap S.toLeft S.toLeftᶜ := by
  have hS : S.toRight = {false} := by
    ext (_ | _) <;> simp [hσ, hτ]
  have hSc : Sᶜ.toRight = {true} := by
    ext (_ | _) <;> simp [hσ, hτ]
  have hScl : Sᶜ.toLeft = S.toLeftᶜ := by
    ext
    simp
  have hA : S.toLeftᶜ ∩ A = A \ S.toLeft := by
    rw [inter_comm, sdiff_eq_inter_compl]
  have hnone : ∑ e : AuxTerminalHom Q A B (inr false) (inr true),
      auxTerminalCapacity cap cσ cτ e = 0 :=
    Fintype.sum_empty _
  simp only [arrowSum_def, sum_sum_eq_sum_toLeft_add_sum_toRight S,
    sum_sum_eq_sum_toLeft_add_sum_toRight Sᶜ, hS, hSc, hScl, sum_singleton,
    sum_auxTerminalCapacity_inl_inl cap cσ cτ, sum_auxTerminalCapacity_source,
    sum_auxTerminalCapacity_sink, sum_ite_mem, hA, sum_add_distrib, hnone,
    add_zero, inter_comm S.toLeft B]
  abel

/-- A vertex set `R` containing `A` and avoiding `B`, together with the fresh source, is a cut
with the same capacity as `R` in the original network. -/
theorem TerminalCut.IsAdmissible.arrowSum_auxTerminalCapacity {R : Finset V}
    (hR : TerminalCut.IsAdmissible A B R) (cap : Assignment Q K) (cσ cτ : V → K) :
    arrowSum (auxTerminalCapacity (A := A) (B := B) cap cσ cτ) (R.disjSum {false})
        (R.disjSum {false})ᶜ = arrowSum cap R Rᶜ := by
  simp [_root_.TauCeti.arrowSum_auxTerminalCapacity cap cσ cτ (S := R.disjSum {false}) (by simp)
    (by simp), sdiff_eq_empty_iff_subset.mpr hR.subset,
    disjoint_iff_inter_eq_empty.mp hR.disjoint.symm]

/-- **Normalization of auxiliary cuts.** Let the original capacities be nonnegative, and suppose
that the arrow from the fresh source to each `a ∈ A` has capacity at least the total capacity
leaving `a`, and the arrow from each `b ∈ B` to the fresh sink has capacity at least the total
capacity entering `b`.
Then for every cut `S` separating the fresh source from the fresh sink, the vertex set
`(S.toLeft ∪ A) \ B`, which is admissible by `TerminalCut.isAdmissible_union_sdiff` when `A` and
`B` are disjoint, has original cut capacity at most the capacity of `S`. -/
theorem arrowSum_union_sdiff_le_arrowSum_auxTerminalCapacity [PartialOrder K]
    [IsOrderedAddMonoid K] {cap : Assignment Q K} (hcap : 0 ≤ cap)
    {cσ cτ : V → K} (hcσ : ∀ a ∈ A, ∑ w, ∑ e : Q a w, cap e ≤ cσ a)
    (hcτ : ∀ b ∈ B, ∑ v, ∑ e : Q v b, cap e ≤ cτ b) {S : Finset (V ⊕ Bool)}
    (hσ : inr false ∈ S) (hτ : inr true ∉ S) :
    arrowSum cap ((S.toLeft ∪ A) \ B) ((S.toLeft ∪ A) \ B)ᶜ ≤
      arrowSum (auxTerminalCapacity (A := A) (B := B) cap cσ cτ) S Sᶜ := by
  set R := S.toLeft
  -- Only the part `A \ B` of `A` survives in the cut set, and it is disjoint from `B`.
  have hT : (R ∪ A) \ B = (R ∪ (A \ B)) \ B := by
    ext x
    simp only [mem_sdiff, mem_union]
    tauto
  have hBRA : B ∩ (R ∪ (A \ B)) = B ∩ R := by
    rw [inter_union_distrib_left, disjoint_iff_inter_eq_empty.mp sdiff_disjoint.symm, union_empty]
  have hout : arrowSum cap ((A \ B) \ R) univ ≤ ∑ a ∈ A \ R, cσ a := by
    refine (arrowSum_mono_left hcap (sdiff_subset_sdiff sdiff_le le_rfl) univ).trans ?_
    rw [arrowSum_def]
    exact sum_le_sum fun a ha ↦ hcσ a (mem_sdiff.mp ha).1
  have hin : arrowSum cap univ (B ∩ R) ≤ ∑ b ∈ B ∩ R, cτ b := by
    rw [arrowSum_def, sum_comm]
    exact sum_le_sum fun b hb ↦ hcτ b (mem_inter.mp hb).1
  rw [hT]
  calc arrowSum cap ((R ∪ (A \ B)) \ B) ((R ∪ (A \ B)) \ B)ᶜ
      = arrowSum cap ((R ∪ (A \ B)) \ (B ∩ (R ∪ (A \ B))))
          ((R ∪ (A \ B)) \ (B ∩ (R ∪ (A \ B))))ᶜ := by
        rw [sdiff_inter_self_right]
    _ ≤ arrowSum cap (R ∪ (A \ B)) (R ∪ (A \ B))ᶜ + arrowSum cap univ (B ∩ (R ∪ (A \ B))) :=
        arrowSum_sdiff_compl_le hcap _ _
    _ = arrowSum cap (R ∪ ((A \ B) \ R)) (R ∪ ((A \ B) \ R))ᶜ + arrowSum cap univ (B ∩ R) := by
        rw [union_sdiff_self_eq_union, hBRA]
    _ ≤ arrowSum cap R Rᶜ + arrowSum cap ((A \ B) \ R) univ + arrowSum cap univ (B ∩ R) := by
        grw [arrowSum_union_compl_le hcap]
    _ ≤ arrowSum cap R Rᶜ + ∑ a ∈ A \ R, cσ a + ∑ b ∈ B ∩ R, cτ b := by
        grw [hout, hin]
    _ = _ := by
        rw [arrowSum_auxTerminalCapacity cap cσ cτ hσ hτ]
        abel

/-- **Normalization of minimum auxiliary cuts.** Under the hypotheses of the normalization lemma
`TauCeti.arrowSum_union_sdiff_le_arrowSum_auxTerminalCapacity`, normalizing a minimum cut `S`
between the fresh terminals to the vertex set `(S.toLeft ∪ A) \ B` preserves its capacity. -/
theorem TerminalCut.IsMinimum.arrowSum_union_sdiff [PartialOrder K] [IsOrderedAddMonoid K]
    (hAB : Disjoint A B) {cap : Assignment Q K} (hcap : 0 ≤ cap) {cσ cτ : V → K}
    (hcσ : ∀ a ∈ A, ∑ w, ∑ e : Q a w, cap e ≤ cσ a)
    (hcτ : ∀ b ∈ B, ∑ v, ∑ e : Q v b, cap e ≤ cτ b) {S : Finset (V ⊕ Bool)}
    (hS : IsMinimum (fun S ↦ arrowSum (auxTerminalCapacity (A := A) (B := B) cap cσ cτ) S Sᶜ)
      {inr false} {inr true} S) :
    arrowSum cap ((S.toLeft ∪ A) \ B) ((S.toLeft ∪ A) \ B)ᶜ =
      arrowSum (auxTerminalCapacity (A := A) (B := B) cap cσ cτ) S Sᶜ := by
  have hσ : inr false ∈ S := hS.admissible.subset (mem_singleton_self _)
  have hτ : inr true ∉ S := disjoint_right.1 hS.admissible.disjoint (mem_singleton_self _)
  refine (arrowSum_union_sdiff_le_arrowSum_auxTerminalCapacity hcap hcσ hcτ hσ hτ).antisymm ?_
  rw [← (isAdmissible_union_sdiff hAB S.toLeft).arrowSum_auxTerminalCapacity cap cσ cτ]
  exact hS.le (isAdmissible_iff.2 ⟨by simp, by simp⟩)

/-- Under the hypotheses of the normalization lemma
`TauCeti.arrowSum_union_sdiff_le_arrowSum_auxTerminalCapacity`, normalizing a minimum cut `S`
between the fresh terminals gives a minimum cut `(S.toLeft ∪ A) \ B` between `A` and `B` in the
original network. -/
theorem TerminalCut.IsMinimum.isMinimum_union_sdiff [PartialOrder K] [IsOrderedAddMonoid K]
    (hAB : Disjoint A B) {cap : Assignment Q K} (hcap : 0 ≤ cap) {cσ cτ : V → K}
    (hcσ : ∀ a ∈ A, ∑ w, ∑ e : Q a w, cap e ≤ cσ a)
    (hcτ : ∀ b ∈ B, ∑ v, ∑ e : Q v b, cap e ≤ cτ b) {S : Finset (V ⊕ Bool)}
    (hS : IsMinimum (fun S ↦ arrowSum (auxTerminalCapacity (A := A) (B := B) cap cσ cτ) S Sᶜ)
      {inr false} {inr true} S) :
    IsMinimum (fun R ↦ arrowSum cap R Rᶜ) A B ((S.toLeft ∪ A) \ B) := by
  refine isMinimum_iff.2 ⟨isAdmissible_union_sdiff hAB _, fun R hR ↦ ?_⟩
  rw [hS.arrowSum_union_sdiff hAB hcap hcσ hcτ, ← hR.arrowSum_auxTerminalCapacity cap cσ cτ]
  exact hS.le (isAdmissible_iff.2 ⟨by simp, by simp⟩)

end Cut

/-! ### Capacities for flows between vertex sets -/

section SetFlowCapacity

variable [AddCommMonoid K] [Fintype V] [∀ v w, Fintype (Q v w)]

/-- The capacities of the auxiliary network for flows between the vertex sets `A` and `B`: `cap` on
the original arrows, the total capacity leaving `a` on the arrow from the fresh source to `a ∈ A`,
and the total capacity entering `b` on the arrow from `b ∈ B` to the fresh sink. These satisfy the
hypotheses of the normalization lemmas with equality. -/
def setFlowCapacity (cap : Assignment Q K) (A B : Finset V) :
    Assignment (AuxTerminalHom Q A B) K :=
  auxTerminalCapacity cap (fun a ↦ ∑ w, ∑ e : Q a w, cap e) fun b ↦ ∑ v, ∑ e : Q v b, cap e

variable (cap : Assignment Q K)

/-- The capacities `setFlowCapacity cap A B` are the auxiliary capacities `auxTerminalCapacity`
with the total capacity leaving `a` and entering `b` on the new arrows. -/
theorem setFlowCapacity_def :
    setFlowCapacity cap A B =
      auxTerminalCapacity cap (fun a ↦ ∑ w, ∑ e : Q a w, cap e) fun b ↦ ∑ v, ∑ e : Q v b, cap e :=
  (rfl)

@[simp]
theorem auxTerminalRestrict_setFlowCapacity : auxTerminalRestrict (setFlowCapacity cap A B) = cap :=
  (rfl)

@[simp]
theorem setFlowCapacity_original {v w : V} (e : Q v w) :
    setFlowCapacity cap A B (AuxTerminalHom.original e) = cap e :=
  auxTerminalCapacity_original ..

@[simp]
theorem setFlowCapacity_source {a : V} (ha : a ∈ A) :
    setFlowCapacity cap A B (AuxTerminalHom.source ha) = ∑ w, ∑ e : Q a w, cap e :=
  auxTerminalCapacity_source ..

@[simp]
theorem setFlowCapacity_sink {b : V} (hb : b ∈ B) :
    setFlowCapacity cap A B (AuxTerminalHom.sink hb) = ∑ v, ∑ e : Q v b, cap e :=
  auxTerminalCapacity_sink ..

variable {cap}

/-- The auxiliary capacities are nonnegative when the original capacities are. -/
theorem setFlowCapacity_nonneg [PartialOrder K] [IsOrderedAddMonoid K] (hcap : 0 ≤ cap) :
    0 ≤ setFlowCapacity cap A B :=
  auxTerminalCapacity_nonneg hcap (fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun e _ ↦ hcap _ _ e)
    fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun e _ ↦ hcap _ _ e

/-- The auxiliary capacities lie in an additive submonoid containing the original capacities. -/
theorem setFlowCapacity_mem {M : Type*} [SetLike M K] [AddSubmonoidClass M K] {H : M}
    (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ H) :
    ∀ ⦃x y⦄ (e : AuxTerminalHom Q A B x y), setFlowCapacity cap A B e ∈ H :=
  AuxTerminalHom.forall_iff.2 ⟨fun _ _ e ↦ hcap e,
    fun _ _ ↦ sum_mem fun _ _ ↦ sum_mem fun e _ ↦ hcap e,
    fun _ _ ↦ sum_mem fun _ _ ↦ sum_mem fun e _ ↦ hcap e⟩

end SetFlowCapacity

section Walk

namespace AuxTerminalHom

/-- Prepend the source arrow to a walk along original arrows. -/
def liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b) := by
  induction p with
  | nil => exact (ArrowWalk.nil _).cons (source ha)
  | cons _ e ih => exact ih.cons (original e)

@[simp]
theorem liftFromSource_nil {a : V} (ha : a ∈ A) :
    liftFromSource (Q := Q) (B := B) ha (ArrowWalk.nil a) = (ArrowWalk.nil _).cons (source ha) :=
  (rfl)

@[simp]
theorem liftFromSource_cons {a b c : V} (ha : a ∈ A) (p : ArrowWalk Q a b) (e : Q b c) :
    liftFromSource (B := B) ha (p.cons e) = (liftFromSource ha p).cons (original e) :=
  (rfl)

/-- Adjoin the auxiliary source and sink arrows to an original walk. -/
def liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true) :=
  (liftFromSource ha p).cons (sink hb)

/-- A walk lifted to both auxiliary terminals is a lifted source prefix followed by its sink
arrow. -/
theorem liftWalk_def {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    liftWalk ha hb p = (liftFromSource ha p).cons (sink hb) :=
  (rfl)

@[simp]
theorem vertices_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).vertices = inr false :: p.vertices.map inl := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih]

@[simp]
theorem vertices_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (liftWalk ha hb p).vertices = inr false :: p.vertices.map inl ++ [inr true] := by
  simp [liftWalk_def]

@[simp]
theorem length_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).length = p.length + 1 := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [ih, Nat.add_assoc]

@[simp]
theorem length_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (liftWalk ha hb p).length = p.length + 2 := by
  simp [liftWalk_def, Nat.add_assoc]

/-- The inclusion of original arrow identities, with their endpoints. -/
def originalArrow : (Σ a b, Q a b) → Σ x y, AuxTerminalHom Q A B x y :=
  Sigma.map inl fun _ => Sigma.map inl fun _ => original

theorem originalArrow_def (e : Σ a b, Q a b) :
    originalArrow (A := A) (B := B) e = ⟨inl e.1, inl e.2.1, original e.2.2⟩ :=
  (rfl)

@[simp]
theorem originalArrow_fst (e : Σ a b, Q a b) :
    (originalArrow (A := A) (B := B) e).1 = inl e.1 :=
  (rfl)

@[simp]
theorem originalArrow_snd_fst (e : Σ a b, Q a b) :
    (originalArrow (A := A) (B := B) e).2.1 = inl e.2.1 :=
  (rfl)

@[simp]
theorem originalArrow_mk {a b : V} (e : Q a b) :
    originalArrow (A := A) (B := B) ⟨a, b, e⟩ = ⟨inl a, inl b, original e⟩ :=
  (rfl)

/-- Inclusion retains the identity of each original arrow. -/
@[grind inj]
theorem originalArrow_injective :
    Function.Injective (originalArrow (Q := Q) (A := A) (B := B)) :=
  inl_injective.sigma_map fun _ => inl_injective.sigma_map fun _ => original_injective

@[simp]
theorem originalArrow_inj {e f : Σ a b, Q a b} :
    originalArrow (A := A) (B := B) e = originalArrow f ↔ e = f :=
  originalArrow_injective.eq_iff

@[simp]
theorem originalArrow_eq_mk_original {e : Σ a b, Q a b} {a b : V} {f : Q a b} :
    originalArrow (A := A) (B := B) e = ⟨inl a, inl b, original f⟩ ↔ e = ⟨a, b, f⟩ := by
  rw [← originalArrow_mk, originalArrow_inj]

@[simp]
theorem originalArrow_ne_mk_inr_left (e : Σ a b, Q a b) (s : Bool) (y : V ⊕ Bool)
    (f : AuxTerminalHom Q A B (inr s) y) :
    originalArrow e ≠ ⟨inr s, y, f⟩ :=
  fun h => Sum.inl_ne_inr (congrArg Sigma.fst h)

@[simp]
theorem originalArrow_ne_mk_inr_right (e : Σ a b, Q a b) (x : V ⊕ Bool) (t : Bool)
    (f : AuxTerminalHom Q A B x (inr t)) :
    originalArrow e ≠ ⟨x, inr t, f⟩ :=
  fun h => Sum.inl_ne_inr (congrArg (fun z => z.2.1) h)

@[simp]
theorem arrows_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).arrows =
      ⟨inr false, inl a, source ha⟩ :: p.arrows.map originalArrow := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

@[simp]
theorem arrows_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (liftWalk ha hb p).arrows =
      ⟨inr false, inl a, source ha⟩ :: p.arrows.map originalArrow ++
        [⟨inl b, inr true, sink hb⟩] := by
  simp [liftWalk_def]

/-- An original arrow occurs in a lifted walk exactly when it occurred in the original walk.
This is not a simp lemma because `arrows_liftWalk` first expands the entire arrow list. -/
@[grind =]
theorem originalArrow_mem_arrows_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (p : ArrowWalk Q a b) (e : Σ v w, Q v w) :
    originalArrow e ∈ (liftWalk ha hb p).arrows ↔ e ∈ p.arrows := by
  simp only [arrows_liftWalk, List.mem_cons, List.mem_append, List.not_mem_nil,
    originalArrow_ne_mk_inr_left, originalArrow_ne_mk_inr_right, false_or, or_false,
    List.mem_map_of_injective originalArrow_injective]

/-- Prepending the source arrow preserves and reflects simplicity. -/
@[simp]
theorem isPath_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    (liftFromSource (B := B) ha p).IsPath ↔ p.IsPath := by
  simp [ArrowWalk.isPath_def, List.nodup_map_iff inl_injective]

/-- Adding auxiliary terminals preserves and reflects simplicity of a walk. -/
@[simp]
theorem isPath_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    (liftWalk ha hb p).IsPath ↔ p.IsPath := by
  simp [ArrowWalk.isPath_def, List.nodup_append, List.nodup_map_iff inl_injective]

/-- A walk from the auxiliary source to an original vertex has a unique original segment. -/
private def projectPrefix {y : V ⊕ Bool}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) y) {b : V} (hy : y = inl b) :
    Σ a : {a // a ∈ A}, ArrowWalk Q a.1 b := by
  induction p generalizing b with
  | nil => exact (Sum.inr_ne_inl hy).elim
  | @cons z y p e ih =>
    subst hy
    rcases z with a | _ | _
    · obtain ⟨a, q⟩ := ih rfl
      exact ⟨a, q.cons (originalEquiv.symm e)⟩
    · exact ⟨⟨b, mem_of_source e⟩, ArrowWalk.nil b⟩
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inl b)) e

/-- Remove the source arrow from a walk ending at an original vertex. -/
def projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    Σ a : {a // a ∈ A}, ArrowWalk Q a.1 b :=
  projectPrefix p rfl

@[simp]
theorem projectFromSource_nil_cons {b : V} (e : AuxTerminalHom Q A B (inr false) (inl b)) :
    projectFromSource ((ArrowWalk.nil _).cons e) = ⟨⟨b, mem_of_source e⟩, ArrowWalk.nil b⟩ :=
  (rfl)

@[simp]
theorem projectFromSource_cons {a b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl a))
    (e : AuxTerminalHom Q A B (inl a) (inl b)) :
    projectFromSource (p.cons e) =
      ⟨(projectFromSource p).1, (projectFromSource p).2.cons (originalEquiv.symm e)⟩ :=
  (rfl)

private theorem liftFromSource_projectPrefix {y : V ⊕ Bool}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) y) {b : V} (hy : y = inl b) :
    HEq (liftFromSource (B := B) (projectPrefix p hy).1.2 (projectPrefix p hy).2) p := by
  induction p generalizing b with
  | nil => exact (Sum.inr_ne_inl hy).elim
  | @cons z y p e ih =>
    subst hy
    rcases z with a | _ | _
    · have h : liftFromSource (B := B) (projectFromSource p).1.2
          (projectFromSource p).2 = p := eq_of_heq (ih (b := a) rfl)
      apply heq_of_eq
      -- Fold the private projection at this original endpoint to use its public cons equation.
      change liftFromSource (B := B) (projectFromSource (ArrowWalk.cons p e)).1.2
        (projectFromSource (ArrowWalk.cons p e)).2 = ArrowWalk.cons p e
      rw [projectFromSource_cons, liftFromSource_cons, original_originalEquiv_symm, h]
    · have hp : p = ArrowWalk.nil (inr false) := by
        cases p with
        | nil => rfl
        | @cons z _ p e => exact isEmptyElim (α := AuxTerminalHom Q A B z (inr false)) e
      subst hp
      exact heq_of_eq <| (liftFromSource_nil (Q := Q) (B := B) (mem_of_source e)).trans
        (congrArg (fun f => (ArrowWalk.nil (inr false)).cons f) (eq_source e).symm)
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inl b)) e

@[simp]
theorem projectFromSource_liftFromSource {a b : V} (ha : a ∈ A) (p : ArrowWalk Q a b) :
    projectFromSource (liftFromSource (B := B) ha p) = ⟨⟨a, ha⟩, p⟩ := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    rw [liftFromSource_cons, projectFromSource_cons, ih, originalEquiv_symm_original]

@[simp]
theorem liftFromSource_projectFromSource {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b)) :
    liftFromSource (projectFromSource p).1.2 (projectFromSource p).2 = p :=
  eq_of_heq (liftFromSource_projectPrefix p rfl)

/-- Remove the two auxiliary terminal arrows, retaining the endpoints and every original arrow.
The original segment need not avoid `A ∪ B` in its interior. -/
def projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    Σ a : {a // a ∈ A}, Σ b : {b // b ∈ B}, ArrowWalk Q a.1 b.1 := by
  cases p with
  | @cons y _ p e =>
    rcases y with b | _ | _
    · obtain ⟨a, q⟩ := projectFromSource p
      exact ⟨a, ⟨b, mem_of_sink e⟩, q⟩
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr false) (inr true)) e
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inr true)) e

@[simp]
theorem projectWalk_cons {b : V}
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inl b))
    (e : AuxTerminalHom Q A B (inl b) (inr true)) :
    projectWalk (p.cons e) =
      ⟨(projectFromSource p).1, ⟨b, mem_of_sink e⟩, (projectFromSource p).2⟩ :=
  (rfl)

/-- Projection after lifting recovers both endpoints and the entire original walk. -/
@[simp]
theorem projectWalk_liftWalk {a b : V} (ha : a ∈ A) (hb : b ∈ B) (p : ArrowWalk Q a b) :
    projectWalk (liftWalk ha hb p) = ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩ := by
  rw [liftWalk_def, projectWalk_cons, projectFromSource_liftFromSource]

/-- Lifting the projected original segment recovers the entire auxiliary walk. -/
@[simp]
theorem liftWalk_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2 (projectWalk p).2.2 = p := by
  cases p with
  | @cons y _ p e =>
    rcases y with b | _ | _
    · rw [projectWalk_cons, liftWalk_def, liftFromSource_projectFromSource, ← eq_sink e]
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr false) (inr true)) e
    · exact isEmptyElim (α := AuxTerminalHom Q A B (inr true) (inr true)) e

/-- Projection removes exactly two arrows. This is not a simp lemma: `length_projectWalk`
already normalizes the length on its left-hand side. -/
theorem length_projectWalk_add_two
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (projectWalk p).2.2.length + 2 = p.length := by
  rw [← length_liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2, liftWalk_projectWalk]

@[simp]
theorem length_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (projectWalk p).2.2.length = p.length - 2 := by
  rw [← length_projectWalk_add_two p, Nat.add_sub_cancel]

@[simp]
theorem mem_vertices_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) (v : V) :
    v ∈ (projectWalk p).2.2.vertices ↔ inl v ∈ p.vertices := by
  have h := vertices_liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2 (projectWalk p).2.2
  rw [liftWalk_projectWalk] at h
  rw [h]
  simp

/-- Recover the vertex list of the original segment, with its original order and repetitions. -/
@[simp]
theorem map_vertices_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (projectWalk p).2.2.vertices.map inl = p.vertices.tail.dropLast := by
  have h := vertices_liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2 (projectWalk p).2.2
  rw [liftWalk_projectWalk] at h
  rw [h]
  simp

@[simp]
theorem mem_arrows_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) (e : Σ a b, Q a b) :
    e ∈ (projectWalk p).2.2.arrows ↔ originalArrow e ∈ p.arrows := by
  simpa only [liftWalk_projectWalk] using
    (originalArrow_mem_arrows_liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2
      (projectWalk p).2.2 e).symm

/-- Recover every original arrow occurrence in order. -/
@[simp]
theorem map_arrows_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (projectWalk p).2.2.arrows.map originalArrow = p.arrows.tail.dropLast := by
  have h := arrows_liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2 (projectWalk p).2.2
  rw [liftWalk_projectWalk] at h
  rw [h]
  simp

/-- An empty source-terminal set gives no walk between the auxiliary terminals. -/
instance instIsEmptyWalkSourceEmpty :
    IsEmpty (ArrowWalk (AuxTerminalHom Q ∅ B) (inr false) (inr true)) :=
  ⟨fun p => Finset.notMem_empty _ (projectWalk p).1.2⟩

/-- An empty sink-terminal set gives no walk between the auxiliary terminals. -/
instance instIsEmptyWalkSinkEmpty :
    IsEmpty (ArrowWalk (AuxTerminalHom Q A ∅) (inr false) (inr true)) :=
  ⟨fun p => Finset.notMem_empty _ (projectWalk p).2.1.2⟩

variable (Q A B) in
/-- Walks through the auxiliary terminals correspond to original walks with first endpoint in
`A` and last endpoint in `B`. Repetitions and zero-length original segments are allowed. -/
def walkEquiv :
    (Σ a : {a // a ∈ A}, Σ b : {b // b ∈ B}, ArrowWalk Q a.1 b.1) ≃
      ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true) where
  toFun p := liftWalk p.1.2 p.2.1.2 p.2.2
  invFun := projectWalk
  left_inv := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, p⟩
    exact projectWalk_liftWalk ha hb p
  right_inv := liftWalk_projectWalk

@[simp]
theorem walkEquiv_apply (p : Σ a : {a // a ∈ A}, Σ b : {b // b ∈ B}, ArrowWalk Q a.1 b.1) :
    walkEquiv Q A B p = liftWalk p.1.2 p.2.1.2 p.2.2 :=
  (rfl)

@[simp]
theorem walkEquiv_symm_apply
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (walkEquiv Q A B).symm p = projectWalk p :=
  (rfl)

/-- Removing auxiliary terminals preserves and reflects simplicity of a walk. -/
@[simp]
theorem isPath_projectWalk
    (p : ArrowWalk (AuxTerminalHom Q A B) (inr false) (inr true)) :
    (projectWalk p).2.2.IsPath ↔ p.IsPath := by
  rw [← isPath_liftWalk (projectWalk p).1.2 (projectWalk p).2.1.2, liftWalk_projectWalk]


end AuxTerminalHom

/-- The fresh sink is reachable from the fresh source avoiding a set `X` of vertices not containing
either, exactly when some vertex of `B` is reachable from some vertex of `A` avoiding the original
vertices in `X`. -/
theorem reachableAvoiding_auxTerminalHom_iff {X : Set (V ⊕ Bool)} (hσ : inr false ∉ X)
    (hτ : inr true ∉ X) :
    ReachableAvoiding (AuxTerminalHom Q A B) X (inr false) (inr true) ↔
      ∃ a ∈ A, ∃ b ∈ B, ReachableAvoiding Q (inl ⁻¹' X) a b := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := reachableAvoiding_def.1 h
    let q := AuxTerminalHom.projectWalk p
    refine ⟨q.1.1, q.1.2, q.2.1.1, q.2.1.2, reachableAvoiding_def.2 ⟨q.2.2, ?_⟩⟩
    exact fun v hv ↦ hp _ ((AuxTerminalHom.mem_vertices_projectWalk p v).1 hv)
  · rintro ⟨a, ha, b, hb, h⟩
    obtain ⟨q, hq⟩ := reachableAvoiding_def.1 h
    refine reachableAvoiding_def.2 ⟨AuxTerminalHom.liftWalk ha hb q, fun x hx ↦ ?_⟩
    rw [AuxTerminalHom.vertices_liftWalk] at hx
    simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | ⟨v, hv, rfl⟩ | rfl
    exacts [hσ, hq v hv, hτ]

end Walk

section Excess

variable [AddCommGroup K] [Fintype V] [DecidableEq V] [∀ v w, Fintype (Q v w)]

/-- The excess at an original vertex `Sum.inl v` of an assignment with auxiliary terminals is the
excess at `v` of its restriction to the original arrows, plus the value arriving from the fresh
source, minus the value sent to the fresh sink. -/
theorem AuxTerminalHom.excessAt_inl (g : Assignment (AuxTerminalHom Q A B) K) (v : V) :
    excessAt g (inl v) = excessAt (auxTerminalRestrict g) v +
      ∑ e : AuxTerminalHom Q A B (inr false) (inl v), g e -
        ∑ e : AuxTerminalHom Q A B (inl v) (inr true), g e := by
  simp only [excessAt_def, Fintype.sum_sum_type, Fintype.sum_bool, Fintype.sum_empty, add_zero,
    sum_inl_inl, auxTerminalRestrict_apply]
  abel

/-- The excess at the fresh sink of an assignment with auxiliary terminals is the total value on
the arrows entering it. -/
theorem AuxTerminalHom.excessAt_inr_true (g : Assignment (AuxTerminalHom Q A B) K) :
    excessAt g (inr true) = ∑ b, ∑ e : AuxTerminalHom Q A B (inl b) (inr true), g e := by
  simp [excessAt_def, Fintype.sum_sum_type]

end Excess

end TauCeti
