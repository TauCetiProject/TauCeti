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
`σ`–`τ` cut need not contain all of `A`, so `S.toLeft` need not be a cut between `A` and `B`. When
`A` and `B` are disjoint, the vertex set `(S.toLeft ∪ A) \ B` contains `A` and avoids `B`; if the
original capacities are nonnegative, each arrow `σ → a` has capacity at least the total capacity
leaving `a`, and each arrow `b → τ` at least the total capacity entering `b`, then this
*normalization* of `S` has original cut capacity at most the capacity of `S`.

## Main definitions

* `TauCeti.AuxTerminalHom Q A B`: the arrow family of `Q` with the auxiliary terminals added.
* `TauCeti.AuxTerminalHom.original`, `TauCeti.AuxTerminalHom.source` and
  `TauCeti.AuxTerminalHom.sink`: its three kinds of arrows.
* `TauCeti.AuxTerminalHom.originalEquiv`: the arrows between original vertices are exactly the
  original arrows.
* `TauCeti.auxTerminalCapacity cap cσ cτ`: the capacities `cap` on original arrows, `cσ a` on
  `σ → a` and `cτ b` on `b → τ`.

## Main results

* `TauCeti.arrowSum_auxTerminalCapacity`: the capacity of a `σ`–`τ` cut.
* `TauCeti.TerminalCut.IsAdmissible.arrowSum_auxTerminalCapacity`: a vertex set containing `A`
  and avoiding `B`, together with `σ`, has the same cut capacity as in the original network.
* `TauCeti.arrowSum_union_sdiff_le_arrowSum_auxTerminalCapacity`: the normalization lemma.

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

section Capacity

variable (cap : Assignment Q K) (cσ cτ : V → K)

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
    0 ≤ auxTerminalCapacity (A := A) (B := B) cap cσ cτ := by
  rintro (v | (_ | _)) (w | (_ | _)) e
  all_goals first | exact hcap _ _ e | exact e.elim | exact hτ _ e.2 | exact hσ _ e.2

end Capacity

section Cut

variable [AddCommMonoid K] [Fintype V] [DecidableEq V] [∀ v w, Fintype (Q v w)]

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
  have hsrc (a : V) : ∑ e : AuxTerminalHom Q A B (inr false) (inl a),
      auxTerminalCapacity cap cσ cτ e = if a ∈ A then cσ a else 0 := by
    split_ifs with ha
    · rw [Fintype.sum_eq_single (AuxTerminalHom.source ha) fun e he ↦
        (he (AuxTerminalHom.eq_source e)).elim, auxTerminalCapacity_source]
    · exact sum_eq_zero fun e _ ↦ (ha (AuxTerminalHom.mem_of_source e)).elim
  have hsnk (b : V) : ∑ e : AuxTerminalHom Q A B (inl b) (inr true),
      auxTerminalCapacity cap cσ cτ e = if b ∈ B then cτ b else 0 := by
    split_ifs with hb
    · rw [Fintype.sum_eq_single (AuxTerminalHom.sink hb) fun e he ↦
        (he (AuxTerminalHom.eq_sink e)).elim, auxTerminalCapacity_sink]
    · exact sum_eq_zero fun e _ ↦ (hb (AuxTerminalHom.mem_of_sink e)).elim
  have hA : S.toLeftᶜ ∩ A = A \ S.toLeft := by
    rw [inter_comm, sdiff_eq_inter_compl]
  have hnone : ∑ e : AuxTerminalHom Q A B (inr false) (inr true),
      auxTerminalCapacity cap cσ cτ e = 0 :=
    Fintype.sum_empty _
  simp only [arrowSum_def, sum_sum_eq_sum_toLeft_add_sum_toRight S,
    sum_sum_eq_sum_toLeft_add_sum_toRight Sᶜ, hS, hSc, hScl, sum_singleton,
    sum_auxTerminalCapacity_inl_inl cap cσ cτ, hsrc, hsnk, sum_ite_mem, hA, sum_add_distrib, hnone,
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

/-- **Normalization of auxiliary cuts.** Let `A` and `B` be disjoint and the original capacities
nonnegative, and suppose that the arrow from the fresh source to each `a ∈ A` has capacity at least
the total capacity leaving `a`, and the arrow from each `b ∈ B` to the fresh sink has capacity at
least the total capacity entering `b`.
Then for every cut `S` separating the fresh source from the fresh sink, the vertex set
`(S.toLeft ∪ A) \ B`, which is admissible by `TerminalCut.isAdmissible_union_sdiff`, has original
cut capacity at most the capacity of `S`. -/
theorem arrowSum_union_sdiff_le_arrowSum_auxTerminalCapacity [PartialOrder K]
    [IsOrderedAddMonoid K] (hAB : Disjoint A B) {cap : Assignment Q K} (hcap : 0 ≤ cap)
    {cσ cτ : V → K} (hcσ : ∀ a ∈ A, ∑ w, ∑ e : Q a w, cap e ≤ cσ a)
    (hcτ : ∀ b ∈ B, ∑ v, ∑ e : Q v b, cap e ≤ cτ b) {S : Finset (V ⊕ Bool)}
    (hσ : inr false ∈ S) (hτ : inr true ∉ S) :
    arrowSum cap ((S.toLeft ∪ A) \ B) ((S.toLeft ∪ A) \ B)ᶜ ≤
      arrowSum (auxTerminalCapacity (A := A) (B := B) cap cσ cτ) S Sᶜ := by
  set R := S.toLeft
  have hBRA : B ∩ (R ∪ A) = B ∩ R := by
    rw [inter_union_distrib_left, disjoint_iff_inter_eq_empty.mp hAB.symm, union_empty]
  have hout : arrowSum cap (A \ R) univ ≤ ∑ a ∈ A \ R, cσ a := by
    rw [arrowSum_def]
    exact sum_le_sum fun a ha ↦ hcσ a (mem_sdiff.mp ha).1
  have hin : arrowSum cap univ (B ∩ R) ≤ ∑ b ∈ B ∩ R, cτ b := by
    rw [arrowSum_def, sum_comm]
    exact sum_le_sum fun b hb ↦ hcτ b (mem_inter.mp hb).1
  calc arrowSum cap ((R ∪ A) \ B) ((R ∪ A) \ B)ᶜ
      = arrowSum cap ((R ∪ A) \ (B ∩ (R ∪ A))) ((R ∪ A) \ (B ∩ (R ∪ A)))ᶜ := by
        rw [sdiff_inter_self_right]
    _ ≤ arrowSum cap (R ∪ A) (R ∪ A)ᶜ + arrowSum cap univ (B ∩ (R ∪ A)) :=
        arrowSum_sdiff_compl_le hcap _ _
    _ = arrowSum cap (R ∪ (A \ R)) (R ∪ (A \ R))ᶜ + arrowSum cap univ (B ∩ R) := by
        rw [union_sdiff_self_eq_union, hBRA]
    _ ≤ arrowSum cap R Rᶜ + arrowSum cap (A \ R) univ + arrowSum cap univ (B ∩ R) := by
        grw [arrowSum_union_compl_le hcap]
    _ ≤ arrowSum cap R Rᶜ + ∑ a ∈ A \ R, cσ a + ∑ b ∈ B ∩ R, cτ b := by
        grw [hout, hin]
    _ = _ := by
        rw [arrowSum_auxTerminalCapacity cap cσ cτ hσ hτ]
        abel

end Cut

end TauCeti
