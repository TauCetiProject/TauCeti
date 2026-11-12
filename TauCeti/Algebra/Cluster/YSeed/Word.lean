/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.YSeed.Basic
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Word

/-!
# Mutation words and reachable Y-seeds

A word acts in reading order. Reversal undoes the action, and adjacent equal directions
cancel even inside a longer word. Coefficient specialization, matrix projection and
simultaneous relabelling transport the word action using `List.foldl_hom`.

Reachability is an equivalence relation, and its class is unchanged on replacing the
initial seed by any reachable seed. These statements concern Y-seeds only: no Laurent chart,
classical cluster variable, or exchange-graph identification is asserted here.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Definitions 2.3–2.4.
-/

public section

namespace TauCeti.YSeed

variable {K K' P Q : Type*} [DecidableEq K] [CoefficientSemifield P]
  [CoefficientSemifield Q]

/-- Apply mutations in the order in which their directions occur in the word. -/
def mutationWord (s : YSeed K P) (w : List K) : YSeed K P :=
  w.foldl mutation s

/-- The word action is the left fold of single-step Y-seed mutation. -/
theorem mutationWord_eq_foldl (s : YSeed K P) (w : List K) :
    s.mutationWord w = w.foldl mutation s := (rfl)

@[simp]
theorem mutationWord_nil (s : YSeed K P) : s.mutationWord [] = s := (rfl)

@[simp]
theorem mutationWord_cons (s : YSeed K P) (k : K) (w : List K) :
    s.mutationWord (k :: w) = (s.mutation k).mutationWord w := (rfl)

/-- The action of concatenation is the successive action of the two words. -/
@[simp]
theorem mutationWord_append (s : YSeed K P) (u v : List K) :
    s.mutationWord (u ++ v) = (s.mutationWord u).mutationWord v :=
  List.foldl_append

/-- A consecutive pair of equal letters can be cancelled anywhere in a word. -/
theorem mutationWord_cancel (s : YSeed K P) (u v : List K) (k : K) :
    s.mutationWord (u ++ k :: k :: v) = s.mutationWord (u ++ v) := by
  simp

/-- The reversed word recovers the initial seed. -/
@[simp]
theorem mutationWord_reverse (s : YSeed K P) (w : List K) :
    (s.mutationWord w).mutationWord w.reverse = s :=
  foldl_reverse_foldl_of_involutive mutation mutation_involutive w s

/-- Each word acts by a bijection, with inverse given by the reversed word. -/
def mutationWordEquiv (w : List K) : YSeed K P ≃ YSeed K P where
  toFun s := s.mutationWord w
  invFun s := s.mutationWord w.reverse
  left_inv s := s.mutationWord_reverse w
  right_inv s := by simpa using s.mutationWord_reverse w.reverse

@[simp]
theorem mutationWordEquiv_apply (w : List K) (s : YSeed K P) :
    mutationWordEquiv w s = s.mutationWord w := (rfl)

@[simp]
theorem mutationWordEquiv_symm (w : List K) :
    (mutationWordEquiv (P := P) w).symm = mutationWordEquiv w.reverse := by
  apply Equiv.ext
  intro s
  rfl

@[simp]
theorem mutationWordEquiv_nil :
    mutationWordEquiv (K := K) (P := P) [] = Equiv.refl (YSeed K P) := by
  apply Equiv.ext
  intro s
  rfl

/-- Concatenation of words corresponds to composition of their seed equivalences. -/
theorem mutationWordEquiv_append (u v : List K) :
    mutationWordEquiv (P := P) (u ++ v) = (mutationWordEquiv u).trans (mutationWordEquiv v) := by
  apply Equiv.ext
  intro s
  exact s.mutationWord_append u v

/-- Forgetting coefficients commutes with the word action. -/
@[simp]
theorem mutationWord_exchangeMatrix (s : YSeed K P) (w : List K) :
    (s.mutationWord w).exchangeMatrix = s.exchangeMatrix.mutationWord w := by
  rw [ExchangeMatrix.mutationWord_eq_foldl]
  exact (List.foldl_hom (fun s : YSeed K P ↦ s.exchangeMatrix)
    (fun s k ↦ (s.mutation_exchangeMatrix k).symm)).symm

/-- Specializing coefficients transports any finite mutation pattern. -/
@[simp]
theorem map_mutationWord (s : YSeed K P) (f : CoefficientSemifieldHom P Q) (w : List K) :
    (s.mutationWord w).map f = (s.map f).mutationWord w := by
  exact (List.foldl_hom (fun s : YSeed K P ↦ s.map f)
    (fun s k ↦ (s.map_mutation f k).symm)).symm

/-- Relabelling transports both the seed and every direction of its mutation word. -/
theorem reindex_mutationWord [DecidableEq K'] (e : K ≃ K') (s : YSeed K P) (w : List K) :
    reindex e (s.mutationWord w) = (reindex e s).mutationWord (w.map e) := by
  simp only [mutationWord, List.foldl_map]
  exact (List.foldl_hom (reindex (P := P) e) (fun s k ↦ s.mutation_reindex e k)).symm

/-! ### Reachability -/

/-- A Y-seed is reachable from another if a finite mutation word takes one to the other. -/
def Reachable (s t : YSeed K P) : Prop := ∃ w : List K, s.mutationWord w = t

/-- Applying a word always gives a reachable seed. -/
theorem reachable_mutationWord (s : YSeed K P) (w : List K) :
    Reachable s (s.mutationWord w) := ⟨w, rfl⟩

/-- Every seed is reachable by the empty word. -/
@[refl]
theorem Reachable.refl (s : YSeed K P) : Reachable s s := ⟨[], rfl⟩

/-- Reverse a witnessing word to reverse reachability. -/
@[symm]
theorem Reachable.symm {s t : YSeed K P} (h : Reachable s t) : Reachable t s := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w.reverse, s.mutationWord_reverse w⟩

/-- Concatenate witnessing words to compose reachability. -/
@[trans]
theorem Reachable.trans {s t u : YSeed K P} (h : Reachable s t) (h' : Reachable t u) :
    Reachable s u := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨w ++ v, s.mutationWord_append w v⟩

/-- Mutation reachability is an equivalence relation. -/
theorem reachable_equivalence : Equivalence (Reachable (K := K) (P := P)) :=
  ⟨Reachable.refl, Reachable.symm, Reachable.trans⟩

/-- Replacing the initial seed by any reachable seed leaves its reachable class unchanged. -/
theorem Reachable.reachable_iff {s t u : YSeed K P} (h : Reachable s t) :
    Reachable t u ↔ Reachable s u :=
  ⟨h.trans, h.symm.trans⟩

/-- Specialization takes reachable seeds to reachable seeds, without injectivity assumptions. -/
theorem Reachable.map {s t : YSeed K P} (h : Reachable s t)
    (f : CoefficientSemifieldHom P Q) : Reachable (s.map f) (t.map f) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w, (s.map_mutationWord f w).symm⟩

/-- Relabelling preserves and reflects reachability. -/
@[simp]
theorem reachable_reindex_iff [DecidableEq K'] (e : K ≃ K') (s t : YSeed K P) :
    Reachable (reindex e s) (reindex e t) ↔ Reachable s t := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.map e.symm, ?_⟩
    apply (reindex (P := P) e).injective
    simpa [reindex_mutationWord, List.map_map] using hw
  · rintro ⟨w, rfl⟩
    exact ⟨w.map e, (reindex_mutationWord e s w).symm⟩

end TauCeti.YSeed
