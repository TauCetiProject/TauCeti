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

Finite mutation words index chart-free Y-patterns from an initial seed. Their reversible
action defines mutation classes independently of the initial seed chosen in a class.
Specializing coefficients along a semifield homomorphism transports the entire pattern,
as do matrix projection and simultaneous relabelling. Words act in reading order,
and adjacent equal directions cancel even inside a longer word.

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
theorem mutationWord_append_cons_cons_self (s : YSeed K P) (u v : List K) (k : K) :
    s.mutationWord (u ++ k :: k :: v) = s.mutationWord (u ++ v) :=
  foldl_append_cons_cons_of_involutive mutation (mutation_involutive k) u v s

/-- The reversed word recovers the initial seed. -/
@[simp]
theorem mutationWord_mutationWord_reverse (s : YSeed K P) (w : List K) :
    (s.mutationWord w).mutationWord w.reverse = s :=
  foldl_reverse_foldl_of_involutive mutation mutation_involutive w s

/-- A reversed word also gives a right inverse to the Y-seed action. -/
@[simp]
theorem mutationWord_reverse_mutationWord (s : YSeed K P) (w : List K) :
    (s.mutationWord w.reverse).mutationWord w = s :=
  foldl_foldl_reverse_of_involutive mutation mutation_involutive w s

/-- A single mutation is injective on Y-seeds. -/
@[simp]
theorem mutation_eq_mutation_iff (s t : YSeed K P) (k : K) :
    s.mutation k = t.mutation k ↔ s = t :=
  (mutation_involutive k).injective.eq_iff

/-- Applying the same mutation word to two Y-seeds preserves equality exactly. -/
@[simp]
theorem mutationWord_eq_mutationWord_iff (s t : YSeed K P) (w : List K) :
    s.mutationWord w = t.mutationWord w ↔ s = t := by
  simpa only [mutationWord_eq_foldl] using
    foldl_eq_foldl_iff_of_involutive mutation mutation_involutive w s t

/-- Move a mutation word to the other side of an equality by reversing its directions. -/
theorem mutationWord_eq_iff (s t : YSeed K P) (w : List K) :
    s.mutationWord w = t ↔ s = t.mutationWord w.reverse := by
  simpa only [mutationWord_eq_foldl] using
    foldl_eq_iff_of_involutive mutation mutation_involutive w s t

/-- Each word acts by a bijection, with inverse given by the reversed word. -/
def mutationWordEquiv (w : List K) : YSeed K P ≃ YSeed K P :=
  foldlEquiv mutation mutation_involutive w

@[simp]
theorem mutationWordEquiv_apply (w : List K) (s : YSeed K P) :
    mutationWordEquiv w s = s.mutationWord w := foldlEquiv_apply _ _ _ _

@[simp]
theorem mutationWordEquiv_symm (w : List K) :
    (mutationWordEquiv (P := P) w).symm = mutationWordEquiv w.reverse :=
  foldlEquiv_symm _ _ _

@[simp]
theorem mutationWordEquiv_nil :
    mutationWordEquiv (K := K) (P := P) [] = Equiv.refl (YSeed K P) := foldlEquiv_nil _ _

/-- Concatenation of words corresponds to composition of their seed equivalences. -/
theorem mutationWordEquiv_append (u v : List K) :
    mutationWordEquiv (P := P) (u ++ v) = (mutationWordEquiv u).trans (mutationWordEquiv v) :=
  foldlEquiv_append _ _ _ _

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

/-- `Reachable s t` means that `t` is obtained from `s` by a finite mutation word. -/
def Reachable (s t : YSeed K P) : Prop := FoldReachable mutation s t

/-- Reachability is equivalent to existence of a word taking the initial seed to the target. -/
theorem reachable_def {s t : YSeed K P} :
    Reachable s t ↔ ∃ w : List K, s.mutationWord w = t := foldReachable_def

/-- Y-seed reachability is the reflexive-transitive closure of single mutations. -/
theorem reachable_iff_reflTransGen {s t : YSeed K P} :
    Reachable s t ↔
      Relation.ReflTransGen (fun x y : YSeed K P ↦ ∃ k : K, x.mutation k = y) s t :=
  foldReachable_iff_reflTransGen

/-- Prove a property along a reachable orbit using only steps starting in that orbit. -/
@[elab_as_elim]
theorem Reachable.induction {s t : YSeed K P} {motive : YSeed K P → Prop}
    (h : Reachable s t) (hs : motive s)
    (hstep : ∀ x k, Reachable s x → motive x → motive (x.mutation k)) : motive t :=
  FoldReachable.induction h hs hstep

/-- Applying a word always gives a reachable seed. -/
theorem reachable_mutationWord (s : YSeed K P) (w : List K) :
    Reachable s (s.mutationWord w) := foldReachable_foldl mutation s w

/-- A single mutation gives a reachable seed. -/
theorem reachable_mutation (s : YSeed K P) (k : K) : Reachable s (s.mutation k) :=
  foldReachable_apply mutation s k

/-- Every Y-seed is reachable from itself. -/
@[refl, simp]
theorem Reachable.refl (s : YSeed K P) : Reachable s s := FoldReachable.refl s

/-- Reachability of Y-seeds is symmetric. -/
@[symm]
theorem Reachable.symm {s t : YSeed K P} (h : Reachable s t) : Reachable t s :=
  FoldReachable.symm mutation_involutive h

/-- Reachability of Y-seeds is transitive. -/
@[trans]
theorem Reachable.trans {s t u : YSeed K P} (h : Reachable s t) (h' : Reachable t u) :
    Reachable s u := FoldReachable.trans h h'

/-- The endpoints of Y-seed reachability can be interchanged. -/
theorem reachable_comm (s t : YSeed K P) : Reachable s t ↔ Reachable t s :=
  FoldReachable.comm mutation_involutive s t

/-- Mutation reachability is an equivalence relation. -/
theorem reachable_equivalence : Equivalence (Reachable (K := K) (P := P)) :=
  FoldReachable.equivalence mutation_involutive

/-- Replacing the initial seed by any reachable seed leaves its reachable class unchanged. -/
theorem Reachable.congr_left {s t u : YSeed K P} (h : Reachable s t) :
    Reachable t u ↔ Reachable s u := FoldReachable.congr_left mutation_involutive h

/-- Replacing the target seed by any reachable seed preserves reachability. -/
theorem Reachable.congr_right {s t u : YSeed K P} (h : Reachable s t) :
    Reachable u t ↔ Reachable u s := FoldReachable.congr_right mutation_involutive h

/-- Mutation words on the initial seed do not alter its mutation class. -/
@[simp]
theorem reachable_mutationWord_left_iff (s t : YSeed K P) (w : List K) :
    Reachable (s.mutationWord w) t ↔ Reachable s t :=
  foldReachable_foldl_left_iff mutation mutation_involutive s t w

/-- Mutation words on the target seed do not alter its mutation class. -/
@[simp]
theorem reachable_mutationWord_right_iff (s t : YSeed K P) (w : List K) :
    Reachable s (t.mutationWord w) ↔ Reachable s t :=
  foldReachable_foldl_right_iff mutation mutation_involutive s t w

/-- A mutation of the initial seed does not alter its mutation class. -/
@[simp]
theorem reachable_mutation_left_iff (s t : YSeed K P) (k : K) :
    Reachable (s.mutation k) t ↔ Reachable s t :=
  foldReachable_apply_left_iff mutation (mutation_involutive k) s t

/-- A mutation of the target seed does not alter its mutation class. -/
@[simp]
theorem reachable_mutation_right_iff (s t : YSeed K P) (k : K) :
    Reachable s (t.mutation k) ↔ Reachable s t :=
  foldReachable_apply_right_iff mutation (mutation_involutive k) s t

/-- Specialization takes reachable seeds to reachable seeds, without injectivity assumptions. -/
theorem Reachable.map {s t : YSeed K P} (h : Reachable s t)
    (f : CoefficientSemifieldHom P Q) : Reachable (s.map f) (t.map f) :=
  FoldReachable.map h (fun s ↦ s.map f) id (fun s k ↦ s.map_mutation f k)

/-- Forgetting the coefficients takes reachable Y-seeds to reachable exchange matrices. -/
theorem Reachable.exchangeMatrix {s t : YSeed K P} (h : Reachable s t) :
    ExchangeMatrix.Reachable s.exchangeMatrix t.exchangeMatrix := by
  obtain ⟨w, rfl⟩ := reachable_def.mp h
  exact ExchangeMatrix.reachable_def.mpr ⟨w, (mutationWord_exchangeMatrix s w).symm⟩

/-- Relabelling preserves and reflects reachability. -/
@[simp]
theorem reachable_reindex_iff [DecidableEq K'] (e : K ≃ K') (s t : YSeed K P) :
    Reachable (reindex e s) (reindex e t) ↔ Reachable s t :=
  FoldReachable.equiv_iff (reindex e) e (fun s k ↦ (s.mutation_reindex e k).symm) s t

end TauCeti.YSeed
