/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.Flip

/-!
# The middle loops of a stack of three Brauer diagrams

The Brauer algebra `B_k(δ)` multiplies its diagram basis by loop-weighted stacking,
`D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂`. Stacking itself is associative
(`TauCeti.composeDiagram_assoc`), so this multiplication is associative exactly when the powers
of `δ` agree as well:

```text
middleLoopCount D₁ D₂ + middleLoopCount (D₁ ∘ D₂) D₃
  = middleLoopCount D₂ D₃ + middleLoopCount D₁ (D₂ ∘ D₃),
```

writing `D₁ ∘ D₂` for `composeDiagram D₁ D₂`. This file proves that identity,
`TauCeti.middleLoopCount_add_middleLoopCount_composeDiagram`. Both sides count the closed loops
of the stack of `D₁` above `D₂` above `D₃`.

## Main results

* `TauCeti.middleLoopCount_add_middleLoopCount_composeDiagram`: **the loop counts of the two
  bracketings of a stack of three Brauer diagrams agree**, the loop-count half of the
  associativity of the Brauer algebra.

## Implementation notes

The stack of three diagrams has two middle boundaries, an upper one between `D₁` and `D₂` and a
lower one between `D₂` and `D₃`, and its arcs that stay off the outer boundary form a graph on
their points: the caps of `D₁` and the cups of `D₂` on the upper boundary, the caps of `D₂` and
the cups of `D₃` on the lower one, and the through strands of `D₂` between them. A closed loop is
a connected component of that graph all of whose points keep both of their arcs inside it; the
components are counted as classes of the quotient by the graph. In the bracketing
`(D₁ ∘ D₂) ∘ D₃`, the loops lying on the upper boundary alone are the middle loops of `D₁` above
`D₂`, and the loops meeting the lower boundary are the middle loops of `D₁ ∘ D₂` above `D₃`: a
cap of `D₁ ∘ D₂` is a cap of `D₂`, or else a strand running up through `D₂`, along the upper
boundary, and down again.

Reflecting the stack in a horizontal line reverses it and exchanges its two middle boundaries
(`TauCeti.flip_composeDiagram`, `TauCeti.middleLoopCount_flip`), so the count for the other
bracketing `D₁ ∘ (D₂ ∘ D₃)` is the same count read upside down, and only one bracketing needs an
argument. The stack of three and its loop count are private to this file.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

namespace TauCeti

open Relation

variable {k : ℕ}

/-! ### The middle graph of a stack of three diagrams -/

/-- **The middle graph of the stack of `D₁` above `D₂` above `D₃`.** Its vertices are the points
of the two middle boundaries, `Sum.inl a` the point `a` of the upper one, between `D₁` and `D₂`,
and `Sum.inr a` the point `a` of the lower one, between `D₂` and `D₃`. Two of them are adjacent
when an arc joins them: on the upper boundary a cap of `D₁` or a cup of `D₂`, between the two
boundaries a through strand of `D₂`, and on the lower boundary a cap of `D₂` or a cup of `D₃`. -/
private def TripleAdj (D₁ D₂ D₃ : BrauerDiagram k) : Fin k ⊕ Fin k → Fin k ⊕ Fin k → Prop
  | Sum.inl a, Sum.inl b => MiddleAdj D₁ D₂ a b
  | Sum.inl a, Sum.inr b => D₂.val (Sum.inr a) = Sum.inl b
  | Sum.inr a, Sum.inl b => D₂.val (Sum.inl a) = Sum.inr b
  | Sum.inr a, Sum.inr b => MiddleAdj D₂ D₃ a b

/-- Both arcs at a vertex of the middle graph of a stack of three diagrams stay in the middle:
the arc of `D₂` always does, so this asks for a cap of `D₁` at an upper point and for a cup of
`D₃` at a lower point. -/
private def IsTripleInterior (D₁ D₃ : BrauerDiagram k) : Fin k ⊕ Fin k → Prop
  | Sum.inl a => D₁.IsCap (Sum.inl a)
  | Sum.inr a => D₃.IsCup (Sum.inr a)

/-- A vertex of the middle graph of a stack of three diagrams lies on a closed loop. -/
private def OnTripleLoop (D₁ D₂ D₃ : BrauerDiagram k) (p : Fin k ⊕ Fin k) : Prop :=
  ∀ q, ReflTransGen (TripleAdj D₁ D₂ D₃) p q → IsTripleInterior D₁ D₃ q

/-- The number of closed loops of the stack of `D₁` above `D₂` above `D₃`, counted as connected
components of its middle graph, that is as classes of the quotient by it. -/
private noncomputable def tripleLoopCount (D₁ D₂ D₃ : BrauerDiagram k) : ℕ :=
  (Quot.mk (TripleAdj D₁ D₂ D₃) '' {p | OnTripleLoop D₁ D₂ D₃ p}).ncard

variable {D₁ D₂ D₃ : BrauerDiagram k}

/-- An arc of the stack of three from an upper point down to a lower point is a through strand of
`D₂`. -/
private theorem tripleAdj_inl_inr {a b : Fin k} :
    TripleAdj D₁ D₂ D₃ (Sum.inl a) (Sum.inr b) ↔ D₂.val (Sum.inr a) = Sum.inl b := Iff.rfl

/-- An arc of the stack of three from a lower point up to an upper point is a through strand of
`D₂`. -/
private theorem tripleAdj_inr_inl {a b : Fin k} :
    TripleAdj D₁ D₂ D₃ (Sum.inr a) (Sum.inl b) ↔ D₂.val (Sum.inl a) = Sum.inr b := Iff.rfl

private theorem TripleAdj.symm {p q : Fin k ⊕ Fin k} (h : TripleAdj D₁ D₂ D₃ p q) :
    TripleAdj D₁ D₂ D₃ q p := by
  rcases p with a | a <;> rcases q with b | b
  · exact MiddleAdj.symm (D₁ := D₁) (D₂ := D₂) h
  · exact D₂.apply_eq_of_apply_eq (x := Sum.inr a) h
  · exact D₂.apply_eq_of_apply_eq (x := Sum.inl a) h
  · exact MiddleAdj.symm (D₁ := D₂) (D₂ := D₃) h

private theorem mk_tripleAdj_eq_mk_iff {p q : Fin k ⊕ Fin k} :
    Quot.mk (TripleAdj D₁ D₂ D₃) p = Quot.mk (TripleAdj D₁ D₂ D₃) q ↔
      ReflTransGen (TripleAdj D₁ D₂ D₃) p q := by
  have : Std.Symm (TripleAdj D₁ D₂ D₃) := ⟨fun _ _ h => TripleAdj.symm h⟩
  rw [Quot.eq, EqvGen.eqvGen_eq_reflTransGen]

private theorem OnTripleLoop.reflTransGen {p q : Fin k ⊕ Fin k} (hp : OnTripleLoop D₁ D₂ D₃ p)
    (hpq : ReflTransGen (TripleAdj D₁ D₂ D₃) p q) : OnTripleLoop D₁ D₂ D₃ q :=
  fun r hr => hp r (hpq.trans hr)

/-- The upper boundary of the stack of three carries the middle graph of `D₁` above `D₂`. -/
private theorem reflTransGen_tripleAdj_inl {a b : Fin k}
    (h : ReflTransGen (MiddleAdj D₁ D₂) a b) :
    ReflTransGen (TripleAdj D₁ D₂ D₃) (Sum.inl a) (Sum.inl b) :=
  h.lift Sum.inl fun _ _ h => h

/-! ### Reflecting the stack of three -/

private theorem tripleAdj_flip (p q : Fin k ⊕ Fin k) :
    TripleAdj D₃.flip D₂.flip D₁.flip p q ↔ TripleAdj D₁ D₂ D₃ p.swap q.swap := by
  rcases p with a | a <;> rcases q with b | b
  · exact middleAdj_flip D₂ D₃ a b
  · rcases h : D₂.val (Sum.inl a) with m | m <;> simp [TripleAdj, h]
  · rcases h : D₂.val (Sum.inr a) with m | m <;> simp [TripleAdj, h]
  · exact middleAdj_flip D₁ D₂ a b

private theorem isTripleInterior_flip (p : Fin k ⊕ Fin k) :
    IsTripleInterior D₃.flip D₁.flip p ↔ IsTripleInterior D₁ D₃ p.swap := by
  rcases p with a | a
  · exact BrauerDiagram.isCap_flip D₃ (Sum.inl a)
  · exact BrauerDiagram.isCup_flip D₁ (Sum.inr a)

private theorem reflTransGen_tripleAdj_flip (p q : Fin k ⊕ Fin k) :
    ReflTransGen (TripleAdj D₃.flip D₂.flip D₁.flip) p q ↔
      ReflTransGen (TripleAdj D₁ D₂ D₃) p.swap q.swap := by
  refine ⟨fun h => h.lift Sum.swap fun x y hxy => (tripleAdj_flip x y).mp hxy, fun h => ?_⟩
  simpa [Function.onFun] using h.lift Sum.swap fun x y hxy =>
    (tripleAdj_flip x.swap y.swap).mpr (by rwa [Sum.swap_swap, Sum.swap_swap])

/-- **Reflection preserves the loops of a stack of three**: turning the stack of `D₁` above `D₂`
above `D₃` upside down gives the stack of the reflections in the reverse order, whose middle
graph is the same graph with its two middle boundaries exchanged. -/
private theorem tripleLoopCount_flip (D₁ D₂ D₃ : BrauerDiagram k) :
    tripleLoopCount D₃.flip D₂.flip D₁.flip = tripleLoopCount D₁ D₂ D₃ := by
  have hloop : ∀ p, OnTripleLoop D₃.flip D₂.flip D₁.flip p ↔ OnTripleLoop D₁ D₂ D₃ p.swap := by
    intro p
    refine ⟨fun h q hq => ?_, fun h q hq => ?_⟩
    · have := h q.swap ((reflTransGen_tripleAdj_flip p q.swap).mpr (by rwa [Sum.swap_swap]))
      rwa [isTripleInterior_flip, Sum.swap_swap] at this
    · exact (isTripleInterior_flip q).mpr (h q.swap ((reflTransGen_tripleAdj_flip p q).mp hq))
  -- reflection carries the class of `p` to the class of `p.swap`
  let Φ : Quot (TripleAdj D₃.flip D₂.flip D₁.flip) → Quot (TripleAdj D₁ D₂ D₃) :=
    Quot.lift (fun p => Quot.mk _ p.swap) fun p q h => Quot.sound ((tripleAdj_flip p q).mp h)
  refine Set.ncard_congr (fun x _ => Φ x) ?_ ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.swap, (hloop p).mp hp, rfl⟩
  · intro x y hx hy h
    obtain ⟨p, -, rfl⟩ := hx
    obtain ⟨q, -, rfl⟩ := hy
    exact mk_tripleAdj_eq_mk_iff.mpr
      ((reflTransGen_tripleAdj_flip p q).mpr (mk_tripleAdj_eq_mk_iff.mp h))
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨_, ⟨p.swap, (hloop p.swap).mpr (by rwa [Sum.swap_swap]), rfl⟩,
      congrArg (Quot.mk _) (Sum.swap_swap p)⟩

/-! ### The strands of the stack of `D₁` above `D₂` in the stack of three -/

/-- The strand of the stack of `D₁` above `D₂` starting at the bottom point `i` reaches the
middle state `t`. -/
private def OnStrand (D₁ D₂ : BrauerDiagram k) (i : Fin k) (t : Fin k ⊕ Fin k) : Prop :=
  ∃ s, stackStart D₁ D₂ (Sum.inl i) = Sum.inr s ∧
    ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t

/-- A strand reaches the middle point `a` about to run down through `D₂` only along a cap of
`D₁` ending at `a`. -/
private theorem OnStrand.exists_of_inr {i a : Fin k} (ht : OnStrand D₁ D₂ i (Sum.inr a)) :
    ∃ b, OnStrand D₁ D₂ i (Sum.inl b) ∧ D₁.val (Sum.inl b) = Sum.inl a := by
  obtain ⟨s, hs, hpath⟩ := ht
  rcases hpath.cases_tail with rfl | ⟨u, hu, hstep⟩
  · exact absurd (stackStart_eq_inr_inr_iff.mp hs).1 (by simp)
  · obtain ⟨b, rfl, hb⟩ := stackStep_eq_inr_inr_iff.mp hstep
    exact ⟨b, ⟨s, hs, hu⟩, D₁.apply_eq_of_apply_eq hb⟩

/-- A strand reaches the middle point `a` about to run up through `D₁` either along its first
arc, a through strand of `D₂`, or along a cup of `D₂` ending at `a`. -/
private theorem OnStrand.exists_of_inl {i a : Fin k} (ht : OnStrand D₁ D₂ i (Sum.inl a)) :
    D₂.val (Sum.inl i) = Sum.inr a ∨
      ∃ b, OnStrand D₁ D₂ i (Sum.inr b) ∧ D₂.val (Sum.inr b) = Sum.inr a := by
  obtain ⟨s, hs, hpath⟩ := ht
  rcases hpath.cases_tail with rfl | ⟨u, hu, hstep⟩
  · exact Or.inl (D₂.apply_eq_of_apply_eq (stackStart_eq_inr_inl_iff.mp hs).2)
  · obtain ⟨b, rfl, hb⟩ := stackStep_eq_inr_inl_iff.mp hstep
    exact Or.inr ⟨b, ⟨s, hs, hu⟩, D₂.apply_eq_of_apply_eq hb⟩

/-- **A strand runs through the whole upper component it enters**: an arc of the middle graph of
`D₁` above `D₂` at a middle point of the strand leads to another middle point of the strand. -/
private theorem OnStrand.exists_of_middleAdj {i c : Fin k} {t : Fin k ⊕ Fin k}
    (ht : OnStrand D₁ D₂ i t) (h : MiddleAdj D₁ D₂ (middlePoint t) c) :
    ∃ t', OnStrand D₁ D₂ i t' ∧ middlePoint t' = c :=
  let ⟨s, hs, hpath⟩ := ht
  let ⟨t', hpath', ht'⟩ := exists_reflTransGen_stackStep_of_middleAdj hs hpath h
  ⟨t', ⟨s, hs, hpath'⟩, ht'⟩

/-- A through strand of `D₂` leaving a middle point of the strand from the bottom point `i` down to
the bottom point `i'` either retraces the first arc of the strand or ends it: then `D₁ ∘ D₂` has a
cap joining `i` to `i'`. -/
private theorem OnStrand.eq_or_composeDiagram {i i' : Fin k} {t : Fin k ⊕ Fin k}
    (ht : OnStrand D₁ D₂ i t) (h : D₂.val (Sum.inr (middlePoint t)) = Sum.inl i') :
    i' = i ∨ (composeDiagram D₁ D₂).val (Sum.inl i) = Sum.inl i' :=
  let ⟨_, hs, hpath⟩ := ht
  (eq_or_composeDiagram_val_eq_inl_of_reflTransGen_stackStep hs hpath h).imp
    (fun h => Sum.inl_injective h) id

/-- If `D₁ ∘ D₂` has a cap at the bottom point `i`, then every middle point the strand from `i`
reaches carries a cap of `D₁`: a through strand of `D₁` there would carry the strand out of the
top of the stack. -/
private theorem OnStrand.isCap {i : Fin k} {t : Fin k ⊕ Fin k} (ht : OnStrand D₁ D₂ i t)
    (hcap : (composeDiagram D₁ D₂).IsCap (Sum.inl i)) : D₁.IsCap (Sum.inl (middlePoint t)) := by
  rcases t with a | a <;> simp only [middlePoint_inl, middlePoint_inr]
  · rcases hv : D₁.val (Sum.inl a) with b | j
    · simp [BrauerDiagram.isCap_def, hv]
    obtain ⟨s, hs, hpath⟩ := ht
    have hval : (composeDiagram D₁ D₂).val (Sum.inl i) = Sum.inr j :=
      (composeDiagram_val_eq_iff D₁ D₂).mpr
        (Or.inr ⟨s, Sum.inl a, hs, hpath, by simp [stackStep_inl, hv]⟩)
    simp [BrauerDiagram.isCap_def, hval] at hcap
  · obtain ⟨b, -, hba⟩ := ht.exists_of_inr
    simp [BrauerDiagram.isCap_def, D₁.apply_eq_of_apply_eq hba]

/-- An arc of the middle graph of `D₁` above `D₂` traversed by a strand. -/
private theorem middleAdj_of_stackStep {u v : Fin k ⊕ Fin k}
    (h : stackStep D₁ D₂ u = Sum.inr v) : MiddleAdj D₁ D₂ (middlePoint u) (middlePoint v) := by
  rcases u with a | a
  · obtain ⟨b, rfl, hb⟩ := stackStep_inl_eq_inr_iff.mp h
    rw [middlePoint_inl, middlePoint_inr, middleAdj_def]
    exact Or.inl hb
  · obtain ⟨b, rfl, hb⟩ := stackStep_inr_eq_inr_iff.mp h
    rw [middlePoint_inl, middlePoint_inr, middleAdj_def]
    exact Or.inr hb

/-- **A strand of the stack of `D₁` above `D₂` from a bottom point is a path in the stack of
three**, from the corresponding lower point to the upper points it runs through. -/
private theorem OnStrand.reflTransGen_tripleAdj {i : Fin k} {t : Fin k ⊕ Fin k}
    (ht : OnStrand D₁ D₂ i t) :
    ReflTransGen (TripleAdj D₁ D₂ D₃) (Sum.inr i) (Sum.inl (middlePoint t)) := by
  obtain ⟨s, hs, hpath⟩ := ht
  obtain ⟨a, rfl, ha⟩ := stackStart_inl_eq_inr_iff.mp hs
  have h := reflTransGen_tripleAdj_inl (D₃ := D₃)
    (hpath.lift middlePoint fun _ _ h => middleAdj_of_stackStep h)
  rw [middlePoint_inl] at h
  exact (ReflTransGen.single (tripleAdj_inr_inl.mpr ha)).trans h

/-! ### The loops of the stack of three meeting the lower boundary -/

/-- **An arc of the middle graph of `D₁ ∘ D₂` above `D₃` is a path in the stack of three.** A
cup of `D₃` is an arc of it already, and a cap of `D₁ ∘ D₂` is a cap of `D₂` or a strand of the
stack of `D₁` above `D₂` running up through `D₂`, along the upper boundary, and down again. -/
private theorem reflTransGen_tripleAdj_of_middleAdj {a b : Fin k}
    (h : MiddleAdj (composeDiagram D₁ D₂) D₃ a b) :
    ReflTransGen (TripleAdj D₁ D₂ D₃) (Sum.inr a) (Sum.inr b) := by
  rcases (middleAdj_def _ _ _ _).mp h with h | h
  · rcases (composeDiagram_val_eq_iff D₁ D₂).mp h with hs | ⟨s, t, hs, hpath, ht⟩
    · refine .single ((middleAdj_def _ _ _ _).mpr (Or.inl ?_))
      rw [stackStart_inl] at hs
      rcases hv : D₂.val (Sum.inl a) with i' | c <;> simp_all
    · rcases t with c | c
      · rcases hv : D₁.val (Sum.inl c) with c' | j <;> simp [hv] at ht
      · have hc : D₂.val (Sum.inr c) = Sum.inl b := by
          rcases hv : D₂.val (Sum.inr c) with i' | c' <;> simp_all
        have h₁ := OnStrand.reflTransGen_tripleAdj (D₃ := D₃) ⟨s, hs, hpath⟩
        rw [middlePoint_inr] at h₁
        exact h₁.tail hc
  · exact .single ((middleAdj_def _ _ _ _).mpr (Or.inr h))

/-- The points of the stack of three reachable from the lower point `a`: the lower points `b`
reachable from `a` in the middle graph of `D₁ ∘ D₂` above `D₃`, and the upper points on the
strands of the stack of `D₁` above `D₂` from those `b`. -/
private def TripleRegion (D₁ D₂ D₃ : BrauerDiagram k) (a : Fin k) : Fin k ⊕ Fin k → Prop
  | Sum.inl c => ∃ i t, ReflTransGen (MiddleAdj (composeDiagram D₁ D₂) D₃) a i ∧
      OnStrand D₁ D₂ i t ∧ middlePoint t = c
  | Sum.inr b => ReflTransGen (MiddleAdj (composeDiagram D₁ D₂) D₃) a b

private theorem tripleRegion_of_tripleAdj {a : Fin k} {p q : Fin k ⊕ Fin k}
    (hp : TripleRegion D₁ D₂ D₃ a p) (h : TripleAdj D₁ D₂ D₃ p q) :
    TripleRegion D₁ D₂ D₃ a q := by
  rcases p with c | b <;> rcases q with c' | b'
  · obtain ⟨i, t, hi, ht, rfl⟩ := hp
    obtain ⟨t', ht', hmid⟩ := ht.exists_of_middleAdj h
    exact ⟨i, t', hi, ht', hmid⟩
  · obtain ⟨i, t, hi, ht, rfl⟩ := hp
    rcases ht.eq_or_composeDiagram h with rfl | hcap
    · exact hi
    · exact hi.tail ((middleAdj_def _ _ _ _).mpr (Or.inl hcap))
  · exact ⟨b, Sum.inl c', hp, ⟨Sum.inl c', stackStart_inl_eq_inr_iff.mpr ⟨c', rfl, h⟩, .refl⟩,
      middlePoint_inl c'⟩
  · rcases (middleAdj_def _ _ _ _).mp h with h | h
    · exact ReflTransGen.tail (b := b) hp ((middleAdj_def _ _ _ _).mpr
        (Or.inl (composeDiagram_val_inl_eq_inl_of_cap_lower D₁ D₂ h)))
    · exact ReflTransGen.tail (b := b) hp ((middleAdj_def _ _ _ _).mpr (Or.inr h))

private theorem tripleRegion_of_reflTransGen {a : Fin k} {q : Fin k ⊕ Fin k}
    (h : ReflTransGen (TripleAdj D₁ D₂ D₃) (Sum.inr a) q) : TripleRegion D₁ D₂ D₃ a q := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hpq ih => exact tripleRegion_of_tripleAdj ih hpq

/-- Two lower points are joined in the stack of three exactly when they are joined in the middle
graph of `D₁ ∘ D₂` above `D₃`. -/
private theorem reflTransGen_tripleAdj_inr_iff {a b : Fin k} :
    ReflTransGen (TripleAdj D₁ D₂ D₃) (Sum.inr a) (Sum.inr b) ↔
      ReflTransGen (MiddleAdj (composeDiagram D₁ D₂) D₃) a b :=
  ⟨tripleRegion_of_reflTransGen,
    fun h => h.lift' Sum.inr fun _ _ h => reflTransGen_tripleAdj_of_middleAdj h⟩

/-- A lower point lies on a loop of the stack of three exactly when it lies on a middle loop of
`D₁ ∘ D₂` above `D₃`. -/
private theorem onTripleLoop_inr_iff {a : Fin k} :
    OnTripleLoop D₁ D₂ D₃ (Sum.inr a) ↔ OnMiddleLoop (composeDiagram D₁ D₂) D₃ a := by
  refine ⟨fun h => (onMiddleLoop_def _ _ _).mpr fun b hab => (isMiddleVertex_def _ _ _).mpr
    ⟨?_, h _ (reflTransGen_tripleAdj_inr_iff.mpr hab)⟩, fun h q hq => ?_⟩
  · rcases hv : (composeDiagram D₁ D₂).val (Sum.inl b) with b' | j
    · simp [BrauerDiagram.isCap_def, hv]
    -- the strand from `b` leaves the stack of `D₁` above `D₂` through a point of the upper
    -- boundary carrying a through strand of `D₁`
    rcases (composeDiagram_val_eq_iff D₁ D₂).mp hv with hs | ⟨s, t, hs, hpath, ht⟩
    · rw [stackStart_inl] at hs
      rcases hv' : D₂.val (Sum.inl b) with i' | c <;> simp [hv'] at hs
    · rcases t with c | c
      · have hc : D₁.val (Sum.inl c) = Sum.inr j := by
          rcases hv' : D₁.val (Sum.inl c) with c' | j' <;> simp_all
        have hint := h _ ((reflTransGen_tripleAdj_inr_iff.mpr hab).trans
          (OnStrand.reflTransGen_tripleAdj ⟨s, hs, hpath⟩))
        simp [IsTripleInterior, BrauerDiagram.isCap_def, hc] at hint
      · rcases hv' : D₂.val (Sum.inr c) with i' | c' <;> simp [hv'] at ht
  · have hint : ∀ b, ReflTransGen (MiddleAdj (composeDiagram D₁ D₂) D₃) a b →
        (composeDiagram D₁ D₂).IsCap (Sum.inl b) ∧ D₃.IsCup (Sum.inr b) := fun b hb =>
      (isMiddleVertex_def _ _ _).mp ((onMiddleLoop_def _ _ _).mp h b hb)
    rcases q with c | b
    · obtain ⟨i, t, hi, ht, rfl⟩ := tripleRegion_of_reflTransGen hq
      exact ht.isCap (hint i hi).1
    · exact (hint b (tripleRegion_of_reflTransGen hq)).2

/-! ### The loops of the stack of three on the upper boundary alone -/

/-- From a point of a middle loop of `D₁` above `D₂`, the stack of three reaches only points of
that loop. -/
private theorem OnMiddleLoop.reflTransGen_tripleAdj {c : Fin k} {q : Fin k ⊕ Fin k}
    (hc : OnMiddleLoop D₁ D₂ c) (h : ReflTransGen (TripleAdj D₁ D₂ D₃) (Sum.inl c) q) :
    ∃ c', q = Sum.inl c' ∧ ReflTransGen (MiddleAdj D₁ D₂) c c' := by
  induction h with
  | refl => exact ⟨c, rfl, .refl⟩
  | @tail p q _ hpq ih =>
    obtain ⟨c', rfl, hcc'⟩ := ih
    rcases q with c'' | b
    · exact ⟨c'', rfl, hcc'.tail hpq⟩
    · have hcup := ((isMiddleVertex_def _ _ _).mp (hc.reflTransGen hcc').isMiddleVertex).2
      simp [BrauerDiagram.isCup_def, tripleAdj_inl_inr.mp hpq] at hcup

private theorem OnMiddleLoop.onTripleLoop {c : Fin k} (hc : OnMiddleLoop D₁ D₂ c) :
    OnTripleLoop D₁ D₂ D₃ (Sum.inl c) := by
  intro q hq
  obtain ⟨c', rfl, hcc'⟩ := hc.reflTransGen_tripleAdj hq
  exact ((isMiddleVertex_def _ _ _).mp (hc.reflTransGen hcc').isMiddleVertex).1

/-- An upper point on a loop of the stack of three whose component misses the lower boundary
lies on a middle loop of `D₁` above `D₂`. -/
private theorem OnTripleLoop.onMiddleLoop {c : Fin k} (hc : OnTripleLoop D₁ D₂ D₃ (Sum.inl c))
    (hlow : ∀ a, ¬ReflTransGen (TripleAdj D₁ D₂ D₃) (Sum.inl c) (Sum.inr a)) :
    OnMiddleLoop D₁ D₂ c := by
  refine (onMiddleLoop_def _ _ _).mpr fun b hb => ?_
  have hb₃ := reflTransGen_tripleAdj_inl (D₃ := D₃) hb
  refine (isMiddleVertex_def _ _ _).mpr ⟨hc _ hb₃, ?_⟩
  rcases hv : D₂.val (Sum.inr b) with i | b'
  · exact absurd (hb₃.tail (tripleAdj_inl_inr.mpr hv)) (hlow i)
  · simp [BrauerDiagram.isCup_def, hv]

/-! ### Counting the loops of the stack of three -/

/-- **The loops of the stack of three, read in the bracketing `(D₁ ∘ D₂) ∘ D₃`**: they are the
middle loops of `D₁` above `D₂` together with the middle loops of `D₁ ∘ D₂` above `D₃`. -/
private theorem tripleLoopCount_eq (D₁ D₂ D₃ : BrauerDiagram k) :
    tripleLoopCount D₁ D₂ D₃ =
      middleLoopCount D₁ D₂ + middleLoopCount (composeDiagram D₁ D₂) D₃ := by
  set M := Quot.mk (TripleAdj D₁ D₂ D₃) with hMdef
  have hM : ∀ {p q}, M p = M q ↔ ReflTransGen (TripleAdj D₁ D₂ D₃) p q := mk_tripleAdj_eq_mk_iff
  have hsplit : M '' {p | OnTripleLoop D₁ D₂ D₃ p} =
      (M ∘ Sum.inr) '' {a | OnMiddleLoop (composeDiagram D₁ D₂) D₃ a} ∪
        (M ∘ Sum.inl) '' {c | OnMiddleLoop D₁ D₂ c} := by
    ext S
    constructor
    · rintro ⟨p | p, hp, rfl⟩
      · by_cases hlow : ∃ a, ReflTransGen (TripleAdj D₁ D₂ D₃) (Sum.inl p) (Sum.inr a)
        · obtain ⟨a, ha⟩ := hlow
          exact Or.inl ⟨a, onTripleLoop_inr_iff.mp (hp.reflTransGen ha), (hM.mpr ha).symm⟩
        · exact Or.inr ⟨p, hp.onMiddleLoop (not_exists.mp hlow), rfl⟩
      · exact Or.inl ⟨p, onTripleLoop_inr_iff.mp hp, rfl⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨c, hc, rfl⟩)
      · exact ⟨Sum.inr a, onTripleLoop_inr_iff.mpr ha, rfl⟩
      · exact ⟨Sum.inl c, (hc : OnMiddleLoop D₁ D₂ c).onTripleLoop, rfl⟩
  have hdisj : Disjoint ((M ∘ Sum.inr) '' {a | OnMiddleLoop (composeDiagram D₁ D₂) D₃ a})
      ((M ∘ Sum.inl) '' {c | OnMiddleLoop D₁ D₂ c}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, -, rfl⟩ ⟨c, hc, hS⟩
    obtain ⟨c', h, -⟩ := (hc : OnMiddleLoop D₁ D₂ c).reflTransGen_tripleAdj (hM.mp hS)
    simp at h
  -- the loops meeting the lower boundary are the middle loops of `D₁ ∘ D₂` above `D₃`
  have hlower : ((M ∘ Sum.inr) '' {a | OnMiddleLoop (composeDiagram D₁ D₂) D₃ a}).ncard =
      middleLoopCount (composeDiagram D₁ D₂) D₃ := by
    let Φ : Quot (MiddleAdj (composeDiagram D₁ D₂) D₃) → Quot (TripleAdj D₁ D₂ D₃) :=
      Quot.lift (fun a => M (Sum.inr a)) fun _ _ h => hM.mpr (reflTransGen_tripleAdj_of_middleAdj h)
    -- `Quot.lift` computes on classes, so `Φ` sends the class of `a` to the class of `Sum.inr a`
    have hΦ : M ∘ Sum.inr = Φ ∘ Quot.mk _ := rfl
    rw [hΦ, Set.image_comp, middleLoopCount_eq_ncard_image]
    refine Set.InjOn.ncard_image ?_
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ h
    exact (mk_middleAdj_eq_mk_iff _ _).mpr (reflTransGen_tripleAdj_inr_iff.mp (hM.mp h))
  -- the loops missing the lower boundary are the middle loops of `D₁` above `D₂`
  have hupper : ((M ∘ Sum.inl) '' {c | OnMiddleLoop D₁ D₂ c}).ncard = middleLoopCount D₁ D₂ := by
    let Ψ : Quot (MiddleAdj D₁ D₂) → Quot (TripleAdj D₁ D₂ D₃) :=
      Quot.lift (fun c => M (Sum.inl c)) fun _ _ h => hM.mpr (.single h)
    have hΨ : M ∘ Sum.inl = Ψ ∘ Quot.mk _ := rfl
    rw [hΨ, Set.image_comp, middleLoopCount_eq_ncard_image]
    refine Set.InjOn.ncard_image ?_
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', -, rfl⟩ h
    obtain ⟨c'', h, hcc''⟩ := (hc : OnMiddleLoop D₁ D₂ c).reflTransGen_tripleAdj (hM.mp h)
    rw [Sum.inl_injective h]
    exact (mk_middleAdj_eq_mk_iff _ _).mpr hcc''
  rw [tripleLoopCount, ← hMdef, hsplit, Set.ncard_union_eq hdisj, hlower, hupper, add_comm]

/-- **The loop counts of the two bracketings of a stack of three Brauer diagrams agree.**
Stacking `D₁` above `D₂` and the composite above `D₃` closes up as many loops in the middle as
stacking `D₂` above `D₃` and `D₁` above the composite. With `TauCeti.composeDiagram_assoc` this
makes the loop-weighted stacking
`D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂` associative, which is the
associativity of the multiplication of the Brauer algebra on its diagram basis. -/
theorem middleLoopCount_add_middleLoopCount_composeDiagram (D₁ D₂ D₃ : BrauerDiagram k) :
    middleLoopCount D₁ D₂ + middleLoopCount (composeDiagram D₁ D₂) D₃ =
      middleLoopCount D₂ D₃ + middleLoopCount D₁ (composeDiagram D₂ D₃) := by
  rw [← tripleLoopCount_eq, ← tripleLoopCount_flip, tripleLoopCount_eq, middleLoopCount_flip,
    ← flip_composeDiagram, middleLoopCount_flip]

end TauCeti
