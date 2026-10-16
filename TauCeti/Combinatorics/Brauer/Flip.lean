/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Brauer.LoopCount

/-!
# Turning a Brauer diagram upside down

Reflecting a Brauer diagram in a horizontal line exchanges its bottom and its top boundary.  On
the perfect matching of `Fin k ⊕ Fin k` that a diagram is, that reflection is conjugation by
`Sum.swap`, and this file builds it as `TauCeti.BrauerDiagram.flip`, together with its two
compatibilities with the vertical stacking of diagrams:

`flip (composeDiagram D₁ D₂) = composeDiagram (flip D₂) (flip D₁)`,
`middleLoopCount (flip D₂) (flip D₁) = middleLoopCount D₁ D₂`.

Reflection therefore reverses the order of a stack and leaves the number of loops that close up in
its middle alone, so `D ↦ flip D` reverses the loop-weighted stacking
`D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂` of diagrams.  That is the
diagram-level operation an anti-automorphism `(x y)* = y* x*` of the Brauer algebra `B_k(δ)` is
read off from; the algebra itself is not built here, and nothing below is a map of algebras.
Reflection is therefore a symmetry of the relations of that stacking: each relation between
diagrams has a mirror, the same stack turned upside down, and reflection carries one to the other.
A cap-cup diagram is its own reflection (`TauCeti.BrauerDiagram.flip_capCup`, stated beside
`TauCeti.capCup` in `TauCeti/Combinatorics/Brauer/Generator.lean`), so the relations between
cap-cup and permutation diagrams in `TauCeti/Combinatorics/Brauer/Relations.lean` come in mirror
pairs.

Reflection is an involution, exchanges caps with cups, inverts a permutation diagram, and on a
relabelled diagram exchanges the two renamings.

## The two stacking compatibilities

Reflecting the stack of `D₁` above `D₂` gives the stack of the reflection of `D₂` above the
reflection of `D₁`: a strand of either is a strand of the other read in the reflected labels, so
the two stacks match the same pairs of outer points once those are reflected
(`TauCeti.flip_composeDiagram`).

The middle of the stack is unchanged as a graph.  Two middle points are joined by an arc of it when
a cap of the upper diagram or a cup of the lower one joins them, and reflection exchanges those two
kinds of arc without moving the middle point, so the two stacks have literally the same middle
graph (`TauCeti.middleAdj_flip`) with the same interior vertices
(`TauCeti.isMiddleVertex_flip`).  Their closed loops, and hence their loop counts, therefore agree
(`TauCeti.middleLoopCount_flip`).

## Main definitions

* `TauCeti.BrauerDiagram.flip`: the Brauer diagram drawn upside down.

## Main results

* `TauCeti.BrauerDiagram.flip_flip`: reflection is an involution.
* `TauCeti.BrauerDiagram.isCap_flip` and `TauCeti.BrauerDiagram.isCup_flip`: reflection exchanges
  caps and cups, with `TauCeti.BrauerDiagram.bottomCap_flip` and
  `TauCeti.BrauerDiagram.topCup_flip` the same statements on the boundary `Finset`s.
* `TauCeti.BrauerDiagram.flip_permToBrauer`: reflection inverts a permutation diagram, and
  `TauCeti.BrauerDiagram.flip_relabel`: it exchanges the two renamings of a relabelling.
* `TauCeti.flip_composeDiagram`: **reflection reverses stacking.**
* `TauCeti.middleAdj_flip`, `TauCeti.reflTransGen_middleAdj_flip` and
  `TauCeti.isMiddleVertex_flip`: the two stacks have the same middle graph, with the same
  reachability and the same interior vertices.
* `TauCeti.middleLoopCount_flip`: **reflection preserves the middle-loop count.**

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
-/

public section

namespace TauCeti

variable {k : ℕ}

namespace BrauerDiagram

/-- **The reflection of a Brauer diagram in a horizontal line**: the same diagram drawn upside
down, its bottom point `i` becoming its top point `i` and conversely.  On the perfect matching it
is conjugation by `Sum.swap`. -/
def flip (D : BrauerDiagram k) : BrauerDiagram k :=
  PerfectMatching.congr (Equiv.sumComm (Fin k) (Fin k)) D

variable (D : BrauerDiagram k)

/-- The arcs of the reflected diagram are the arcs of the diagram with both endpoints
reflected. -/
@[simp]
theorem flip_val_swap (x : Fin k ⊕ Fin k) : D.flip.val x.swap = (D.val x).swap :=
  PerfectMatching.congr_val_apply_apply (Equiv.sumComm (Fin k) (Fin k)) D x

/-- The arc of the reflected diagram at `x` is the arc at the reflected point, reflected. -/
theorem flip_val (x : Fin k ⊕ Fin k) : D.flip.val x = (D.val x.swap).swap := by
  rw [← flip_val_swap D x.swap, Sum.swap_swap]

/-- The arc of the reflected diagram at a bottom point is the arc of the diagram at the
corresponding top point. -/
@[simp]
theorem flip_val_inl (i : Fin k) : D.flip.val (Sum.inl i) = (D.val (Sum.inr i)).swap :=
  flip_val_swap D (Sum.inr i)

/-- The arc of the reflected diagram at a top point is the arc of the diagram at the corresponding
bottom point. -/
@[simp]
theorem flip_val_inr (j : Fin k) : D.flip.val (Sum.inr j) = (D.val (Sum.inl j)).swap :=
  flip_val_swap D (Sum.inl j)

/-- **Reflection is an involution**: reflecting twice restores the diagram. -/
@[simp]
theorem flip_flip : D.flip.flip = D :=
  Subtype.ext (Equiv.ext fun x => by rw [flip_val, flip_val_swap, Sum.swap_swap])

/-- Reflection is injective, being an involution. -/
theorem flip_injective : Function.Injective (flip (k := k)) :=
  Function.LeftInverse.injective flip_flip

/-! ### Reflection exchanges caps and cups -/

/-- **Reflection carries a through strand to a through strand.** -/
@[simp]
theorem isThrough_flip (x : Fin k ⊕ Fin k) : D.flip.IsThrough x ↔ D.IsThrough x.swap := by
  rcases x with i | i
  · rcases h : D.val (Sum.inr i) with m | m <;> simp [isThrough_def, h]
  · rcases h : D.val (Sum.inl i) with m | m <;> simp [isThrough_def, h]

/-- **Reflection carries a cap to a cup.** -/
@[simp]
theorem isCap_flip (x : Fin k ⊕ Fin k) : D.flip.IsCap x ↔ D.IsCup x.swap := by
  rcases x with i | i
  · rcases h : D.val (Sum.inr i) with m | m <;> simp [isCap_def, isCup_def, h]
  · simp [isCap_def, isCup_def]

/-- **Reflection carries a cup to a cap.** -/
@[simp]
theorem isCup_flip (x : Fin k ⊕ Fin k) : D.flip.IsCup x ↔ D.IsCap x.swap := by
  rcases x with i | i
  · simp [isCap_def, isCup_def]
  · rcases h : D.val (Sum.inl i) with m | m <;> simp [isCap_def, isCup_def, h]

/-- The bottom endpoints of the through strands of the reflected diagram are the top endpoints of
the through strands of the diagram. -/
@[simp]
theorem bottomThrough_flip : D.flip.bottomThrough = D.topThrough := by
  ext i; rw [mem_bottomThrough, mem_topThrough, isThrough_flip]; rfl

/-- The top endpoints of the through strands of the reflected diagram are the bottom endpoints of
the through strands of the diagram. -/
@[simp]
theorem topThrough_flip : D.flip.topThrough = D.bottomThrough := by
  ext j; rw [mem_topThrough, mem_bottomThrough, isThrough_flip]; rfl

/-- The capped bottom points of the reflected diagram are the cupped top points of the
diagram. -/
@[simp]
theorem bottomCap_flip : D.flip.bottomCap = D.topCup := by
  ext i; rw [mem_bottomCap, mem_topCup, isCap_flip]; rfl

/-- The cupped top points of the reflected diagram are the capped bottom points of the
diagram. -/
@[simp]
theorem topCup_flip : D.flip.topCup = D.bottomCap := by
  ext j; rw [mem_topCup, mem_bottomCap, isCup_flip]; rfl

/-! ### Reflection on permutation and relabelled diagrams -/

/-- **Reflection inverts a permutation diagram**: read upside down, the strand `i ↦ σ i` is the
strand `σ i ↦ i`. -/
@[simp]
theorem flip_permToBrauer (σ : Equiv.Perm (Fin k)) :
    (permToBrauer σ).flip = permToBrauer σ⁻¹ := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  rcases x with i | j
  · simp [Equiv.Perm.inv_def]
  · simp [Equiv.Perm.inv_def]

/-- **Reflection exchanges the two renamings of a relabelling**: the renaming of the bottom
boundary becomes the renaming of the top boundary and conversely. -/
@[simp]
theorem flip_relabel (σ τ : Equiv.Perm (Fin k)) :
    (D.relabel σ τ).flip = D.flip.relabel τ σ := by
  have he : (Equiv.Perm.sumCongr σ τ).trans (Equiv.sumComm (Fin k) (Fin k))
      = (Equiv.sumComm (Fin k) (Fin k)).trans (Equiv.Perm.sumCongr τ σ) :=
    Equiv.ext fun x => by rcases x with i | j <;> rfl
  rw [flip, relabel_def, relabel_def, flip, PerfectMatching.congr_trans,
    PerfectMatching.congr_trans, he]

end BrauerDiagram

/-! ### Reflection reverses stacking -/

/-- **The first arc of a strand of the reflected stack.** Reflecting the stack of `D₁` above `D₂`
gives the stack of the reflection of `D₂` above the reflection of `D₁`, and the first arc of its
strand at the reflected outer point is the reflection of the first arc of the strand at that outer
point: `Sum.swap` carries the outer boundary and the middle states across together. -/
theorem stackStart_flip (D₁ D₂ : BrauerDiagram k) (x : Fin k ⊕ Fin k) :
    stackStart D₂.flip D₁.flip x.swap = Sum.map Sum.swap Sum.swap (stackStart D₁ D₂ x) := by
  rcases x with i | j
  · rcases h : D₂.val (Sum.inl i) with m | m <;> simp [h]
  · rcases h : D₁.val (Sum.inr j) with m | m <;> simp [h]

/-- **A later arc of a strand of the reflected stack**, the companion of
`TauCeti.stackStart_flip`.  Reflection exchanges the two diagrams a middle state can point at, so
it exchanges the two kinds of middle state and leaves the middle point untouched. -/
theorem stackStep_flip (D₁ D₂ : BrauerDiagram k) (s : Fin k ⊕ Fin k) :
    stackStep D₂.flip D₁.flip s.swap = Sum.map Sum.swap Sum.swap (stackStep D₁ D₂ s) := by
  rcases s with a | a
  · rcases h : D₁.val (Sum.inl a) with m | m <;> simp [h]
  · rcases h : D₂.val (Sum.inr a) with m | m <;> simp [h]

/-- A chain of middle states of the stack of `D₁` above `D₂` is a chain of middle states of the
reflected stack. -/
private theorem reflTransGen_stackStep_flip {D₁ D₂ : BrauerDiagram k} {s t : Fin k ⊕ Fin k}
    (h : Relation.ReflTransGen (fun u v => stackStep D₁ D₂ u = Sum.inr v) s t) :
    Relation.ReflTransGen (fun u v => stackStep D₂.flip D₁.flip u = Sum.inr v) s.swap t.swap := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (by rw [stackStep_flip, hstep]; rfl)

/-- **Reflection reverses stacking**: the stack of `D₁` above `D₂`, read upside down, is the stack
of the reflection of `D₂` above the reflection of `D₁`.  Together with
`TauCeti.middleLoopCount_flip` this says that reflection reverses the loop-weighted stacking of
diagrams, the multiplication the Brauer algebra carries on its diagram basis. -/
@[simp]
theorem flip_composeDiagram (D₁ D₂ : BrauerDiagram k) :
    (composeDiagram D₁ D₂).flip = composeDiagram D₂.flip D₁.flip := by
  refine Subtype.ext (Equiv.ext fun z => ?_)
  obtain ⟨x, rfl⟩ : ∃ x, z = x.swap := ⟨z.swap, (Sum.swap_swap z).symm⟩
  rw [BrauerDiagram.flip_val_swap]
  refine ((composeDiagram_val_eq_iff D₂.flip D₁.flip).mpr ?_).symm
  rcases (composeDiagram_val_eq_iff D₁ D₂).mp rfl with hstart | ⟨s, t, hstart, hpath, hexit⟩
  · exact Or.inl (by rw [stackStart_flip, hstart]; rfl)
  · exact Or.inr ⟨s.swap, t.swap, by rw [stackStart_flip, hstart]; rfl,
      reflTransGen_stackStep_flip hpath, by rw [stackStep_flip, hexit]; rfl⟩

/-! ### Reflection preserves the middle-loop count -/

/-- **The two stacks have the same middle graph**: reflection exchanges a cap of the upper diagram
with a cup of the lower one, and both join the same two middle points. -/
@[simp]
theorem middleAdj_flip (D₁ D₂ : BrauerDiagram k) (a b : Fin k) :
    MiddleAdj D₂.flip D₁.flip a b ↔ MiddleAdj D₁ D₂ a b := by
  rcases h₁ : D₂.val (Sum.inr a) with m | m <;> rcases h₂ : D₁.val (Sum.inl a) with n | n <;>
    simp [middleAdj_def, h₁, h₂, or_comm]

/-- **Reflection preserves reachability in the middle graph**: the two stacks have the same middle
graph, so the same middle points are joined by a chain of its arcs. -/
@[simp]
theorem reflTransGen_middleAdj_flip (D₁ D₂ : BrauerDiagram k) (a b : Fin k) :
    Relation.ReflTransGen (MiddleAdj D₂.flip D₁.flip) a b ↔
      Relation.ReflTransGen (MiddleAdj D₁ D₂) a b :=
  ⟨Relation.ReflTransGen.mono (fun _ _ h => (middleAdj_flip D₁ D₂ _ _).mp h) a b,
    Relation.ReflTransGen.mono (fun _ _ h => (middleAdj_flip D₁ D₂ _ _).mpr h) a b⟩

/-- **The two stacks have the same interior middle points**: keeping both arcs in the middle means
being capped above and cupped below, and reflection exchanges the two conditions. -/
@[simp]
theorem isMiddleVertex_flip (D₁ D₂ : BrauerDiagram k) (a : Fin k) :
    IsMiddleVertex D₂.flip D₁.flip a ↔ IsMiddleVertex D₁ D₂ a := by
  rw [isMiddleVertex_def, isMiddleVertex_def, BrauerDiagram.isCap_flip,
    BrauerDiagram.isCup_flip]
  exact and_comm

/-- **Reflection preserves the closed middle loops**: a middle point lies on a loop of the
reflected stack exactly when it lies on a loop of the stack. -/
@[simp]
theorem onMiddleLoop_flip (D₁ D₂ : BrauerDiagram k) (a : Fin k) :
    OnMiddleLoop D₂.flip D₁.flip a ↔ OnMiddleLoop D₁ D₂ a := by
  rw [onMiddleLoop_def, onMiddleLoop_def]
  exact forall_congr' fun b =>
    imp_congr (reflTransGen_middleAdj_flip D₁ D₂ a b) (isMiddleVertex_flip D₁ D₂ b)

/-- Reflection preserves the least point of a closed middle loop, the point the loops are counted
by. -/
@[simp]
theorem isMiddleLoopMin_flip (D₁ D₂ : BrauerDiagram k) (a : Fin k) :
    IsMiddleLoopMin D₂.flip D₁.flip a ↔ IsMiddleLoopMin D₁ D₂ a := by
  rw [isMiddleLoopMin_def, isMiddleLoopMin_def]
  exact and_congr (onMiddleLoop_flip D₁ D₂ a)
    (forall_congr' fun b => imp_congr_left (reflTransGen_middleAdj_flip D₁ D₂ a b))

/-- **Reflection preserves the middle-loop count**: turning a stack of two Brauer diagrams upside
down closes up the same loops in the middle.  With `TauCeti.flip_composeDiagram` this says that
reflection reverses the loop-weighted stacking
`D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂` of diagrams, the multiplication the
Brauer algebra carries on its diagram basis. -/
@[simp]
theorem middleLoopCount_flip (D₁ D₂ : BrauerDiagram k) :
    middleLoopCount D₂.flip D₁.flip = middleLoopCount D₁ D₂ := by
  rw [middleLoopCount_def, middleLoopCount_def]
  exact congrArg Set.ncard (Set.ext fun a => isMiddleLoopMin_flip D₁ D₂ a)

end TauCeti
