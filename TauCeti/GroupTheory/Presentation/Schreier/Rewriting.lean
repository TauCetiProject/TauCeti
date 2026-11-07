/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Relator
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Signed Schreier word rewriting

`TauCeti.Schreier.trace` reads a signed word from left to right in a family of permutations.
`TauCeti.Schreier.rewrite` records the traversed positive edges, using the inverse of the edge
ending at the current state for a negative letter. Thus it works for arbitrary generators,
not only involutions, and for arbitrary state sets.

Given representatives `r q` and generator images `f a`, an edge denotes
`r q * f a * (r (σ a q))⁻¹`. The telescoping identity `lift_rewrite` reconstructs the original
word with its initial and final representatives. Concatenation and inversion agree with this
rewriting at the level of signed lists, before passing to free groups.

`TauCeti.Schreier.pathPerm` acts on a state and an accumulated edge value; `lift_pathPerm`
identifies its word action with the trace and evaluated rewrite. This gives a permutation
realization of the rewriting calculus for proving completeness of subgroup presentations.

For a group action, use the permutations given by the inverses of the generators. If
`(r q)⁻¹ • b = q`, these edges lie in the stabilizer of `b`. The theorem
`coe_lift_stabilizerGenerator_rewrite` then gives an explicit word in stabilizer generators
for every input word fixing `b`, provided `r b = 1`. This supplies the word dictionary needed
for subgroup rewriting; it does not assert that the edge generators form a free basis or
that any proposed subgroup presentation is complete.

## References

* D. L. Johnson, *Presentations of Groups*, second edition, Chapter 9
  (Reidemeister--Schreier rewriting).
* Mathlib's `Subgroup.closure_mul_image_eq` proves the set-generation version of Schreier's
  lemma; here the output is an explicit signed word with its reconstruction identity.
-/

public section

namespace TauCeti.Schreier

variable {α Q G : Type*} [Group G]

/-- The final state of a left-to-right scan. A negative letter uses the inverse permutation. -/
def trace (σ : α → Equiv.Perm Q) : Q → PresentationWord α → Q
  | q, [] => q
  | q, (a, true) :: w => trace σ (σ a q) w
  | q, (a, false) :: w => trace σ ((σ a).symm q) w

@[simp]
theorem trace_nil (σ : α → Equiv.Perm Q) (q : Q) : trace σ q [] = q := (rfl)

@[simp]
theorem trace_cons_true (σ : α → Equiv.Perm Q) (q : Q) (a : α)
    (w : PresentationWord α) : trace σ q ((a, true) :: w) = trace σ (σ a q) w := (rfl)

@[simp]
theorem trace_cons_false (σ : α → Equiv.Perm Q) (q : Q) (a : α)
    (w : PresentationWord α) : trace σ q ((a, false) :: w) = trace σ ((σ a).symm q) w := (rfl)

/-- The scan depends only on the free-group element of the word. The inverses compensate
for the left-to-right scan and Mathlib's right-to-left permutation multiplication. -/
theorem trace_eq_lift (σ : α → Equiv.Perm Q) (q : Q) (w : PresentationWord α) :
    trace σ q w = (FreeGroup.lift (fun a => (σ a)⁻¹) (FreeGroup.mk w))⁻¹ q := by
  induction w generalizing q with
  | nil => simp [FreeGroup.lift_mk]
  | cons l w ih =>
    rcases l with ⟨a, s⟩
    cases s <;> simp [ih, FreeGroup.lift_mk, Equiv.Perm.mul_apply]

/-- Rewrite a path using positive edges as generators. The inverse of an edge is indexed by
its positive starting state, not by the state from which the negative step starts. -/
def rewrite (σ : α → Equiv.Perm Q) : Q → PresentationWord α → PresentationWord (Q × α)
  | _, [] => []
  | q, (a, true) :: w => ((q, a), true) :: rewrite σ (σ a q) w
  | q, (a, false) :: w => (((σ a).symm q, a), false) :: rewrite σ ((σ a).symm q) w

@[simp]
theorem rewrite_nil (σ : α → Equiv.Perm Q) (q : Q) : rewrite σ q [] = [] := (rfl)

@[simp]
theorem rewrite_cons_true (σ : α → Equiv.Perm Q) (q : Q) (a : α)
    (w : PresentationWord α) :
    rewrite σ q ((a, true) :: w) = ((q, a), true) :: rewrite σ (σ a q) w := (rfl)

@[simp]
theorem rewrite_cons_false (σ : α → Equiv.Perm Q) (q : Q) (a : α)
    (w : PresentationWord α) :
    rewrite σ q ((a, false) :: w) =
      (((σ a).symm q, a), false) :: rewrite σ ((σ a).symm q) w := (rfl)

/-- Scanning a concatenation continues from the endpoint of the first word. -/
@[simp]
theorem trace_append (σ : α → Equiv.Perm Q) (q : Q) (u v : PresentationWord α) :
    trace σ q (u ++ v) = trace σ (trace σ q u) v := by
  induction u generalizing q with
  | nil => simp
  | cons l u ih => rcases l with ⟨a, s⟩; cases s <;> simp [ih]

/-- Rewriting a concatenation continues from the endpoint of the first word. -/
@[simp]
theorem rewrite_append (σ : α → Equiv.Perm Q) (q : Q) (u v : PresentationWord α) :
    rewrite σ q (u ++ v) = rewrite σ q u ++ rewrite σ (trace σ q u) v := by
  induction u generalizing q with
  | nil => simp
  | cons l u ih => rcases l with ⟨a, s⟩; cases s <;> simp [ih]

/-- Rewriting emits exactly one signed edge for each input letter, including trivial edges. -/
@[simp]
theorem length_rewrite (σ : α → Equiv.Perm Q) (q : Q) (w : PresentationWord α) :
    (rewrite σ q w).length = w.length := by
  induction w generalizing q with
  | nil => simp
  | cons l w ih => rcases l with ⟨a, s⟩; cases s <;> simp [ih]

/-- Reading the inverse word from the endpoint returns to the initial state. -/
@[simp]
theorem trace_invRev (σ : α → Equiv.Perm Q) (q : Q) (w : PresentationWord α) :
    trace σ (trace σ q w) (FreeGroup.invRev w) = q := by
  simp [trace_eq_lift, ← FreeGroup.inv_mk]

/-- Reversing a path and all its signs reverses and inverts the rewritten word literally. -/
@[simp]
theorem rewrite_invRev (σ : α → Equiv.Perm Q) (q : Q) (w : PresentationWord α) :
    rewrite σ (trace σ q w) (FreeGroup.invRev w) = FreeGroup.invRev (rewrite σ q w) := by
  induction w generalizing q with
  | nil => simp [FreeGroup.invRev]
  | cons l w ih =>
    rcases l with ⟨a, s⟩
    have hinv : FreeGroup.invRev [(a, s)] = [(a, !s)] := by simp [FreeGroup.invRev]
    rw [FreeGroup.invRev_cons, hinv, rewrite_append]
    cases s <;> simp only [trace_cons_false, trace_cons_true, ih, trace_invRev,
      rewrite_cons_false, rewrite_cons_true] <;>
      simp [FreeGroup.invRev]

/-- The element attached to a positive edge by a choice of representatives. -/
def generator (σ : α → Equiv.Perm Q) (f : α → G) (r : Q → G) (e : Q × α) : G :=
  r e.1 * f e.2 * (r (σ e.2 e.1))⁻¹

@[simp]
theorem generator_apply (σ : α → Equiv.Perm Q) (f : α → G) (r : Q → G) (q : Q) (a : α) :
    generator σ f r (q, a) = r q * f a * (r (σ a q))⁻¹ := (rfl)

/-- The telescoping identity for Schreier rewriting. It holds without any transversal or
subgroup hypothesis: the final representative records exactly the unclosed part of the path. -/
theorem lift_rewrite (σ : α → Equiv.Perm Q) (f : α → G) (r : Q → G)
    (q : Q) (w : PresentationWord α) :
    FreeGroup.lift (generator σ f r) (FreeGroup.mk (rewrite σ q w)) =
      r q * FreeGroup.lift f (FreeGroup.mk w) * (r (trace σ q w))⁻¹ := by
  induction w generalizing q with
  | nil => simp [FreeGroup.lift_mk]
  | cons l w ih =>
    rcases l with ⟨a, s⟩
    cases s <;>
      simp only [rewrite_cons_false, rewrite_cons_true, trace_cons_false, trace_cons_true,
        FreeGroup.lift_mk, List.map_cons, List.prod_cons, Bool.cond_false, Bool.cond_true]
    · rw [← FreeGroup.lift_mk, ih]
      simp [generator, mul_assoc]
    · rw [← FreeGroup.lift_mk, ih]
      simp [generator, mul_assoc]

/-- A labelled edge acts on a state and an accumulated group element. The inverse-generator
convention makes the inverse of a lifted word follow the left-to-right Schreier scan. -/
def pathPerm (σ : α → Equiv.Perm Q) (f : Q × α → G) (a : α) : Equiv.Perm (Q × G) :=
  Equiv.prodShear (σ a) (fun q => Equiv.mulRight (f (q, a)))

@[simp]
theorem pathPerm_apply (σ : α → Equiv.Perm Q) (f : Q × α → G) (a : α) (q : Q) (h : G) :
    pathPerm σ f a (q, h) = (σ a q, h * f (q, a)) := (rfl)

@[simp]
theorem pathPerm_symm_apply (σ : α → Equiv.Perm Q) (f : Q × α → G)
    (a : α) (q : Q) (h : G) :
    (pathPerm σ f a).symm (q, h) = ((σ a).symm q, h * (f ((σ a).symm q, a))⁻¹) := (rfl)

/-- The permutation lift records both the endpoint and the evaluated rewritten word.
In particular, relations among rewritten edges certify relations in this permutation action. -/
theorem lift_pathPerm (σ : α → Equiv.Perm Q) (f : Q × α → G)
    (q : Q) (h : G) (w : PresentationWord α) :
    (FreeGroup.lift (fun a => (pathPerm σ f a)⁻¹) (FreeGroup.mk w))⁻¹ (q, h) =
      (trace σ q w, h * FreeGroup.lift f (FreeGroup.mk (rewrite σ q w))) := by
  induction w generalizing q h with
  | nil => simp [FreeGroup.lift_mk]
  | cons l w ih =>
    rcases l with ⟨a, s⟩
    simp [FreeGroup.lift_mk] at ih
    cases s <;> simp [FreeGroup.lift_mk, Equiv.Perm.mul_apply, ih, mul_assoc]

section Action

variable [MulAction G Q]

/-- The inverse-generator permutations for a left action. Their left-to-right scan follows
right multiplication of coset representatives. -/
def actionPerm (f : α → G) (a : α) : Equiv.Perm Q := MulAction.toPerm (f a)⁻¹

@[simp]
theorem actionPerm_apply (f : α → G) (a : α) (q : Q) :
    actionPerm (Q := Q) f a q = (f a)⁻¹ • q := (rfl)

@[simp]
theorem actionPerm_symm_apply (f : α → G) (a : α) (q : Q) :
    (actionPerm (Q := Q) f a).symm q = f a • q := by
  simp [actionPerm]

/-- The endpoint is the action of the inverse of the evaluated word, in agreement with
Mathlib's convention that the rightmost factor acts first. -/
theorem trace_actionPerm (f : α → G) (q : Q) (w : PresentationWord α) :
    trace (actionPerm f) q w = (FreeGroup.lift f (FreeGroup.mk w))⁻¹ • q := by
  rw [trace_eq_lift, ← FreeGroup.lift_unique
    (f := fun a => (actionPerm f a)⁻¹)
    ((MulAction.toPermHom G Q).comp (FreeGroup.lift f))
    (by
      intro a
      simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, actionPerm,
        ← MulAction.coe_toPermHom, map_inv, inv_inv])]
  simp

/-- Rewriting a relation from any state yields a relation among the edge generators.
In particular every transversal-conjugated defining relator evaluates to one. -/
theorem lift_rewrite_eq_one (f : α → G) (r : Q → G) (q : Q)
    (w : PresentationWord α) (hw : FreeGroup.lift f (FreeGroup.mk w) = 1) :
    FreeGroup.lift (generator (actionPerm f) f r)
      (FreeGroup.mk (rewrite (actionPerm f) q w)) = 1 := by
  rw [lift_rewrite, trace_actionPerm, hw]
  simp

/-- Schreier edge generators fix the base point when the representatives send it to the
corresponding states under the inverse action. -/
theorem generator_actionPerm_mem_stabilizer (f : α → G) (b : Q) (r : Q → G)
    (hr : ∀ q, (r q)⁻¹ • b = q) (e : Q × α) :
    generator (actionPerm f) f r e ∈ MulAction.stabilizer G b := by
  rw [MulAction.mem_stabilizer_iff]
  simp only [generator, actionPerm_apply, mul_smul, hr]
  rw [smul_inv_smul]
  exact (inv_smul_eq_iff.mp (hr e.1)).symm

/-- Schreier edge generators, as elements of the actual stabilizer of the base point.
Representatives satisfy `(r q)⁻¹ • b = q`; no faithfulness or finiteness is required. -/
def stabilizerGenerator (f : α → G) (b : Q) (r : Q → G)
    (hr : ∀ q, (r q)⁻¹ • b = q) (e : Q × α) : MulAction.stabilizer G b :=
  ⟨generator (actionPerm f) f r e, generator_actionPerm_mem_stabilizer f b r hr e⟩

@[simp]
theorem coe_stabilizerGenerator (f : α → G) (b : Q) (r : Q → G)
    (hr : ∀ q, (r q)⁻¹ • b = q) (e : Q × α) :
    (stabilizerGenerator f b r hr e : G) = generator (actionPerm f) f r e := (rfl)

/-- A word fixing the base point rewrites to a word in its stabilizer generators denoting
exactly the same element. This is an explicit word dictionary, not only a generation assertion. -/
theorem coe_lift_stabilizerGenerator_rewrite (f : α → G) (b : Q) (r : Q → G)
    (hr : ∀ q, (r q)⁻¹ • b = q) (hb : r b = 1) (w : PresentationWord α)
    (hw : FreeGroup.lift f (FreeGroup.mk w) ∈ MulAction.stabilizer G b) :
    (FreeGroup.lift (stabilizerGenerator f b r hr)
      (FreeGroup.mk (rewrite (actionPerm f) b w)) : G) =
      FreeGroup.lift f (FreeGroup.mk w) := by
  have hend : trace (actionPerm f) b w = b := by
    rw [trace_actionPerm]
    exact MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer G b).inv_mem hw)
  calc
    _ = FreeGroup.lift (generator (actionPerm f) f r)
        (FreeGroup.mk (rewrite (actionPerm f) b w)) :=
      FreeGroup.lift_unique ((MulAction.stabilizer G b).subtype.comp
        (FreeGroup.lift (stabilizerGenerator f b r hr))) (by intro e; simp)
    _ = _ := by rw [lift_rewrite, hend, hb]; simp

end Action

end TauCeti.Schreier
