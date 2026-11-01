/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import TauCeti.GroupTheory.Presentation.Relator

/-!
# Compressed certificates for normal generation

A `NormalClosureProgram` builds elements from a distinguished element using products, inverses
and conjugation by words in an ambient generator family. Instructions refer only to earlier
registers, so common subexpressions can be shared without expanding products of conjugates.
All register values lie in every normal subgroup containing the distinguished element.

`NormalClosureProgram.check` compares selected registers with the ambient generators. If the
generators generate the group, an accepted check proves that the distinguished element normally
generates it. The check must be made in the group whose normal closure is claimed: checking in
a finite image does not prove normal generation in an abstract presented group.

Conjugating words are interpreted by `Relator.eval`.
Conjugation by `w` means `w⁻¹ * x * w`, as in `Relator.conj`; permutation multiplication retains
Mathlib's convention. Evaluation commutes with group homomorphisms.
-/

public section

namespace TauCeti

/-- One instruction for constructing an element of a normal closure, with `n` earlier registers.
Every reference is bounded, so forward and out-of-range references cannot be encoded. -/
inductive NormalClosureStep (α : Type*) (n : ℕ) where
  /-- Insert the distinguished element. -/
  | seed
  /-- Multiply two earlier values in the indicated order. -/
  | mul (i j : Fin n)
  /-- Invert an earlier value. -/
  | inv (i : Fin n)
  /-- Conjugate an earlier value by an ambient word, using `w⁻¹ * x * w`. -/
  | conj (w : Relator α) (i : Fin n)

namespace NormalClosureStep

variable {α G H : Type*} [Group G] [Group H] {n : ℕ}

/-- Interpret an instruction using an ambient generator assignment and earlier register values. -/
def eval (s : NormalClosureStep α n) (f : α → G) (x : G) (v : Fin n → G) : G :=
  match s with
  | .seed => x
  | .mul i j => v i * v j
  | .inv i => (v i)⁻¹
  | .conj w i => (w.eval f)⁻¹ * v i * w.eval f

/-- The seed instruction returns the distinguished element. -/
@[simp]
theorem eval_seed (f : α → G) (x : G) (v : Fin n → G) :
    (seed : NormalClosureStep α n).eval f x v = x := by rfl

/-- A multiplication instruction multiplies its two referenced values. -/
@[simp]
theorem eval_mul (i j : Fin n) (f : α → G) (x : G) (v : Fin n → G) :
    (mul i j : NormalClosureStep α n).eval f x v = v i * v j := by rfl

/-- An inverse instruction inverts its referenced value. -/
@[simp]
theorem eval_inv (i : Fin n) (f : α → G) (x : G) (v : Fin n → G) :
    (inv i : NormalClosureStep α n).eval f x v = (v i)⁻¹ := by rfl

/-- A conjugation instruction uses the inverse-on-the-left convention. -/
@[simp]
theorem eval_conj (w : Relator α) (i : Fin n) (f : α → G) (x : G) (v : Fin n → G) :
    (conj w i).eval f x v = (w.eval f)⁻¹ * v i * w.eval f := by rfl

/-- Instruction evaluation commutes with group homomorphisms. -/
@[simp]
theorem map_eval (s : NormalClosureStep α n) (φ : G →* H) (f : α → G) (x : G)
    (v : Fin n → G) :
    φ (s.eval f x v) = s.eval (φ ∘ f) (φ x) (φ ∘ v) := by
  cases s <;> simp

/-- A normal subgroup containing the seed and all earlier values contains the next value.
No membership condition is needed on the ambient conjugating words. -/
theorem eval_mem (s : NormalClosureStep α n) (f : α → G) (x : G) (v : Fin n → G)
    (N : Subgroup G) [N.Normal] (hx : x ∈ N) (hv : ∀ i, v i ∈ N) :
    s.eval f x v ∈ N := by
  cases s with
  | seed => exact hx
  | mul i j => exact N.mul_mem (hv i) (hv j)
  | inv i => exact N.inv_mem (hv i)
  | conj w i =>
    exact Subgroup.Normal.conj_mem' inferInstance (v i) (hv i) (w.eval f)

end NormalClosureStep

/-- A straight-line construction with `n` registers, each using only earlier registers.
The register number is its insertion position, starting at zero. -/
inductive NormalClosureProgram (α : Type*) : ℕ → Type _ where
  /-- The empty program has no registers. -/
  | nil : NormalClosureProgram α 0
  /-- Append an instruction whose references are to the existing registers. -/
  | snoc {n : ℕ} (p : NormalClosureProgram α n) (s : NormalClosureStep α n) :
      NormalClosureProgram α (n + 1)

namespace NormalClosureProgram

variable {α G H : Type*} [Group G] [Group H] {n : ℕ}

/-- Evaluate all registers of a program. Existing registers keep their indices when an
instruction is appended; its new value occupies the last index. -/
def eval : {n : ℕ} → NormalClosureProgram α n → (α → G) → G → Fin n → G
  | 0, .nil, _, _ => Fin.elim0
  | _ + 1, .snoc p s, f, x =>
    let v := p.eval f x
    Fin.snoc v (s.eval f x v)

/-- Evaluation of the empty program is the empty tuple. -/
@[simp]
theorem eval_nil (f : α → G) (x : G) : nil.eval f x = Fin.elim0 := by rfl

/-- Appending an instruction extends the tuple by its value on the earlier registers.
This equation also supports evaluation at literal register numbers. -/
theorem eval_snoc (p : NormalClosureProgram α n) (s : NormalClosureStep α n)
    (f : α → G) (x : G) :
    (p.snoc s).eval f x = Fin.snoc (p.eval f x) (s.eval f x (p.eval f x)) := by
  rfl

/-- Appending an instruction leaves earlier register values unchanged. -/
@[simp]
theorem eval_snoc_castSucc (p : NormalClosureProgram α n) (s : NormalClosureStep α n)
    (f : α → G) (x : G) (i : Fin n) :
    (p.snoc s).eval f x i.castSucc = p.eval f x i := by
  simp [eval]

/-- The last register evaluates the appended instruction on the earlier values. -/
@[simp]
theorem eval_snoc_last (p : NormalClosureProgram α n) (s : NormalClosureStep α n)
    (f : α → G) (x : G) :
    (p.snoc s).eval f x (Fin.last n) = s.eval f x (p.eval f x) := by
  simp [eval]

/-- Program evaluation commutes with group homomorphisms, register by register. -/
@[simp]
theorem map_eval (p : NormalClosureProgram α n) (φ : G →* H) (f : α → G) (x : G)
    (i : Fin n) :
    φ (p.eval f x i) = p.eval (φ ∘ f) (φ x) i := by
  induction p with
  | nil => exact Fin.elim0 i
  | snoc p s ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [eval_snoc_last, NormalClosureStep.map_eval]
      congr 1
      funext j
      exact ih j
    · simpa using ih j

/-- Every register lies in any normal subgroup containing the distinguished element. -/
theorem eval_mem (p : NormalClosureProgram α n) (f : α → G) (x : G)
    (N : Subgroup G) [N.Normal] (hx : x ∈ N) (i : Fin n) :
    p.eval f x i ∈ N := by
  induction p with
  | nil => exact Fin.elim0 i
  | snoc p s ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using s.eval_mem f x (p.eval f x) N hx ih
    · simpa using ih j

/-- Check that the selected output register for each generator recovers that generator.
Equality is checked in the actual target group, not in a separate model. -/
def check [Fintype α] [DecidableEq G] (p : NormalClosureProgram α n)
    (f : α → G) (x : G) (output : α → Fin n) : Bool :=
  decide (∀ a, p.eval f x (output a) = f a)

/-- An accepted check is exactly the collection of generator-recovery equations. -/
@[simp]
theorem check_eq_true [Fintype α] [DecidableEq G] (p : NormalClosureProgram α n)
    (f : α → G) (x : G) (output : α → Fin n) :
    p.check f x output = true ↔ ∀ a, p.eval f x (output a) = f a := by
  simp [check]

/-- Recovery equations put the subgroup generated by the assignment inside the normal closure
of the distinguished element, without finiteness or decidable equality assumptions. -/
theorem closure_le_normalClosure_of_eval_eq
    (p : NormalClosureProgram α n) (f : α → G) (x : G) (output : α → Fin n)
    (h : ∀ a, p.eval f x (output a) = f a) :
    Subgroup.closure (Set.range f) ≤ Subgroup.normalClosure {x} := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨a, rfl⟩
  rw [← h a]
  exact p.eval_mem f x _ (Subgroup.subset_normalClosure (Set.mem_singleton x)) _

/-- A program recovering a generating family proves normal generation of the group,
without finiteness or decidable equality assumptions. -/
theorem normalClosure_eq_top_of_eval_eq
    (p : NormalClosureProgram α n) (f : α → G) (x : G) (output : α → Fin n)
    (hgen : Subgroup.closure (Set.range f) = ⊤)
    (h : ∀ a, p.eval f x (output a) = f a) :
    Subgroup.normalClosure {x} = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact p.closure_le_normalClosure_of_eval_eq f x output h

/-- Checked recovery puts the subgroup generated by the assignment inside the normal closure
of the distinguished element. This form does not require that the assignment generate `G`. -/
theorem closure_le_normalClosure_of_check [Fintype α] [DecidableEq G]
    (p : NormalClosureProgram α n) (f : α → G) (x : G) (output : α → Fin n)
    (h : p.check f x output = true) :
    Subgroup.closure (Set.range f) ≤ Subgroup.normalClosure {x} :=
  p.closure_le_normalClosure_of_eval_eq f x output ((p.check_eq_true f x output).mp h)

/-- A checked program recovering a generating family proves normal generation of the group. -/
theorem normalClosure_eq_top_of_check [Fintype α] [DecidableEq G]
    (p : NormalClosureProgram α n) (f : α → G) (x : G) (output : α → Fin n)
    (hgen : Subgroup.closure (Set.range f) = ⊤) (h : p.check f x output = true) :
    Subgroup.normalClosure {x} = ⊤ :=
  p.normalClosure_eq_top_of_eval_eq f x output hgen ((p.check_eq_true f x output).mp h)

end NormalClosureProgram

end TauCeti
