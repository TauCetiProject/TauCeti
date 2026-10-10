/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.Encoding.Bits
public import TauCeti.Computability.TuringMachine.OutputLength
public import Mathlib.Tactic.Linarith

/-!
# Polynomial-time machines on self-delimiting bit strings

Explicit fixed finite-control programs implement constants, pair projection, option
elimination, list length, and equality. The proofs give exact step counts for every scan,
transfer and halt, and then package these counts in `TM2ComputableInPolyTime`.
-/

@[expose] public section

namespace Turing
namespace BitMachines

open Computability

/-- Exactly `n` iterations of the optional transition function take `a` to `b`. -/
def StepsTo {σ : Type} (f : σ → Option σ) (a b : σ) (n : ℕ) : Prop :=
  (flip bind f)^[n] (some a) = some b

theorem StepsTo.refl {σ : Type} (f : σ → Option σ) (a : σ) : StepsTo f a a 0 := rfl

theorem StepsTo.head {σ : Type} {f : σ → Option σ} {a b c : σ} {n : ℕ} (h : f a = some b)
    (h' : StepsTo f b c n) : StepsTo f a c (n + 1) := by
  unfold StepsTo at *
  rw [Function.iterate_succ_apply]
  simpa [flip, h] using h'

theorem StepsTo.single {σ : Type} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    StepsTo f a b 1 :=
  StepsTo.head h (StepsTo.refl f b)

theorem StepsTo.trans {σ : Type} {f : σ → Option σ} {a b c : σ} {n m : ℕ} (h₁ : StepsTo f a b n)
    (h₂ : StepsTo f b c m) : StepsTo f a c (n + m) := by
  unfold StepsTo at *
  rw [add_comm, Function.iterate_add_apply, h₁, h₂]

theorem StepsTo.of_eq {σ : Type} {f : σ → Option σ} {a b : σ} {n n' : ℕ} (h : StepsTo f a b n)
    (hn : n = n') : StepsTo f a b n' := hn ▸ h

theorem StepsTo.congr {σ : Type} {f : σ → Option σ} {a b b' : σ} {n n' : ℕ} (h : StepsTo f a b n)
    (hb : b = b') (hn : n = n') : StepsTo f a b' n' := hb ▸ hn ▸ h

theorem StepsTo.succ_inv {σ : Type} {f : σ → Option σ} {a b : σ} {n : ℕ}
    (h : StepsTo f a b (n + 1)) : ∃ c, f a = some c ∧ StepsTo f c b n := by
  have hn : ∀ n, (flip bind f)^[n] none = none := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply]; exact ih
  unfold StepsTo at h
  rw [Function.iterate_succ_apply] at h
  cases hc : f a with
  | none => rw [show (flip bind f) (some a) = f a from rfl, hc, hn] at h; cases h
  | some c => rw [show (flip bind f) (some a) = f a from rfl, hc] at h; exact ⟨c, rfl, h⟩

theorem StepsTo.loop {σ τ α : Type} {f : σ → Option σ} (C : List α → List α → τ → σ)
    (D : List α → σ) (hc : ∀ p a l v, ∃ v', f (C p (a :: l) v) = some (C (p ++ [a]) l v'))
    (hn : ∀ p v, f (C p [] v) = some (D p)) (l : List α) :
    ∀ p v, StepsTo f (C p l v) (D (p ++ l)) (l.length + 1) := by
  induction l with
  | nil => intro p v; simpa using StepsTo.single (hn p v)
  | cons a l ih =>
    intro p v
    obtain ⟨v', h⟩ := hc p a l v
    simpa using StepsTo.head h (ih (p ++ [a]) v')

/-- A TM2 statement with bit stacks and a register holding an optional bit. -/
abbrev Stmt (K Λ : Type) : Type := TM2.Stmt (fun _ : K => Bool) Λ (Option Bool)

/-- A configuration of a bit-stack TM2 machine. -/
abbrev Cfg (K Λ : Type) : Type := TM2.Cfg (fun _ : K => Bool) Λ (Option Bool)

theorem initList_eq (M : FinTM2) (l : List (M.Γ M.k₀)) :
    initList M l = ⟨some M.main, M.initialState, Function.update (fun _ ↦ []) M.k₀ l⟩ :=
  congrArg (TM2.Cfg.mk (some M.main) M.initialState) (initList_stk M l)

theorem haltList_eq (M : FinTM2) (l : List (M.Γ M.k₁)) :
    haltList M l = ⟨none, M.initialState, Function.update (fun _ ↦ []) M.k₁ l⟩ :=
  congrArg (TM2.Cfg.mk none M.initialState) (haltList_stk M l)

theorem computableInPolyTime_mk {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (M : FinTM2) (e₀ : M.Γ M.k₀ ≃ Bool) (e₁ : M.Γ M.k₁ ≃ Bool) (p : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ p.eval (ea a).length, StepsTo (TM2.step M.m)
      (initList M ((ea a).map e₀.symm)) (haltList M ((eb (f a)).map e₁.symm)) n) :
    Nonempty (TM2ComputableInPolyTime ea eb f) :=
  ⟨{ tm := M, inputAlphabet := e₀, outputAlphabet := e₁, time := p,
     outputsFun := fun a => ⟨⟨_, (Classical.choose_spec (h a)).2⟩,
       (Classical.choose_spec (h a)).1⟩ }⟩

/-! ### Statements built from reading and writing single bits -/

section Stmts

variable {K Λ : Type}

/-- Jump to a label independently of the register value. -/
abbrev goto' (L : Λ) : Stmt K Λ := TM2.Stmt.goto fun _ => L

/-- Branch on a register containing one, zero, or no bit. -/
def branch3 (q₁ q₀ qₙ : Stmt K Λ) : Stmt K Λ :=
  TM2.Stmt.branch (fun v => v == some true) q₁ (TM2.Stmt.branch (fun v => v == some false) q₀ qₙ)

/-- Pop one bit from stack `k`, then branch on that bit or the empty stack. -/
def read (k : K) (q₁ q₀ qₙ : Stmt K Λ) : Stmt K Λ :=
  TM2.Stmt.pop k (fun _ o => o) (branch3 q₁ q₀ qₙ)

/-- Push a fixed bit onto stack `k` before executing `q`. -/
abbrev put (k : K) (b : Bool) (q : Stmt K Λ) : Stmt K Λ := TM2.Stmt.push k (fun _ => b) q

/-- Clear the optional-bit register and halt. -/
abbrev stop : Stmt K Λ := TM2.Stmt.load (fun _ => none) TM2.Stmt.halt

/-- Prepend a fixed bit string to stack `k` before executing the continuation. -/
def putList (k : K) : List Bool → Stmt K Λ → Stmt K Λ
  | [], q => q
  | b :: l, q => putList k l (put k b q)

variable [DecidableEq K]

theorem step_some (m : Λ → Stmt K Λ) (L : Λ) (v : Option Bool) (S : K → List Bool) :
    TM2.step m ⟨some L, v, S⟩ = some (TM2.stepAux (m L) v S) := rfl

theorem stepAux_read (k : K) (q₁ q₀ qₙ : Stmt K Λ) (v : Option Bool) (S : K → List Bool) :
    TM2.stepAux (read k q₁ q₀ qₙ) v S =
      match S k with
      | [] => TM2.stepAux qₙ none S
      | true :: t => TM2.stepAux q₁ (some true) (Function.update S k t)
      | false :: t => TM2.stepAux q₀ (some false) (Function.update S k t) := by
  rcases h : S k with _ | ⟨_ | _, t⟩
  · simp only [read, branch3, TM2.stepAux.eq_3, h, List.head?_nil, List.tail_nil,
      TM2.stepAux.eq_5, Option.none_beq_some, cond_eq_ite, Bool.false_eq_true, ↓reduceIte]
    exact congrArg _ (Function.update_eq_self_iff.2 h.symm)
  · simp only [read, branch3, TM2.stepAux.eq_3, h, List.head?_cons, List.tail_cons,
      TM2.stepAux.eq_5, Option.some_beq_some, beq_true, BEq.rfl, cond_eq_ite,
      ↓reduceIte, Bool.false_eq_true]
  · simp only [read, branch3, TM2.stepAux.eq_3, h, List.head?_cons, List.tail_cons,
      TM2.stepAux.eq_5, BEq.rfl, Option.some_beq_some, beq_false, Bool.not_true,
      cond_eq_ite, Bool.false_eq_true, ↓reduceIte]


@[simp] theorem stepAux_putList (k : K) (l : List Bool) (q : Stmt K Λ) (v : Option Bool)
    (S : K → List Bool) :
    TM2.stepAux (putList k l q) v S = TM2.stepAux q v (Function.update S k (l ++ S k)) := by
  induction l generalizing q S with
  | nil => simp [putList]
  | cons b l ih => simp [putList, ih]

end Stmts

/-! ### Loops -/

section Loops

variable {K Λ : Type} [DecidableEq K] (m : Λ → Stmt K Λ)

theorem erase_run {L L' : Λ} {k : K} (hL : m L = read k (goto' L) (goto' L) (goto' L')) :
    ∀ (S : K → List Bool) (v : Option Bool),
    StepsTo (TM2.step m) ⟨some L, v, S⟩ ⟨some L', none, Function.update S k []⟩
      ((S k).length + 1) := fun S v => by
  simpa using StepsTo.loop (f := TM2.step m) (fun _ l v => ⟨some L, v, Function.update S k l⟩)
    (fun _ => ⟨some L', none, Function.update S k []⟩)
    (fun _ b l v => ⟨some b, by cases b <;> simp [hL, stepAux_read]⟩)
    (fun _ v => by simp [hL, stepAux_read]) (S k) [] v

theorem stop_run {L : Λ} (hL : m L = stop) (S : K → List Bool) (v : Option Bool) :
    StepsTo (TM2.step m) ⟨some L, v, S⟩ ⟨none, none, S⟩ 1 :=
  StepsTo.single (by rw [step_some, hL]; rfl)

/-- Prove equality of stack maps by splitting the keys of their functional updates. -/
macro "updExt" : tactic =>
  `(tactic| (funext j; simp only [Function.update_apply]; split_ifs <;> simp_all))

/-- One transfer-loop step, replacing a source bit by `u` on the destination stack. -/
def moveAll (u : Bool → List Bool) (k₁ k₂ : K) (L L' : Λ) : Stmt K Λ :=
  read k₁ (putList k₂ (u true) (goto' L)) (putList k₂ (u false) (goto' L)) (goto' L')

theorem moveAll_run (u : Bool → List Bool) {L L' : Λ} {k₁ k₂ : K} (hk : k₁ ≠ k₂)
    (hL : m L = moveAll u k₁ k₂ L L') :
    ∀ (S : K → List Bool) (v : Option Bool),
    StepsTo (TM2.step m) ⟨some L, v, S⟩
      ⟨some L', none, Function.update (Function.update S k₁ []) k₂
        ((S k₁).reverse.flatMap u ++ S k₂)⟩ ((S k₁).length + 1) := fun S v => by
  simpa using StepsTo.loop (f := TM2.step m)
    (fun p l v => ⟨some L, v, Function.update (Function.update S k₁ l) k₂
      (p.reverse.flatMap u ++ S k₂)⟩)
    (fun p => ⟨some L', none, Function.update (Function.update S k₁ []) k₂
      (p.reverse.flatMap u ++ S k₂)⟩)
    (fun _ b _ _ => ⟨some b, by
      cases b <;> simp only [TM2.step.eq_2, hL, moveAll, stepAux_read,
        Function.update_of_ne hk, Function.update_self, stepAux_putList,
        TM2.stepAux.eq_6, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.flatMap_cons, List.append_assoc,
        Option.some.injEq, TM2.Cfg.mk.injEq, true_and] <;> updExt⟩)
    (fun _ _ => by simp [hL, moveAll, stepAux_read, Function.update_of_ne hk]) (S k₁) [] v

theorem move_run {L L' : Λ} {k₁ k₂ : K} (hk : k₁ ≠ k₂)
    (hL : m L = moveAll (fun b => [b]) k₁ k₂ L L') (S : K → List Bool) (v : Option Bool) :
    StepsTo (TM2.step m) ⟨some L, v, S⟩ ⟨some L', none,
      Function.update (Function.update S k₁ []) k₂ ((S k₁).reverse ++ S k₂)⟩ ((S k₁).length + 1) :=
  by simpa using moveAll_run m _ hk hL S v

theorem moveMap_run (g : Bool → Bool) {L L' : Λ} {k₁ k₂ k₃ : K} (h₁₂ : k₁ ≠ k₂) (h₁₃ : k₁ ≠ k₃)
    (h₂₃ : k₂ ≠ k₃) (hL : m L = read k₁ (put k₂ true (put k₃ (g true) (goto' L)))
      (put k₂ false (put k₃ (g false) (goto' L))) (goto' L')) :
    ∀ (S : K → List Bool) (v : Option Bool),
    StepsTo (TM2.step m) ⟨some L, v, S⟩
      ⟨some L', none, Function.update (Function.update (Function.update S k₁ []) k₂
        ((S k₁).reverse ++ S k₂)) k₃ (((S k₁).map g).reverse ++ S k₃)⟩ ((S k₁).length + 1) :=
  fun S v => by
  simpa using StepsTo.loop (f := TM2.step m)
    (fun p l v => ⟨some L, v, Function.update (Function.update (Function.update S k₁ l) k₂
      (p.reverse ++ S k₂)) k₃ ((p.map g).reverse ++ S k₃)⟩)
    (fun p => ⟨some L', none, Function.update (Function.update (Function.update S k₁ []) k₂
      (p.reverse ++ S k₂)) k₃ ((p.map g).reverse ++ S k₃)⟩)
    (fun _ b _ _ => ⟨some b, by
      cases b <;> simp only [TM2.step.eq_2, hL, stepAux_read,
        Function.update_of_ne h₁₃, Function.update_of_ne h₁₂, Function.update_self,
        TM2.stepAux.eq_1, TM2.stepAux.eq_6, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.cons_append, List.map_append,
        List.map_cons, List.map_nil, Option.some.injEq, TM2.Cfg.mk.injEq, true_and] <;>
        updExt⟩)
    (fun _ _ => by simp [hL, stepAux_read, Function.update_of_ne h₁₂, Function.update_of_ne h₁₃])
    (S k₁) [] v

theorem ones_run {L L' : Λ} {k₁ k₂ : K} (hk : k₁ ≠ k₂)
    (hL : m L = read k₁ (put k₂ true (goto' L)) (goto' L') (goto' L')) (n : ℕ) :
    ∀ (S : K → List Bool) (t : List Bool) (v : Option Bool),
    S k₁ = List.replicate n true ++ false :: t →
    StepsTo (TM2.step m) ⟨some L, v, S⟩
      ⟨some L', some false,
        Function.update (Function.update S k₁ t) k₂ (List.replicate n true ++ S k₂)⟩ (n + 1) :=
  fun S t v hl => by
  simpa [← hl] using StepsTo.loop (f := TM2.step m)
    (fun p l v => ⟨some L, v, Function.update (Function.update S k₁
      (List.replicate l.length true ++ false :: t)) k₂ (List.replicate p.length true ++ S k₂)⟩)
    (fun p => ⟨some L', some false, Function.update (Function.update S k₁ t) k₂
      (List.replicate p.length true ++ S k₂)⟩)
    (fun _ _ _ _ => ⟨some true, by
      simp only [List.length_cons, List.replicate_succ, List.cons_append, TM2.step.eq_2,
        hL, stepAux_read, Function.update_of_ne hk, Function.update_self,
        TM2.stepAux.eq_1, TM2.stepAux.eq_6, List.length_append, List.length_nil,
        zero_add, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      updExt⟩)
    (fun _ _ => by
      simp only [List.length_nil, List.replicate_zero, List.nil_append, TM2.step.eq_2,
        hL, stepAux_read, Function.update_of_ne hk, Function.update_self,
        TM2.stepAux.eq_6, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
      updExt)
    (List.replicate n ()) [] v

/-- One clocked transfer step; the length of stack `c` limits the number of source bits. -/
def countMove (u : Bool → List Bool) (c k₁ k₂ : K) (L L' : Λ) : Stmt K Λ :=
  read c (moveAll u k₁ k₂ L L) (moveAll u k₁ k₂ L L) (goto' L')

theorem countMove_run (u : Bool → List Bool) {L L' : Λ} {c k₁ k₂ : K} (h₁ : c ≠ k₁)
    (h₂ : c ≠ k₂) (hk : k₁ ≠ k₂) (hL : m L = countMove u c k₁ k₂ L L') (x : List Bool) :
    ∀ (S : K → List Bool) (t : List Bool) (v : Option Bool),
    (S c).length = x.length → S k₁ = x ++ t →
    StepsTo (TM2.step m) ⟨some L, v, S⟩
      ⟨some L', none, Function.update (Function.update (Function.update S c []) k₁ t) k₂
        (x.reverse.flatMap u ++ S k₂)⟩ (x.length + 1) := fun S t v hc hl => by
  simpa [List.map_fst_zip hc.le, List.map_snd_zip hc.ge, ← hl, hc] using
    StepsTo.loop (f := TM2.step m)
    (fun p l v => ⟨some L, v, Function.update (Function.update (Function.update S c
      (l.map Prod.fst)) k₁ (l.map Prod.snd ++ t)) k₂ ((p.map Prod.snd).reverse.flatMap u ++ S k₂)⟩)
    (fun p => ⟨some L', none, Function.update (Function.update (Function.update S c []) k₁ t) k₂
      ((p.map Prod.snd).reverse.flatMap u ++ S k₂)⟩)
    (fun _ a _ _ => ⟨some a.2, by
      obtain ⟨d, b⟩ := a
      cases d <;> cases b <;> simp only [List.map_cons, List.cons_append, TM2.step.eq_2,
        hL, countMove, moveAll, stepAux_read, Function.update_of_ne h₂,
        Function.update_of_ne h₁, Function.update_self, Function.update_of_ne h₁.symm,
        Function.update_of_ne hk, stepAux_putList, Function.update_of_ne hk.symm,
        Function.update_of_ne h₂.symm, TM2.stepAux.eq_6, List.map_append, List.map_nil,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.flatMap_cons, List.append_assoc, Option.some.injEq, TM2.Cfg.mk.injEq,
        true_and] <;> updExt⟩)
    (fun _ _ => by simp [hL, countMove, stepAux_read, Function.update_of_ne h₁,
      Function.update_of_ne h₂]) ((S c).zip x) [] v

end Loops

/-! ### Five stacks -/

/-- The input/output stack and four scratch stacks used by the bit programs. -/
inductive Stk
  | main | s₁ | s₂ | s₃ | s₄
  deriving DecidableEq

instance : Fintype Stk := Fintype.ofList [.main, .s₁, .s₂, .s₃, .s₄] (by intro x; cases x <;> simp)

/-- Specify the contents of the five bit-program stacks. -/
@[simp] def stks (x a b c d : List Bool) : Stk → List Bool
  | .main => x
  | .s₁ => a
  | .s₂ => b
  | .s₃ => c
  | .s₄ => d

section StksLemmas

variable (x a b c d y : List Bool)

@[simp] theorem update_stks_main : Function.update (stks x a b c d) .main y = stks y a b c d := by
  funext k; cases k <;> rfl

@[simp] theorem update_stks_s₁ : Function.update (stks x a b c d) .s₁ y = stks x y b c d := by
  funext k; cases k <;> rfl

@[simp] theorem update_stks_s₂ : Function.update (stks x a b c d) .s₂ y = stks x a y c d := by
  funext k; cases k <;> rfl

@[simp] theorem update_stks_s₃ : Function.update (stks x a b c d) .s₃ y = stks x a b y d := by
  funext k; cases k <;> rfl

@[simp] theorem update_stks_s₄ : Function.update (stks x a b c d) .s₄ y = stks x a b c y := by
  funext k; cases k <;> rfl

@[simp] theorem update_nil_main :
    Function.update (fun _ => []) Stk.main x = stks x [] [] [] [] := by
  funext k; cases k <;> rfl

end StksLemmas

theorem computableInPolyTime' {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (Λ : Type) [Finite Λ] (main : Λ) (m : Λ → Stmt Stk Λ) (p : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ p.eval (ea a).length,
      StepsTo (TM2.step m) ⟨some main, none, stks (ea a) [] [] [] []⟩
        ⟨none, none, stks (eb (f a)) [] [] [] []⟩ n) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  let := Fintype.ofFinite Λ
  exact
  computableInPolyTime_mk
    { K := Stk, k₀ := .main, k₁ := .main, Γ := fun _ => Bool, Λ := Λ, main := main,
      σ := Option Bool, initialState := none, m := m } (Equiv.refl _) (Equiv.refl _) p
    fun a => by
    obtain ⟨n, hn, h⟩ := h a
    refine ⟨n, hn, ?_⟩
    rw [initList_eq, haltList_eq]
    simpa using h

/-- The linear transition bound `a * n + b`. -/
noncomputable def linPoly (a b : ℕ) : Polynomial ℕ := Polynomial.C a * Polynomial.X + Polynomial.C b

@[simp] theorem eval_linPoly (a b n : ℕ) : (linPoly a b).eval n = a * n + b := by
  simp [linPoly]

/-! ### Prepending a fixed string: `some`, `cons`, and maps that keep the code -/

theorem tm_prepend {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    {f : α → β} (w : List Bool) (hf : ∀ a, BitEncoding.enc (f a) = w ++ BitEncoding.enc a) :
    Nonempty (TM2ComputableInPolyTime BitEncoding.enc BitEncoding.enc f) :=
  computableInPolyTime' Unit () (fun _ => putList .main w stop) 1 fun a =>
    ⟨1, by simp, StepsTo.single (by rw [step_some, hf]; simp)⟩

theorem tm_some {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := Option α))
      (fun a => some a)) :=
  tm_prepend [true] enc_some

theorem tm_cons {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α × List α))
      (BitEncoding.enc (α := List α)) (fun p => p.1 :: p.2)) :=
  tm_prepend [true] fun _ => rfl

/-! ### Constants: erase the input, write a fixed string -/

/-- Erase the input and write the fixed output string `w`. -/
def constProg (w : List Bool) : Fin 2 → Stmt Stk (Fin 2)
  | 0 => read .main (goto' 0) (goto' 0) (goto' 1)
  | 1 => putList .main w stop

theorem tm_const {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    (b : β) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := β))
      (fun _ => b)) := by
  refine computableInPolyTime' (Fin 2) 0 (constProg (BitEncoding.enc b)) (linPoly 1 2)
    fun a => ⟨_, by simp, ((erase_run _ (L := 0) (L' := 1) (k := .main) rfl _ none).trans
      (StepsTo.single (step_some _ _ _ _))).congr (by simp [constProg]) rfl⟩

theorem tm_const_of_subsingleton {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β]
    [BitEncoding β] [Subsingleton β] (f : α → β) (b : β) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := β)) f) :=
  (funext fun _ => Subsingleton.elim _ _ : (fun _ => b) = f) ▸ tm_const b

/-! ### Phases on the five stacks -/

section Phases

variable {Λ : Type} (m : Λ → Stmt Stk Λ)

theorem ones_phase {L L' : Λ} (hL : m L = read .main (put .s₁ true (goto' L)) (goto' L') (goto' L'))
    (x y b c d : List Bool) (v : Option Bool) :
    StepsTo (TM2.step m) ⟨some L, v, stks (BitEncoding.prefixCode x ++ y) [] b c d⟩
      ⟨some L', some false, stks (x ++ y) (List.replicate x.length true) b c d⟩
      (x.length + 1) := by
  simpa using ones_run m (k₁ := .main) (k₂ := .s₁) (by decide) hL x.length
    (stks (BitEncoding.prefixCode x ++ y) [] b c d) (x ++ y) v (by simp [prefixCode_eq])

theorem countMove_phase {L₁ L₂ : Λ} (h₁ : m L₁ = countMove (fun b => [b]) .s₁ .main .s₂ L₁ L₂)
    (x y c d : List Bool) (v : Option Bool) :
    StepsTo (TM2.step m) ⟨some L₁, v, stks (x ++ y) (List.replicate x.length true) [] c d⟩
      ⟨some L₂, none, stks y [] x.reverse c d⟩ (x.length + 1) := by
  simpa using countMove_run m _ (c := .s₁) (k₁ := .main) (k₂ := .s₂) (by decide) (by decide)
    (by decide) h₁ x (stks (x ++ y) (List.replicate x.length true) [] c d) y v (by simp) rfl

theorem extract_phase {L₁ L₂ L₃ L₄ : Λ}
    (h₁ : m L₁ = countMove (fun b => [b]) .s₁ .main .s₂ L₁ L₂)
    (h₂ : m L₂ = read .main (goto' L₂) (goto' L₂) (goto' L₃))
    (h₃ : m L₃ = moveAll (fun b => [b]) .s₂ .main L₃ L₄) (x y c d : List Bool)
    (v : Option Bool) :
    StepsTo (TM2.step m) ⟨some L₁, v, stks (x ++ y) (List.replicate x.length true) [] c d⟩
      ⟨some L₄, none, stks x [] [] c d⟩ (2 * x.length + y.length + 3) :=
  ((countMove_phase m h₁ x y c d v).trans ((erase_run m (k := .main) h₂ _ none).trans
    (move_run m (k₁ := .s₂) (k₂ := .main) (by decide) h₃ _ none))).congr (by simp)
    (by simp; omega)

theorem dropCount_phase {L₁ L₂ : Λ} (h₁ : m L₁ = countMove (fun _ => []) .s₁ .main .s₂ L₁ L₂)
    (x y b c d : List Bool) (v : Option Bool) :
    StepsTo (TM2.step m) ⟨some L₁, v, stks (x ++ y) (List.replicate x.length true) b c d⟩
      ⟨some L₂, none, stks y [] b c d⟩ (x.length + 1) := by
  simpa [show x.reverse.flatMap (fun _ => ([] : List Bool)) = [] by simp] using
    countMove_run m _ (c := .s₁) (k₁ := .main) (k₂ := .s₂) (by decide) (by decide) (by decide) h₁
      x (stks (x ++ y) (List.replicate x.length true) b c d) y v (by simp) rfl

end Phases

/-! ### Projections -/

/-- Discard the length-delimited first component of a pair and retain the second. -/
def sndProg : Fin 3 → Stmt Stk (Fin 3)
  | 0 => read .main (put .s₁ true (goto' 0)) (goto' 1) (goto' 1)
  | 1 => countMove (fun _ => []) .s₁ .main .s₂ 1 2
  | 2 => stop

theorem tm_snd {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α × β)) (BitEncoding.enc (α := β))
      (fun p => p.2)) := by
  refine computableInPolyTime' (Fin 3) 0 sndProg (linPoly 1 3) fun p =>
    ⟨2 * (BitEncoding.enc p.1).length + 3, ?_, ?_⟩
  · simp [enc_prod, length_prefixCode]; omega
  · exact ((ones_phase sndProg (L := 0) (L' := 1) rfl (BitEncoding.enc p.1) (BitEncoding.enc p.2)
      [] [] [] none).trans ((dropCount_phase sndProg (L₁ := 1) (L₂ := 2) rfl _ _ [] [] []
      (some false)).trans (stop_run sndProg (L := 2) rfl _ none))).of_eq (by omega)

/-! ### `getD` -/

/-- Compute option elimination with a supplied default from an encoded pair. -/
def getDProg : Fin 6 → Stmt Stk (Fin 6)
  | 0 => read .main (put .s₁ true (goto' 0)) (goto' 1) (goto' 1)
  | 1 =>
    let q := read .main (goto' 2) (goto' 5) (goto' 5)
    read .s₁ q q q
  | 2 => countMove (fun b => [b]) .s₁ .main .s₂ 2 3
  | 3 => read .main (goto' 3) (goto' 3) (goto' 4)
  | 4 => moveAll (fun b => [b]) .s₂ .main 4 5
  | 5 => stop

theorem tm_getD {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := Option α × α))
      (BitEncoding.enc (α := α)) (fun p => p.1.getD p.2)) := by
  refine computableInPolyTime' (Fin 6) 0 getDProg (linPoly 2 6) fun p =>
    ⟨p.1.elim 4 fun a => 3 * (BitEncoding.enc a).length + (BitEncoding.enc p.2).length + 7,
      ?_, ?_⟩
  · obtain ⟨o, y⟩ := p
    cases o <;> simp [enc_prod, enc_some, enc_none, length_prefixCode]; omega
  · obtain ⟨o, y⟩ := p
    cases o with
    | none => rw [enc_prod, enc_none]; simp [StepsTo, Function.iterate_succ_apply, flip, getDProg,
        stepAux_read, prefixCode_eq]
    | some a =>
      refine ((ones_phase getDProg (L := 0) (L' := 1) rfl (true :: BitEncoding.enc a)
        (BitEncoding.enc y) [] [] [] none).trans (StepsTo.trans (b := ⟨some 2, some true,
          stks (BitEncoding.enc a ++ BitEncoding.enc y)
            (List.replicate (BitEncoding.enc a).length true) [] [] []⟩)
        (StepsTo.single (by rw [step_some]; simp [getDProg, stepAux_read, List.replicate_succ]))
        ((extract_phase getDProg (L₁ := 2) (L₂ := 3) (L₃ := 4) (L₄ := 5) rfl rfl rfl _ _ [] []
          (some true)).trans (stop_run getDProg (L := 5) rfl _ none)))).of_eq (by simp; omega)

/-! ### Lists: length -/

/-- Count the elements of an encoded list and output the count in unary. -/
def lengthProg : Fin 5 → Stmt Stk (Fin 5)
  | 0 => read .main (put .s₃ true (goto' 1)) (goto' 3) (goto' 3)
  | 1 => read .main (put .s₁ true (goto' 1)) (goto' 2) (goto' 2)
  | 2 => countMove (fun _ => []) .s₁ .main .s₂ 2 0
  | 3 => moveAll (fun b => [b]) .s₃ .main 3 4
  | 4 => stop

theorem lengthProg_loop {α : Type} [Primcodable α] [BitEncoding α] (l : List α) :
    ∀ (j : ℕ) (v : Option Bool),
    StepsTo (TM2.step lengthProg)
      ⟨some 0, v, stks (BitEncoding.enc l) [] [] (List.replicate j true) []⟩
      ⟨some 3, some false, stks [] [] [] (List.replicate (j + l.length) true) []⟩
      ((BitEncoding.enc l).length + l.length) := by
  induction l with
  | nil =>
    intro j v
    exact StepsTo.single (by rw [step_some]; simp [lengthProg, stepAux_read, enc_list,
      BitEncoding.listEnc])
  | cons a l ih =>
    intro j v
    refine (StepsTo.trans (b := ⟨some 1, some true, stks (BitEncoding.prefixCode
        (BitEncoding.enc a) ++ BitEncoding.enc l) [] [] (List.replicate (j + 1) true) []⟩)
      (StepsTo.single (by rw [step_some]; simp [lengthProg, stepAux_read, enc_list, listEnc_cons,
        List.replicate_succ]))
      ((ones_phase lengthProg (L := 1) (L' := 2) rfl _ _ [] _ [] (some true)).trans
      ((dropCount_phase lengthProg (L₁ := 2) (L₂ := 0) rfl _ _ [] _ [] (some false)).trans
      (ih (j + 1) none)))).congr ?_ ?_
    · simp [Nat.add_assoc, Nat.add_comm 1]
    · simp [enc_list, listEnc_cons, length_prefixCode]; omega

theorem tm_length {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := List α)) (BitEncoding.enc (α := ℕ))
      List.length) := by
  refine computableInPolyTime' (Fin 5) 0 lengthProg (linPoly 3 2) fun l =>
    ⟨(BitEncoding.enc l).length + 2 * l.length + 2, ?_, ?_⟩
  · have := length_le_listEnc BitEncoding.enc l
    simp only [eval_linPoly, enc_list] at this ⊢; omega
  · exact ((lengthProg_loop l 0 none).trans ((move_run lengthProg (L := 3) (L' := 4) (k₁ := .s₃)
      (k₂ := .main) (by decide) rfl _ _).trans (stop_run lengthProg (L := 4) rfl _ none))).congr
      (by simp [enc_nat]) (by simp; omega)

/-! ### Equality test -/

/-- Compare the two bit strings in an encoded pair, clearing scratch stacks before halting. -/
def beqProg : Fin 11 → Stmt Stk (Fin 11)
  | 0 => read .main (put .s₁ true (goto' 0)) (goto' 1) (goto' 1)
  | 1 => countMove (fun b => [b]) .s₁ .main .s₂ 1 2
  | 2 => moveAll (fun b => [b]) .s₂ .s₃ 2 3
  | 3 => read .s₃ (goto' 4) (goto' 5) (goto' 6)
  | 4 => read .main (goto' 3) (goto' 7) (goto' 7)
  | 5 => read .main (goto' 7) (goto' 3) (goto' 7)
  | 6 => read .main (goto' 7) (goto' 7) (goto' 9)
  | 7 => read .main (goto' 7) (goto' 7) (goto' 8)
  | 8 => read .s₃ (goto' 8) (goto' 8) (goto' 10)
  | 9 => put .main true stop
  | 10 => put .main false stop

theorem beqProg_neq (u w : List Bool) (v : Option Bool) :
    StepsTo (TM2.step beqProg) ⟨some 7, v, stks w [] [] u []⟩
      ⟨none, none, stks [false] [] [] [] []⟩ (w.length + u.length + 3) :=
  ((erase_run beqProg (L := 7) (L' := 8) (k := .main) rfl _ v).trans
    ((erase_run beqProg (L := 8) (L' := 10) (k := .s₃) rfl _ none).trans
    (StepsTo.single (step_some _ _ _ _)))).congr (by simp [beqProg]) (by simp; omega)

theorem beqProg_cmp (u : List Bool) :
    ∀ (w : List Bool) (v : Option Bool), ∃ T ≤ 2 * (u.length + w.length) + 5,
    StepsTo (TM2.step beqProg) ⟨some 3, v, stks w [] [] u []⟩
      ⟨none, none, stks [decide (u = w)] [] [] [] []⟩ T := by
  induction u with
  | nil =>
    intro w v
    cases w with
    | nil => exact ⟨3, by simp, by simp [StepsTo, Function.iterate_succ_apply, flip, beqProg,
        stepAux_read]⟩
    | cons b w =>
      have e₀ : StepsTo (TM2.step beqProg) ⟨some 3, v, stks (b :: w) [] [] [] []⟩
          ⟨some 7, some b, stks w [] [] [] []⟩ 2 := by
        cases b <;> simp [StepsTo, Function.iterate_succ_apply, flip, beqProg, stepAux_read]
      exact ⟨_, by simp; omega, (e₀.trans (beqProg_neq [] w (some b))).congr (by simp) rfl⟩
  | cons a u ih =>
    intro w v
    cases w with
    | nil =>
      have e₀ : StepsTo (TM2.step beqProg) ⟨some 3, v, stks [] [] [] (a :: u) []⟩
          ⟨some 7, none, stks [] [] [] u []⟩ 2 := by
        cases a <;> simp [StepsTo, Function.iterate_succ_apply, flip, beqProg, stepAux_read]
      exact ⟨_, by simp; omega, (e₀.trans (beqProg_neq u [] none)).congr (by simp) rfl⟩
    | cons b w =>
      by_cases hab : a = b
      · subst hab
        obtain ⟨T, hT, e₁⟩ := ih w (some a)
        have e₀ : StepsTo (TM2.step beqProg) ⟨some 3, v, stks (a :: w) [] [] (a :: u) []⟩
            ⟨some 3, some a, stks w [] [] u []⟩ 2 := by
          cases a <;> simp [StepsTo, Function.iterate_succ_apply, flip, beqProg, stepAux_read]
        exact ⟨T + 2, by simp; omega, (e₀.trans e₁).congr (by simp) (by omega)⟩
      · have e₀ : StepsTo (TM2.step beqProg) ⟨some 3, v, stks (b :: w) [] [] (a :: u) []⟩
            ⟨some 7, some b, stks w [] [] u []⟩ 2 := by
          cases a <;> cases b <;>
            simp_all [StepsTo, Function.iterate_succ_apply, flip, beqProg, stepAux_read]
        exact ⟨_, by simp; omega, (e₀.trans (beqProg_neq u w (some b))).congr (by simp [hab])
          rfl⟩
theorem tm_beq {α : Type} [Primcodable α] [BitEncoding α] [DecidableEq α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α × α))
      (BitEncoding.enc (α := Bool)) (fun p => decide (p.1 = p.2))) := by
  refine computableInPolyTime' (Fin 11) 0 beqProg (linPoly 3 8) fun p => ?_
  obtain ⟨x, y⟩ := p
  obtain ⟨T, hT, e₄⟩ := beqProg_cmp (BitEncoding.enc x) (BitEncoding.enc y) none
  refine ⟨3 * (BitEncoding.enc x).length + 3 + T, ?_, ?_⟩
  · simp [enc_prod, length_prefixCode]; omega
  refine ((ones_phase beqProg (L := 0) (L' := 1) rfl (BitEncoding.enc x) (BitEncoding.enc y) [] []
    [] none).trans ((countMove_phase beqProg (L₁ := 1) (L₂ := 2) rfl _ _ [] [] (some false)).trans
    ((move_run beqProg (L := 2) (L' := 3) (k₁ := .s₂) (k₂ := .s₃) (by decide) rfl _ none).trans
    (by simpa using e₄)))).congr ?_ (by simp; omega)
  simp [enc_bool, BitEncoding.enc_injective.eq_iff]

/-! ### Writing and reading the code of a bit string -/

theorem enc_listBool (w : List Bool) :
    BitEncoding.enc w = w.flatMap (fun b => [true, true, false, b]) ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [enc_list, listEnc_cons, ← enc_list, ih]
    simp [enc_bool, BitEncoding.prefixCode]

/-! ### The code of a value, as a bit string -/

/-- Convert an encoded value's bits into the self-delimiting encoding of a bit list. -/
def encProg : Fin 4 → Stmt Stk (Fin 4)
  | 0 => moveAll (fun b => [b]) .main .s₂ 0 1
  | 1 => put .main false (goto' 2)
  | 2 => moveAll (fun b => [true, true, false, b]) .s₂ .main 2 3
  | 3 => stop

theorem tm_enc {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := List Bool))
      (fun a => BitEncoding.enc a)) := by
  refine computableInPolyTime' (Fin 4) 0 encProg (linPoly 2 4) fun a => ⟨_, ?_,
    ((move_run encProg (L := 0) (L' := 1) (k₁ := .main) (k₂ := .s₂) (by decide) rfl _ none).trans
    ((StepsTo.single (step_some _ _ _ _)).trans ((moveAll_run encProg
    (fun b => [true, true, false, b]) (L := 2) (L' := 3) (k₁ := .s₂) (k₂ := .main) (by decide)
    rfl _ none).trans (stop_run encProg (L := 3) rfl _ none)))).congr ?_ rfl⟩
  · simp; omega
  · simp [enc_listBool]

/-! ### Arbitrary machines: simulation, stack sizes, polynomial bounds -/

end BitMachines
end Turing
