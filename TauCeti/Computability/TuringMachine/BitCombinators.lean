/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.BitPrimitives
public import TauCeti.Computability.TuringMachine.Composition
public import Mathlib.Data.Nat.SuccPred
public import TauCeti.Algebra.Polynomial.Eval.Monotone

/-!
# Composition, pairing and bounded iteration of bit-stack machines

A component machine is embedded in a fixed finite-control wrapper. A separate bit stack
stores a unary iteration clock. The execution proof counts component calls and all transfers;
a polynomial bound on intermediate encoded lengths yields a polynomial bound on actual steps.
-/

@[expose] public section

namespace Turing
namespace BitMachines

open Computability

theorem StepsTo.map {σ τ : Type} {f : σ → Option σ} {g : τ → Option τ} (e : σ → τ)
    (he : ∀ c c', f c = some c' → g (e c) = some (e c')) {a b : σ} {n : ℕ}
    (h : StepsTo f a b n) : StepsTo g (e a) (e b) n := by
  induction n generalizing a with
  | zero => obtain rfl := Option.some.inj h; exact StepsTo.refl _ _
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := h.succ_inv
    exact StepsTo.head (he a c hc) (ih h)

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

section Transfer

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

/-- Transfer one symbol between stacks with possibly different bit alphabets. -/
def xfer (k₁ k₂ : K) (get : Γ k₁ → Bool) (put : Bool → Γ k₂) (rd : σ → Option Bool)
    (wr : σ → Option Bool → σ) (L L' : Λ) : TM2.Stmt Γ Λ σ :=
  .pop k₁ (fun s o => wr s (o.map get)) (.branch (fun s => (rd s).isSome)
    (.push k₂ (fun s => put ((rd s).getD false)) (.goto fun _ => L)) (.goto fun _ => L'))

theorem xfer_run (m : Λ → TM2.Stmt Γ Λ σ) {k₁ k₂ : K} (hk : k₁ ≠ k₂) {get : Γ k₁ → Bool}
    {put : Bool → Γ k₂} {rd : σ → Option Bool} {wr : σ → Option Bool → σ} {L L' : Λ}
    (hL : m L = xfer k₁ k₂ get put rd wr L L') (hrw : ∀ s o, rd (wr s o) = o)
    (hww : ∀ s o o', wr (wr s o) o' = wr s o') (S : ∀ k, List (Γ k)) (s : σ) (o : Option Bool) :
    StepsTo (TM2.step m) ⟨some L, wr s o, S⟩ ⟨some L', wr s none, Function.update
      (Function.update S k₁ []) k₂ (((S k₁).map (put ∘ get)).reverse ++ S k₂)⟩
      ((S k₁).length + 1) := by
  simpa using StepsTo.loop (f := TM2.step m)
    (fun p l o => ⟨some L, wr s o, Function.update (Function.update S k₁ l) k₂
      ((p.map (put ∘ get)).reverse ++ S k₂)⟩)
    (fun p => ⟨some L', wr s none, Function.update (Function.update S k₁ []) k₂
      ((p.map (put ∘ get)).reverse ++ S k₂)⟩)
    (fun _ x _ _ => ⟨some (get x), by
      simp [hL, xfer, hrw, hww, Function.update_of_ne hk, Function.update_comm hk.symm]⟩)
    (fun _ _ => by simp [hL, xfer, hrw, hww, Function.update_of_ne hk]) (S k₁) [] o

end Transfer

/-! ### Embedding the statements of one machine into another -/

section Embed

variable {K K' Λ Λ' σ σ' : Type} {Γ' : K' → Type} [DecidableEq K'] (ι : K → K') (lab : Λ → Λ')
  (get : σ' → σ) (set : σ' → σ → σ') (fin : TM2.Stmt Γ' Λ' σ')

/-- Embed a statement by translating stack keys, labels, registers, and its halt continuation. -/
def embStmt : TM2.Stmt (fun k => Γ' (ι k)) Λ σ → TM2.Stmt Γ' Λ' σ'
  | .push k f q => .push (ι k) (fun s => f (get s)) (embStmt q)
  | .peek k f q => .peek (ι k) (fun s o => set s (f (get s) o)) (embStmt q)
  | .pop k f q => .pop (ι k) (fun s o => set s (f (get s) o)) (embStmt q)
  | .load f q => .load (fun s => set s (f (get s))) (embStmt q)
  | .branch f q₁ q₂ => .branch (fun s => f (get s)) (embStmt q₁) (embStmt q₂)
  | .goto f => .goto fun s => lab (f (get s))
  | .halt => fin

variable [DecidableEq K]

theorem StepsTo.lift {Γ : K → Type} {m : Λ → TM2.Stmt Γ Λ σ} {m' : Λ' → TM2.Stmt Γ' Λ' σ'}
    (e : TM2.Cfg Γ Λ σ → TM2.Cfg Γ' Λ' σ')
    (he : ∀ L v S, TM2.step m' (e ⟨some L, v, S⟩) = some (e (TM2.stepAux (m L) v S)))
    {c c' : TM2.Cfg Γ Λ σ} {n : ℕ} (h : StepsTo (TM2.step m) c c' n) :
    StepsTo (TM2.step m') (e c) (e c') n :=
  h.map e fun c c' h => by obtain ⟨_ | L, v, S⟩ := c <;> cases h; exact he L v S

end Embed

section Join

variable {A B : Type} {Γ : A ⊕ B → Type} [DecidableEq A] [DecidableEq B]

/-- Combine disjoint stack maps indexed by the two sides of a sum. -/
@[simp] def join (S : ∀ a, List (Γ (.inl a))) (T : ∀ b, List (Γ (.inr b))) : ∀ k, List (Γ k)
  | .inl a => S a
  | .inr b => T b

theorem update_join_inl (S : ∀ a, List (Γ (.inl a))) (T : ∀ b, List (Γ (.inr b))) (a : A)
    (x : List (Γ (.inl a))) :
    Function.update (join S T) (.inl a) x = join (Function.update S a x) T := by
  funext k; rcases k with k | k <;> simp [Function.update_of_ne]

theorem update_join_inr (S : ∀ a, List (Γ (.inl a))) (T : ∀ b, List (Γ (.inr b))) (b : B)
    (x : List (Γ (.inr b))) :
    Function.update (join S T) (.inr b) x = join S (Function.update T b x) := by
  funext k; rcases k with k | k <;> simp [Function.update_of_ne]

end Join

/-- Compose actual polynomial-time machines, including the cost of their output transfer. -/
theorem tm_comp {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ}
    (hg : TM2ComputableInPolyTime eb ec g) (hf : TM2ComputableInPolyTime ea eb f) :
    Nonempty (TM2ComputableInPolyTime ea ec (g ∘ f)) :=
  ⟨hg.comp hf⟩

namespace Wrap

variable (M : FinTM2) (PL : Type)

/-- Stack keys for a wrapped machine and its five bit-program scratch stacks. -/
abbrev WK : Type := M.K ⊕ Stk

/-- The original alphabet on machine stacks and the bit alphabet on scratch stacks. -/
abbrev WΓ : WK M → Type
  | .inl k => M.Γ k
  | .inr _ => Bool

/-- Labels for the original machine, wrapper program, and two transfer loops. -/
abbrev WΛ : Type := M.Λ ⊕ PL ⊕ Bool

/-- Separate registers for the original machine and bit wrapper. -/
abbrev Wσ : Type := M.σ × Option Bool

variable {M PL}

/-- Embed an original-machine statement, transferring its output when it halts. -/
def liftM (q : TM2.Stmt M.Γ M.Λ M.σ) : TM2.Stmt (WΓ M) (WΛ M PL) (Wσ M) :=
  embStmt Sum.inl Sum.inl Prod.fst (fun s v => (v, s.2)) (.goto fun _ => .inr (.inr true)) q

/-- Embed a wrapper statement whose halt either calls the machine or terminates the wrapper. -/
def liftP (q : Stmt Stk PL) : TM2.Stmt (WΓ M) (WΛ M PL) (Wσ M) :=
  embStmt Sum.inr (fun L => .inr (.inl L)) Prod.snd (fun s r => (s.1, r))
    (.branch (fun s => s.2 == some true) (.goto fun _ => .inr (.inr false)) .halt) q

/-- Embed an original-machine configuration while retaining the wrapper's register and stacks. -/
def embM (r : Option Bool) (T : Stk → List Bool) (c : TM2.Cfg M.Γ M.Λ M.σ) :
    TM2.Cfg (WΓ M) (WΛ M PL) (Wσ M) :=
  ⟨some (c.l.elim (.inr (.inr true)) .inl), (c.var, r), join c.stk T⟩

/-- Continue with the input transfer exactly when the wrapper register requests a machine call. -/
def exitL (r : Option Bool) : Option (WΛ M PL) :=
  if r = some true then some (.inr (.inr false)) else none

/-- Embed a bit-program configuration while retaining the original machine's register and stacks. -/
def embP (v : M.σ) (S : ∀ k, List (M.Γ k)) (c : Cfg Stk PL) : TM2.Cfg (WΓ M) (WΛ M PL) (Wσ M) :=
  ⟨c.l.elim (exitL c.var) fun L => some (.inr (.inl L)), (v, c.var), join S c.stk⟩

theorem stepAux_liftM (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (r : Option Bool)
    (S : ∀ k, List (M.Γ k)) (T : Stk → List Bool) :
    TM2.stepAux (liftM (PL := PL) q) (v, r) (join S T) = embM r T (TM2.stepAux q v S) := by
  induction q generalizing v S <;> simp_all [liftM, embStmt, TM2.stepAux, update_join_inl,
    apply_ite (embM (PL := PL) r T)] <;> rfl

theorem stepAux_liftP (q : Stmt Stk PL) (v : M.σ) (r : Option Bool) (S : ∀ k, List (M.Γ k))
    (T : Stk → List Bool) :
    TM2.stepAux (liftP (M := M) q) (v, r) (join S T) = embP v S (TM2.stepAux q r T) := by
  induction q generalizing r T with
  | halt => rcases r with _ | _ | _ <;> rfl
  | _ => simp_all [liftP, embStmt, TM2.stepAux, update_join_inr, apply_ite (embP v S)] <;> rfl
/-- One step copying the wrapper's prepared input into the original machine's input stack. -/
def transferIn (e : M.Γ M.k₀ ≃ Bool) : TM2.Stmt (WΓ M) (WΛ M PL) (Wσ M) :=
  xfer (.inr .s₄) (.inl M.k₀) id e.symm (·.2) (fun s o => (s.1, o)) (.inr (.inr false))
    (.inl M.main)

/-- Run the bit wrapper, original machine, and input/output transfer phases as one program. -/
def prog (P : PL → Stmt Stk PL) (post : PL) (eIn : M.Γ M.k₀ ≃ Bool) (eOut : M.Γ M.k₁ ≃ Bool) :
    WΛ M PL → TM2.Stmt (WΓ M) (WΛ M PL) (Wσ M)
  | .inl L => liftM (M.m L)
  | .inr (.inl L) => liftP (P L)
  | .inr (.inr false) => transferIn eIn
  | .inr (.inr true) => xfer (.inl M.k₁) (.inr .s₄) eOut id (·.2) (fun s o => (s.1, o))
      (.inr (.inr true)) (.inr (.inl post))

section Any

variable (m : WΛ M PL → TM2.Stmt (WΓ M) (WΛ M PL) (Wσ M))

theorem seg {P : PL → Stmt Stk PL} {c c' : Cfg Stk PL} {n : ℕ} (h : StepsTo (TM2.step P) c c' n)
    (hP : ∀ L, m (.inr (.inl L)) = liftP (P L) := by intro _; rfl) :
    StepsTo (TM2.step m) (embP M.initialState (fun k => ([] : List (M.Γ k))) c)
      (embP M.initialState (fun k => ([] : List (M.Γ k))) c') n :=
  h.lift (m' := m) (embP _ _) fun L r T =>
    congrArg some ((congrArg (TM2.stepAux · _ _) (hP L)).trans (stepAux_liftP (P L) _ r _ T))

theorem transferIn_run (eIn : M.Γ M.k₀ ≃ Bool) (hIn : m (.inr (.inr false)) = transferIn eIn)
    (x : List Bool) (S : ∀ k, List (M.Γ k)) (T : Stk → List Bool) (v : M.σ) (r : Option Bool)
    (hT : T .s₄ = x) :
    StepsTo (TM2.step m) ⟨some (.inr (.inr false)), (v, r), join S T⟩
      ⟨some (.inl M.main), (v, none), join
        (Function.update S M.k₀ (x.reverse.map eIn.symm ++ S M.k₀)) (Function.update T .s₄ [])⟩
      (x.length + 1) := by
  have h := xfer_run m (k₁ := .inr .s₄) (k₂ := .inl M.k₀) (get := id) (put := eIn.symm)
    (rd := (·.2)) (wr := fun s o => (s.1, o)) (L := .inr (.inr false)) (L' := .inl M.main)
    (by simp) hIn (fun _ _ => rfl) (fun _ _ _ => rfl) (join S T) (v, r) r
  subst hT
  simpa [update_join_inl, update_join_inr, Function.comp_def] using h

/-- Package a wrapped program as a finite-control TM2 with bit input and output. -/
abbrev machine [Fintype PL] (start : PL) : FinTM2 where
  K := WK M
  k₀ := .inr .main
  k₁ := .inr .main
  Γ := WΓ M
  Λ := WΛ M PL
  main := .inr (.inl start)
  σ := Wσ M
  initialState := (M.initialState, none)
  m := m

theorem computableInPolyTime_wrap {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} [Finite PL] (start : PL) (p : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ p.eval (ea a).length, StepsTo (TM2.step m)
      (embP M.initialState (fun _ => []) ⟨some start, none, stks (ea a) [] [] [] []⟩)
      (embP M.initialState (fun _ => []) ⟨none, none, stks (eb (f a)) [] [] [] []⟩) n) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  classical
  let := Fintype.ofFinite PL
  have e : ∀ l, Function.update (fun k => ([] : List (WΓ M k))) (.inr .main) l =
      join (fun _ => []) (stks l [] [] [] []) := fun l => by
    funext k; rcases k with k | (_ | _ | _ | _ | _) <;> simp [Function.update_of_ne]
  refine computableInPolyTime_mk (machine m start) (Equiv.refl _) (Equiv.refl _) p fun a => ?_
  rw [initList_eq, haltList_eq, e, e]
  simpa [embP, exitL] using h a

end Any

variable (P : PL → Stmt Stk PL) (post : PL) (eIn : M.Γ M.k₀ ≃ Bool) (eOut : M.Γ M.k₁ ≃ Bool)

theorem call (L : PL) (r : Option Bool) (T T₁ : Stk → List Bool) (z y : List Bool) (n₁ t : ℕ)
    (hpre : StepsTo (TM2.step P) ⟨some L, r, T⟩ ⟨none, some true, T₁⟩ n₁)
    (hT₁ : T₁ .s₄ = z.reverse)
    (hM : StepsTo (TM2.step M.m) (initList M (z.map eIn.symm)) (haltList M (y.map eOut.symm)) t) :
    StepsTo (TM2.step (prog P post eIn eOut))
      (embP M.initialState (fun k => ([] : List (M.Γ k))) ⟨some L, r, T⟩)
      (embP M.initialState (fun k => ([] : List (M.Γ k)))
        ⟨some post, none, Function.update T₁ .s₄ y.reverse⟩)
      (n₁ + ((z.reverse.length + 1) + (t + (y.length + 1)))) := by
  have e₁ := seg (prog P post eIn eOut) hpre
  have e₂ := transferIn_run (prog P post eIn eOut) eIn rfl z.reverse
    (fun k => ([] : List (M.Γ k))) T₁ M.initialState (some true) hT₁
  have e₃ := hM.lift (m' := prog P post eIn eOut) (embM none (Function.update T₁ .s₄ []))
    fun L v S => congrArg some (stepAux_liftM (M.m L) v none S _)
  have e₄ := xfer_run (prog P post eIn eOut) (k₁ := .inl M.k₁) (k₂ := .inr .s₄) (get := eOut)
    (put := id) (rd := (·.2)) (wr := fun s o => (s.1, o)) (L := .inr (.inr true))
    (L' := .inr (.inl post)) (by simp) rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (join (Function.update (fun k => []) M.k₁ (y.map eOut.symm)) (Function.update T₁ .s₄ []))
    (M.initialState, none) none
  simp only [embM, initList_eq, haltList_eq, Option.elim] at e₃
  simp only [List.reverse_reverse, List.append_nil] at e₂
  refine e₁.trans (e₂.trans (e₃.trans (e₄.congr ?_ (by simp))))
  simp [embP, update_join_inl, update_join_inr, Function.comp_def]

end Wrap

/-! ### Iterating a machine -/

/-- Wrapper phases for iterating a machine a unary-encoded number of times. -/
def iterProg : Fin 7 → Stmt Stk (Fin 7)
  | 0 => read .main (put .s₁ true (goto' 0)) (goto' 1) (goto' 1)
  | 1 => countMove (fun b => [b]) .s₁ .main .s₂ 1 2
  | 2 => read .s₂ (goto' 3) (goto' 3) (goto' 6)
  | 3 => moveAll (fun b => [b]) .main .s₄ 3 4
  | 4 => TM2.Stmt.load (fun _ => some true) TM2.Stmt.halt
  | 5 => moveAll (fun b => [b]) .s₄ .main 5 2
  | 6 => stop

theorem iterProg_loop {α : Type} [Primcodable α] [BitEncoding α] {g : α → α}
    (hg : TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := α)) g)
    (B i : ℕ) :
    ∀ (s : α) (v : Option Bool), (∀ j ≤ i, (BitEncoding.enc (g^[j] s)).length ≤ B) →
    ∃ T ≤ i * (5 * B + hg.time.eval B + 7) + 2,
    StepsTo (TM2.step (Wrap.prog iterProg 5 hg.inputAlphabet hg.outputAlphabet))
      (Wrap.embP hg.tm.initialState (fun k => ([] : List (hg.tm.Γ k)))
        ⟨some 2, v, stks (BitEncoding.enc s) [] (List.replicate i true) [] []⟩)
      (Wrap.embP hg.tm.initialState (fun k => ([] : List (hg.tm.Γ k)))
        ⟨none, none, stks (BitEncoding.enc (g^[i] s)) [] [] [] []⟩) T := by
  induction i with
  | zero =>
    intro s v _
    exact ⟨2, by omega, Wrap.seg (Wrap.prog iterProg 5 hg.inputAlphabet hg.outputAlphabet)
      (P := iterProg) (by simp [StepsTo, Function.iterate_succ_apply, flip, iterProg,
        stepAux_read])⟩
  | succ i ih =>
    intro s v hB
    obtain ⟨⟨t, hM⟩, ht⟩ := hg.outputsFun s
    simp only at ht
    set X := BitEncoding.enc s
    set Y := BitEncoding.enc (g s)
    have hX : X.length ≤ B := hB 0 (by omega)
    have hY : Y.length ≤ B := hB 1 (by omega)
    have ht' : t ≤ hg.time.eval B := le_trans ht (Polynomial.eval_le_eval _ hX)
    obtain ⟨T, hT, e₃⟩ := ih (g s) none fun j hj => by
      have := hB (j + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
    refine ⟨_, ?_, ((Wrap.call iterProg 5 hg.inputAlphabet hg.outputAlphabet 2 v _
      (stks [] [] (List.replicate i true) [] X.reverse) X Y _ t ((StepsTo.single
        (step_some iterProg 2 v (stks X [] (List.replicate (i + 1) true) [] []))).trans
        ((move_run iterProg (L := 3) (L' := 4) (k₁ := .main) (k₂ := .s₄) (by decide) rfl _ _).trans
        (StepsTo.single (step_some _ _ _ _))) |>.congr (by simp [iterProg]) rfl) rfl hM).trans
      ((Wrap.seg _ ((move_run iterProg (L := 5) (L' := 2) (k₁ := .s₄) (k₂ := .main) (by decide)
        rfl _ none).congr ?_ rfl)).trans e₃)).congr ?_ rfl⟩
    · simp; nlinarith
    · simp [Y]
    · simp [Function.iterate_succ_apply]

theorem tm_iterate {α : Type} [Primcodable α] [BitEncoding α] {g : α → α}
    (hg : TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := α)) g)
    (Q : Polynomial ℕ)
    (hQ : ∀ (N : ℕ) (s : α), ∀ i ≤ N,
      (BitEncoding.enc (g^[i] s)).length ≤ Q.eval (BitEncoding.enc (N, s)).length) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := ℕ × α)) (BitEncoding.enc (α := α))
      (fun p => g^[p.1] p.2)) := by
  refine Wrap.computableInPolyTime_wrap
    (Wrap.prog iterProg 5 hg.inputAlphabet hg.outputAlphabet) 0 (Polynomial.X *
      (Polynomial.C 5 * Q + hg.time.comp Q + Polynomial.C 7) + Polynomial.C 2 * Polynomial.X +
      Polynomial.C 4) fun p => ?_
  obtain ⟨N, s⟩ := p
  set n := (BitEncoding.enc (N, s)).length with hn
  obtain ⟨T, hT, e₃⟩ := iterProg_loop hg (Q.eval n) N s none fun j hj => hQ N s j hj
  have hN : 2 * N + 1 ≤ n := by
    simp [hn, enc_prod, enc_nat, length_prefixCode]
  refine ⟨_, ?_, (Wrap.seg _ (((ones_phase iterProg (L := 0) (L' := 1) rfl (List.replicate N true)
    (BitEncoding.enc s) [] [] [] none).trans (countMove_phase iterProg (L₁ := 1) (L₂ := 2) rfl _ _
    [] [] (some false))).congr (by simp) rfl)).trans e₃⟩
  have := Nat.mul_le_mul_right (5 * Q.eval n + hg.time.eval (Q.eval n) + 7) (show N ≤ n by omega)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_comp, List.length_replicate]
  omega

/-! ### Pairing: duplicate the input, apply a machine to the first component, swap -/

/-- Copy an encoded value into both components of a length-delimited pair. -/
def dupProg : Fin 6 → Stmt Stk (Fin 6)
  | 0 => read .main (put .s₁ true (put .s₂ true (goto' 0)))
      (put .s₁ false (put .s₂ false (goto' 0))) (goto' 1)
  | 1 => moveAll (fun b => [b]) .s₁ .main 1 2
  | 2 => read .s₂ (put .main true (put .s₃ true (goto' 2)))
      (put .main false (put .s₃ true (goto' 2))) (goto' 3)
  | 3 => put .main false (goto' 4)
  | 4 => moveAll (fun b => [b]) .s₃ .main 4 5
  | 5 => stop

theorem tm_dup {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := α × α))
      (fun a => (a, a))) := by
  refine computableInPolyTime' (Fin 6) 0 dupProg (linPoly 4 6) fun a => ⟨_, ?_,
    ((moveMap_run dupProg id (L := 0) (L' := 1) (k₁ := .main) (k₂ := .s₁) (k₃ := .s₂)
      (by decide) (by decide) (by decide) rfl _ none).trans
    ((move_run dupProg (L := 1) (L' := 2) (k₁ := .s₁) (k₂ := .main) (by decide) rfl _ none).trans
    ((moveMap_run dupProg (fun _ => true) (L := 2) (L' := 3) (k₁ := .s₂) (k₂ := .main)
      (k₃ := .s₃) (by decide) (by decide) (by decide) rfl _ none).trans
    ((StepsTo.single (step_some _ _ _ _)).trans
    ((move_run dupProg (L := 4) (L' := 5) (k₁ := .s₃) (k₂ := .main) (by decide) rfl _ none).trans
    (stop_run dupProg (L := 5) rfl _ none)))))).congr ?_ rfl⟩
  · simp; omega
  · simp [enc_prod, prefixCode_eq]

/-- Wrapper phases that apply a machine to a pair's first component and preserve the second. -/
def tensLProg : Fin 7 → Stmt Stk (Fin 7)
  | 0 => read .main (put .s₁ true (goto' 0)) (goto' 1) (goto' 1)
  | 1 => countMove (fun b => [b]) .s₁ .main .s₄ 1 2
  | 2 => TM2.Stmt.load (fun _ => some true) TM2.Stmt.halt
  | 3 => read .s₄ (put .main true (put .s₃ true (goto' 3)))
      (put .main false (put .s₃ true (goto' 3))) (goto' 4)
  | 4 => put .main false (goto' 5)
  | 5 => moveAll (fun b => [b]) .s₃ .main 5 6
  | 6 => stop

theorem tm_tensL {α β δ : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    [Primcodable δ] [BitEncoding δ] {f : α → β}
    (hf : TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := β)) f) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α × δ))
      (BitEncoding.enc (α := β × δ)) (fun p => (f p.1, p.2))) := by
  refine Wrap.computableInPolyTime_wrap
    (Wrap.prog tensLProg 3 hf.inputAlphabet hf.outputAlphabet) 0
    (Polynomial.C 6 * Polynomial.X + Polynomial.C (3 * hf.tm.maxPushes + 1) * hf.time +
      Polynomial.C 9) fun p => ?_
  obtain ⟨x, w⟩ := p
  obtain ⟨⟨t, hM⟩, ht⟩ := hf.outputsFun x
  simp only at ht
  set X := BitEncoding.enc x
  set Y := BitEncoding.enc (f x)
  set W := BitEncoding.enc w
  have hlen : Y.length ≤ X.length + hf.tm.maxPushes * t := by
    let hout : TM2Outputs hf.tm ((BitEncoding.enc x).map hf.inputAlphabet.symm)
        (some ((BitEncoding.enc (f x)).map hf.outputAlphabet.symm)) := ⟨t, hM⟩
    simpa [hout, Y, X] using hout.length_le
  refine ⟨_, ?_, (Wrap.call tensLProg 3 hf.inputAlphabet hf.outputAlphabet 0 none
    (stks (BitEncoding.enc (x, w)) [] [] [] []) (stks W [] [] [] X.reverse) X Y _ t
    (((ones_phase tensLProg (L := 0) (L' := 1) rfl X W [] [] [] none).trans
      ((countMove_run tensLProg (fun b => [b]) (L := 1) (L' := 2) (c := .s₁) (k₁ := .main)
        (k₂ := .s₄) (by decide) (by decide) (by decide) rfl X _ W (some false) (by simp)
        (by rfl)).trans (StepsTo.single (step_some _ _ _ _)))).congr (by simp [tensLProg])
        rfl) rfl hM).trans
    (Wrap.seg _ (((moveMap_run tensLProg (fun _ => true) (L := 3) (L' := 4) (k₁ := .s₄)
      (k₂ := .main) (k₃ := .s₃) (by decide) (by decide) (by decide) rfl _ none).trans
      ((StepsTo.single (step_some _ _ _ _)).trans ((move_run tensLProg (L := 5) (L' := 6)
        (k₁ := .s₃) (k₂ := .main) (by decide) rfl _ none).trans
        (stop_run tensLProg (L := 6) rfl _ none)))).congr
        (by simp [enc_prod, prefixCode_eq, Y, W]) rfl))⟩
  have ht' : t ≤ hf.time.eval (BitEncoding.enc (x, w)).length :=
    le_trans ht (Polynomial.eval_le_eval _ (by simp [enc_prod, length_prefixCode, X]; omega))
  have hX : X.length ≤ (BitEncoding.enc (x, w)).length := by
    simp [enc_prod, length_prefixCode, X]; omega
  have := Nat.mul_le_mul_left hf.tm.maxPushes ht'
  simp
  nlinarith

/-- Swap the two components of a length-delimited encoded pair. -/
def swapProg : Fin 8 → Stmt Stk (Fin 8)
  | 0 => read .main (put .s₁ true (goto' 0)) (goto' 1) (goto' 1)
  | 1 => countMove (fun b => [b]) .s₁ .main .s₂ 1 2
  | 2 => read .main (put .s₃ true (put .s₄ true (goto' 2)))
      (put .s₃ false (put .s₄ true (goto' 2))) (goto' 3)
  | 3 => moveAll (fun b => [b]) .s₂ .main 3 4
  | 4 => moveAll (fun b => [b]) .s₃ .main 4 5
  | 5 => put .main false (goto' 6)
  | 6 => moveAll (fun b => [b]) .s₄ .main 6 7
  | 7 => stop

theorem tm_swap {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α × β))
      (BitEncoding.enc (α := β × α)) (fun p => (p.2, p.1))) := by
  refine computableInPolyTime' (Fin 8) 0 swapProg (linPoly 4 8) fun p => ⟨_, ?_,
    ((ones_phase swapProg (L := 0) (L' := 1) rfl (BitEncoding.enc p.1) (BitEncoding.enc p.2) [] []
      [] none).trans
    ((countMove_phase swapProg (L₁ := 1) (L₂ := 2) rfl _ _ [] [] (some false)).trans
    ((moveMap_run swapProg (fun _ => true) (L := 2) (L' := 3) (k₁ := .main) (k₂ := .s₃)
      (k₃ := .s₄) (by decide) (by decide) (by decide) rfl _ none).trans
    ((move_run swapProg (L := 3) (L' := 4) (k₁ := .s₂) (k₂ := .main) (by decide) rfl _ none).trans
    ((move_run swapProg (L := 4) (L' := 5) (k₁ := .s₃) (k₂ := .main) (by decide) rfl _ none).trans
    ((StepsTo.single (step_some _ _ _ _)).trans
    ((move_run swapProg (L := 6) (L' := 7) (k₁ := .s₄) (k₂ := .main) (by decide) rfl _ none).trans
    (stop_run swapProg (L := 7) rfl _ none)))))))).congr ?_ rfl⟩
  · simp [enc_prod, length_prefixCode]; omega
  · simp [enc_prod, prefixCode_eq]

theorem tm_pair {α β γ : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    [Primcodable γ] [BitEncoding γ] {f : α → β} {g : α → γ}
    (hf : TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := β)) f)
    (hg : TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := γ)) g) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := β × γ))
      (fun a => (f a, g a))) := by
  obtain ⟨h₁⟩ := tm_comp (tm_tensL (δ := α) hf).some (tm_dup (α := α)).some
  obtain ⟨h₂⟩ := tm_comp (tm_swap (α := β) (β := α)).some h₁
  obtain ⟨h₃⟩ := tm_comp (tm_tensL (δ := β) hg).some h₂
  exact tm_comp (tm_swap (α := γ) (β := β)).some h₃

/-! ### Derived: first component, head and tail, `drop`, `cond` -/

theorem tm_fst {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := α × β)) (BitEncoding.enc (α := α))
      (fun p => p.1)) :=
  (tm_comp (tm_snd (α := β) (β := α)).some tm_swap.some :)

theorem tm_headD_tail {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := List α × α))
      (BitEncoding.enc (α := α × List α)) fun p => (p.1.headD p.2, p.1.tail)) := by
  obtain ⟨hu⟩ := tm_prepend (f := fun l : List α => l.head?.map (·, l.tail)) [] fun l => by
    cases l <;> rfl
  obtain ⟨hp⟩ := tm_pair (tm_comp hu (tm_fst (β := α)).some).some
    (tm_pair (tm_snd (α := List α)).some (tm_const (α := List α × α) ([] : List α)).some).some
  exact (funext fun p => by obtain ⟨_ | _, _⟩ := p <;> rfl : (fun p : List α × α =>
    (p.1.head?.map (·, p.1.tail)).getD (p.2, [])) = fun p => (p.1.headD p.2, p.1.tail)) ▸
    (tm_comp tm_getD.some hp :)

theorem tm_headD {α : Type} [Primcodable α] [BitEncoding α] (d : α) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := List α)) (BitEncoding.enc (α := α))
      (fun l => l.headD d)) :=
  (tm_comp (tm_fst (β := List α)).some (tm_comp tm_headD_tail.some
    (tm_pair (idComputableInPolyTime _) (tm_const d).some).some).some :)

theorem tm_tail {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := List α))
      (BitEncoding.enc (α := List α)) List.tail) := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨d⟩⟩
  · exact tm_const_of_subsingleton _ []
  exact (tm_comp (tm_snd (α := α)).some (tm_comp tm_headD_tail.some
    (tm_pair (idComputableInPolyTime _) (tm_const d).some).some).some :)

theorem length_enc_iterate_le {α : Type} [Primcodable α] [BitEncoding α] {g : α → α}
    (hle : ∀ s, (BitEncoding.enc (g s)).length ≤ (BitEncoding.enc s).length) (N : ℕ) (s : α)
    (i : ℕ) (hi : i ≤ N) :
    (BitEncoding.enc (g^[i] s)).length ≤ Polynomial.X.eval (BitEncoding.enc (N, s)).length := by
  rw [Polynomial.eval_X, length_enc_prod]
  induction i with
  | zero => simp only [Function.iterate_zero, id]; omega
  | succ i ih => rw [Function.iterate_succ_apply']; exact (hle _).trans (ih (by omega))

theorem tm_drop {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := ℕ × List α))
      (BitEncoding.enc (α := List α)) (fun p => p.2.drop p.1)) := by
  obtain ⟨h⟩ := tm_tail (α := α)
  refine (funext fun p => List.tail_iterate p.2 p.1 :
    (fun p : ℕ × List α => List.tail^[p.1] p.2) = _) ▸ tm_iterate h Polynomial.X
      (length_enc_iterate_le fun l => ?_)
  cases l with
  | nil => exact le_rfl
  | cons a l => rw [List.tail_cons, length_enc_cons]; omega

theorem tm_cond {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := Bool × α × α))
      (BitEncoding.enc (α := α)) (fun p => bif p.1 then p.2.1 else p.2.2)) := by
  obtain ⟨hn⟩ := tm_comp (tm_getD (α := ℕ)).some (tm_pair (tm_prepend
    (f := fun b : Bool => bif b then some 0 else none) [] fun b => by cases b <;> rfl).some
    (tm_const (α := Bool) 1).some).some
  obtain ⟨hx⟩ := tm_comp (tm_cons (α := α)).some (tm_pair (tm_comp (tm_fst (β := α)).some
    (tm_snd (α := Bool)).some).some (tm_const (α := Bool × α × α) ([] : List α)).some).some
  obtain ⟨hl⟩ := tm_comp (tm_drop (α := α)).some
    (tm_pair (tm_comp hn (tm_fst (β := α × α)).some).some hx).some
  obtain ⟨hh⟩ := tm_comp tm_headD_tail.some
    (tm_pair hl (tm_comp (tm_snd (α := α)).some (tm_snd (α := Bool)).some).some).some
  exact (funext fun p => by obtain ⟨_ | _, _, _⟩ := p <;> rfl : (fun p : Bool × α × α =>
    ([p.2.1].drop ((bif p.1 then some 0 else none).getD 1)).headD p.2.2) =
      fun p => bif p.1 then p.2.1 else p.2.2) ▸ (tm_comp (tm_fst (β := List α)).some hh :)
/-! ### Sums, products and powers of unary numbers: iterated successor, sum, product -/
theorem tm_add :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := ℕ × ℕ)) (BitEncoding.enc (α := ℕ))
      (fun p => p.1 + p.2)) :=
  (funext fun p => by rw [Nat.succ_iterate, Nat.add_comm] :
    (fun p : ℕ × ℕ => Nat.succ^[p.1] p.2) = fun p => p.1 + p.2) ▸
    tm_iterate (tm_prepend (f := Nat.succ) [true] fun _ => rfl).some Polynomial.X fun N n i hi => by
      simp only [Nat.succ_iterate, Polynomial.eval_X, length_enc_prod, length_enc_nat]
      omega

theorem tm_mul : Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := ℕ × ℕ))
    (BitEncoding.enc (α := ℕ)) (fun p => p.1 * p.2)) := by
  have hit : ∀ i n k : ℕ, (fun p : ℕ × ℕ => (p.1, p.1 + p.2))^[i] (n, k) = (n, i * n + k) := by
    intro i n k
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply', ih]; simp only [Prod.mk.injEq]; ring_nf; simp
  obtain ⟨hi⟩ := tm_iterate (tm_pair (tm_fst (α := ℕ) (β := ℕ)).some tm_add.some).some
    (Polynomial.X + Polynomial.X * Polynomial.X) fun N s i hi => by
      obtain ⟨n, k⟩ := s
      have : i * n ≤ (2 * N + 1 + (2 * n + 1 + k)) * (2 * N + 1 + (2 * n + 1 + k)) :=
        Nat.mul_le_mul (by omega) (by omega)
      simp only [hit, length_enc_prod, length_enc_nat, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X]
      omega
  obtain ⟨hin⟩ := tm_pair (tm_fst (α := ℕ) (β := ℕ)).some
    (tm_pair (tm_snd (α := ℕ) (β := ℕ)).some (tm_const (α := ℕ × ℕ) 0).some).some
  refine (funext fun p => ?_ : _ = fun p : ℕ × ℕ => p.1 * p.2) ▸
    tm_comp (tm_snd (α := ℕ) (β := ℕ)).some (tm_comp hi hin).some
  simp [hit]

end BitMachines
end Turing
