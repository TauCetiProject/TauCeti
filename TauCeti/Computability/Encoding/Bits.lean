/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.List
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Computable self-delimiting bit encodings

Natural numbers are unary. Pairs, lists and options carry delimiters, allowing their
components to be extracted by finite-state bit-stack machines. All encodings are injective
and computable; no mathematical value is stored in a single bit-stack symbol.
-/

@[expose] public section

namespace Computability

/-- A **bit encoding** of a type: an injective computable map to bit strings, the inputs and
outputs of machines. The instances on standard types are size-faithful: numbers in unary; pairs,
lists and options self-delimiting. -/
class BitEncoding (α : Type) [Primcodable α] where
  /-- The computable injective bit representation of a value. -/
  enc : α → List Bool
  enc_injective : Function.Injective enc
  enc_computable : Computable enc

theorem computable_iterate {α : Type} [Primcodable α] {g : α → α} (hg : Computable g) :
    Computable (fun p : ℕ × α => g^[p.1] p.2) := by
  refine (Computable.nat_rec Computable.fst Computable.snd
    (hg.comp (Computable.snd.comp Computable.snd)).to₂).of_eq fun p => ?_
  obtain ⟨N, s⟩ := p
  induction N with
  | zero => rfl
  | succ N ih => exact (congrArg g ih).trans (Function.iterate_succ_apply' g N s).symm

theorem primrec_replicate {σ : Type} [Primcodable σ] :
    Primrec₂ (fun (N : ℕ) (s : σ) => List.replicate N s) :=
  (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.snd.comp Primrec.fst).to₂).of_eq
    fun p => by simp

namespace BitEncoding

/-- The self-delimiting code of a bit string `w`: its length in unary, a zero, then `w`. -/
def prefixCode (w : List Bool) : List Bool := List.replicate w.length true ++ false :: w

theorem replicate_true_append_false_inj {m m' : ℕ} {u u' : List Bool}
    (h : List.replicate m true ++ false :: u = List.replicate m' true ++ false :: u') :
    m = m' ∧ u = u' := by
  induction m generalizing m' with
  | zero => cases m' <;> simp_all [List.replicate_succ]
  | succ m ih =>
    cases m' with
    | zero => simp [List.replicate_succ] at h
    | succ m' =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

theorem prefixCode_append_inj {w w' t t' : List Bool}
    (h : prefixCode w ++ t = prefixCode w' ++ t') : w = w' ∧ t = t' := by
  simp only [prefixCode, List.append_assoc, List.cons_append] at h
  obtain ⟨hl, h⟩ := replicate_true_append_false_inj h
  exact List.append_inj h hl

theorem primrec_replicate_true : Primrec (fun n : ℕ => List.replicate n true) :=
  primrec_replicate.comp Primrec.id (Primrec.const true)

theorem primrec_prefixCode : Primrec prefixCode :=
  Primrec.list_append.comp (primrec_replicate_true.comp Primrec.list_length)
    (Primrec.list_cons.comp (Primrec.const false) Primrec.id)

instance nat : BitEncoding ℕ where
  enc n := List.replicate n true
  enc_injective m n h := by simpa using congrArg List.length h
  enc_computable := primrec_replicate_true.to_comp

instance bool : BitEncoding Bool where
  enc b := [b]
  enc_injective a b h := by simpa using h
  enc_computable := (Primrec.list_cons.comp Primrec.id (Primrec.const [])).to_comp

instance unit : BitEncoding Unit where
  enc _ := []
  enc_injective _ _ _ := rfl
  enc_computable := Computable.const []

instance prod {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β] :
    BitEncoding (α × β) where
  enc p := prefixCode (enc p.1) ++ enc p.2
  enc_injective := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨h₁, h₂⟩ := prefixCode_append_inj h
    exact Prod.ext (enc_injective h₁) (enc_injective h₂)
  enc_computable :=
    Computable.list_append.comp
      (primrec_prefixCode.to_comp.comp (enc_computable.comp Computable.fst))
      (enc_computable.comp Computable.snd)

/-- Encode a list with individually length-delimited elements and a final zero marker. -/
def listEnc {α : Type} (e : α → List Bool) (l : List α) : List Bool :=
  l.foldr (fun a acc => true :: (prefixCode (e a) ++ acc)) [false]

theorem listEnc_eq {α : Type} (e : α → List Bool) (l : List α) :
    listEnc e l = ((l.map e).flatMap fun w => true :: prefixCode w) ++ [false] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change true :: (prefixCode (e a) ++ listEnc e l) = _
    rw [ih]
    simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.append_assoc]

instance list {α : Type} [Primcodable α] [BitEncoding α] : BitEncoding (List α) where
  enc := listEnc enc
  enc_injective := by
    intro l
    induction l with
    | nil => rintro (_ | ⟨a, l'⟩) h <;> simp_all [listEnc]
    | cons a l ih =>
      rintro (_ | ⟨a', l'⟩) h
      · simp [listEnc] at h
      · simp only [listEnc, List.foldr_cons, List.cons.injEq, true_and] at h
        obtain ⟨h₁, h₂⟩ := prefixCode_append_inj h
        rw [enc_injective h₁, ih h₂]
  enc_computable := by
    have hframe : Primrec (fun L : List (List Bool) =>
        (L.flatMap fun w => true :: prefixCode w) ++ [false]) :=
      Primrec.list_append.comp
        (Primrec.list_flatMap Primrec.id
          (Primrec.list_cons.comp (Primrec.const true) (primrec_prefixCode.comp Primrec.snd)).to₂)
        (Primrec.const [false])
    exact (hframe.to_comp.comp
      (Computable.list_map Computable.id (enc_computable.comp Computable.snd).to₂)).of_eq fun l =>
      (listEnc_eq enc l).symm

instance option {α : Type} [Primcodable α] [BitEncoding α] : BitEncoding (Option α) where
  enc o := o.elim [false] fun a => true :: enc a
  enc_injective := by
    rintro (_ | a) (_ | a') h <;> simp_all [enc_injective.eq_iff]
  enc_computable :=
    (Computable.option_casesOn Computable.id (Computable.const [false])
      ((Computable.list_cons.comp (Computable.const true)
        (enc_computable.comp Computable.snd)).to₂)).of_eq fun o => by cases o <;> rfl

/-- **The bit encodings**: `n` is `n` ones, a bit is itself, a pair prefixes the code of its first
component with its length in unary, a list marks each element's code with a one and ends with a
zero, and an option is a zero or a one followed by the code. -/
theorem enc_eq {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    (n : ℕ) (b : Bool) (a : α) (x : β) (l : List α) (o : Option α) :
    enc n = List.replicate n true ∧ enc b = [b] ∧ enc () = [] ∧
      enc (a, x) = prefixCode (enc a) ++ enc x ∧
      enc l = ((l.map enc).flatMap fun w => true :: prefixCode w) ++ [false] ∧
      enc o = o.elim [false] (fun a => true :: enc a) :=
  ⟨rfl, rfl, rfl, rfl, listEnc_eq enc l, rfl⟩

end BitEncoding


open BitEncoding

theorem enc_nat (n : ℕ) : enc n = List.replicate n true := rfl

theorem enc_bool (b : Bool) : enc b = [b] := rfl

theorem enc_prod {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    (p : α × β) : enc p = prefixCode (enc p.1) ++ enc p.2 := rfl

theorem enc_some {α : Type} [Primcodable α] [BitEncoding α] (a : α) :
    enc (some a) = true :: enc a := rfl

theorem enc_none {α : Type} [Primcodable α] [BitEncoding α] :
    enc (none : Option α) = [false] := rfl

theorem enc_list {α : Type} [Primcodable α] [BitEncoding α] (l : List α) :
    enc l = listEnc enc l := rfl

theorem length_prefixCode (w : List Bool) : (prefixCode w).length = 2 * w.length + 1 := by
  simp [prefixCode]; omega

theorem length_prefixCode_append_le {a b : List Bool} {s e₁ e₂ : ℕ} (hs : 2 ≤ s)
    (ha : a.length ≤ s ^ e₁) (hb : b.length ≤ s ^ e₂) :
    (prefixCode a ++ b).length ≤ s ^ (e₁ + e₂ + 2) := by
  have h₀ : 1 ≤ s ^ e₁ * s ^ e₂ := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h₁ := Nat.mul_le_mul_left (s ^ e₁) (Nat.one_le_pow e₂ s (by omega))
  have h₂ := Nat.mul_le_mul_right (s ^ e₂) (Nat.one_le_pow e₁ s (by omega))
  rw [List.length_append, length_prefixCode]
  calc 2 * a.length + 1 + b.length ≤ 4 * (s ^ e₁ * s ^ e₂) := by linarith
    _ ≤ s ^ 2 * (s ^ e₁ * s ^ e₂) := Nat.mul_le_mul_right _ (by nlinarith)
    _ = s ^ (e₁ + e₂ + 2) := by ring

theorem prefixCode_eq (w : List Bool) :
    prefixCode w = List.replicate w.length true ++ false :: w := rfl

theorem listEnc_cons {α : Type} (e : α → List Bool) (a : α) (l : List α) :
    listEnc e (a :: l) = true :: (prefixCode (e a) ++ listEnc e l) := rfl

theorem length_le_listEnc {α : Type} (e : α → List Bool) (l : List α) :
    l.length ≤ (listEnc e l).length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [listEnc_cons, length_prefixCode]; omega

variable {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]

theorem length_enc_nat (n : ℕ) : (enc n).length = n := enc_nat n ▸ List.length_replicate

theorem length_enc_prod (a : α) (b : β) :
    (enc (a, b)).length = 2 * (enc a).length + 1 + (enc b).length := by
  rw [enc_prod, List.length_append, length_prefixCode]

theorem length_enc_nil : (enc ([] : List α)).length = 1 := rfl

theorem length_enc_cons (a : α) (l : List α) :
    (enc (a :: l)).length = 2 * (enc a).length + 2 + (enc l).length := by
  rw [enc_list, listEnc_cons, List.length_cons, List.length_append, length_prefixCode, ← enc_list]
  omega

theorem length_enc_append (l l' : List α) :
    (enc (l ++ l')).length + 1 = (enc l).length + (enc l').length := by
  induction l with
  | nil => rw [List.nil_append, length_enc_nil]; omega
  | cons a l ih => rw [List.cons_append, length_enc_cons, length_enc_cons]; omega

theorem length_enc_bits (l : List Bool) : (enc l).length = 4 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [length_enc_cons, ih, enc_bool]
    simp only [List.length_cons, List.length_nil]
    omega

theorem length_le_of_mem_listEnc {α : Type} (e : α → List Bool) {l : List α} {a : α}
    (h : a ∈ l) : (e a).length ≤ (BitEncoding.listEnc e l).length := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    simp only [listEnc_cons, List.length_cons, List.length_append, length_prefixCode]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

theorem length_enc_list_le (l : List α) {B : ℕ} (h : ∀ a ∈ l, (enc a).length ≤ B) :
    (enc l).length ≤ l.length * (2 * B + 2) + 1 := by
  induction l with
  | nil => simp [length_enc_nil]
  | cons a l ih =>
    rw [length_enc_cons, List.length_cons]
    have h₁ := h a (List.mem_cons_self ..)
    have h₂ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    nlinarith

end Computability
