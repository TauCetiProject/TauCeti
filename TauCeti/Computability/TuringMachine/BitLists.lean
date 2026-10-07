/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Computability.TuringMachine.BitCombinators
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial-time list operations on bit-stack machines

Reversal, mapping, taking a prefix and appending lists are implemented by bounded calls
to concrete machines. An encoded-size invariant bounds every intermediate list.
-/

@[expose] public section

namespace Turing
namespace BitMachines

open Computability

theorem exists_eval_le_pow (p : Polynomial ℕ) : ∃ d, ∀ n, p.eval n ≤ (n + 2) ^ d := by
  refine ⟨p.eval 1 + p.natDegree, fun n => ?_⟩
  have h1 : p.eval n ≤ p.eval 1 * (n + 2) ^ p.natDegree := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [one_pow, mul_one]
    refine Nat.mul_le_mul_left _ ?_
    exact le_trans (Nat.pow_le_pow_left (by omega) i)
      (Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
  have h2 : p.eval 1 ≤ (n + 2) ^ p.eval 1 :=
    le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_left (by omega) _)
  calc p.eval n ≤ p.eval 1 * (n + 2) ^ p.natDegree := h1
    _ ≤ (n + 2) ^ p.eval 1 * (n + 2) ^ p.natDegree := Nat.mul_le_mul_right _ h2
    _ = (n + 2) ^ (p.eval 1 + p.natDegree) := (pow_add _ _ _).symm

/-- A polynomial-time machine has polynomially bounded encoded output length. -/
theorem length_enc_le_of_tm {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β]
    [BitEncoding β] {f : α → β}
    (h : TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := β)) f) :
    ∃ c, ∀ a, (BitEncoding.enc (f a)).length ≤ ((BitEncoding.enc a).length + 2) ^ c := by
  obtain ⟨c, hc⟩ := exists_eval_le_pow (Polynomial.X + Polynomial.C h.tm.maxPushes * h.time)
  refine ⟨c, fun a ↦ (h.length_le a).trans ?_⟩
  simpa using hc (BitEncoding.enc a).length

theorem tm_revMap₂ {α β γ : Type} [Primcodable α] [BitEncoding α] [Primcodable β]
    [BitEncoding β] [Primcodable γ] [BitEncoding γ] {f : γ × α → β}
    (hf : TM2ComputableInPolyTime (BitEncoding.enc (α := γ × α)) (BitEncoding.enc (α := β)) f)
    (d : α) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := ℕ × γ × List β × List α))
      (BitEncoding.enc (α := γ × List β × List α)) fun p => (p.2.1,
        ((p.2.2.2.take p.1).map fun x => f (p.2.1, x)).reverse ++ p.2.2.1, p.2.2.2.drop p.1)) := by
  let step : γ × List β × List α → γ × List β × List α := fun q =>
    (q.1, bif decide (q.2.2.length = 0) then q.2.1 else f (q.1, q.2.2.headD d) :: q.2.1,
      q.2.2.tail)
  have hit : ∀ i a acc rest, step^[i] (a, acc, rest) =
      (a, ((rest.take i).map fun x => f (a, x)).reverse ++ acc, rest.drop i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rintro a acc (_ | ⟨x, r⟩)
      · simpa [step] using ih a acc []
      · simpa [step] using ih a (f (a, x) :: acc) r
  obtain ⟨hs⟩ : Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := γ × List β × List α))
      (BitEncoding.enc (α := γ × List β × List α)) step) := by
    have ha := (tm_fst (α := γ) (β := List β × List α)).some
    have hq := (tm_snd (α := γ) (β := List β × List α)).some
    obtain ⟨hacc⟩ := tm_comp (tm_fst (α := List β) (β := List α)).some hq
    obtain ⟨hr⟩ := tm_comp (tm_snd (α := List β) (β := List α)).some hq
    obtain ⟨hl⟩ := tm_comp (tm_length (α := α)).some hr
    obtain ⟨hb⟩ := tm_comp (tm_beq (α := ℕ)).some (tm_pair hl (tm_const 0).some).some
    obtain ⟨hh⟩ := tm_comp hf (tm_pair ha (tm_comp (tm_headD d).some hr).some).some
    obtain ⟨hy⟩ := tm_comp (tm_cons (α := β)).some (tm_pair hh hacc).some
    obtain ⟨hc⟩ := tm_comp (tm_cond (α := List β)).some (tm_pair hb (tm_pair hacc hy).some).some
    exact tm_pair ha (tm_pair hc (tm_comp (tm_tail (α := α)).some hr).some).some
  obtain ⟨c, hc⟩ := length_enc_le_of_tm hf
  refine (funext fun p => hit p.1 p.2.1 p.2.2.1 p.2.2.2 :
    (fun p : ℕ × γ × List β × List α => step^[p.1] p.2) = _) ▸ tm_iterate hs
    (Polynomial.C 4 * (Polynomial.X * (Polynomial.C 2 * (Polynomial.X + Polynomial.C 2) ^ c +
      Polynomial.C 2)) + Polynomial.C 8) fun N q i _ => ?_
  obtain ⟨a, acc, rest⟩ := q
  have hn := length_enc_prod N (a, acc, rest)
  rw [length_enc_nat, length_enc_prod a, length_enc_prod acc] at hn
  rw [hit, length_enc_prod, length_enc_prod]
  set n := (BitEncoding.enc (N, a, acc, rest)).length
  set ys := ((rest.take i).map fun x => f (a, x)).reverse
  have h₁ := length_enc_append ys acc
  have h₂ := length_enc_append (rest.take i) (rest.drop i)
  rw [List.take_append_drop] at h₂
  have hr : rest.length ≤ (BitEncoding.enc rest).length := length_le_listEnc _ rest
  have h₃ := length_enc_list_le ys (B := (n + 2) ^ c) fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hy)
    have : (BitEncoding.enc x).length ≤ (BitEncoding.enc rest).length :=
      length_le_of_mem_listEnc _ (List.mem_of_mem_take hx)
    exact (hc (a, x)).trans (Nat.pow_le_pow_left (by rw [length_enc_prod]; omega) c)
  have h₄ := Nat.mul_le_mul_right (2 * (n + 2) ^ c + 2) (show ys.length ≤ n by
    simp only [ys, List.length_reverse, List.length_map, List.length_take]; omega)
  have h₅ : n ≤ n * (2 * (n + 2) ^ c + 2) := Nat.le_mul_of_pos_right _ (by omega)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  omega

theorem tm_revMap {α β : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    {f : α → β}
    (hf : TM2ComputableInPolyTime (BitEncoding.enc (α := α)) (BitEncoding.enc (α := β)) f)
    (d : α) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := ℕ × (List β × List α)))
      (BitEncoding.enc (α := List β × List α))
      fun p => (((p.2.2.take p.1).map f).reverse ++ p.2.1, p.2.2.drop p.1)) :=
  (tm_comp (tm_snd (α := Unit)).some (tm_comp (tm_revMap₂ (tm_comp hf
    (tm_snd (α := Unit)).some).some d).some (tm_pair (tm_fst (β := List β × List α)).some
      (tm_pair (tm_const ()).some (tm_snd (α := ℕ)).some).some).some).some :)

theorem tm_reverse {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := List α))
      (BitEncoding.enc (α := List α)) List.reverse) := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨d⟩⟩
  · exact tm_const_of_subsingleton _ []
  refine (funext fun l => by simp : (fun l : List α =>
    (((l.take l.length).map id).reverse ++ [], l.drop l.length).1) = List.reverse) ▸
    tm_comp (tm_fst (α := List α) (β := List α)).some (tm_comp (tm_revMap
      (idComputableInPolyTime BitEncoding.enc) d).some (tm_pair (tm_length (α := α)).some
        (tm_pair (tm_const []).some (idComputableInPolyTime BitEncoding.enc)).some).some).some

theorem tm_map₂ {α β γ : Type} [Primcodable α] [BitEncoding α] [Primcodable β] [BitEncoding β]
    [Primcodable γ] [BitEncoding γ] {f : γ × α → β}
    (hf : TM2ComputableInPolyTime (BitEncoding.enc (α := γ × α)) (BitEncoding.enc (α := β)) f) :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := γ × List α))
      (BitEncoding.enc (α := List β)) fun p => p.2.map fun x => f (p.1, x)) := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨d⟩⟩
  · exact (funext fun p => by rw [Subsingleton.elim p.2 []]; rfl :
      (fun _ => ([] : List β)) = fun p : γ × List α => p.2.map fun x => f (p.1, x)) ▸ tm_const []
  obtain ⟨hr⟩ := tm_comp (tm_revMap₂ hf d).some (tm_pair (tm_comp (tm_length (α := α)).some
    (tm_snd (α := γ)).some).some (tm_pair (tm_fst (β := List α)).some (tm_pair
      (tm_const (α := γ × List α) ([] : List β)).some (tm_snd (α := γ)).some).some).some).some
  exact (funext fun p => by simp : (fun p : γ × List α => ((((p.2.take p.2.length).map fun x =>
    f (p.1, x)).reverse ++ []).reverse)) = fun p => p.2.map fun x => f (p.1, x)) ▸
    (tm_comp (tm_reverse (α := β)).some (tm_comp (tm_fst (β := List α)).some
      (tm_comp (tm_snd (α := γ)).some hr).some).some :)

theorem tm_take {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := ℕ × List α))
      (BitEncoding.enc (α := List α)) (fun p => p.2.take p.1)) := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨d⟩⟩
  · exact tm_const_of_subsingleton _ []
  refine (funext fun p => by simp : (fun p : ℕ × List α =>
    ((((p.2.take p.1).map id).reverse ++ [], p.2.drop p.1).1).reverse) =
      fun p => p.2.take p.1) ▸
    tm_comp (tm_reverse (α := α)).some (tm_comp (tm_fst (α := List α) (β := List α)).some
      (tm_comp (tm_revMap (idComputableInPolyTime BitEncoding.enc) d).some (tm_pair
        (tm_fst (α := ℕ) (β := List α)).some (tm_pair (tm_const []).some
          (tm_snd (α := ℕ) (β := List α)).some).some).some).some).some

theorem tm_append {α : Type} [Primcodable α] [BitEncoding α] :
    Nonempty (TM2ComputableInPolyTime (BitEncoding.enc (α := List α × List α))
      (BitEncoding.enc (α := List α)) (fun p => p.1 ++ p.2)) := by
  rcases isEmpty_or_nonempty α with hα | ⟨⟨d⟩⟩
  · exact tm_const_of_subsingleton _ []
  have hfst := (tm_fst (α := List α) (β := List α)).some
  refine (funext fun p => by simp [List.take_of_length_le] : (fun p : List α × List α =>
    (((p.1.reverse.take p.1.length).map id).reverse ++ p.2, p.1.reverse.drop p.1.length).1) =
      fun p => p.1 ++ p.2) ▸
    tm_comp hfst (tm_comp (tm_revMap (idComputableInPolyTime BitEncoding.enc) d).some (tm_pair
      (tm_comp (tm_length (α := α)).some hfst).some (tm_pair (tm_snd (α := List α)
        (β := List α)).some (tm_comp (tm_reverse (α := α)).some hfst).some).some).some).some

end BitMachines
end Turing
