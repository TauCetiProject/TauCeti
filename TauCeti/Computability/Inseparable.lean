/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE
import TauCeti.Computability.Enumeration.Domain

/-!
# Computably inseparable sets

Two disjoint sets `A` and `B` are **computably inseparable** when no computable set separates
them, that is, every computable set containing `A` meets `B`. Neither set of such a pair is
computable, since a computable one would separate itself from the other.

The standard example is given by the diagonal function `e ↦ φ_e(e)`, where `φ_e` is the partial
computable function of the code `Denumerable.ofNat Code e`. For distinct values `b ≠ b'`, the
fibers `{e | φ_e(e) = b}` and `{e | φ_e(e) = b'}` are disjoint c.e. sets, and they are computably
inseparable: if a computable set `C` contained the first and missed the second, the computable
function with value `b'` on `C` and `b` off `C` would have an index `e`, and `e` could lie neither
in `C` nor outside it. The fibers are c.e. uniformly in the value, with a computable map from
values to codes for them.

## Main definitions

* `Set.ComputablyInseparable`: two disjoint sets with no computable set separating them.
* `TauCeti.diagonalFiber`: the set of indices `e` with `φ_e(e) = b`.
* `TauCeti.diagonalFiberCode`: a computable map sending each value `b` to a code whose domain is
  the diagonal fiber over `b`.

## Main results

* `Set.ComputablyInseparable.symm`: computable inseparability is symmetric.
* `Set.ComputablyInseparable.mono`: disjoint supersets of computably inseparable sets are
  computably inseparable.
* `Set.ComputablyInseparable.not_computablePred_left`,
  `Set.ComputablyInseparable.not_computablePred_right`: neither set of a computably inseparable pair
  is computable.
* `TauCeti.computable_diagonalFiberCode`, `TauCeti.dom_eval_diagonalFiberCode_iff`: the diagonal
  fibers are c.e. uniformly in the value, with a computable map from values to codes for them.
* `TauCeti.computablyInseparable_diagonalFiber`: diagonal fibers over distinct values are
  computably inseparable.
* `TauCeti.exists_computablyInseparable_rePred`: there is a pair of computably inseparable c.e.
  sets.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter I.3, exercises
  on computably inseparable sets.
-/

public section

open Nat.Partrec

namespace Set

variable {α : Type*} [Primcodable α] {A A' B B' : Set α}

/-- Two sets `A` and `B` are **computably inseparable** when they are disjoint and no computable
set separates them: every computable set containing `A` meets `B`. -/
structure ComputablyInseparable (A B : Set α) : Prop where
  /-- Computably inseparable sets are disjoint. -/
  disjoint : Disjoint A B
  /-- Every computable set containing the first set meets the second. -/
  inter_nonempty : ∀ C : Set α, ComputablePred (· ∈ C) → A ⊆ C → (C ∩ B).Nonempty

/-- **Computable inseparability is symmetric.** A computable set containing `B` and missing `A`
would have a computable complement containing `A` and missing `B`. -/
theorem ComputablyInseparable.symm (h : A.ComputablyInseparable B) :
    B.ComputablyInseparable A := by
  refine ⟨h.disjoint.symm, fun C hC hBC => ?_⟩
  by_contra hCA
  obtain ⟨x, hxC, hxB⟩ := h.inter_nonempty Cᶜ hC.not fun x hxA hxC =>
    hCA ⟨x, hxC, hxA⟩
  exact hxC (hBC hxB)

/-- Computable inseparability does not depend on the order of the two sets. -/
theorem computablyInseparable_comm :
    A.ComputablyInseparable B ↔ B.ComputablyInseparable A :=
  ⟨.symm, .symm⟩

/-- Disjoint supersets of computably inseparable sets are computably inseparable. -/
theorem ComputablyInseparable.mono (h : A.ComputablyInseparable B) (hA : A ⊆ A') (hB : B ⊆ B')
    (hd : Disjoint A' B') : A'.ComputablyInseparable B' := by
  refine ⟨hd, fun C hC hAC => ?_⟩
  obtain ⟨x, hxC, hxB⟩ := h.inter_nonempty C hC (hA.trans hAC)
  exact ⟨x, hxC, hB hxB⟩

/-- **The first set of a computably inseparable pair is not computable**: otherwise it would
separate itself from the second. -/
theorem ComputablyInseparable.not_computablePred_left (h : A.ComputablyInseparable B) :
    ¬ComputablePred (· ∈ A) := fun hA => by
  obtain ⟨x, hxA, hxB⟩ := h.inter_nonempty A hA subset_rfl
  exact Set.disjoint_left.1 h.disjoint hxA hxB

/-- **The second set of a computably inseparable pair is not computable.** -/
theorem ComputablyInseparable.not_computablePred_right (h : A.ComputablyInseparable B) :
    ¬ComputablePred (· ∈ B) :=
  h.symm.not_computablePred_left

end Set

namespace TauCeti

/-- The fiber over `b` of the diagonal function `e ↦ φ_e(e)`: the set of indices `e` such that
the code `Denumerable.ofNat Code e` halts on the input `e` with output `b`. -/
def diagonalFiber (b : ℕ) : Set ℕ :=
  {e | b ∈ (Denumerable.ofNat Code e).eval e}

@[simp]
theorem mem_diagonalFiber {b e : ℕ} :
    e ∈ diagonalFiber b ↔ b ∈ (Denumerable.ofNat Code e).eval e :=
  Iff.rfl

/-- Diagonal fibers over distinct values are disjoint, since the diagonal function is a partial
function. -/
theorem disjoint_diagonalFiber {b b' : ℕ} (h : b ≠ b') :
    Disjoint (diagonalFiber b) (diagonalFiber b') :=
  Set.disjoint_left.2 fun _ hb hb' => h (Part.mem_unique hb hb')

/-- A computable map `g` sends each value `b` to a code whose domain is the diagonal fiber over
`b`. -/
private theorem exists_computable_dom_eval_iff_mem_diagonalFiber :
    ∃ g : ℕ → Code, Computable g ∧ ∀ b e, ((g b).eval e).Dom ↔ e ∈ diagonalFiber b := by
  -- on the input `⟨b, e⟩`, run `φ_e(e)` and halt with output `0` exactly when it returns `b`
  let F : ℕ →. ℕ := fun n => ((Denumerable.ofNat Code n.unpair.2).eval n.unpair.2).bind
    fun y => cond (y == n.unpair.1) (Part.some 0) Part.none
  have hF : Partrec F := by
    have hu : Primrec fun n : ℕ => n.unpair := Primrec.unpair
    refine Partrec.bind (Code.eval_part.comp
      ((Primrec.ofNat Code).comp (Primrec.snd.comp hu)).to_comp
      (Primrec.snd.comp hu).to_comp) ?_
    exact Partrec.cond (Primrec.beq.comp Primrec.snd
      (Primrec.fst.comp (hu.comp Primrec.fst))).to_comp
      (Partrec.const' _) Partrec.none
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hF)
  refine ⟨Code.curry c, (Code.primrec₂_curry.comp (Primrec.const c) Primrec.id).to_comp,
    fun b e => ?_⟩
  rw [Code.eval_curry, hc, mem_diagonalFiber, Part.dom_iff_mem]
  simp only [F, Nat.unpair_pair, Part.mem_bind_iff]
  constructor
  · rintro ⟨_, y, hy, hb⟩
    cases hyb : y == b <;> simp_all
  · exact fun hb => ⟨0, b, hb, by simp⟩

/-- A **c.e. index of the diagonal fiber** over `b`: a code whose domain is the set of indices `e`
with `φ_e(e) = b`. It depends computably on `b`. -/
noncomputable def diagonalFiberCode : ℕ → Code :=
  exists_computable_dom_eval_iff_mem_diagonalFiber.choose

/-- **The diagonal fibers are uniformly c.e.**: the code of the diagonal fiber over `b` is
computable in `b`. -/
theorem computable_diagonalFiberCode : Computable diagonalFiberCode :=
  exists_computable_dom_eval_iff_mem_diagonalFiber.choose_spec.1

/-- The code `diagonalFiberCode b` halts on the input `e` exactly when `e` lies in the diagonal
fiber over `b`. -/
theorem dom_eval_diagonalFiberCode_iff {b e : ℕ} :
    ((diagonalFiberCode b).eval e).Dom ↔ e ∈ diagonalFiber b :=
  exists_computable_dom_eval_iff_mem_diagonalFiber.choose_spec.2 b e

/-- Each diagonal fiber is c.e. -/
theorem rePred_mem_diagonalFiber (b : ℕ) : REPred (· ∈ diagonalFiber b) :=
  (diagonalFiberCode b).rePred_dom_eval.of_eq fun _ => dom_eval_diagonalFiberCode_iff

/-- **Diagonal fibers over distinct values are computably inseparable.** If a computable set `C`
contained the fiber over `b` and missed the fiber over `b'`, the computable function with value
`b'` on `C` and `b` off `C` would be `φ_e` for some index `e`; then `e ∈ C` would put `e` in the
fiber over `b'`, and `e ∉ C` would put `e` in the fiber over `b`. -/
theorem computablyInseparable_diagonalFiber {b b' : ℕ} (h : b ≠ b') :
    (diagonalFiber b).ComputablyInseparable (diagonalFiber b') := by
  refine ⟨disjoint_diagonalFiber h, fun C hC hbC => ?_⟩
  obtain ⟨_, hC⟩ := hC
  -- an index `e` of the computable function with value `b'` on `C` and `b` off `C`
  obtain ⟨c, hc⟩ := Code.exists_code.1 <| Partrec.nat_iff.1
    (Computable.cond hC (Computable.const b') (Computable.const b)).partrec
  have he : c.eval (Encodable.encode c) =
      Part.some (cond (decide (Encodable.encode c ∈ C)) b' b) := by
    rw [hc, PFun.coe_val]
  by_cases hmem : Encodable.encode c ∈ C
  · refine ⟨Encodable.encode c, hmem, ?_⟩
    simp [he, hmem]
  · exact absurd (hbC (by simp [he, hmem])) hmem

/-- **There is a pair of computably inseparable c.e. sets**, for instance the diagonal fibers over
`0` and `1`. -/
theorem exists_computablyInseparable_rePred :
    ∃ A B : Set ℕ, REPred (· ∈ A) ∧ REPred (· ∈ B) ∧ A.ComputablyInseparable B :=
  ⟨_, _, rePred_mem_diagonalFiber 0, rePred_mem_diagonalFiber 1,
    computablyInseparable_diagonalFiber zero_ne_one⟩

end TauCeti
