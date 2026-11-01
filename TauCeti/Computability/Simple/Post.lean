/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Simple.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Post's simple set

Post's construction of a simple set. For each index `e`, the positive requirement `P_e` asks that
the set meet `W_e`, the domain of the code `Denumerable.ofNat Code e`, whenever `W_e` is infinite.
The partial computable function `postWitness` satisfies it with the first element of `W_e`
greater than `2 * e` in a computable enumeration of `W_e`, read along the stage/element pairs
`Nat.pair s x` with `x` found in `W_e` within `s` steps. Post's set `postSimpleSet` is the range of
`postWitness`.

Each requirement contributes at most one element, and the witness bound `x > 2 * e` keeps the
contributions sparse: the **counting invariant** `|A ∩ [0, 2n]| ≤ n` holds, since only the
requirements `e < n` can contribute below `2n`. This leaves a coinfinite reservoir, so the set is
simple; in particular it is c.e. but not computable.

## Main definitions

* `TauCeti.postWitness`: the partial computable witness for the requirement `P_e`.
* `TauCeti.postSimpleSet`: Post's simple set, the range of `postWitness`.

## Main results

* `TauCeti.partrec_postWitness`: the witness function is partial computable.
* `TauCeti.postWitness_dom_iff`: the requirement `P_e` receives a witness exactly when `W_e` has an
  element greater than `2 * e`.
* `TauCeti.ncard_postSimpleSet_inter_Iic_le`: the counting invariant.
* `TauCeti.simple_postSimpleSet`: Post's set is simple.

## References

* E. L. Post, *Recursively enumerable sets of positive integers and their decision problems*,
  Bull. Amer. Math. Soc. 50 (1944), 284–316.
* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Theorem V.1.3.
-/

public section

open Nat.Partrec Nat.Partrec.Code

namespace TauCeti

/-- The search condition for the requirement `P_e`: the element `x` of the stage/element pair
`n = Nat.pair s x` exceeds `2 * e`, and the code `Denumerable.ofNat Code e` halts on `x` within `s`
steps. -/
private def postSearch (e n : ℕ) : Bool :=
  2 * e < n.unpair.2 && (evaln n.unpair.1 (Denumerable.ofNat Code e) n.unpair.2).isSome

private theorem postSearch_eq_true {e n : ℕ} :
    postSearch e n = true ↔
      2 * e < n.unpair.2 ∧ (evaln n.unpair.1 (Denumerable.ofNat Code e) n.unpair.2).isSome := by
  simp [postSearch]

/-- The witness for Post's requirement `P_e`: the first element greater than `2 * e` in the
enumeration of `W_e`, the domain of `Denumerable.ofNat Code e`, along the stage/element pairs
`Nat.pair s x`. It is undefined when `W_e` has no element greater than `2 * e`. -/
def postWitness : ℕ →. ℕ := fun e =>
  (Nat.rfind fun n => Part.some (postSearch e n)).map fun n => n.unpair.2

/-- The witness function is partial computable. -/
theorem partrec_postWitness : Partrec postWitness := by
  have hs : Primrec₂ postSearch :=
    Primrec.and.comp
      (Primrec.nat_lt.decide.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
      (Primrec.option_isSome.comp (primrec_evaln.comp
        ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
          ((Primrec.ofNat Code).comp Primrec.fst) |>.pair
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))))
  exact (Partrec.rfind hs.to_comp.partrec₂).map
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp.to₂

/-- **Witness specification.** A witness for `P_e` exceeds `2 * e` and lies in `W_e`. -/
theorem postWitness_spec {e x : ℕ} (h : x ∈ postWitness e) :
    2 * e < x ∧ ((Denumerable.ofNat Code e).eval x).Dom := by
  obtain ⟨n, hn, rfl⟩ := Part.mem_map_iff _ |>.1 h
  obtain ⟨hlt, hsome⟩ := postSearch_eq_true.1 (Part.mem_some_iff.1 (Nat.mem_rfind.1 hn).1).symm
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  exact ⟨hlt, Part.dom_iff_mem.2 ⟨y, evaln_sound hy⟩⟩

/-- **The requirement `P_e` receives a witness** exactly when `W_e`, the domain of
`Denumerable.ofNat Code e`, has an element greater than `2 * e`. -/
theorem postWitness_dom_iff {e : ℕ} :
    (postWitness e).Dom ↔ ∃ x, 2 * e < x ∧ ((Denumerable.ofNat Code e).eval x).Dom := by
  refine ⟨fun h => ⟨_, postWitness_spec (Part.get_mem h)⟩, ?_⟩
  rintro ⟨x, hx, hdom⟩
  -- a halting computation on `x` is found within some number `s` of steps
  obtain ⟨s, hs⟩ := evaln_complete.1 (Part.get_mem hdom)
  refine Part.dom_iff_mem.2 ⟨_, Part.mem_map _ (Part.get_mem (Nat.rfind_dom'.2
    ⟨Nat.pair s x, Part.mem_some_iff.2 ?_, fun _ => trivial⟩))⟩
  rw [eq_comm, postSearch_eq_true, Nat.unpair_pair]
  exact ⟨hx, Option.isSome_iff_exists.2 ⟨_, hs⟩⟩

/-- **Post's simple set**: the range of the witness function `postWitness`. -/
def postSimpleSet : Set ℕ :=
  {x | ∃ e, x ∈ postWitness e}

/-- Membership in Post's set: being the witness of some requirement. -/
@[simp]
theorem mem_postSimpleSet {x : ℕ} : x ∈ postSimpleSet ↔ ∃ e, x ∈ postWitness e :=
  Iff.rfl

/-- Post's set is c.e. -/
theorem rePred_mem_postSimpleSet : REPred (· ∈ postSimpleSet) := by
  -- search for an index `e` and a number of steps `k` after which `postWitness e` outputs `x`
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 partrec_postWitness)
  have hsearch : Primrec₂ fun (x m : ℕ) => decide (evaln m.unpair.1 c m.unpair.2 = some x) :=
    Primrec.eq.decide.comp (primrec_evaln.comp
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair (Primrec.const c) |>.pair
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      (Primrec.option_some.comp Primrec.fst)
  refine (Partrec.rfind hsearch.to_comp.partrec₂).dom_re.of_eq fun x => ?_
  simp only [PFun.coe_val, Nat.rfind_dom', Part.mem_some_iff, Part.some_dom, implies_true,
    and_true, mem_postSimpleSet, ← hc, evaln_complete, eq_comm (a := true), decide_eq_true_eq]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨_, _, hm⟩
  · rintro ⟨e, k, hk⟩
    exact ⟨Nat.pair k e, by rwa [Nat.unpair_pair]⟩

/-- **The counting invariant.** Post's set has at most `n` elements up to `2 * n`: an element up
to `2 * n` is the witness of a requirement `e < n`, and each requirement has at most one
witness. -/
theorem ncard_postSimpleSet_inter_Iic_le (n : ℕ) :
    (postSimpleSet ∩ Set.Iic (2 * n)).ncard ≤ n := by
  classical
  -- the witness of `e`, or `0` when there is none
  let w : ℕ → ℕ := fun e => if h : (postWitness e).Dom then (postWitness e).get h else 0
  have hsub : postSimpleSet ∩ Set.Iic (2 * n) ⊆ ((Finset.range n).image w : Set ℕ) := by
    rintro x ⟨⟨e, hx⟩, hxn⟩
    have he : e < n := by
      have := (postWitness_spec hx).1
      simp only [Set.mem_Iic] at hxn
      omega
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨e, Finset.mem_range.2 he, ?_⟩)
    simp [w, Part.dom_iff_mem.2 ⟨x, hx⟩, Part.get_eq_of_mem hx]
  calc (postSimpleSet ∩ Set.Iic (2 * n)).ncard
      ≤ (((Finset.range n).image w : Finset ℕ) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ n := by
        rw [Set.ncard_coe_finset]
        exact Finset.card_image_le.trans (Finset.card_range n).le

/-- The complement of Post's set is infinite. -/
theorem infinite_compl_postSimpleSet : postSimpleSetᶜ.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨N, hN⟩ => ?_
  -- every number above `N` lies in the set, which overfills the interval `[0, 2(N + 1)]`
  have hsub : (Finset.Icc (N + 1) (2 * (N + 1)) : Set ℕ) ⊆
      postSimpleSet ∩ Set.Iic (2 * (N + 1)) := by
    intro x hx
    rw [Finset.coe_Icc, Set.mem_Icc] at hx
    refine ⟨by_contra fun hxA => ?_, hx.2⟩
    have := hN hxA
    omega
  have := (Set.ncard_le_ncard hsub ((Set.finite_Iic _).inter_of_right _)).trans
    (ncard_postSimpleSet_inter_Iic_le (N + 1))
  rw [Set.ncard_coe_finset, Nat.card_Icc] at this
  omega

/-- **Post's requirements are met**: Post's set meets the domain of every code whose domain is
infinite. -/
theorem inter_postSimpleSet_nonempty {c : Code} (hc : {x | (c.eval x).Dom}.Infinite) :
    ({x | (c.eval x).Dom} ∩ postSimpleSet).Nonempty := by
  obtain ⟨x, hxc, hx⟩ := hc.exists_gt (2 * Encodable.encode c)
  have hdom : (postWitness (Encodable.encode c)).Dom :=
    postWitness_dom_iff.2 ⟨x, hx, by rwa [Denumerable.ofNat_encode]⟩
  have hspec := postWitness_spec (Part.get_mem hdom)
  rw [Denumerable.ofNat_encode] at hspec
  exact ⟨_, hspec.2, _, Part.get_mem hdom⟩

/-- **Post's set is simple.** -/
theorem simple_postSimpleSet : postSimpleSet.Simple :=
  Set.simple_iff_forall_code.2
    ⟨rePred_mem_postSimpleSet, infinite_compl_postSimpleSet, fun _ => inter_postSimpleSet_nonempty⟩

end TauCeti
