/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import TauCeti.Combinatorics.Network.AugmentingPath
public import TauCeti.Data.Rat.ZMultiples

/-!
# Termination of augmentation for capacities in a cyclic subgroup

Let the capacities of an arrow family lie in the cyclic subgroup `zmultiples d` of a linearly
ordered additive commutative group, for some `0 < d`, and let `s ≠ t`. A flow whose arrow values
lie in `zmultiples d` has value `n • d` for a natural number `n`, and by weak duality this value
is at most the total capacity leaving `s`, itself a multiple of `d`. Residual capacities, and
hence bottlenecks, also lie in `zmultiples d`, so an augmentation step keeps the arrow values in
`zmultiples d` and raises the value by a positive multiple of `d`, so by at least `d`. The values
therefore range over finitely many multiples of `d`, and every sequence of augmentation steps
terminates, whatever augmenting walks are chosen. Since a flow admits an augmentation step exactly
when it is not maximum, augmentation from the zero flow ends at a maximum flow with arrow values
in `zmultiples d`, whose value equals the capacity of some cut.

No Archimedean, completeness, or discreteness assumption on the coefficients is needed. Integer
capacities are the case `d = 1`, where every flow has arrow values in `zmultiples 1`; finitely
many rational capacities lie in `zmultiples (1 / D)` for a common denominator `D`. Outside a cyclic
subgroup, augmentation sequences need not terminate.

## Main results

* `TauCeti.Flow.AugmentsTo.val_add_le`: an augmentation step raises the value by at least `d`.
* `TauCeti.Flow.wellFounded_val_lt`: the relation of having larger value is well-founded on flows
  with values in `zmultiples d`.
* `TauCeti.Flow.acc_augmentsTo`: every sequence of augmentation steps from a flow with values in
  `zmultiples d` is finite.
* `TauCeti.Flow.exists_reflTransGen_augmentsTo_isMaximum`: finitely many augmentation steps reach
  a maximum flow.
* `TauCeti.Flow.exists_val_eq_arrowSum_of_mem_zmultiples`: max-flow/min-cut, with a maximum flow
  whose arrow values lie in `zmultiples d`.
* `TauCeti.Flow.acc_augmentsTo_int`, `TauCeti.Flow.exists_isMaximum_int`,
  `TauCeti.Flow.acc_augmentsTo_rat` and `TauCeti.Flow.exists_isMaximum_rat`: the integer and
  rational cases.

## References

* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canadian J. Math. 8 (1956).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 10.4 (termination of the Ford–Fulkerson method for integer and rational capacities).
-/

public section

namespace TauCeti

open Finset AddSubgroup

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

variable [Fintype V] [∀ v w, Fintype (Q v w)]

namespace Flow

section LinearOrder

variable [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K] {cap : Assignment Q K} {s t : V}
  {d : K}

/-- For capacities in `zmultiples d`, an augmentation step between distinct terminals from a flow
with arrow values in `zmultiples d` raises the value by at least `d`. -/
theorem AugmentsTo.val_add_le (hst : s ≠ t) (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ zmultiples d)
    {f g : Flow cap s t} (h : f.AugmentsTo g)
    (hf : ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d) : f.val + d ≤ g.val := by
  obtain ⟨p, hp, hne, hpos, rfl⟩ := augmentsTo_iff.1 h
  rw [val_augmentBottleneck hst]
  gcongr
  have hb : 0 < p.bottleneck (residualCapacity 0 cap f.toFun) hne :=
    ArrowWalk.lt_bottleneck_iff.2 hpos
  obtain ⟨k, hk⟩ := mem_zmultiples_iff.1 <| bottleneck_residualCapacity_mem (hne := hne) hcap hf
  rw [← hk] at hb ⊢
  rcases le_or_gt d 0 with hd | hd
  · exact hd.trans hb.le
  · have hk₀ : 0 < k := (zsmul_lt_zsmul_iff_left hd).1 (by simpa using hb)
    simpa using (zsmul_le_zsmul_iff_left hd).2 (by omega : (1 : ℤ) ≤ k)

/-- For capacities in `zmultiples d` with `0 < d` and distinct terminals, the relation of having
larger value, `f.val < g.val`, is well-founded on the flows with arrow values in `zmultiples d`:
their values are among the finitely many multiples `n • d` between zero and the total capacity
leaving the source. So there is no infinite sequence of such flows of strictly increasing value. -/
theorem wellFounded_val_lt (hst : s ≠ t) (hd : 0 < d)
    (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ zmultiples d) :
    WellFounded fun g f : {f : Flow cap s t // ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d} ↦
      f.1.val < g.1.val := by
  classical
  obtain ⟨m, hm⟩ := mem_zmultiples_iff.1 (arrowSum_mem hcap {s} {s}ᶜ)
  choose n hn using fun f : {f : Flow cap s t // ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d} ↦
    exists_nsmul_eq_val hd f.2
  have hnm (f : {f : Flow cap s t // ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d}) :
      (n f : ℤ) ≤ m := by
    refine (zsmul_le_zsmul_iff_left hd).1 ?_
    rw [natCast_zsmul, hn, hm]
    exact f.1.val_le_arrowSum (mem_singleton_self s) (by simpa using hst.symm)
  refine Subrelation.wf (fun {g f} h ↦ ?_)
    (InvImage.wf (fun f ↦ (m - n f).toNat) wellFounded_lt)
  have hlt : n f < n g := (nsmul_lt_nsmul_iff_left hd).1 (by rwa [hn, hn])
  have := hnm g
  exact (by omega : (m - n g).toNat < (m - n f).toNat)

/-- **Termination of augmentation for capacities in a cyclic subgroup.** For capacities in
`zmultiples d` with `0 < d` and distinct terminals, every sequence of augmentation steps starting
from a flow with arrow values in `zmultiples d` is finite, whatever augmenting walks are chosen. -/
theorem acc_augmentsTo (hst : s ≠ t) (hd : 0 < d)
    (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ zmultiples d) {f : Flow cap s t}
    (hf : ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d) :
    Acc (fun g f : Flow cap s t ↦ f.AugmentsTo g) f := by
  suffices ∀ f : {f : Flow cap s t // ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d},
      Acc (fun g f : Flow cap s t ↦ f.AugmentsTo g) f.1 from this ⟨f, hf⟩
  intro f
  induction f using (wellFounded_val_lt hst hd hcap).induction with
  | _ f ih => exact ⟨_, fun g hg ↦ ih ⟨g, fun _ _ ↦ hg.mem hcap f.2⟩ (hg.val_lt hst)⟩

/-- For capacities in `zmultiples d` with `0 < d` and distinct terminals, finitely many
augmentation steps lead from a flow with arrow values in `zmultiples d` to a maximum flow, again
with arrow values in `zmultiples d`. -/
theorem exists_reflTransGen_augmentsTo_isMaximum (hst : s ≠ t) (hd : 0 < d)
    (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ zmultiples d) {f : Flow cap s t}
    (hf : ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d) :
    ∃ g, Relation.ReflTransGen AugmentsTo f g ∧ g.IsMaximum ∧
      ∀ ⦃v w⦄ (e : Q v w), g.toFun e ∈ zmultiples d := by
  induction acc_augmentsTo hst hd hcap hf with
  | intro f _ ih =>
    by_cases hmax : f.IsMaximum
    · exact ⟨f, .refl, hmax, hf⟩
    · obtain ⟨g, hg⟩ := not_forall_not.1 (mt (isMaximum_iff_forall_not_augmentsTo hst f).2 hmax)
      obtain ⟨g', hg', hmax', hmem⟩ := ih g hg fun _ _ ↦ hg.mem hcap hf
      exact ⟨g', .head hg hg', hmax', hmem⟩

/-- For nonnegative capacities in `zmultiples d` with `0 < d` and distinct terminals, some maximum
flow has all its arrow values in `zmultiples d`. -/
theorem exists_isMaximum_of_mem_zmultiples (hst : s ≠ t) (hd : 0 < d) (hcap₀ : 0 ≤ cap)
    (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ zmultiples d) :
    ∃ f : Flow cap s t, f.IsMaximum ∧ ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d := by
  obtain ⟨f, -, hf⟩ :=
    exists_reflTransGen_augmentsTo_isMaximum hst hd hcap (f := zero hcap₀)
      fun _ _ _ ↦ by simp
  exact ⟨f, hf⟩

/-- **Max-flow/min-cut for capacities in a cyclic subgroup.** For nonnegative capacities in
`zmultiples d` with `0 < d` and distinct terminals, some flow with arrow values in `zmultiples d`
has value equal to the capacity of the arrows leaving some vertex set containing `s` but not `t`.
By weak duality this flow is maximum and this cut is minimum. -/
theorem exists_val_eq_arrowSum_of_mem_zmultiples [DecidableEq V] (hst : s ≠ t) (hd : 0 < d)
    (hcap₀ : 0 ≤ cap) (hcap : ∀ ⦃v w⦄ (e : Q v w), cap e ∈ zmultiples d) :
    ∃ f : Flow cap s t, (∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples d) ∧
      ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ f.val = arrowSum cap S Sᶜ := by
  obtain ⟨f, hmax, hf⟩ := exists_isMaximum_of_mem_zmultiples hst hd hcap₀ hcap
  exact ⟨f, hf, hmax.exists_val_eq_arrowSum hst⟩

end LinearOrder

/-! ### Integer and rational capacities -/

section Int

variable {cap : Assignment Q ℤ} {s t : V}

/-- For integer capacities and distinct terminals, the relation of having larger value,
`f.val < g.val`, is well-founded on ordinary flows. -/
theorem wellFounded_val_lt_int (hst : s ≠ t) :
    WellFounded fun g f : Flow cap s t ↦ f.val < g.val :=
  InvImage.wf (fun f ↦ (⟨f, fun _ _ _ ↦ by simp⟩ :
    {f : Flow cap s t // ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ zmultiples (1 : ℤ)}))
    (wellFounded_val_lt hst one_pos fun _ _ _ ↦ by simp)

/-- For integer capacities and distinct terminals, every sequence of augmentation steps is
finite. -/
theorem acc_augmentsTo_int (hst : s ≠ t) (f : Flow cap s t) :
    Acc (fun g f : Flow cap s t ↦ f.AugmentsTo g) f :=
  acc_augmentsTo hst one_pos (fun _ _ _ ↦ by simp) fun _ _ _ ↦ by simp

/-- For nonnegative integer capacities and distinct terminals, a maximum flow exists. -/
theorem exists_isMaximum_int (hst : s ≠ t) (hcap₀ : 0 ≤ cap) : ∃ f : Flow cap s t, f.IsMaximum :=
  (exists_isMaximum_of_mem_zmultiples hst one_pos hcap₀ fun _ _ _ ↦ by simp).imp fun _ ↦ And.left

end Int

section Rat

variable {cap : Assignment Q ℚ} {s t : V}

/-- For rational capacities and distinct terminals, every sequence of augmentation steps is
finite: the capacities and the arrow values of the initial flow lie in `zmultiples (1 / D)` for a
common denominator `D`. -/
theorem acc_augmentsTo_rat (hst : s ≠ t) (f : Flow cap s t) :
    Acc (fun g f : Flow cap s t ↦ f.AugmentsTo g) f := by
  obtain ⟨D, hD, h⟩ := Rat.exists_forall_mem_zmultiples_inv_natCast
    (Sum.elim (fun a : Σ v w, Q v w ↦ cap a.2.2) fun a : Σ v w, Q v w ↦ f.toFun a.2.2)
  exact acc_augmentsTo hst (inv_pos.2 (Nat.cast_pos.2 hD)) (fun v w e ↦ h (.inl ⟨v, w, e⟩))
    fun v w e ↦ h (.inr ⟨v, w, e⟩)

/-- For nonnegative rational capacities and distinct terminals, a maximum flow exists. -/
theorem exists_isMaximum_rat (hst : s ≠ t) (hcap₀ : 0 ≤ cap) : ∃ f : Flow cap s t, f.IsMaximum := by
  obtain ⟨D, hD, h⟩ := Rat.exists_forall_mem_zmultiples_inv_natCast fun a : Σ v w, Q v w ↦ cap a.2.2
  exact (exists_isMaximum_of_mem_zmultiples hst (inv_pos.2 (Nat.cast_pos.2 hD)) hcap₀
    fun v w e ↦ h ⟨v, w, e⟩).imp fun _ ↦ And.left

end Rat

end Flow

end TauCeti
