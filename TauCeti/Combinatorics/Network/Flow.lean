/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Order.Group.Basic
public import TauCeti.Combinatorics.Network.Residual

/-!
# Bounded terminal assignments, flows, and weak duality

Let `Q` be an arrow family on a finite vertex type `V` with lower and upper bounds
`lo hi : Assignment Q K`. A *bounded `s`–`t` assignment* is an arrow assignment between the bounds
that is conserved at every vertex other than the terminals `s` and `t`; its *value* is its excess
at `t`, of either sign. An *ordinary `s`–`t` flow* for capacities `cap` is the special case with
zero lower bounds and nonnegative value. Both share the arrow assignments, excess calculus and
residual updates of `TauCeti.Combinatorics.Network.Excess` and
`TauCeti.Combinatorics.Network.Residual`.

The value of a bounded `s`–`t` assignment is the net value across every vertex set `S` containing
`s` but not `t`. This gives **weak duality**: the value is at most the cut bound
`hi(δ⁺ S) - lo(δ⁻ S)`, and for an ordinary flow at most the capacity `cap(δ⁺ S)` of the cut. A
residual `s`–`t` assignment within the residual capacities updates a bounded `s`–`t` assignment
to another one, adding the two values, and every bounded `s`–`t` assignment arises from any other
in this way. These are the steps from which the augmenting-path characterization of maximum
flows is assembled.

## Main definitions

* `TauCeti.BoundedFlow lo hi s t`: bounded `s`–`t` assignments, with value `BoundedFlow.val`.
* `TauCeti.cutBound lo hi S`: the total upper bound leaving `S` minus the total lower bound
  entering `S`.
* `TauCeti.BoundedFlow.swap`: the same assignment as a bounded `t`–`s` assignment.
* `TauCeti.BoundedFlow.update`: the residual update by a residual `s`–`t` assignment.
* `TauCeti.Flow cap s t`: ordinary `s`–`t` flows for the capacities `cap`.
* `TauCeti.Flow.zero`: the zero flow for nonnegative capacities.
* `TauCeti.BoundedFlow.swapFlow`: terminal exchange, turning a capacity-feasible assignment of
  nonpositive value into an ordinary flow in the opposite direction.
* `TauCeti.Flow.augment`: augmentation of a flow by a flow of its residual network.

## Main results

* `TauCeti.BoundedFlow.val_eq_arrowSum_sub`: the value is the net value across any
  terminal-separating vertex set.
* `TauCeti.BoundedFlow.val_le_cutBound` and `TauCeti.BoundedFlow.neg_cutBound_compl_le_val`:
  weak duality for bounded `s`–`t` assignments, from above and from below.
* `TauCeti.Flow.val_le_arrowSum`: weak duality for ordinary flows.
* `TauCeti.Flow.arrowSum_le_arrowSum_univ`: a flow carries at most the total capacity across any
  pair of vertex sets.
* `TauCeti.map_cutBound`: cut bounds commute with additive coefficient maps.
* `TauCeti.BoundedFlow.cutBound_sub_val` and `TauCeti.BoundedFlow.val_eq_cutBound_iff`: the gap
  between a cut bound and the value is the residual capacity leaving the cut, so the value attains
  the cut bound exactly when no residual arrow of positive capacity leaves the cut.
* `TauCeti.BoundedFlow.val_update` and `TauCeti.BoundedFlow.exists_update_eq`: residual updates
  add values, and connect any two bounded `s`–`t` assignments.
* `TauCeti.Flow.exists_augment_eq`: every flow of at least the value of `f` is an augmentation of
  `f` by a flow of its residual network.
* `TauCeti.Flow.exists_nsmul_eq_val`: a flow with arrow values in `zmultiples d` has value
  `n • d` for a natural number `n`.

## References

* R. K. Ahuja, T. L. Magnanti, J. B. Orlin, *Network Flows: Theory, Algorithms, and
  Applications*, Prentice Hall, 1993.
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003.
-/

public section

namespace TauCeti

open Finset

universe u v w

variable {V : Type u} {Q : V → V → Type v} {K : Type w}

section BoundedFlow

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K]

/-- A *bounded `s`–`t` assignment* for lower and upper bounds `lo` and `hi`: an arrow assignment
between the bounds, conserved at every vertex other than `s` and `t`. There is no sign condition
on the arrow values or on the value. -/
@[ext]
structure BoundedFlow [Preorder K] (lo hi : Assignment Q K) (s t : V) where
  /-- The value on each arrow. -/
  toFun : Assignment Q K
  /-- The assignment lies between the lower and upper bounds. -/
  mem_Icc : toFun ∈ Set.Icc lo hi
  /-- The assignment is conserved at every vertex other than the terminals. -/
  conserve : ∀ v, v ≠ s → v ≠ t → excessAt toFun v = 0

/-- The *cut bound* of a vertex set `S` for lower and upper bounds `lo` and `hi`: the total upper
bound on arrows leaving `S` minus the total lower bound on arrows entering `S`. For zero lower
bounds it is the capacity of the arrows leaving `S`. -/
def cutBound [DecidableEq V] (lo hi : Assignment Q K) (S : Finset V) : K :=
  arrowSum hi S Sᶜ - arrowSum lo Sᶜ S

theorem cutBound_def [DecidableEq V] (lo hi : Assignment Q K) (S : Finset V) :
    cutBound lo hi S = arrowSum hi S Sᶜ - arrowSum lo Sᶜ S :=
  (rfl)

@[simp]
theorem cutBound_zero_left [DecidableEq V] (hi : Assignment Q K) (S : Finset V) :
    cutBound 0 hi S = arrowSum hi S Sᶜ := by
  rw [cutBound_def, arrowSum_zero, sub_zero]

/-- Cut bounds commute with additive coefficient maps. -/
theorem map_cutBound [DecidableEq V] {L F : Type*} [AddCommGroup L] [FunLike F K L]
    [AddMonoidHomClass F K L] (φ : F) (lo hi : Assignment Q K) (S : Finset V) :
    φ (cutBound lo hi S) = cutBound (lo.map φ) (hi.map φ) S := by
  rw [cutBound_def, cutBound_def, map_sub, map_arrowSum, map_arrowSum]

namespace BoundedFlow

section Preorder

variable [Preorder K] {lo hi : Assignment Q K} {s t : V}

theorem lower_le (f : BoundedFlow lo hi s t) {x y : V} (e : Q x y) : lo e ≤ f.toFun e :=
  f.mem_Icc.1 x y e

theorem le_upper (f : BoundedFlow lo hi s t) {x y : V} (e : Q x y) : f.toFun e ≤ hi e :=
  f.mem_Icc.2 x y e

/-- The *value* of a bounded `s`–`t` assignment: its excess at the sink `t`. -/
def val (f : BoundedFlow lo hi s t) : K :=
  excessAt f.toFun t

theorem val_def (f : BoundedFlow lo hi s t) : f.val = excessAt f.toFun t :=
  (rfl)

/-- The excess at the source is minus the value. -/
theorem excessAt_source (f : BoundedFlow lo hi s t) : excessAt f.toFun s = -f.val :=
  excessAt_source_eq_neg_sink f.toFun f.conserve

/-- The value of a bounded `s`–`t` assignment is the value on arrows leaving `S` minus the value
on arrows entering `S`, for every vertex set `S` containing `s` but not `t`. -/
theorem val_eq_arrowSum_sub [DecidableEq V] (f : BoundedFlow lo hi s t) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : f.val = arrowSum f.toFun S Sᶜ - arrowSum f.toFun Sᶜ S :=
  excessAt_sink_eq_arrowSum_sub f.toFun f.conserve hs ht

/-- **Residual cut gap.** For every vertex set `S` containing `s` but not `t`, the cut bound of `S`
exceeds the value of a bounded `s`–`t` assignment by its total residual capacity on the residual
arrows leaving `S`: the room left on the arrows leaving `S` plus the room left to decrease the
arrows entering `S`. -/
theorem cutBound_sub_val [DecidableEq V] (f : BoundedFlow lo hi s t) {S : Finset V} (hs : s ∈ S)
    (ht : t ∉ S) :
    cutBound lo hi S - f.val = arrowSum (residualCapacity lo hi f.toFun) S Sᶜ := by
  rw [arrowSum_residualCapacity, arrowSum_sub, arrowSum_sub, f.val_eq_arrowSum_sub hs ht,
    cutBound_def]
  abel

/-- A bounded `s`–`t` assignment, viewed as a bounded `t`–`s` assignment. -/
def swap (f : BoundedFlow lo hi s t) : BoundedFlow lo hi t s where
  toFun := f.toFun
  mem_Icc := f.mem_Icc
  conserve v hvt hvs := f.conserve v hvs hvt

@[simp]
theorem swap_toFun (f : BoundedFlow lo hi s t) : f.swap.toFun = f.toFun :=
  (rfl)

@[simp]
theorem swap_swap (f : BoundedFlow lo hi s t) : f.swap.swap = f :=
  (rfl)

/-- Exchanging the terminals negates the value. -/
@[simp]
theorem val_swap (f : BoundedFlow lo hi s t) : f.swap.val = -f.val := by
  rw [val_def, swap_toFun, excessAt_source]

/-- A bounded assignment whose terminals coincide has value zero. -/
theorem val_eq_zero_of_eq (hst : s = t) (f : BoundedFlow lo hi s t) : f.val = 0 := by
  subst hst
  rw [val_def, ← sum_excessAt f.toFun, Fintype.sum_eq_single s fun v hv ↦ f.conserve v hv hv]

end Preorder

section Ordered

variable [PartialOrder K] [IsOrderedAddMonoid K] {lo hi : Assignment Q K} {s t : V}

/-- **Weak duality.** The value of a bounded `s`–`t` assignment is at most the cut bound of every
vertex set containing `s` but not `t`. -/
theorem val_le_cutBound [DecidableEq V] (f : BoundedFlow lo hi s t) {S : Finset V} (hs : s ∈ S)
    (ht : t ∉ S) : f.val ≤ cutBound lo hi S := by
  rw [f.val_eq_arrowSum_sub hs ht, cutBound_def]
  exact sub_le_sub (arrowSum_mono f.mem_Icc.2 _ _) (arrowSum_mono f.mem_Icc.1 _ _)

/-- A bounded `s`–`t` assignment attains the cut bound of a vertex set `S` containing `s` but not
`t` exactly when every residual arrow leaving `S` has zero residual capacity. -/
theorem val_eq_cutBound_iff [DecidableEq V] (f : BoundedFlow lo hi s t) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) :
    f.val = cutBound lo hi S ↔
      ∀ v ∈ S, ∀ w ∉ S, ∀ e : ResidualHom Q v w, residualCapacity lo hi f.toFun e = 0 := by
  rw [eq_comm, ← sub_eq_zero, f.cutBound_sub_val hs ht,
    arrowSum_eq_zero_iff_of_nonneg (residualCapacity_nonneg f.mem_Icc)]
  simp only [mem_compl]

/-- **Weak duality from below.** The value of a bounded `s`–`t` assignment is at least minus the
cut bound of the complement of every vertex set containing `s` but not `t`, that is, at least the
total lower bound leaving the set minus the total upper bound entering it. -/
theorem neg_cutBound_compl_le_val [DecidableEq V] (f : BoundedFlow lo hi s t) {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : -cutBound lo hi Sᶜ ≤ f.val := by
  rw [f.val_eq_arrowSum_sub hs ht, cutBound_def, compl_compl, neg_sub]
  exact sub_le_sub (arrowSum_mono f.mem_Icc.1 _ _) (arrowSum_mono f.mem_Icc.2 _ _)

/-- The *residual update* of a bounded `s`–`t` assignment `f` by a residual `s`–`t` assignment `r`
between zero and the residual capacities of `f`: the value on an arrow `e` becomes
`f e + r e⁺ - r e⁻`. -/
def update (f : BoundedFlow lo hi s t)
    (r : BoundedFlow 0 (residualCapacity lo hi f.toFun) s t) : BoundedFlow lo hi s t where
  toFun := residualUpdate f.toFun r.toFun
  mem_Icc := residualUpdate_mem_Icc r.mem_Icc
  conserve v hvs hvt := by
    rw [excessAt_residualUpdate, f.conserve v hvs hvt, r.conserve v hvs hvt, add_zero]

@[simp]
theorem update_toFun (f : BoundedFlow lo hi s t)
    (r : BoundedFlow 0 (residualCapacity lo hi f.toFun) s t) :
    (f.update r).toFun = residualUpdate f.toFun r.toFun :=
  (rfl)

/-- A residual update adds the value of the residual assignment. -/
@[simp]
theorem val_update (f : BoundedFlow lo hi s t)
    (r : BoundedFlow 0 (residualCapacity lo hi f.toFun) s t) :
    (f.update r).val = f.val + r.val := by
  rw [val_def, update_toFun, excessAt_residualUpdate, val_def, val_def]

end Ordered

/-- Every bounded `s`–`t` assignment `g` is a residual update of any other one `f`, by a residual
`s`–`t` assignment, necessarily of value `g.val - f.val`. -/
theorem exists_update_eq [Lattice K] [IsOrderedAddMonoid K] {lo hi : Assignment Q K} {s t : V}
    (f g : BoundedFlow lo hi s t) :
    ∃ r : BoundedFlow 0 (residualCapacity lo hi f.toFun) s t, f.update r = g := by
  obtain ⟨r, hr, hfr⟩ := exists_residualUpdate_eq f.mem_Icc g.mem_Icc
  refine ⟨⟨r, hr, fun v hvs hvt ↦ ?_⟩, BoundedFlow.ext hfr⟩
  have hv := congrArg (excessAt · v) hfr
  rwa [excessAt_residualUpdate, f.conserve v hvs hvt, g.conserve v hvs hvt, zero_add] at hv

end BoundedFlow

/-! ### Ordinary flows -/

section Flow

variable [Preorder K]

/-- An *ordinary `s`–`t` flow* for the capacities `cap`: a bounded `s`–`t` assignment with zero
lower bounds, so with `0 ≤ f e ≤ cap e` on every arrow, whose value is nonnegative. -/
@[ext]
structure Flow (cap : Assignment Q K) (s t : V) extends BoundedFlow 0 cap s t where
  /-- The excess at the sink, which is the value of the flow, is nonnegative. -/
  excessAt_sink_nonneg : 0 ≤ excessAt toFun t

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-- The zero flow for nonnegative capacities. -/
def zero (hcap : 0 ≤ cap) : Flow cap s t where
  toFun := 0
  mem_Icc := ⟨le_rfl, hcap⟩
  conserve v _ _ := excessAt_zero v
  excessAt_sink_nonneg := (excessAt_zero t).ge

@[simp]
theorem zero_toFun (hcap : 0 ≤ cap) : (zero hcap : Flow cap s t).toFun = 0 :=
  (rfl)

@[simp]
theorem val_zero (hcap : 0 ≤ cap) : (zero hcap : Flow cap s t).val = 0 := by
  rw [BoundedFlow.val_def, zero_toFun, excessAt_zero]

theorem nonneg (f : Flow cap s t) {x y : V} (e : Q x y) : 0 ≤ f.toFun e :=
  f.lower_le e

theorem val_nonneg (f : Flow cap s t) : 0 ≤ f.val :=
  f.excessAt_sink_nonneg

/-- Ordinary `s`–`t` flows are the bounded `s`–`t` assignments with zero lower bounds and
nonnegative value. -/
def equivBoundedFlow : Flow cap s t ≃ {f : BoundedFlow 0 cap s t // 0 ≤ f.val} where
  toFun f := ⟨f.toBoundedFlow, f.val_nonneg⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_equivBoundedFlow_apply (f : Flow cap s t) :
    (equivBoundedFlow f : BoundedFlow 0 cap s t) = f.toBoundedFlow :=
  (rfl)

@[simp]
theorem toBoundedFlow_equivBoundedFlow_symm_apply (f : {f : BoundedFlow 0 cap s t // 0 ≤ f.val}) :
    (equivBoundedFlow.symm f).toBoundedFlow = f :=
  (rfl)

end Flow

end Flow

section Ordered

variable [PartialOrder K] [IsOrderedAddMonoid K]

/-- **Terminal exchange.** A capacity-feasible `s`–`t` assignment of nonpositive value is an
ordinary `t`–`s` flow, with the same arrow values and the opposite value. -/
def BoundedFlow.swapFlow {cap : Assignment Q K} {s t : V} (f : BoundedFlow 0 cap s t)
    (hf : f.val ≤ 0) : Flow cap t s where
  toBoundedFlow := f.swap
  excessAt_sink_nonneg := by
    rw [← BoundedFlow.val_def, BoundedFlow.val_swap]
    exact neg_nonneg.mpr hf

@[simp]
theorem BoundedFlow.toBoundedFlow_swapFlow {cap : Assignment Q K} {s t : V}
    (f : BoundedFlow 0 cap s t) (hf : f.val ≤ 0) : (f.swapFlow hf).toBoundedFlow = f.swap :=
  (rfl)

namespace Flow

variable {cap : Assignment Q K} {s t : V}

/-- **Weak duality.** The value of an ordinary `s`–`t` flow is at most the total capacity of the
arrows leaving any vertex set containing `s` but not `t`. -/
theorem val_le_arrowSum [DecidableEq V] (f : Flow cap s t) {S : Finset V} (hs : s ∈ S)
    (ht : t ∉ S) : f.val ≤ arrowSum cap S Sᶜ :=
  calc f.val ≤ cutBound 0 cap S := f.toBoundedFlow.val_le_cutBound hs ht
    _ = arrowSum cap S Sᶜ := cutBound_zero_left cap S

/-- The value of an ordinary flow on the arrows from any vertex set to any other is at most the
total capacity of all arrows. -/
theorem arrowSum_le_arrowSum_univ (f : Flow cap s t) (S T : Finset V) :
    arrowSum f.toFun S T ≤ arrowSum cap univ univ :=
  calc arrowSum f.toFun S T ≤ arrowSum f.toFun univ univ :=
        (arrowSum_mono_left f.mem_Icc.1 (subset_univ S) T).trans
          (arrowSum_mono_right f.mem_Icc.1 univ (subset_univ T))
    _ ≤ arrowSum cap univ univ := arrowSum_mono f.mem_Icc.2 univ univ

/-- The *augmentation* of an ordinary `s`–`t` flow `f` by an ordinary `s`–`t` flow `r` of its
residual network: the residual update of `f` by `r`. -/
def augment (f : Flow cap s t) (r : Flow (residualCapacity 0 cap f.toFun) s t) :
    Flow cap s t where
  toBoundedFlow := f.update r.toBoundedFlow
  excessAt_sink_nonneg := by
    rw [← BoundedFlow.val_def, BoundedFlow.val_update]
    exact add_nonneg f.val_nonneg r.val_nonneg

@[simp]
theorem toBoundedFlow_augment (f : Flow cap s t) (r : Flow (residualCapacity 0 cap f.toFun) s t) :
    (f.augment r).toBoundedFlow = f.update r.toBoundedFlow :=
  (rfl)

end Flow

end Ordered

/-- Every ordinary `s`–`t` flow `g` of value at least that of `f` is the augmentation of `f` by an
ordinary `s`–`t` flow of the residual network of `f`, necessarily of value `g.val - f.val`. -/
theorem Flow.exists_augment_eq [Lattice K] [IsOrderedAddMonoid K] {cap : Assignment Q K}
    {s t : V} (f g : Flow cap s t) (hfg : f.val ≤ g.val) :
    ∃ r : Flow (residualCapacity 0 cap f.toFun) s t, f.augment r = g := by
  obtain ⟨r, hr⟩ := f.toBoundedFlow.exists_update_eq g.toBoundedFlow
  have hval : r.val = g.val - f.val := by
    rw [← hr, BoundedFlow.val_update, add_sub_cancel_left]
  refine ⟨⟨r, ?_⟩, Flow.ext (congrArg BoundedFlow.toFun hr)⟩
  rw [← BoundedFlow.val_def, hval]
  exact sub_nonneg.mpr hfg

/-- For `0 < d`, an ordinary flow with arrow values in `zmultiples d` has value `n • d` for a
natural number `n`. -/
theorem Flow.exists_nsmul_eq_val [PartialOrder K] [IsOrderedAddMonoid K] {cap : Assignment Q K}
    {s t : V} {d : K} (hd : 0 < d) {f : Flow cap s t}
    (hf : ∀ ⦃v w⦄ (e : Q v w), f.toFun e ∈ AddSubgroup.zmultiples d) :
    ∃ n : ℕ, n • d = f.val := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (excessAt_mem hf t)
  rw [← BoundedFlow.val_def] at hk
  have hk₀ : 0 ≤ k := (zsmul_le_zsmul_iff_left hd).1 (by simpa [hk] using f.val_nonneg)
  exact ⟨k.toNat, by rw [← natCast_zsmul, Int.toNat_of_nonneg hk₀, hk]⟩

end BoundedFlow

/-! ### Network abbreviations -/

namespace Network

variable [Fintype V] [AddCommGroup K] [Preorder K]

/-- The bounded `s`–`t` assignments of a network, respecting both its lower and upper bounds. -/
abbrev BoundedFlow (N : Network K V) [∀ x y, Fintype (N.Hom x y)] (s t : V) :=
  TauCeti.BoundedFlow N.lower N.upper s t

/-- The ordinary `s`–`t` flows against the upper bounds of a network. The lower bounds are
ignored, so this is the flow type of `N` only when its lower bounds vanish, as for networks built
by `Network.ofCapacity`. -/
abbrev UpperFlow (N : Network K V) [∀ x y, Fintype (N.Hom x y)] (s t : V) :=
  TauCeti.Flow N.upper s t

end Network

end TauCeti
