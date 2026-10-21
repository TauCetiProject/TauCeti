/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Hom.Monoid
public import TauCeti.Combinatorics.Network.AugmentingPath

/-!
# Change of coefficients for networks and flows

An order-preserving additive group homomorphism `φ : K →+o L` carries the finite-bound flow
theory over `K` to the one over `L`: apply `φ` to every bound and to the value of an assignment
on every arrow, written `Assignment.map`. Additivity makes `φ` commute with arrow sums, excess,
cut bounds, residual capacities and residual updates, and monotonicity preserves feasibility.
So a bounded `s`–`t` assignment or an ordinary flow over `K` becomes one over `L`, whose value
is the image of the original value. The standard examples are the embeddings `ℤ → ℚ → ℝ`, which
turn integral flows into rational and real ones.

Every such `φ` preserves maximality, whether or not it is injective: between distinct terminals,
a maximum assignment attains the cut bound of some cut, `φ` carries this equality to `L`, and
weak duality over `L` makes the image maximum. A strictly monotone `φ` also reflects maximality,
since it preserves and reflects positivity of residual capacities, and hence the existence of
augmenting walks.

## Main definitions

* `TauCeti.Network.map N φ hφ`: the network with the same arrows as `N` and bounds mapped by a
  monotone function `φ`.
* `TauCeti.BoundedFlow.map φ f` and `TauCeti.Flow.map φ f`: a bounded `s`–`t` assignment or an
  ordinary flow with its coefficients changed along `φ : K →+o L`.

## Main results

* `TauCeti.map_cutBound`: cut bounds commute with additive coefficient maps.
* `TauCeti.Assignment.map_residualCapacity` and `TauCeti.Assignment.map_residualUpdate`:
  residual capacities and residual updates commute with additive coefficient maps.
* `TauCeti.positiveReachable_map_iff`: a coefficient map preserving and reflecting positivity
  does not change positive reachability.
* `TauCeti.BoundedFlow.val_map` and `TauCeti.Flow.val_map`: the value of the image is the image
  of the value.
* `TauCeti.BoundedFlow.IsMaximum.map` and `TauCeti.Flow.IsMaximum.map`: maximum assignments and
  flows stay maximum after any change of coefficients.
* `TauCeti.BoundedFlow.isMaximum_map_iff` and `TauCeti.Flow.isMaximum_map_iff`: strictly monotone
  coefficient maps also reflect maximality.
-/

public section

namespace TauCeti

open Finset

variable {V : Type*} {Q : V → V → Type*} {K L : Type*}

/-! ### Assignments -/

namespace Assignment

section Algebra

variable {F : Type*} [FunLike F K L]

@[simp]
theorem map_zero [Zero K] [Zero L] [ZeroHomClass F K L] (φ : F) :
    (0 : Assignment Q K).map φ = 0 := by
  funext _ _ e
  exact (map_apply _ _ e).trans (_root_.map_zero φ)

@[simp]
theorem map_add [Add K] [Add L] [AddHomClass F K L] (φ : F) (f g : Assignment Q K) :
    (f + g).map φ = f.map φ + g.map φ := by
  funext _ _ e
  simp

@[simp]
theorem map_neg [AddGroup K] [AddGroup L] [AddMonoidHomClass F K L] (φ : F)
    (f : Assignment Q K) : (-f).map φ = -f.map φ := by
  funext _ _ e
  simp

@[simp]
theorem map_sub [AddGroup K] [AddGroup L] [AddMonoidHomClass F K L] (φ : F)
    (f g : Assignment Q K) : (f - g).map φ = f.map φ - g.map φ := by
  funext _ _ e
  simp

/-- Residual capacities commute with additive coefficient maps. -/
theorem map_residualCapacity [AddGroup K] [AddGroup L] [AddMonoidHomClass F K L] (φ : F)
    (lo hi f : Assignment Q K) :
    (residualCapacity lo hi f).map φ = residualCapacity (lo.map φ) (hi.map φ) (f.map φ) := by
  funext _ _ e
  rcases e with e | e <;> simp

theorem map_residualNet [AddCommGroup K] [AddCommGroup L] [AddMonoidHomClass F K L] (φ : F)
    (r : Assignment (ResidualHom Q) K) : (residualNet r).map φ = residualNet (r.map φ) := by
  funext _ _ e
  simp

/-- Residual updates commute with additive coefficient maps. -/
theorem map_residualUpdate [AddCommGroup K] [AddCommGroup L] [AddMonoidHomClass F K L] (φ : F)
    (f : Assignment Q K) (r : Assignment (ResidualHom Q) K) :
    (residualUpdate f r).map φ = residualUpdate (f.map φ) (r.map φ) := by
  rw [residualUpdate_def, residualUpdate_def, map_add, map_residualNet]

end Algebra

section Order

variable [Preorder K] [Preorder L] {φ : K → L}

theorem map_mono (hφ : Monotone φ) {f g : Assignment Q K} (h : f ≤ g) : f.map φ ≤ g.map φ := by
  intro x y e
  simpa only [map_apply] using hφ (h x y e)

/-- A monotone coefficient map preserves feasibility, with the bounds mapped as well. -/
theorem map_mem_Icc (hφ : Monotone φ) {lo hi f : Assignment Q K} (hf : f ∈ Set.Icc lo hi) :
    f.map φ ∈ Set.Icc (lo.map φ) (hi.map φ) :=
  ⟨map_mono hφ hf.1, map_mono hφ hf.2⟩

end Order

end Assignment

/-! ### Excess, cuts and positive reachability -/

section Excess

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K] [AddCommGroup L] {F : Type*}
  [FunLike F K L] [AddMonoidHomClass F K L]

/-- A circulation stays a circulation after an additive change of coefficients. -/
theorem IsCirculation.map {f : Assignment Q K} (hf : IsCirculation f) (φ : F) :
    IsCirculation (f.map φ) :=
  (isCirculation_iff _).2 fun v ↦ by
    rw [← map_excessAt, (isCirculation_iff f).1 hf v, _root_.map_zero]

/-- Cut bounds commute with additive coefficient maps. -/
theorem map_cutBound [DecidableEq V] (φ : F) (lo hi : Assignment Q K) (S : Finset V) :
    φ (cutBound lo hi S) = cutBound (lo.map φ) (hi.map φ) S := by
  rw [cutBound_def, cutBound_def, _root_.map_sub, map_arrowSum, map_arrowSum]

end Excess

/-- Positive reachability is unchanged by a coefficient map that preserves and reflects
positivity, such as a strictly monotone additive map. -/
theorem positiveReachable_map_iff [Zero K] [LT K] [Zero L] [LT L] {c : Assignment Q K}
    {φ : K → L} (hφ : ∀ x, 0 < φ x ↔ 0 < x) {s t : V} :
    PositiveReachable (c.map φ) s t ↔ PositiveReachable c s t := by
  simp only [positiveReachable_def, Assignment.map_apply, hφ]

/-! ### Networks -/

namespace Network

variable [Preorder K] [Preorder L]

/-- The network with the same arrows as `N` and both bounds mapped by a monotone function `φ`.

This definition is exposed because its arrow family must reduce when assignments on the resulting
network are elaborated. -/
@[expose]
def map (N : Network K V) (φ : K → L) (hφ : Monotone φ) : Network L V where
  Hom := N.Hom
  lower := N.lower.map φ
  upper := N.upper.map φ
  lower_le_upper e := by simpa only [Assignment.map_apply] using hφ (N.lower_le_upper e)

variable (N : Network K V) (φ : K → L) (hφ : Monotone φ)

@[simp]
theorem map_Hom : (N.map φ hφ).Hom = N.Hom :=
  (rfl)

@[simp]
theorem map_lower {x y : V} (e : (N.map φ hφ).Hom x y) : (N.map φ hφ).lower e = φ (N.lower e) :=
  Assignment.map_apply _ _ _

@[simp]
theorem map_upper {x y : V} (e : (N.map φ hφ).Hom x y) : (N.map φ hφ).upper e = φ (N.upper e) :=
  Assignment.map_apply _ _ _

@[simp]
theorem map_id : N.map id monotone_id = N := by
  cases N
  simp [map]

@[simp]
theorem map_map {M : Type*} [Preorder M] (ψ : L → M) (hψ : Monotone ψ) :
    (N.map φ hφ).map ψ hψ = N.map (ψ ∘ φ) (hψ.comp hφ) := by
  simp [map]

/-- Changing the coefficients of an ordinary network along a monotone map fixing zero gives the
ordinary network of the mapped capacities. -/
theorem ofCapacity_map [Zero K] [Zero L] (Hom : V → V → Type*) (capacity : TauCeti.Assignment Hom K)
    (hcapacity : ∀ {x y} (e : Hom x y), 0 ≤ capacity e) (hφ₀ : φ 0 = 0) :
    (ofCapacity Hom capacity hcapacity).map φ hφ =
      ofCapacity Hom (capacity.map φ) fun e ↦ by simpa [hφ₀] using hφ (hcapacity e) := by
  simp only [map, ofCapacity, mk.injEq, heq_eq_eq, true_and, and_true]
  funext _ _ e
  simp [hφ₀]

end Network

/-! ### Bounded assignments and flows -/

variable [Fintype V] [∀ v w, Fintype (Q v w)] [AddCommGroup K] [AddCommGroup L] {s t : V}

namespace BoundedFlow

section Preorder

variable [Preorder K] [Preorder L] {lo hi : Assignment Q K}

/-- The bounded `s`–`t` assignment for the mapped bounds obtained by applying `φ` to the value on
every arrow. -/
def map (φ : K →+o L) (f : BoundedFlow lo hi s t) : BoundedFlow (lo.map φ) (hi.map φ) s t where
  toFun := f.toFun.map φ
  mem_Icc := Assignment.map_mem_Icc (OrderHomClass.mono φ) f.mem_Icc
  conserve v hvs hvt := by rw [← map_excessAt, f.conserve v hvs hvt, _root_.map_zero]

@[simp]
theorem map_toFun (φ : K →+o L) (f : BoundedFlow lo hi s t) : (f.map φ).toFun = f.toFun.map φ :=
  (rfl)

/-- Changing coefficients maps the value. -/
@[simp]
theorem val_map (φ : K →+o L) (f : BoundedFlow lo hi s t) : (f.map φ).val = φ f.val := by
  rw [val_def, val_def, map_toFun, map_excessAt]

theorem map_swap (φ : K →+o L) (f : BoundedFlow lo hi s t) : f.swap.map φ = (f.map φ).swap :=
  BoundedFlow.ext (by simp)

end Preorder

variable [LinearOrder K] [IsOrderedAddMonoid K] {lo hi : Assignment Q K}

/-- **Maximality under change of coefficients.** The image of a maximum bounded `s`–`t` assignment
between distinct terminals under an order-preserving additive map is maximum. -/
theorem IsMaximum.map [PartialOrder L] [IsOrderedAddMonoid L] (hst : s ≠ t) (φ : K →+o L)
    {f : BoundedFlow lo hi s t} (hf : f.IsMaximum) : (f.map φ).IsMaximum := by
  classical
  obtain ⟨S, hs, ht, h⟩ := hf.exists_val_eq_cutBound hst
  exact (f.map φ).isMaximum_of_val_eq_cutBound hs ht (by rw [val_map, h, map_cutBound])

/-- A strictly monotone additive map preserves and reflects maximality of bounded `s`–`t`
assignments between distinct terminals. -/
theorem isMaximum_map_iff [LinearOrder L] [IsOrderedAddMonoid L] (hst : s ≠ t) {φ : K →+o L}
    (hφ : StrictMono φ) {f : BoundedFlow lo hi s t} : (f.map φ).IsMaximum ↔ f.IsMaximum := by
  rw [isMaximum_iff_not_positiveReachable hst, isMaximum_iff_not_positiveReachable hst,
    map_toFun, ← Assignment.map_residualCapacity,
    positiveReachable_map_iff fun x ↦ by simpa using hφ.lt_iff_lt (a := 0) (b := x)]

end BoundedFlow

namespace Flow

section Preorder

variable [Preorder K] [Preorder L] {cap : Assignment Q K}

/-- The ordinary `s`–`t` flow for the mapped capacities obtained by applying `φ` to the value on
every arrow. -/
def map (φ : K →+o L) (f : Flow cap s t) : Flow (cap.map φ) s t where
  toFun := f.toFun.map φ
  mem_Icc := by
    simpa only [BoundedFlow.map_toFun, Assignment.map_zero] using (f.toBoundedFlow.map φ).mem_Icc
  conserve := (f.toBoundedFlow.map φ).conserve
  excessAt_sink_nonneg := by
    simpa only [← map_excessAt, _root_.map_zero] using (OrderHomClass.mono φ) f.excessAt_sink_nonneg

@[simp]
theorem map_toFun (φ : K →+o L) (f : Flow cap s t) : (f.map φ).toFun = f.toFun.map φ :=
  (rfl)

/-- Changing coefficients maps the value. -/
@[simp]
theorem val_map (φ : K →+o L) (f : Flow cap s t) : (f.map φ).val = φ f.val := by
  rw [BoundedFlow.val_def, BoundedFlow.val_def, map_toFun, map_excessAt]

end Preorder

variable [LinearOrder K] [IsOrderedAddMonoid K] {cap : Assignment Q K}

/-- **Maximality under change of coefficients.** The image of a maximum ordinary `s`–`t` flow
between distinct terminals under an order-preserving additive map is maximum. -/
theorem IsMaximum.map [PartialOrder L] [IsOrderedAddMonoid L] (hst : s ≠ t) (φ : K →+o L)
    {f : Flow cap s t} (hf : f.IsMaximum) : (f.map φ).IsMaximum := by
  classical
  obtain ⟨S, hs, ht, h⟩ := hf.exists_val_eq_arrowSum hst
  refine isMaximum_iff.2 fun g ↦ ?_
  rw [val_map, h, map_arrowSum]
  exact g.val_le_arrowSum hs ht

/-- A strictly monotone additive map preserves and reflects maximality of ordinary `s`–`t` flows
between distinct terminals. -/
theorem isMaximum_map_iff [LinearOrder L] [IsOrderedAddMonoid L] (hst : s ≠ t) {φ : K →+o L}
    (hφ : StrictMono φ) {f : Flow cap s t} : (f.map φ).IsMaximum ↔ f.IsMaximum := by
  rw [isMaximum_iff_not_positiveReachable hst, isMaximum_iff_not_positiveReachable hst,
    map_toFun, ← Assignment.map_zero φ, ← Assignment.map_residualCapacity,
    positiveReachable_map_iff fun x ↦ by simpa using hφ.lt_iff_lt (a := 0) (b := x)]

end Flow

end TauCeti
