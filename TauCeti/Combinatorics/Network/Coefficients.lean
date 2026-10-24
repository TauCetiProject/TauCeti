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

@[simp]
theorem map_id (f : BoundedFlow lo hi s t) : f.map (OrderAddMonoidHom.id K) = f :=
  BoundedFlow.ext (rfl)

@[simp]
theorem map_map {M : Type*} [AddCommGroup M] [Preorder M] (φ : K →+o L) (ψ : L →+o M)
    (f : BoundedFlow lo hi s t) : (f.map φ).map ψ = f.map (ψ.comp φ) :=
  BoundedFlow.ext (rfl)

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
    positiveReachable_map_iff_of_strictMono hφ (map_zero φ)]

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

@[simp]
theorem map_id (f : Flow cap s t) : f.map (OrderAddMonoidHom.id K) = f :=
  Flow.ext (rfl)

@[simp]
theorem map_map {M : Type*} [AddCommGroup M] [Preorder M] (φ : K →+o L) (ψ : L →+o M)
    (f : Flow cap s t) : (f.map φ).map ψ = f.map (ψ.comp φ) :=
  Flow.ext (rfl)

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
    positiveReachable_map_iff_of_strictMono hφ (map_zero φ)]

end Flow

end TauCeti
