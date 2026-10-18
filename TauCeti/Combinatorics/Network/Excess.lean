/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic.Abel
public import TauCeti.Combinatorics.Network.Basic

/-!
# Excess of a directed arrow assignment

This file develops the additive calculus of excess on a finite directed arrow family. Excess is
incoming value minus outgoing value. Its total is zero, while its sum over a vertex set is the
value entering the set minus the value leaving it. These identities are the algebraic foundation
for flows, cuts, residual updates, and bounded circulations.
-/

public section

open Finset

universe u v w z

namespace TauCeti

variable {V : Type u} (Hom : V → V → Type v)

/-- Apply an additive homomorphism to every value of an assignment. -/
def Assignment.map {Hom : V → V → Type v} {K : Type w} {L : Type z}
    [AddZero K] [AddZero L]
    (f : Assignment Hom K) (g : K →+ L) : Assignment Hom L :=
  fun e ↦ g (f e)

@[simp]
theorem Assignment.map_apply {Hom : V → V → Type v} {K : Type w} {L : Type z}
    [AddZero K] [AddZero L]
    (f : Assignment Hom K) (g : K →+ L) {x y} (e : Hom x y) :
    f.map g e = g (f e) := (rfl)

/-- The total value entering a finite vertex set from its complement. -/
noncomputable def Assignment.inflow {Hom : V → V → Type v} [Fintype V]
    [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommMonoid K] (f : Assignment Hom K) (S : Finset V) : K :=
  by
    classical
    exact ∑ y ∈ S, ∑ x ∈ Sᶜ, ∑ e : Hom x y, f e

/-- The total value leaving a finite vertex set for its complement. -/
noncomputable def Assignment.outflow {Hom : V → V → Type v} [Fintype V]
    [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommMonoid K] (f : Assignment Hom K) (S : Finset V) : K :=
  by
    classical
    exact ∑ x ∈ S, ∑ y ∈ Sᶜ, ∑ e : Hom x y, f e

@[simp]
theorem Assignment.inflow_empty [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommMonoid K] (f : Assignment Hom K) : f.inflow ∅ = 0 := by
  simp [Assignment.inflow]

@[simp]
theorem Assignment.outflow_empty [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommMonoid K] (f : Assignment Hom K) : f.outflow ∅ = 0 := by
  simp [Assignment.outflow]

@[simp]
theorem Assignment.inflow_univ [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommMonoid K] (f : Assignment Hom K) : f.inflow univ = 0 := by
  simp [Assignment.inflow]

@[simp]
theorem Assignment.outflow_univ [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommMonoid K] (f : Assignment Hom K) : f.outflow univ = 0 := by
  simp [Assignment.outflow]

/-- The excess of an assignment at a vertex, with incoming value counted positively. -/
noncomputable def excessAt [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f : Assignment Hom K) (x : V) : K :=
  (∑ y, ∑ e : Hom y x, f e) - ∑ y, ∑ e : Hom x y, f e

@[simp]
theorem excessAt_zero [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (x : V) : excessAt Hom (0 : Assignment Hom K) x = 0 := by
  simp [excessAt]

@[simp]
theorem excessAt_add [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f g : Assignment Hom K) (x : V) :
    excessAt Hom (fun e ↦ f e + g e) x = excessAt Hom f x + excessAt Hom g x := by
  simp [excessAt, sum_add_distrib]
  abel

@[simp]
theorem excessAt_neg [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f : Assignment Hom K) (x : V) :
    excessAt Hom (fun e ↦ -f e) x = -excessAt Hom f x := by
  simp [excessAt]
  abel

@[simp]
theorem excessAt_sub [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f g : Assignment Hom K) (x : V) :
    excessAt Hom (fun e ↦ f e - g e) x = excessAt Hom f x - excessAt Hom g x := by
  simp [excessAt, sum_sub_distrib]
  abel

/-- Excess, as an additive homomorphism from assignments to vertex functions. -/
noncomputable def excessHom [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] : Assignment Hom K →+ (V → K) where
  toFun := excessAt Hom
  map_zero' := funext (excessAt_zero Hom)
  map_add' f g := funext (excessAt_add Hom f g)

@[simp]
theorem excessHom_apply [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f : Assignment Hom K) (x : V) :
    excessHom Hom f x = excessAt Hom f x := (rfl)

/-- Mapping coefficients by an additive homomorphism commutes with excess. -/
theorem excessAt_map [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} {L : Type z} [AddCommGroup K] [AddCommGroup L]
    (g : K →+ L) (f : Assignment Hom K) (x : V) :
    excessAt Hom (f.map g) x = g (excessAt Hom f x) := by
  simp only [excessAt, Assignment.map_apply, map_sub, map_sum]

/-- The total excess of a finite arrow assignment is zero. Loops cancel at their vertex. -/
theorem sum_excessAt_eq_zero [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f : Assignment Hom K) :
    ∑ x, excessAt Hom f x = 0 := by
  simp only [excessAt, sum_sub_distrib]
  rw [Finset.sum_comm]
  exact sub_self _

/-- Summed excess over a set is its inflow minus its outflow. -/
theorem sum_excessAt_eq_inflow_sub_outflow [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f : Assignment Hom K) (S : Finset V) :
    ∑ x ∈ S, excessAt Hom f x = f.inflow S - f.outflow S := by
  classical
  simp only [excessAt, sum_sub_distrib]
  have hin :
      (∑ y ∈ S, ∑ x, ∑ e : Hom x y, f e) =
        (∑ y ∈ S, ∑ x ∈ S, ∑ e : Hom x y, f e) + f.inflow S := by
    simp only [Assignment.inflow]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    exact S.sum_add_sum_compl (fun x ↦ ∑ e : Hom x y, f e) |>.symm
  have hout :
      (∑ x ∈ S, ∑ y, ∑ e : Hom x y, f e) =
        (∑ x ∈ S, ∑ y ∈ S, ∑ e : Hom x y, f e) + f.outflow S := by
    simp only [Assignment.outflow]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    exact S.sum_add_sum_compl (fun y ↦ ∑ e : Hom x y, f e) |>.symm
  rw [hin, hout]
  have hinternal :
      (∑ y ∈ S, ∑ x ∈ S, ∑ e : Hom x y, f e) =
        ∑ x ∈ S, ∑ y ∈ S, ∑ e : Hom x y, f e := by
    rw [Finset.sum_comm]
  rw [hinternal]
  abel

/-- Signed circulations are precisely the kernel of the excess homomorphism. -/
noncomputable def signedCirculations [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] : AddSubgroup (Assignment Hom K) :=
  (excessHom Hom).ker

@[simp]
theorem mem_signedCirculations [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f : Assignment Hom K) :
    (f : Assignment Hom K) ∈ signedCirculations Hom ↔ ∀ x, excessAt Hom f x = 0 := by
  rw [signedCirculations, AddMonoidHom.mem_ker]
  constructor
  · intro h x
    exact congrFun h x
  · exact fun h ↦ funext h

/-- Two assignments have the same excess exactly when their difference is a circulation. -/
theorem sub_mem_signedCirculations_iff [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f g : Assignment Hom K) :
    ((fun {x y} (e : Hom x y) ↦ f e - g e) : Assignment Hom K) ∈
      signedCirculations Hom ↔
      ∀ x, excessAt Hom f x = excessAt Hom g x := by
  simp only [mem_signedCirculations, excessAt_sub, sub_eq_zero]

/-- An assignment conserved away from two terminals has opposite terminal excesses. -/
theorem excessAt_source_eq_neg_sink [Fintype V] [∀ x y, Fintype (Hom x y)]
    {K : Type w} [AddCommGroup K] (f : Assignment Hom K) {s t : V}
    (hconserve : ∀ x, x ≠ s → x ≠ t → excessAt Hom f x = 0) :
    excessAt Hom f s = -excessAt Hom f t := by
  classical
  by_cases hst : s = t
  · subst t
    have hsingle :=
      (Fintype.sum_eq_single s fun x hx ↦ hconserve x hx hx).symm.trans
        (sum_excessAt_eq_zero Hom f)
    simp [hsingle]
  · exact eq_neg_of_add_eq_zero_left <|
      (Fintype.sum_eq_add s t hst fun x hx ↦ hconserve x hx.1 hx.2).symm.trans
        (sum_excessAt_eq_zero Hom f)

namespace Network

/-- Excess of an assignment on a network's arrow family. The network's bounds play no role. -/
noncomputable abbrev excessAt {C : Type*} [LE C] (N : Network C V) [Fintype V]
    [∀ x y, Fintype (N.Hom x y)] {K : Type w} [AddCommGroup K]
    (f : N.Assignment K) (x : V) : K :=
  TauCeti.excessAt N.Hom f x

/-- The additive excess map on a network's arrow family. -/
noncomputable abbrev excessHom {C : Type*} [LE C] (N : Network C V) [Fintype V]
    [∀ x y, Fintype (N.Hom x y)] {K : Type w} [AddCommGroup K] :
    N.Assignment K →+ (V → K) :=
  TauCeti.excessHom N.Hom

end Network

end TauCeti
