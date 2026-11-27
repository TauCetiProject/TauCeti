/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.MvPowerSeries.Order

/-!
# Formal implicit functions with identity linear part

* `MvPowerSeries.existsUnique_fixedPoint_of_order_sub` gives a fixed point for a map of
  zero-constant tuples that raises the order of differences by one.
* `MvPowerSeries.existsUnique_subst_eq_of_two_le_order_sub_X` solves a substitution equation
  when the coordinate series agree with the variables through degree one.

The fixed point uses `MvPowerSeries.exists_forall_le_order_sub`; the substitution estimate
uses `MvPowerSeries.le_order_subst_sub_subst` and Mathlib's `MvPowerSeries.subst_sub`.
For the degree-by-degree construction of the inverse of a formal group law, see Stix,
*A course on finite flat group schemes and p-divisible groups*, §10.2.2.
-/

public section

namespace MvPowerSeries

variable {ι σ τ R : Type*}

section Ring

variable [Ring R]

/-- A self-map of zero-constant tuples of power series has a unique fixed point if it
improves every common lower bound on the orders of coordinate differences by one. -/
theorem existsUnique_fixedPoint_of_order_sub
    (F : {a : ι → MvPowerSeries σ R // ∀ i, constantCoeff (a i) = 0} →
      {a : ι → MvPowerSeries σ R // ∀ i, constantCoeff (a i) = 0})
    (hF : ∀ {a b} {n : ℕ}, (∀ i, (n : ℕ∞) ≤ (a.val i - b.val i).order) →
      ∀ i, ((n + 1 : ℕ) : ℕ∞) ≤ ((F a).val i - (F b).val i).order) :
    ∃! a, F a = a := by
  let u : ℕ → {a : ι → MvPowerSeries σ R // ∀ i, constantCoeff (a i) = 0} :=
    fun n ↦ F^[n] ⟨0, fun _ ↦ map_zero constantCoeff⟩
  have hsucc (n : ℕ) : u (n + 1) = F (u n) := Function.iterate_succ_apply' F n _
  have hstep (n : ℕ) : ∀ i, (n : ℕ∞) ≤ ((u (n + 1)).val i - (u n).val i).order := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [hsucc] using hF ih
  choose a ha using fun i ↦
    exists_forall_le_order_sub (f := fun n ↦ (u n).val i) (fun n ↦ hstep n i)
  have ha₀ (i : ι) : constantCoeff (a i) = 0 := by
    have h := one_le_order_iff_constCoeff_eq_zero.mp (ha i 1)
    simpa only [map_sub, (u 1).prop i, sub_zero] using h
  let x : {a : ι → MvPowerSeries σ R // ∀ i, constantCoeff (a i) = 0} := ⟨a, ha₀⟩
  have hsep {b c : {a : ι → MvPowerSeries σ R // ∀ i, constantCoeff (a i) = 0}}
      (h : ∀ (n : ℕ) i, (n : ℕ∞) ≤ (b.val i - c.val i).order) : b = c := by
    apply Subtype.ext
    funext i
    apply sub_eq_zero.mp
    apply order_eq_top_iff.mp
    exact top_le_iff.mp (ENat.forall_natCast_le_iff_le.mp fun n _ ↦ h n i)
  have hx : F x = x := by
    apply hsep
    intro n i
    have h₁ := hF (a := x) (b := u n) (fun j ↦ ha j n) i
    have h₂ := ha i (n + 1)
    rw [hsucc] at h₂
    have he : (F x).val i - x.val i =
        ((F x).val i - (F (u n)).val i) - (x.val i - (F (u n)).val i) := by abel
    rw [he]
    have hn : (n : ℕ∞) ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast n.le_succ
    exact le_order_sub (hn.trans h₁) (hn.trans h₂)
  refine ⟨x, hx, fun y hy ↦ hsep ?_⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih => simpa only [hy, hx] using hF (a := y) (b := x) ih

end Ring

section CommRing

variable [CommRing R]

/-- A finite tuple of coordinate series agreeing with the variables in degrees zero and one
has a unique zero-constant solution to each zero-constant substitution equation. This applies
to the formal group inverse construction of Stix §10.2.2. -/
theorem existsUnique_subst_eq_of_two_le_order_sub_X [Finite σ] (f : σ → MvPowerSeries σ R)
    (hf : ∀ i, (2 : ℕ∞) ≤ (f i - X i).order) (q : σ → MvPowerSeries τ R)
    (hq : ∀ i, constantCoeff (q i) = 0) :
    ∃! a : {a : σ → MvPowerSeries τ R // ∀ i, constantCoeff (a i) = 0},
      ∀ i, substAlgHom (hasSubst_of_constantCoeff_zero a.prop) (f i) = q i := by
  let F (a : {a : σ → MvPowerSeries τ R // ∀ i, constantCoeff (a i) = 0}) :
      {a : σ → MvPowerSeries τ R // ∀ i, constantCoeff (a i) = 0} :=
    ⟨fun i ↦ q i - (f i - X i).subst a.val, fun i ↦ by
      have hzero := constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero a.prop) a.prop
        (constantCoeff_eq_zero_of_le_order (by decide) (hf i))
      rw [map_sub, hq i, hzero, sub_zero]⟩
  have hcontract {a b : {a : σ → MvPowerSeries τ R // ∀ i, constantCoeff (a i) = 0}}
      {n : ℕ} (h : ∀ i, (n : ℕ∞) ≤ (a.val i - b.val i).order) (i : σ) :
      ((n + 1 : ℕ) : ℕ∞) ≤ ((F a).val i - (F b).val i).order := by
    have ha := hasSubst_of_constantCoeff_zero a.prop
    have hb := hasSubst_of_constantCoeff_zero b.prop
    have he : (F a).val i - (F b).val i =
        -((f i - X i).subst a.val - (f i - X i).subst b.val) := by
      dsimp only [F]
      abel
    rw [he, order_neg]
    have hn : n + 2 - 1 = n + 1 := by omega
    simpa only [hn] using le_order_subst_sub_subst (hf i) ha hb a.prop b.prop h
  have hsolve (a : {a : σ → MvPowerSeries τ R // ∀ i, constantCoeff (a i) = 0}) :
      F a = a ↔ ∀ i, substAlgHom (hasSubst_of_constantCoeff_zero a.prop) (f i) = q i := by
    rw [Subtype.ext_iff, funext_iff]
    apply forall_congr'
    intro i
    have ha := hasSubst_of_constantCoeff_zero a.prop
    have he : (F a).val i = a.val i + (q i - (f i).subst a.val) := by
      dsimp only [F]
      rw [subst_sub ha, subst_X ha]
      abel
    rw [he, add_eq_left, sub_eq_zero, substAlgHom_apply, eq_comm]
  obtain ⟨a, ha, huniq⟩ := existsUnique_fixedPoint_of_order_sub F (fun h i ↦ hcontract h i)
  exact ⟨a, (hsolve a).mp ha, fun b hb ↦ huniq b ((hsolve b).mpr hb)⟩

end CommRing

end MvPowerSeries
