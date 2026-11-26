/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
import TauCeti.NumberTheory.Padics.Module

/-!
# Closed subgroups of the additive group of p-adic integers

The closed subgroups of `ℤ_p` are ideals. Every nonzero one is a level `p ^ n ℤ_p`,
and multiplication by `p ^ n` identifies `ℤ_p` with that level as a topological group.
-/

public section

open Multiplicative

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- Every nontrivial closed subgroup of the additive group of `ℤ_p` is a level `p ^ n ℤ_p`. -/
theorem _root_.Subgroup.exists_eq_padicIntLevel_of_isClosed
    (H : Subgroup (Multiplicative ℤ_[p])) (hH : IsClosed (H : Set (Multiplicative ℤ_[p])))
    (hne : H ≠ ⊥) : ∃ n : ℕ, H = (padicIntLevel p n).toSubgroup := by
  let A : ClosedAddSubgroup ℤ_[p] :=
    ⟨AddSubgroup.toSubgroup.symm H, hH.preimage continuous_ofAdd⟩
  let I : Ideal ℤ_[p] := (A.toPadicIntSubmodule p).toSubmodule
  have hmem (x : Multiplicative ℤ_[p]) : x ∈ H ↔ x.toAdd ∈ I :=
    (A.mem_toPadicIntSubmodule p (x := x.toAdd)).symm
  have hI : I ≠ ⊥ := by
    intro h
    apply hne
    ext x
    rw [Subgroup.mem_bot, hmem, h, Ideal.mem_bot, toAdd_eq_zero]
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hI
  refine ⟨n, ?_⟩
  ext x
  rw [hmem, hn, Ideal.mem_span_singleton]
  exact (mem_padicIntLevel_iff p n).symm

private noncomputable def padicIntLevelMulHom (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Multiplicative ℤ_[p] →* ↥(padicIntLevel p n) :=
  (AddMonoidHom.mulLeft ((p : ℤ_[p]) ^ n)).toMultiplicative.codRestrict
    (padicIntLevel p n).toSubgroup fun x ↦ (mem_padicIntLevel_iff p n).2 (dvd_mul_right _ x.toAdd)

/-- Multiplication by `p ^ n` gives the topological group isomorphism onto `p ^ n ℤ_p`. -/
noncomputable def padicIntLevelMulEquiv (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Multiplicative ℤ_[p] ≃ₜ* ↥(padicIntLevel p n) := by
  let f := padicIntLevelMulHom p n
  have hcont : Continuous f :=
    (continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)).subtype_mk _
  have hn : (p : ℤ_[p]) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hinj : Function.Injective f := by
    intro x y h
    have hmul := congrArg (fun z : ↥(padicIntLevel p n) ↦ z.val.toAdd) h
    exact ofAdd.symm.injective (mul_left_cancel₀ hn hmul)
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (mem_padicIntLevel_iff p n).1 y.property
    exact ⟨ofAdd x, Subtype.ext (ofAdd.symm.injective hx.symm)⟩
  let e := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  exact ⟨e, hcont, hcont.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv)⟩

@[simp]
theorem coe_padicIntLevelMulEquiv_apply (n : ℕ) (x : Multiplicative ℤ_[p]) :
    (padicIntLevelMulEquiv p n x : Multiplicative ℤ_[p]) = ofAdd ((p : ℤ_[p]) ^ n * x.toAdd) :=
  (rfl)

/-- An open subgroup of the additive group of `ℤ_p` is topologically isomorphic to `ℤ_p`. -/
theorem _root_.OpenSubgroup.nonempty_continuousMulEquiv_padicInt
    (H : OpenSubgroup (Multiplicative ℤ_[p])) : Nonempty (H ≃ₜ* Multiplicative ℤ_[p]) := by
  obtain ⟨n, hn⟩ := exists_padicIntLevel_le p H
  have hne : H.toSubgroup ≠ ⊥ := by
    intro h
    have hx : ofAdd ((p : ℤ_[p]) ^ n) ∈ H.toSubgroup :=
      hn ((mem_padicIntLevel_iff p n).2 (dvd_refl _))
    rw [h, Subgroup.mem_bot, ofAdd_eq_one] at hx
    exact (pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) hx
  obtain ⟨m, hm⟩ := H.toSubgroup.exists_eq_padicIntLevel_of_isClosed H.isClosed hne
  have h : Nonempty (↥H.toSubgroup ≃ₜ* Multiplicative ℤ_[p]) := by
    rw [hm]
    exact ⟨(padicIntLevelMulEquiv p m).symm⟩
  exact h

end TauCeti
