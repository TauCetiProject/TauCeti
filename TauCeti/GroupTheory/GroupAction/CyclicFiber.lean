/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.QuotientGroup
import TauCeti.Algebra.Group.Subgroup.CyclicKernel
import TauCeti.Algebra.Group.Subgroup.ZPowers

/-!
# Cyclic orbits restricted to a fiber

If an involution and a stabilizer generator have the same nontrivial image under a
homomorphism, multiplying the generator by the involution gives a cyclic description
of the lifts of the point and its involutive partner in the kernel.
A further homomorphism cuts out a cyclic orbit with a larger step.
-/

public section

namespace MulAction

open Subgroup

/-- In the kernel of `r`, the elements taking `P` to either `P` or `c • P` are precisely
powers of `c * g`, when `g` generates the stabilizer and has the same nontrivial image as the
commuting involution `c`. -/
theorem mem_zpowers_mul_iff_smul_eq_or {G H X : Type*} [Group G] [Group H] [MulAction G X]
    (r : G →* H) {P : X} {c g y : G} (hstab : zpowers g = stabilizer G P)
    (hc : c ^ 2 = 1) (hcomm : Commute c g) (hr : r c = r g) (hrc : r c ≠ 1) :
    y ∈ zpowers (c * g) ↔ r y = 1 ∧ (y • P = P ∨ y • P = c • P) := by
  have hstep : r (c * g) = 1 := by
    rw [map_mul, ← hr, ← sq, ← map_pow, hc, map_one]
  have hpower (n : ℤ) : g ^ n • P = P := by
    rw [← mem_stabilizer_iff, ← hstab]
    exact zpow_mem_zpowers g n
  constructor
  · rintro hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨by simp [hstep], ?_⟩
    rw [hcomm.mul_zpow, mul_smul, hpower]
    rcases (mem_zpowers_iff_of_sq_eq_one hc).mp (zpow_mem_zpowers c n) with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by rw [h])
  · rintro ⟨hy, hyP⟩
    have hprod : ∀ {a : G}, r a = 1 → a • P = P → a ∈ zpowers (c * g) := by
      intro a ha haP
      rw [← mem_stabilizer_iff, ← hstab] at haP
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp haP
      have hcn : c ^ n = 1 := by
        rcases (mem_zpowers_iff_of_sq_eq_one hc).mp (zpow_mem_zpowers c n) with h | h
        · exact h
        · exact (hrc (by rwa [← h, map_zpow, hr, ← map_zpow])).elim
      exact mem_zpowers_iff.mpr ⟨n, by rw [hcomm.mul_zpow, hcn, one_mul]⟩
    rcases hyP with h | h
    · exact hprod hy h
    have hgy : (g⁻¹ * c * y) • P = P := by
      rw [mul_smul, mul_smul, h, ← mul_smul c c, ← sq, hc, one_smul, ← zpow_neg_one]
      exact hpower (-1)
    have hz := hprod (a := g⁻¹ * c * y) (by simp [hr, hy]) hgy
    have hcancel : (c * g) * (g⁻¹ * c * y) = y := by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc, ← sq, hc, one_mul]
    exact hcancel ▸ (zpowers (c * g)).mul_mem (mem_zpowers (c * g)) hz

/-- Restrict the lifts of a point and its involutive partner to the identity fibers of two
homomorphisms. Starting at `τ`, the labels in the restricted orbit are indexed without
repetitions by the cyclic group of order `orderOf v`, with step
`v = (c * g) ^ orderOf (f (c * g))`. -/
theorem exists_zmod_cycle_fiber {G H J X : Type*} [Group G] [Group H] [Group J] [MulAction G X]
    (r : G →* H) (f : G →* J) {P : X} {c g τ : G} (hstab : zpowers g = stabilizer G P)
    (hc : c ^ 2 = 1) (hcomm : Commute c g) (hr : r c = r g) (hrc : r c ≠ 1)
    (hτr : r τ = 1) (hτf : f τ = 1) :
    let v := (c * g) ^ orderOf (f (c * g))
    ∃ t : ZMod (orderOf v) → G, Function.Injective t ∧ t 0 = τ ∧
      (∀ i, t (i + 1) = v * t i) ∧
      Set.range t = {y | r y = 1 ∧ f y = 1 ∧
        ((y * τ⁻¹) • P = P ∨ (y * τ⁻¹) • P = c • P)} := by
  dsimp only
  let v := (c * g) ^ orderOf (f (c * g))
  have hperiod : Function.minimalPeriod (v • ·) τ = orderOf v := by
    rw [orderOf, Function.minimalPeriod_eq_minimalPeriod_iff]
    intro n
    rw [isPeriodicPt_smul_iff, isPeriodicPt_mul_iff_pow_eq_one, smul_eq_mul]
    exact ⟨fun h ↦ mul_right_cancel (h.trans (one_mul τ).symm), fun h ↦ by simp [h]⟩
  let e : ZMod (orderOf v) ≃ orbit (zpowers v) τ :=
    (Equiv.cast (congrArg ZMod hperiod.symm)).trans (orbitZPowersEquiv v τ).symm
  let t : ZMod (orderOf v) → G := fun i ↦ e i
  have hval (i : ℤ) : t (i : ZMod (orderOf v)) = v ^ i * τ := by
    have hcast {m n : ℕ} (h : m = n) : (Equiv.cast (congrArg ZMod h)) (i : ZMod m) =
        (i : ZMod n) := by subst n; rfl
    simp only [t, e, Equiv.trans_apply]
    rw [hcast hperiod.symm, orbitZPowersEquiv_symm_apply']
    rfl
  refine ⟨t, fun a b hab ↦ e.injective (Subtype.ext hab), ?_, ?_, ?_⟩
  · simpa using hval 0
  · intro i
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective i
    rw [← Int.cast_one, ← Int.cast_add, hval, hval, zpow_add, zpow_one]
    rw [← mul_assoc, (Commute.refl v).zpow_left _ |>.eq]
  · have hmem (y : G) : y ∈ zpowers v ↔
        r y = 1 ∧ f y = 1 ∧ (y • P = P ∨ y • P = c • P) := by
      rw [show zpowers v = zpowers (c * g) ⊓ f.ker from (zpowers_inf_ker_eq f _).symm,
        mem_inf, mem_zpowers_mul_iff_smul_eq_or r hstab hc hcomm hr hrc, MonoidHom.mem_ker]
      tauto
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := mem_orbit_iff.mp (e i).property
      have h := (hmem _).mp a.property
      have hit : t i = (a : G) * τ := ha.symm
      simpa [hit, hτr, hτf, mul_assoc] using h
    · intro hy
      have h : y * τ⁻¹ ∈ zpowers v := (hmem _).mpr (by simpa [hτr, hτf] using hy)
      have ho : y ∈ orbit (zpowers v) τ :=
        mem_orbit_iff.mpr ⟨⟨y * τ⁻¹, h⟩, by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]⟩
      exact ⟨e.symm ⟨y, ho⟩, by simp [t]⟩

end MulAction
