/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Group

/-!
# Orbit monodromy on coset spaces and conjugate cyclic actions

This file collects orbit-quotient utilities for cyclic actions: monodromy elements around `g`-orbits
on a left-coset space `G ⧸ U` and conjugacy equivalences between `⟨r⁻¹ * g * r⟩`-orbits and
`⟨g⟩`-orbits.

## Main results

* `Subgroup.conj_pow_minimalPeriod_mem`: if `r` represents `q : G ⧸ U`, then
  `r⁻¹ * g ^ Function.minimalPeriod (g • ·) q * r ∈ U`.
* `Subgroup.apply_conj_pow_minimalPeriod_eq_of_orbitRel`: any `U`-conjugation-invariant function
  assigns the same value to the monodromy elements at any two representatives of the same
  `⟨g⟩`-orbit on `G ⧸ U`.
* `MulAction.conjOrbitEquiv`: the canonical bijection between the orbits of `⟨r⁻¹ * g * r⟩` and
  the orbits of `⟨g⟩`, induced by left multiplication by `r`.
-/

public section

namespace Subgroup

/-- **Coset monodromy lies in the subgroup.** If `r` represents the left coset `q : G ⧸ U`,
then `r⁻¹ * g ^ Function.minimalPeriod (g • ·) q * r` lies in `U`. -/
theorem conj_pow_minimalPeriod_mem {G : Type*} [Group G] (U : Subgroup G) (g : G)
    {q : G ⧸ U} {r : G} (hr : (QuotientGroup.mk r : G ⧸ U) = q) :
    r⁻¹ * g ^ Function.minimalPeriod (g • ·) q * r ∈ U := by
  have hper : g ^ Function.minimalPeriod (g • ·) q • q = q := by
    rw [← smul_iterate_apply]
    exact Function.isPeriodicPt_minimalPeriod (g • ·) q
  have hmk : (QuotientGroup.mk (g ^ Function.minimalPeriod (g • ·) q * r) : G ⧸ U) =
      g ^ Function.minimalPeriod (g • ·) q • (QuotientGroup.mk r : G ⧸ U) :=
    rfl
  rw [mul_assoc, ← QuotientGroup.eq, hr, hmk, hr, eq_comm]
  exact hper

/-- **Monodromy orbit invariance.** A `U`-conjugation-invariant function `f : U → R` takes the
same value on the coset monodromy elements attached to any two points `qx, qy : G ⧸ U` in the same
`⟨g⟩`-orbit and any representatives `rx, ry : G` of `qx, qy`. -/
theorem apply_conj_pow_minimalPeriod_eq_of_orbitRel {R G : Type*} [Group G] {U : Subgroup G}
    {f : U → R} (hf : ∀ u v : U, f (v * u * v⁻¹) = f u) (g : G) {qx qy : G ⧸ U}
    (horb : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ U) qx qy) {rx ry : G}
    (hrx : (QuotientGroup.mk rx : G ⧸ U) = qx) (hry : (QuotientGroup.mk ry : G ⧸ U) = qy) :
    f ⟨ry⁻¹ * g ^ Function.minimalPeriod (g • ·) qy * ry, conj_pow_minimalPeriod_mem U g hry⟩ =
      f ⟨rx⁻¹ * g ^ Function.minimalPeriod (g • ·) qx * rx,
        conj_pow_minimalPeriod_mem U g hrx⟩ := by
  obtain ⟨⟨_, k, rfl⟩, hqk⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp horb)
  have hqk' : g ^ k • qy = qx := hqk
  have hm : Function.minimalPeriod (g • ·) qx = Function.minimalPeriod (g • ·) qy := by
    have hsc : Function.Semiconj ((g ^ k) • ·) (g • ·) (g • ·) := fun z : G ⧸ U ↦ calc
      (g ^ k) • (g • z) = (g ^ k * g) • z := (mul_smul (g ^ k) g z).symm
      _ = (g * g ^ k) • z := by rw [(Commute.zpow_self g k).eq]
      _ = g • ((g ^ k) • z) := mul_smul g (g ^ k) z
    rw [← hqk']
    refine Function.minimalPeriod_eq_minimalPeriod_iff.mpr fun n ↦ ?_
    simp only [Function.IsPeriodicPt, Function.IsFixedPt, ← (hsc.iterate_right n).eq]
    exact (MulAction.injective (g ^ k)).eq_iff
  have hvmem : rx⁻¹ * (g ^ k * ry) ∈ U := by
    have hmk : (QuotientGroup.mk (g ^ k * ry) : G ⧸ U) =
        g ^ k • (QuotientGroup.mk ry : G ⧸ U) := rfl
    rw [← QuotientGroup.eq, hrx, ← hqk', ← hry, hmk]
  let v : U := ⟨rx⁻¹ * (g ^ k * ry), hvmem⟩
  have hconj :
      (⟨ry⁻¹ * g ^ Function.minimalPeriod (g • ·) qy * ry,
          conj_pow_minimalPeriod_mem U g hry⟩ : U) =
        v⁻¹ * ⟨rx⁻¹ * g ^ Function.minimalPeriod (g • ·) qx * rx,
          conj_pow_minimalPeriod_mem U g hrx⟩ * v := by
    apply Subtype.ext
    -- Express both monodromies in terms of group words and commute `g ^ k` past `g ^ m`.
    change ry⁻¹ * g ^ Function.minimalPeriod (g • ·) qy * ry =
      (rx⁻¹ * (g ^ k * ry))⁻¹ * (rx⁻¹ * g ^ Function.minimalPeriod (g • ·) qx * rx) *
        (rx⁻¹ * (g ^ k * ry))
    have hcomm : g ^ k * g ^ Function.minimalPeriod (g • ·) qy =
        g ^ Function.minimalPeriod (g • ·) qy * g ^ k := by
      rw [← zpow_natCast g, (Commute.zpow_zpow_self g k _).eq]
    rw [hm]
    calc
      ry⁻¹ * g ^ Function.minimalPeriod (g • ·) qy * ry =
          ry⁻¹ * (g ^ k)⁻¹ * (g ^ k * g ^ Function.minimalPeriod (g • ·) qy) * ry := by
        group
      _ = ry⁻¹ * (g ^ k)⁻¹ * (g ^ Function.minimalPeriod (g • ·) qy * g ^ k) * ry := by
        rw [hcomm]
      _ = (rx⁻¹ * (g ^ k * ry))⁻¹ * (rx⁻¹ * g ^ Function.minimalPeriod (g • ·) qy * rx) *
          (rx⁻¹ * (g ^ k * ry)) := by
        group
  rw [hconj]
  simpa using hf ⟨rx⁻¹ * g ^ Function.minimalPeriod (g • ·) qx * rx,
    conj_pow_minimalPeriod_mem U g hrx⟩ v⁻¹

end Subgroup

namespace MulAction

/-- **Conjugate orbit equivalence.** Acting by `r` gives an equivalence from `⟨r⁻¹ * g * r⟩`-orbits
to `⟨g⟩`-orbits on any `G`-action. -/
noncomputable def conjOrbitEquiv {G α : Type*} [Group G] [MulAction G α] (g r : G) :
    orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) α ≃
      orbitRel.Quotient (Subgroup.zpowers g) α :=
  Quotient.congr (toPerm r) fun x y ↦ by
    have hconj : ∀ k : ℤ, r • ((r⁻¹ * g * r) ^ k • y) = g ^ k • (r • y) := fun k ↦ by
      have hpow : (r⁻¹ * g * r) ^ k = r⁻¹ * g ^ k * r := by
        simpa [inv_inv] using (conj_zpow (i := k) (a := r⁻¹) (b := g))
      rw [hpow, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    simp only [orbitRel_apply, mem_orbit_iff, toPerm_apply]
    constructor
    · rintro ⟨⟨_, k, rfl⟩, rfl⟩
      exact ⟨⟨g ^ k, k, rfl⟩, (hconj k).symm⟩
    · rintro ⟨⟨_, k, rfl⟩, h⟩
      refine ⟨⟨(r⁻¹ * g * r) ^ k, k, rfl⟩, (toPerm r).injective ?_⟩
      exact (hconj k).trans h

/-- Evaluating `MulAction.conjOrbitEquiv` on an orbit class translates the representative by `r`. -/
@[simp]
theorem conjOrbitEquiv_mk {G α : Type*} [Group G] [MulAction G α] (g r : G) (x : α) :
    conjOrbitEquiv g r (Quotient.mk (orbitRel (Subgroup.zpowers (r⁻¹ * g * r)) α) x) =
      Quotient.mk (orbitRel (Subgroup.zpowers g) α) (r • x) := by
  rfl

end MulAction
