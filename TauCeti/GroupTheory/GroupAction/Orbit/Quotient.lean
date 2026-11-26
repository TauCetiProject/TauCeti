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
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Tactic.Group
import TauCeti.GroupTheory.GroupAction.Orbit.Basic
import TauCeti.GroupTheory.QuotientGroup.Basic

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
* `Subgroup.apply_conj_pow_minimalPeriod_conjOrbitEquiv`: a `U`-conjugation-invariant function
  takes the same value on the monodromy of `r⁻¹ * g * r` at `ω` and on the monodromy of `g` at
  `MulAction.conjOrbitEquiv g r ω`, for any choice of coset representatives.
-/

public section

namespace Subgroup

/-- **Coset monodromy lies in the subgroup.** If `r` represents the left coset `q : G ⧸ U`,
then `r⁻¹ * g ^ Function.minimalPeriod (g • ·) q * r` lies in `U`. -/
theorem conj_pow_minimalPeriod_mem {G : Type*} [Group G] (U : Subgroup G) (g : G)
    {q : G ⧸ U} {r : G} (hr : (QuotientGroup.mk r : G ⧸ U) = q) :
    r⁻¹ * g ^ Function.minimalPeriod (g • ·) q * r ∈ U := by
  rw [← TauCeti.smul_quotientGroup_mk_eq_self_iff, hr, ← MulAction.period_eq_minimalPeriod]
  exact MulAction.pow_period_smul g q

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
  have hqk' : g ^ k • qy = qx := by rwa [Subgroup.smul_def] at hqk
  have hm : Function.minimalPeriod (g • ·) qx = Function.minimalPeriod (g • ·) qy := by
    rw [← hqk']
    simpa [(Commute.zpow_self g k).eq] using MulAction.minimalPeriod_conj_smul g (g ^ k) qy
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

/-- The representative of `MulAction.conjOrbitEquiv g r ω` lies in the `⟨g⟩`-orbit of
`r • ω.out`. -/
theorem orbitRel_smul_out_conjOrbitEquiv_out {G α : Type*} [Group G] [MulAction G α] (g r : G)
    (ω : orbitRel.Quotient (Subgroup.zpowers (r⁻¹ * g * r)) α) :
    orbitRel (Subgroup.zpowers g) α (r • ω.out) (conjOrbitEquiv g r ω).out := by
  have hq : conjOrbitEquiv g r ω = Quotient.mk'' (r • ω.out) := by
    conv_lhs => rw [← Quotient.out_eq ω]
    exact conjOrbitEquiv_mk g r ω.out
  exact Quotient.exact' (hq.symm.trans (Quotient.out_eq _).symm)

end MulAction

namespace Subgroup

/-- **Monodromy under conjugation.** For coset representatives `t : G ⧸ U → G`, a
`U`-conjugation-invariant function `f : U → R` takes the same value on the coset monodromy of
`r⁻¹ * g * r` at an orbit `ω` and on the coset monodromy of `g` at the orbit
`MulAction.conjOrbitEquiv g r ω`. -/
theorem apply_conj_pow_minimalPeriod_conjOrbitEquiv {R G : Type*} [Group G] {U : Subgroup G}
    {f : U → R} (hf : ∀ u v : U, f (v * u * v⁻¹) = f u) (t : G ⧸ U → G)
    (ht : ∀ q, (QuotientGroup.mk (t q) : G ⧸ U) = q) (g r : G)
    (ω : MulAction.orbitRel.Quotient (zpowers (r⁻¹ * g * r)) (G ⧸ U)) :
    f ⟨(t ω.out)⁻¹ * (r⁻¹ * g * r) ^ Function.minimalPeriod ((r⁻¹ * g * r) • ·) ω.out * t ω.out,
        conj_pow_minimalPeriod_mem U (r⁻¹ * g * r) (ht ω.out)⟩ =
      f ⟨(t (MulAction.conjOrbitEquiv g r ω).out)⁻¹ *
          g ^ Function.minimalPeriod (g • ·) (MulAction.conjOrbitEquiv g r ω).out *
          t (MulAction.conjOrbitEquiv g r ω).out,
        conj_pow_minimalPeriod_mem U g (ht _)⟩ := by
  have hrep : (QuotientGroup.mk (r * t ω.out) : G ⧸ U) = r • ω.out := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, ht]
  refine Eq.trans ?_ (apply_conj_pow_minimalPeriod_eq_of_orbitRel hf g
    (MulAction.orbitRel_smul_out_conjOrbitEquiv_out g r ω) hrep (ht _)).symm
  congr 1
  apply Subtype.ext
  dsimp only
  have hm : Function.minimalPeriod ((r⁻¹ * g * r) • ·) ω.out =
      Function.minimalPeriod (g • ·) (r • ω.out) := by
    simpa [inv_inv, inv_smul_smul] using
      (MulAction.minimalPeriod_conj_smul g r⁻¹ (r • ω.out))
  have hp : (r⁻¹ * g * r) ^ Function.minimalPeriod (g • ·) (r • ω.out) =
      r⁻¹ * g ^ Function.minimalPeriod (g • ·) (r • ω.out) * r := by
    simpa [inv_inv] using (conj_pow (a := r⁻¹) (b := g))
  rw [hm, hp]
  simp [mul_assoc]

end Subgroup
