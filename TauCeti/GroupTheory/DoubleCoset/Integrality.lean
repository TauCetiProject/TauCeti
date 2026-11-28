/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import TauCeti.GroupTheory.DoubleCoset.ClassSum

/-!
# Clearing stabilizer denominators in class sums

A class sum weights each double coset by the reciprocal of its stabilizer order. A common
multiple clears those denominators, so values in an additive subgroup give a scaled class sum
in the same subgroup. For a pairing in integral matrix coordinates, integrality of the first
vector at the conjugate embedding and the second at the given embedding puts the scaled
pairing in the nonarchimedean unit ball.

The class-sum integrality statements follow `New.weylGauge_classSum_le_one` and
`New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one` in `Lib/Adelic/AutomorphicForms/PAdicGauge.lean`
of lsernau/grh-lean (revision `72fead1`).
-/

public section

open Matrix

namespace TauCeti

variable {G : Type*} [Group G] {Γ K : Subgroup G}

/-- After multiplication by a common multiple of the stabilizer orders, the class sum uses
natural multiplicities instead of rational weights. An infinite stabilizer contributes zero
on both sides, under the `Nat.card` and division-by-zero conventions. -/
theorem nsmul_doubleCosetClassSum_eq_finsum {W : Type*} [AddCommGroup W] [Module ℚ W]
    (f : G → W) {A : ℕ}
    (hA : ∀ q : DoubleCoset.Quotient (Γ : Set G) K, 0 < Nat.card (mackeySubgroup q.out K Γ) →
      Nat.card (mackeySubgroup q.out K Γ) ∣ A) :
    A • doubleCosetClassSum Γ K f = ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) K,
      (A / Nat.card (mackeySubgroup q.out K Γ)) • f q.out := by
  rw [doubleCosetClassSum_def, ← Nat.cast_smul_eq_nsmul ℚ, smul_finsum]
  refine finsum_congr fun q ↦ ?_
  let d := Nat.card (mackeySubgroup q.out K Γ)
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have hzero : Nat.card (mackeySubgroup q.out K Γ) = 0 := hd
    simp only [hzero, Nat.cast_zero, inv_zero, zero_smul, smul_zero, Nat.div_zero]
  · obtain ⟨b, hb⟩ := hA q hd
    have hb' : A = d * b := hb
    have hdiv : A / d = b := by rw [hb', Nat.mul_div_cancel_left _ hd]
    rw [hdiv, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hb', Nat.cast_mul]
    have hdQ : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    rw [mul_comm (d : ℚ), mul_assoc, mul_inv_cancel₀ hdQ, mul_one]

/-- A common multiple of the stabilizer orders makes the class sum preserve membership in an
additive subgroup. Only values at the representatives used in the sum need to be tested. -/
theorem nsmul_doubleCosetClassSum_mem {W : Type*} [AddCommGroup W] [Module ℚ W]
    (S : AddSubgroup W) {f : G → W} {A : ℕ}
    (hA : ∀ q : DoubleCoset.Quotient (Γ : Set G) K, 0 < Nat.card (mackeySubgroup q.out K Γ) →
      Nat.card (mackeySubgroup q.out K Γ) ∣ A)
    (hf : ∀ q : DoubleCoset.Quotient (Γ : Set G) K, f q.out ∈ S) :
    A • doubleCosetClassSum Γ K f ∈ S := by
  rw [nsmul_doubleCosetClassSum_eq_finsum f hA]
  let F (q : DoubleCoset.Quotient (Γ : Set G) K) : S :=
    (A / Nat.card (mackeySubgroup q.out K Γ)) • ⟨f q.out, hf q⟩
  have h := S.subtype.map_finsum_of_injective Subtype.val_injective F
  exact h ▸ (∑ᶠ q, F q).property

/-- An integral coefficient matrix pairs vectors integral at conjugate embeddings to give an
integral class sum after clearing the stabilizer denominators. The first vector is tested after
complex conjugation because the pairing is conjugate-linear in that variable. -/
theorem norm_map_nsmul_doubleCosetClassSum_dotProduct_mulVec_le_one
    {ι κ L : Type*} [Fintype ι] [Fintype κ] [SeminormedRing L] [IsUltrametricDist L]
    (e : ℂ →+* L) (B : Matrix ι κ ℤ) {u : G → ι → ℂ} {v : G → κ → ℂ} {A : ℕ}
    (hA : ∀ q : DoubleCoset.Quotient (Γ : Set G) K, 0 < Nat.card (mackeySubgroup q.out K Γ) →
      Nat.card (mackeySubgroup q.out K Γ) ∣ A)
    (hu : ∀ (q : DoubleCoset.Quotient (Γ : Set G) K) i, ‖e (star (u q.out i))‖ ≤ 1)
    (hv : ∀ (q : DoubleCoset.Quotient (Γ : Set G) K) j, ‖e (v q.out j)‖ ≤ 1) :
    ‖e (A • doubleCosetClassSum Γ K
      (fun g ↦ (fun i ↦ star (u g i)) ⬝ᵥ (B.map (Int.castRingHom ℂ) *ᵥ v g)))‖ ≤ 1 := by
  let ball : AddSubgroup L := IsUltrametricDist.closedBall_openAddSubgroup L one_pos
  let S := ball.comap e.toAddMonoidHom
  have mem_S (x : ℂ) : x ∈ S ↔ ‖e x‖ ≤ 1 := by
    -- Expose the metric ball carrier, which is bundled as an open additive subgroup.
    change e x ∈ Metric.closedBall 0 1 ↔ _
    rw [Metric.mem_closedBall, dist_zero_right]
  refine (mem_S _).mp (nsmul_doubleCosetClassSum_mem S hA fun q ↦ ?_)
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine S.sum_mem fun i _ ↦ S.sum_mem fun j _ ↦ ?_
  have hprod : star (u q.out i) * v q.out j ∈ S := by
    rw [mem_S, map_mul]
    have hmul := mul_le_mul (hu q i) (hv q j) (norm_nonneg _) zero_le_one
    exact (norm_mul_le _ _).trans (by simpa only [mul_one] using hmul)
  have hcast : (B.map (Int.castRingHom ℂ)) i j = (B i j : ℂ) := rfl
  rw [hcast, mul_left_comm, ← zsmul_eq_mul]
  exact S.zsmul_mem hprod (B i j)

end TauCeti
