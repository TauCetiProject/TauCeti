/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import TauCeti.Algebra.Module.ZLattice.OrthSum
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion

/-!
# Theta series of even unimodular lattices

Let `L` be an even unimodular lattice in a real inner product space `E` of dimension `n`. This
file proves that `n` is divisible by `8` and that, writing `n = 2k`, the theta series `Θ_L` is a
modular form of weight `k` for `SL(2, ℤ)`.

For a unimodular lattice `L^∨ = L` and `covol L = 1`, so the inversion law reads
`Θ_L ∣[k] S = (-i)^k Θ_L` (`ZLattice.IsUnimodular.thetaSeries_slash_S`). The rank argument is
the elementary one. If `n ≡ 4 (mod 8)`, then `k ≡ 2 (mod 4)` and `Θ_L ∣[k] S = -Θ_L`, while
`Θ_L ∣[k] T = Θ_L` because `L` is even. The relation `S³ T S T S = T⁻¹` in `SL(2, ℤ)` then
gives `-Θ_L = Θ_L`, which is impossible since `Θ_L(i) ≠ 0`. A general rank `n` reduces to this
case: the orthogonal direct sums `L ⊕ L` and `(L ⊕ L) ⊕ (L ⊕ L)` are again even unimodular, of
ranks `2n` and `4n`, and none of `n`, `2n`, `4n` being `4` modulo `8` forces `8 ∣ n`.

Once `8 ∣ n`, the factor `(-i)^k` is `1`, so `Θ_L` is invariant under both generators `S` and
`T` of `SL(2, ℤ)`; with holomorphy and boundedness at `i∞` this makes `Θ_L` a level-one modular
form, `ZLattice.thetaForm`, built as Mathlib builds `CuspForm.discriminant`.

## Main definitions

* `ZLattice.thetaForm`: the theta series of an even unimodular lattice of rank `2k`, as a modular
  form of weight `k` for `SL(2, ℤ)`.

## Main statements

* `ZLattice.IsEven.eight_dvd_finrank`: the rank of an even unimodular lattice is divisible by `8`.
* `ZLattice.IsEven.thetaSeries_slash_S`: `Θ_L ∣[k] S = Θ_L` for even unimodular `L`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, §3.2.
-/

public section

open Complex Module ModularGroup SlashInvariantForm
open scoped ModularForm MatrixGroups

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

namespace IsEven

/-- The rank of an even unimodular lattice is not `4` modulo `8`. -/
private theorem finrank_mod_eight_ne_four (hL : IsEven L) (hU : IsUnimodular L) :
    finrank ℝ E % 8 ≠ 4 := by
  intro h8
  obtain ⟨k, hk, hk4⟩ : ∃ k, finrank ℝ E = 2 * k ∧ k % 4 = 2 :=
    ⟨finrank ℝ E / 2, by omega, by omega⟩
  -- Since `k ≡ 2 (mod 4)`, the factor `(-i)^k` of the inversion law is `-1`.
  have hI : (-I) ^ k = -1 := by
    rw [← Nat.div_add_mod k 4, hk4, pow_add, pow_mul, (by decide : Even 4).neg_pow, I_pow_four]
    simp
  have hS : thetaSeries L ∣[(k : ℤ)] S = -thetaSeries L := by
    rw [hU.thetaSeries_slash_S hk, hI, neg_one_smul]
  have hT := hL.thetaSeries_slash_T (k : ℤ)
  -- `T⁻¹ = S³ T S T S` acts on `Θ_L` by `(-1)^5 = -1`, and also trivially.
  have h : -thetaSeries L = thetaSeries L := by
    calc -thetaSeries L = thetaSeries L ∣[(k : ℤ)] (S • S • S • T • S • T • S) := by
          simp [smul_eq_mul, SlashAction.slash_mul, hS, hT, SlashAction.neg_slash]
      _ = thetaSeries L := by
          rw [T_S_rel]
          conv_lhs => rw [← hT, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  have hi := congrFun h UpperHalfPlane.I
  rw [Pi.neg_apply] at hi
  exact thetaSeries_ne_zero_of_re_eq_zero L UpperHalfPlane.I_re
    (by linear_combination (-1 / 2 : ℂ) * hi)

/-- **The rank of an even unimodular lattice is divisible by `8`.** -/
theorem eight_dvd_finrank (hL : IsEven L) (hU : IsUnimodular L) : 8 ∣ finrank ℝ E := by
  have hL₂ : IsEven (orthSum L L) := isEven_orthSum_iff.2 ⟨hL, hL⟩
  have hU₂ : IsUnimodular (orthSum L L) := isUnimodular_orthSum_iff.2 ⟨hU, hU⟩
  have h₁ := hL.finrank_mod_eight_ne_four hU
  have h₂ := hL₂.finrank_mod_eight_ne_four hU₂
  have h₄ := (isEven_orthSum_iff.2 ⟨hL₂, hL₂⟩).finrank_mod_eight_ne_four
    (isUnimodular_orthSum_iff.2 ⟨hU₂, hU₂⟩)
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, finrank_prod] at h₂ h₄
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, finrank_prod] at h₄
  omega

/-- **The inversion law of an even unimodular lattice**: if `L` is even unimodular and
`dim E = 2k`, then `Θ_L ∣[k] S = Θ_L`. -/
theorem thetaSeries_slash_S (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k) :
    thetaSeries L ∣[(k : ℤ)] S = thetaSeries L := by
  obtain ⟨m, rfl⟩ : 4 ∣ k := by have := hL.eight_dvd_finrank hU; omega
  rw [hU.thetaSeries_slash_S hk, pow_mul, (by decide : Even 4).neg_pow, I_pow_four]
  simp

end IsEven

/-- **The theta series of an even unimodular lattice is a level-one modular form**: if `L` is
even unimodular and `dim E = 2k`, then `Θ_L` is a modular form of weight `k` for `SL(2, ℤ)`. Its
coercion is `thetaSeries L` (`ZLattice.coe_thetaForm`). -/
noncomputable def thetaForm (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k) :
    ModularForm 𝒮ℒ k where
  toFun := thetaSeries L
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z (hL.thetaSeries_slash_S hU hk) (hL.thetaSeries_slash_T _) A
  holo' := mdifferentiable_thetaSeries L
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦ by
    rw [slash_action_generators_SL2Z (hL.thetaSeries_slash_S hU hk) (hL.thetaSeries_slash_T _)]
    exact isBoundedAtImInfty_thetaSeries L

/-- The coercion of `ZLattice.thetaForm` to a function is the theta series. -/
@[simp]
theorem coe_thetaForm (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k) :
    ⇑(thetaForm hL hU hk) = thetaSeries L :=
  (rfl)

end ZLattice
