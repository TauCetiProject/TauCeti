/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Chevalley.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.RingTheory.DividedPowers.RootString.G2.Signed
public import TauCeti.RingTheory.DividedPowers.RootString.G2.ShortPair
public import TauCeti.LinearAlgebra.RootSystem.Finite.G2.Coordinates
public import Mathlib.Algebra.Lie.BaseChange

/-!
# G₂ collection for the full cocharacter Chevalley algebra

The two exceptional G₂ divided-power collection rules hold in the rational enveloping
algebra of the integral Chevalley algebra on the whole cocharacter lattice. The hypotheses
are local root equations, excluded root sums and descending string lengths. Neither
irreducibility nor spanning by the coroots is required.

The integer coefficients retain the actual signs of the supplied Chevalley table, including
the highest-root sign. The associative identities are
`TauCeti.Associative.dividedPower_mul_dividedPower_of_g2_zsmul` and
`TauCeti.Associative.dividedPower_mul_dividedPower_of_g2_short_pair`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
-/

public section

open scoped TensorProduct
open TauCeti.Associative Finset

namespace RootPairing.ChevalleyLieAlgebra

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Finite ι]
  {P : RootPairing ι ℤ X Y} (c : P.ChevalleyConstants)

local notation "Lℚ" => ℚ ⊗[ℤ] ChevalleyLieAlgebra c
local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ Lℚ
local notation "e" => (fun i : ι ↦ _root_.UniversalEnvelopingAlgebra.ι ℚ
  ((1 : ℚ) ⊗ₜ[ℤ] root c i))

private theorem g2_triple_data [P.IsReduced] {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ) :
    P.chainBotCoeff α β = 0 ∧ P.chainBotCoeff δ γ = 2 ∧
      ∀ a b : ℕ,
        (a, b) ∈ ({(4, 1), (4, 2), (1, 2), (5, 2), (4, 3), (5, 3), (6, 3)} :
          Finset (ℕ × ℕ)) → a • P.root α + b • P.root β ∉ Set.range P.root := by
  have hpair := P.pairingIn_eq_neg_three_of_triple_chain hγ hδ hε
  let g : P.EmbeddedG2 := ⟨β, α, hpair⟩
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hp := P.chainBotCoeff_sub_chainTopCoeff hli
  have hb := P.chainBotCoeff_add_chainTopCoeff_le_three (i := α) (j := β)
  have hbot : P.chainBotCoeff α β = 0 := by omega
  have hli' := P.linearIndependent_of_add_mem_range_root' ⟨ζ, hζ⟩
  have htwo : 2 ≤ P.chainBotCoeff δ γ :=
    (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hli').mp
      ⟨P.reflectionPerm ε ε, by
        have hn : P.root (P.reflectionPerm ε ε) = -P.root ε := by simp
        rw [hn, hε, hδ, hγ]
        module⟩
  have hone := P.one_le_chainTopCoeff_of_root_add_mem ⟨ζ, hζ⟩
  have hlen := P.chainBotCoeff_add_chainTopCoeff_le_three (i := δ) (j := γ)
  refine ⟨hbot, by omega, ?_⟩
  intro a b hab
  have he : a • P.root α + b • P.root β ∈ Set.range P.root ↔
      ![(a : ℤ), (b : ℤ)] ∈ EmbeddedG2.allCoeffs := by
    simpa only [EmbeddedG2.shortRoot, EmbeddedG2.longRoot, EmbeddedG2.short,
      EmbeddedG2.long, g, natCast_zsmul] using
      @EmbeddedG2.smul_add_smul_mem_range_root_iff ι X Y _ _ _ P g (a : ℤ) (b : ℤ)
  rw [he]
  simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hab
  rcases hab with h | h | h | h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;> decide

private theorem g2_triple_constants {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ) :
    c.structConst α γ = 2 * (c.structConst α γ).sign ∧
      c.structConst α δ = 3 * (c.structConst α δ).sign ∧
      c.structConst δ γ = 3 * (c.structConst δ γ).sign := by
  let := c.isReduced
  obtain ⟨hbot, hbot', _⟩ := g2_triple_data hγ hδ hε hζ
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hli' := P.linearIndependent_of_add_mem_range_root' ⟨δ, hδ⟩
  have h₁ := c.natAbs_structConst hδ
  have h₂ := c.natAbs_structConst hε
  have h₃ := c.natAbs_structConst hζ
  rw [P.chainBotCoeff_of_add hli (hγ.trans (add_comm _ _)), hbot] at h₁
  rw [P.chainBotCoeff_of_add hli' (hδ.trans (add_comm _ _)),
    P.chainBotCoeff_of_add hli (hγ.trans (add_comm _ _)), hbot] at h₂
  rw [hbot'] at h₃
  have hs₁ := Int.sign_mul_natAbs (c.structConst α γ)
  have hs₂ := Int.sign_mul_natAbs (c.structConst α δ)
  have hs₃ := Int.sign_mul_natAbs (c.structConst δ γ)
  rw [h₁] at hs₁
  rw [h₂] at hs₂
  rw [h₃] at hs₃
  exact ⟨by simpa [mul_comm] using hs₁.symm,
    by simpa [mul_comm] using hs₂.symm, by simpa [mul_comm] using hs₃.symm⟩

private theorem g2_triple_commute {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ) :
    Commute (e α) (e ε) ∧ Commute (e α) (e ζ) ∧ Commute (e β) (e γ) ∧
      Commute (e δ) (e ε) ∧ Commute (e γ) (e ζ) ∧ Commute (e δ) (e ζ) ∧
      Commute (e ε) (e ζ) := by
  let := c.isReduced
  obtain ⟨_, _, hnot⟩ := g2_triple_data hγ hδ hε hζ
  have hli := P.linearIndependent_of_add_mem_range_root' ⟨γ, hγ⟩
  have hc (i j : ι) (a b : ℕ)
      (hab : (a, b) ∈ ({(4, 1), (4, 2), (1, 2), (5, 2), (4, 3), (5, 3), (6, 3)} :
        Finset (ℕ × ℕ)))
      (hs : P.root i + P.root j = a • P.root α + b • P.root β) :
      Commute (e i) (e j) := by
    apply TauCeti.UniversalEnvelopingAlgebra.commute_of_lie_eq_zero (RingHom.id U)
    have hne : P.root i + P.root j ≠ 0 := by
      intro h
      have hz := hli.eq_zero_of_pair (s := (a : ℤ)) (t := (b : ℤ))
        (by simpa only [natCast_zsmul] using hs.symm.trans h)
      simp only [mem_insert, mem_singleton, Prod.mk.injEq] at hab
      rcases hz with ⟨ha, hb⟩
      norm_cast at ha hb
      omega
    simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
      root_lie_root_of_notMem_of_add_ne_zero c (hs ▸ hnot a b hab) hne,
      TensorProduct.tmul_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc α ε 4 1 (by simp) (by simp only [hε, hδ, hγ]; module)
  · exact hc α ζ 4 2 (by simp) (by simp only [hζ, hδ, hγ]; module)
  · exact hc β γ 1 2 (by simp) (by simp only [hγ]; module)
  · exact hc δ ε 5 2 (by simp) (by simp only [hε, hδ, hγ]; module)
  · exact hc γ ζ 4 3 (by simp) (by simp only [hζ, hδ, hγ]; module)
  · exact hc δ ζ 5 3 (by simp) (by simp only [hζ, hδ, hγ]; module)
  · exact hc ε ζ 6 3 (by simp) (by simp only [hζ, hε, hδ, hγ]; module)

private theorem g2_triple_brackets {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ) :
    (e α * e β = e β * e α + c.structConst α β • e γ) ∧
      (e α * e γ = e γ * e α + 2 • ((c.structConst α γ).sign • e δ)) ∧
      (e α * e δ = e δ * e α + 3 • ((c.structConst α δ).sign • e ε)) ∧
      (e δ * e γ = e γ * e δ + 3 • ((c.structConst δ γ).sign • e ζ)) := by
  let := c.isReduced
  have hm {i j k : ι} (hk : P.root k = P.root i + P.root j) :
      e i * e j = e j * e i + c.structConst i j • e k := by
    apply TauCeti.UniversalEnvelopingAlgebra.mul_eq_mul_add_zsmul_of_lie_eq (RingHom.id U)
    simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul,
      root_lie_root_of_root_eq_add c hk, TensorProduct.tmul_smul]
  obtain ⟨hb, hd, hf⟩ := g2_triple_constants c hγ hδ hε hζ
  refine ⟨hm hγ, ?_, ?_, ?_⟩
  · have h := hm hδ
    rw [hb, mul_smul] at h
    simpa only [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_ofNat] using h
  · have h := hm hε
    rw [hd, mul_smul] at h
    simpa only [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_ofNat] using h
  · have h := hm hζ
    rw [hf, mul_smul] at h
    simpa only [← Nat.cast_smul_eq_nsmul ℤ, Nat.cast_ofNat] using h

/-- Collection in the short–long G₂ configuration. The four additional root factors are
`α + β`, `2α + β`, `3α + β` and `3α + 2β`. The last coefficient uses the sign of
`N_(2α+β,α+β)`, rather than a sign inferred from the simple-root string alone. -/
theorem dividedPower_root_mul_of_g2_triple {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ)
    (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      ∑ p ∈ chainG2Index m n,
        (c.structConst α β ^ p.1 *
          (c.structConst α β * (c.structConst α γ).sign) ^ p.2.1 *
          (c.structConst α β * (c.structConst α γ).sign *
            (c.structConst α δ).sign) ^ p.2.2.1 *
          (c.structConst α β ^ 2 * (c.structConst α γ).sign *
            (c.structConst δ γ).sign) ^ p.2.2.2) •
          (dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) (e β) *
            dividedPower p.1 (e γ) * dividedPower p.2.1 (e δ) *
            dividedPower p.2.2.1 (e ε) * dividedPower p.2.2.2 (e ζ) *
            dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) (e α)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := g2_triple_brackets c hγ hδ hε hζ
  obtain ⟨h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := g2_triple_commute c hγ hδ hε hζ
  exact dividedPower_mul_dividedPower_of_g2_zsmul _ _ _ _
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ m n

/-- Collection of the two short roots `α` and `α + β` with short sum `2α + β`.
The three correction factors lie at `2α + β`, `3α + β` and `3α + 2β`.
All signs come from the supplied table, with no normalization of its root vectors. -/
private theorem g2_short_pair_in_triple {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ)
    (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e γ) =
      ∑ p ∈ g2ShortPairIndex m n,
        ((2 ^ p.1 * 3 ^ (p.2.1 + p.2.2) : ℤ) *
          (c.structConst α γ).sign ^ p.1 *
          ((c.structConst α γ).sign * (c.structConst α δ).sign) ^ p.2.1 *
          ((c.structConst α γ).sign * (c.structConst δ γ).sign) ^ p.2.2) •
          (dividedPower (n - p.1 - p.2.1 - 2 * p.2.2) (e γ) *
            dividedPower p.1 (e δ) * dividedPower p.2.1 (e ε) *
            dividedPower p.2.2 (e ζ) *
            dividedPower (m - p.1 - 2 * p.2.1 - p.2.2) (e α)) := by
  obtain ⟨_, h₂, h₃, h₄⟩ := g2_triple_brackets c hγ hδ hε hζ
  obtain ⟨h₅, h₆, _, h₈, h₉, h₁₀, h₁₁⟩ := g2_triple_commute c hγ hδ hε hζ
  let b := (c.structConst α γ).sign
  let d := (c.structConst α δ).sign
  let f := (c.structConst δ γ).sign
  have hxz : e α * (b • e δ) = (b • e δ) * e α + 3 • ((b * d) • e ε) := by
    simp only [mul_smul_comm, smul_mul_assoc, h₃, smul_add,
      ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
    congr 2
    ring
  have hzy : (b • e δ) * e γ = e γ * (b • e δ) + 3 • ((b * f) • e ζ) := by
    simp only [mul_smul_comm, smul_mul_assoc, h₄, smul_add,
      ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
    congr 2
    ring
  rw [dividedPower_mul_dividedPower_of_g2_short_pair h₂ hxz hzy
    (h₅.smul_right (b * d)) (h₆.smul_right (b * f)) (h₉.smul_right (b * f))
    ((h₈.smul_left b).smul_right (b * d))
    ((h₁₀.smul_left b).smul_right (b * f))
    ((h₁₁.smul_left (b * d)).smul_right (b * f)) m n]
  apply sum_congr rfl
  intro p _
  simp only [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc,
    ← Nat.cast_smul_eq_nsmul ℤ, smul_smul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    b, d, f]
  congr 1
  ring

/-- Collection for two short roots with short sum, from the three local root equations.
The correction roots are `α + β`, `2α + β` and `α + 2β`. Every coefficient is an integer
with the signs of the supplied Chevalley table. Other components and the full lattice remain. -/
theorem dividedPower_root_mul_of_g2_short_pair {α β γ δ ε : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root γ + P.root β)
    (m n : ℕ) :
    dividedPower m (e α) * dividedPower n (e β) =
      ∑ p ∈ g2ShortPairIndex m n,
        ((2 ^ p.1 * 3 ^ (p.2.1 + p.2.2) : ℤ) *
          (c.structConst α β).sign ^ p.1 *
          ((c.structConst α β).sign * (c.structConst α γ).sign) ^ p.2.1 *
          ((c.structConst α β).sign * (c.structConst γ β).sign) ^ p.2.2) •
          (dividedPower (n - p.1 - p.2.1 - 2 * p.2.2) (e β) *
            dividedPower p.1 (e γ) * dividedPower p.2.1 (e δ) *
            dividedPower p.2.2 (e ε) *
            dividedPower (m - p.1 - 2 * p.2.1 - p.2.2) (e α)) := by
  let := c.isReduced
  obtain ⟨η, hη⟩ := P.exists_root_eq_sub_of_g2_short_pair hγ hδ hε
  have hβ : P.root β = P.root α + P.root η := by rw [hη]; module
  exact g2_short_pair_in_triple c hβ hγ hδ hε m n

/-- The swapped product is the leading term; every correction has strictly smaller total
sum of divided-power exponents. All correction coefficients are integers. -/
theorem dividedPower_root_mul_eq_swap_add_of_g2_triple {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ)
    (m n : ℕ) :
    (dividedPower m (e α) * dividedPower n (e β) =
      dividedPower n (e β) * dividedPower m (e α) +
        ∑ p ∈ (chainG2Index m n).erase 0,
        (c.structConst α β ^ p.1 *
          (c.structConst α β * (c.structConst α γ).sign) ^ p.2.1 *
          (c.structConst α β * (c.structConst α γ).sign *
            (c.structConst α δ).sign) ^ p.2.2.1 *
          (c.structConst α β ^ 2 * (c.structConst α γ).sign *
            (c.structConst δ γ).sign) ^ p.2.2.2) •
          (dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) (e β) *
            dividedPower p.1 (e γ) * dividedPower p.2.1 (e δ) *
            dividedPower p.2.2.1 (e ε) * dividedPower p.2.2.2 (e ζ) *
            dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) (e α))) ∧
      ∀ p ∈ (chainG2Index m n).erase 0,
        (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) + p.1 + p.2.1 + p.2.2.1 + p.2.2.2 +
          (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) < m + n := by
  classical
  constructor
  · rw [dividedPower_root_mul_of_g2_triple c hγ hδ hε hζ]
    simp
  · rintro ⟨i, j, k, l⟩ hp
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    have hb := mem_chainG2Index.mp hp
    simp only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hne
    dsimp only at hb ⊢
    omega

/-- The swapped product is the leading term; every correction has strictly smaller total
sum of divided-power exponents. All correction coefficients are integers. -/
theorem dividedPower_root_mul_eq_swap_add_of_g2_short_pair {α β γ δ ε : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root γ + P.root β)
    (m n : ℕ) :
    (dividedPower m (e α) * dividedPower n (e β) =
      dividedPower n (e β) * dividedPower m (e α) +
        ∑ p ∈ (g2ShortPairIndex m n).erase 0,
        ((2 ^ p.1 * 3 ^ (p.2.1 + p.2.2) : ℤ) *
          (c.structConst α β).sign ^ p.1 *
          ((c.structConst α β).sign * (c.structConst α γ).sign) ^ p.2.1 *
          ((c.structConst α β).sign * (c.structConst γ β).sign) ^ p.2.2) •
          (dividedPower (n - p.1 - p.2.1 - 2 * p.2.2) (e β) *
            dividedPower p.1 (e γ) * dividedPower p.2.1 (e δ) *
            dividedPower p.2.2 (e ε) *
            dividedPower (m - p.1 - 2 * p.2.1 - p.2.2) (e α))) ∧
      ∀ p ∈ (g2ShortPairIndex m n).erase 0, (n - p.1 - p.2.1 - 2 * p.2.2) + p.1 + p.2.1 + p.2.2 +
          (m - p.1 - 2 * p.2.1 - p.2.2) < m + n := by
  classical
  constructor
  · rw [dividedPower_root_mul_of_g2_short_pair c hγ hδ hε]
    simp
  · rintro ⟨i, j, k⟩ hp
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    have hb := mem_g2ShortPairIndex.mp hp
    simp only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hne
    dsimp only at hb ⊢
    omega

/-- Collection in the opposite orientation of the triple string. The factor order reverses,
and the sum-root and third-string coefficients change sign. -/
theorem dividedPower_root_mul_of_g2_reverse_triple {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ)
    (m n : ℕ) :
    dividedPower n (e β) * dividedPower m (e α) =
      ∑ p ∈ chainG2Index m n,
        ((-c.structConst α β) ^ p.1 *
          (c.structConst α β * (c.structConst α γ).sign) ^ p.2.1 *
          (-(c.structConst α β * (c.structConst α γ).sign *
            (c.structConst α δ).sign)) ^ p.2.2.1 *
          (c.structConst α β ^ 2 * (c.structConst α γ).sign *
            (c.structConst δ γ).sign) ^ p.2.2.2) •
          (dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) (e α) *
            dividedPower p.2.2.2 (e ζ) * dividedPower p.2.2.1 (e ε) *
            dividedPower p.2.1 (e δ) * dividedPower p.1 (e γ) *
            dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) (e β)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := g2_triple_brackets c hγ hδ hε hζ
  obtain ⟨h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := g2_triple_commute c hγ hδ hε hζ
  have rev (x y a : U) (h : x * y = y * x + a) :
      MulOpposite.op x * MulOpposite.op y =
        MulOpposite.op y * MulOpposite.op x + -MulOpposite.op a := by
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_add, MulOpposite.unop_neg,
      MulOpposite.unop_op]
    rw [h, add_neg_cancel_right]
  have h₁' := rev _ _ _ h₁
  have h₂' := rev _ _ _ h₂
  have h₃' := rev _ _ _ h₃
  have h₄' := rev _ _ _ h₄
  simp only [MulOpposite.op_smul] at h₁' h₂' h₃' h₄'
  rw [← neg_smul] at h₁'
  rw [← smul_neg, ← neg_smul] at h₂' h₃' h₄'
  have h := dividedPower_mul_dividedPower_of_g2_zsmul
    (-c.structConst α β) (-(c.structConst α γ).sign)
    (-(c.structConst α δ).sign) (-(c.structConst δ γ).sign)
    h₁' h₂' h₃' h₄' h₅.op h₆.op h₇.op h₈.op h₉.op h₁₀.op h₁₁.op m n
  have hpow (k : ℕ) (u : Uᵐᵒᵖ) :
      MulOpposite.unop (dividedPower k u) = dividedPower k (MulOpposite.unop u) := by
    simp only [dividedPower_def, MulOpposite.unop_smul, MulOpposite.unop_pow]
  simpa only [MulOpposite.unop_mul, Finset.unop_sum, MulOpposite.unop_smul,
    MulOpposite.unop_op, hpow, mul_assoc, neg_mul_neg, mul_neg,
    neg_mul, neg_sq, neg_neg] using congrArg MulOpposite.unop h

/-- The short-pair collection formula in the reverse orientation. The two double-root factors
exchange places, and the sum-root coefficient changes sign. -/
theorem dividedPower_root_mul_of_g2_reverse_short_pair {α β γ δ ε : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root γ + P.root β) (m n : ℕ) :
    dividedPower n (e β) * dividedPower m (e α) =
      ∑ p ∈ g2ShortPairIndex n m,
        ((2 ^ p.1 * 3 ^ (p.2.1 + p.2.2) : ℤ) *
          (-(c.structConst α β).sign) ^ p.1 *
          ((c.structConst α β).sign * (c.structConst γ β).sign) ^ p.2.1 *
          ((c.structConst α β).sign * (c.structConst α γ).sign) ^ p.2.2) •
          (dividedPower (m - p.1 - p.2.1 - 2 * p.2.2) (e α) *
            dividedPower p.1 (e γ) * dividedPower p.2.1 (e ε) *
            dividedPower p.2.2 (e δ) *
            dividedPower (n - p.1 - 2 * p.2.1 - p.2.2) (e β)) := by
  have hγ' : P.root γ = P.root β + P.root α := hγ.trans (add_comm _ _)
  have hε' : P.root ε = P.root β + P.root γ := hε.trans (add_comm _ _)
  have hδ' : P.root δ = P.root γ + P.root α := hδ.trans (add_comm _ _)
  simpa only [c.structConst_swap α β, c.structConst_swap γ β,
    c.structConst_swap α γ, Int.sign_neg, neg_mul_neg] using
    dividedPower_root_mul_of_g2_short_pair c hγ' hε' hδ' n m

/-- Reverse collection with the leading swapped product isolated and every correction
strictly smaller in total divided-power degree. -/
theorem dividedPower_root_mul_eq_swap_add_of_g2_reverse_triple {α β γ δ ε ζ : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root α + P.root δ)
    (hζ : P.root ζ = P.root δ + P.root γ)
    (m n : ℕ) :
    (dividedPower n (e β) * dividedPower m (e α) =
      dividedPower m (e α) * dividedPower n (e β) +
        ∑ p ∈ (chainG2Index m n).erase 0,
        ((-c.structConst α β) ^ p.1 *
          (c.structConst α β * (c.structConst α γ).sign) ^ p.2.1 *
          (-(c.structConst α β * (c.structConst α γ).sign *
            (c.structConst α δ).sign)) ^ p.2.2.1 *
          (c.structConst α β ^ 2 * (c.structConst α γ).sign *
            (c.structConst δ γ).sign) ^ p.2.2.2) •
          (dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) (e α) *
            dividedPower p.2.2.2 (e ζ) * dividedPower p.2.2.1 (e ε) *
            dividedPower p.2.1 (e δ) * dividedPower p.1 (e γ) *
            dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) (e β))) ∧
      ∀ p ∈ (chainG2Index m n).erase 0, (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) +
          p.2.2.2 + p.2.2.1 + p.2.1 + p.1 +
          (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) < m + n := by
  classical
  constructor
  · rw [dividedPower_root_mul_of_g2_reverse_triple c hγ hδ hε hζ]
    simp
  · rintro ⟨i, j, k, l⟩ hp
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    have hb := mem_chainG2Index.mp hp
    simp only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hne
    dsimp only at hb ⊢
    omega

/-- Reverse collection with the leading swapped product isolated and every correction
strictly smaller in total divided-power degree. -/
theorem dividedPower_root_mul_eq_swap_add_of_g2_reverse_short_pair {α β γ δ ε : ι}
    (hγ : P.root γ = P.root α + P.root β)
    (hδ : P.root δ = P.root α + P.root γ)
    (hε : P.root ε = P.root γ + P.root β) (m n : ℕ) :
    (dividedPower n (e β) * dividedPower m (e α) =
      dividedPower m (e α) * dividedPower n (e β) +
        ∑ p ∈ (g2ShortPairIndex n m).erase 0,
        ((2 ^ p.1 * 3 ^ (p.2.1 + p.2.2) : ℤ) *
          (-(c.structConst α β).sign) ^ p.1 *
          ((c.structConst α β).sign * (c.structConst γ β).sign) ^ p.2.1 *
          ((c.structConst α β).sign * (c.structConst α γ).sign) ^ p.2.2) •
          (dividedPower (m - p.1 - p.2.1 - 2 * p.2.2) (e α) *
            dividedPower p.1 (e γ) * dividedPower p.2.1 (e ε) *
            dividedPower p.2.2 (e δ) *
            dividedPower (n - p.1 - 2 * p.2.1 - p.2.2) (e β))) ∧
      ∀ p ∈ (g2ShortPairIndex n m).erase 0, (m - p.1 - p.2.1 - 2 * p.2.2) + p.1 + p.2.1 + p.2.2 +
          (n - p.1 - 2 * p.2.1 - p.2.2) < m + n := by
  classical
  constructor
  · rw [dividedPower_root_mul_of_g2_reverse_short_pair c hγ hδ hε]
    simp
  · rintro ⟨i, j, k⟩ hp
    obtain ⟨hne, hp⟩ := mem_erase.mp hp
    have hb := mem_g2ShortPairIndex.mp hp
    simp only [ne_eq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hne
    dsimp only at hb ⊢
    omega

end RootPairing.ChevalleyLieAlgebra
