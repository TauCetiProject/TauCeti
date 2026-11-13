/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.G2.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Short–long root collection and element commutators in type G₂

For roots α, β with the three-step string β, α + β, 2α + β, 3α + β, this file
computes the integral coefficients of the four-factor Chevalley multiplication formula.
The divisions by two and three are exact in ℤ, before passing to the value ring.
The formulas on Kostant-stable lattices therefore include characteristics two and three.

The short–long element commutator has factors in increasing root height at α + β, 2α + β,
3α + β and 3α + 2β. Moving the long-root factor in the collection identity to the right
changes its highest-root coefficient from b to 2b. The correction follows from the
class-two relation for β and 3α + β and the Jacobi identity, using
`commutatorElement_chevalleyRootSubgroup_of_lie_eq`. No faithfulness or weight-basis
assumption is needed.

The long–short element commutator follows from
`chevalleyRootSubgroup_mul_of_g2_short_long` at the negative long-root parameter.
For a short root `α` and a long root `β`, its four factors are ordered by increasing total
degree: `α + β`, `2α + β`, `3α + β`, `3α + 2β`. Their coefficients are `-c`, `-d`, `-a`, `b`
in the collection formula's notation. The highest-root coefficient is `b`, rather than the
`2b` appearing when the short-root element comes first; this distinction matters when
collecting arbitrary root products in a fixed order. The four root equations specify the
full G₂ string without additional bracket or nilpotence assumptions on nonsimple root vectors.

The exponential argument follows
`kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul`; here its bracket hypotheses are
discharged from the numbered root datum rather than supplied by the caller.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2. The commutator convention here is
  x y x⁻¹ y⁻¹, not Carter's x⁻¹ y⁻¹ x y.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling LieModule
open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

noncomputable section

variable {t : DynkinType} {ht : t.Valid}

-- The divisions are performed in ℤ, not in the ring of points.
private theorem three_step_divisions {α β γ δ ε ζ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hε : (t.simplyConnectedRootDatum ht).root ε =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ)
    (hζ : (t.simplyConnectedRootDatum ht).root ζ =
      (t.simplyConnectedRootDatum ht).root δ + (t.simplyConnectedRootDatum ht).root γ) :
    let N := t.structureConstant ht
    N α γ = 2 * (N α γ / 2) ∧
      N α δ = 3 * (N α δ / 3) ∧
      N δ γ = 3 * (N δ γ / 3) := by
  let P := t.simplyConnectedRootDatum ht
  let : P.IsReduced := t.isReduced_simplyConnectedRootDatum ht
  have hadd : P.root α + P.root β ∈ Set.range P.root := ⟨γ, hγ⟩
  have hli := P.linearIndependent_of_add_mem_range_root' hadd
  have htop : 3 ≤ P.chainTopCoeff α β := by
    apply (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli).1
    exact ⟨ε, by rw [hε, hδ, hγ]; abel⟩
  have hlen := P.chainBotCoeff_add_chainTopCoeff_le_three (i := α) (j := β)
  have hbot : P.chainBotCoeff α β = 0 := by omega
  have hbotγ : P.chainBotCoeff α γ = 1 := by
    rw [P.chainBotCoeff_of_add hli (hγ.trans (add_comm _ _)), hbot]
  have haddγ : P.root α + P.root γ ∈ Set.range P.root := ⟨δ, hδ⟩
  have hliγ := P.linearIndependent_of_add_mem_range_root' haddγ
  have hbotδ : P.chainBotCoeff α δ = 2 := by
    rw [P.chainBotCoeff_of_add hliγ (hδ.trans (add_comm _ _)), hbotγ]
  have hliδγ := P.linearIndependent_of_add_mem_range_root' ⟨ζ, hζ⟩
  have htwo : 2 ≤ P.chainBotCoeff δ γ := by
    apply (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hliδγ).1
    refine ⟨P.reflectionPerm ε ε, ?_⟩
    simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    rw [hε, hδ, hγ]
    abel
  have htop' := P.one_le_chainTopCoeff_of_root_add_mem ⟨ζ, hζ⟩
  have hlen' := P.chainBotCoeff_add_chainTopCoeff_le_three (i := δ) (j := γ)
  have hbotδγ : P.chainBotCoeff δ γ = 2 := by omega
  have hc₂ := structureConstant_eq_natCast_or_eq_neg_natCast ⟨δ, hδ⟩
  have hc₃ := structureConstant_eq_natCast_or_eq_neg_natCast ⟨ε, hε⟩
  have hc₃' := structureConstant_eq_natCast_or_eq_neg_natCast ⟨ζ, hζ⟩
  rw [hbotγ] at hc₂
  rw [hbotδ] at hc₃
  rw [hbotδγ] at hc₃'
  rcases hc₂ with h | h <;> rcases hc₃ with h' | h' <;>
    rcases hc₃' with h'' | h'' <;> simp [h, h', h'']

/-- The successive divided brackets in a three-step root string, with their integral
coefficients. These identities retain the factors two and three before scalar extension. -/
private theorem lie_chevalleySystem_three_step {α β γ δ ε ζ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hε : (t.simplyConnectedRootDatum ht).root ε =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ)
    (hζ : (t.simplyConnectedRootDatum ht).root ζ =
      (t.simplyConnectedRootDatum ht).root δ + (t.simplyConnectedRootDatum ht).root γ) :
    let N := t.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    let e := t.chevalleySystem ht
    c • ⁅e α, e γ⁆ = (2 * d) • e δ ∧
      d • ⁅e α, e δ⁆ = (3 * a) • e ε ∧
      (d * c) • ⁅e δ, e γ⁆ = (3 * b) • e ζ := by
  obtain ⟨hc₂, hc₃, hc₃'⟩ := three_step_divisions hγ hδ hε hζ
  dsimp only
  rw [lie_chevalleySystem_eq_structureConstant_zsmul hδ,
    lie_chevalleySystem_eq_structureConstant_zsmul hε,
    lie_chevalleySystem_eq_structureConstant_zsmul hζ, ← mul_smul, ← mul_smul, ← mul_smul]
  -- Rewrite only the numerator occurrence, leaving the exact quotient unchanged.
  refine ⟨?_, ?_, ?_⟩ <;> congr 1
  · calc
      _ = t.structureConstant ht α β * (2 * (t.structureConstant ht α γ / 2)) :=
        congrArg (t.structureConstant ht α β * ·) hc₂
      _ = _ := by ring
  · calc
      _ = (t.structureConstant ht α β * (t.structureConstant ht α γ / 2)) *
          (3 * (t.structureConstant ht α δ / 3)) :=
        congrArg ((t.structureConstant ht α β * (t.structureConstant ht α γ / 2)) * ·) hc₃
      _ = _ := by ring
  · calc
      _ = (t.structureConstant ht α β * (t.structureConstant ht α γ / 2) *
          t.structureConstant ht α β) * (3 * (t.structureConstant ht δ γ / 3)) :=
        congrArg ((t.structureConstant ht α β * (t.structureConstant ht α γ / 2) *
          t.structureConstant ht α β) * ·) hc₃'
      _ = _ := by ring

/-- Two vanishing brackets forced by reducedness in a three-step root configuration:
the sums β + δ and β + ζ are respectively twice and three times γ. -/
private theorem lie_chevalleySystem_three_step_eq_zero {α β γ δ ζ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hζ : (t.simplyConnectedRootDatum ht).root ζ =
      (t.simplyConnectedRootDatum ht).root δ + (t.simplyConnectedRootDatum ht).root γ) :
    let e := t.chevalleySystem ht
    ⁅e β, e δ⁆ = 0 ∧ ⁅e β, e ζ⁆ = 0 := by
  let P := t.simplyConnectedRootDatum ht
  let : P.IsReduced := t.isReduced_simplyConnectedRootDatum ht
  have htwo : P.root β + P.root δ = (2 : ℕ) • P.root γ := by rw [hδ, hγ]; abel
  have hthree : P.root β + P.root ζ = (3 : ℕ) • P.root γ := by
    rw [hζ, hδ, hγ]
    abel
  have hvanish (η : Fin t.numRoots) (n : ℕ) [n.AtLeastTwo]
      (hsum : P.root β + P.root η = n • P.root γ) :
      ⁅t.chevalleySystem ht β, t.chevalleySystem ht η⁆ = 0 := by
    have hn : (n : ℤ) ≠ 0 := by
      have := Nat.AtLeastTwo.prop (n := n)
      omega
    apply lie_chevalleySystem_eq_zero
    · rw [hsum]
      exact P.nsmul_notMem_range_root
    · rw [hsum]
      simpa only [Nat.cast_smul_eq_nsmul] using smul_ne_zero hn (P.ne_zero γ)
  exact ⟨hvanish δ 2 htwo, hvanish ζ 3 hthree⟩

private theorem three_step_highest_root {α β γ δ ε ζ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hε : (t.simplyConnectedRootDatum ht).root ε =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ)
    (hζ : (t.simplyConnectedRootDatum ht).root ζ =
      (t.simplyConnectedRootDatum ht).root δ + (t.simplyConnectedRootDatum ht).root γ) :
    (t.simplyConnectedRootDatum ht).root ζ =
      (t.simplyConnectedRootDatum ht).root β + (t.simplyConnectedRootDatum ht).root ε := by
  rw [hζ, hε, hδ, hγ]
  abel

/-- In a three-step root string, `a * N β ε = b`, where `a` and `b` are the coefficients
of 3α + β and 3α + 2β in the collection formula. All divisions in these coefficients
are performed in ℤ. -/
private theorem mul_structureConstant_three_step_eq {α β γ δ ε ζ : Fin t.numRoots}
    (hγ : (t.simplyConnectedRootDatum ht).root γ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root β)
    (hδ : (t.simplyConnectedRootDatum ht).root δ =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root γ)
    (hε : (t.simplyConnectedRootDatum ht).root ε =
      (t.simplyConnectedRootDatum ht).root α + (t.simplyConnectedRootDatum ht).root δ)
    (hζ : (t.simplyConnectedRootDatum ht).root ζ =
      (t.simplyConnectedRootDatum ht).root δ + (t.simplyConnectedRootDatum ht).root γ) :
    let N := t.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    a * N β ε = b := by
  let e := t.chevalleySystem ht
  let N := t.structureConstant ht
  let c := N α β
  let d := c * (N α γ / 2)
  let a := d * (N α δ / 3)
  let b := d * c * (N δ γ / 3)
  obtain ⟨_, hαδ, hδγ⟩ := lie_chevalleySystem_three_step hγ hδ hε hζ
  have hβδ := (lie_chevalleySystem_three_step_eq_zero hγ hδ hζ).1
  have hβε := three_step_highest_root hγ hδ hε hζ
  have hjac : (3 * (a * N β ε)) • e ζ = (3 * b) • e ζ := by
    calc
      _ = ⁅e β, d • ⁅e α, e δ⁆⁆ := by
        rw [hαδ, lie_smul, lie_chevalleySystem_eq_structureConstant_zsmul hβε, smul_smul]
        congr 1
        ring
      _ = d • (⁅⁅e β, e α⁆, e δ⁆ + ⁅e α, ⁅e β, e δ⁆⁆) := by
        rw [lie_smul, leibniz_lie]
      _ = (d * c) • ⁅e δ, e γ⁆ := by
        rw [hβδ, ← lie_skew (e β) (e α),
          lie_chevalleySystem_eq_structureConstant_zsmul hγ]
        simpa only [lie_zero, add_zero, neg_lie, smul_lie, smul_neg, smul_smul] using
          congrArg ((d * c) • ·) (lie_skew (e δ) (e γ))
      _ = _ := hδγ
  have he : e ζ ≠ 0 := (t.isSl2Triple_chevalleySystem ht ζ).e_ne_zero
  have hc : ((3 * (a * N β ε) : ℤ) : ℚ) = ((3 * b : ℤ) : ℚ) :=
    (smul_left_injective ℚ he) (by simpa only [Int.cast_smul_eq_zsmul] using hjac)
  have hc' : 3 * (a * N β ε) = 3 * b := by exact_mod_cast hc
  exact mul_left_cancel₀ (by decide : (3 : ℤ) ≠ 0) hc'

private theorem g2_short_long_exclusions (α β : Fin 12)
    (hadd : g2SimplyConnectedRootDatum.root α +
      g2SimplyConnectedRootDatum.root β ∈ Set.range g2SimplyConnectedRootDatum.root)
    (hthree : g2SimplyConnectedRootDatum.root β +
      (3 : ℕ) • g2SimplyConnectedRootDatum.root α ∈
        Set.range g2SimplyConnectedRootDatum.root) :
    ∀ ξ : Fin 12,
      g2SimplyConnectedRootDatum.root ξ ≠
        4 • g2SimplyConnectedRootDatum.root α + g2SimplyConnectedRootDatum.root β ∧
      g2SimplyConnectedRootDatum.root ξ ≠
        4 • g2SimplyConnectedRootDatum.root α + 2 • g2SimplyConnectedRootDatum.root β ∧
      g2SimplyConnectedRootDatum.root ξ ≠
        g2SimplyConnectedRootDatum.root α + 2 • g2SimplyConnectedRootDatum.root β ∧
      g2SimplyConnectedRootDatum.root ξ ≠
        5 • g2SimplyConnectedRootDatum.root α + 2 • g2SimplyConnectedRootDatum.root β ∧
      g2SimplyConnectedRootDatum.root ξ ≠
        4 • g2SimplyConnectedRootDatum.root α + 3 • g2SimplyConnectedRootDatum.root β ∧
      g2SimplyConnectedRootDatum.root ξ ≠
        5 • g2SimplyConnectedRootDatum.root α + 3 • g2SimplyConnectedRootDatum.root β ∧
      g2SimplyConnectedRootDatum.root ξ ≠
        6 • g2SimplyConnectedRootDatum.root α +
          3 • g2SimplyConnectedRootDatum.root β := by
  simp only [g2SimplyConnectedRootDatum_root, Set.mem_range, g2Root_apply] at hadd hthree ⊢
  revert α β
  decide +kernel

private theorem short_long_exclusions (ht : G2.Valid) (α β : Fin G2.numRoots)
    (hadd : (G2.simplyConnectedRootDatum ht).root α +
      (G2.simplyConnectedRootDatum ht).root β ∈ Set.range (G2.simplyConnectedRootDatum ht).root)
    (hthree : (G2.simplyConnectedRootDatum ht).root β +
      (3 : ℕ) • (G2.simplyConnectedRootDatum ht).root α ∈
        Set.range (G2.simplyConnectedRootDatum ht).root) :
    ∀ ξ : Fin G2.numRoots,
      (G2.simplyConnectedRootDatum ht).root ξ ≠
        4 • (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β ∧
      (G2.simplyConnectedRootDatum ht).root ξ ≠
        4 • (G2.simplyConnectedRootDatum ht).root α + 2 • (G2.simplyConnectedRootDatum ht).root β ∧
      (G2.simplyConnectedRootDatum ht).root ξ ≠
        (G2.simplyConnectedRootDatum ht).root α + 2 • (G2.simplyConnectedRootDatum ht).root β ∧
      (G2.simplyConnectedRootDatum ht).root ξ ≠
        5 • (G2.simplyConnectedRootDatum ht).root α + 2 • (G2.simplyConnectedRootDatum ht).root β ∧
      (G2.simplyConnectedRootDatum ht).root ξ ≠
        4 • (G2.simplyConnectedRootDatum ht).root α + 3 • (G2.simplyConnectedRootDatum ht).root β ∧
      (G2.simplyConnectedRootDatum ht).root ξ ≠
        5 • (G2.simplyConnectedRootDatum ht).root α + 3 • (G2.simplyConnectedRootDatum ht).root β ∧
      (G2.simplyConnectedRootDatum ht).root ξ ≠
        6 • (G2.simplyConnectedRootDatum ht).root α +
          3 • (G2.simplyConnectedRootDatum ht).root β := by
  revert α β
  -- Normalize coordinate types inside the instances as well as the binders.
  simpa +instances only [simplyConnectedRootDatum_G2, numRoots_G2, rank_G2] using
    g2_short_long_exclusions

/-- Seven vanishing brackets among the root vectors of α and the G₂ string
β, α + β, 2α + β, 3α + β, 3α + 2β, used when collecting root-subgroup factors.
The brackets of β with 2α + β and 3α + 2β are given separately by
`lie_chevalleySystem_three_step_eq_zero`, for every valid Dynkin type. -/
private theorem lie_chevalleySystem_g2_three_step_eq_zero (ht : G2.Valid)
    {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ) :
    let e := G2.chevalleySystem ht
    ⁅e α, e ε⁆ = 0 ∧ ⁅e α, e ζ⁆ = 0 ∧ ⁅e β, e γ⁆ = 0 ∧
      ⁅e δ, e ε⁆ = 0 ∧ ⁅e γ, e ζ⁆ = 0 ∧ ⁅e δ, e ζ⁆ = 0 ∧ ⁅e ε, e ζ⁆ = 0 := by
  let P := G2.simplyConnectedRootDatum ht
  let : P.IsReduced := G2.isReduced_simplyConnectedRootDatum ht
  have hadd : P.root α + P.root β ∈ Set.range P.root := ⟨γ, hγ⟩
  have hthree : P.root β + (3 : ℕ) • P.root α ∈ Set.range P.root :=
    ⟨ε, by rw [hε, hδ, hγ]; abel⟩
  have hx := short_long_exclusions ht α β hadd hthree
  have hli := P.linearIndependent_of_add_mem_range_root' hadd
  have hnz (m n : ℤ) (hm : m ≠ 0) : m • P.root α + n • P.root β ≠ 0 := by
    intro h
    exact hm (Fintype.linearIndependent_iff.mp hli ![m, n]
      (by simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h) 0)
  have vanish (i j : Fin G2.numRoots) (m n : ℤ)
      (hij : P.root i + P.root j = m • P.root α + n • P.root β)
      (hnot : ∀ ξ, P.root ξ ≠ m • P.root α + n • P.root β) (hm : m ≠ 0) :
      ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht j⁆ = 0 := by
    apply lie_chevalleySystem_eq_zero
    · rintro ⟨ξ, hξ⟩
      exact hnot ξ (hξ.trans hij)
    · rw [hij]
      exact hnz m n hm
  refine ⟨vanish α ε 4 1 ?_
      (fun ξ => by simpa only [P, one_smul, ofNat_zsmul] using (hx ξ).1) (by decide),
    vanish α ζ 4 2 ?_ (fun ξ => (hx ξ).2.1) (by decide),
    vanish β γ 1 2 ?_
      (fun ξ => by simpa only [P, one_smul, ofNat_zsmul] using (hx ξ).2.2.1) (by decide),
    vanish δ ε 5 2 ?_ (fun ξ => (hx ξ).2.2.2.1) (by decide),
    vanish γ ζ 4 3 ?_ (fun ξ => (hx ξ).2.2.2.2.1) (by decide),
    vanish δ ζ 5 3 ?_ (fun ξ => (hx ξ).2.2.2.2.2.1) (by decide),
    vanish ε ζ 6 3 ?_ (fun ξ => (hx ξ).2.2.2.2.2.2) (by decide)⟩ <;>
    simp only [P, hζ, hε, hδ, hγ] <;> abel

section Lattice

variable (ht : G2.Valid)
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (G2.lieBasis ht).rootGenerator (G2.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis ht).rootGenerator i))))

-- Match tensor products to the ℤ-algebra instance stored by each CommAlgCat object.
attribute [local instance high] Algebra.toModule

/-- The four-factor short–long root collection formula on every Kostant-stable lattice.
The factors are ordered as β, α + β, 2α + β, 3α + β, 3α + 2β, α. The coefficient
at the highest root is for this order; moving the β factor changes that coefficient. -/
theorem chevalleyRootSubgroup_mul_of_g2_short_long {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    let x := chevalleyRootSubgroup ρ M hM hnil
    x α A (Multiplicative.ofAdd u) * x β A (Multiplicative.ofAdd v) =
      x β A (Multiplicative.ofAdd v) * x γ A (Multiplicative.ofAdd ((c : A) * (u * v))) *
        x δ A (Multiplicative.ofAdd ((d : A) * (u ^ 2 * v))) *
        x ε A (Multiplicative.ofAdd ((a : A) * (u ^ 3 * v))) *
        x ζ A (Multiplicative.ofAdd ((b : A) * (u ^ 3 * v ^ 2))) *
        x α A (Multiplicative.ofAdd u) := by
  obtain ⟨hik, hil, hlk⟩ := lie_chevalleySystem_three_step hγ hδ hε hζ
  have hij := lie_chevalleySystem_eq_structureConstant_zsmul hγ
  obtain ⟨him, hio, hjk, hlm, hko, hlo, hmo⟩ :=
    lie_chevalleySystem_g2_three_step_eq_zero ht hγ hδ hε hζ
  let hroot := isNilpotent_apply_ι_chevalleySystem ρ hnil
  have hcollection := kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul'
    (G2.chevalleySystem ht) (G2.lieBasis ht).h ρ M
    (kostantForm_chevalleySystem_smul_mem ρ M hM hnil) hij hik hil hlk
    him hio hjk hlm hko hlo hmo (hroot α) (hroot β) (hroot γ) (hroot δ) (hroot ε) (hroot ζ)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd u))
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd v))
  -- Both root-subgroup interfaces act by the same divided-power exponentials.
  apply Units.ext
  simpa only [Units.val_mul, chevalleyRootSubgroup_val, kostantRootSubgroupPoints_val,
    MulEquiv.apply_symm_apply, toAdd_ofAdd] using congrArg Units.val hcollection

variable {ht}

/-- The ordered short–long G₂ element-commutator formula on a Kostant-stable lattice.
The factors are in increasing root height. The highest-root coefficient is twice the
coefficient in the root-collection formula, with the divisions performed in ℤ. -/
theorem commutatorElement_chevalleyRootSubgroup_of_g2_short_long {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    let x := fun i w => chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd w)
    ⁅x α u, x β v⁆ =
      x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
        x ε ((a : A) * (u ^ 3 * v)) * x ζ ((2 * b : ℤ) * (u ^ 3 * v ^ 2)) := by
  let N := G2.structureConstant ht
  let c := N α β
  let d := c * (N α γ / 2)
  let a := d * (N α δ / 3)
  let b := d * c * (N δ γ / 3)
  let x := fun i (w : A) => chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd w)
  -- Keep the local coefficients opaque to group associativity simplification below, which
  -- would otherwise also reassociate the products inside their integer definitions.
  change ⁅x α u, x β v⁆ = x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
    x ε ((a : A) * (u ^ 3 * v)) * x ζ ((2 * b : ℤ) * (u ^ 3 * v ^ 2))
  -- Conjugation by the long-root factor fixes three factors and corrects the fourth.
  obtain ⟨_, _, hβγ, _, _, _, hεζ⟩ :=
    lie_chevalleySystem_g2_three_step_eq_zero ht hγ hδ hε hζ
  obtain ⟨hβδ, hβζ⟩ := lie_chevalleySystem_three_step_eq_zero hγ hδ hζ
  have hconj (i : Fin G2.numRoots)
      (hβi : ⁅G2.chevalleySystem ht β, G2.chevalleySystem ht i⁆ = 0) (s : A) :
      MulAut.conj (x β v) (x i s) = x i s := by
    rw [MulAut.conj_apply,
      (commute_chevalleyRootSubgroup_of_lie_eq_zero ρ M hM hnil hβi A v s).eq,
      mul_inv_cancel_right]
  have hconjε : MulAut.conj (x β v) (x ε ((a : A) * (u ^ 3 * v))) =
      x ε ((a : A) * (u ^ 3 * v)) * x ζ ((b : A) * (u ^ 3 * v ^ 2)) := by
    rw [conj_eq_commutatorElement_mul,
      commutatorElement_chevalleyRootSubgroup_of_lie_eq ρ M hM hnil
        (lie_chevalleySystem_eq_structureConstant_zsmul
          (three_step_highest_root hγ hδ hε hζ)) hβζ hεζ]
    have hab : (a : A) * (N β ε : A) = (b : A) := by
      have hab : a * N β ε = b :=
        mul_structureConstant_three_step_eq hγ hδ hε hζ
      rw [← Int.cast_mul, hab]
    have hc : (N β ε : A) * (v * ((a : A) * (u ^ 3 * v))) =
        (b : A) * (u ^ 3 * v ^ 2) := by
      linear_combination (u ^ 3 * v ^ 2) * hab
    rw [hc, (commute_chevalleyRootSubgroup_of_lie_eq_zero ρ M hM hnil hεζ A _ _).eq]
  have hprod : x α u * x β v = x β v * x γ ((c : A) * (u * v)) *
      x δ ((d : A) * (u ^ 2 * v)) * x ε ((a : A) * (u ^ 3 * v)) *
        x ζ ((b : A) * (u ^ 3 * v ^ 2)) * x α u :=
    chevalleyRootSubgroup_mul_of_g2_short_long ht ρ M hM hnil hγ hδ hε hζ A u v
  have hstart : ⁅x α u, x β v⁆ = MulAut.conj (x β v)
      (x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
        x ε ((a : A) * (u ^ 3 * v)) * x ζ ((b : A) * (u ^ 3 * v ^ 2))) := by
    rw [commutatorElement_def, hprod, MulAut.conj_apply]
    group
  have hdouble : x ζ ((b : A) * (u ^ 3 * v ^ 2)) * x ζ ((b : A) * (u ^ 3 * v ^ 2)) =
      x ζ ((2 * b : ℤ) * (u ^ 3 * v ^ 2)) := by
    rw [← map_mul, ← ofAdd_add]
    congr 2
    push_cast
    ring
  -- Collect the two highest-root parameters after distributing conjugation.
  rw [hstart, map_mul, map_mul, map_mul, hconj γ hβγ, hconj δ hβδ, hconjε, hconj ζ hβζ]
  simpa only [mul_assoc] using congrArg
    (fun z => x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
      x ε ((a : A) * (u ^ 3 * v)) * z) hdouble

/-- The long–short G₂ element commutator, with factors in increasing total degree in `α`, `β`.
Here `α` is the short root, `β` is the long root, and the long-root element occurs first in the
commutator. The integer highest-root coefficient is the collection coefficient `b`, not `2b`.
All coefficients are computed before passage to the commutative value ring. -/
theorem commutatorElement_chevalleyRootSubgroup_of_g2_long_short
    {α β γ δ ε ζ : Fin G2.numRoots}
    (hγ : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β)
    (hδ : (G2.simplyConnectedRootDatum ht).root δ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root γ)
    (hε : (G2.simplyConnectedRootDatum ht).root ε =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root δ)
    (hζ : (G2.simplyConnectedRootDatum ht).root ζ =
      (G2.simplyConnectedRootDatum ht).root δ + (G2.simplyConnectedRootDatum ht).root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    let x := fun i w => chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd w)
    ⁅x β v, x α u⁆ =
      x γ ((-c : A) * (u * v)) * x δ ((-d : A) * (u ^ 2 * v)) *
        x ε ((-a : A) * (u ^ 3 * v)) * x ζ ((b : A) * (u ^ 3 * v ^ 2)) := by
  have h := chevalleyRootSubgroup_mul_of_g2_short_long ht ρ M hM hnil hγ hδ hε hζ A u (-v)
  dsimp only at h ⊢
  simp only [mul_neg, neg_sq] at h
  have hc := congrArg (fun g =>
    chevalleyRootSubgroup ρ M hM hnil β A (Multiplicative.ofAdd v) * g *
      (chevalleyRootSubgroup ρ M hM hnil α A (Multiplicative.ofAdd u))⁻¹) h
  simpa only [commutatorElement_def, ofAdd_neg, map_inv, mul_assoc,
    mul_inv_cancel, mul_one, mul_inv_cancel_left, neg_mul] using hc

end Lattice

end

end TauCeti.DynkinType
