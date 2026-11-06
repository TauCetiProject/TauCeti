/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
import TauCeti.RingTheory.Nilpotent.RootString.G2.Basic
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Reduced

/-!
# Short–long root collection in type G₂

For roots α, β with the three-step string β, α + β, 2α + β, 3α + β, this file
computes the integral coefficients of the four-factor Chevalley multiplication formula.
The divisions by two and three are exact in ℤ, before passing to the value ring.
The formula on Kostant-stable lattices therefore includes characteristics two and three.

The exponential argument follows
`kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul`; here its bracket hypotheses are
discharged from the numbered root datum rather than supplied by the caller.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open LieAlgebra LieAlgebra.IsKilling LieModule
open TauCeti.UniversalEnvelopingAlgebra

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
  have hliγ := P.linearIndependent_of_add_mem_range_root'
    (show P.root α + P.root γ ∈ Set.range P.root from ⟨δ, hδ⟩)
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

private theorem three_step_brackets {α β γ δ ε ζ : Fin t.numRoots}
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
  -- Normalize the binders too, so the finite table is read at its native index types.
  simp only [simplyConnectedRootDatum_G2, numRoots, rank]
  -- Full-transparency rewriting identifies the uniform coordinate instances with the table.
  erw [g2SimplyConnectedRootDatum_root]
  dsimp +instances only [rank, numRoots]
  simp only [Set.mem_range, g2Root_apply]
  decide +kernel

private theorem short_long_vanishing (ht : G2.Valid) {α β γ δ ε ζ : Fin G2.numRoots}
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
  let N := G2.structureConstant ht
  let c := N α β
  let d := c * (N α γ / 2)
  let a := d * (N α δ / 3)
  let b := d * c * (N δ γ / 3)
  obtain ⟨hik, hil, hlk⟩ := three_step_brackets hγ hδ hε hζ
  have hij := lie_chevalleySystem_eq_structureConstant_zsmul hγ
  obtain ⟨him, hio, hjk, hlm, hko, hlo, hmo⟩ := short_long_vanishing ht hγ hδ hε hζ
  -- Translate the native Lie brackets into the scaled associative commutator relations.
  let E (i : Fin G2.numRoots) := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ
    (G2.chevalleySystem ht i))
  have hstable := dividedPower_chevalleySystem_smul_mem ρ M hM hnil
  have hscaled (z : ℤ) (i : Fin G2.numRoots) :
      ∀ n, ∀ w ∈ M, Associative.dividedPower n (z • E i) • w ∈ M := by
    intro n w hw
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (hstable i n w hw) _
  have hxy : E α * E β = E β * E α + c • E γ :=
    mul_eq_mul_add_zsmul_of_lie_eq ρ hij
  have hxz : E α * (c • E γ) = (c • E γ) * E α + 2 • (d • E δ) := by
    simpa only [one_zsmul] using zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
      (p := 1) (q := c) (r := d) (n := 2) (by simpa using hik)
  have hxw : E α * (d • E δ) = (d • E δ) * E α + 3 • (a • E ε) := by
    simpa only [one_zsmul] using zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
      (p := 1) (q := d) (r := a) (n := 3) (by simpa using hil)
  have hwz : (d • E δ) * (c • E γ) = (c • E γ) * (d • E δ) + 3 • (b • E ζ) :=
    zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ hlk
  -- Apply the integral exponential identity and put integer factors back in the parameters.
  refine Units.ext ?_
  simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
  rw [← baseChangeExp_zsmul c M (hstable γ) (hscaled c γ)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil γ),
    ← baseChangeExp_zsmul d M (hstable δ) (hscaled d δ)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil δ),
    ← baseChangeExp_zsmul a M (hstable ε) (hscaled a ε)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil ε),
    ← baseChangeExp_zsmul b M (hstable ζ) (hscaled b ζ)
      (isNilpotent_apply_ι_chevalleySystem ρ hnil ζ)]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul M hxy hxz hxw hwz
    ((commute_of_lie_eq_zero ρ him).smul_right a)
    ((commute_of_lie_eq_zero ρ hio).smul_right b)
    ((commute_of_lie_eq_zero ρ hjk).smul_right c)
    (((commute_of_lie_eq_zero ρ hlm).smul_left d).smul_right a)
    (((commute_of_lie_eq_zero ρ hko).smul_left c).smul_right b)
    (((commute_of_lie_eq_zero ρ hlo).smul_left d).smul_right b)
    (((commute_of_lie_eq_zero ρ hmo).smul_left a).smul_right b)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil α)
    (isNilpotent_apply_ι_chevalleySystem ρ hnil β)
    ((isNilpotent_apply_ι_chevalleySystem ρ hnil γ).smul c)
    ((isNilpotent_apply_ι_chevalleySystem ρ hnil δ).smul d)
    (hstable α) (hstable β) (hscaled c γ) (hscaled d δ) (hscaled a ε) (hscaled b ζ) u v

end Lattice

end

end TauCeti.DynkinType
