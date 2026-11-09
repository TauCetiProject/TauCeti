/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Subgroup
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.RootString
import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
import TauCeti.RingTheory.Nilpotent.RootString.G2.Basic

/-!
# Long–short straightening for the pinned G₂ root subgroups

For a short root α and a long root β with α + β a root, this file proves the four-factor
straightening relation for the native root subgroups on any Kostant-stable lattice. The output
roots are γ = α + β, δ = 2α + β, ε = 3α + β and ζ = 3α + 2β. All coefficients come from the
integer structure constants of the pinned Chevalley system; division by two and three takes
place exactly in ℤ, before passage to the value ring. Thus the relation also holds in
characteristics two and three.

The order is xβ xγ xδ xε xζ xα. In particular the coefficient at ζ is a straightening
coefficient, not the coefficient in an element commutator with its β factor cancelled.
These relations reorder arbitrary root elements, not just the two pinned simple roots.

The operator transport follows
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints_mul_of_lie_eq_three_nsmul`,
using `TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul`. Here the requisite
bracket relations are proved from the numbered root datum, rather than supplied as hypotheses.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType

open Set TensorProduct TauCeti.UniversalEnvelopingAlgebra

private theorem long_short_output_lengths (i j k : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 3) :
    (g2Root k = 2 • g2Root i + g2Root j → g2Length k = 1) ∧
      (g2Root k = 3 • g2Root i + 2 • g2Root j → g2Length k = 3) := by
  simp only [g2Root_apply, g2Length_apply] at hi hj ⊢
  revert i j k
  decide +kernel

-- The seven sums appearing in the vanishing brackets of the straightening identity.
private def long_short_excludedSums (i j : Fin 12) : Set (Fin 2 → ℤ) :=
  {4 • g2Root i + g2Root j, 4 • g2Root i + 2 • g2Root j,
    g2Root i + 2 • g2Root j, 5 • g2Root i + 2 • g2Root j,
    4 • g2Root i + 3 • g2Root j, 5 • g2Root i + 3 • g2Root j,
    6 • g2Root i + 3 • g2Root j}

private theorem long_short_exclusions (i j : Fin 12)
    (hi : g2Length i = 1) (hj : g2Length j = 3)
    (hadd : g2Root i + g2Root j ∈ range g2Root) :
    ∀ v ∈ long_short_excludedSums i j, v ∉ range g2Root ∧ v ≠ 0 := by
  simp only [long_short_excludedSums, mem_insert_iff, mem_singleton_iff, forall_eq_or_imp,
    forall_eq, mem_range, not_exists, g2Root_apply, g2Length_apply] at hi hj hadd ⊢
  revert i j
  decide +kernel

variable {ht : G2.Valid}
variable {α β γ δ ε ζ : Fin 12}

private theorem long_short_coordinates
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    g2Root δ = 2 • g2Root α + g2Root β ∧
      g2Root ε = 3 • g2Root α + g2Root β ∧
      g2Root ζ = 3 • g2Root α + 2 • g2Root β := by
  rw [hζ, hε, hδ, hγ]
  exact ⟨by abel, by abel, by abel⟩

private theorem long_short_divisibility
    (hα : g2Length α = 1) (hβ : g2Length β = 3)
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    (2 : ℤ) ∣ G2.structureConstant ht α γ ∧
      (3 : ℤ) ∣ G2.structureConstant ht α δ ∧
      (3 : ℤ) ∣ G2.structureConstant ht δ γ := by
  have hli := g2SimplyConnectedRootDatum.linearIndependent_of_add_mem_range_root'
    (i := α) (j := β) ⟨γ, by simpa only [g2SimplyConnectedRootDatum_root] using hγ⟩
  have hbot := (g2_chainBotCoeff_eq_zero_and_chainTopCoeff_eq_three_of_short_long
    α β hα hβ ⟨γ, by simpa only [g2SimplyConnectedRootDatum_root] using hγ⟩).1
  have hbγ : g2SimplyConnectedRootDatum.chainBotCoeff α γ = 1 := by
    simpa [hbot] using g2SimplyConnectedRootDatum.chainBotCoeff_of_add hli
      (by simpa only [g2SimplyConnectedRootDatum_root] using hγ.trans (add_comm _ _))
  have hbδ : g2SimplyConnectedRootDatum.chainBotCoeff α δ = 2 := by
    have hli' := g2SimplyConnectedRootDatum.linearIndependent_of_add_mem_range_root'
      (i := α) (j := γ) ⟨δ, by simpa only [g2SimplyConnectedRootDatum_root] using hδ⟩
    simpa [hbγ] using g2SimplyConnectedRootDatum.chainBotCoeff_of_add hli'
      (by simpa only [g2SimplyConnectedRootDatum_root] using hδ.trans (add_comm _ _))
  obtain ⟨hδcoord, _, hζcoord⟩ := long_short_coordinates hγ hδ hε hζ
  have hγlen := g2Length_eq_one_of_long_add_short_eq_root β α γ hβ hα
    (by simpa only [g2SimplyConnectedRootDatum_root] using hγ.trans (add_comm _ _))
  have hbζ := g2_chainBotCoeff_eq_two_of_short_add_short_eq_long δ γ ζ
    ((long_short_output_lengths α β δ hα hβ).1 hδcoord) hγlen
    ((long_short_output_lengths α β ζ hα hβ).2 hζcoord)
    (by simpa only [g2SimplyConnectedRootDatum_root] using hζ.trans (add_comm _ _))
  have hc2 := structureConstant_eq_natCast_or_eq_neg_natCast (t := G2) (ht := ht)
    (α := α) (β := γ) ⟨δ, (g2_root_add_iff α γ δ).2 hδ⟩
  have hc3 := structureConstant_eq_natCast_or_eq_neg_natCast (t := G2) (ht := ht)
    (α := α) (β := δ) ⟨ε, (g2_root_add_iff α δ ε).2 hε⟩
  have hc3' := structureConstant_eq_natCast_or_eq_neg_natCast (t := G2) (ht := ht)
    (α := δ) (β := γ) ⟨ζ, (g2_root_add_iff δ γ ζ).2 hζ⟩
  obtain ⟨hbγ', hbδ', hbζ'⟩ :
      (G2.simplyConnectedRootDatum ht).chainBotCoeff α γ = 1 ∧
        (G2.simplyConnectedRootDatum ht).chainBotCoeff α δ = 2 ∧
        (G2.simplyConnectedRootDatum ht).chainBotCoeff δ γ = 2 := by
    rw [simplyConnectedRootDatum_G2]
    exact ⟨hbγ, hbδ, hbζ⟩
  omega

private theorem long_short_zero_brackets
    (hα : g2Length α = 1) (hβ : g2Length β = 3)
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    let e := G2.chevalleySystem ht
    (⁅e α, e ε⁆ = 0) ∧ (⁅e α, e ζ⁆ = 0) ∧ (⁅e β, e γ⁆ = 0) ∧
      (⁅e δ, e ε⁆ = 0) ∧ (⁅e γ, e ζ⁆ = 0) ∧ (⁅e δ, e ζ⁆ = 0) ∧
      (⁅e ε, e ζ⁆ = 0) := by
  have hex := long_short_exclusions α β hα hβ ⟨γ, hγ⟩
  have hz (i j : Fin 12) (h : g2Root i + g2Root j ∈ long_short_excludedSums α β) :
      ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht j⁆ = 0 :=
    lie_chevalleySystem_eq_zero (t := G2) (ht := ht)
      (by rw [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root]; exact (hex _ h).1)
      (by rw [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root]; exact (hex _ h).2)
  obtain ⟨hδcoord, hεcoord, hζcoord⟩ := long_short_coordinates hγ hδ hε hζ
  have h1 : g2Root α + g2Root ε = 4 • g2Root α + g2Root β := by rw [hεcoord]; abel
  have h2 : g2Root α + g2Root ζ = 4 • g2Root α + 2 • g2Root β := by rw [hζcoord]; abel
  have h3 : g2Root β + g2Root γ = g2Root α + 2 • g2Root β := by rw [hγ]; abel
  have h4 : g2Root δ + g2Root ε = 5 • g2Root α + 2 • g2Root β := by
    rw [hδcoord, hεcoord]; abel
  have h5 : g2Root γ + g2Root ζ = 4 • g2Root α + 3 • g2Root β := by rw [hγ, hζcoord]; abel
  have h6 : g2Root δ + g2Root ζ = 5 • g2Root α + 3 • g2Root β := by
    rw [hδcoord, hζcoord]; abel
  have h7 : g2Root ε + g2Root ζ = 6 • g2Root α + 3 • g2Root β := by
    rw [hεcoord, hζcoord]; abel
  exact ⟨hz _ _ (by simp [long_short_excludedSums, h1]),
    hz _ _ (by simp [long_short_excludedSums, h2]),
    hz _ _ (by simp [long_short_excludedSums, h3]),
    hz _ _ (by simp [long_short_excludedSums, h4]),
    hz _ _ (by simp [long_short_excludedSums, h5]),
    hz _ _ (by simp [long_short_excludedSums, h6]),
    hz _ _ (by simp [long_short_excludedSums, h7])⟩

noncomputable section

-- Keep the uniform root-index type here so the general root-subgroup simp API applies
-- without conversion between Fin G2.numRoots and Fin 12.
variable {α β γ δ ε ζ : Fin G2.numRoots}

private theorem long_short_scaled_brackets
    (hα : g2Length α = 1) (hβ : g2Length β = 3)
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    let e := G2.chevalleySystem ht
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    (⁅e α, e β⁆ = c • e γ) ∧
      (c • ⁅e α, e γ⁆ = (2 * d) • e δ) ∧
      (d • ⁅e α, e δ⁆ = (3 * a) • e ε) ∧
      ((d * c) • ⁅e δ, e γ⁆ = (3 * b) • e ζ) := by
  obtain ⟨h2, h3, h3'⟩ := long_short_divisibility (ht := ht) hα hβ hγ hδ hε hζ
  dsimp only
  refine ⟨lie_chevalleySystem_eq_structureConstant_zsmul
    ((g2_root_add_iff α β γ).2 hγ), ?_, ?_, ?_⟩
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul
      ((g2_root_add_iff α γ δ).2 hδ), smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h2]
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul
      ((g2_root_add_iff α δ ε).2 hε), smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h3]
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul
      ((g2_root_add_iff δ γ ζ).2 hζ), smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h3']

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ (G2.lieAlgebra ht) →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm (G2.lieBasis ht).rootGenerator (G2.lieBasis ht).h,
  ∀ v ∈ M, ρ u v ∈ M)
variable (hnil : ∀ i, IsNilpotent
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ((G2.lieBasis ht).rootGenerator i))))

attribute [local instance high] Algebra.toModule

/-- **Long–short G₂ straightening on every Kostant-stable lattice.** The four output roots
are `γ = α + β`, `δ = 2α + β`, `ε = 3α + β` and `ζ = 3α + 2β`. The coefficients are integers
computed from the native structure constants, with exact division performed before reduction
in the value ring. The last coefficient is for the displayed product order, not for the
commutator order. -/
theorem chevalleyRootSubgroup_mul_of_g2_long_short
    (hα : g2Length α = 1) (hβ : g2Length β = 3)
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ)
    (A : CommAlgCat ℤ) (u v : A) :
    let N := G2.structureConstant ht
    let c := N α β
    let d := c * (N α γ / 2)
    let a := d * (N α δ / 3)
    let b := d * c * (N δ γ / 3)
    let x := fun i w => chevalleyRootSubgroup ρ M hM hnil i A (Multiplicative.ofAdd w)
    x α u * x β v =
      x β v * x γ ((c : A) * (u * v)) * x δ ((d : A) * (u ^ 2 * v)) *
        x ε ((a : A) * (u ^ 3 * v)) * x ζ ((b : A) * (u ^ 3 * v ^ 2)) * x α u := by
  let N := G2.structureConstant ht
  let c := N α β
  let d := c * (N α γ / 2)
  let a := d * (N α δ / 3)
  let b := d * c * (N δ γ / 3)
  let E := fun i => ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (G2.chevalleySystem ht i))
  obtain ⟨hbracket, hscaled2, hscaled3, hscaled3'⟩ :=
    long_short_scaled_brackets (ht := ht) hα hβ hγ hδ hε hζ
  obtain ⟨hαε, hαζ, hβγ, hδε, hγζ, hδζ, hεζ⟩ :=
    long_short_zero_brackets (ht := ht) hα hβ hγ hδ hε hζ
  -- Translate the native brackets into the scaled operator relations of the integral identity.
  have hxy : E α * E β = E β * E α + c • E γ :=
    mul_eq_mul_add_zsmul_of_lie_eq ρ hbracket
  have hxz : E α * (c • E γ) = (c • E γ) * E α + 2 • (d • E δ) := by
    simpa only [one_zsmul] using zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
      (p := 1) (q := c) (r := d) (n := 2) (by simpa using hscaled2)
  have hxw : E α * (d • E δ) = (d • E δ) * E α + 3 • (a • E ε) := by
    simpa only [one_zsmul] using zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
      (p := 1) (q := d) (r := a) (n := 3) (by simpa using hscaled3)
  have hwz : (d • E δ) * (c • E γ) = (c • E γ) * (d • E δ) + 3 • (b • E ζ) :=
    zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ hscaled3'
  -- All-root divided-power stability also gives stability for the four scaled operators.
  have hstable := dividedPower_chevalleySystem_smul_mem ρ M hM hnil
  have hscaled (z : ℤ) (i : Fin G2.numRoots) (n : ℕ) :
      ∀ w ∈ M, Associative.dividedPower n (z • E i) • w ∈ M := by
    intro w hw
    rw [Associative.dividedPower_zsmul, smul_assoc]
    exact M.zsmul_mem (hstable i n w hw) _
  have hn := isNilpotent_apply_ι_chevalleySystem ρ hnil
  -- Use the value API, then absorb the integer coefficients into the exponentials.
  apply Units.ext
  simp only [Units.val_mul, chevalleyRootSubgroup_val, toAdd_ofAdd]
  rw [← baseChangeExp_zsmul c M (hstable γ) (hscaled c γ) (hn γ),
    ← baseChangeExp_zsmul d M (hstable δ) (hscaled d δ) (hn δ),
    ← baseChangeExp_zsmul a M (hstable ε) (hscaled a ε) (hn ε),
    ← baseChangeExp_zsmul b M (hstable ζ) (hscaled b ζ) (hn ζ)]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul M hxy hxz hxw hwz
    ((commute_of_lie_eq_zero ρ hαε).smul_right a)
    ((commute_of_lie_eq_zero ρ hαζ).smul_right b)
    ((commute_of_lie_eq_zero ρ hβγ).smul_right c)
    (((commute_of_lie_eq_zero ρ hδε).smul_left d).smul_right a)
    (((commute_of_lie_eq_zero ρ hγζ).smul_left c).smul_right b)
    (((commute_of_lie_eq_zero ρ hδζ).smul_left d).smul_right b)
    (((commute_of_lie_eq_zero ρ hεζ).smul_left a).smul_right b)
    (hn α) (hn β) ((hn γ).smul c) ((hn δ).smul d)
    (hstable α) (hstable β) (hscaled c γ) (hscaled d δ) (hscaled a ε) (hscaled b ζ) u v

end

end TauCeti.DynkinType
