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
`g2_short_long_coefficients_isUnit` shows that all four integer coefficients are units.

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

variable {ht : G2.Valid}
-- Keep the native index type so simplification does not have to unfold G2.numRoots.
variable {α β γ δ ε ζ : Fin G2.numRoots}

private theorem g2_root_eq_add_of_coordinates {i j k : Fin G2.numRoots}
    (h : g2Root k = g2Root i + g2Root j) :
    (G2.simplyConnectedRootDatum ht).root k =
      (G2.simplyConnectedRootDatum ht).root i + (G2.simplyConnectedRootDatum ht).root j := by
  rw [simplyConnectedRootDatum_G2, g2SimplyConnectedRootDatum_root]
  exact h

private theorem g2_chainBotCoeff_eq (p q : Fin G2.numRoots) :
    (G2.simplyConnectedRootDatum ht).chainBotCoeff p q =
      g2SimplyConnectedRootDatum.chainBotCoeff p q := by
  rw [simplyConnectedRootDatum_G2]
  rfl

/-- The four integer coefficients in the short–long `G₂` straightening formula are units
(that is, each is `1` or `-1`). The divisions are taken in `ℤ`, before any base change. -/
theorem g2_short_long_coefficients_isUnit
    (hα : g2Length α = 1) (hβ : g2Length β = 3)
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hε : g2Root ε = g2Root α + g2Root δ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    let c := G2.structureConstant ht α β
    let d := c * (G2.structureConstant ht α γ / 2)
    let a := d * (G2.structureConstant ht α δ / 3)
    let b := d * c * (G2.structureConstant ht δ γ / 3)
    IsUnit c ∧ IsUnit d ∧ IsUnit a ∧ IsUnit b := by
  obtain ⟨hij, hik, hil, hlk⟩ := g2_chainBotCoeff_of_short_add_long_eq_root α β γ δ ζ hα hβ
    (by simpa only [g2SimplyConnectedRootDatum_root] using hγ)
    (by simpa only [g2SimplyConnectedRootDatum_root] using hδ)
    (by simpa only [g2SimplyConnectedRootDatum_root] using hζ)
  have values {p q r : Fin G2.numRoots} (h : g2Root r = g2Root p + g2Root q) :=
    structureConstant_eq_natCast_or_eq_neg_natCast (t := G2) (ht := ht)
      (α := p) (β := q) ⟨r, g2_root_eq_add_of_coordinates h⟩
  have hc := values hγ
  have hd := values hδ
  have ha := values hε
  have hb := values hζ
  simp only [g2_chainBotCoeff_eq, hij, hik, hil, hlk, Nat.reduceAdd, Nat.cast_ofNat]
    at hc hd ha hb
  rcases hc with hc | hc <;> rcases hd with hd | hd <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> norm_num [hc, hd, ha, hb]

private theorem long_short_divisibility
    (hα : g2Length α = 1) (hβ : g2Length β = 3)
    (hγ : g2Root γ = g2Root α + g2Root β)
    (hδ : g2Root δ = g2Root α + g2Root γ)
    (hζ : g2Root ζ = g2Root δ + g2Root γ) :
    (2 : ℤ) ∣ G2.structureConstant ht α γ ∧
      (3 : ℤ) ∣ G2.structureConstant ht α δ ∧
      (3 : ℤ) ∣ G2.structureConstant ht δ γ := by
  obtain ⟨_, hik, hil, hlk⟩ := g2_chainBotCoeff_of_short_add_long_eq_root α β γ δ ζ hα hβ
    (by simpa only [g2SimplyConnectedRootDatum_root] using hγ)
    (by simpa only [g2SimplyConnectedRootDatum_root] using hδ)
    (by simpa only [g2SimplyConnectedRootDatum_root] using hζ)
  have dvd (p q : Fin G2.numRoots) :=
    chainBotCoeff_add_one_dvd_structureConstant (t := G2) (ht := ht) (α := p) (β := q)
  simpa only [g2_chainBotCoeff_eq, hik, hil, hlk, Nat.reduceAdd, Nat.cast_ofNat] using
    And.intro (dvd α γ) (And.intro (dvd α δ) (dvd δ γ))

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
  have hz (i j : Fin G2.numRoots) (a b : ℕ)
      (hab : (a, b) ∈ ({(4, 1), (4, 2), (1, 2), (5, 2), (4, 3), (5, 3), (6, 3)} :
        Finset (ℕ × ℕ)))
      (heq : g2Root i + g2Root j = a • g2Root α + b • g2Root β) :
      ⁅G2.chevalleySystem ht i, G2.chevalleySystem ht j⁆ = 0 := by
    obtain ⟨hnot, hne⟩ :=
      g2_smul_short_add_smul_long_notMem_range_root_and_ne_zero α β hα hβ
        ⟨γ, by simpa only [g2SimplyConnectedRootDatum_root] using hγ⟩ a b hab
    simp only [g2SimplyConnectedRootDatum_root] at hnot hne
    apply lie_chevalleySystem_eq_zero (t := G2) (ht := ht) <;>
      rw [simplyConnectedRootDatum_G2]
    · simpa only [g2SimplyConnectedRootDatum_root] using heq.symm ▸ hnot
    · simpa only [g2SimplyConnectedRootDatum_root] using heq.symm ▸ hne
  exact ⟨hz α ε 4 1 (by decide) (by rw [hε, hδ, hγ]; module),
    hz α ζ 4 2 (by decide) (by rw [hζ, hδ, hγ]; module),
    hz β γ 1 2 (by decide) (by rw [hγ]; module),
    hz δ ε 5 2 (by decide) (by rw [hε, hδ, hγ]; module),
    hz γ ζ 4 3 (by decide) (by rw [hζ, hδ, hγ]; module),
    hz δ ζ 5 3 (by decide) (by rw [hζ, hδ, hγ]; module),
    hz ε ζ 6 3 (by decide) (by rw [hε, hζ, hδ, hγ]; module)⟩

noncomputable section

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
  obtain ⟨h2, h3, h3'⟩ := long_short_divisibility (ht := ht) hα hβ hγ hδ hζ
  dsimp only
  refine ⟨lie_chevalleySystem_eq_structureConstant_zsmul
    (g2_root_eq_add_of_coordinates hγ), ?_, ?_, ?_⟩
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul
      (g2_root_eq_add_of_coordinates hδ), smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h2]
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul
      (g2_root_eq_add_of_coordinates hε), smul_smul]
    congr 1
    rw [mul_left_comm, Int.mul_ediv_cancel' h3]
  · rw [lie_chevalleySystem_eq_structureConstant_zsmul
      (g2_root_eq_add_of_coordinates hζ), smul_smul]
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
  have hscaled := dividedPower_zsmul_chevalleySystem_smul_mem ρ M hM hnil
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
