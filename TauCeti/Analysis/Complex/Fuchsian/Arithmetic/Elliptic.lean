/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic.Basic
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Coset description of Fuchsian elliptic orbits

For a subgroup `Γ' ≤ PSL(2, ℤ)`, the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` of orders
`2` and `3` are in canonical bijection with the `S`-fixed and `R`-fixed cosets in `PSL(2, ℤ) ⧸ Γ'`
(`TauCeti.ModularGroup.fixedCosetSEquivOrderTwoEllipticOrbits` and
`TauCeti.ModularGroup.fixedCosetREquivOrderThreeEllipticOrbits`), sending a fixed coset `g Γ'` to
the orbit of `g⁻¹ • i` or `g⁻¹ • ρ`.
-/

public noncomputable section

open Equiv Function Matrix Matrix.ProjectiveSpecialLinearGroup MulAction Subgroup UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-- If `q₂` is fixed by `s` and the level-one stabilizer of `z₀` is `⟨s⟩`, then
`inverseTranslateOrbit Γ' z₀` can merge another coset `q₁` with `q₂` only when `q₁ = q₂`. -/
theorem injective_inverseTranslateOrbit_on_fixed {Γ' : Subgroup PSL(2, ℤ)}
    {z₀ : ℍ} {s : PSL(2, ℤ)} (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    {q₁ q₂ : PSL(2, ℤ) ⧸ Γ'} (hq₂ : s • q₂ = q₂)
    (horb : inverseTranslateOrbit Γ' z₀ q₁ = inverseTranslateOrbit Γ' z₀ q₂) : q₁ = q₂ := by
  have hstab' : ∀ g : PSL(2, ℤ), psl2zToPSL2R g • z₀ = z₀ ↔ g ∈ Subgroup.zpowers s := fun g ↦ by
    rw [UpperHalfPlane.psl2zToPSL2R_smul, ← mem_stabilizer_iff, hstab]
  rw [inverseTranslateOrbit_eq_iff_mem_orbit_zpowers Γ' hstab', mem_orbit_iff] at horb
  obtain ⟨⟨t, ht⟩, hsmul⟩ := horb
  have ht_fix : t • q₂ = q₂ :=
    mem_stabilizer_iff.mp ((Subgroup.zpowers_le.mpr (mem_stabilizer_iff.mpr hq₂)) ht)
  rw [Subgroup.smul_def, ht_fix] at hsmul; exact hsmul.symm

private def stabilizerSubgroupOfEquiv (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ} {s : PSL(2, ℤ)}
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s) (g : PSL(2, ℤ)) :
    (MulAut.conj g • Γ').subgroupOf (Subgroup.zpowers s) ≃
      stabilizer (Γ'.map psl2zToPSL2R) (psl2zToPSL2R g⁻¹ • z₀) :=
  Equiv.ofBijective
    (fun ⟨t, ht⟩ ↦ ⟨⟨psl2zToPSL2R (g⁻¹ * t.val * g),
        Subgroup.mem_map_of_mem psl2zToPSL2R
          ((TauCeti.mem_conj_smul g Γ' t).mp (Subgroup.mem_subgroupOf.mp ht))⟩, by
      have htfix : t.val • z₀ = z₀ := mem_stabilizer_iff.mp (by rw [hstab]; exact t.property)
      rw [mem_stabilizer_iff, Subgroup.smul_def, ← mul_smul, ← map_mul,
        mul_inv_cancel_right, map_mul, mul_smul,
        UpperHalfPlane.psl2zToPSL2R_smul, UpperHalfPlane.psl2zToPSL2R_smul, htfix,
        ← UpperHalfPlane.psl2zToPSL2R_smul]⟩)
    ⟨fun ⟨⟨t₁, _⟩, _⟩ ⟨⟨t₂, _⟩, _⟩ h ↦ Subtype.ext <| Subtype.ext <| by
      simpa using psl2zToPSL2R_injective (congrArg (fun y ↦ y.val.val) h),
    fun ⟨⟨x, hx⟩, hxfix⟩ ↦ by
      obtain ⟨h, hhΓ, rfl⟩ := Subgroup.mem_map.mp hx
      -- Pull the stabilizer condition at `g⁻¹ • z₀` back to `z₀` via conjugation by `g`.
      have hfix : (g * h * g⁻¹) • z₀ = z₀ := by
        rw [mem_stabilizer_iff, Subgroup.smul_def] at hxfix; dsimp only at hxfix
        rw [UpperHalfPlane.psl2zToPSL2R_smul, UpperHalfPlane.psl2zToPSL2R_smul] at hxfix
        rw [mul_smul, mul_smul, hxfix, smul_inv_smul]
      refine ⟨⟨⟨g * h * g⁻¹, hstab ▸ mem_stabilizer_iff.mpr hfix⟩,
        Subgroup.mem_subgroupOf.mpr ((TauCeti.mem_conj_smul g Γ' _).mpr
          (by simpa [mul_assoc] using hhΓ))⟩,
        Subtype.ext <| Subtype.ext <| congrArg psl2zToPSL2R (by group)⟩⟩

/-- When `stabilizer PSL(2, ℤ) z₀ = ⟨s⟩` has order `p > 0`, the `(Γ'.map psl2zToPSL2R)`-orbit of
`inverseTranslateOrbit Γ' z₀ q` has stabilizer order `p` iff `s` fixes the coset `q`. -/
theorem cardStabilizerOnOrbit_inverseTranslateOrbit_eq_iff
    {Γ' : Subgroup PSL(2, ℤ)} {z₀ : ℍ} {s : PSL(2, ℤ)} {p : ℕ} (hp : 0 < p)
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    (hcard : Nat.card (Subgroup.zpowers s) = p) (q : PSL(2, ℤ) ⧸ Γ') :
    cardStabilizerOnOrbit (inverseTranslateOrbit Γ' z₀ q) = p ↔ s • q = q := by
  induction q using QuotientGroup.induction_on with | H g =>
  have : Finite (Subgroup.zpowers s) := Nat.finite_of_card_ne_zero (hcard ▸ hp.ne')
  -- Identify the stabilizer of `g⁻¹ • z₀` in `Γ'` with `(g Γ' g⁻¹) ⊓ ⟨s⟩`.
  rw [inverseTranslateOrbit_mk, cardStabilizerOnOrbit_mk,
    ← Nat.card_congr (stabilizerSubgroupOfEquiv Γ' hstab g), ← hcard,
    Subgroup.card_eq_iff_eq_top, Subgroup.eq_top_iff', TauCeti.smul_quotientGroup_mk_eq_self_iff]
  refine ⟨fun htop ↦ (TauCeti.mem_conj_smul g Γ' s).mp
    (Subgroup.mem_subgroupOf.mp (htop ⟨s, Subgroup.mem_zpowers s⟩)), fun hs ⟨t, ht⟩ ↦ ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hconj : g⁻¹ * s ^ k * g = (g⁻¹ * s * g) ^ k := by
    simpa [MulAut.conj_apply] using map_zpow (MulAut.conj g⁻¹) s k
  rw [Subgroup.mem_subgroupOf, TauCeti.mem_conj_smul, hconj]
  exact zpow_mem hs k

/-- Bijection between `s`-fixed cosets in `PSL(2, ℤ) ⧸ Γ'` and `(Γ'.map psl2zToPSL2R)`-orbits of
`g • z₀` having stabilizer order `p`, when `stabilizer PSL(2, ℤ) z₀ = ⟨s⟩` has order `p > 0`. -/
def fixedCosetEquivEllipticTranslateOrbit (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ}
    {s : PSL(2, ℤ)} {p : ℕ} (hp : 0 < p)
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    (hcard : Nat.card (Subgroup.zpowers s) = p) :
    {q : PSL(2, ℤ) ⧸ Γ' // s • q = q} ≃
      {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
        (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • z₀)) ∧
          cardStabilizerOnOrbit o = p} :=
  Equiv.ofBijective
    (fun q ↦ ⟨inverseTranslateOrbit Γ' z₀ q.val,
      ⟨by induction q.val using QuotientGroup.induction_on with | H g =>
          exact ⟨g⁻¹, by rw [inverseTranslateOrbit_mk, UpperHalfPlane.psl2zToPSL2R_smul]⟩,
        (cardStabilizerOnOrbit_inverseTranslateOrbit_eq_iff hp hstab hcard q.val).mpr q.property⟩⟩)
    ⟨fun ⟨_, _⟩ ⟨_, hq₂⟩ horb ↦ Subtype.ext <|
      injective_inverseTranslateOrbit_on_fixed hstab hq₂ (congrArg Subtype.val horb),
    fun ⟨_, ⟨g, rfl⟩, ho⟩ ↦ ⟨⟨((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'), by
        rw [← cardStabilizerOnOrbit_inverseTranslateOrbit_eq_iff hp hstab hcard,
          inverseTranslateOrbit_mk, inv_inv, UpperHalfPlane.psl2zToPSL2R_smul]; exact ho⟩,
      Subtype.ext <| by
        dsimp only; rw [inverseTranslateOrbit_mk, inv_inv, UpperHalfPlane.psl2zToPSL2R_smul]⟩⟩

/-- Underlying orbit of `fixedCosetEquivEllipticTranslateOrbit`. -/
@[simp] theorem fixedCosetEquivEllipticTranslateOrbit_val (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ}
    {s : PSL(2, ℤ)} {p : ℕ} (hp : 0 < p)
    (hstab : stabilizer PSL(2, ℤ) z₀ = Subgroup.zpowers s)
    (hcard : Nat.card (Subgroup.zpowers s) = p) (q : {q : PSL(2, ℤ) ⧸ Γ' // s • q = q}) :
    (fixedCosetEquivEllipticTranslateOrbit Γ' hp hstab hcard q).val =
      inverseTranslateOrbit Γ' z₀ q.val := (rfl)

/-- For an elliptic order `p` whose points all lie in the `SL(2, ℤ)`-orbit of `z₀`, elliptic
orbits of order `p` are the orbits of `PSL(2, ℤ)`-translates of `z₀` of stabilizer order `p`. -/
def ellipticTranslateEquivOrder (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ} {p : ℕ}
    (hz₀ : ∀ z : ℍ, Nat.card (stabilizer (Γ'.liftSL.map sl2zToPSL2R) z) = p →
      ∃ γ : SL(2, ℤ), γ • z₀ = z) :
    {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
      (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • z₀)) ∧
        cardStabilizerOnOrbit o = p} ≃
      {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit o = p} where
  toFun o := ⟨o.val, o.property.2⟩
  invFun o := ⟨o.val, ⟨by
    obtain ⟨o', ho'⟩ := o; induction o' using Quotient.inductionOn with | h z =>
    rw [cardStabilizerOnOrbit_mk, ← Γ'.map_liftSL_sl2zToPSL2R] at ho'
    obtain ⟨γ, rfl⟩ := hz₀ z ho'
    exact ⟨(γ : PSL(2, ℤ)), by rw [UpperHalfPlane.pslMk_smul]⟩, o.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Underlying orbit of `ellipticTranslateEquivOrder`. -/
@[simp] theorem ellipticTranslateEquivOrder_val (Γ' : Subgroup PSL(2, ℤ)) {z₀ : ℍ} {p : ℕ}
    (hz₀ : ∀ z : ℍ, Nat.card (stabilizer (Γ'.liftSL.map sl2zToPSL2R) z) = p →
      ∃ γ : SL(2, ℤ), γ • z₀ = z)
    (o : {o : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ //
      (∃ g : PSL(2, ℤ), o = Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g • z₀)) ∧
        cardStabilizerOnOrbit o = p}) :
    (ellipticTranslateEquivOrder Γ' hz₀ o).val = o.val := (rfl)

/-- **Order-`2` elliptic orbits via `S`-fixed cosets.** The cosets in `PSL(2, ℤ) ⧸ Γ'` fixed by
`S` are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having stabilizer
order `2`: the fixed coset `g Γ'` maps to the orbit of `g⁻¹ • i`. -/
def fixedCosetSEquivOrderTwoEllipticOrbits (Γ' : Subgroup PSL(2, ℤ)) :
    {q : PSL(2, ℤ) ⧸ Γ' // (S : PSL(2, ℤ)) • q = q} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 2} :=
  (fixedCosetEquivEllipticTranslateOrbit Γ' two_pos stabilizer_psl_I_eq_zpowers
    (by rw [Nat.card_zpowers, orderOf_coe_S])).trans
    (ellipticTranslateEquivOrder Γ' fun z _ ↦ by
      rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one (z := z) (by omega) with
        ⟨γ, rfl, -⟩ | ⟨_, -, h3⟩
      · exact ⟨γ, rfl⟩
      · omega)

/-- Evaluating `fixedCosetSEquivOrderTwoEllipticOrbits` on `g Γ'` gives the orbit of `g⁻¹ • i`. -/
@[simp] theorem fixedCosetSEquivOrderTwoEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ)) (g : PSL(2, ℤ))
    (hg : (S : PSL(2, ℤ)) • (g : PSL(2, ℤ) ⧸ Γ') = g) :
    (fixedCosetSEquivOrderTwoEllipticOrbits Γ' ⟨g, hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • I) := by
  rw [fixedCosetSEquivOrderTwoEllipticOrbits, Equiv.trans_apply, ellipticTranslateEquivOrder_val,
    fixedCosetEquivEllipticTranslateOrbit_val, inverseTranslateOrbit_mk,
    UpperHalfPlane.psl2zToPSL2R_smul]

/-- **Order-`3` elliptic orbits via `R`-fixed cosets.** The cosets in `PSL(2, ℤ) ⧸ Γ'` fixed by
`R = S T` are in bijection with the elliptic orbits of `Γ'.map psl2zToPSL2R` on `ℍ` having
stabilizer order `3`: the fixed coset `g Γ'` maps to the orbit of `g⁻¹ • ρ`. -/
def fixedCosetREquivOrderThreeEllipticOrbits (Γ' : Subgroup PSL(2, ℤ)) :
    {q : PSL(2, ℤ) ⧸ Γ' // (R : PSL(2, ℤ)) • q = q} ≃
      {q : orbitRel.Quotient (Γ'.map psl2zToPSL2R) ℍ // cardStabilizerOnOrbit q = 3} :=
  (fixedCosetEquivEllipticTranslateOrbit Γ' (by decide) stabilizer_psl_ρ_eq_zpowers
    (by rw [Nat.card_zpowers, orderOf_coe_R])).trans
    (ellipticTranslateEquivOrder Γ' fun z _ ↦ by
      rcases Γ'.liftSL.exists_smul_eq_of_card_stabilizer_ne_one (z := z) (by omega) with
        ⟨_, -, h2⟩ | ⟨γ, rfl, -⟩
      · omega
      · exact ⟨γ, rfl⟩)

/-- Evaluating `fixedCosetREquivOrderThreeEllipticOrbits` on `g Γ'` gives the orbit of
`g⁻¹ • ρ`. -/
@[simp] theorem fixedCosetREquivOrderThreeEllipticOrbits_mk (Γ' : Subgroup PSL(2, ℤ))
    (g : PSL(2, ℤ)) (hg : (R : PSL(2, ℤ)) • (g : PSL(2, ℤ) ⧸ Γ') = g) :
    (fixedCosetREquivOrderThreeEllipticOrbits Γ' ⟨g, hg⟩).val =
      Quotient.mk (orbitRel (Γ'.map psl2zToPSL2R) ℍ) (g⁻¹ • ρ) := by
  rw [fixedCosetREquivOrderThreeEllipticOrbits, Equiv.trans_apply, ellipticTranslateEquivOrder_val,
    fixedCosetEquivEllipticTranslateOrbit_val, inverseTranslateOrbit_mk,
    UpperHalfPlane.psl2zToPSL2R_smul]

end TauCeti.ModularGroup
