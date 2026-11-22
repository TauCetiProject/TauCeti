/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ArithmeticSubgroups
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
import TauCeti.GroupTheory.Coset.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.Modular.Stabilizer
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The projective valence formula

For a finite-index `Γ ≤ SL(2, ℤ)` the general-level valence formula
`TauCeti.ModularForm.valence_formula_finiteIndex` is read on the **full** coset space: its
interior weights are `2 / |Stab_Γ P|`, its cusp terms are indexed by the `T`-orbits on
`SL(2, ℤ) ⧸ Γ`, and its total is `k · [SL(2, ℤ) : Γ] / 12`. This file reads the same identity on
the effective quotient `±Γ \ ℍ`, the quotient by the image of `Γ` in `PSL(2, ℤ)`:

`Σ_{P ∈ Γ \ ℍ} ord_P f / e_P + Σ_{cusps c of Γ} ord_c f = k · [SL(2, ℤ) : ±Γ] / 12`,

where `e_P` is the effective elliptic order and `ord_c f` is the geometric order at the cusp
(Diamond–Shurman, §3.2 with the author errata for pp. 74–75, and §3.3).

The passage divides the whole native identity by `δ = [±Γ : Γ]`, which is `1` when `-I ∈ Γ` and
`2` otherwise; no unconditional factor `2` enters.

* **Interior.** The effective elliptic order `e_P` (`ellipticOrderOnSubgroupOrbit`) is the order of
  the stabiliser of `P` in the image of `Γ` in `PSL(2, ℤ)`. The matrix stabiliser order is
  `|Γ ∩ {±I}| · e_P`, and `|Γ ∩ {±I}| · δ = 2`, so the native weight `2 / |Stab_Γ P|` is
  `δ / e_P`.
* **Cusps.** The cusps of `Γ` are indexed by the `T`-orbits on the cosets of `±Γ`, that is by the
  double cosets `⟨±T⟩ \ SL(2, ℤ) / Γ`. At the cusp of a coset `x (±Γ)`, of geometric width `h`
  (the least `h > 0` with `x⁻¹ T ^ h x ∈ ±Γ`), the geometric order is `orderAtCusp h (f ∣[k] x⁻¹)`:
  half the exponent of the leading term of the expansion in `q_{2h}`. At a regular cusp, where
  `f ∣[k] x⁻¹` is `h`-periodic, this is the exponent in `q_h`; at an irregular cusp it is half an
  odd integer exactly when the weight is odd. It does not depend on the representative `x`
  (`geometricOrderAtCusp_mk`).
  Every cusp translation orbit of `Γ` over a cusp `c` of `±Γ` has width `m ∣ 2h`, and its native
  order is `m / h` times the geometric order at `c`; the widths over `c` add up to `δ · h`, so the
  native cusp terms over `c` add up to `δ · ord_c f`.

## Main definitions

* `TauCeti.ModularForm.ellipticOrderOnSubgroupOrbit`: the effective elliptic order `e_P`.
* `TauCeti.ModularForm.geometricOrderAtCusp`: the geometric order of a form at a cusp of `Γ`.

## Main results

* `TauCeti.ModularForm.cardStabilizerOnOrbit_eq_card_center_mul_ellipticOrderOnSubgroupOrbit`:
  `|Stab_Γ P| = |Γ ∩ {±I}| · e_P`.
* `TauCeti.ModularForm.weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_mul_div`: the native
  interior weight is `[±Γ : Γ] · ord_P f / e_P`.
* `TauCeti.ModularForm.geometricOrderAtCusp_mk`: the geometric order may be read at any
  representative of the cusp.
* `TauCeti.ModularForm.sum_orderAtCuspTranslationOrbit_eq_relIndex_mul_sum_geometricOrderAtCusp`:
  the native cusp terms add up to `[±Γ : Γ]` times the geometric ones.
* `TauCeti.ModularForm.valence_formula_projective`: **the projective valence formula**.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §§3.2–3.3,
  and the author errata for pp. 74–75.
-/

public section

open UpperHalfPlane MulAction Function SlashInvariantForm

open scoped ModularForm MatrixGroups

namespace TauCeti

namespace ModularForm

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-! ### Effective elliptic orders -/

/-- **The effective elliptic order `e_P` of a `Γ`-orbit of `ℍ`**: the order of the stabiliser of
any point of the orbit in the image of `Γ` in `PSL(2, ℤ)`, the group acting effectively on `ℍ`.
It is the order of the matrix stabiliser divided by `|Γ ∩ {±I}|`
(`cardStabilizerOnOrbit_eq_card_center_mul_ellipticOrderOnSubgroupOrbit`). For `Γ = SL(2, ℤ)` it
is `2` on the orbit of `i`, `3` on the orbit of `ρ` and `1` elsewhere. -/
noncomputable def ellipticOrderOnSubgroupOrbit
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) : ℕ :=
  Quotient.liftOn' o
    (fun p ↦ Nat.card (stabilizer (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) p))
    fun _ b h ↦ by
      obtain ⟨g, rfl⟩ := h
      obtain ⟨γ, hγ, hg⟩ := Subgroup.mem_map.mp g.property
      refine card_stabilizer_of_orbitRel
        (mem_orbit_iff.mpr ⟨⟨QuotientGroup.mk' _ γ, γ, hγ, rfl⟩, ?_⟩)
      dsimp only
      rw [Subgroup.smul_def g, ← hg, ← Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
        ← ModularGroup.sl_moeb]
      exact (Subgroup.smul_def _ _).trans (UpperHalfPlane.pslMk_smul γ b)

/-- Evaluating the effective elliptic order on the orbit of `p` recovers the order of the
stabiliser of `p` in the image of `Γ` in `PSL(2, ℤ)`. -/
@[simp]
theorem ellipticOrderOnSubgroupOrbit_mk (p : ℍ) :
    ellipticOrderOnSubgroupOrbit
        (Quotient.mk'' p : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) =
      Nat.card (stabilizer (Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) p) :=
  (rfl)

/-- **The matrix stabiliser order is `|Γ ∩ {±I}|` times the effective elliptic order.** -/
theorem cardStabilizerOnOrbit_eq_card_center_mul_ellipticOrderOnSubgroupOrbit
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    cardStabilizerOnOrbit o =
      Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) * ellipticOrderOnSubgroupOrbit o := by
  induction o using Quotient.inductionOn' with
  | h p =>
    rw [cardStabilizerOnOrbit_mk, ellipticOrderOnSubgroupOrbit_mk,
      ← ModularGroup.card_stabilizer_eq_card_center_mul_card_stabilizer_psl]
    -- `Γ` and its image in `GL(2, ℝ)` act on `ℍ` through the same Möbius transformations, by
    -- definition of the action of `SL(2, ℤ)` on `ℍ` (`ModularGroup.sl_moeb` is `rfl`)
    exact card_stabilizer_congr
      (Γ.equivMapOfInjective _ Matrix.SpecialLinearGroup.mapGL_injective) (f := id) p
      (fun _ ↦ rfl) fun _ h ↦ h

/-- The effective elliptic order is positive. -/
theorem ellipticOrderOnSubgroupOrbit_pos
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    0 < ellipticOrderOnSubgroupOrbit o :=
  Nat.pos_of_ne_zero fun h ↦ cardStabilizerOnOrbit_ne_zero o (by
    rw [cardStabilizerOnOrbit_eq_card_center_mul_ellipticOrderOnSubgroupOrbit, h, mul_zero])

/-- `|Γ ∩ {±I}| · [±Γ : Γ] = 2`: the two factors are `2, 1` when `-I ∈ Γ` and `1, 2` otherwise. -/
private lemma card_center_subgroupOf_mul_relIndex_adjoinNegOne (Γ : Subgroup SL(2, ℤ)) :
    Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) * Γ.relIndex Γ.adjoinNegOne = 2 := by
  by_cases h : (-1 : SL(2, ℤ)) ∈ Γ
  · rw [(Matrix.SpecialLinearGroup.card_center_subgroupOf_eq_two_iff Γ).mpr h,
      Subgroup.adjoinNegOne_eq_self_iff.mpr h, Subgroup.relIndex_self]
  · rw [(Matrix.SpecialLinearGroup.card_center_subgroupOf_eq_one_iff Γ).mpr h,
      Subgroup.relIndex_adjoinNegOne_eq_two h]

/-- **The native interior weight is `[±Γ : Γ] / e_P`**: the weight `2 · ord_P f / |Stab_Γ P|` of
the general-level valence formula is `[±Γ : Γ] · ord_P f / e_P`. -/
theorem weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_mul_div
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    (o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    weightedOrderOfVanishingOnSubgroupOrbit f o =
      Γ.relIndex Γ.adjoinNegOne * (orderOfVanishingOnSubgroupOrbit f o : ℚ) /
        ellipticOrderOnSubgroupOrbit o := by
  have he : (ellipticOrderOnSubgroupOrbit o : ℚ) ≠ 0 := by
    exact_mod_cast (ellipticOrderOnSubgroupOrbit_pos o).ne'
  have hc : (Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) : ℚ) *
      Γ.relIndex Γ.adjoinNegOne = 2 := by
    exact_mod_cast card_center_subgroupOf_mul_relIndex_adjoinNegOne Γ
  have hc0 : (Nat.card ((Subgroup.center SL(2, ℤ)).subgroupOf Γ) : ℚ) ≠ 0 := by
    rintro h
    norm_num [h] at hc
  rw [weightedOrderOfVanishingOnSubgroupOrbit_def,
    cardStabilizerOnOrbit_eq_card_center_mul_ellipticOrderOnSubgroupOrbit, Nat.cast_mul,
    div_eq_div_iff (mul_ne_zero hc0 he) he]
  linear_combination -(orderOfVanishingOnSubgroupOrbit f o : ℚ) *
    (ellipticOrderOnSubgroupOrbit o : ℚ) * hc

/-! ### Geometric orders at the cusps -/

/-- `±Γ`, read in `GL(2, ℝ)`, is the image of `Γ` with `-I` adjoined. -/
private lemma coe_adjoinNegOne :
    ((Γ.adjoinNegOne : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) =
      (Γ : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne :=
  Subgroup.map_adjoinNegOne Γ _ fun g ↦ by
    rw [← neg_one_mul g, map_mul, Matrix.SpecialLinearGroup.mapGL_neg_one, neg_one_mul]

/-- The cosets of `Γ` refine those of `±Γ`. -/
private lemma subgroupOf_le_adjoinNegOne :
    (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ ≤
      (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ :=
  Subgroup.subgroupOf_mono _ (Subgroup.map_mono Γ.le_adjoinNegOne)

/-- **The geometric order of `f` at a cusp of `Γ`.** The cusps of `Γ` are indexed by the cusp
translation orbits of `±Γ`, the `T`-orbits on `𝒮ℒ ⧸ ±Γ`. At the orbit of the coset of `x`,
representing the cusp `x⁻¹ ∞` of geometric width `h`, the geometric order is
`orderAtCusp h (f ∣[k] x⁻¹)`: half the exponent of the expansion of `f ∣[k] x⁻¹` in `q_{2h}`, where
`f ∣[k] x⁻¹` is the factor `quotientFunc f` of the coset of `Γ` of `x`. This is the exponent in
`q_h` at a regular cusp, and may be half an odd integer at an irregular cusp in odd weight. It may
be read at any representative (`geometricOrderAtCusp_mk`). -/
noncomputable def geometricOrderAtCusp [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F)
    (c : CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) : ℚ :=
  orderAtCusp (cuspTranslationOrbitWidth c)
    (quotientFunc f (QuotientGroup.mk c.out.out : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))

/-- The geometric order is nonnegative. -/
theorem geometricOrderAtCusp_nonneg [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]
    (f : F) (c : CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) :
    0 ≤ geometricOrderAtCusp f c :=
  orderAtCusp_nonneg _ _

/-- The period at the cosets of `Γ` divides twice the period at the cosets of `±Γ`: if
`x⁻¹ T ^ h x = ±γ` with `γ ∈ Γ`, then `x⁻¹ T ^ (2h) x = γ²`. -/
private lemma minimalPeriod_dvd_two_mul_minimalPeriod_adjoinNegOne (x : 𝒮ℒ) :
    minimalPeriod (TSL • ·)
        (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∣
      2 * minimalPeriod (TSL • ·)
        (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  set h := minimalPeriod (TSL • ·)
    (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  have hh := (minimalPeriod_TSL_dvd_iff (𝒢 := (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) x h).mp
    dvd_rfl
  rw [coe_adjoinNegOne, Subgroup.mem_adjoinNegOne_iff] at hh
  have hsq : (x⁻¹ * TSL ^ (2 * h) * x : 𝒮ℒ) = (x⁻¹ * TSL ^ h * x) ^ 2 := by
    rw [sq, two_mul, pow_add]
    group
  rw [minimalPeriod_TSL_dvd_iff, hsq, Subgroup.coe_pow]
  rcases hh with hh | hh
  · exact pow_mem hh 2
  · simpa only [neg_sq] using pow_mem hh 2

section Order

variable [Γ.FiniteIndex] [ModularFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k]

/-- The order of the coset factor of a coset `q` of `Γ`, read in `q_{2h}` for `h` the period at the
coset of `±Γ` below `q`. It is twice the geometric order at the cusp of `q`
(`doubleWidthOrder_eq_two_mul_geometricOrderAtCusp`). -/
private noncomputable def doubleWidthOrder (f : F)
    (q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) : ℤ :=
  qExpansionOrderAtCusp
    (2 * (minimalPeriod (TSL • ·) (Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q) : ℝ))
    (quotientFunc f q)

/-- **Rescaling from the period of `q` to twice the period below it**: for `m` the period at `q`
and `h` the period at the coset of `±Γ` below it, `m ∣ 2h`, so the order in `q_{2h}` is `2h / m`
times the order in `q_m`. -/
private lemma natCast_minimalPeriod_mul_doubleWidthOrder (f : F)
    (q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    (minimalPeriod (TSL • ·) q : ℤ) * doubleWidthOrder f q =
      2 * minimalPeriod (TSL • ·) (Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q) *
        qExpansionOrderAtCusp (minimalPeriod (TSL • ·) q : ℝ) (quotientFunc f q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨t, ht⟩ := minimalPeriod_dvd_two_mul_minimalPeriod_adjoinNegOne (Γ := Γ) x
    have hpos : (0 : ℝ) < minimalPeriod (TSL • ·)
        (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
      mod_cast Nat.pos_of_neZero _
    have hw : 2 * (minimalPeriod (TSL • ·) (Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne
        (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) : ℝ) =
        (t : ℝ) * minimalPeriod (TSL • ·)
          (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
      rw [Subgroup.quotientMapOfLE_apply_mk]
      exact_mod_cast ht.trans (mul_comm _ _)
    rw [doubleWidthOrder, hw, qExpansionOrderAtCusp_nat_mul hpos (periodic_quotientFunc f _)
      (SlashInvariantForm.isBoundedAtImInfty_quotientFunc f _)
      (SlashInvariantForm.mdifferentiable_quotientFunc f _), Subgroup.quotientMapOfLE_apply_mk]
    have ht' : (2 * minimalPeriod (TSL • ·) (QuotientGroup.mk x :
        𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) : ℤ) =
        minimalPeriod (TSL • ·)
          (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) * t := by
      exact_mod_cast ht
    rw [ht']
    ring

/-- `doubleWidthOrder` is unchanged by translating the coset by a power of `T`. -/
private lemma doubleWidthOrder_TSL_zpow_smul (f : F)
    (q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) (j : ℤ) :
    doubleWidthOrder f (TSL ^ j • q) = doubleWidthOrder f q := by
  have hπ : Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne (TSL ^ j • q) =
      TSL ^ j • Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q := by
    induction q using QuotientGroup.induction_on with
    | H x => rw [MulAction.Quotient.smul_mk, Subgroup.quotientMapOfLE_apply_mk,
        Subgroup.quotientMapOfLE_apply_mk, MulAction.Quotient.smul_mk]
  have hm := natCast_minimalPeriod_mul_doubleWidthOrder f (TSL ^ j • q)
  rw [hπ, minimalPeriod_TSL_zpow_smul, minimalPeriod_TSL_zpow_smul,
    qExpansionOrderAtCusp_quotientFunc_TSL_zpow_smul,
    ← natCast_minimalPeriod_mul_doubleWidthOrder f q] at hm
  exact mul_left_cancel₀ (mod_cast (Nat.pos_of_neZero _).ne') hm

/-- `doubleWidthOrder` is unchanged by replacing the representative `x` by `-x`: the coset factor
changes by `(-1) ^ k`. -/
private lemma doubleWidthOrder_neg_one_mul (f : F) (x : 𝒮ℒ) :
    doubleWidthOrder f
        (QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (-1) * x) :
          𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =
      doubleWidthOrder f
        (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  have hn : (((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (-1) : 𝒮ℒ) : GL (Fin 2) ℝ) = -1 :=
    Matrix.SpecialLinearGroup.mapGL_neg_one
  have hπ : (QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (-1) * x) :
      𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, coe_adjoinNegOne]
    have : ((((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (-1) * x)⁻¹ * x : 𝒮ℒ) :
        GL (Fin 2) ℝ) = -1 := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hn, mul_inv_rev, inv_neg_one, mul_neg,
        mul_one, neg_mul, inv_mul_cancel]
    rw [this]
    exact Subgroup.neg_one_mem_adjoinNegOne _
  have hper : Periodic (quotientFunc f (QuotientGroup.mk x :
      𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) ∘ ofComplex)
      ((2 * (minimalPeriod (TSL • ·) (QuotientGroup.mk x :
        𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) : ℝ) : ℝ) : ℂ) := by
    obtain ⟨t, ht⟩ := minimalPeriod_dvd_two_mul_minimalPeriod_adjoinNegOne (Γ := Γ) x
    have ht' : 2 * (minimalPeriod (TSL • ·) (QuotientGroup.mk x :
        𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) : ℝ) =
        t * minimalPeriod (TSL • ·)
          (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
      exact_mod_cast ht.trans (mul_comm _ _)
    convert (periodic_quotientFunc f _).nat_mul t using 1
    rw [ht']
    push_cast
    ring
  have hpos : (0 : ℝ) < 2 * (minimalPeriod (TSL • ·) (QuotientGroup.mk x :
      𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) : ℝ) := by
    have : 0 < minimalPeriod (TSL • ·) (QuotientGroup.mk x :
        𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := Nat.pos_of_neZero _
    positivity
  have hana := analyticAt_cuspFunction_zero hpos hper
    (SlashInvariantForm.mdifferentiable_quotientFunc f _)
    (SlashInvariantForm.isBoundedAtImInfty_quotientFunc f _)
  rw [doubleWidthOrder, doubleWidthOrder, Subgroup.quotientMapOfLE_apply_mk,
    Subgroup.quotientMapOfLE_apply_mk, hπ]
  rw [_root_.SlashInvariantForm.quotientFunc_mk] at hana ⊢
  rw [_root_.SlashInvariantForm.quotientFunc_mk, Subgroup.coe_mul, hn, neg_one_mul, inv_neg,
    ModularForm.slash_neg, qExpansionOrderAtCusp_neg_one_zpow_mul hana]

/-- `doubleWidthOrder` depends only on the cusp below the coset. -/
private lemma doubleWidthOrder_eq_of_mk_eq (f : F)
    {q₁ q₂ : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ}
    (h : (⟦Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q₁⟧ :
        CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) =
      ⟦Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q₂⟧) :
    doubleWidthOrder f q₁ = doubleWidthOrder f q₂ := by
  induction q₁ using QuotientGroup.induction_on with
  | H x₁ =>
  induction q₂ using QuotientGroup.induction_on with
  | H x₂ =>
  obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.exact h
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [Subgroup.quotientMapOfLE_apply_mk, Subgroup.quotientMapOfLE_apply_mk] at hgx
  dsimp only at hgx
  rw [Subgroup.mk_smul, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf, coe_adjoinNegOne, Subgroup.mem_adjoinNegOne_iff] at hgx
  rcases hgx with hgx | hgx
  · -- `x₁` lies in the coset of `Γ` of `T ^ j x₂`
    have hq : (QuotientGroup.mk x₁ : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =
        TSL ^ j • QuotientGroup.mk x₂ := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      exact hgx
    rw [hq, doubleWidthOrder_TSL_zpow_smul]
  · -- `x₁` lies in the coset of `Γ` of `T ^ j (-x₂)`
    have hq : (QuotientGroup.mk x₁ : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) =
        TSL ^ j •
          QuotientGroup.mk ((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (-1) * x₂) := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hn : (((Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict (-1) : 𝒮ℒ) :
          GL (Fin 2) ℝ) = -1 := Matrix.SpecialLinearGroup.mapGL_neg_one
      convert hgx using 1
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hn, mul_inv_rev, inv_neg_one, neg_mul,
        mul_neg, mul_one]
    rw [hq, doubleWidthOrder_TSL_zpow_smul, doubleWidthOrder_neg_one_mul]

/-- `doubleWidthOrder` is twice the geometric order at the cusp below the coset. -/
private lemma doubleWidthOrder_eq_two_mul_geometricOrderAtCusp (f : F)
    (q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    (doubleWidthOrder f q : ℚ) =
      2 * geometricOrderAtCusp f ⟦Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q⟧ := by
  set c : CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)) :=
    ⟦Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q⟧
  have hout : Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne
      (QuotientGroup.mk c.out.out : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) = c.out := by
    rw [Subgroup.quotientMapOfLE_apply_mk, QuotientGroup.out_eq']
  have hq : doubleWidthOrder f q = doubleWidthOrder f (QuotientGroup.mk c.out.out) :=
    doubleWidthOrder_eq_of_mk_eq f (by rw [hout, Quotient.out_eq])
  have hw : minimalPeriod (TSL • ·) c.out = cuspTranslationOrbitWidth c := by
    rw [← cuspTranslationOrbitWidth_mk, Quotient.out_eq]
  rw [hq, doubleWidthOrder, hout, hw, geometricOrderAtCusp, orderAtCusp_def]
  ring

/-- **The geometric order may be read at any representative**: at the cusp of the coset of `x`,
it is `orderAtCusp h (f ∣[k] x⁻¹)` for `h` the period of that coset of `±Γ`. -/
@[simp]
theorem geometricOrderAtCusp_mk (f : F) (x : 𝒮ℒ) :
    geometricOrderAtCusp f
        (⟦(QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)⟧ :
          CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) =
      orderAtCusp (minimalPeriod (TSL • ·)
          (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))
        ((⇑f : ℍ → ℂ) ∣[k] (x : GL (Fin 2) ℝ)⁻¹) := by
  have h := doubleWidthOrder_eq_two_mul_geometricOrderAtCusp f
    (QuotientGroup.mk x : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)
  rw [doubleWidthOrder, Subgroup.quotientMapOfLE_apply_mk,
    _root_.SlashInvariantForm.quotientFunc_mk] at h
  rw [orderAtCusp_def, h]
  ring

/-- Per unit of width, the order at a cusp translation orbit of `Γ` is the geometric order at the
cusp below it. -/
private lemma orderAtCuspTranslationOrbit_div_eq (f : F)
    (q : 𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    (orderAtCuspTranslationOrbit f (⟦q⟧ : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) :
        ℚ) / cuspTranslationOrbitWidth (⟦q⟧ : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ))) =
      geometricOrderAtCusp f ⟦Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q⟧ /
        cuspTranslationOrbitWidth (⟦Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q⟧ :
          CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ))) := by
  have hm : (0 : ℚ) < minimalPeriod (TSL • ·) q := mod_cast Nat.pos_of_neZero _
  have hh : (0 : ℚ) < minimalPeriod (TSL • ·)
      (Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q) := mod_cast Nat.pos_of_neZero _
  have hscale : ((minimalPeriod (TSL • ·) q : ℤ) * doubleWidthOrder f q : ℚ) =
      ((2 * minimalPeriod (TSL • ·) (Subgroup.quotientMapOfLE subgroupOf_le_adjoinNegOne q) *
        qExpansionOrderAtCusp (minimalPeriod (TSL • ·) q : ℝ) (quotientFunc f q) : ℤ) : ℚ) :=
    mod_cast natCast_minimalPeriod_mul_doubleWidthOrder f q
  push_cast at hscale
  rw [doubleWidthOrder_eq_two_mul_geometricOrderAtCusp] at hscale
  rw [orderAtCuspTranslationOrbit_mk, cuspTranslationOrbitWidth_mk, cuspTranslationOrbitWidth_mk,
    div_eq_div_iff hm.ne' hh.ne']
  linear_combination -hscale / 2

/-- **The native cusp terms are `[±Γ : Γ]` times the geometric ones**: the orders of `f` at the
cusp translation orbits of `Γ`, which the general-level valence formula sums, add up to
`[±Γ : Γ]` times the sum of the geometric orders at the cusps of `Γ`. -/
theorem sum_orderAtCuspTranslationOrbit_eq_relIndex_mul_sum_geometricOrderAtCusp (f : F) :
    ∑ c : CuspTranslationOrbit (Γ : Subgroup (GL (Fin 2) ℝ)),
        (orderAtCuspTranslationOrbit f c : ℚ) =
      Γ.relIndex Γ.adjoinNegOne *
        ∑ c : CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)),
          geometricOrderAtCusp f c := by
  classical
  let _ : Fintype (𝒮ℒ ⧸ (Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  let _ : Fintype (𝒮ℒ ⧸ (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
    Fintype.ofFinite _
  have hrel : ((Γ : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ).relIndex
      ((Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) = Γ.relIndex Γ.adjoinNegOne := by
    rw [Subgroup.relIndex_subgroupOf (Subgroup.map_le_range _ _),
      Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective]
  rw [← sum_div_cuspTranslationOrbitWidth, ← sum_div_cuspTranslationOrbitWidth]
  simp_rw [orderAtCuspTranslationOrbit_div_eq f]
  rw [Subgroup.sum_comp_quotientMapOfLE subgroupOf_le_adjoinNegOne
    (fun q ↦ geometricOrderAtCusp f ⟦q⟧ / cuspTranslationOrbitWidth
      (⟦q⟧ : CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)))), hrel, nsmul_eq_mul]

/-- **The projective valence formula** (Diamond–Shurman, §§3.2–3.3): for a nonzero weight-`k`
form `f` on a finite-index `Γ ≤ SL(2, ℤ)`, the orders of `f` on the effective quotient, divided
by the effective elliptic orders `e_P`, together with the geometric orders at the cusps of `Γ`,
add up to `k · [SL(2, ℤ) : ±Γ] / 12`. -/
theorem valence_formula_projective (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    (∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
          (orderOfVanishingOnSubgroupOrbit f o : ℚ) / ellipticOrderOnSubgroupOrbit o) +
        ∑ c : CuspTranslationOrbit (Γ.adjoinNegOne : Subgroup (GL (Fin 2) ℝ)),
          geometricOrderAtCusp f c =
      (k : ℚ) * Γ.projectiveIndex / 12 := by
  have hδ : (Γ.relIndex Γ.adjoinNegOne : ℚ) ≠ 0 := mod_cast Γ.relIndex_adjoinNegOne_ne_zero
  have hint : ∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
      weightedOrderOfVanishingOnSubgroupOrbit f o =
        Γ.relIndex Γ.adjoinNegOne * ∑ᶠ o : orbitRel.Quotient (Γ : Subgroup (GL (Fin 2) ℝ)) ℍ,
          (orderOfVanishingOnSubgroupOrbit f o : ℚ) / ellipticOrderOnSubgroupOrbit o := by
    rw [mul_finsum]
    exact finsum_congr fun o ↦ by
      rw [weightedOrderOfVanishingOnSubgroupOrbit_eq_relIndex_mul_div, mul_div_assoc]
  have hnative := valence_formula_finiteIndex f hf
  rw [hint, sum_orderAtCuspTranslationOrbit_eq_relIndex_mul_sum_geometricOrderAtCusp,
    Subgroup.card_quotient_mapGL_eq_index, ← Subgroup.relIndex_mul_index Γ.le_adjoinNegOne,
    ← Subgroup.projectiveIndex_def] at hnative
  refine mul_left_cancel₀ hδ ?_
  push_cast at hnative
  linear_combination hnative

end Order

end ModularForm

end TauCeti
