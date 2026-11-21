/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.RingTheory.DiscreteValuationRing.UnitFiltration
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.GroupTheory.PGroup
import TauCeti.RingTheory.LocalRing.Monogenic

/-!
# Graded embeddings of the ramification filtration of a discrete valuation ring

Let a group `G` act by ring automorphisms on a discrete valuation ring `B` with maximal ideal `𝔪`
and residue field `k`. Fixing a uniformizer `ϖ` of `B`, every automorphism `σ` carries `ϖ` to
another uniformizer `σ • ϖ`, so there is a unique unit `u_σ : Bˣ` with `ϖ * u_σ = σ • ϖ`. When `σ`
lies in the `i`-th lower ramification group `G_i = TauCeti.IsLocalRing.ramificationGroup G B i`,
`u_σ` lies in the `i`-th step `U_i = TauCeti.IsLocalRing.unitFiltration B i` of the unit
filtration, and its class modulo `U_{i+1}` is independent of `ϖ`, multiplicative in `σ`, and
trivial on `G_{i+1}`. It therefore descends to a canonical homomorphism

`θ_i : G_i / G_{i+1} →* U_i / U_{i+1}`.

At depth zero, composing with `U_0 / U_1 ≃* kˣ` gives the **tame character** `G_0 →* kˣ` and its
graded form `G_0 / G_1 →* kˣ`, independent of `ϖ`. At positive depth `i = n + 1`, composing with
the uniformizer coordinate `Additive (U_{n+1} / U_{n+2}) ≃+ k` gives an additive homomorphism
sending `σ` with `σ • ϖ - ϖ = y * ϖ ^ (n + 2)` to `residue B y`; if `ϖ' = ϖ * a` for a unit
`a`, the coordinate relative to `ϖ` equals `(residue B a) ^ (n + 1)` times the coordinate relative
to `ϖ'` (equivalently, replacing `ϖ` by `ϖ'` divides the coordinate by
`(residue B a) ^ (n + 1)`).

None of the constructions above requires a base ring or separability. Suppose now that `B` is a
local algebra over a local ring `A` whose elements `G` fixes (`[SMulCommClass G A B]`), and that
the residue field extension `ResidueField B / ResidueField A` is separable — with no perfectness or
finiteness hypothesis on the residue fields and no DVR assumption on `A`. Then membership of an
element `σ ∈ G_0` in `G_n` is decided at a uniformizer alone (`σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`), so every
`θ_i` is **injective**:

* when `G_0 / G_1` is finite, it is cyclic, and in prime residue characteristic `p` its order is
  not divisible by `p`; when `k` is finite, `#(G_0 / G_1)` divides `#k - 1`;
* in prime residue characteristic `p`, every positive graded piece `G_{n+1} / G_{n+2}` has exponent
  dividing `p` and is a `p`-group; when the action is faithful and `G_0` is finite, every `G_i`
  with `i > 0` is a `p`-group, and `G_1` is the unique normal Sylow `p`-subgroup of `G_0`;
* in residue characteristic zero, every positive graded piece `G_{n+1} / G_{n+2}` is torsion-free,
  and when the action is faithful and `G_0` is finite, `G_i = ⊥` for all `i > 0` (in particular
  `G_1 = ⊥`).

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u_σ ∈ U_i` with
  `ϖ * u_σ = σ • ϖ`, for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToUnitFiltrationGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded`: the quotient
  homomorphisms `G_i →* U_i / U_{i+1}` and `θ_i : G_i / G_{i+1} →* U_i / U_{i+1}`.
* `TauCeti.IsDiscreteValuationRing.tameCharacter` and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded`: the depth-zero character `G_0 →* kˣ` and
  its graded form `G_0 / G_1 →* kˣ`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField`: the positive-depth
  additive homomorphism `Additive (G_{n+1} / G_{n+2}) →+ k` attached to a uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`: in prime residue characteristic `p`,
  the wild inertia group `G_1` as the unique normal Sylow `p`-subgroup of `G_0`.

## Main results

* `TauCeti.IsDiscreteValuationRing.ramificationGroupToUnitFiltrationGraded_eq_of_irreducible`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_eq_of_irreducible`, and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_eq_of_irreducible`: independence of the
  choice of uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_of_smul_sub_eq` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_change`: evaluation on a
  displacement and uniformizer-change scaling at positive depth.
* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`: for a separable
  residue extension, membership of `σ ∈ G_0` in `G_n` is decided at a uniformizer.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToUnitFiltrationGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToUnitFiltrationGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective`: exactness of
  the kernels and injectivity of the graded maps under separable residue extension.
* `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero`,
  `TauCeti.IsDiscreteValuationRing.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one`,
  and `TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one`: cyclicity of
  `G_0 / G_1`, divisibility of `#k - 1` by `#(G_0 / G_1)`, and coprimality of `[G_0 : G_1]` to the
  residue characteristic.
* `TauCeti.IsDiscreteValuationRing.isPGroup_ramificationGroupGraded_natCast_succ`,
  `TauCeti.IsDiscreteValuationRing.isPGroup_ramificationGroup`,
  `TauCeti.IsDiscreteValuationRing.eq_ramificationGroupOneSylow`,
  `TauCeti.IsDiscreteValuationRing.natCard_ramificationGroup_one`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroup_one_eq_bot_iff_not_dvd_card`:
  `p`-group structure of positive ramification groups and Sylow characterization of `G_1`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroup_eq_bot_of_charZero` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroup_one_eq_bot_of_charZero`: vanishing of positive
  ramification groups in residue characteristic zero.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–7 and Corollaries.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Proposition 1 and Corollaries 1–2.
-/

public section

open IsLocalRing Polynomial TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

/-! ### Uniformizer ratios and graded homomorphisms -/

section Homomorphisms

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

private theorem uniformizerChangeUnit_smul_mem_unitFiltration {ϖ : B} (hϖ : Irreducible ϖ)
    {i : ℕ} {σ : G} (hσϖ : Irreducible (σ • ϖ))
    (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ (σ • ϖ) hϖ hσϖ ∈ unitFiltration B i := by
  rw [mem_unitFiltration_iff_mul_irreducible_mem hϖ, sub_mul, one_mul, mul_comm,
    mul_uniformizerChangeUnit]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

/-- The unit `u_σ ∈ U_i` carrying a uniformizer `ϖ` to `(σ : G) • ϖ`, for `σ` in the `i`-th
ramification group `G_i`. -/
noncomputable def uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) : unitFiltration B i :=
  have hσϖ : Irreducible ((σ : G) • ϖ) :=
    hϖ.map (MulSemiringAction.toRingEquiv G B (σ : G)).toMulEquiv
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ,
    uniformizerChangeUnit_smul_mem_unitFiltration hϖ hσϖ σ.property⟩

/-- Multiplying `ϖ` on the right by `uniformizerRatio i hϖ σ` gives `(σ : G) • ϖ`. -/
@[simp]
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ :=
  mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

/-- The 1-cocycle identity `u_{στ} = u_σ * σ(u_τ)` in `Bˣ` for the uniformizer ratio. -/
theorem coe_uniformizerRatio_mul_apply (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ (σ * τ) : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  calc
    ϖ * ((uniformizerRatio i hϖ (σ * τ) : Bˣ) : B)
        = (σ : G) • ((τ : G) • ϖ) := by
          rw [mul_coe_uniformizerRatio, Subgroup.coe_mul, mul_smul]
    _ = (σ : G) • (ϖ * ((uniformizerRatio i hϖ τ : Bˣ) : B)) := by
          rw [mul_coe_uniformizerRatio]
    _ = (ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B)) *
          (σ : G) • ((uniformizerRatio i hϖ τ : Bˣ) : B) := by
          rw [smul_mul', mul_coe_uniformizerRatio]
    _ = ϖ * (((uniformizerRatio i hϖ σ : Bˣ) *
          Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
            (uniformizerRatio i hϖ τ : Bˣ) : Bˣ) : B) := by
          rw [Units.val_mul, Units.coe_map, mul_assoc]
          rfl

/-- The **quotient homomorphism** `G_i →* U_i / U_{i+1}` sending `σ` to the class of its
uniformizer ratio `u_σ`. It does not depend on `ϖ`
(`ramificationGroupToUnitFiltrationGraded_eq_of_irreducible`) and kills `G_{i+1}`. -/
noncomputable def ramificationGroupToUnitFiltrationGraded (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B (i : ℤ) →* UnitFiltrationGraded B i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio i hϖ σ)) <| by
    intro σ τ
    rw [← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf, ← Subgroup.inv_mem_iff]
    have hcocycle :
        ((↑((uniformizerRatio i hϖ (σ * τ))⁻¹ *
            (uniformizerRatio i hϖ σ * uniformizerRatio i hϖ τ)))⁻¹ : Bˣ) =
          Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
            (uniformizerRatio i hϖ τ : Bˣ) / (uniformizerRatio i hϖ τ : Bˣ) := by
      push_cast
      rw [mul_inv_rev, inv_inv, mul_inv_rev, coe_uniformizerRatio_mul_apply,
        mul_assoc, inv_mul_cancel_left, mul_comm, ← div_eq_mul_inv]
    rw [hcocycle]
    exact unitsMap_div_mem_unitFiltration_succ σ.property _

/-- Evaluates `ramificationGroupToUnitFiltrationGraded i hϖ` at `σ` as the quotient class of
`uniformizerRatio i hϖ σ`. -/
@[simp]
theorem ramificationGroupToUnitFiltrationGraded_apply (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToUnitFiltrationGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

private theorem coe_uniformizerRatio_change (i : ℕ) {ϖ ϖ' : B} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (σ : ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ ϖ' hϖ hϖ' * (uniformizerRatio i hϖ' σ : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerChangeUnit ϖ ϖ' hϖ hϖ') := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  calc
    ϖ * ((uniformizerChangeUnit ϖ ϖ' hϖ hϖ' * (uniformizerRatio i hϖ' σ : Bˣ) : Bˣ) : B)
        = (σ : G) • ϖ' := by
          rw [Units.val_mul, ← mul_assoc, mul_uniformizerChangeUnit, mul_coe_uniformizerRatio]
    _ = (σ : G) • (ϖ * (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : B)) := by
          rw [mul_uniformizerChangeUnit]
    _ = (ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B)) *
          (σ : G) • (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : B) := by
          rw [smul_mul', mul_coe_uniformizerRatio]
    _ = ϖ * (((uniformizerRatio i hϖ σ : Bˣ) *
          Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
            (uniformizerChangeUnit ϖ ϖ' hϖ hϖ') : Bˣ) : B) := by
          rw [Units.val_mul, Units.coe_map, mul_assoc]
          rfl

/-- The quotient homomorphism `G_i →* U_i / U_{i+1}` does not depend on the choice of
uniformizer. -/
theorem ramificationGroupToUnitFiltrationGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupToUnitFiltrationGraded (G := G) i hϖ' := by
  refine MonoidHom.ext fun σ ↦ ?_
  rw [ramificationGroupToUnitFiltrationGraded_apply, ramificationGroupToUnitFiltrationGraded_apply]
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf]
  set a := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have hrel :
      ((uniformizerRatio i hϖ σ)⁻¹ * uniformizerRatio i hϖ' σ : unitFiltration B i).val =
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a / a := by
    apply mul_left_cancel (a := a)
    rw [Subgroup.coe_mul, InvMemClass.coe_inv, mul_left_comm,
      coe_uniformizerRatio_change i hϖ hϖ' σ, inv_mul_cancel_left, div_eq_mul_inv,
      mul_comm _ a⁻¹, mul_inv_cancel_left]
  rw [hrel]
  exact unitsMap_div_mem_unitFiltration_succ σ.property a

/-- An element `σ ∈ G_i` lies in the kernel of `ramificationGroupToUnitFiltrationGraded i hϖ`
if and only if `(σ : G) • ϖ - ϖ ∈ 𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToUnitFiltrationGraded_iff {i : ℕ} {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G B (i : ℤ)} :
    σ ∈ (ramificationGroupToUnitFiltrationGraded i hϖ).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToUnitFiltrationGraded_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, mem_unitFiltration_iff_mul_irreducible_mem hϖ, sub_mul, one_mul,
    mul_comm, mul_coe_uniformizerRatio]

/-- The next ramification group `G_{i+1}` lies in the kernel of the `i`-th quotient
homomorphism. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToUnitFiltrationGraded i hϖ).ker := by
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

/-- The **graded ramification homomorphism** `θ_i : G_i / G_{i+1} →* U_i / U_{i+1}`, induced by
sending `σ ∈ G_i` to the class of its uniformizer ratio `u_σ`. -/
noncomputable def ramificationGroupGradedToUnitFiltrationGraded (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B (i : ℤ) →* UnitFiltrationGraded B i :=
  QuotientGroup.lift _ (ramificationGroupToUnitFiltrationGraded i hϖ)
    (ramificationGroup_succ_subgroupOf_le_ker i hϖ)

/-- Evaluates `ramificationGroupGradedToUnitFiltrationGraded` on the class of `σ`. -/
@[simp]
theorem ramificationGroupGradedToUnitFiltrationGraded_mk (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToUnitFiltrationGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

/-- The graded ramification homomorphism `θ_i` does not depend on the choice of uniformizer. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ =
      ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ' := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    exact DFunLike.congr_fun
      (ramificationGroupToUnitFiltrationGraded_eq_of_irreducible i hϖ hϖ') σ

/-! ### The tame character and positive-depth residue coordinates -/

/-- The **tame character** `G_0 →* (ResidueField B)ˣ`, obtained by composing the depth-zero
quotient homomorphism with `U_0 / U_1 ≃* (ResidueField B)ˣ`. It sends `σ` to the residue of `u_σ`
where `ϖ * u_σ = σ • ϖ`, and does not depend on `ϖ`. -/
noncomputable def tameCharacter {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B 0 →* (ResidueField B)ˣ :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupToUnitFiltrationGraded 0 hϖ)

/-- The underlying residue-field value of `tameCharacter hϖ σ` is the residue of `u_σ`. -/
theorem coe_tameCharacter_apply {ϖ : B} (hϖ : Irreducible ϖ) (σ : ramificationGroup G B 0) :
    (tameCharacter hϖ σ : ResidueField B) = residue B ((uniformizerRatio 0 hϖ σ : Bˣ) : B) := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToUnitFiltrationGraded_apply (i := 0),
    coe_unitFiltrationGradedZeroEquivResidueFieldUnits_mk]

/-- If `y * ϖ = (σ : G) • ϖ`, then `tameCharacter hϖ σ` evaluates to `residue B y`. -/
theorem coe_tameCharacter_of_mul_eq {ϖ : B} (hϖ : Irreducible ϖ) (σ : ramificationGroup G B 0)
    {y : B} (hy : y * ϖ = (σ : G) • ϖ) :
    (tameCharacter hϖ σ : ResidueField B) = residue B y := by
  have hy' : ((uniformizerRatio 0 hϖ σ : Bˣ) : B) = y :=
    mul_right_cancel₀ hϖ.ne_zero
      (((mul_comm _ _).trans (mul_coe_uniformizerRatio 0 hϖ σ)).trans hy.symm)
  rw [coe_tameCharacter_apply, hy']

/-- The tame character does not depend on the choice of uniformizer. -/
theorem tameCharacter_eq_of_irreducible {ϖ ϖ' : B} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    tameCharacter (G := G) hϖ = tameCharacter (G := G) hϖ' := by
  rw [tameCharacter, tameCharacter,
    ramificationGroupToUnitFiltrationGraded_eq_of_irreducible (G := G) 0 hϖ hϖ']

/-- An element `σ ∈ G_0` has trivial tame character if and only if `(σ : G) • ϖ - ϖ ∈ 𝔪 ^ 2`. -/
theorem tameCharacter_eq_one_iff {ϖ : B} (hϖ : Irreducible ϖ) (σ : ramificationGroup G B 0) :
    tameCharacter hϖ σ = 1 ↔ (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ 2 := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
    ← MonoidHom.mem_ker, mem_ker_ramificationGroupToUnitFiltrationGraded_iff (i := 0) hϖ]

/-- The **graded tame character** `G_0 / G_1 →* (ResidueField B)ˣ`. -/
noncomputable def tameCharacterGraded {ϖ : B} (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B 0 →* (ResidueField B)ˣ :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupGradedToUnitFiltrationGraded 0 hϖ)

/-- Evaluates `tameCharacterGraded` on the class of `σ` as `tameCharacter hϖ σ`. -/
@[simp]
theorem tameCharacterGraded_mk {ϖ : B} (hϖ : Irreducible ϖ) (σ : ramificationGroup G B 0) :
    tameCharacterGraded hϖ (QuotientGroup.mk σ) = tameCharacter hϖ σ :=
  (rfl)

/-- The graded tame character does not depend on the choice of uniformizer. -/
theorem tameCharacterGraded_eq_of_irreducible {ϖ ϖ' : B} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacterGraded (G := G) hϖ = tameCharacterGraded (G := G) hϖ' := by
  rw [tameCharacterGraded, tameCharacterGraded,
    ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible (G := G) 0 hϖ hϖ']

variable (G B) in
/-- At positive depth `n + 1`, fixing a uniformizer `π` gives an additive homomorphism from
`Additive (G_{n+1} / G_{n+2})` to `ResidueField B`, sending `σ` with
`σ • π - π = y * π ^ (n + 2)` to `residue B y`. -/
noncomputable def ramificationGroupGradedToResidueField (n : ℕ) (π : B) (hπ : Irreducible π) :
    Additive (RamificationGroupGraded G B ((n : ℤ) + 1)) →+ ResidueField B :=
  (unitFiltrationGradedSuccEquivResidueField n π hπ).toAddMonoidHom.comp
    (ramificationGroupGradedToUnitFiltrationGraded (n + 1) hπ).toAdditive

/-- Evaluates `ramificationGroupGradedToResidueField` on the class of `τ` via the uniformizer
coordinate of `uniformizerRatio (n + 1) hπ τ`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (π : B) (hπ : Irreducible π)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n π hπ (Additive.ofMul (QuotientGroup.mk τ)) =
      unitFiltrationGradedSuccEquivResidueField n π hπ
        (Additive.ofMul (QuotientGroup.mk (uniformizerRatio (n + 1) hπ τ))) :=
  (rfl)

/-- If `(τ : G) • π - π = y * π ^ (n + 2)`, then the positive-depth residue coordinate of `τ`
relative to `π` is `residue B y`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) (π : B) (hπ : Irreducible π)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) (y : B)
    (hmove : (τ : G) • π - π = y * π ^ (n + 2)) :
    ramificationGroupGradedToResidueField G B n π hπ (Additive.ofMul (QuotientGroup.mk τ)) =
      residue B y := by
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  refine unitFiltrationGradedSuccEquivResidueField_eq_residue n π hπ _ y ?_
  apply mul_right_cancel₀ hπ.ne_zero
  rw [sub_mul, one_mul, mul_comm _ π, mul_coe_uniformizerRatio, hmove, mul_assoc, ← pow_succ]

/-- If `π' = π * a`, the positive-depth ramification coordinate relative to `π` equals
`(residue B a) ^ (n + 1)` times the coordinate relative to `π'` (equivalently, replacing `π` by
`π'` divides the coordinate by `(residue B a) ^ (n + 1)`). -/
theorem ramificationGroupGradedToResidueField_change (n : ℕ) (π π' : B) (hπ : Irreducible π)
    (hπ' : Irreducible π') (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n π hπ (Additive.ofMul τ) =
      residue B (uniformizerChangeUnit π π' hπ hπ' : B) ^ (n + 1) *
        ramificationGroupGradedToResidueField G B n π' hπ' (Additive.ofMul τ) := by
  have hchange :=
    unitFiltrationGradedSuccEquivResidueField_change n π π' hπ hπ'
      (Additive.ofMul (ramificationGroupGradedToUnitFiltrationGraded (n + 1) hπ τ))
  have htheta :=
    DFunLike.congr_fun
      (ramificationGroupGradedToUnitFiltrationGraded_eq_of_irreducible (n + 1) hπ hπ') τ
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  simpa only [AddEquiv.coe_toAddMonoidHom, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    htheta] using hchange

end Homomorphisms

/-! ### Separable residue extensions: uniformizer criterion and injectivity -/

section Separable

variable {G : Type*} [Group G] (A : Type*) [CommRing A] [IsLocalRing A]
variable {B : Type*} [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [MulSemiringAction G B] [SMulCommClass G A B]

private theorem smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : G} (hσ : σ ∈ ramificationGroup G B 0) {k : ℕ}
    (ih : ∀ z : B, σ • z - z ∈ maximalIdeal B ^ (k + 1))
    (hϖk : σ • ϖ - ϖ ∈ maximalIdeal B ^ (k + 2)) (x : B) :
    σ • x - x ∈ maximalIdeal B ^ (k + 2) := by
  -- Lift the minimal polynomial of `residue B x` over `ResidueField A` to `f ∈ A[X]`.
  obtain ⟨f, hf⟩ :=
    Polynomial.map_surjective (residue A) residue_surjective
      (minpoly (ResidueField A) (residue B x))
  set P : B[X] := f.map (algebraMap A B)
  have hroot : aeval x f ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, map_aeval_eq_aeval_map residue_comp_algebraMap, hf]
    exact minpoly.aeval _ _
  have hder : residue B ((derivative P).eval x) ≠ 0 := by
    rw [derivative_map, eval_map_algebraMap, map_aeval_eq_aeval_map residue_comp_algebraMap,
      ← derivative_map, hf]
    exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  -- Write `aeval x f = ϖ * y`; applying `σ - id` puts `P(σ • x) - P(x)` in `𝔪 ^ (k + 2)`.
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hroot
  obtain ⟨y, hy⟩ := hroot
  have hσϖ : σ • ϖ ∈ maximalIdeal B := by
    rw [← pow_one (maximalIdeal B), smul_mem_maximalIdeal_pow_iff, pow_one, mem_maximalIdeal]
    exact hϖ.not_isUnit
  have hdiff : P.eval (σ • x) - P.eval x ∈ maximalIdeal B ^ (k + 2) := by
    have hsplit : σ • (ϖ * y) - ϖ * y = σ • ϖ * (σ • y - y) + (σ • ϖ - ϖ) * y := by
      rw [smul_mul']; ring
    rw [eval_map_algebraMap, eval_map_algebraMap, f.aeval_smul, hy, hsplit]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hϖk)
    rw [pow_succ']
    exact Ideal.mul_mem_mul hσϖ (ih y)
  -- Taylor-expand `P(σ • x) - P(x) = (σ • x - x) * u` with `u` a unit of `B`, then cancel `u`.
  set d : B := σ • x - x
  obtain ⟨c, hc⟩ := binomExpansion P x d
  rw [add_sub_cancel] at hc
  have hd0 : residue B d = 0 := by
    rw [residue_eq_zero_iff]
    exact mem_ramificationGroup_zero_iff.mp hσ x
  have hu : IsUnit ((derivative P).eval x + c * d) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, map_add, map_mul, hd0, mul_zero, add_zero]
    exact hder
  have hfac : P.eval (σ • x) - P.eval x = (hu.unit : B) * d := by
    rw [IsUnit.unit_spec, hc]; ring
  exact (Ideal.unit_mul_mem_iff_mem _ hu.unit.isUnit).mp (hfac ▸ hdiff)

include A in
/-- **Membership in the lower ramification filtration is decided at a uniformizer** when the
residue field extension `ResidueField B / ResidueField A` is separable: an element `σ ∈ G_0` lies
in `G_n` if and only if `σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : G} (hσ : σ ∈ ramificationGroup G B 0) {n : ℕ} :
    σ ∈ ramificationGroup G B (n : ℤ) ↔ σ • ϖ - ϖ ∈ maximalIdeal B ^ (n + 1) := by
  rw [mem_ramificationGroup_natCast_iff]
  refine ⟨fun h ↦ h ϖ, fun h ↦ ?_⟩
  suffices ∀ m ≤ n, ∀ x : B, σ • x - x ∈ maximalIdeal B ^ (m + 1) from this n le_rfl
  intro m
  induction m with
  | zero =>
    intro _ x
    rw [zero_add, pow_one]
    exact mem_ramificationGroup_zero_iff.mp hσ x
  | succ k ih =>
    intro hk x
    exact smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer A hϖ hσ (ih (by omega))
      (Ideal.pow_le_pow_right (by omega) h) x

include A in
/-- For a separable residue extension, **the kernel of the `i`-th quotient homomorphism is
`G_{i+1}`**. -/
theorem ker_ramificationGroupToUnitFiltrationGraded
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    (ramificationGroupToUnitFiltrationGraded (G := G) i hϖ).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker i hϖ)
  rw [mem_ker_ramificationGroupToUnitFiltrationGraded_iff hϖ] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G B 0 :=
    ramificationGroup_antitone G B (Int.natCast_nonneg i) σ.property
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ hσ₀]
  exact hσ

include A in
/-- **The graded ramification homomorphisms `θ_i : G_i / G_{i+1} →* U_i / U_{i+1}` are injective**
when the residue extension is separable. -/
theorem ramificationGroupGradedToUnitFiltrationGraded_injective
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToUnitFiltrationGraded (G := G) i hϖ) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToUnitFiltrationGraded A i hϖ).symm

include A in
/-- For a separable residue extension, **the kernel of the tame character is `G_1`**. -/
theorem ker_tameCharacter [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B}
    (hϖ : Irreducible ϖ) :
    (tameCharacter (G := G) hϖ).ker =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) := by
  rw [tameCharacter, MulEquiv.toMonoidHom_eq_coe, MonoidHom.ker_mulEquiv_comp]
  exact_mod_cast ker_ramificationGroupToUnitFiltrationGraded A 0 hϖ

include A in
/-- **The graded tame character `G_0 / G_1 →* (ResidueField B)ˣ` is injective** when the residue
extension is separable. -/
theorem tameCharacterGraded_injective [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {ϖ : B} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacterGraded (G := G) hϖ) :=
  (unitFiltrationGradedZeroEquivResidueFieldUnits B).injective.comp
    (ramificationGroupGradedToUnitFiltrationGraded_injective A 0 hϖ)

include A in
/-- **The positive-depth residue coordinate `Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` is
injective** when the residue extension is separable. -/
theorem ramificationGroupGradedToResidueField_injective
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] (n : ℕ) (π : B)
    (hπ : Irreducible π) :
    Function.Injective (ramificationGroupGradedToResidueField G B n π hπ) :=
  (unitFiltrationGradedSuccEquivResidueField n π hπ).injective.comp
    (ramificationGroupGradedToUnitFiltrationGraded_injective A (n + 1) hπ)

include A in
/-- In prime residue characteristic `p`, an element `σ ∈ G_0` lies in `G_1` as soon as a `p`-power
of its uniformizer ratio is congruent to `1` modulo `𝔪`. -/
theorem mem_ramificationGroup_one_of_pow_sub_one_mem_maximalIdeal
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : G} (hσ : σ ∈ ramificationGroup G B 0) (p k : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p]
    (h : ((uniformizerRatio 0 hϖ ⟨σ, hσ⟩ : Bˣ) : B) ^ p ^ k - 1 ∈ maximalIdeal B) :
    σ ∈ ramificationGroup G B 1 := by
  have hp : p.Prime := Fact.out
  set u : Bˣ := (uniformizerRatio 0 hϖ ⟨σ, hσ⟩ : Bˣ)
  have hu1 : u ∈ unitFiltration B 1 := by
    rw [mem_unitFiltration_one_iff_residue_eq_one, ← sub_eq_zero,
      ← pow_eq_zero_iff (pow_ne_zero k hp.ne_zero), sub_pow_char_pow, one_pow,
      ← map_pow, ← map_one (residue B), ← map_sub, residue_eq_zero_iff]
    exact h
  have h2 : σ • ϖ - ϖ ∈ maximalIdeal B ^ 2 := by
    rw [mem_unitFiltration_iff_mul_irreducible_mem hϖ, sub_mul, one_mul,
      mul_comm _ ϖ, mul_coe_uniformizerRatio 0 hϖ ⟨σ, hσ⟩] at hu1
    exact hu1
  exact (mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ hσ (n := 1)).mpr h2

end Separable

/-! ### Consequences for tame inertia `G_0 / G_1` and wild inertia `G_1` -/

section Consequences

variable (G : Type*) [Group G] (A : Type*) [CommRing A] [IsLocalRing A]
variable (B : Type*) [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [MulSemiringAction G B] [SMulCommClass G A B]
variable [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

include A

/-- **The tame quotient `G_0 / G_1` is cyclic** whenever it is finite and the residue extension is
separable. -/
theorem isCyclic_ramificationGroupGraded_zero [Finite (RamificationGroupGraded G B 0)] :
    IsCyclic (RamificationGroupGraded G B 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacterGraded hϖ))
    (Units.val_injective.comp (tameCharacterGraded_injective A hϖ))

/-- When the residue extension is separable, the order of the tame quotient `G_0 / G_1` divides
`#(ResidueField B) - 1`. -/
theorem card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one :
    Nat.card (RamificationGroupGraded G B 0) ∣ Nat.card (ResidueField B) - 1 := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  rw [← Nat.card_units]
  exact Subgroup.card_dvd_of_injective _ (tameCharacterGraded_injective A hϖ)

/-- **The index `[G_0 : G_1]` is not divisible by the residue characteristic `p`** whenever
`G_0 / G_1` is finite and the residue extension is separable. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [Finite (RamificationGroupGraded G B 0)] :
    ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hφ := tameCharacterGraded_injective A (G := G) hϖ
  intro hp
  have hpCard : p ∣ Nat.card (RamificationGroupGraded G B 0) := by
    rwa [RamificationGroupGraded, zero_add, ← Subgroup.index_eq_card]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpCard
  -- The image of `x` is a primitive `p`-th root of unity in `ResidueField B`, impossible in char p.
  have hord : orderOf ((tameCharacterGraded hϖ x : (ResidueField B)ˣ) : ResidueField B) = p := by
    rw [orderOf_units, orderOf_injective _ hφ x, hx]
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hroot := hord ▸
    IsPrimitiveRoot.orderOf ((tameCharacterGraded hϖ x : (ResidueField B)ˣ) : ResidueField B)
  exact hroot.neZero'.out (CharP.cast_eq_zero _ p)

/-- When the residue field has characteristic `p` and the residue extension is separable, every
element of a positive graded piece `G_{n+1} / G_{n+2}` satisfies `x ^ p = 1`. -/
theorem ramificationGroupGraded_natCast_succ_pow_eq_one (p : ℕ) [CharP (ResidueField B) p]
    (n : ℕ) (x : RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)) :
    x ^ p = 1 := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  apply (ramificationGroupGradedToUnitFiltrationGraded_injective A (G := G) (n + 1) hϖ)
  rw [map_pow, map_one, unitFiltrationGraded_succ_pow_eq_one_of_charP B p n]

/-- **Every positive graded piece `G_{n+1} / G_{n+2}` is a `p`-group** for the residue
characteristic `p` when the residue extension is separable. No finiteness assumption on `G_0` or on
the residue field is needed. -/
theorem isPGroup_ramificationGroupGraded_natCast_succ (p : ℕ) [CharP (ResidueField B) p]
    (n : ℕ) :
    IsPGroup p (RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  exact (isPGroup_unitFiltrationGraded_succ B p n).of_injective _
    (ramificationGroupGradedToUnitFiltrationGraded_injective A (n + 1) hϖ)

/-- **Every positive-depth ramification group `G_i` (`i > 0`) is a `p`-group** for the residue
characteristic `p`, whenever the residue extension is separable, the action is faithful, and `G_0`
is finite; in particular the wild inertia group `G_1` is a `p`-group. -/
theorem isPGroup_ramificationGroup (p : ℕ) [CharP (ResidueField B) p] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] {i : ℤ} (hi : 0 < i) :
    IsPGroup p (ramificationGroup G B i) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G B
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = ((j + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
  suffices ∀ d j : ℕ, N ≤ j + 1 + d → IsPGroup p (ramificationGroup G B ((j + 1 : ℕ) : ℤ)) from
    this N.toNat j (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [hN _ (by omega)]
    exact IsPGroup.of_bot
  | succ d ih =>
    intro j hj
    have hsucc := ih (j + 1) (by omega)
    push_cast at hsucc
    refine IsPGroup.of_subgroup_of_quotient ?_
      (isPGroup_ramificationGroupGraded_natCast_succ G A B p j)
    push_cast
    exact hsucc.comap_subtype

/-- **Wild inertia is the Sylow `p`-subgroup of inertia**: in prime residue characteristic `p`,
under separable residue extension, faithful action, and finite inertia `G_0`, the first
ramification group `G_1` viewed inside `G_0` is a Sylow `p`-subgroup. -/
noncomputable def ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Sylow p (ramificationGroup G B 0) :=
  ((isPGroup_ramificationGroup G A B p (i := 1) (by omega)).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one G A B p)

/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` viewed inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow G A B p : Subgroup (ramificationGroup G B 0)) =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) :=
  (rfl)

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow G A B p : Subgroup (ramificationGroup G B 0)).Normal := by
  rw [ramificationGroupOneSylow_coe,
    Subgroup.normal_subgroupOf_iff_le_normalizer
      (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)),
    Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

/-- **Wild inertia is the unique Sylow `p`-subgroup of inertia.** -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (Q : Sylow p (ramificationGroup G B 0)) :
    Q = ramificationGroupOneSylow G A B p := by
  let _ : Unique (Sylow p (ramificationGroup G B 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow G A B p)
      (ramificationGroupOneSylow_normal G A B p)
  exact Subsingleton.elim _ _

/-- The order of `G_1` is the `p`-part of the order of `G_0`: `#G_1 = p ^ (v_p #G_0)`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Nat.card (ramificationGroup G B 1) =
      p ^ (Nat.card (ramificationGroup G B 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow G A B p)]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe
      (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`** (the tamely ramified
case). -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField B) p] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  have hp : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one G A B p,
    pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
  simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`** when `ResidueField B` is
finite (the tamely ramified case), without assuming `G_0` is finite. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_of_finite_residueField (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ResidueField B)] :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  by_cases hfin : Finite (ramificationGroup G B 0)
  · exact ramificationGroup_one_eq_bot_iff_not_dvd_card G A B p
  · have hinf := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite]
    simp only [dvd_zero, not_true_eq_false, iff_false]
    intro h
    obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
    have hker := ker_tameCharacter A (G := G) hϖ
    rw [h, Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff] at hker
    exact hfin (Finite.of_injective _ hker)

/-- When `p` does not divide `#G_0`, every positive-depth ramification group `G_i` (`i > 0`) is
trivial. -/
theorem ramificationGroup_eq_bot_of_not_dvd_card (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    {i : ℤ} (hi : 0 < i) (hp : ¬ p ∣ Nat.card (ramificationGroup G B 0)) :
    ramificationGroup G B i = ⊥ :=
  eq_bot_mono (ramificationGroup_antitone G B (by omega : (1 : ℤ) ≤ i))
    ((ramificationGroup_one_eq_bot_iff_not_dvd_card G A B p).mpr hp)

/-! ### Residue characteristic zero -/

/-- In residue characteristic zero, under separable residue extension, every positive graded piece
`G_{n+1} / G_{n+2}` is torsion-free. -/
theorem eq_one_of_pow_eq_one_ramificationGroupGraded_natCast_succ_of_charZero
    [CharZero (ResidueField B)] {n k : ℕ} (hk : k ≠ 0)
    {x : RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)} (hx : x ^ k = 1) :
    x = 1 := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  apply (ramificationGroupGradedToUnitFiltrationGraded_injective A (G := G) (n + 1) hϖ)
  rw [map_one]
  refine eq_one_of_pow_eq_one_unitFiltrationGraded_succ_of_charZero hk ?_
  rw [← map_pow, hx, map_one]

/-- In residue characteristic zero, under separable residue extension, every finite positive graded
piece `G_{n+1} / G_{n+2}` is trivial. -/
theorem subsingleton_ramificationGroupGraded_natCast_succ_of_charZero [CharZero (ResidueField B)]
    (n : ℕ) [Finite (RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ))] :
    Subsingleton (RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)) :=
  subsingleton_of_forall_eq 1 fun x ↦
    eq_one_of_pow_eq_one_ramificationGroupGraded_natCast_succ_of_charZero G A B
      (isOfFinOrder_of_finite x).orderOf_pos.ne' (pow_orderOf_eq_one x)

/-- **In residue characteristic zero, every positive-depth ramification group `G_i` (`i > 0`) is
trivial**, whenever the residue extension is separable, the action is faithful, and `G_0` is
finite. -/
theorem ramificationGroup_eq_bot_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] {i : ℤ} (hi : 0 < i) :
    ramificationGroup G B i = ⊥ := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G B
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = ((j + 1 : ℕ) : ℤ) := ⟨(i - 1).toNat, by omega⟩
  suffices ∀ d j : ℕ, N ≤ j + 1 + d → ramificationGroup G B ((j + 1 : ℕ) : ℤ) = ⊥ from
    this N.toNat j (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    exact hN _ (by omega)
  | succ d ih =>
    intro j hj
    have hsucc : ramificationGroup G B ((j + 1 : ℕ) + 1) = ⊥ := by
      exact_mod_cast ih (j + 1) (by omega)
    have : Finite (ramificationGroup G B ((j + 1 : ℕ) : ℤ)) :=
      Finite.of_injective
        (Subgroup.inclusion (ramificationGroup_antitone G B (Int.natCast_nonneg (j + 1))))
        (Subgroup.inclusion_injective _)
    have : Subsingleton (RamificationGroupGraded G B ((j + 1 : ℕ) : ℤ)) :=
      subsingleton_ramificationGroupGraded_natCast_succ_of_charZero G A B j
    -- Since `G_{j+2} = ⊥` and `G_{j+1} / G_{j+2}` is a subsingleton, `G_{j+1} = ⊥`.
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    have hmk :
        (QuotientGroup.mk ⟨σ, hσ⟩ : RamificationGroupGraded G B ((j + 1 : ℕ) : ℤ)) = 1 :=
      Subsingleton.elim _ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hsucc, Subgroup.mem_bot] at hmk
    exact hmk

/-- **In residue characteristic zero, the wild inertia group `G_1` is trivial**, whenever the
residue extension is separable, the action is faithful, and `G_0` is finite. -/
theorem ramificationGroup_one_eq_bot_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    ramificationGroup G B 1 = ⊥ :=
  ramificationGroup_eq_bot_of_charZero G A B (by omega)

end Consequences

end TauCeti.IsDiscreteValuationRing
