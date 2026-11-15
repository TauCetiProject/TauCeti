/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.IntegralDomain
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.Monogenic
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.GroupTheory.PGroup

/-!
# Graded embeddings and tame/wild structure of ramification groups on a discrete valuation ring

Let a group `G` act by ring automorphisms on a discrete valuation ring `B` with maximal ideal `𝔪`
and residue field `k = ResidueField B`. Fixing a uniformizer `ϖ` of `B`, every `σ ∈ G_i` sends `ϖ`
to another uniformizer `σ • ϖ = ϖ * u_σ` with `u_σ ∈ (𝔪 ^ i).principalUnitGroup` (`Bˣ` for `i = 0`
and `1 + 𝔪 ^ i` for `i ≥ 1`). Passing to the successive quotient
`PrincipalUnitGroupGraded B i` yields a group homomorphism

`ramificationGroup G B i →* PrincipalUnitGroupGraded B i`

that is independent of the choice of uniformizer `ϖ` and kills `G_{i+1}`, hence descends to a
canonical homomorphism `RamificationGroupGraded G B i →* PrincipalUnitGroupGraded B i`. Composing
with the depth-`0` reduction isomorphism gives the uniformizer-independent **tame character**
`G_0 →* kˣ` (and `G_0 / G_1 →* kˣ`), while at positive depth `n + 1` composing with the uniformizer
coordinate gives an additive homomorphism
`Additive (G_{n+1} / G_{n+2}) →+ k` sending `σ` to the residue of `(σ • ϖ - ϖ) / ϖ ^ (n + 2)`.

Nothing in the construction of these homomorphisms requires a base ring, a fraction field,
completeness, or residue-field finiteness. When `G` acts by `R`-algebra automorphisms over a local
ring `R` such that the residue extension `ResidueField B / ResidueField R` is separable, Taylor
expansion of lifted minimal polynomials shows that membership of `σ ∈ G_0` in `G_n` is decided at
a single uniformizer (`σ ∈ G_n ↔ σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`). Consequently the kernel of the `i`-th
quotient homomorphism is `G_{i+1}` and all graded homomorphisms are injective.

From these embeddings one reads off the structure of inertia `G_0` and wild inertia `G_1` without
assuming a finite residue field:

* Every successive quotient `G_i / G_{i+1}` (`i ≥ 0`) is commutative, and when `G_0` is finite the
  tame quotient `G_0 / G_1` is cyclic.
* When `ResidueField B` has prime characteristic `p`, the index `[G_0 : G_1]` is prime to `p`,
  every positive graded piece `G_{n+1} / G_{n+2}` has exponent dividing `p` (hence is a `p`-group),
  and when `G` acts faithfully and `G_0` is finite every `G_i` (`i > 0`) is a `p`-group and `G_1`
  is the unique normal Sylow `p`-subgroup of `G_0`.
* When `ResidueField B` has characteristic zero and `G` acts faithfully with `G_0` finite, every
  positive ramification group vanishes (`G_1 = ⊥`) and `G_0` itself is cyclic.

The API and the positive-characteristic Sylow consequences parallel the local-field formalization
in `TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`, replacing fraction-field
unit ratios and Teichmüller lifts by `TauCeti.uniformizerChangeUnit` in `Bˣ` and polynomial lifting
adapted from `TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean` and
`TauCeti/RingTheory/LocalRing/Monogenic.lean`.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u_σ ∈ 1 + 𝔪 ^ i` satisfying
  `ϖ * u_σ = σ • ϖ`, for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded`: the
  uniformizer-independent homomorphisms `G_i →* PrincipalUnitGroupGraded B i` and
  `G_i / G_{i+1} →* PrincipalUnitGroupGraded B i`.
* `TauCeti.IsDiscreteValuationRing.tameCharacter` and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded`: the tame character `G_0 →* kˣ` and its
  descent to `G_0 / G_1`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField`: the positive-depth
  additive residue coordinate `Additive (G_{n+1} / G_{n+2}) →+ k` attached to a uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`: for separable residue extension in
  prime residue characteristic `p`, `G_1` as the unique normal Sylow `p`-subgroup of `G_0`.

## Main results

* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`: under a
  separable residue extension, `σ ∈ G_0` lies in `G_n` iff `σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGroupGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective`: injectivity of
  the graded maps under separable residue extension.
* `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one`: `G_0 / G_1` is cyclic of
  order prime to `p`.
* `TauCeti.IsDiscreteValuationRing.isPGroup_ramificationGroup`, `eq_ramificationGroupOneSylow`,
  `natCard_ramificationGroup_one`, and
  `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: wild inertia in positive
  residue characteristic.
* `TauCeti.IsDiscreteValuationRing.ramificationGroup_eq_bot_of_charZero`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroup_one_eq_bot_of_charZero`, and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: vanishing of wild
  inertia and cyclicity of inertia in residue characteristic zero.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–7 and 9.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Proposition 1 and Corollaries 1–2.
-/

public section
noncomputable section

open IsLocalRing Polynomial TauCeti.IsLocalRing

namespace TauCeti

namespace IsDiscreteValuationRing

section Homomorphisms

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]
variable {ϖ : B} {i : ℕ} {σ : G}

/-- Multiplying by a uniformizer shifts maximal-ideal power membership by one. -/
private theorem mul_mem_maximalIdeal_pow_succ_iff (hϖ : Irreducible ϖ) {x : B} (k : ℕ) :
    ϖ * x ∈ maximalIdeal B ^ (k + 1) ↔ x ∈ maximalIdeal B ^ k := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ',
    mul_dvd_mul_iff_left hϖ.ne_zero]

/-- For `σ ∈ G_i` and a uniformizer `ϖ`, the change unit sending `ϖ` to `σ • ϖ` lies in
`(𝔪 ^ i).principalUnitGroup`. -/
theorem uniformizerChangeUnit_smul_mem_principalUnitGroup (hϖ : Irreducible ϖ)
    (hσϖ : Irreducible (σ • ϖ)) (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ (σ • ϖ) hϖ hσϖ ∈ (maximalIdeal B ^ i).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup, ← mul_mem_maximalIdeal_pow_succ_iff hϖ i, mul_sub, mul_one,
    mul_uniformizerChangeUnit]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

variable (i) in
/-- The unit `u_σ ∈ (𝔪 ^ i).principalUnitGroup` characterized by `ϖ * u_σ = σ • ϖ`, for a
uniformizer `ϖ` and `σ ∈ G_i`. -/
def uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    (maximalIdeal B ^ i).principalUnitGroup :=
  have hσϖ : Irreducible ((σ : G) • ϖ) := hϖ.map (MulSemiringAction.toRingAut G B (σ : G))
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ,
    uniformizerChangeUnit_smul_mem_principalUnitGroup hϖ hσϖ σ.2⟩

/-- Multiplying `ϖ` on the right by `uniformizerRatio i hϖ σ` yields `σ • ϖ`. -/
@[simp]
theorem mul_uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ :=
  mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

/-- The uniformizer ratio of the identity element is `1`. -/
@[simp]
theorem uniformizerRatio_one (hϖ : Irreducible ϖ) :
    uniformizerRatio i hϖ (1 : ramificationGroup G B (i : ℤ)) = 1 := by
  ext
  exact mul_left_cancel₀ hϖ.ne_zero (by simp)

/-- `uniformizerRatio i hϖ σ` lies one step deeper in the principal-unit filtration precisely when
`σ` moves `ϖ` into `𝔪 ^ (i + 2)`. -/
theorem uniformizerRatio_mem_succ_iff (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ σ : Bˣ) ∈ (maximalIdeal B ^ (i + 1)).principalUnitGroup ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [Ideal.mem_principalUnitGroup, ← mul_mem_maximalIdeal_pow_succ_iff hϖ (i + 1), mul_sub,
    mul_one, mul_uniformizerRatio]

/-- Cocycle relation for `uniformizerRatio`: `u_{σ * τ} = u_σ * σ(u_τ)` in `Bˣ`. -/
private theorem coe_uniformizerRatio_mul (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ (σ * τ) : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  rw [mul_uniformizerRatio, Units.val_mul, ← mul_assoc, mul_uniformizerRatio, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulSemiringAction.toRingHom_apply,
    ← smul_mul', mul_uniformizerRatio, Subgroup.coe_mul, mul_smul]

/-- An element of `G_i` moves every unit of `B` by a factor in
`(𝔪 ^ (i + 1)).principalUnitGroup`. -/
private theorem unitsMap_smul_mul_inv_mem_principalUnitGroup
    (hσ : σ ∈ ramificationGroup G B (i : ℤ)) (u : Bˣ) :
    Units.map (MulSemiringAction.toRingHom G B σ).toMonoidHom u * u⁻¹ ∈
      (maximalIdeal B ^ (i + 1)).principalUnitGroup := by
  rw [Ideal.mul_inv_mem_principalUnitGroup, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, MulSemiringAction.toRingHom_apply]
  exact mem_ramificationGroup_natCast_iff.mp hσ (u : B)

variable (i) in
/-- The **quotient homomorphism** `G_i →* PrincipalUnitGroupGraded B i` sending `σ` to the class of
the unit `u_σ` with `ϖ * u_σ = σ • ϖ`. It does not depend on the choice of uniformizer `ϖ`
(`ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible`) and kills `G_{i+1}`. -/
def ramificationGroupToPrincipalUnitGroupGraded (hϖ : Irreducible ϖ) :
    ramificationGroup G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio i hϖ σ)) fun σ τ ↦ by
    symm
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_mul, coe_uniformizerRatio_mul]
    have hcancel :
        ((uniformizerRatio i hϖ σ : Bˣ) * (uniformizerRatio i hϖ τ : Bˣ))⁻¹ *
          ((uniformizerRatio i hϖ σ : Bˣ) *
            Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
              (uniformizerRatio i hϖ τ : Bˣ)) =
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) * (uniformizerRatio i hϖ τ : Bˣ)⁻¹ := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_comm]
    rw [hcancel]
    exact unitsMap_smul_mul_inv_mem_principalUnitGroup σ.2 (uniformizerRatio i hϖ τ : Bˣ)

/-- Evaluating `ramificationGroupToPrincipalUnitGroupGraded` at `σ` yields the class of
`uniformizerRatio i hϖ σ`. -/
@[simp]
theorem ramificationGroupToPrincipalUnitGroupGraded_apply (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToPrincipalUnitGroupGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

/-- `ramificationGroupToPrincipalUnitGroupGraded` is independent of the choice of uniformizer. -/
theorem ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible {ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ =
      ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ' := by
  set a : Bˣ := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have ha : ϖ * (a : B) = ϖ' := mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  refine MonoidHom.ext fun σ ↦ ?_
  rw [ramificationGroupToPrincipalUnitGroupGraded_apply,
    ramificationGroupToPrincipalUnitGroupGraded_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    Subgroup.coe_mul, Subgroup.coe_inv]
  have hrel : a * (uniformizerRatio i hϖ' σ : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
    apply Units.ext
    apply mul_left_cancel₀ hϖ.ne_zero
    rw [Units.val_mul, Units.val_mul, ← mul_assoc, ha, mul_uniformizerRatio, ← mul_assoc,
      mul_uniformizerRatio, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulSemiringAction.toRingHom_apply, ← smul_mul', ha]
  have hratio : (uniformizerRatio i hϖ σ : Bˣ)⁻¹ * (uniformizerRatio i hϖ' σ : Bˣ) =
      Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a * a⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul]
    apply mul_right_cancel (b := a)
    rw [mul_comm _ a, hrel, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  rw [hratio]
  exact unitsMap_smul_mul_inv_mem_principalUnitGroup σ.2 a

/-- An element `σ ∈ G_i` lies in the kernel of `ramificationGroupToPrincipalUnitGroupGraded i hϖ`
precisely when `σ • ϖ - ϖ ∈ 𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G B (i : ℤ)} :
    σ ∈ (ramificationGroupToPrincipalUnitGroupGraded i hϖ).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGroupGraded_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, uniformizerRatio_mem_succ_iff]

/-- The next ramification subgroup `G_{i+1}` lies in the kernel of
`ramificationGroupToPrincipalUnitGroupGraded i hϖ`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (hϖ : Irreducible ϖ) :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToPrincipalUnitGroupGraded i hϖ).ker := by
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff hϖ]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

variable (i) in
/-- The induced homomorphism `G_i / G_{i+1} →* PrincipalUnitGroupGraded B i` on successive
quotients. It does not depend on `ϖ`, and is injective whenever the residue extension over a
G-invariant local subring is separable
(`ramificationGroupGradedToPrincipalUnitGroupGraded_injective`). -/
def ramificationGroupGradedToPrincipalUnitGroupGraded (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGroupGraded i hϖ)
    fun _ hσ ↦ ramificationGroup_succ_subgroupOf_le_ker hϖ hσ

/-- Evaluating `ramificationGroupGradedToPrincipalUnitGroupGraded` on the class of `σ` yields the
class of `uniformizerRatio i hϖ σ`. -/
@[simp]
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGroupGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

/-- `ramificationGroupGradedToPrincipalUnitGroupGraded` does not depend on the uniformizer. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible {ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ =
      ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ' := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    exact DFunLike.congr_fun
      (ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible (G := G) (i := i) hϖ hϖ') σ

/-! ### Depth zero: the tame character -/

/-- The **tame character** `G_0 →* (ResidueField B)ˣ`, sending `σ ∈ G_0` to the residue of the unit
`u_σ` with `ϖ * u_σ = σ • ϖ`. It is independent of `ϖ` (`tameCharacter_eq_of_irreducible`) and
factors through `G_0 / G_1` (`tameCharacterGraded`). -/
def tameCharacter (hϖ : Irreducible ϖ) :
    ramificationGroup G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupToPrincipalUnitGroupGraded 0 hϖ)

/-- The underlying residue-field element of `tameCharacter hϖ σ` is the residue of
`uniformizerRatio 0 hϖ σ`. -/
theorem coe_tameCharacter (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (0 : ℤ)) :
    (tameCharacter hϖ σ : ResidueField B) =
      residue B ((uniformizerRatio 0 hϖ σ : Bˣ) : B) := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGroupGraded_apply (i := 0),
    principalUnitGroupGradedZeroEquivResidueFieldUnits_mk, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]

/-- Computing `tameCharacter hϖ σ` from any `y : B` satisfying `ϖ * y = σ • ϖ`. -/
theorem coe_tameCharacter_of_mul_eq (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (0 : ℤ))
    {y : B} (hy : ϖ * y = (σ : G) • ϖ) :
    (tameCharacter hϖ σ : ResidueField B) = residue B y := by
  have hy_eq : ((uniformizerRatio 0 hϖ σ : Bˣ) : B) = y :=
    mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio hϖ σ).trans hy.symm)
  rw [coe_tameCharacter, hy_eq]

/-- The tame character is independent of the choice of uniformizer. -/
theorem tameCharacter_eq_of_irreducible {ϖ' : B} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    tameCharacter (G := G) hϖ = tameCharacter (G := G) hϖ' := by
  rw [tameCharacter, tameCharacter,
    ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible (G := G) (i := 0) hϖ hϖ']

/-- An element of `G_0` lies in the kernel of `tameCharacter hϖ` iff `σ • ϖ - ϖ ∈ 𝔪 ^ 2`. -/
theorem mem_ker_tameCharacter_iff (hϖ : Irreducible ϖ) {σ : ramificationGroup G B (0 : ℤ)} :
    σ ∈ (tameCharacter hϖ).ker ↔ (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ 2 := by
  rw [tameCharacter, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGroupGradedZeroEquivResidueFieldUnits B).injective,
    ← MonoidHom.mem_ker, mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (i := 0) hϖ]

/-- The induced **graded tame character** `G_0 / G_1 →* (ResidueField B)ˣ`. -/
def tameCharacterGraded (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded 0 hϖ)

/-- Evaluating `tameCharacterGraded` on the class of `σ` agrees with `tameCharacter`. -/
@[simp]
theorem tameCharacterGraded_mk (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (0 : ℤ)) :
    tameCharacterGraded hϖ (QuotientGroup.mk σ) = tameCharacter hϖ σ :=
  (rfl)

/-- The graded tame character is independent of the choice of uniformizer. -/
theorem tameCharacterGraded_eq_of_irreducible {ϖ' : B} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacterGraded (G := G) hϖ = tameCharacterGraded (G := G) hϖ' := by
  rw [tameCharacterGraded, tameCharacterGraded,
    ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible (G := G) (i := 0) hϖ hϖ']

/-- **Conjugation equivariance of the tame character** (Serre, *Local Fields*, IV §2,
Proposition 9): conjugating `σ ∈ G_0` by `g ∈ G` acts on `tameCharacter hϖ σ` via the induced
action of `g` on `ResidueField B`. -/
@[simp]
theorem tameCharacter_conj (hϖ : Irreducible ϖ) (g : G) (σ : ramificationGroup G B (0 : ℤ)) :
    (tameCharacter hϖ (MulAut.conjNormal g σ) : ResidueField B) =
      g • (tameCharacter hϖ σ : ResidueField B) := by
  have hgϖ : Irreducible (g⁻¹ • ϖ) := hϖ.map (MulSemiringAction.toRingAut G B g⁻¹)
  conv_rhs => rw [tameCharacter_eq_of_irreducible (G := G) hϖ hgϖ, coe_tameCharacter]
  rw [← ResidueField.residue_smul]
  refine coe_tameCharacter_of_mul_eq hϖ (MulAut.conjNormal g σ) ?_
  calc ϖ * g • ((uniformizerRatio 0 hgϖ σ : Bˣ) : B)
      = g • (g⁻¹ • ϖ) * g • ((uniformizerRatio 0 hgϖ σ : Bˣ) : B) := by rw [smul_inv_smul]
    _ = g • (g⁻¹ • ϖ * ((uniformizerRatio 0 hgϖ σ : Bˣ) : B)) := (smul_mul' g _ _).symm
    _ = g • ((σ : G) • (g⁻¹ • ϖ)) := by rw [mul_uniformizerRatio]
    _ = (MulAut.conjNormal g σ : G) • ϖ := by
      rw [MulAut.conjNormal_apply, mul_smul, mul_smul]

/-- Conjugation by `g ∈ G` on `G_0 / G_1` corresponds under `tameCharacterGraded` to the induced
action of `g` on `ResidueField B`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (hϖ : Irreducible ϖ) (g : G)
    (x : RamificationGroupGraded G B (0 : ℤ)) :
    (tameCharacterGraded hϖ (ramificationGroupGradedConj G B g 0 x) : ResidueField B) =
      g • (tameCharacterGraded hϖ x : ResidueField B) := by
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

/-! ### Positive depth: additive residue-field coordinates -/

variable (G B) in
/-- The positive-depth additive homomorphism `Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` in the
coordinate determined by a uniformizer `ϖ`, sending `σ` to the residue of
`(σ • ϖ - ϖ) / ϖ ^ (n + 2)`. -/
def ramificationGroupGradedToResidueField (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ) :
    Additive (RamificationGroupGraded G B ((n : ℤ) + 1)) →+ ResidueField B := by
  simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
    (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ).toAddMonoidHom.comp
      (ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) (n + 1) hϖ).toAdditive

/-- Evaluating `ramificationGroupGradedToResidueField` on the class of `τ` gives the uniformizer
coordinate of `uniformizerRatio (n + 1) hϖ τ`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n ϖ hϖ (Additive.ofMul (QuotientGroup.mk τ)) =
      principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ
        (Additive.ofMul (QuotientGroup.mk (uniformizerRatio (n + 1) hϖ τ))) := by
  rw [ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply]
  apply congrArg _
  exact congrArg Additive.ofMul
    (ramificationGroupGradedToPrincipalUnitGroupGraded_mk (i := n + 1) hϖ τ)

/-- Compute the positive-depth residue coordinate from `(τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) (y : B)
    (hmove : (τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)) :
    ramificationGroupGradedToResidueField G B n ϖ hϖ
        (Additive.ofMul (QuotientGroup.mk τ)) = residue B y := by
  have hdiff : ((uniformizerRatio (n + 1) hϖ τ : Bˣ) : B) - 1 = y * ϖ ^ (n + 1) := by
    apply mul_left_cancel₀ hϖ.ne_zero
    calc ϖ * (((uniformizerRatio (n + 1) hϖ τ : Bˣ) : B) - 1)
        = (τ : G) • ϖ - ϖ := by rw [mul_sub, mul_uniformizerRatio, mul_one]
      _ = y * ϖ ^ (n + 2) := hmove
      _ = ϖ * (y * ϖ ^ (n + 1)) := by rw [pow_succ']; ring
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  exact principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
    n ϖ hϖ _ y hdiff

/-- Replacing `ϖ` by `ϖ' = ϖ * a` scales `ramificationGroupGradedToResidueField`: the coordinate
relative to `ϖ` equals `residue B a ^ (n + 1)` times the coordinate relative to `ϖ'`. -/
theorem ramificationGroupGradedToResidueField_change (n : ℕ) (ϖ ϖ' : B) (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n ϖ hϖ (Additive.ofMul τ) =
      residue B (uniformizerChangeUnit ϖ ϖ' hϖ hϖ' : B) ^ (n + 1) *
        ramificationGroupGradedToResidueField G B n ϖ' hϖ' (Additive.ofMul τ) := by
  have hchange :=
    principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_change n ϖ ϖ' hϖ hϖ'
      (Additive.ofMul (ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) (n + 1) hϖ τ))
  have htheta := DFunLike.congr_fun
    (ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible
      (G := G) (i := n + 1) hϖ hϖ') τ
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply]
  simpa [htheta] using hchange

end Homomorphisms

section Separable

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]
variable (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R B] [IsLocalHom (algebraMap R B)]
  [SMulCommClass G R B] [Algebra.IsSeparable (ResidueField R) (ResidueField B)]
variable {ϖ : B} {i : ℕ} {σ : G}

include R

/-- **Uniformizer criterion for higher ramification groups under separable residue extension.**
When `G` acts by `R`-algebra automorphisms over a local ring `R` and
`ResidueField B / ResidueField R` is separable, an element `σ ∈ G_0` lies in `G_n` if and only if
`σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)` for a single uniformizer `ϖ`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem (hϖ : Irreducible ϖ)
    (hσ : σ ∈ ramificationGroup G B 0) {n : ℕ} :
    σ ∈ ramificationGroup G B (n : ℤ) ↔ σ • ϖ - ϖ ∈ maximalIdeal B ^ (n + 1) := by
  rw [mem_ramificationGroup_natCast_iff]
  refine ⟨fun h ↦ h ϖ, fun hϖn ↦ ?_⟩
  have hϖ_mem : ϖ ∈ maximalIdeal B := (mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  suffices ∀ m ≤ n + 1, ∀ x : B, σ • x - x ∈ maximalIdeal B ^ m from this (n + 1) le_rfl
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    -- First propagate from `ϖ` to all elements of `𝔪`: write `w = ϖ * y`.
    have hmax : ∀ w ∈ maximalIdeal B, σ • w - w ∈ maximalIdeal B ^ (m + 1) := by
      intro w hw
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hw
      obtain ⟨y, rfl⟩ := hw
      have hsplit : σ • (ϖ * y) - ϖ * y = (σ • ϖ - ϖ) * (σ • y) + ϖ * (σ • y - y) := by
        rw [smul_mul']
        ring
      rw [hsplit]
      refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hm hϖn)) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hϖ_mem (ih (by omega) y)
    -- Now take any `x : B`, lift the minimal polynomial of `residue B x` over `ResidueField R`,
    -- and expand `f_B(σ • x) - f_B(x)` around `x`.
    intro x
    obtain ⟨f, hf⟩ := (mem_lifts _).mp
      (mem_lifts_of_surjective residue_surjective (minpoly (ResidueField R) (residue B x)))
    let fB : B[X] := f.map (algebraMap R B)
    have hfB_eval : fB.eval x ∈ maximalIdeal B := by
      dsimp only [fB]
      rw [← residue_eq_zero_iff, eval_map, ← aeval_def,
        map_aeval_eq_aeval_map (residue_comp_algebraMap (R := R) (S := B)), hf]
      exact minpoly.aeval _ _
    have hfB_der : IsUnit ((derivative fB).eval x) := by
      dsimp only [fB]
      rw [derivative_map, eval_map, ← aeval_def, ← residue_ne_zero_iff_isUnit,
        map_aeval_eq_aeval_map (residue_comp_algebraMap (R := R) (S := B)), ← derivative_map, hf]
      exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
    obtain ⟨K, hK⟩ := binomExpansion fB x (σ • x - x)
    rw [add_sub_cancel] at hK
    set u : B := (derivative fB).eval x + K * (σ • x - x)
    have hdx_mem : σ • x - x ∈ maximalIdeal B := mem_ramificationGroup_zero_iff.mp hσ x
    have hu_unit : IsUnit u := by
      refine notMem_maximalIdeal.mp fun hu_mem ↦ notMem_maximalIdeal.mpr hfB_der ?_
      simpa [u] using sub_mem hu_mem (Ideal.mul_mem_left _ K hdx_mem)
    have hdu : fB.eval (σ • x) - fB.eval x = (σ • x - x) * u := by
      rw [hK]
      ring
    have heval_mem : (σ • x - x) * u ∈ maximalIdeal B ^ (m + 1) := by
      have hsmul : fB.eval (σ • x) = σ • fB.eval x := by
        simpa only [fB, eval_map, ← aeval_def] using f.aeval_smul σ x
      rw [← hdu, hsmul]
      exact hmax _ hfB_eval
    obtain ⟨u', hu'⟩ := hu_unit.exists_right_inv
    simpa [mul_assoc, hu'] using Ideal.mul_mem_right u' _ heval_mem

/-- **The kernel of the `i`-th quotient homomorphism is `G_{i+1}`**, when the residue extension
over `R` is separable. -/
theorem ker_ramificationGroupToPrincipalUnitGroupGraded (hϖ : Irreducible ϖ) :
    (ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker hϖ)
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff hϖ] at hσ
  have hσ0 : (σ : G) ∈ ramificationGroup G B 0 :=
    ramificationGroup_antitone G B (Int.natCast_nonneg i) σ.2
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ hσ0]
  exact hσ

/-- **The graded homomorphism `G_i / G_{i+1} →* PrincipalUnitGroupGraded B i` is injective**, when
the residue extension over `R` is separable. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_injective (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGroupGraded R hϖ).symm

/-- **The kernel of the tame character is `G_1`**, when the residue extension over `R` is
separable. -/
theorem ker_tameCharacter (hϖ : Irreducible ϖ) :
    (tameCharacter (G := G) hϖ).ker =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) := by
  ext σ
  rw [mem_ker_tameCharacter_iff hϖ, Subgroup.mem_subgroupOf,
    ← Nat.cast_one, mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ σ.2]

/-- **The graded tame character `G_0 / G_1 →* (ResidueField B)ˣ` is injective**, when the residue
extension over `R` is separable. -/
theorem tameCharacterGraded_injective (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacterGraded (G := G) hϖ) :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits B).injective.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded_injective R (i := 0) hϖ)

/-- **The positive-depth residue coordinate `Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` is
injective**, when the residue extension over `R` is separable. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToResidueField G B n ϖ hϖ) :=
  (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ).injective.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded_injective R (i := n + 1) hϖ)

/-! ### Tame and wild structure of `G_0` and `G_1` -/

/-- Every successive quotient `G_i / G_{i+1}` (`i ≥ 0`) is commutative when the residue extension
over `R` is separable: it embeds into `PrincipalUnitGroupGraded B i`, a quotient of a subgroup of
the commutative group `Bˣ`. -/
theorem isMulCommutative_ramificationGroupGraded (i : ℕ) :
    IsMulCommutative (RamificationGroupGraded G B (i : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hinj := ramificationGroupGradedToPrincipalUnitGroupGraded_injective R (G := G) (i := i) hϖ
  exact IsMulCommutative.of_comm fun a b ↦ hinj (by rw [map_mul, map_mul, mul_comm'])

/-- **The tame quotient `G_0 / G_1` is cyclic** whenever `G_0` is finite and the residue extension
over `R` is separable, with no finiteness assumption on `ResidueField B`. -/
theorem isCyclic_ramificationGroupGraded_zero [Finite (ramificationGroup G B 0)] :
    IsCyclic (RamificationGroupGraded G B (0 : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacterGraded (G := G) hϖ))
    (Units.val_injective.comp (tameCharacterGraded_injective R hϖ))

/-- In residue characteristic `p`, every element of `G_{n+1} / G_{n+2}` has `p`-th power equal to
`1`, since `G_{n+1} / G_{n+2}` embeds into the additive group of `ResidueField B`. -/
theorem pow_char_eq_one_of_ramificationGroupGraded_natCast_succ (p : ℕ)
    [CharP (ResidueField B) p] (n : ℕ)
    (x : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    x ^ p = 1 := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  apply Additive.ofMul.injective
  apply ramificationGroupGradedToResidueField_injective R n ϖ hϖ
  rw [ofMul_pow, map_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofMul_one, map_zero]

/-- At positive depth `n + 1`, the graded piece `G_{n+1} / G_{n+2}` is a `p`-group for the residue
characteristic `p` (with no finiteness assumption on `G_0` or `ResidueField B`). -/
theorem isPGroup_ramificationGroupGraded_natCast_succ (p : ℕ) [CharP (ResidueField B) p] (n : ℕ) :
    IsPGroup p (RamificationGroupGraded G B ((n : ℤ) + 1)) := fun x ↦
  ⟨1, by rw [pow_one, pow_char_eq_one_of_ramificationGroupGraded_natCast_succ R p n x]⟩

/-- **Every positive-depth ramification group is a `p`-group** in residue characteristic `p`,
whenever the action on `B` is faithful, `G_0` is finite, and the residue extension over `R` is
separable. -/
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
      (isPGroup_ramificationGroupGraded_natCast_succ R p j)
    push_cast
    exact hsucc.comap_subtype

/-- **The index of `G_1` in `G_0` is prime to `p`** when `ResidueField B` has prime characteristic
`p`, `G_0` is finite, and the residue extension over `R` is separable: `(ResidueField B)ˣ` contains
no element of order `p`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [Finite (ramificationGroup G B 0)] :
    ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hφ := tameCharacterGraded_injective R (G := G) hϖ
  intro hp
  have hp_card : p ∣ Nat.card (RamificationGroupGraded G B 0) := by
    rwa [RamificationGroupGraded, zero_add, ← Subgroup.index_eq_card]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp_card
  have hord : orderOf ((tameCharacterGraded hϖ x : (ResidueField B)ˣ) : ResidueField B) = p := by
    rw [orderOf_units, orderOf_injective _ hφ x, hx]
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hroot := hord ▸
    IsPrimitiveRoot.orderOf ((tameCharacterGraded hϖ x : (ResidueField B)ˣ) : ResidueField B)
  exact hroot.neZero'.out (CharP.cast_eq_zero _ p)

/-- **Wild inertia `G_1` as a Sylow `p`-subgroup of inertia `G_0`**, for a faithful action with
finite `G_0` and separable residue extension over `R` in prime residue characteristic `p`. -/
def ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Sylow p (ramificationGroup G B 0) :=
  ((isPGroup_ramificationGroup R p (G := G) (i := 1) (by omega)).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one R p)

/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` viewed inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow R (G := G) (B := B) p : Subgroup (ramificationGroup G B 0)) =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) :=
  (rfl)

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow R (G := G) (B := B) p :
      Subgroup (ramificationGroup G B 0)).Normal := by
  rw [ramificationGroupOneSylow_coe, Subgroup.normal_subgroupOf_iff_le_normalizer
    (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)),
    Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

/-- `ramificationGroupOneSylow` is the unique Sylow `p`-subgroup of `G_0`. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (Q : Sylow p (ramificationGroup G B 0)) :
    Q = ramificationGroupOneSylow R (G := G) (B := B) p := by
  let _ : Unique (Sylow p (ramificationGroup G B 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow R (G := G) (B := B) p)
      (ramificationGroupOneSylow_normal R (G := G) (B := B) p)
  exact Subsingleton.elim _ _

/-- The order of wild inertia `G_1` is the `p`-part of the order of inertia `G_0`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Nat.card (ramificationGroup G B 1) =
      p ^ (Nat.card (ramificationGroup G B 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow R (G := G) (B := B) p)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`**, in prime residue
characteristic `p`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField B) p] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  have hp : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one R (G := G) (B := B) p,
    pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
  simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

/-! ### Residue characteristic zero -/

/-- In residue characteristic zero, every positive graded piece `G_{n+1} / G_{n+2}` is trivial once
`G_0` is finite: a finite subgroup of the torsion-free additive group `ResidueField B` is zero. -/
theorem subsingleton_ramificationGroupGraded_natCast_succ [CharZero (ResidueField B)]
    [Finite (ramificationGroup G B 0)] (n : ℕ) :
    Subsingleton (RamificationGroupGraded G B ((n : ℤ) + 1)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hfin : Finite (ramificationGroup G B ((n : ℤ) + 1)) :=
    Finite.of_injective
      (Subgroup.inclusion (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ (n : ℤ) + 1)))
      (Subgroup.inclusion_injective _)
  have hfinQ : Finite (RamificationGroupGraded G B ((n : ℤ) + 1)) := inferInstance
  have h1 : ∀ x : RamificationGroupGraded G B ((n : ℤ) + 1), x = 1 := fun x ↦ by
    have hord_pos : 0 < orderOf x := (isOfFinOrder_of_finite x).orderOf_pos
    have himg : ramificationGroupGradedToResidueField G B n ϖ hϖ (Additive.ofMul x) = 0 := by
      have hmul : (orderOf x : ResidueField B) *
          ramificationGroupGradedToResidueField G B n ϖ hϖ (Additive.ofMul x) = 0 := by
        rw [← nsmul_eq_mul, ← map_nsmul, ← ofMul_pow, pow_orderOf_eq_one, ofMul_one, map_zero]
      exact (mul_eq_zero.mp hmul).resolve_left (Nat.cast_ne_zero.mpr hord_pos.ne')
    apply Additive.ofMul.injective
    exact ramificationGroupGradedToResidueField_injective R n ϖ hϖ (himg.trans (map_zero _).symm)
  exact ⟨fun x y ↦ (h1 x).trans (h1 y).symm⟩

/-- **In residue characteristic zero, all positive ramification groups vanish** whenever `G` acts
faithfully on `B`, `G_0` is finite, and the residue extension over `R` is separable. -/
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
    have hsucc : ramificationGroup G B (((j + 1 : ℕ) : ℤ) + 1) = ⊥ := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using ih (j + 1) (by omega)
    have hsub : Subsingleton (RamificationGroupGraded G B ((j + 1 : ℕ) : ℤ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        subsingleton_ramificationGroupGraded_natCast_succ R (G := G) (B := B) j
    rw [eq_bot_iff]
    intro g hg
    have hq : QuotientGroup.mk (s := (ramificationGroup G B (((j + 1 : ℕ) : ℤ) + 1)).subgroupOf
        (ramificationGroup G B ((j + 1 : ℕ) : ℤ))) ⟨g, hg⟩ = 1 :=
      Subsingleton.elim _ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hsucc] at hq
    exact hq

/-- **Wild inertia vanishes in residue characteristic zero**, for a faithful action with finite
`G_0` and separable residue extension over `R`. -/
theorem ramificationGroup_one_eq_bot_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    ramificationGroup G B 1 = ⊥ :=
  ramificationGroup_eq_bot_of_charZero R (by omega)

/-- **Inertia `G_0` is cyclic in residue characteristic zero**, for a faithful action with finite
`G_0` and separable residue extension over `R`. -/
theorem isCyclic_ramificationGroup_zero_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    IsCyclic (ramificationGroup G B 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hker : (tameCharacter (G := G) hϖ).ker = ⊥ := by
    rw [ker_tameCharacter R hϖ, ramificationGroup_one_eq_bot_of_charZero R (G := G) (B := B),
      Subgroup.bot_subgroupOf]
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacter (G := G) hϖ))
    (Units.val_injective.comp ((MonoidHom.ker_eq_bot_iff _).mp hker))

end Separable

end IsDiscreteValuationRing

end TauCeti
