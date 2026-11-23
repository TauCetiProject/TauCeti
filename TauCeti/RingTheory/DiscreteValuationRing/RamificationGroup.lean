/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.IntegralDomain
public import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

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
`Additive (G_{n+1} / G_{n+2}) →+ k` sending `σ` to the residue of `(σ • ϖ - ϖ) / ϖ ^ (n + 2)`, on
which conjugation by `σ ∈ G_0` acts as multiplication by `(tameCharacter G B σ) ^ (n + 1)`.

Nothing in the construction of these homomorphisms, their conjugation equivariance, or the
characteristic-zero structure of `G_0` requires a base ring, a fraction field, completeness, or
residue-field finiteness. In residue characteristic zero, any finite-order element of `G_0` that
moves a uniformizer by `𝔪 ^ 2` lies in `G_1`, so whenever `G` acts faithfully and `G_0` is finite,
wild inertia vanishes (`TauCeti.IsLocalRing.ramificationGroup_one_eq_bot_of_charZero`), the tame
character is injective, and `G_0` is cyclic.

When `G` acts by `R`-algebra automorphisms over a local ring `R` such that the residue extension
`ResidueField B / ResidueField R` is separable, Taylor expansion of lifted minimal polynomials
(`TauCeti.IsLocalRing.mem_inertia_of_forall_mem_maximalIdeal`) shows that membership of `σ ∈ G_0` in
`G_n` is decided at a single uniformizer (`σ ∈ G_n ↔ σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`). Consequently the
kernel of the `i`-th quotient homomorphism is `G_{i+1}` and all graded homomorphisms are injective.

Combining these embeddings with the base-free, local-ring positive-depth structure theorems in
`TauCeti/RingTheory/LocalRing/RamificationGroup.lean`, one reads off the structure of inertia `G_0`
and wild inertia `G_1` without assuming a finite residue field:

* Under a separable residue extension over `R`, every successive quotient `G_i / G_{i+1}` (`i ≥ 0`)
  is commutative (positive-depth commutativity already holds without `R` or DVR assumptions in
  `TauCeti/RingTheory/LocalRing/RamificationGroup.lean`), and when `G_0 / G_1` is finite the tame
  quotient `G_0 / G_1` is cyclic.
* When `ResidueField B` has prime characteristic `p` and `ResidueField B / ResidueField R` is
  separable, the index `[G_0 : G_1]` is prime to `p` whenever `G_0 / G_1` is finite; more
  generally, whenever `[G_0 : G_1]` is prime to `p` (and `G` acts faithfully with `G_0` finite),
  combining this with `TauCeti.IsLocalRing.isPGroup_ramificationGroup` shows that `G_1` is the
  unique normal Sylow `p`-subgroup of `G_0`.
* When `ResidueField B` has characteristic zero and `G` acts faithfully with `G_0` finite (with no
  base ring `R` or separability assumption), every positive ramification group vanishes
  (`TauCeti.IsLocalRing.ramificationGroup_eq_bot_of_charZero`) and `G_0` itself is cyclic.

The API and the positive-characteristic Sylow consequences parallel the local-field formalization
in `TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean`, with the conjugation
equivariance of `tameCharacter`, `tameCharacterGraded`, and
`ramificationGroupGradedToResidueField` adapted from
`TauCeti/NumberTheory/LocalField/UnitFiltration/Conjugation.lean`, replacing fraction-field unit
ratios and Teichmüller lifts by `TauCeti.uniformizerChangeUnit` in `Bˣ` and polynomial lifting
from `TauCeti/RingTheory/LocalRing/Monogenic.lean`. The separable-residue polynomial-lifting
criterion and the non-finite-residue-field cyclicity and prime-to-`p` index proofs for `G_0 / G_1`
are adapted from `TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean`.

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
* `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`: for a faithful action with finite
  `G_0` in prime residue characteristic `p` when `[G_0 : G_1]` is prime to `p`, `G_1` as the
  unique normal Sylow `p`-subgroup of `G_0`.

## Main results

* `TauCeti.IsDiscreteValuationRing.coe_uniformizerRatio_mul`,
  `TauCeti.IsDiscreteValuationRing.tameCharacter_conj`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_ramificationGroupGradedConj`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_conj`: the 1-cocycle law
  for `uniformizerRatio` and the conjugation-equivariance formulas on depth `0` and positive-depth
  graded pieces.
* `TauCeti.IsDiscreteValuationRing.smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer`:
  propagation of `σ • x - x ∈ 𝔪 ^ m` to `𝔪 ^ (m + 1)` on `𝔪` from a uniformizer.
* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_one_of_charZero`,
  `TauCeti.IsDiscreteValuationRing.ker_tameCharacter_of_charZero`, and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: in residue
  characteristic zero, without any base ring or separability assumption, a faithful action with
  finite `G_0` has injective tame character and cyclic inertia `G_0`.
* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_natCast_iff_smul_sub_mem`: under a
  separable residue extension over `R`, `σ ∈ G_0` lies in `G_n` iff `σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGroupGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective`: injectivity of
  the graded maps under separable residue extension over `R`.
* `TauCeti.IsDiscreteValuationRing.isMulCommutative_ramificationGroupGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedConj_zero`,
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero`, and
  `TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one`: under separable residue
  extension over `R`, each `G_i / G_{i+1}` is commutative, `G_0` acts trivially on `G_0 / G_1`, and
  when `G_0 / G_1` is finite it is cyclic and (in prime residue characteristic `p`) of order prime
  to `p`.
* `TauCeti.IsDiscreteValuationRing.eq_ramificationGroupOneSylow`, `natCard_ramificationGroup_one`,
  and `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: for a faithful action
  with finite `G_0` in prime residue characteristic `p` when `[G_0 : G_1]` is prime to `p`,
  `G_1` is the unique normal Sylow `p`-subgroup of `G_0`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5–7 and 9.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Proposition 1 and Corollaries 1–2.
-/

public section
noncomputable section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti

namespace IsDiscreteValuationRing

section Homomorphisms

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]
variable {ϖ : B} {i : ℕ} {σ : G}

/-- Propagating congruence along a uniformizer `ϖ`: if `σ • ϖ - ϖ ∈ 𝔪 ^ (m + 1)` and
`σ • y - y ∈ 𝔪 ^ m` for every `y : B`, then `σ • w - w ∈ 𝔪 ^ (m + 1)` for every `w ∈ 𝔪`. -/
theorem smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer {m : ℕ} (hϖ : Irreducible ϖ)
    (hϖm : σ • ϖ - ϖ ∈ maximalIdeal B ^ (m + 1)) (hB : ∀ y : B, σ • y - y ∈ maximalIdeal B ^ m)
    {w : B} (hw : w ∈ maximalIdeal B) :
    σ • w - w ∈ maximalIdeal B ^ (m + 1) := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hw
  obtain ⟨y, rfl⟩ := hw
  rw [smul_mul_sub_mul]
  refine add_mem (Ideal.mul_mem_right _ _ hϖm) ?_
  rw [pow_succ']
  exact Ideal.mul_mem_mul ((mem_maximalIdeal ϖ).mpr hϖ.not_isUnit) (hB y)

/-- For `σ ∈ G_i` and a uniformizer `ϖ`, the change unit sending `ϖ` to `σ • ϖ` lies in
`(𝔪 ^ i).principalUnitGroup`. -/
theorem uniformizerChangeUnit_smul_mem_principalUnitGroup (hϖ : Irreducible ϖ)
    (hσϖ : Irreducible (σ • ϖ)) (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    uniformizerChangeUnit ϖ (σ • ϖ) hϖ hσϖ ∈ (maximalIdeal B ^ i).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup, ← hϖ.mul_mem_maximalIdeal_pow_succ_iff, mul_sub, mul_one,
    mul_uniformizerChangeUnit]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

variable (i) in
/-- The unit `u_σ ∈ (𝔪 ^ i).principalUnitGroup` characterized by `ϖ * u_σ = σ • ϖ`, for a
uniformizer `ϖ` and `σ ∈ G_i`. -/
def uniformizerRatio (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    (maximalIdeal B ^ i).principalUnitGroup :=
  have hσϖ : Irreducible ((σ : G) • ϖ) := hϖ.map (MulSemiringAction.toRingAut G B (σ : G))
  ⟨uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ hσϖ,
    uniformizerChangeUnit_smul_mem_principalUnitGroup hϖ hσϖ σ.property⟩

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
`σ` moves `ϖ` by an element of `𝔪 ^ (i + 2)`. -/
theorem coe_uniformizerRatio_mem_principalUnitGroup_succ_iff (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ σ : Bˣ) ∈ (maximalIdeal B ^ (i + 1)).principalUnitGroup ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [Ideal.mem_principalUnitGroup, ← hϖ.mul_mem_maximalIdeal_pow_succ_iff, mul_sub,
    mul_one, mul_uniformizerRatio]

/-- Cocycle relation for `uniformizerRatio`: `u_{σ * τ} = u_σ * σ(u_τ)` in `Bˣ`. -/
theorem coe_uniformizerRatio_mul (hϖ : Irreducible ϖ)
    (σ τ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ (σ * τ) : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
          (uniformizerRatio i hϖ τ : Bˣ) := by
  apply Units.ext
  apply mul_left_cancel₀ hϖ.ne_zero
  calc ϖ * ((uniformizerRatio i hϖ (σ * τ) : Bˣ) : B)
      = (σ : G) • ((τ : G) • ϖ) := by simp [mul_smul]
    _ = (σ : G) • (ϖ * ((uniformizerRatio i hϖ τ : Bˣ) : B)) := by rw [mul_uniformizerRatio]
    _ = ((σ : G) • ϖ) * ((σ : G) • ((uniformizerRatio i hϖ τ : Bˣ) : B)) := smul_mul' _ _ _
    _ = ϖ * (((uniformizerRatio i hϖ σ : Bˣ) *
          Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom
            (uniformizerRatio i hϖ τ : Bˣ) : Bˣ) : B) := by
        rw [← mul_uniformizerRatio hϖ σ, mul_assoc]
        simp

private def ramificationGroupToPrincipalUnitGroupGradedOf (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
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
    exact unitsMap_mul_inv_mem_principalUnitGroup_natCast σ.property (uniformizerRatio i hϖ τ : Bˣ)

private theorem ramificationGroupToPrincipalUnitGroupGradedOf_eq {i : ℕ} {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToPrincipalUnitGroupGradedOf (G := G) i hϖ =
      ramificationGroupToPrincipalUnitGroupGradedOf (G := G) i hϖ' := by
  set a : Bˣ := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have ha : ϖ * (a : B) = ϖ' := mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  refine MonoidHom.ext fun σ ↦ ?_
  change QuotientGroup.mk (uniformizerRatio i hϖ σ) =
    QuotientGroup.mk (uniformizerRatio i hϖ' σ)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have hrel : a * (uniformizerRatio i hϖ' σ : Bˣ) =
      (uniformizerRatio i hϖ σ : Bˣ) *
        Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
    apply Units.ext
    apply mul_left_cancel₀ hϖ.ne_zero
    calc ϖ * ((a * (uniformizerRatio i hϖ' σ : Bˣ) : Bˣ) : B)
        = ϖ' * ((uniformizerRatio i hϖ' σ : Bˣ) : B) := by rw [Units.val_mul, ← mul_assoc, ha]
      _ = (σ : G) • (ϖ * (a : B)) := by rw [mul_uniformizerRatio, ha]
      _ = ((σ : G) • ϖ) * ((σ : G) • (a : B)) := smul_mul' _ _ _
      _ = ϖ * (((uniformizerRatio i hϖ σ : Bˣ) *
            Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a : Bˣ) : B) := by
          rw [← mul_uniformizerRatio hϖ σ, mul_assoc]
          simp
  have hratio : (uniformizerRatio i hϖ σ : Bˣ)⁻¹ * (uniformizerRatio i hϖ' σ : Bˣ) =
      Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a * a⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul]
    apply mul_right_cancel (b := a)
    rw [mul_comm _ a, hrel, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  rw [hratio]
  exact unitsMap_mul_inv_mem_principalUnitGroup_natCast σ.property a

variable (G B i) in
/-- The **quotient homomorphism** `G_i →* PrincipalUnitGroupGraded B i` sending `σ` to the class of
the unit `u_σ` with `ϖ * u_σ = σ • ϖ` for any uniformizer `ϖ`. It is independent of `ϖ` and kills
`G_{i+1}`. -/
def ramificationGroupToPrincipalUnitGroupGraded :
    ramificationGroup G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  ramificationGroupToPrincipalUnitGroupGradedOf i
    (_root_.IsDiscreteValuationRing.exists_irreducible B).choose_spec

/-- Evaluating `ramificationGroupToPrincipalUnitGroupGraded` at `σ` using any uniformizer `ϖ`
yields the class of `uniformizerRatio i hϖ σ`. -/
theorem ramificationGroupToPrincipalUnitGroupGraded_apply (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToPrincipalUnitGroupGraded G B i σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupToPrincipalUnitGroupGraded,
    ramificationGroupToPrincipalUnitGroupGradedOf_eq (G := G) _ hϖ]
  rfl

/-- An element `σ ∈ G_i` lies in the kernel of `ramificationGroupToPrincipalUnitGroupGraded G B i`
precisely when `σ • ϖ - ϖ ∈ 𝔪 ^ (i + 2)` for a uniformizer `ϖ`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G B (i : ℤ)} :
    σ ∈ (ramificationGroupToPrincipalUnitGroupGraded G B i).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGroupGraded_apply hϖ,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    coe_uniformizerRatio_mem_principalUnitGroup_succ_iff]

variable (G B i) in
/-- The next ramification subgroup `G_{i+1}` lies in the kernel of
`ramificationGroupToPrincipalUnitGroupGraded G B i`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToPrincipalUnitGroupGraded G B i).ker := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff hϖ]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

variable (G B i) in
/-- The induced homomorphism `G_i / G_{i+1} →* PrincipalUnitGroupGraded B i` on successive
quotients. It is injective whenever the residue extension over a `G`-invariant local subring is
separable (`ramificationGroupGradedToPrincipalUnitGroupGraded_injective`). -/
def ramificationGroupGradedToPrincipalUnitGroupGraded :
    RamificationGroupGraded G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGroupGraded G B i)
    (ramificationGroup_succ_subgroupOf_le_ker G B i)

/-- Evaluating `ramificationGroupGradedToPrincipalUnitGroupGraded` on the class of `σ` using any
uniformizer `ϖ` yields the class of `uniformizerRatio i hϖ σ`. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_mk (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGroupGraded G B i (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) := by
  rw [ramificationGroupGradedToPrincipalUnitGroupGraded, QuotientGroup.lift_mk,
    ramificationGroupToPrincipalUnitGroupGraded_apply hϖ]

/-! ### Depth zero: the tame character -/

variable (G B) in
/-- The **tame character** `G_0 →* (ResidueField B)ˣ`, sending `σ ∈ G_0` to the residue of the unit
`u_σ` with `ϖ * u_σ = σ • ϖ` for any uniformizer `ϖ`. It is independent of `ϖ` and factors through
`G_0 / G_1` (`tameCharacterGraded`). -/
def tameCharacter :
    ramificationGroup G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupToPrincipalUnitGroupGraded G B 0)

/-- The underlying residue-field element of `tameCharacter G B σ` is the residue of
`uniformizerRatio 0 hϖ σ` for any uniformizer `ϖ`. -/
theorem coe_tameCharacter (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (0 : ℤ)) :
    (tameCharacter G B σ : ResidueField B) =
      residue B ((uniformizerRatio 0 hϖ σ : Bˣ) : B) := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGroupGraded_apply (i := 0) hϖ,
    principalUnitGroupGradedZeroEquivResidueFieldUnits_mk]
  simp

/-- Computing `tameCharacter G B σ` from any uniformizer `ϖ` and `y : B` satisfying
`ϖ * y = σ • ϖ`. -/
theorem coe_tameCharacter_of_mul_eq (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (0 : ℤ))
    {y : B} (hy : ϖ * y = (σ : G) • ϖ) :
    (tameCharacter G B σ : ResidueField B) = residue B y := by
  have hy_eq : ((uniformizerRatio 0 hϖ σ : Bˣ) : B) = y :=
    mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio hϖ σ).trans hy.symm)
  rw [coe_tameCharacter hϖ, hy_eq]

/-- An element of `G_0` lies in the kernel of `tameCharacter G B` iff `σ • ϖ - ϖ ∈ 𝔪 ^ 2` for a
uniformizer `ϖ`. -/
theorem mem_ker_tameCharacter_iff (hϖ : Irreducible ϖ) {σ : ramificationGroup G B (0 : ℤ)} :
    σ ∈ (tameCharacter G B).ker ↔ (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ 2 := by
  rw [tameCharacter, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ (principalUnitGroupGradedZeroEquivResidueFieldUnits B).injective,
    ← MonoidHom.mem_ker, mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (i := 0) hϖ]

variable (G B) in
/-- The induced **graded tame character** `G_0 / G_1 →* (ResidueField B)ˣ`. -/
def tameCharacterGraded :
    RamificationGroupGraded G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits B).toMonoidHom.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded G B 0)

/-- Evaluating `tameCharacterGraded` on the class of `σ` agrees with `tameCharacter`. -/
@[simp]
theorem tameCharacterGraded_mk (σ : ramificationGroup G B (0 : ℤ)) :
    tameCharacterGraded G B (QuotientGroup.mk σ) = tameCharacter G B σ :=
  (rfl)

/-- **Conjugation equivariance of the tame character** (Serre, *Local Fields*, IV §2,
Proposition 9): conjugating `σ ∈ G_0` by `g ∈ G` acts on `tameCharacter G B σ` via the induced
action of `g` on `ResidueField B`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G B (0 : ℤ)) :
    (tameCharacter G B (MulAut.conjNormal g σ) : ResidueField B) =
      g • (tameCharacter G B σ : ResidueField B) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hgϖ : Irreducible (g⁻¹ • ϖ) := hϖ.map (MulSemiringAction.toRingAut G B g⁻¹)
  rw [coe_tameCharacter hgϖ σ, ← ResidueField.residue_smul]
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
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (x : RamificationGroupGraded G B (0 : ℤ)) :
    (tameCharacterGraded G B (ramificationGroupGradedConj G B g 0 x) : ResidueField B) =
      g • (tameCharacterGraded G B x : ResidueField B) := by
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

/-! ### Positive depth: additive residue-field coordinates -/

private def ramificationGroupGradedCongr (G B : Type*) [Group G] [CommRing B] [IsLocalRing B]
    [MulSemiringAction G B] {i j : ℤ} (h : i = j) :
    RamificationGroupGraded G B i ≃* RamificationGroupGraded G B j := by
  subst h
  exact MulEquiv.refl _

private theorem ramificationGroupGradedCongr_mk (G B : Type*) [Group G] [CommRing B]
    [IsLocalRing B] [MulSemiringAction G B] {i j : ℤ} (h : i = j)
    (σ : ramificationGroup G B i) :
    ramificationGroupGradedCongr G B h (QuotientGroup.mk σ) =
      QuotientGroup.mk ⟨(σ : G), h ▸ σ.property⟩ := by
  subst h
  rfl

variable (G B) in
/-- The positive-depth additive homomorphism `Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` in the
coordinate determined by a uniformizer `ϖ`, sending `σ` to the residue of
`(σ • ϖ - ϖ) / ϖ ^ (n + 2)`. -/
def ramificationGroupGradedToResidueField (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ) :
    Additive (RamificationGroupGraded G B ((n : ℤ) + 1)) →+ ResidueField B :=
  (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ).toAddMonoidHom.comp
    ((ramificationGroupGradedToPrincipalUnitGroupGraded G B (n + 1)).comp
      (ramificationGroupGradedCongr G B (Nat.cast_succ n).symm).toMonoidHom).toAdditive

/-- Evaluating `ramificationGroupGradedToResidueField` on the class of `τ` gives the uniformizer
coordinate of `uniformizerRatio (n + 1) hϖ τ'`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n ϖ hϖ (Additive.ofMul (QuotientGroup.mk τ)) =
      principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ
        (Additive.ofMul (QuotientGroup.mk (uniformizerRatio (n + 1) hϖ
          ⟨(τ : G), (Nat.cast_succ (R := ℤ) n).symm ▸ τ.property⟩))) := by
  rw [ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, ramificationGroupGradedCongr_mk, toMul_ofMul]
  exact congrArg (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ)
    (congrArg Additive.ofMul
      (ramificationGroupGradedToPrincipalUnitGroupGraded_mk (i := n + 1) hϖ
        ⟨(τ : G), (Nat.cast_succ (R := ℤ) n).symm ▸ τ.property⟩))

/-- Compute the positive-depth residue coordinate from `(τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) (y : B)
    (hmove : (τ : G) • ϖ - ϖ = y * ϖ ^ (n + 2)) :
    ramificationGroupGradedToResidueField G B n ϖ hϖ
        (Additive.ofMul (QuotientGroup.mk τ)) = residue B y := by
  let τ' : ramificationGroup G B ((n + 1 : ℕ) : ℤ) :=
    ⟨(τ : G), (Nat.cast_succ (R := ℤ) n).symm ▸ τ.property⟩
  have hdiff : ((uniformizerRatio (n + 1) hϖ τ' : Bˣ) : B) - 1 = y * ϖ ^ (n + 1) := by
    apply mul_left_cancel₀ hϖ.ne_zero
    calc ϖ * (((uniformizerRatio (n + 1) hϖ τ' : Bˣ) : B) - 1)
        = (τ' : G) • ϖ - ϖ := by rw [mul_sub, mul_uniformizerRatio, mul_one]
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
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply]
  exact principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_change n ϖ ϖ' hϖ hϖ' _

/-- **Conjugation action formula on positive ramification quotients** (Serre, *Local Fields*,
IV §2, Proposition 9): in the residue coordinate determined by `ϖ`, conjugation by `σ ∈ G_0` acts
on `G_{n+1} / G_{n+2}` as multiplication by `(tameCharacter G B σ) ^ (n + 1)`. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B 0) (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n ϖ hϖ
        (Additive.ofMul (ramificationGroupGradedConj G B (σ : G) ((n : ℤ) + 1) τ)) =
      (tameCharacter G B σ : ResidueField B) ^ (n + 1) *
        ramificationGroupGradedToResidueField G B n ϖ hϖ (Additive.ofMul τ) := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let ϖ' : B := g⁻¹ • ϖ
    have hϖ' : Irreducible ϖ' := hϖ.map (MulSemiringAction.toRingAut G B g⁻¹)
    have hmove : (τ : G) • ϖ' - ϖ' ∈ maximalIdeal B ^ (n + 2) :=
      mem_ramificationGroup_add_one_iff.mp τ.property ϖ'
    rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hτcoord :
        ramificationGroupGradedToResidueField G B n ϖ' hϖ'
            (Additive.ofMul (QuotientGroup.mk τ)) = residue B y :=
      ramificationGroupGradedToResidueField_of_smul_sub_eq n ϖ' hϖ' τ y hy.symm
    have hconjMove :
        ((MulAut.conjNormal g τ : ramificationGroup G B ((n : ℤ) + 1)) : G) • ϖ - ϖ =
          g • y * ϖ ^ (n + 2) := by
      calc
        _ = g • ((τ : G) • ϖ' - ϖ') := by
          simp [ϖ', MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * ϖ' ^ (n + 2)) := by rw [hy]
        _ = g • y * ϖ ^ (n + 2) := by simp [ϖ', smul_mul', smul_pow']
    have hconjCoord :=
      ramificationGroupGradedToResidueField_of_smul_sub_eq n ϖ hϖ (MulAut.conjNormal g τ)
        (g • y) hconjMove
    have hresidue : residue B (g • y) = residue B y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G B σ.property y
    set a : Bˣ := uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
    have hprodB : ((uniformizerRatio 0 hϖ σ : Bˣ) : B) * (g • (a : B)) = 1 := by
      apply mul_left_cancel₀ hϖ.ne_zero
      calc ϖ * (((uniformizerRatio 0 hϖ σ : Bˣ) : B) * (g • (a : B)))
          = (g • ϖ) * (g • (a : B)) := by rw [← mul_assoc, mul_uniformizerRatio]
        _ = g • (ϖ * (a : B)) := (smul_mul' g _ _).symm
        _ = g • ϖ' := by rw [mul_uniformizerChangeUnit]
        _ = ϖ * 1 := by simp [ϖ']
    have hprod : (tameCharacter G B σ : ResidueField B) * residue B (a : B) = 1 := by
      rw [coe_tameCharacter hϖ,
        ← residue_smul_eq_of_mem_ramificationGroup_zero G B σ.property (a : B),
        ← map_mul, hprodB, map_one]
    have hchange :=
      ramificationGroupGradedToResidueField_change n ϖ ϖ' hϖ hϖ' (QuotientGroup.mk τ)
    rw [ramificationGroupGradedConj_mk, hconjCoord, hresidue, ← hτcoord, hchange, ← mul_assoc,
      ← mul_pow, hprod, one_pow, one_mul]

end Homomorphisms

section CharZero

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

/-- In residue characteristic zero, a finite-order inertia element `σ ∈ G_0` that moves a
uniformizer `ϖ` by an element of `𝔪 ^ 2` lies in wild inertia `G_1`, with no base ring or
separability assumption. -/
theorem mem_ramificationGroup_one_of_charZero [CharZero (ResidueField B)]
    {ϖ : B} (hϖ : Irreducible ϖ) {σ : G} (hσ : σ ∈ ramificationGroup G B 0)
    (hfin : IsOfFinOrder σ) (hϖ2 : σ • ϖ - ϖ ∈ maximalIdeal B ^ 2) :
    σ ∈ ramificationGroup G B 1 := by
  have h1 : σ ∈ (maximalIdeal B ^ 2).inertia G :=
    mem_inertia_of_forall_mem_maximalIdeal_of_charZero hσ hfin fun w hw ↦
      smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer hϖ hϖ2
        (fun y ↦ by simpa only [pow_one] using mem_ramificationGroup_zero_iff.mp hσ y) hw
  simpa [ramificationGroup_def] using h1

variable (G B) in
/-- **In residue characteristic zero, the tame character is injective** whenever `G` acts faithfully
on `B` and `G_0` is finite, with no base ring or separability assumption. -/
theorem ker_tameCharacter_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    (tameCharacter G B).ker = ⊥ := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  rw [eq_bot_iff]
  intro σ hσ
  rw [mem_ker_tameCharacter_iff hϖ] at hσ
  have h1 : (σ : G) ∈ ramificationGroup G B 1 :=
    mem_ramificationGroup_one_of_charZero hϖ σ.property
      ((ramificationGroup G B 0).subtype.isOfFinOrder (isOfFinOrder_of_finite σ)) hσ
  have : Finite (ramificationGroup G B 1) :=
    Finite.of_injective
      (Subgroup.inclusion (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)))
      (Subgroup.inclusion_injective _)
  rw [ramificationGroup_one_eq_bot_of_charZero G B] at h1
  exact Subtype.ext h1

/-- **Inertia `G_0` is cyclic in residue characteristic zero**, whenever `G` acts faithfully on `B`
and `G_0` is finite, with no base ring or separability assumption. -/
theorem isCyclic_ramificationGroup_zero_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    IsCyclic (ramificationGroup G B 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacter G B))
    (Units.val_injective.comp
      ((MonoidHom.ker_eq_bot_iff _).mp (ker_tameCharacter_of_charZero G B)))

end CharZero

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
  suffices ∀ m ≤ n + 1, ∀ x : B, σ • x - x ∈ maximalIdeal B ^ m from this (n + 1) le_rfl
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    exact Ideal.mem_inertia.mp <| mem_inertia_of_forall_mem_maximalIdeal R hσ fun w hw ↦
      smul_sub_mem_maximalIdeal_pow_succ_of_uniformizer hϖ
        (Ideal.pow_le_pow_right hm hϖn) (ih (by omega)) hw

variable (G B i) in
/-- **The kernel of the `i`-th quotient homomorphism is `G_{i+1}`**, when the residue extension
over `R` is separable. -/
theorem ker_ramificationGroupToPrincipalUnitGroupGraded :
    (ramificationGroupToPrincipalUnitGroupGraded G B i).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker G B i)
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff hϖ] at hσ
  have hσ0 : (σ : G) ∈ ramificationGroup G B 0 :=
    ramificationGroup_antitone G B (Int.natCast_nonneg i) σ.property
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ hσ0]
  exact hσ

variable (G B i) in
/-- **The graded homomorphism `G_i / G_{i+1} →* PrincipalUnitGroupGraded B i` is injective**, when
the residue extension over `R` is separable. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_injective :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGroupGraded G B i) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGroupGraded G B R i).symm

variable (G B) in
/-- **The kernel of the tame character is `G_1`**, when the residue extension over `R` is
separable. -/
theorem ker_tameCharacter :
    (tameCharacter G B).ker =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  ext σ
  rw [mem_ker_tameCharacter_iff hϖ, Subgroup.mem_subgroupOf,
    ← Nat.cast_one, mem_ramificationGroup_natCast_iff_smul_sub_mem R hϖ σ.property]

variable (G B) in
/-- **The graded tame character `G_0 / G_1 →* (ResidueField B)ˣ` is injective**, when the residue
extension over `R` is separable. -/
theorem tameCharacterGraded_injective :
    Function.Injective (tameCharacterGraded G B) :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits B).injective.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded_injective G B R 0)

variable (G B) in
/-- **The positive-depth residue coordinate `Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` is
injective**, when the residue extension over `R` is separable. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (ϖ : B) (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToResidueField G B n ϖ hϖ) :=
  (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n ϖ hϖ).injective.comp
    ((ramificationGroupGradedToPrincipalUnitGroupGraded_injective G B R (n + 1)).comp
      (ramificationGroupGradedCongr G B (Nat.cast_succ n).symm).injective)

/-! ### Tame and wild structure of `G_0` and `G_1` -/

variable (G B) in
/-- Every successive quotient `G_i / G_{i+1}` (`i ≥ 0`) is commutative when the residue extension
over `R` is separable: it embeds into `PrincipalUnitGroupGraded B i`, a quotient of a subgroup of
the commutative group `Bˣ`. (For positive depth `i = n + 1`, commutativity holds without `R` or
DVR hypotheses via `TauCeti.IsLocalRing.instIsMulCommutativeRamificationGroupGradedNatCastSucc`.) -/
theorem isMulCommutative_ramificationGroupGraded (i : ℕ) :
    IsMulCommutative (RamificationGroupGraded G B (i : ℤ)) :=
  let hinj := ramificationGroupGradedToPrincipalUnitGroupGraded_injective G B R i
  IsMulCommutative.of_comm fun _ _ ↦
    hinj (by rw [map_mul, map_mul]; exact mul_comm (G := PrincipalUnitGroupGraded B i) _ _)

/-- Conjugation by an inertia element `σ ∈ G_0` acts trivially on the tame quotient `G_0 / G_1`,
when the residue extension over `R` is separable. (Not marked `@[simp]` because `R` does not
appear in the left-hand side; once `isMulCommutative_ramificationGroupGraded G B R 0` is in scope,
`TauCeti.IsLocalRing.ramificationGroupGradedConj_self` simplifies this automatically.) -/
theorem ramificationGroupGradedConj_zero (σ : ramificationGroup G B 0)
    (τ : RamificationGroupGraded G B (0 : ℤ)) :
    ramificationGroupGradedConj G B (σ : G) 0 τ = τ := by
  have := isMulCommutative_ramificationGroupGraded G B R 0
  exact ramificationGroupGradedConj_self G B 0 σ τ

variable (G B) in
/-- **The tame quotient `G_0 / G_1` is cyclic** whenever `G_0 / G_1` is finite and the residue
extension over `R` is separable, with no finiteness assumption on `G_0` or `ResidueField B`. -/
theorem isCyclic_ramificationGroupGraded_zero [Finite (RamificationGroupGraded G B (0 : ℤ))] :
    IsCyclic (RamificationGroupGraded G B (0 : ℤ)) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacterGraded G B))
    (Units.val_injective.comp (tameCharacterGraded_injective G B R))

variable (G B) in
/-- **The index of `G_1` in `G_0` is prime to `p`** when `ResidueField B` has prime characteristic
`p`, `G_0 / G_1` is finite, and the residue extension over `R` is separable: `(ResidueField B)ˣ`
contains no element of order `p`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [Finite (RamificationGroupGraded G B (0 : ℤ))] :
    ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index := by
  have hφ := tameCharacterGraded_injective G B R
  intro hp
  have hp_card : p ∣ Nat.card (RamificationGroupGraded G B 0) := by
    rwa [RamificationGroupGraded, zero_add, ← Subgroup.index_eq_card]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp_card
  have hord : orderOf ((tameCharacterGraded G B x : (ResidueField B)ˣ) : ResidueField B) = p := by
    rw [orderOf_units, orderOf_injective _ hφ x, hx]
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hroot := hord ▸
    IsPrimitiveRoot.orderOf ((tameCharacterGraded G B x : (ResidueField B)ˣ) : ResidueField B)
  exact hroot.neZero'.out (CharP.cast_eq_zero _ p)

end Separable

section Sylow

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [IsDomain B]
  [_root_.IsDiscreteValuationRing B] [MulSemiringAction G B]

variable (G B) in
/-- **Wild inertia `G_1` as a Sylow `p`-subgroup of inertia `G_0`**, for a faithful action with
finite `G_0` in prime residue characteristic `p` whenever the index `[G_0 : G_1]` is prime to
`p`. -/
def ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (hp : ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index) :
    Sylow p (ramificationGroup G B 0) :=
  have : Finite (ramificationGroup G B 1) :=
    Finite.of_injective
      (Subgroup.inclusion (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)))
      (Subgroup.inclusion_injective _)
  ((isPGroup_ramificationGroup G B p (i := 1) (by omega)).comap_subtype).toSylow hp

/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` viewed inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (hp : ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index) :
    (ramificationGroupOneSylow G B p hp : Subgroup (ramificationGroup G B 0)) =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) :=
  (rfl)

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (hp : ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index) :
    (ramificationGroupOneSylow G B p hp : Subgroup (ramificationGroup G B 0)).Normal :=
  ramificationGroupOneSylow_coe p hp ▸ inferInstance

/-- `ramificationGroupOneSylow` is the unique Sylow `p`-subgroup of `G_0`. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (hp : ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index)
    (Q : Sylow p (ramificationGroup G B 0)) :
    Q = ramificationGroupOneSylow G B p hp := by
  let _ : Unique (Sylow p (ramificationGroup G B 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow G B p hp)
      (ramificationGroupOneSylow_normal p hp)
  exact Subsingleton.elim _ _

/-- The order of wild inertia `G_1` is the `p`-part of the order of inertia `G_0`, for a faithful
action with finite `G_0` in prime residue characteristic `p` when `[G_0 : G_1]` is prime to `p`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (hp : ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index) :
    Nat.card (ramificationGroup G B 1) =
      p ^ (Nat.card (ramificationGroup G B 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow G B p hp)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`**, for a faithful action
with finite `G_0` in prime residue characteristic `p` when `[G_0 : G_1]` is prime to `p`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField B) p] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)]
    (hp : ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index) :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  have hp' : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one p hp,
    pow_eq_one_iff_right hp'.ne_one, Nat.factorization_eq_zero_iff]
  simp only [hp', not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

end Sylow

end IsDiscreteValuationRing

end TauCeti
