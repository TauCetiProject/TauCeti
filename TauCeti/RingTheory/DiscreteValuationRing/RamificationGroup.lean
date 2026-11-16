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
import Mathlib.FieldTheory.Finite.Basic
import TauCeti.GroupTheory.PGroup

/-!
# Graded embeddings of the lower ramification filtration over a discrete valuation ring

Let a group `G` act by ring automorphisms on a discrete valuation ring `S` with maximal ideal `𝔪`
and residue field `κ`, and write `G_i = TauCeti.IsLocalRing.ramificationGroup G S i` for its lower
ramification filtration. No completeness of `S` and no finiteness of `κ` is assumed.

Fixing a uniformizer `ϖ` of `S`, every `σ ∈ G` carries `ϖ` to another uniformizer `σ • ϖ`, so
`ϖ * u = σ • ϖ` for a unique unit `u = uniformizerRatio ϖ hϖ σ : Sˣ`. When `σ ∈ G_i` (`i : ℕ`),
this unit lies in the `i`-th principal-unit subgroup `1 + 𝔪 ^ i`, and its class in the graded
piece `PrincipalUnitGraded S i = (1 + 𝔪 ^ i) ⧸ (1 + 𝔪 ^ (i + 1))`

* is independent of the choice of uniformizer `ϖ`,
* is multiplicative in `σ`, and
* kills `G_{i+1}`,

giving canonical homomorphisms `ramificationGroupToPrincipalUnitGraded G S i : G_i →*
PrincipalUnitGraded S i` and `ramificationGroupGradedToPrincipalUnitGraded G S i :
G_i / G_{i+1} →* PrincipalUnitGraded S i` whose signatures do not mention a uniformizer.

Composing at depth `0` with `PrincipalUnitGraded S 0 ≃* κˣ` gives the canonical **tame character**
`tameCharacter G S : G_0 →* κˣ` and its descent `tameCharacterGraded G S : G_0 / G_1 →* κˣ`. At
positive depth `n + 1`, composing with the uniformizer coordinate
`principalUnitGradedSuccEquivResidueFieldOfUniformizer n π hπ` gives the additive map
`ramificationGroupGradedToResidueField G S n π hπ : Additive (G_{n+1} / G_{n+2}) →+ κ`, together
with its change-of-uniformizer and conjugation formulas.

Even without any base ring or separability assumption on `κ`, the kernel of `tameCharacter G S`
moves every element of `𝔪` by an element of `𝔪 ^ 2`; combining this with the general local-ring
filtration theory in `TauCeti/RingTheory/LocalRing/RamificationGroup.lean` yields solvability of
`G_i` (`i ≥ 0`), cyclicity of `G_0` in residue characteristic zero or when the residue
characteristic does not divide `#G_0`, and the divisibility `#(G_0 / G_1) ∣ #κ - 1`.

When `S` is an algebra over a local ring `R` fixed by `G` such that `algebraMap R S` is local and
the residue extension `κ / ResidueField R` is separable, membership of an element of `G_i` in
`G_{i+1}` is decided at a uniformizer
(`TauCeti.IsLocalRing.mem_ramificationGroup_succ_iff_of_irreducible`),
so all of the graded maps are **injective**. From those embeddings follow the tame/wild
splitting theorems without residue finiteness:

* every graded piece `G_i / G_{i+1}` (`i ≥ 0`) is commutative;
* when `G_0 / G_1` is finite, it is cyclic of order not divisible by the residue characteristic;
* in positive residue characteristic `p`, for a faithful action with finite `G_0`, wild inertia
  `G_1` is the unique normal Sylow `p`-subgroup of `G_0`, and `G_1 = ⊥` if and only if `p ∤ #G_0`.

The positive-depth coordinate, conjugation equivariance, and wild-inertia Sylow constructions here
adapt the nonarchimedean local-field formalizations in
`TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean` and
`TauCeti/NumberTheory/LocalField/UnitFiltration/Conjugation.lean` (where `κ` is finite and
Teichmüller lifts replace the separable-residue hypothesis).

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u : Sˣ` with `ϖ * u = σ • ϖ`.
* `TauCeti.IsDiscreteValuationRing.principalUnitUniformizerRatio`: `uniformizerRatio` bundled in
  `(maximalIdeal S ^ i).principalUnitGroup` for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded`: the canonical
  uniformizer-independent homomorphisms from `G_i` and `G_i / G_{i+1}` to `PrincipalUnitGraded S i`.
* `TauCeti.IsDiscreteValuationRing.tameCharacter` and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded`: the canonical tame character `G_0 →* κˣ`
  and its descent `G_0 / G_1 →* κˣ`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField`: the positive-depth
  homomorphism `Additive (G_{n+1} / G_{n+2}) →+ κ` attached to a uniformizer `π`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`: wild inertia `G_1` as a Sylow
  `p`-subgroup of inertia `G_0` in positive residue characteristic `p`.

## Main results

* `TauCeti.IsDiscreteValuationRing.tameCharacter_conj`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_ramificationGroupGradedConj`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_conj`: conjugation
  equivariance of the tame character and positive-depth residue coordinates.
* `TauCeti.IsDiscreteValuationRing.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one`,
  `TauCeti.IsDiscreteValuationRing.isSolvable_ramificationGroup`,
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`, and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_not_dvd_card`: divisibility,
  solvability, and cyclicity of inertia without a base ring or separability assumption.
* `TauCeti.IsDiscreteValuationRing.ker_ramificationGroupToPrincipalUnitGraded`,
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective`: exactness of
  the kernels and injectivity of the graded maps over a separable residue extension.
* `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one`: `G_0 / G_1` is cyclic of
  order prime to the residue characteristic over a separable residue extension.
* `TauCeti.IsDiscreteValuationRing.eq_ramificationGroupOneSylow` and
  `ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero`: wild inertia `G_1` as
  the unique normal Sylow `p`-subgroup of `G_0`, and the unified criterion for `G_1 = ⊥`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §§1–2, Propositions 2, 5, 7, and 9, and
  Corollaries 1–5.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math.
  France **89** (1961), 105–154, n° 3.1, Proposition 1 and Corollaries 1–2.
-/

public section
noncomputable section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

section UniformizerRatio

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsDomain S]
  [_root_.IsDiscreteValuationRing S] [MulSemiringAction G S]

/-- The unique unit `u : Sˣ` satisfying `ϖ * u = σ • ϖ`, for a uniformizer `ϖ` of `S` and `σ : G`.
In the fraction field of `S` this unit represents `σ(ϖ) / ϖ`. -/
def uniformizerRatio (ϖ : S) (hϖ : Irreducible ϖ) (σ : G) : Sˣ :=
  TauCeti.uniformizerChangeUnit ϖ (σ • ϖ) hϖ (hϖ.map (MulSemiringAction.toRingAut G S σ).toMulEquiv)

/-- Multiplying `ϖ` on the right by `uniformizerRatio ϖ hϖ σ` gives `σ • ϖ`. -/
@[simp]
theorem mul_uniformizerRatio (ϖ : S) (hϖ : Irreducible ϖ) (σ : G) :
    ϖ * (uniformizerRatio ϖ hϖ σ : S) = σ • ϖ :=
  TauCeti.mul_uniformizerChangeUnit ϖ (σ • ϖ) hϖ
    (hϖ.map (MulSemiringAction.toRingAut G S σ).toMulEquiv)

/-- Multiplying `ϖ` on the left by `uniformizerRatio ϖ hϖ σ` gives `σ • ϖ`. -/
@[simp]
theorem uniformizerRatio_mul_self (ϖ : S) (hϖ : Irreducible ϖ) (σ : G) :
    (uniformizerRatio ϖ hϖ σ : S) * ϖ = σ • ϖ := by
  rw [mul_comm, mul_uniformizerRatio]

/-- Characterization of `uniformizerRatio ϖ hϖ σ` by its defining product relation. -/
theorem uniformizerRatio_eq_iff (ϖ : S) (hϖ : Irreducible ϖ) (σ : G) {u : Sˣ} :
    uniformizerRatio ϖ hϖ σ = u ↔ ϖ * (u : S) = σ • ϖ := by
  refine ⟨fun h ↦ h ▸ mul_uniformizerRatio ϖ hϖ σ, fun h ↦ Units.ext ?_⟩
  exact mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio ϖ hϖ σ).trans h.symm)

/-- The identity automorphism has uniformizer ratio `1`. -/
@[simp]
theorem uniformizerRatio_one (ϖ : S) (hϖ : Irreducible ϖ) :
    uniformizerRatio ϖ hϖ (1 : G) = 1 :=
  (uniformizerRatio_eq_iff ϖ hϖ 1).mpr (by simp)

/-- **1-cocycle identity** for `uniformizerRatio`: the ratio of `σ * τ` is the ratio of `σ` times
the `σ`-translate of the ratio of `τ`. -/
theorem uniformizerRatio_mul (ϖ : S) (hϖ : Irreducible ϖ) (σ τ : G) :
    uniformizerRatio ϖ hϖ (σ * τ) =
      uniformizerRatio ϖ hϖ σ *
        Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom (uniformizerRatio ϖ hϖ τ) := by
  rw [uniformizerRatio_eq_iff]
  simp [← mul_assoc, ← smul_mul', mul_smul]

/-- Replacing `ϖ` by `ϖ' = ϖ * a` multiplies `uniformizerRatio` by the coboundary
`(σ • a) * a⁻¹`. -/
theorem uniformizerRatio_change (ϖ ϖ' : S) (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') (σ : G) :
    uniformizerRatio ϖ' hϖ' σ =
      uniformizerRatio ϖ hϖ σ *
        (Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom
          (TauCeti.uniformizerChangeUnit ϖ ϖ' hϖ hϖ') *
          (TauCeti.uniformizerChangeUnit ϖ ϖ' hϖ hϖ')⁻¹) := by
  set a := TauCeti.uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have ha : ϖ * (a : S) = ϖ' := TauCeti.mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  apply Units.ext
  apply mul_left_cancel₀ hϖ'.ne_zero
  calc
    ϖ' * (uniformizerRatio ϖ' hϖ' σ : S) = σ • ϖ' := mul_uniformizerRatio ϖ' hϖ' σ
    _ = σ • (ϖ * (a : S)) := by rw [ha]
    _ = ϖ * (uniformizerRatio ϖ hϖ σ : S) * (σ • (a : S)) * ((a : S) * ↑a⁻¹) := by
      rw [smul_mul', mul_uniformizerRatio, a.mul_inv, mul_one]
    _ = ϖ' * ↑(uniformizerRatio ϖ hϖ σ *
          (Units.map (MulSemiringAction.toRingHom G S σ).toMonoidHom a * a⁻¹)) := by
      rw [← ha]
      simp [-mul_uniformizerRatio, -uniformizerRatio_mul_self, -Units.mul_inv]
      ring

/-- The uniformizer ratio lies in `1 + 𝔪 ^ i` if and only if `σ` moves `ϖ` by an element of
`𝔪 ^ (i + 1)`. -/
theorem uniformizerRatio_mem_principalUnitGroup_pow_iff (i : ℕ) (ϖ : S) (hϖ : Irreducible ϖ)
    (σ : G) :
    uniformizerRatio ϖ hϖ σ ∈ (maximalIdeal S ^ i).principalUnitGroup ↔
      σ • ϖ - ϖ ∈ maximalIdeal S ^ (i + 1) := by
  have hsub : ((uniformizerRatio ϖ hϖ σ : S) - 1) * ϖ = σ • ϖ - ϖ := by
    rw [sub_mul, one_mul, uniformizerRatio_mul_self]
  rw [Ideal.mem_principalUnitGroup, ← hsub, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ,
    mul_dvd_mul_iff_right hϖ.ne_zero]

/-- For `σ ∈ G_i` (`i : ℕ`), the uniformizer ratio lies in `1 + 𝔪 ^ i`. -/
theorem uniformizerRatio_mem_principalUnitGroup_pow {i : ℕ} (ϖ : S) (hϖ : Irreducible ϖ) {σ : G}
    (hσ : σ ∈ ramificationGroup G S (i : ℤ)) :
    uniformizerRatio ϖ hϖ σ ∈ (maximalIdeal S ^ i).principalUnitGroup :=
  (uniformizerRatio_mem_principalUnitGroup_pow_iff i ϖ hϖ σ).mpr
    (mem_ramificationGroup_natCast_iff.mp hσ ϖ)

/-- The uniformizer ratio of `σ ∈ G_i` bundled in `(maximalIdeal S ^ i).principalUnitGroup`. -/
def principalUnitUniformizerRatio (i : ℕ) (ϖ : S) (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S (i : ℤ)) : (maximalIdeal S ^ i).principalUnitGroup :=
  ⟨uniformizerRatio ϖ hϖ (σ : G), uniformizerRatio_mem_principalUnitGroup_pow ϖ hϖ σ.2⟩

@[simp]
theorem coe_principalUnitUniformizerRatio (i : ℕ) (ϖ : S) (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S (i : ℤ)) :
    (principalUnitUniformizerRatio i ϖ hϖ σ : Sˣ) = uniformizerRatio ϖ hϖ (σ : G) :=
  (rfl)

@[simp]
theorem principalUnitUniformizerRatio_one (i : ℕ) (ϖ : S) (hϖ : Irreducible ϖ) :
    principalUnitUniformizerRatio (G := G) i ϖ hϖ 1 = 1 :=
  Subtype.ext (uniformizerRatio_one ϖ hϖ)

/-! ### Canonical graded homomorphisms -/

/-- Auxiliary uniformizer-indexed homomorphism `G_i →* PrincipalUnitGraded S i`, shown immediately
below to be independent of the uniformizer and repackaged canonically as
`ramificationGroupToPrincipalUnitGraded`. -/
private def ramificationGroupToPrincipalUnitGradedAux (i : ℕ) (ϖ : S) (hϖ : Irreducible ϖ) :
    ramificationGroup G S (i : ℤ) →* PrincipalUnitGraded S i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (principalUnitUniformizerRatio i ϖ hϖ σ)) fun σ τ ↦ by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hmul :
        (((principalUnitUniformizerRatio i ϖ hϖ (σ * τ))⁻¹ *
            (principalUnitUniformizerRatio i ϖ hϖ σ *
              principalUnitUniformizerRatio i ϖ hϖ τ) :
            (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) =
          (Units.map (MulSemiringAction.toRingHom G S (σ : G)).toMonoidHom
            (uniformizerRatio ϖ hϖ (τ : G)) * (uniformizerRatio ϖ hϖ (τ : G))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_principalUnitUniformizerRatio,
        uniformizerRatio_mul, mul_inv_rev, inv_inv]
      rw [mul_assoc, inv_mul_cancel_left, mul_comm]
    rw [hmul, Subgroup.inv_mem_iff]
    exact unitsMap_mul_inv_mem_principalUnitGroup_pow_succ σ.2 (uniformizerRatio ϖ hϖ (τ : G))

private theorem ramificationGroupToPrincipalUnitGradedAux_apply (i : ℕ) (ϖ : S)
    (hϖ : Irreducible ϖ) (σ : ramificationGroup G S (i : ℤ)) :
    ramificationGroupToPrincipalUnitGradedAux i ϖ hϖ σ =
      QuotientGroup.mk (principalUnitUniformizerRatio i ϖ hϖ σ) :=
  congrFun (MonoidHom.mk'_apply _ _) σ

private theorem ramificationGroupToPrincipalUnitGradedAux_eq (i : ℕ) {ϖ ϖ' : S}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToPrincipalUnitGradedAux (G := G) i ϖ hϖ =
      ramificationGroupToPrincipalUnitGradedAux (G := G) i ϖ' hϖ' := by
  ext σ
  rw [ramificationGroupToPrincipalUnitGradedAux_apply,
    ramificationGroupToPrincipalUnitGradedAux_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  set a := TauCeti.uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have hchange :
      (((principalUnitUniformizerRatio i ϖ hϖ σ)⁻¹ *
          principalUnitUniformizerRatio i ϖ' hϖ' σ :
          (maximalIdeal S ^ i).principalUnitGroup) : Sˣ) =
        Units.map (MulSemiringAction.toRingHom G S (σ : G)).toMonoidHom a * a⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_principalUnitUniformizerRatio,
      coe_principalUnitUniformizerRatio, uniformizerRatio_change ϖ ϖ' hϖ hϖ' (σ : G),
      inv_mul_cancel_left]
  rw [hchange]
  exact unitsMap_mul_inv_mem_principalUnitGroup_pow_succ σ.2 a

variable (G S) in
/-- The canonical homomorphism `G_i →* (1 + 𝔪 ^ i) ⧸ (1 + 𝔪 ^ (i + 1))` sending `σ ∈ G_i` to the
class of `uniformizerRatio ϖ hϖ σ` for any uniformizer `ϖ` of `S`. Its value at every uniformizer
is given by `ramificationGroupToPrincipalUnitGraded_apply_of_irreducible`. -/
def ramificationGroupToPrincipalUnitGraded (i : ℕ) :
    ramificationGroup G S (i : ℤ) →* PrincipalUnitGraded S i :=
  ramificationGroupToPrincipalUnitGradedAux i
    (_root_.IsDiscreteValuationRing.exists_irreducible S).choose
    (_root_.IsDiscreteValuationRing.exists_irreducible S).choose_spec

/-- On any uniformizer `ϖ` of `S`, `ramificationGroupToPrincipalUnitGraded G S i` sends `σ ∈ G_i`
to the class of `principalUnitUniformizerRatio i ϖ hϖ σ`. -/
theorem ramificationGroupToPrincipalUnitGraded_apply_of_irreducible (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (σ : ramificationGroup G S (i : ℤ)) :
    ramificationGroupToPrincipalUnitGraded G S i σ =
      QuotientGroup.mk (principalUnitUniformizerRatio i ϖ hϖ σ) := by
  rw [ramificationGroupToPrincipalUnitGraded,
    ramificationGroupToPrincipalUnitGradedAux_eq i _ hϖ,
    ramificationGroupToPrincipalUnitGradedAux_apply]

/-- An element `σ ∈ G_i` lies in the kernel of `ramificationGroupToPrincipalUnitGraded G S i` if
and only if it moves a chosen uniformizer `ϖ` by an element of `𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGraded_iff_of_irreducible {i : ℕ} {ϖ : S}
    (hϖ : Irreducible ϖ) {σ : ramificationGroup G S (i : ℤ)} :
    σ ∈ (ramificationGroupToPrincipalUnitGraded G S i).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal S ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGraded_apply_of_irreducible i hϖ,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, coe_principalUnitUniformizerRatio,
    uniformizerRatio_mem_principalUnitGroup_pow_iff]

variable (G S) in
/-- The next ramification group `G_{i+1}` always lies in the kernel of
`ramificationGroupToPrincipalUnitGraded G S i`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker_ramificationGroupToPrincipalUnitGraded (i : ℕ) :
    (ramificationGroup G S ((i : ℤ) + 1)).subgroupOf (ramificationGroup G S (i : ℤ)) ≤
      (ramificationGroupToPrincipalUnitGraded G S i).ker := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  intro σ hσ
  rw [mem_ker_ramificationGroupToPrincipalUnitGraded_iff_of_irreducible hϖ]
  have hσ' : (σ : G) ∈ ramificationGroup G S ((i + 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Subgroup.mem_subgroupOf.mp hσ
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

variable (G S) in
/-- The canonical graded homomorphism `θ_i : G_i / G_{i+1} →* (1 + 𝔪 ^ i) ⧸ (1 + 𝔪 ^ (i + 1))`
induced by `ramificationGroupToPrincipalUnitGraded`. Over a separable residue extension it is
injective (`ramificationGroupGradedToPrincipalUnitGraded_injective`). -/
def ramificationGroupGradedToPrincipalUnitGraded (i : ℕ) :
    RamificationGroupGraded G S (i : ℤ) →* PrincipalUnitGraded S i :=
  QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGraded G S i)
    (ramificationGroup_succ_subgroupOf_le_ker_ramificationGroupToPrincipalUnitGraded G S i)

@[simp]
theorem ramificationGroupGradedToPrincipalUnitGraded_mk (i : ℕ)
    (σ : ramificationGroup G S (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGraded G S i (QuotientGroup.mk σ) =
      ramificationGroupToPrincipalUnitGraded G S i σ :=
  (rfl)

/-- Explicit value of `ramificationGroupGradedToPrincipalUnitGraded` on a class in `G_i / G_{i+1}`
in terms of any uniformizer `ϖ`. -/
theorem ramificationGroupGradedToPrincipalUnitGraded_mk_of_irreducible (i : ℕ) {ϖ : S}
    (hϖ : Irreducible ϖ) (σ : ramificationGroup G S (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGraded G S i (QuotientGroup.mk σ) =
      QuotientGroup.mk (principalUnitUniformizerRatio i ϖ hϖ σ) :=
  ramificationGroupToPrincipalUnitGraded_apply_of_irreducible i hϖ σ

/-! ### The tame character and positive-depth residue coordinates -/

variable (G S) in
/-- The canonical **tame character** `θ_0 : G_0 →* (ResidueField S)ˣ`, sending `σ ∈ G_0` to the
residue of `uniformizerRatio ϖ hϖ σ` for any uniformizer `ϖ` of `S`. -/
def tameCharacter : ramificationGroup G S 0 →* (ResidueField S)ˣ :=
  (principalUnitGradedZeroEquivResidueFieldUnits S).toMonoidHom.comp
    (ramificationGroupToPrincipalUnitGraded G S 0)

variable (G S) in
/-- Defining factorization of `tameCharacter` through `PrincipalUnitGraded S 0`. -/
theorem tameCharacter_def :
    tameCharacter G S =
      (principalUnitGradedZeroEquivResidueFieldUnits S).toMonoidHom.comp
        (ramificationGroupToPrincipalUnitGraded G S 0) :=
  (rfl)

/-- At any uniformizer `ϖ`, the tame character reduces `uniformizerRatio ϖ hϖ σ` modulo `𝔪`. -/
theorem tameCharacter_apply_of_irreducible {ϖ : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S 0) :
    tameCharacter G S σ =
      Units.map (residue S).toMonoidHom (uniformizerRatio ϖ hϖ (σ : G)) := by
  rw [tameCharacter_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGraded_apply_of_irreducible 0 hϖ,
    principalUnitGradedZeroEquivResidueFieldUnits_mk, coe_principalUnitUniformizerRatio]

/-- If `ϖ * y = σ • ϖ` for a uniformizer `ϖ`, the tame character of `σ ∈ G_0` has underlying
residue-field element `residue S y`. -/
theorem coe_tameCharacter_of_mul_eq_smul {ϖ y : S} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G S 0) (hy : ϖ * y = (σ : G) • ϖ) :
    (tameCharacter G S σ : ResidueField S) = residue S y := by
  rw [tameCharacter_apply_of_irreducible hϖ]
  simpa using congrArg (residue S)
    (mul_left_cancel₀ hϖ.ne_zero ((mul_uniformizerRatio ϖ hϖ (σ : G)).trans hy.symm))

/-- An element `σ ∈ G_0` lies in the kernel of `tameCharacter` if and only if it moves a chosen
uniformizer `ϖ` by an element of `𝔪 ^ 2`. -/
theorem mem_ker_tameCharacter_iff_of_irreducible {ϖ : S} (hϖ : Irreducible ϖ)
    {σ : ramificationGroup G S 0} :
    σ ∈ (tameCharacter G S).ker ↔ (σ : G) • ϖ - ϖ ∈ maximalIdeal S ^ 2 := by
  rw [tameCharacter_def, MulEquiv.toMonoidHom_eq_coe, MonoidHom.ker_mulEquiv_comp,
    mem_ker_ramificationGroupToPrincipalUnitGraded_iff_of_irreducible hϖ, zero_add]

variable (G S) in
/-- Wild inertia `G_1` always lies in the kernel of `tameCharacter`. -/
theorem ramificationGroup_one_subgroupOf_le_ker_tameCharacter :
    (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) ≤
      (tameCharacter G S).ker := by
  intro σ hσ
  rw [tameCharacter_def, MulEquiv.toMonoidHom_eq_coe, MonoidHom.ker_mulEquiv_comp]
  exact ramificationGroup_succ_subgroupOf_le_ker_ramificationGroupToPrincipalUnitGraded G S 0
    (by simpa only [Subgroup.mem_subgroupOf, Nat.cast_zero, zero_add] using hσ)

variable (G S) in
/-- The canonical **graded tame character** `G_0 / G_1 →* (ResidueField S)ˣ`. Over a separable
residue extension it is injective (`tameCharacterGraded_injective`). -/
def tameCharacterGraded : RamificationGroupGraded G S 0 →* (ResidueField S)ˣ :=
  (principalUnitGradedZeroEquivResidueFieldUnits S).toMonoidHom.comp
    (ramificationGroupGradedToPrincipalUnitGraded G S 0)

variable (G S) in
/-- Defining factorization of `tameCharacterGraded` through `PrincipalUnitGraded S 0`. -/
theorem tameCharacterGraded_def :
    tameCharacterGraded G S =
      (principalUnitGradedZeroEquivResidueFieldUnits S).toMonoidHom.comp
        (ramificationGroupGradedToPrincipalUnitGraded G S 0) :=
  (rfl)

@[simp]
theorem tameCharacterGraded_mk (σ : ramificationGroup G S 0) :
    tameCharacterGraded G S (QuotientGroup.mk σ) = tameCharacter G S σ :=
  (rfl)

private def ramificationGroupGradedSuccCastEquiv (n : ℕ) :
    RamificationGroupGraded G S ((n : ℤ) + 1) ≃*
      RamificationGroupGraded G S ((n + 1 : ℕ) : ℤ) :=
  QuotientGroup.equivQuotientSubgroupOfOfEq
    (congrArg (ramificationGroup G S) (by push_cast; rfl))
    (congrArg (ramificationGroup G S) (by push_cast; rfl))

private theorem ramificationGroupGradedSuccCastEquiv_mk (n : ℕ)
    (τ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupGradedSuccCastEquiv (G := G) (S := S) n
        (QuotientGroup.mk τ : RamificationGroupGraded G S ((n : ℤ) + 1)) =
      (QuotientGroup.mk ⟨(τ : G), by simpa only [Nat.cast_add, Nat.cast_one] using τ.2⟩ :
        RamificationGroupGraded G S ((n + 1 : ℕ) : ℤ)) := by
  simp only [ramificationGroupGradedSuccCastEquiv, QuotientGroup.equivQuotientSubgroupOfOfEq,
    MonoidHom.toMulEquiv_apply, QuotientGroup.quotientMapSubgroupOfOfLe_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext (Subgroup.coe_inclusion _ τ))

variable (G S) in
/-- The positive-depth graded homomorphism `Additive (G_{n+1} / G_{n+2}) →+ ResidueField S` in the
coordinate determined by a uniformizer `π` of `S`, sending the class of `τ ∈ G_{n+1}` to the
residue of `(τ • π - π) / π ^ (n + 2)`. -/
def ramificationGroupGradedToResidueField (n : ℕ) (π : S) (hπ : Irreducible π) :
    Additive (RamificationGroupGraded G S ((n : ℤ) + 1)) →+ ResidueField S :=
  (TauCeti.principalUnitGradedSuccEquivResidueFieldOfUniformizer n π hπ).toAddMonoidHom.comp <|
    ((ramificationGroupGradedToPrincipalUnitGraded G S (n + 1)).comp
      (ramificationGroupGradedSuccCastEquiv (G := G) (S := S) n).toMonoidHom).toAdditive

@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (π : S) (hπ : Irreducible π)
    (τ : ramificationGroup G S ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G S n π hπ (Additive.ofMul (QuotientGroup.mk τ)) =
      TauCeti.principalUnitGradedSuccEquivResidueFieldOfUniformizer n π hπ
        (Additive.ofMul
          (QuotientGroup.mk (principalUnitUniformizerRatio (n + 1) π hπ
            ⟨(τ : G), by simpa only [Nat.cast_add, Nat.cast_one] using τ.2⟩))) := by
  simp only [ramificationGroupGradedToResidueField, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [ramificationGroupGradedSuccCastEquiv_mk,
    ramificationGroupGradedToPrincipalUnitGraded_mk_of_irreducible (n + 1) hπ]

/-- If `(τ : G) • π - π = y * π ^ (n + 2)` for `τ ∈ G_{n+1}`, then the positive-depth residue
coordinate of `τ` with respect to `π` is `residue S y`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) (π : S) (hπ : Irreducible π)
    (τ : ramificationGroup G S ((n : ℤ) + 1)) (y : S)
    (hmove : (τ : G) • π - π = y * π ^ (n + 2)) :
    ramificationGroupGradedToResidueField G S n π hπ (Additive.ofMul (QuotientGroup.mk τ)) =
      residue S y := by
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  refine TauCeti.principalUnitGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue
    n π hπ _ y ?_
  apply mul_left_cancel₀ hπ.ne_zero
  calc
    π * (((principalUnitUniformizerRatio (n + 1) π hπ
          ⟨(τ : G), by simpa only [Nat.cast_add, Nat.cast_one] using τ.2⟩ : Sˣ) : S) - 1) =
        (τ : G) • π - π := by
      rw [coe_principalUnitUniformizerRatio, mul_sub, mul_one, mul_uniformizerRatio]
    _ = y * π ^ (n + 2) := hmove
    _ = π * (y * π ^ (n + 1)) := by ring

/-- When `π' = π * a`, the positive-depth residue coordinate on `G_{n+1} / G_{n+2}` relative to
`π` equals `residue S a ^ (n + 1)` times the coordinate relative to `π'` (so replacing `π` by
`π'` divides the coordinate by `residue S a ^ (n + 1)`). -/
theorem ramificationGroupGradedToResidueField_change (n : ℕ) (π π' : S) (hπ : Irreducible π)
    (hπ' : Irreducible π') (τ : RamificationGroupGraded G S ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G S n π hπ (Additive.ofMul τ) =
      residue S (TauCeti.uniformizerChangeUnit π π' hπ hπ' : S) ^ (n + 1) *
        ramificationGroupGradedToResidueField G S n π' hπ' (Additive.ofMul τ) := by
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.coe_toAddMonoidHom]
  exact TauCeti.principalUnitGradedSuccEquivResidueFieldOfUniformizer_change n π π' hπ hπ' _

/-! ### Conjugation on the graded homomorphisms -/

/-- **Equivariance of the tame character.** Conjugating `σ ∈ G_0` by `g ∈ G` acts on the tame
character via the residue-field automorphism induced by `g`:
`θ_0(g σ g⁻¹) = g • θ_0(σ)`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G S 0) :
    (tameCharacter G S (MulAut.conjNormal g σ) : ResidueField S) =
      g • (tameCharacter G S σ : ResidueField S) := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  set u : S := (uniformizerRatio π hπ (σ : G) : S)
  have hu : π * u = (σ : G) • π := mul_uniformizerRatio π hπ (σ : G)
  have hgu : (g • π) * (g • u) = (MulAut.conjNormal g σ : G) • (g • π) := by
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_smul, ← hu, smul_mul']
  rw [coe_tameCharacter_of_mul_eq_smul (hπ.map (MulSemiringAction.toRingAut G S g).toMulEquiv)
      (MulAut.conjNormal g σ) hgu,
    coe_tameCharacter_of_mul_eq_smul hπ σ hu, ResidueField.residue_smul]

/-- If `g ∈ G` acts on the residue field as the `q`-th power map, then
`θ_0(g σ g⁻¹) = θ_0(σ) ^ q` for every `σ ∈ G_0`. -/
theorem tameCharacter_conj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField S, g • x = x ^ q) (σ : ramificationGroup G S 0) :
    tameCharacter G S (MulAut.conjNormal g σ) = tameCharacter G S σ ^ q :=
  Units.ext (by rw [tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

/-- Equivariance of the graded tame character under conjugation by `G` on `G_0 / G_1`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (τ : RamificationGroupGraded G S 0) :
    (tameCharacterGraded G S (ramificationGroupGradedConj G S g 0 τ) : ResidueField S) =
      g • (tameCharacterGraded G S τ : ResidueField S) := by
  induction τ using QuotientGroup.induction_on with
  | _ σ => rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

/-- Power-map twist of the graded tame character on `G_0 / G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField S, g • x = x ^ q) (τ : RamificationGroupGraded G S 0) :
    tameCharacterGraded G S (ramificationGroupGradedConj G S g 0 τ) =
      tameCharacterGraded G S τ ^ q :=
  Units.ext (by rw [tameCharacterGraded_ramificationGroupGradedConj, hg, Units.val_pow_eq_pow_val])

/-- **Conjugation on positive-depth ramification quotients.** In the residue coordinate determined
by a uniformizer `π`, conjugation by an inertia element `σ ∈ G_0` acts on `G_{n+1} / G_{n+2}` as
multiplication by `θ_0(σ) ^ (n + 1)` (Serre, *Local Fields*, Chapter IV, §2, Proposition 9). -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) (π : S) (hπ : Irreducible π)
    (σ : ramificationGroup G S 0) (τ : RamificationGroupGraded G S ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G S n π hπ
        (Additive.ofMul (ramificationGroupGradedConj G S (σ : G) ((n : ℤ) + 1) τ)) =
      (tameCharacter G S σ : ResidueField S) ^ (n + 1) *
        ramificationGroupGradedToResidueField G S n π hπ (Additive.ofMul τ) := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let π' : S := (σ : G)⁻¹ • π
    have hπ' : Irreducible π' := hπ.map (MulSemiringAction.toRingAut G S (σ : G)⁻¹).toMulEquiv
    have hτ' : (τ : G) ∈ ramificationGroup G S ((n + 1 : ℕ) : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using τ.2
    have hmove : (τ : G) • π' - π' ∈ maximalIdeal S ^ (n + 2) :=
      mem_ramificationGroup_natCast_iff.mp hτ' π'
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hτcoord :
        ramificationGroupGradedToResidueField G S n π' hπ'
          (Additive.ofMul (QuotientGroup.mk τ)) = residue S y :=
      ramificationGroupGradedToResidueField_of_smul_sub_eq n π' hπ' τ y hy.symm
    have hconjMove :
        ((MulAut.conjNormal (σ : G) τ : ramificationGroup G S ((n : ℤ) + 1)) : G) • π - π =
          ((σ : G) • y) * π ^ (n + 2) := by
      calc
        _ = (σ : G) • ((τ : G) • π' - π') := by
          simp [π', MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = (σ : G) • (y * π' ^ (n + 2)) := by rw [hy]
        _ = ((σ : G) • y) * π ^ (n + 2) := by
          rw [smul_mul', smul_pow']
          simp [π']
    have hconjCoord :
        ramificationGroupGradedToResidueField G S n π hπ
          (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal (σ : G) τ))) =
        residue S y := by
      rw [ramificationGroupGradedToResidueField_of_smul_sub_eq n π hπ _ _ hconjMove,
        residue_smul_eq_of_mem_ramificationGroup_zero G S σ.2 y]
    have haResidue :
        residue S (TauCeti.uniformizerChangeUnit π π' hπ hπ' : S) =
          (((tameCharacter G S σ)⁻¹ : (ResidueField S)ˣ) : ResidueField S) := by
      rw [← map_inv, ← coe_tameCharacter_of_mul_eq_smul hπ σ⁻¹
        (TauCeti.mul_uniformizerChangeUnit π π' hπ hπ')]
    have hchange := ramificationGroupGradedToResidueField_change n π π' hπ hπ' (QuotientGroup.mk τ)
    rw [haResidue, hτcoord] at hchange
    rw [ramificationGroupGradedConj_mk, hconjCoord, hchange, ← mul_assoc, ← mul_pow,
      Units.mul_inv, one_pow, one_mul]

end UniformizerRatio

section InertiaStructure

variable (G S : Type*) [Group G] [CommRing S] [IsDomain S]
  [_root_.IsDiscreteValuationRing S] [MulSemiringAction G S]

/-! ### Divisibility, solvability, and cyclicity of inertia without separability hypotheses -/

/-- The cardinality of `G_0 / G_1` divides `Nat.card (ResidueField S) - 1` (in particular, when the
residue field is finite of order `q`, `#(G_0 / G_1) ∣ q - 1`). -/
theorem card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one :
    Nat.card (RamificationGroupGraded G S 0) ∣ Nat.card (ResidueField S) - 1 := by
  by_cases hfin : Finite (ResidueField S)
  · cases nonempty_fintype (ResidueField S)
    have hker :
        (ramificationGroupToPrincipalUnitGraded G S 0).ker =
          (ramificationGroup G S ((0 : ℤ) + 1)).subgroupOf (ramificationGroup G S 0) := by
      obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
      refine le_antisymm (fun σ hσ ↦ ?_)
        (ramificationGroup_succ_subgroupOf_le_ker_ramificationGroupToPrincipalUnitGraded G S 0)
      rw [mem_ker_ramificationGroupToPrincipalUnitGraded_iff_of_irreducible hϖ, zero_add] at hσ
      rw [Subgroup.mem_subgroupOf, zero_add, ← Nat.cast_one, mem_ramificationGroup_natCast_iff]
      intro x
      set q := Fintype.card (ResidueField S)
      have hq_mem : (q : S) ∈ maximalIdeal S := by
        rw [← residue_eq_zero_iff, map_natCast, FiniteField.cast_card_eq_zero]
      set d : S := (σ : G) • x - x
      have hd : d ∈ maximalIdeal S := mem_ramificationGroup_zero_iff.mp σ.2 x
      have hpow : ((σ : G) • x) ^ q - x ^ q ∈ maximalIdeal S ^ 2 := by
        have hdx : (σ : G) • x = d + x := by simp [d]
        have hexp : (d + x) ^ q - x ^ q =
            ∑ k ∈ Finset.range q, d ^ (k + 1) * x ^ (q - (k + 1)) * (q.choose (k + 1) : S) := by
          rw [add_pow, Finset.sum_range_succ']
          simp
        rw [hdx, hexp]
        refine Submodule.sum_mem _ fun k _ ↦ ?_
        cases k with
        | zero =>
          simp only [zero_add, pow_one, Nat.choose_one_right]
          have hrew : d * x ^ (q - 1) * (q : S) = ((q : S) * d) * x ^ (q - 1) := by ring
          rw [hrew]
          exact Ideal.mul_mem_right _ _ (by rw [sq]; exact Ideal.mul_mem_mul hq_mem hd)
        | succ k =>
          have hrew :
              d ^ (k + 1 + 1) * x ^ (q - (k + 1 + 1)) * (q.choose (k + 1 + 1) : S) =
                d ^ 2 * (d ^ k * x ^ (q - (k + 1 + 1)) * (q.choose (k + 1 + 1) : S)) := by ring
          rw [hrew]
          exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hd 2)
      set z : S := x ^ q - x
      have hz : z ∈ maximalIdeal S := by
        rw [← residue_eq_zero_iff, map_sub, map_pow, FiniteField.pow_card, sub_self]
      have hσ0 : (σ : G) ∈ ramificationGroup G S (0 : ℕ) := by
        simpa only [Nat.cast_zero] using σ.2
      have hϖmove : ∀ π ∈ ({ϖ} : Set S), (σ : G) • π - π ∈ maximalIdeal S ^ (0 + 2) := by
        intro π hπ
        rw [Set.mem_singleton_iff.mp hπ, zero_add]
        exact hσ
      have hmovez : (σ : G) • z - z ∈ maximalIdeal S ^ 2 :=
        smul_sub_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal hϖ.maximalIdeal_eq.symm hσ0 hϖmove hz
      have hdiff : d = (((σ : G) • x) ^ q - x ^ q) - ((σ : G) • z - z) := by
        simp only [d, z, smul_sub, smul_pow']
        ring
      rw [hdiff]
      exact sub_mem hpow hmovez
    have hinj : Function.Injective (tameCharacterGraded G S) :=
      (principalUnitGradedZeroEquivResidueFieldUnits S).injective.comp
        ((QuotientGroup.injective_lift_iff _ _ _).2 hker.symm)
    rw [← Nat.card_units]
    exact Subgroup.card_dvd_of_injective _ hinj
  · have : Infinite (ResidueField S) := not_finite_iff_infinite.mp hfin
    rw [Nat.card_eq_zero_of_infinite (α := ResidueField S), Nat.zero_sub]
    exact dvd_zero _

private theorem ramificationGroup_ker_tameCharacter_zero_eq_top :
    ramificationGroup (tameCharacter G S).ker S 0 = ⊤ := by
  rw [eq_top_iff]
  rintro σ -
  rw [mem_ramificationGroup_zero_iff]
  intro x
  rw [Subgroup.smul_def, Subgroup.smul_def]
  exact mem_ramificationGroup_zero_iff.mp σ.1.2 x

private theorem smul_sub_mem_of_mem_ramificationGroup_ker_tameCharacter_zero :
    ∀ σ ∈ ramificationGroup (tameCharacter G S).ker S 0,
      ∀ y ∈ maximalIdeal S ^ ((0 : ℤ) + 1).toNat,
        σ • y - y ∈ maximalIdeal S ^ ((0 : ℤ) + 1 + 1).toNat := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  intro σ _ y hy
  have h1 : ((0 : ℤ) + 1).toNat = 1 := rfl
  have h2 : ((0 : ℤ) + 1 + 1).toNat = 2 := rfl
  rw [h1, pow_one] at hy
  rw [h2, Subgroup.smul_def, Subgroup.smul_def]
  have hσ0 : ((σ : ramificationGroup G S 0) : G) ∈ ramificationGroup G S (0 : ℕ) := by
    simpa only [Nat.cast_zero] using σ.1.2
  have hϖmove : ∀ π ∈ ({ϖ} : Set S),
      ((σ : ramificationGroup G S 0) : G) • π - π ∈ maximalIdeal S ^ (0 + 2) := by
    intro π hπ
    rw [Set.mem_singleton_iff.mp hπ, zero_add]
    exact (mem_ker_tameCharacter_iff_of_irreducible hϖ).mp σ.2
  exact smul_sub_mem_maximalIdeal_pow_succ_of_mem_maximalIdeal
    hϖ.maximalIdeal_eq.symm hσ0 hϖmove hy

/-- **Inertia is solvable** whenever `G` acts faithfully on a discrete valuation ring `S` with
finite inertia group `G_0` (with no separability assumption on the residue field). -/
theorem isSolvable_ramificationGroup_zero [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    Group.IsSolvable (ramificationGroup G S 0) := by
  let K := (tameCharacter G S).ker
  have hK1 : Group.IsSolvable (ramificationGroup K S 1) :=
    isSolvable_ramificationGroup_of_pos K S one_pos
  let H1 := (ramificationGroup K S ((0 : ℤ) + 1)).subgroupOf (ramificationGroup K S 0)
  have : Group.IsSolvable H1 := by
    let e1 : H1 ≃* ramificationGroup K S 1 :=
      (Subgroup.subgroupOfEquivOfLe
        (ramificationGroup_antitone K S (by omega : (0 : ℤ) ≤ (0 : ℤ) + 1))).trans
        (MulEquiv.subgroupCongr (congrArg (ramificationGroup K S) (zero_add (1 : ℤ))))
    exact Group.isSolvable_of_isSolvable_injective (f := e1.toMonoidHom) e1.injective
  have : Group.IsSolvable (RamificationGroupGraded K S 0) :=
    Group.isSolvable_of_comm (mul_comm_ramificationGroupGraded_of_smul_sub_mem le_rfl
      (smul_sub_mem_of_mem_ramificationGroup_ker_tameCharacter_zero G S))
  have hK0 : Group.IsSolvable (ramificationGroup K S 0) :=
    Group.isSolvable_of_subgroup_quotient H1
  let eK : K ≃* ramificationGroup K S 0 :=
    Subgroup.topEquiv.symm.trans
      (MulEquiv.subgroupCongr (ramificationGroup_ker_tameCharacter_zero_eq_top G S).symm)
  have : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective (f := eK.toMonoidHom) eK.injective
  have : Group.IsSolvable (ramificationGroup G S 0 ⧸ K) := by
    let eq := QuotientGroup.quotientKerEquivRange (tameCharacter G S)
    exact Group.isSolvable_of_isSolvable_injective (f := eq.toMonoidHom) eq.injective
  exact Group.isSolvable_of_subgroup_quotient K

/-- **Solvability of the ramification groups.** For a faithful action on a discrete valuation ring
`S` with finite inertia group `G_0`, every `G_i` with `0 ≤ i` — in particular `G_0` itself — is
solvable (Serre, *Local Fields*, Chapter IV, §2, Corollary 4). -/
theorem isSolvable_ramificationGroup [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    {i : ℤ} (hi : 0 ≤ i) : Group.IsSolvable (ramificationGroup G S i) := by
  have := isSolvable_ramificationGroup_zero G S
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (ramificationGroup_antitone G S hi))
    (Subgroup.inclusion_injective _)

/-- **Inertia is cyclic in residue characteristic zero**, for a faithful action on a discrete
valuation ring `S` with finite `G_0` (with no separability assumption on the residue field). -/
theorem isCyclic_ramificationGroup_zero_of_charZero [CharZero (ResidueField S)] [FaithfulSMul G S]
    [Finite (ramificationGroup G S 0)] :
    IsCyclic (ramificationGroup G S 0) := by
  let K := (tameCharacter G S).ker
  have hK1 : ramificationGroup K S 1 = ⊥ := ramificationGroup_one_eq_bot_of_charZero K S
  have : Subsingleton (RamificationGroupGraded K S 0) :=
    subsingleton_ramificationGroupGraded_of_charZero_of_smul_sub_mem le_rfl
      (smul_sub_mem_of_mem_ramificationGroup_ker_tameCharacter_zero G S)
  have hK0 : ramificationGroup K S 0 = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    have hq : (QuotientGroup.mk ⟨σ, hσ⟩ : RamificationGroupGraded K S 0) = 1 :=
      Subsingleton.elim _ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, zero_add, hK1] at hq
    exact hq
  have htop : (⊤ : Subgroup K) = ⊥ := by
    rw [← ramificationGroup_ker_tameCharacter_zero_eq_top G S, hK0]
  have hker : (tameCharacter G S).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hk : (⟨x, hx⟩ : K) ∈ (⊤ : Subgroup K) := trivial
    rw [htop, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (tameCharacter G S))
    (Units.val_injective.comp ((MonoidHom.ker_eq_bot_iff _).mp hker))

/-- When the residue characteristic `p` does not divide `#G_0`, inertia `G_0` itself is cyclic
(with no separability assumption on the residue field). -/
theorem isCyclic_ramificationGroup_zero_of_not_dvd_card (p : ℕ) [CharP (ResidueField S) p]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (hndvd : ¬ p ∣ Nat.card (ramificationGroup G S 0)) :
    IsCyclic (ramificationGroup G S 0) := by
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    let K := (tameCharacter G S).ker
    have hK1 : IsPGroup p (ramificationGroup K S 1) :=
      isPGroup_ramificationGroup K S p one_pos
    have hK1' : IsPGroup p
        ((ramificationGroup K S ((0 : ℤ) + 1)).subgroupOf (ramificationGroup K S 0)) := by
      rw [zero_add]
      exact hK1.comap_subtype
    have hK0 : IsPGroup p (ramificationGroup K S 0) :=
      IsPGroup.of_subgroup_of_quotient hK1'
        (isPGroup_ramificationGroupGraded_of_smul_sub_mem p le_rfl
          (smul_sub_mem_of_mem_ramificationGroup_ker_tameCharacter_zero G S))
    let eK : K ≃* ramificationGroup K S 0 :=
      Subgroup.topEquiv.symm.trans
        (MulEquiv.subgroupCongr (ramificationGroup_ker_tameCharacter_zero_eq_top G S).symm)
    have hKp : IsPGroup p K := hK0.of_equiv eK.symm
    have htopCard : ¬ p ∣ Nat.card (⊤ : Subgroup (ramificationGroup G S 0)) := by
      rwa [Nat.card_congr Subgroup.topEquiv.toEquiv]
    have hker : (tameCharacter G S).ker = ⊥ := by
      rw [← top_inf_eq (tameCharacter G S).ker]
      exact (TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup htopCard hKp).eq_bot
    exact isCyclic_of_injective_ringHom
      ((Units.coeHom (ResidueField S)).comp (tameCharacter G S))
      (Units.val_injective.comp ((MonoidHom.ker_eq_bot_iff _).mp hker))
  · have : CharZero (ResidueField S) := CharP.charP_to_charZero (ResidueField S)
    exact isCyclic_ramificationGroup_zero_of_charZero G S

end InertiaStructure

section SeparableResidue

variable (R G S : Type*) [Group G] [CommRing R] [IsLocalRing R] [CommRing S] [IsDomain S]
  [_root_.IsDiscreteValuationRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  [MulSemiringAction G S] [SMulCommClass G R S]
  [Algebra.IsSeparable (ResidueField R) (ResidueField S)]
include R

/-! ### Exact kernels and injectivity of the graded maps -/

/-- **Exact kernel of `ramificationGroupToPrincipalUnitGraded`.** Over a separable residue
extension, an element of `G_i` maps to `1` in `PrincipalUnitGraded S i` if and only if it belongs
to `G_{i+1}`. -/
theorem ker_ramificationGroupToPrincipalUnitGraded (i : ℕ) :
    (ramificationGroupToPrincipalUnitGraded G S i).ker =
      (ramificationGroup G S ((i : ℤ) + 1)).subgroupOf (ramificationGroup G S (i : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible S
  refine le_antisymm (fun σ hσ ↦ ?_)
    (ramificationGroup_succ_subgroupOf_le_ker_ramificationGroupToPrincipalUnitGraded G S i)
  rw [mem_ker_ramificationGroupToPrincipalUnitGraded_iff_of_irreducible hϖ] at hσ
  rw [Subgroup.mem_subgroupOf, mem_ramificationGroup_succ_iff_of_irreducible R hϖ σ.2]
  exact hσ

/-- **Injectivity of the principal-unit graded map.** Over a separable residue extension,
`θ_i : G_i / G_{i+1} →* (1 + 𝔪 ^ i) ⧸ (1 + 𝔪 ^ (i + 1))` is injective for every `i : ℕ`. -/
theorem ramificationGroupGradedToPrincipalUnitGraded_injective (i : ℕ) :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGraded G S i) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGraded R G S i).symm

/-- **Exact kernel of the tame character.** Over a separable residue extension, the kernel of
`tameCharacter G S : G_0 →* (ResidueField S)ˣ` is wild inertia `G_1`. -/
theorem ker_tameCharacter :
    (tameCharacter G S).ker =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) := by
  rw [tameCharacter_def, MulEquiv.toMonoidHom_eq_coe, MonoidHom.ker_mulEquiv_comp,
    ker_ramificationGroupToPrincipalUnitGraded R G S 0]
  ext σ
  simp only [Subgroup.mem_subgroupOf, Nat.cast_zero, zero_add]

/-- **Injectivity of the graded tame character.** Over a separable residue extension,
`G_0 / G_1` embeds into `(ResidueField S)ˣ` via `tameCharacterGraded`. -/
theorem tameCharacterGraded_injective :
    Function.Injective (tameCharacterGraded G S) :=
  (principalUnitGradedZeroEquivResidueFieldUnits S).injective.comp
    (ramificationGroupGradedToPrincipalUnitGraded_injective R G S 0)

/-- **Injectivity of the positive-depth residue coordinate.** Over a separable residue extension,
`Additive (G_{n+1} / G_{n+2})` embeds into the additive group of `ResidueField S` via
`ramificationGroupGradedToResidueField G S n π hπ`. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (π : S) (hπ : Irreducible π) :
    Function.Injective (ramificationGroupGradedToResidueField G S n π hπ) :=
  (TauCeti.principalUnitGradedSuccEquivResidueFieldOfUniformizer n π hπ).injective.comp <|
    (ramificationGroupGradedToPrincipalUnitGraded_injective R G S (n + 1)).comp
      (ramificationGroupGradedSuccCastEquiv (G := G) (S := S) n).injective

variable {G S} in
/-- Over a separable residue extension, conjugation by inertia acts trivially on `G_0 / G_1`. -/
theorem ramificationGroupGradedConj_zero (σ : ramificationGroup G S 0)
    (τ : RamificationGroupGraded G S 0) :
    ramificationGroupGradedConj G S (σ : G) 0 τ = τ := by
  apply tameCharacterGraded_injective R G S
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk]
    simp [MulAut.conjNormal_val, MulAut.conj_apply]

/-! ### Commutativity of the graded pieces and structure of `G_0 / G_1` -/

/-- Every graded piece `G_i / G_{i+1}` (`0 ≤ i`) is commutative: positive-depth pieces commute over
any local ring (`TauCeti.IsLocalRing.mul_comm_ramificationGroupGraded_of_pos`), and at depth `0`
over a separable residue extension `G_0 / G_1` embeds into `(ResidueField S)ˣ`. -/
theorem mul_comm_ramificationGroupGraded {i : ℤ} (hi : 0 ≤ i)
    (x y : RamificationGroupGraded G S i) : x * y = y * x := by
  rcases hi.eq_or_lt with rfl | hpos
  · apply tameCharacterGraded_injective R G S
    rw [map_mul, map_mul, mul_comm]
  · exact mul_comm_ramificationGroupGraded_of_pos G S hpos x y

/-- Bundled `IsMulCommutative` form of `mul_comm_ramificationGroupGraded`. -/
theorem isMulCommutative_ramificationGroupGraded {i : ℤ} (hi : 0 ≤ i) :
    IsMulCommutative (RamificationGroupGraded G S i) :=
  ⟨⟨mul_comm_ramificationGroupGraded R G S hi⟩⟩

/-- **The tame quotient is cyclic.** Over a separable residue extension, any finite tame quotient
`G_0 / G_1` embeds into the multiplicative group of the field `ResidueField S`, hence is cyclic.
No finiteness of `ResidueField S` is needed. -/
theorem isCyclic_ramificationGroupGraded_zero [Finite (RamificationGroupGraded G S 0)] :
    IsCyclic (RamificationGroupGraded G S 0) :=
  isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField S)).comp (tameCharacterGraded G S))
    (Units.val_injective.comp (tameCharacterGraded_injective R G S))

/-- Over a separable residue extension, whenever wild inertia `G_1` is trivial and `G_0` is finite,
inertia `G_0` itself is cyclic. -/
theorem isCyclic_ramificationGroup_zero_of_ramificationGroup_one_eq_bot
    [Finite (ramificationGroup G S 0)] (h1 : ramificationGroup G S 1 = ⊥) :
    IsCyclic (ramificationGroup G S 0) := by
  have := isCyclic_ramificationGroupGraded_zero R G S
  refine isCyclic_of_injective
    (QuotientGroup.mk'
      ((ramificationGroup G S ((0 : ℤ) + 1)).subgroupOf (ramificationGroup G S 0))) ?_
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', zero_add, h1, Subgroup.bot_subgroupOf]

/-- **The order of `G_0 / G_1` is not divisible by the residue characteristic.** Holds both in
positive characteristic `p` (since `(ResidueField S)ˣ` has no nontrivial `p`-torsion) and in
characteristic `0` (`p = 0`). -/
theorem not_dvd_card_ramificationGroupGraded_zero (p : ℕ) [CharP (ResidueField S) p]
    [Finite (RamificationGroupGraded G S 0)] :
    ¬ p ∣ Nat.card (RamificationGroupGraded G S 0) := by
  cases nonempty_fintype (RamificationGroupGraded G S 0)
  let e : RamificationGroupGraded G S 0 ≃* (tameCharacterGraded G S).range :=
    MonoidHom.ofInjective (tameCharacterGraded_injective R G S)
  let _ : Fintype (tameCharacterGraded G S).range := Fintype.ofEquiv _ e.toEquiv
  have hcard : Nat.card (RamificationGroupGraded G S 0) =
      Fintype.card (tameCharacterGraded G S).range := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  rw [hcard, ← CharP.cast_eq_zero_iff (ResidueField S) p]
  exact FiniteField.card_cast_subgroup_card_ne_zero (tameCharacterGraded G S).range

/-- The index `[G_0 : G_1]` is not divisible by the residue characteristic `p`. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [CharP (ResidueField S) p]
    [Finite (RamificationGroupGraded G S 0)] :
    ¬ p ∣ ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index := by
  have h : ((ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0)).index =
      Nat.card (RamificationGroupGraded G S 0) := by
    rw [RamificationGroupGraded, zero_add, Subgroup.index_eq_card]
  rw [h]
  exact not_dvd_card_ramificationGroupGraded_zero R G S p

/-! ### Wild inertia as the Sylow `p`-subgroup of `G_0` and unified tame-inertia criterion -/

/-- **Wild inertia is the Sylow `p`-subgroup of inertia.** In positive residue characteristic `p`,
for a faithful action with finite `G_0` and separable residue extension, `G_1` viewed inside `G_0`
is a Sylow `p`-subgroup of `G_0` (Serre, *Local Fields*, Chapter IV, §2, Corollary 3). -/
def ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    Sylow p (ramificationGroup G S 0) :=
  have : Finite (ramificationGroup G S 1) :=
    Finite.of_injective
      (Subgroup.inclusion (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1)))
      (Subgroup.inclusion_injective _)
  ((isPGroup_ramificationGroup G S p (i := 1) one_pos).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one R G S p)

@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    (ramificationGroupOneSylow R G S p : Subgroup (ramificationGroup G S 0)) =
      (ramificationGroup G S 1).subgroupOf (ramificationGroup G S 0) :=
  (rfl)

/-- The wild inertia Sylow subgroup is normal in `G_0`. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    (ramificationGroupOneSylow R G S p : Subgroup (ramificationGroup G S 0)).Normal := by
  rw [ramificationGroupOneSylow_coe]
  infer_instance

/-- `ramificationGroupOneSylow` is the unique Sylow `p`-subgroup of `G_0`. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)]
    (Q : Sylow p (ramificationGroup G S 0)) :
    Q = ramificationGroupOneSylow R G S p := by
  let _ : Unique (Sylow p (ramificationGroup G S 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow R G S p)
      (ramificationGroupOneSylow_normal R G S p)
  exact Subsingleton.elim _ _

/-- The order of wild inertia `G_1` is the `p`-part of the order of inertia `G_0`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]
    [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    Nat.card (ramificationGroup G S 1) =
      p ^ (Nat.card (ramificationGroup G S 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow R G S p)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

/-- **Wild inertia is trivial if and only if the residue characteristic `p` does not divide
`#G_0`.** Holds uniformly for both positive prime characteristic and characteristic zero
(`p = 0`). -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_card_ramificationGroup_zero (p : ℕ)
    [CharP (ResidueField S) p] [FaithfulSMul G S] [Finite (ramificationGroup G S 0)] :
    ramificationGroup G S 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G S 0) := by
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one R G S p,
      pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
    simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]
  · have : CharZero (ResidueField S) := CharP.charP_to_charZero (ResidueField S)
    have : Finite (ramificationGroup G S 1) :=
      Finite.of_injective
        (Subgroup.inclusion (ramificationGroup_antitone G S (by omega : (0 : ℤ) ≤ 1)))
        (Subgroup.inclusion_injective _)
    rw [ramificationGroup_one_eq_bot_of_charZero G S, zero_dvd_iff]
    exact ⟨fun _ ↦ Nat.card_pos.ne', fun _ ↦ rfl⟩

end SeparableResidue

end TauCeti.IsDiscreteValuationRing
