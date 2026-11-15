/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
public import TauCeti.RingTheory.DiscreteValuationRing.PrincipalUnitGroup
public import TauCeti.RingTheory.LocalRing.RamificationGroup
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.GroupTheory.PGroup

/-!
# Graded embeddings of the ramification filtration of a discrete valuation ring

Let a group `G` act by ring automorphisms on a discrete valuation ring `B` with maximal ideal `𝔪`
and residue field `κ`. Fixing a uniformizer `ϖ` of `B`, every `σ` in the `i`-th ramification group
`G_i = TauCeti.IsLocalRing.ramificationGroup G B (i : ℤ)` (`i : ℕ`) sends `ϖ` to the uniformizer
`σ • ϖ = ϖ * u`, where the unique unit `u : Bˣ` lies in `U(B, i) = (𝔪 ^ i).principalUnitGroup`.

Without any base ring or separability assumption, `σ ↦ u` induces a uniformizer-independent group
homomorphism `G_i →* U(B, i) / U(B, i + 1)` that kills `G_{i+1}` and therefore descends to
`θ_i : G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`:

* at depth zero, composing with `U(B, 0) / U(B, 1) ≃* κˣ` gives the uniformizer-independent **tame
  character** `G_0 →* κˣ` and its descent `G_0 / G_1 →* κˣ`, which are equivariant for conjugation
  by `G` and the induced action on `κ`;
* at positive depth `n + 1`, composing with the uniformizer coordinate
  `Additive (U(B, n + 1) / U(B, n + 2)) ≃+ κ` gives a homomorphism
  `Additive (G_{n+1} / G_{n+2}) →+ κ`, which scales by `residue B a ^ (n + 1)` when `ϖ` is replaced
  by `ϖ * a` and satisfies Serre's conjugation formula
  `θ_{n+1}(σ τ σ⁻¹) = θ_0(σ) ^ (n + 1) * θ_{n+1}(τ)` for `σ ∈ G_0`.

When `B` is an algebra over a local ring `A` whose elements `G` fixes and the residue extension
`ResidueField B / ResidueField A` is separable, membership of `σ ∈ G_0` in `G_n` is decided on `ϖ`
alone (`mem_ramificationGroup_natCast_iff_smul_sub_mem`), so `lowerIndex B σ = addVal B (σ • ϖ - ϖ)`
on `G_0`, the kernel of `G_i →* U(B, i) / U(B, i + 1)` is `G_{i+1}`, and every graded map `θ_i` is
injective. Neither completeness of `A`, nor module-finiteness of `B` over `A`, nor finiteness of
`κ` is required. Consequently:

* every nonnegative graded piece `G_i / G_{i+1}` (`i ≥ 0`) is commutative, and when `G` acts
  faithfully and `G_0` is finite, every `G_i` (`i ≥ 0`, in particular `G_0`) is solvable regardless
  of the residue characteristic;
* when `G_0 / G_1` is finite, `G_0 / G_1` is cyclic, and in positive residue characteristic `p` its
  order (and the index `[G_0 : G_1]`) is prime to `p`;
* in positive residue characteristic `p`, each positive-depth graded piece `G_{n+1} / G_{n+2}` has
  exponent dividing `p` (`x ^ p = 1`) and is a `p`-group, and when `G` acts faithfully and `G_0` is
  finite, every `G_i` (`i > 0`) is a `p`-group and `G_1` is the unique normal Sylow `p`-subgroup of
  `G_0`, trivial if and only if `¬ p ∣ #G_0`;
* in residue characteristic zero (`CharZero (ResidueField B)`), every finite-order element of
  `G_{n+1} / G_{n+2}` is trivial, and when `G_0` is finite every `G_i` (`i > 0`) equals the kernel
  of the action (`⊥` when `G` acts faithfully), making `G_0` itself cyclic for a faithful action.

On a nonarchimedean local field `L` with finite residue field, the fraction-field counterparts are
developed in `TauCeti/NumberTheory/LocalField/UnitFiltration/RamificationGroup.lean` and
`TauCeti/NumberTheory/LocalField/UnitFiltration/Conjugation.lean`; for places of function fields,
see `TauCeti/FieldTheory/FunctionField/Place/Extension/TameInertia.lean` and
`TauCeti/FieldTheory/FunctionField/Place/Extension/WildInertia.lean`.

## Main definitions

* `TauCeti.IsDiscreteValuationRing.uniformizerRatio`: the unit `u ∈ U(B, i)` with `ϖ * u = σ • ϖ`
  for `σ ∈ G_i`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupToPrincipalUnitGroupGraded` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded`: the
  uniformizer-independent homomorphisms `G_i →* U(B, i) / U(B, i + 1)` and
  `G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`.
* `TauCeti.IsDiscreteValuationRing.tameCharacter` and
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded`: the tame character on `G_0` and
  `G_0 / G_1`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField`: the positive-depth
  additive residue coordinate on `G_{n+1} / G_{n+2}` determined by a uniformizer.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupOneSylow`: `G_1` as the unique normal Sylow
  `p`-subgroup of `G_0` in positive residue characteristic `p`.

## Main results

* `TauCeti.IsDiscreteValuationRing.mem_ramificationGroup_natCast_iff_smul_sub_mem` and
  `TauCeti.IsDiscreteValuationRing.lowerIndex_eq_addVal_of_mem_ramificationGroup_zero`: under a
  separable residue extension, `σ ∈ G_0` lies in `G_n` iff `σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)` and has lower
  index `addVal B (σ • ϖ - ϖ)`.
* `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToPrincipalUnitGroupGraded_injective`,
  `TauCeti.IsDiscreteValuationRing.tameCharacterGraded_injective`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_injective`: injectivity of
  the graded homomorphisms under a separable residue extension.
* `TauCeti.IsDiscreteValuationRing.tameCharacter_conj` and
  `TauCeti.IsDiscreteValuationRing.ramificationGroupGradedToResidueField_conj`: conjugation laws on
  the graded pieces.
* `TauCeti.IsDiscreteValuationRing.isMulCommutative_ramificationGroupGraded` and
  `TauCeti.IsDiscreteValuationRing.isSolvable_ramificationGroup_zero`: commutativity of the graded
  pieces `G_i / G_{i+1}` (`i ≥ 0`) and solvability of `G_0`.
* `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroupGraded_zero` and
  `TauCeti.IsDiscreteValuationRing.not_dvd_index_ramificationGroup_one`: cyclicity and prime-to-`p`
  order of the tame quotient.
* `TauCeti.IsDiscreteValuationRing.isPGroup_ramificationGroup`,
  `TauCeti.IsDiscreteValuationRing.eq_ramificationGroupOneSylow`, and
  `TauCeti.IsDiscreteValuationRing.ramificationGroup_one_eq_bot_iff_not_dvd_natCard`:
  wild inertia structure in positive residue characteristic (Sylow `p`-subgroup and tameness
  criterion).
* `TauCeti.IsDiscreteValuationRing.ramificationGroup_eq_bot_of_charZero` and
  `TauCeti.IsDiscreteValuationRing.isCyclic_ramificationGroup_zero_of_charZero`: vanishing of wild
  inertia and cyclicity of `G_0` in residue characteristic zero.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Propositions 5, 7, and 9, Corollaries
  1–4.
* J.-P. Serre, *Sur les corps locaux à corps résiduel algébriquement clos*, Bull. Soc. Math. France
  89 (1961), n° 3.1, Proposition 1 with Corollaries 1–2 and Proposition 2, pp. 126–127.
-/

public section
noncomputable section

open IsLocalRing TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

section GradedMaps

variable {G : Type*} [Group G]
variable {B : Type*} [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
variable [MulSemiringAction G B]

/-- Multiplying by a uniformizer `ϖ` shifts membership in powers of the maximal ideal by `1`. -/
private theorem mul_mem_maximalIdeal_pow_succ_iff {ϖ c : B} (hϖ : Irreducible ϖ) (i : ℕ) :
    ϖ * c ∈ maximalIdeal B ^ (i + 1) ↔ c ∈ maximalIdeal B ^ i := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_succ',
    mul_dvd_mul_iff_left hϖ.ne_zero]

/-- An element `σ ∈ G_i` moves any unit `u : Bˣ` by a factor `u⁻¹ * σ(u)` in `U(B, i + 1)`. -/
private theorem inv_mul_unitsMap_mem_principalUnitGroup_succ {i : ℕ} {σ : G}
    (hσ : σ ∈ ramificationGroup G B (i : ℤ)) (u : Bˣ) :
    u⁻¹ * Units.map (MulSemiringAction.toRingHom G B σ).toMonoidHom u ∈
      (maximalIdeal B ^ (i + 1)).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup]
  have hsplit : ((u⁻¹ * Units.map (MulSemiringAction.toRingHom G B σ).toMonoidHom u : Bˣ) : B) -
      1 = ↑u⁻¹ * (σ • (u : B) - (u : B)) := by
    rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulSemiringAction.toRingHom_apply, mul_sub, Units.inv_mul]
  rw [hsplit]
  exact Ideal.mul_mem_left _ _ (mem_ramificationGroup_natCast_iff.mp hσ (u : B))

/-- For `σ ∈ G_i` and a uniformizer `ϖ`, the unique unit carrying `ϖ` to `σ • ϖ` lies in
`U(B, i) = (𝔪 ^ i).principalUnitGroup`. -/
theorem uniformizerChangeUnit_smul_mem_principalUnitGroup (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    {σ : G} (hσ : σ ∈ ramificationGroup G B (i : ℤ)) :
    TauCeti.uniformizerChangeUnit ϖ (σ • ϖ) hϖ
        (by simpa using hϖ.map (MulSemiringAction.toRingAut G B σ)) ∈
      (maximalIdeal B ^ i).principalUnitGroup := by
  rw [Ideal.mem_principalUnitGroup, ← mul_mem_maximalIdeal_pow_succ_iff hϖ i, mul_sub, mul_one,
    TauCeti.mul_uniformizerChangeUnit]
  exact mem_ramificationGroup_natCast_iff.mp hσ ϖ

/-- The unit `u ∈ U(B, i)` satisfying `ϖ * u = σ • ϖ`, attached to a uniformizer `ϖ` and an
element `σ` of the `i`-th ramification group `G_i`. -/
def uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (maximalIdeal B ^ i).principalUnitGroup :=
  ⟨TauCeti.uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ
      (by simpa using hϖ.map (MulSemiringAction.toRingAut G B (σ : G))),
    uniformizerChangeUnit_smul_mem_principalUnitGroup i hϖ σ.2⟩

/-- In `Bˣ`, `uniformizerRatio i hϖ σ` is `uniformizerChangeUnit ϖ (σ • ϖ)`. -/
theorem coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    (uniformizerRatio i hϖ σ : Bˣ) =
      TauCeti.uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ
        (by simpa using hϖ.map (MulSemiringAction.toRingAut G B (σ : G))) :=
  (rfl)

/-- Multiplying `ϖ` on the right by `uniformizerRatio i hϖ σ` recovers `σ • ϖ`. -/
@[simp]
theorem mul_coe_uniformizerRatio (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ϖ * ((uniformizerRatio i hϖ σ : Bˣ) : B) = (σ : G) • ϖ :=
  TauCeti.mul_uniformizerChangeUnit ϖ ((σ : G) • ϖ) hϖ _

/-! ### The quotient homomorphism into the principal-unit graded piece -/

/-- The **quotient homomorphism** `G_i →* U(B, i) / U(B, i + 1)` sending `σ` to the class of the
unit `u` with `ϖ * u = σ • ϖ`. Neither a base ring nor separability of a residue extension is
needed to construct it or prove its independence of `ϖ`. -/
def ramificationGroupToPrincipalUnitGroupGraded (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  MonoidHom.mk' (fun σ ↦ QuotientGroup.mk (uniformizerRatio i hϖ σ)) fun σ τ ↦ by
    rw [← QuotientGroup.mk_mul, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    set uσ : Bˣ := (uniformizerRatio i hϖ σ : Bˣ)
    set uτ : Bˣ := (uniformizerRatio i hϖ τ : Bˣ)
    set uστ : Bˣ := (uniformizerRatio i hϖ (σ * τ) : Bˣ)
    have hcocycle :
        uστ = uσ * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom uτ := by
      apply Units.ext
      apply mul_left_cancel₀ hϖ.ne_zero
      rw [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        MulSemiringAction.toRingHom_apply, ← mul_assoc, mul_coe_uniformizerRatio,
        mul_coe_uniformizerRatio, Subgroup.coe_mul, mul_smul,
        ← mul_coe_uniformizerRatio i hϖ τ, smul_mul']
    rw [hcocycle, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact inv_mul_unitsMap_mem_principalUnitGroup_succ σ.2 uτ

@[simp]
theorem ramificationGroupToPrincipalUnitGroupGraded_apply (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupToPrincipalUnitGroupGraded i hϖ σ =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

/-- The homomorphism `G_i →* U(B, i) / U(B, i + 1)` does not depend on the choice of
uniformizer. -/
theorem ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ =
      ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ' := by
  set a : Bˣ := TauCeti.uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  have ha : ϖ * (a : B) = ϖ' := TauCeti.mul_uniformizerChangeUnit ϖ ϖ' hϖ hϖ'
  refine MonoidHom.ext fun σ ↦ ?_
  rw [ramificationGroupToPrincipalUnitGroupGraded_apply,
    ramificationGroupToPrincipalUnitGroupGraded_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  set u : Bˣ := (uniformizerRatio i hϖ σ : Bˣ)
  set u' : Bˣ := (uniformizerRatio i hϖ' σ : Bˣ)
  have hrel :
      a * u' = u * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
    apply Units.ext
    apply mul_left_cancel₀ hϖ.ne_zero
    rw [Units.val_mul, ← mul_assoc, ha, mul_coe_uniformizerRatio, ← ha, smul_mul',
      Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulSemiringAction.toRingHom_apply, ← mul_assoc, mul_coe_uniformizerRatio]
  have hrel' :
      u⁻¹ * u' = a⁻¹ * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
    calc u⁻¹ * u' = u⁻¹ * (a⁻¹ * (a * u')) := by rw [inv_mul_cancel_left]
      _ = u⁻¹ * (a⁻¹ *
            (u * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a)) := by
        rw [hrel]
      _ = a⁻¹ * Units.map (MulSemiringAction.toRingHom G B (σ : G)).toMonoidHom a := by
        rw [← mul_assoc, mul_comm u⁻¹ a⁻¹, mul_assoc, inv_mul_cancel_left]
  rw [hrel']
  exact inv_mul_unitsMap_mem_principalUnitGroup_succ σ.2 a

/-- An element `σ ∈ G_i` lies in the kernel of `ramificationGroupToPrincipalUnitGroupGraded i hϖ`
if and only if `σ • ϖ - ϖ ∈ 𝔪 ^ (i + 2)`. -/
theorem mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) {σ : ramificationGroup G B (i : ℤ)} :
    σ ∈ (ramificationGroupToPrincipalUnitGroupGraded i hϖ).ker ↔
      (σ : G) • ϖ - ϖ ∈ maximalIdeal B ^ (i + 2) := by
  rw [MonoidHom.mem_ker, ramificationGroupToPrincipalUnitGroupGraded_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Ideal.mem_principalUnitGroup,
    ← mul_mem_maximalIdeal_pow_succ_iff hϖ (i + 1), mul_sub, mul_one, mul_coe_uniformizerRatio]

/-- The subgroup `G_{i+1}` is contained in the kernel of
`ramificationGroupToPrincipalUnitGroupGraded i hϖ`. -/
theorem ramificationGroup_succ_subgroupOf_le_ker (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) ≤
      (ramificationGroupToPrincipalUnitGroupGraded i hϖ).ker := by
  intro σ hσ
  have hσ' : (σ : G) ∈ ramificationGroup G B ((i + 1 : ℕ) : ℤ) := by
    exact_mod_cast Subgroup.mem_subgroupOf.mp hσ
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff]
  exact mem_ramificationGroup_natCast_iff.mp hσ' ϖ

/-- The descended **graded homomorphism** `θ_i : G_i / G_{i+1} →* U(B, i) / U(B, i + 1)`. Under a
separable residue extension it is injective
(`ramificationGroupGradedToPrincipalUnitGroupGraded_injective`). -/
def ramificationGroupGradedToPrincipalUnitGroupGraded (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B (i : ℤ) →* PrincipalUnitGroupGraded B i :=
  QuotientGroup.lift _ (ramificationGroupToPrincipalUnitGroupGraded i hϖ)
    fun _ hσ ↦ ramificationGroup_succ_subgroupOf_le_ker i hϖ hσ

@[simp]
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_mk (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) (σ : ramificationGroup G B (i : ℤ)) :
    ramificationGroupGradedToPrincipalUnitGroupGraded i hϖ (QuotientGroup.mk σ) =
      QuotientGroup.mk (uniformizerRatio i hϖ σ) :=
  (rfl)

/-- The graded homomorphism `G_i / G_{i+1} →* U(B, i) / U(B, i + 1)` does not depend on the choice
of uniformizer. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible (i : ℕ) {ϖ ϖ' : B}
    (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ =
      ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ' := by
  refine MonoidHom.ext fun x ↦ ?_
  induction x using QuotientGroup.induction_on with
  | _ σ =>
    exact DFunLike.congr_fun
      (ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible (G := G) i hϖ hϖ') σ

/-! ### The tame character -/

/-- The **tame character** `θ_0 : G_0 →* (ResidueField B)ˣ`: the depth-zero quotient homomorphism
composed with `U(B, 0) / U(B, 1) ≃* (ResidueField B)ˣ`. It sends `σ ∈ G_0` to the residue of the
unit `u` with `ϖ * u = σ • ϖ`. -/
def tameCharacter {ϖ : B} (hϖ : Irreducible ϖ) :
    ramificationGroup G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits (R := B)).toMonoidHom.comp
    (ramificationGroupToPrincipalUnitGroupGraded 0 hϖ)

/-- If `ϖ * y = σ • ϖ` in `B`, then the tame character of `σ ∈ G_0` has value `residue B y`. -/
theorem coe_tameCharacter_of_mul_eq_smul {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (0 : ℤ)) {y : B} (hy : ϖ * y = (σ : G) • ϖ) :
    (tameCharacter hϖ σ : ResidueField B) = residue B y := by
  rw [tameCharacter, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ramificationGroupToPrincipalUnitGroupGraded_apply (i := 0),
    principalUnitGroupGradedZeroEquivResidueFieldUnits_mk, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  congr 1
  exact mul_left_cancel₀ hϖ.ne_zero ((mul_coe_uniformizerRatio 0 hϖ σ).trans hy.symm)

/-- The tame character does not depend on the choice of uniformizer. -/
theorem tameCharacter_eq_of_irreducible {ϖ ϖ' : B} (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ') :
    tameCharacter (G := G) hϖ = tameCharacter (G := G) hϖ' := by
  rw [tameCharacter, tameCharacter,
    ramificationGroupToPrincipalUnitGroupGraded_eq_of_irreducible (G := G) 0 hϖ hϖ']

/-- The tame character descended to `G_0 / G_1 →* (ResidueField B)ˣ`. -/
def tameCharacterGraded {ϖ : B} (hϖ : Irreducible ϖ) :
    RamificationGroupGraded G B (0 : ℤ) →* (ResidueField B)ˣ :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits (R := B)).toMonoidHom.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded 0 hϖ)

@[simp]
theorem tameCharacterGraded_mk {ϖ : B} (hϖ : Irreducible ϖ)
    (σ : ramificationGroup G B (0 : ℤ)) :
    tameCharacterGraded hϖ (QuotientGroup.mk σ) = tameCharacter hϖ σ :=
  (rfl)

/-- The graded tame character does not depend on the choice of uniformizer. -/
theorem tameCharacterGraded_eq_of_irreducible {ϖ ϖ' : B} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') :
    tameCharacterGraded (G := G) hϖ = tameCharacterGraded (G := G) hϖ' := by
  rw [tameCharacterGraded, tameCharacterGraded,
    ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible (G := G) 0 hϖ hϖ']

/-- **Equivariance of the tame character.** Conjugation by `g ∈ G` transports the tame character
through the action of `g` on `ResidueField B`: `θ_0(g σ g⁻¹) = g • θ_0(σ)`. -/
@[simp]
theorem tameCharacter_conj {π : B} (hπ : Irreducible π) (g : G)
    (σ : ramificationGroup G B (0 : ℤ)) :
    (tameCharacter hπ (MulAut.conjNormal g σ) : ResidueField B) =
      g • (tameCharacter hπ σ : ResidueField B) := by
  have hgπ : Irreducible (g • π) := hπ.map (MulSemiringAction.toRingAut G B g)
  set u : B := ((uniformizerRatio 0 hπ σ : Bˣ) : B)
  have hu : π * u = (σ : G) • π := mul_coe_uniformizerRatio 0 hπ σ
  have hgu : (g • π) * (g • u) = (MulAut.conjNormal g σ : G) • (g • π) := by
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_smul, ← hu, smul_mul']
  rw [DFunLike.congr_fun (tameCharacter_eq_of_irreducible (G := G) hπ hgπ) (MulAut.conjNormal g σ),
    coe_tameCharacter_of_mul_eq_smul hgπ _ hgu,
    coe_tameCharacter_of_mul_eq_smul hπ σ hu, ResidueField.residue_smul]

/-- If `g ∈ G` acts on the residue field as `x ↦ x ^ q`, then `θ_0(g σ g⁻¹) = θ_0(σ) ^ q`. -/
theorem tameCharacter_conj_of_smul_eq_pow {π : B} (hπ : Irreducible π) {g : G} {q : ℕ}
    (hg : ∀ x : ResidueField B, g • x = x ^ q) (σ : ramificationGroup G B (0 : ℤ)) :
    tameCharacter hπ (MulAut.conjNormal g σ) = tameCharacter hπ σ ^ q :=
  Units.ext (by rw [tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

/-- Equivariance of the graded tame character on `G_0 / G_1` under conjugation by `G`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj {π : B} (hπ : Irreducible π) (g : G)
    (τ : RamificationGroupGraded G B (0 : ℤ)) :
    (tameCharacterGraded hπ (ramificationGroupGradedConj G B g 0 τ) : ResidueField B) =
      g • (tameCharacterGraded hπ τ : ResidueField B) := by
  induction τ using QuotientGroup.induction_on with
  | _ σ =>
    rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

/-- Power-map twist of the graded tame character when `g ∈ G` acts on the residue field as
`x ↦ x ^ q`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {π : B}
    (hπ : Irreducible π) {g : G} {q : ℕ} (hg : ∀ x : ResidueField B, g • x = x ^ q)
    (τ : RamificationGroupGraded G B (0 : ℤ)) :
    tameCharacterGraded hπ (ramificationGroupGradedConj G B g 0 τ) =
      tameCharacterGraded hπ τ ^ q :=
  Units.ext (by rw [tameCharacterGraded_ramificationGroupGradedConj, hg, Units.val_pow_eq_pow_val])

/-! ### Positive-depth residue-field coordinates and conjugation -/

variable (G B) in
/-- The positive-depth homomorphism `Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` determined by a
uniformizer `π`, carrying `τ ∈ G_{n+1}` with `τ • π - π = y * π ^ (n + 2)` to `residue B y`. -/
def ramificationGroupGradedToResidueField (n : ℕ) (π : B) (hπ : Irreducible π) :
    Additive (RamificationGroupGraded G B ((n : ℤ) + 1)) →+ ResidueField B := by
  simpa only [Int.natCast_add, Int.cast_ofNat_Int] using
    (principalUnitGroupGradedSuccEquivResidueField n π hπ).toAddMonoidHom.comp
      (ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) (n + 1) hπ).toAdditive

@[simp]
theorem ramificationGroupGradedToResidueField_ofMul_mk (n : ℕ) (π : B) (hπ : Irreducible π)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n π hπ (Additive.ofMul (QuotientGroup.mk τ)) =
      principalUnitGroupGradedSuccEquivResidueField n π hπ
        (Additive.ofMul (QuotientGroup.mk (uniformizerRatio (n + 1) hπ τ))) := by
  rw [ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply]
  exact congrArg _ (congrArg Additive.ofMul
    (ramificationGroupGradedToPrincipalUnitGroupGraded_mk (n + 1) hπ τ))

/-- If `τ • π - π = y * π ^ (n + 2)`, then `ramificationGroupGradedToResidueField` sends the class
of `τ` to `residue B y`. -/
theorem ramificationGroupGradedToResidueField_of_smul_sub_eq (n : ℕ) (π : B) (hπ : Irreducible π)
    (τ : ramificationGroup G B ((n : ℤ) + 1)) (y : B)
    (hmove : (τ : G) • π - π = y * π ^ (n + 2)) :
    ramificationGroupGradedToResidueField G B n π hπ (Additive.ofMul (QuotientGroup.mk τ)) =
      residue B y := by
  rw [ramificationGroupGradedToResidueField_ofMul_mk]
  refine principalUnitGroupGradedSuccEquivResidueField_of_sub_eq n π hπ _ y ?_
  apply mul_left_cancel₀ hπ.ne_zero
  calc π * (((uniformizerRatio (n + 1) hπ τ : Bˣ) : B) - 1)
      = (τ : G) • π - π := by rw [mul_sub, mul_one, mul_coe_uniformizerRatio]
    _ = y * π ^ (n + 2) := hmove
    _ = π * (y * π ^ (n + 1)) := by rw [pow_succ', ← mul_assoc, mul_comm y π, mul_assoc]

/-- Replacing `π` by `π' = π * a` multiplies `ramificationGroupGradedToResidueField` by
`residue B a ^ (n + 1)`. -/
theorem ramificationGroupGradedToResidueField_change (n : ℕ) (π π' : B)
    (hπ : Irreducible π) (hπ' : Irreducible π')
    (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n π hπ (Additive.ofMul τ) =
      residue B (TauCeti.uniformizerChangeUnit π π' hπ hπ' : B) ^ (n + 1) *
        ramificationGroupGradedToResidueField G B n π' hπ' (Additive.ofMul τ) := by
  have hchange :=
    principalUnitGroupGradedSuccEquivResidueField_change n π π' hπ hπ'
      (Additive.ofMul (ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) (n + 1) hπ τ))
  have htheta := DFunLike.congr_fun
    (ramificationGroupGradedToPrincipalUnitGroupGraded_eq_of_irreducible (G := G) (n + 1) hπ hπ') τ
  rw [ramificationGroupGradedToResidueField, ramificationGroupGradedToResidueField]
  simp only [AddMonoidHom.comp_apply]
  simpa [htheta] using hchange

/-- **Conjugation formula on positive-depth ramification quotients.** In the residue coordinate
determined by `π`, conjugation by `σ ∈ G_0` acts on `G_{n+1} / G_{n+2}` as multiplication by
`θ_0(σ) ^ (n + 1)`, where `θ_0` is the tame character. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) (π : B) (hπ : Irreducible π)
    (σ : ramificationGroup G B (0 : ℤ))
    (τ : RamificationGroupGraded G B ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G B n π hπ
        (Additive.ofMul (ramificationGroupGradedConj G B (σ : G) ((n : ℤ) + 1) τ)) =
      (tameCharacter hπ σ : ResidueField B) ^ (n + 1) *
        ramificationGroupGradedToResidueField G B n π hπ (Additive.ofMul τ) := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let π' : B := g⁻¹ • π
    have hπ' : Irreducible π' := hπ.map (MulSemiringAction.toRingAut G B g⁻¹)
    have hmove : (τ : G) • π' - π' ∈ maximalIdeal B ^ (n + 2) :=
      mem_ramificationGroup_natCast_iff.mp τ.2 π'
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    have hτcoord :
        ramificationGroupGradedToResidueField G B n π' hπ'
          (Additive.ofMul (QuotientGroup.mk τ)) = residue B y :=
      ramificationGroupGradedToResidueField_of_smul_sub_eq n π' hπ' τ y hy.symm
    have hconjMove :
        ((MulAut.conjNormal g τ : ramificationGroup G B ((n : ℤ) + 1)) : G) • π - π =
          g • y * π ^ (n + 2) := by
      calc _ = g • ((τ : G) • π' - π') := by
            simp [π', MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * π' ^ (n + 2)) := by rw [hy]
        _ = g • y * π ^ (n + 2) := by simp [π', smul_mul', smul_pow']
    have hconjCoord :
        ramificationGroupGradedToResidueField G B n π hπ
          (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g τ))) = residue B (g • y) :=
      ramificationGroupGradedToResidueField_of_smul_sub_eq n π hπ _ (g • y) hconjMove
    have hres : residue B (g • y) = residue B y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G B σ.2 y
    have haResidue :
        residue B (TauCeti.uniformizerChangeUnit π π' hπ hπ' : B) =
          ((tameCharacter hπ σ : (ResidueField B)ˣ)⁻¹ : ResidueField B) := by
      have ha : π * (TauCeti.uniformizerChangeUnit π π' hπ hπ' : B) =
          ((σ⁻¹ : ramificationGroup G B 0) : G) • π :=
        TauCeti.mul_uniformizerChangeUnit π π' hπ hπ'
      rw [← coe_tameCharacter_of_mul_eq_smul hπ σ⁻¹ ha, map_inv, Units.val_inv_eq_inv_val]
    have hchange := ramificationGroupGradedToResidueField_change (G := G) (B := B) n π π' hπ hπ'
      (QuotientGroup.mk τ)
    rw [haResidue] at hchange
    simp only [ramificationGroupGradedConj_mk]
    rw [hconjCoord, hres, ← hτcoord]
    calc ramificationGroupGradedToResidueField G B n π' hπ'
          (Additive.ofMul (QuotientGroup.mk τ)) =
        (tameCharacter hπ σ : ResidueField B) ^ (n + 1) *
          (((tameCharacter hπ σ : (ResidueField B)ˣ)⁻¹ : ResidueField B) ^ (n + 1) *
            ramificationGroupGradedToResidueField G B n π' hπ'
              (Additive.ofMul (QuotientGroup.mk τ))) := by simp
      _ = (tameCharacter hπ σ : ResidueField B) ^ (n + 1) *
            ramificationGroupGradedToResidueField G B n π hπ
              (Additive.ofMul (QuotientGroup.mk τ)) := by rw [← hchange]

end GradedMaps

/-! ### Separable residue extension: uniformizer criterion and graded embeddings -/

section SeparableResidue

variable (A : Type*) [CommRing A] [IsLocalRing A]
variable {G : Type*} [Group G]
variable {B : Type*} [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]
variable [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
variable [MulSemiringAction G B] [SMulCommClass G A B]
include A

/-- **Membership in the ramification filtration of a DVR is decided at a uniformizer** when `B` is
an algebra over a local ring `A` fixed by `G` with separable residue extension: an element `σ ∈ G_0`
lies in `G_n` (`n : ℕ`) if and only if `σ • ϖ - ϖ ∈ 𝔪 ^ (n + 1)`. -/
theorem mem_ramificationGroup_natCast_iff_smul_sub_mem {ϖ : B} (hϖ : Irreducible ϖ) {σ : G}
    (hσ : σ ∈ ramificationGroup G B 0) {n : ℕ} :
    σ ∈ ramificationGroup G B (n : ℤ) ↔ σ • ϖ - ϖ ∈ maximalIdeal B ^ (n + 1) :=
  mem_ramificationGroup_natCast_iff_smul_sub_mem_of_maximalIdeal_eq_span A hϖ.maximalIdeal_eq hσ

/-- **Lower index of an inertia element at a uniformizer.** Under a separable residue extension, the
lower index of any `σ ∈ G_0` equals `addVal B (σ • ϖ - ϖ)` at a uniformizer `ϖ`, without assuming
`B` is monogenic over `A`. -/
theorem lowerIndex_eq_addVal_of_mem_ramificationGroup_zero {ϖ : B} (hϖ : Irreducible ϖ) {σ : G}
    (hσ : σ ∈ ramificationGroup G B 0) :
    lowerIndex B σ = _root_.IsDiscreteValuationRing.addVal B (σ • ϖ - ϖ) := by
  apply ENat.eq_of_forall_natCast_le_iff
  rintro (_ | n)
  · simp
  · rw [natCast_le_lowerIndex_iff_mem_ramificationGroup, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ hσ,
      mem_maximalIdeal_pow_iff_le_addVal]

/-- **The kernel of `G_i →* U(B, i) / U(B, i + 1)` is `G_{i+1}`** under a separable residue
extension. -/
theorem ker_ramificationGroupToPrincipalUnitGroupGraded (i : ℕ) {ϖ : B} (hϖ : Irreducible ϖ) :
    (ramificationGroupToPrincipalUnitGroupGraded (G := G) i hϖ).ker =
      (ramificationGroup G B ((i : ℤ) + 1)).subgroupOf (ramificationGroup G B (i : ℤ)) := by
  refine le_antisymm (fun σ hσ ↦ ?_) (ramificationGroup_succ_subgroupOf_le_ker i hϖ)
  rw [mem_ker_ramificationGroupToPrincipalUnitGroupGraded_iff] at hσ
  have hσ₀ : (σ : G) ∈ ramificationGroup G B 0 :=
    ramificationGroup_antitone G B (Int.natCast_nonneg i) σ.2
  rw [Subgroup.mem_subgroupOf, ← Nat.cast_succ,
    mem_ramificationGroup_natCast_iff_smul_sub_mem A hϖ hσ₀]
  exact hσ

/-- **The graded homomorphism `G_i / G_{i+1} →* U(B, i) / U(B, i + 1)` is injective** under a
separable residue extension. -/
theorem ramificationGroupGradedToPrincipalUnitGroupGraded_injective (i : ℕ) {ϖ : B}
    (hϖ : Irreducible ϖ) :
    Function.Injective (ramificationGroupGradedToPrincipalUnitGroupGraded (G := G) i hϖ) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    (ker_ramificationGroupToPrincipalUnitGroupGraded A i hϖ).symm

/-- **The kernel of the tame character is `G_1`** under a separable residue extension. -/
theorem ker_tameCharacter {ϖ : B} (hϖ : Irreducible ϖ) :
    (tameCharacter (G := G) hϖ).ker =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) := by
  ext σ
  simp [tameCharacter, ker_ramificationGroupToPrincipalUnitGroupGraded A 0 hϖ]

/-- **The graded tame character `G_0 / G_1 →* (ResidueField B)ˣ` is injective** under a separable
residue extension. -/
theorem tameCharacterGraded_injective {ϖ : B} (hϖ : Irreducible ϖ) :
    Function.Injective (tameCharacterGraded (G := G) hϖ) :=
  (principalUnitGroupGradedZeroEquivResidueFieldUnits (R := B)).injective.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded_injective A 0 hϖ)

/-- Conjugation by an element of inertia `G_0` acts trivially on the tame quotient `G_0 / G_1` under
a separable residue extension. -/
theorem ramificationGroupGradedConj_zero (σ : ramificationGroup G B 0)
    (τ : RamificationGroupGraded G B 0) :
    ramificationGroupGradedConj G B (σ : G) 0 τ = τ := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  apply tameCharacterGraded_injective A hπ
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    simp only [ramificationGroupGradedConj_mk, tameCharacterGraded_mk]
    rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
      mul_comm (tameCharacter hπ σ) (tameCharacter hπ τ), mul_assoc, mul_inv_cancel, mul_one]

/-- **The positive-depth graded map `Additive (G_{n+1} / G_{n+2}) →+ ResidueField B` is injective**
under a separable residue extension. -/
theorem ramificationGroupGradedToResidueField_injective (n : ℕ) (π : B) (hπ : Irreducible π) :
    Function.Injective (ramificationGroupGradedToResidueField G B n π hπ) :=
  (principalUnitGroupGradedSuccEquivResidueField n π hπ).injective.comp
    (ramificationGroupGradedToPrincipalUnitGroupGraded_injective A (n + 1) hπ)

variable (G B) in
/-- **Every nonnegative graded piece `G_i / G_{i+1}` (`0 ≤ i`) is commutative** under a separable
residue extension: it embeds into `(ResidueField B)ˣ` at depth `0` and into the additive group of
`ResidueField B` at positive depth. -/
theorem isMulCommutative_ramificationGroupGraded {i : ℤ} (hi : 0 ≤ i) :
    IsMulCommutative (RamificationGroupGraded G B i) := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  rcases eq_or_lt_of_le hi with rfl | hi'
  · refine IsMulCommutative.of_comm fun x y ↦ tameCharacterGraded_injective A hπ ?_
    rw [map_mul, map_mul, mul_comm]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n : ℤ) + 1 := ⟨(i - 1).toNat, by omega⟩
    refine IsMulCommutative.of_comm fun x y ↦ ?_
    apply Additive.ofMul.injective
    apply ramificationGroupGradedToResidueField_injective A n π hπ
    rw [ofMul_mul, ofMul_mul, map_add, map_add, add_comm]

variable (G B) in
/-- **Every nonnegative ramification group `G_i` (`0 ≤ i`) is solvable** under a separable residue
extension when `G` acts faithfully and `G_0` is finite, regardless of the residue characteristic:
the filtration reaches `⊥` in finitely many steps and all of its quotients `G_j / G_{j+1}` (`0 ≤ j`)
are commutative. -/
theorem isSolvable_ramificationGroup [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    {i : ℤ} (hi : 0 ≤ i) :
    Group.IsSolvable (ramificationGroup G B i) := by
  obtain ⟨N, hN⟩ := exists_forall_ramificationGroup_eq_bot G B
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (j : ℤ) := ⟨i.toNat, (Int.toNat_of_nonneg hi).symm⟩
  suffices ∀ d j : ℕ, N ≤ j + d → Group.IsSolvable (ramificationGroup G B (j : ℤ)) from
    this N.toNat j (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [hN _ (by omega)]
    infer_instance
  | succ d ih =>
    intro j hj
    have hsucc := ih (j + 1) (by omega)
    push_cast at hsucc
    have : IsMulCommutative (RamificationGroupGraded G B (j : ℤ)) :=
      isMulCommutative_ramificationGroupGraded A G B (Int.natCast_nonneg j)
    let e := Subgroup.subgroupOfEquivOfLe
      (ramificationGroup_antitone G B (by omega : (j : ℤ) ≤ j + 1))
    have : Group.IsSolvable
        ((ramificationGroup G B ((j : ℤ) + 1)).subgroupOf (ramificationGroup G B (j : ℤ))) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_subgroup_quotient
      ((ramificationGroup G B ((j : ℤ) + 1)).subgroupOf (ramificationGroup G B (j : ℤ)))

variable (G B) in
/-- **The inertia group `G_0` is solvable** under a separable residue extension when `G` acts
faithfully and `G_0` is finite, regardless of the residue characteristic. -/
theorem isSolvable_ramificationGroup_zero [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Group.IsSolvable (ramificationGroup G B 0) :=
  isSolvable_ramificationGroup A G B le_rfl

/-! ### Cyclicity and prime-to-`p` order of the tame quotient -/

variable (G B) in
/-- **The tame quotient `G_0 / G_1` is cyclic** whenever it is finite and the residue extension is
separable: it embeds into `(ResidueField B)ˣ`, whose finite subgroups are cyclic even when
`ResidueField B` is infinite. -/
theorem isCyclic_ramificationGroupGraded_zero [Finite (RamificationGroupGraded G B 0)] :
    IsCyclic (RamificationGroupGraded G B 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacterGraded (G := G) hϖ))
    (Units.val_injective.comp (tameCharacterGraded_injective A hϖ))

variable (G B) in
/-- **The order of a finite tame quotient `G_0 / G_1` is not divisible by the residue characteristic
`p`**, under a separable residue extension: for `p` prime a field of characteristic `p` has no
nontrivial `p`-th roots of unity, while `p = 0` never divides `#(G_0 / G_1) > 0`. -/
theorem not_dvd_natCard_ramificationGroupGraded_zero (p : ℕ)
    [CharP (ResidueField B) p] [Finite (RamificationGroupGraded G B 0)] :
    ¬ p ∣ Nat.card (RamificationGroupGraded G B 0) := by
  rcases CharP.char_is_prime_or_zero (ResidueField B) p with hp_prime | rfl
  · let _ : Fact p.Prime := ⟨hp_prime⟩
    have : NeZero p := ⟨hp_prime.ne_zero⟩
    obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
    let φ := tameCharacterGraded (G := G) hϖ
    have hφ := tameCharacterGraded_injective A (G := G) hϖ
    intro hp
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp
    have hord : orderOf ((φ x : (ResidueField B)ˣ) : ResidueField B) = p := by
      rw [orderOf_units, orderOf_injective φ hφ x, hx]
    have hroot := hord ▸ IsPrimitiveRoot.orderOf ((φ x : (ResidueField B)ˣ) : ResidueField B)
    exact hroot.neZero'.out (CharP.cast_eq_zero _ p)
  · rw [zero_dvd_iff]
    exact Nat.card_pos.ne'

variable (G B) in
/-- **The index `[G_0 : G_1]` is not divisible by the residue characteristic `p`** whenever
`G_0 / G_1` is finite and the residue extension is separable. -/
theorem not_dvd_index_ramificationGroup_one (p : ℕ) [CharP (ResidueField B) p]
    [Finite (RamificationGroupGraded G B 0)] :
    ¬ p ∣ ((ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0)).index := by
  rw [Subgroup.index_eq_card]
  simpa only [RamificationGroupGraded, zero_add] using
    not_dvd_natCard_ramificationGroupGraded_zero A G B p

variable (G B) in
/-- In positive residue characteristic `p`, `p` is coprime to `#(G_0 / G_1)` whenever `G_0 / G_1` is
finite and the residue extension is separable. -/
theorem coprime_natCard_ramificationGroupGraded_zero (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField B) p] [Finite (RamificationGroupGraded G B 0)] :
    p.Coprime (Nat.card (RamificationGroupGraded G B 0)) :=
  (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (not_dvd_natCard_ramificationGroupGraded_zero A G B p)

/-! ### Wild ramification in positive residue characteristic -/

/-- In residue characteristic `p`, every element of `G_{n+1} / G_{n+2}` has `p`-th power equal to
`1`, under a separable residue extension: `Additive (G_{n+1} / G_{n+2})` embeds into the additive
group of `ResidueField B`, which is annihilated by `p`. -/
theorem pow_char_eq_one_ramificationGroupGraded_natCast_succ (p : ℕ) [CharP (ResidueField B) p]
    (n : ℕ) (x : RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)) :
    x ^ p = 1 := by
  revert x
  rw [Nat.cast_succ]
  intro x
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  apply Additive.ofMul.injective
  apply ramificationGroupGradedToResidueField_injective A n π hπ
  rw [ofMul_pow, map_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofMul_one, map_zero]

/-- In residue characteristic `p`, raising an element of `G_{n+1}` to the `p`-th power lands in
`G_{n+2}`, under a separable residue extension. -/
theorem pow_mem_ramificationGroup_natCast_succ_of_charP (p : ℕ) [CharP (ResidueField B) p]
    {n : ℕ} {σ : G} (hσ : σ ∈ ramificationGroup G B ((n + 1 : ℕ) : ℤ)) :
    σ ^ p ∈ ramificationGroup G B ((n + 2 : ℕ) : ℤ) := by
  have hmk : QuotientGroup.mk (⟨σ, hσ⟩ ^ p) =
      (1 : RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)) := by
    rw [QuotientGroup.mk_pow]
    exact pow_char_eq_one_ramificationGroupGraded_natCast_succ A p n _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmk
  simpa only [Subgroup.coe_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc,
    one_add_one_eq_two] using hmk

variable (G B) in
/-- At positive depth, each graded piece `G_{n+1} / G_{n+2}` is a `p`-group in residue
characteristic `p`, under a separable residue extension. -/
theorem isPGroup_ramificationGroupGraded_natCast_succ (p : ℕ)
    [CharP (ResidueField B) p] (n : ℕ) :
    IsPGroup p (RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)) :=
  fun x ↦ ⟨1, by rw [pow_one]; exact pow_char_eq_one_ramificationGroupGraded_natCast_succ A p n x⟩

variable (G B) in
/-- **The positive-depth ramification groups are `p`-groups** in residue characteristic `p`,
whenever the residue extension is separable, `G` acts faithfully, and `G_0` is finite; in particular
the wild inertia group `G_1` is a `p`-group. -/
theorem isPGroup_ramificationGroup (p : ℕ) [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] {i : ℤ} (hi : 0 < i) :
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
      (isPGroup_ramificationGroupGraded_natCast_succ A G B p j)
    push_cast
    exact hsucc.comap_subtype

variable (G B) in
/-- **Wild inertia is a Sylow `p`-subgroup of inertia** in positive residue characteristic `p`,
under a separable residue extension, a faithful action, and finite `G_0`. -/
def ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Sylow p (ramificationGroup G B 0) :=
  ((isPGroup_ramificationGroup A G B p (i := 1) (by omega)).comap_subtype).toSylow
    (not_dvd_index_ramificationGroup_one A G B p)

variable (G B) in
/-- The subgroup underlying `ramificationGroupOneSylow` is `G_1` inside `G_0`. -/
@[simp]
theorem ramificationGroupOneSylow_coe (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow A G B p : Subgroup (ramificationGroup G B 0)) =
      (ramificationGroup G B 1).subgroupOf (ramificationGroup G B 0) :=
  (rfl)

variable (G B) in
/-- The wild inertia Sylow `p`-subgroup is normal in `G_0`. -/
theorem ramificationGroupOneSylow_normal (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    (ramificationGroupOneSylow A G B p : Subgroup (ramificationGroup G B 0)).Normal := by
  rw [ramificationGroupOneSylow_coe,
    Subgroup.normal_subgroupOf_iff_le_normalizer
      (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1)),
    Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

/-- **Wild inertia is the unique Sylow `p`-subgroup of inertia** in positive residue characteristic
`p`, under a separable residue extension, a faithful action, and finite `G_0`. -/
theorem eq_ramificationGroupOneSylow (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)]
    (Q : Sylow p (ramificationGroup G B 0)) :
    Q = ramificationGroupOneSylow A G B p := by
  let _ : Unique (Sylow p (ramificationGroup G B 0)) :=
    Sylow.unique_of_normal (ramificationGroupOneSylow A G B p)
      (ramificationGroupOneSylow_normal A G B p)
  exact Subsingleton.elim _ _

variable (G B) in
/-- The order of wild inertia `G_1` is the `p`-part of the order of inertia `G_0`:
`#G_1 = p ^ (#G_0).factorization p`. -/
theorem natCard_ramificationGroup_one (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p]
    [FaithfulSMul G B] [Finite (ramificationGroup G B 0)] :
    Nat.card (ramificationGroup G B 1) =
      p ^ (Nat.card (ramificationGroup G B 0)).factorization p := by
  rw [← Sylow.card_eq_multiplicity (ramificationGroupOneSylow A G B p)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (ramificationGroup_antitone G B (by omega : (0 : ℤ) ≤ 1))).toEquiv.symm

variable (G B) in
/-- **Wild inertia is trivial if and only if `p` does not divide `#G_0`**, in positive residue
characteristic `p`, under a separable residue extension, a faithful action, and finite `G_0`. -/
theorem ramificationGroup_one_eq_bot_iff_not_dvd_natCard (p : ℕ)
    [Fact p.Prime] [CharP (ResidueField B) p] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    ramificationGroup G B 1 = ⊥ ↔ ¬ p ∣ Nat.card (ramificationGroup G B 0) := by
  have hp : p.Prime := Fact.out
  rw [← Subgroup.card_eq_one, natCard_ramificationGroup_one A G B p,
    pow_eq_one_iff_right hp.ne_one, Nat.factorization_eq_zero_iff]
  simp only [hp, not_true_eq_false, false_or, Nat.card_pos.ne', or_false]

/-! ### Vanishing of higher ramification groups in residue characteristic zero -/

/-- In residue characteristic zero, every finite-order element of `G_{n+1} / G_{n+2}` is trivial
under a separable residue extension: `Additive (G_{n+1} / G_{n+2})` embeds into the torsion-free
additive group of `ResidueField B`. -/
theorem eq_one_of_isOfFinOrder_ramificationGroupGraded_natCast_succ [CharZero (ResidueField B)]
    (n : ℕ) {x : RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)} (hx : IsOfFinOrder x) :
    x = 1 := by
  revert x
  rw [Nat.cast_succ]
  intro x hx
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  apply Additive.ofMul.injective
  apply ramificationGroupGradedToResidueField_injective A n π hπ
  have hpow : ramificationGroupGradedToResidueField G B n π hπ (Additive.ofMul x) *
      (orderOf x : ResidueField B) = 0 := by
    rw [mul_comm, ← nsmul_eq_mul, ← map_nsmul, ← ofMul_pow, pow_orderOf_eq_one, ofMul_one,
      map_zero]
  rw [ofMul_one, map_zero]
  exact (mul_eq_zero.mp hpow).resolve_right (Nat.cast_ne_zero.mpr hx.orderOf_pos.ne')

variable (G B) in
/-- In residue characteristic zero, any finite positive-depth graded piece `G_{n+1} / G_{n+2}` is
trivial under a separable residue extension. -/
theorem subsingleton_ramificationGroupGraded_natCast_succ [CharZero (ResidueField B)] (n : ℕ)
    [Finite (RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ))] :
    Subsingleton (RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)) :=
  subsingleton_iff_forall_eq 1 |>.mpr fun x ↦
    eq_one_of_isOfFinOrder_ramificationGroupGraded_natCast_succ A n (isOfFinOrder_of_finite x)

/-- In residue characteristic zero, any finite-order element of `G_1` acts trivially on `B` under a
separable residue extension: it vanishes in every positive-depth quotient `G_{n+1} / G_{n+2}` and
therefore lies in `⨅ i, G_i`. -/
theorem mem_ker_toRingAut_of_isOfFinOrder_of_mem_ramificationGroup_one
    [CharZero (ResidueField B)] {σ : G} (hfin : IsOfFinOrder σ)
    (hσ : σ ∈ ramificationGroup G B 1) :
    σ ∈ MonoidHom.ker (MulSemiringAction.toRingAut G B) := by
  obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hall : ∀ n : ℕ, σ ∈ ramificationGroup G B ((n + 1 : ℕ) : ℤ) := by
    intro n
    induction n with
    | zero => simpa using hσ
    | succ n ih =>
      set s : ramificationGroup G B ((n + 1 : ℕ) : ℤ) := ⟨σ, ih⟩
      have hsm : s ^ m = 1 := Subtype.ext (by simpa using hpow)
      have hs : IsOfFinOrder (QuotientGroup.mk s :
          RamificationGroupGraded G B ((n + 1 : ℕ) : ℤ)) :=
        isOfFinOrder_iff_pow_eq_one.mpr
          ⟨m, hm, by rw [← QuotientGroup.mk_pow, hsm, QuotientGroup.mk_one]⟩
      have hmk := eq_one_of_isOfFinOrder_ramificationGroupGraded_natCast_succ A n hs
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmk
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two]
        using hmk
  rw [← iInf_ramificationGroup_eq_ker G B, Subgroup.mem_iInf]
  exact fun i ↦ ramificationGroup_antitone G B (by omega : i ≤ ((i.toNat + 1 : ℕ) : ℤ))
    (hall i.toNat)

/-- In residue characteristic zero, `G_1` has no nontrivial elements of finite order when `G` acts
faithfully and the residue extension is separable. -/
theorem eq_one_of_isOfFinOrder_of_mem_ramificationGroup_one [CharZero (ResidueField B)]
    [FaithfulSMul G B] {σ : G} (hfin : IsOfFinOrder σ) (hσ : σ ∈ ramificationGroup G B 1) :
    σ = 1 := by
  have hmem := mem_ker_toRingAut_of_isOfFinOrder_of_mem_ramificationGroup_one A hfin hσ
  rwa [TauCeti.MulSemiringAction.ker_toRingAut_eq_bot, Subgroup.mem_bot] at hmem

variable (G B) in
/-- **In residue characteristic zero, all positive-depth ramification groups equal the kernel of the
action** once `G_0` is finite and the residue extension is separable. -/
theorem ramificationGroup_eq_ker_of_charZero [CharZero (ResidueField B)]
    [Finite (ramificationGroup G B 0)] {i : ℤ} (hi : 0 < i) :
    ramificationGroup G B i = MonoidHom.ker (MulSemiringAction.toRingAut G B) := by
  refine le_antisymm (fun σ hσ ↦ ?_)
    ((iInf_ramificationGroup_eq_ker G B).symm.trans_le (iInf_le _ i))
  have hσ0 : σ ∈ ramificationGroup G B 0 := ramificationGroup_antitone G B hi.le hσ
  have hσ1 : σ ∈ ramificationGroup G B 1 := ramificationGroup_antitone G B (by omega) hσ
  have hfin : IsOfFinOrder σ :=
    (Subgroup.subtype _).isOfFinOrder (isOfFinOrder_of_finite (⟨σ, hσ0⟩ : ramificationGroup G B 0))
  exact mem_ker_toRingAut_of_isOfFinOrder_of_mem_ramificationGroup_one A hfin hσ1

variable (G B) in
/-- **In residue characteristic zero, all positive-depth ramification groups are trivial** when the
residue extension is separable, `G` acts faithfully, and `G_0` is finite. -/
theorem ramificationGroup_eq_bot_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] {i : ℤ} (hi : 0 < i) :
    ramificationGroup G B i = ⊥ := by
  rw [ramificationGroup_eq_ker_of_charZero A G B hi, TauCeti.MulSemiringAction.ker_toRingAut_eq_bot]

variable (G B) in
/-- **In residue characteristic zero, the inertia group `G_0` is cyclic** when the residue extension
is separable, `G` acts faithfully, and `G_0` is finite: `G_1 = ⊥`, so the tame character embeds
`G_0` into `(ResidueField B)ˣ`. -/
theorem isCyclic_ramificationGroup_zero_of_charZero [CharZero (ResidueField B)] [FaithfulSMul G B]
    [Finite (ramificationGroup G B 0)] :
    IsCyclic (ramificationGroup G B 0) := by
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B
  have hker : (tameCharacter (G := G) hϖ).ker = ⊥ := by
    rw [ker_tameCharacter A hϖ, ramificationGroup_eq_bot_of_charZero A G B zero_lt_one,
      Subgroup.bot_subgroupOf]
  exact isCyclic_of_injective_ringHom
    ((Units.coeHom (ResidueField B)).comp (tameCharacter (G := G) hϖ))
    (Units.val_injective.comp ((MonoidHom.ker_eq_bot_iff _).mp hker))

end SeparableResidue

end TauCeti.IsDiscreteValuationRing
