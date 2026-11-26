/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup
import TauCeti.RingTheory.Valuation.ValuativeRel.Action

/-!
# Conjugation on ramification quotients

Let a group `G` act on a nonarchimedean local field `L`, preserving its ring of integers.
Conjugation by an element `σ` of inertia acts on every ramification quotient `G_i/G_{i+1}`.
At depth zero this action is trivial. At positive depth, the embedding into the additive residue
field transforms by the `i`th power of the tame character:

`theta_i(σ τ σ⁻¹) = theta_0(σ)^i * theta_i(τ)`.

Here `theta_0` is the tame character `TauCeti.IsLocalRing.tameCharacter G 𝒪[L]`, and the
positive-depth maps `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField` are read in the
residue coordinate associated to a uniformizer.
The exponent is forced by changing from the uniformizer `π` to `σ⁻¹ π`. This formula supplies the
constant appearing in ramification-theoretic norm computations.

Conjugation by an arbitrary element `g ∈ G`, which need not act trivially on the residue field,
transports the tame character through the residue-field automorphism induced by `g`:

`theta_0(g σ g⁻¹) = g • theta_0(σ)`.

When `g` acts on the residue field as `x ↦ x ^ q`, as an arithmetic Frobenius does, this reads
`theta_0(g σ g⁻¹) = theta_0(σ) ^ q`, the finite-level form of the Frobenius twist on tame inertia.

## Main results

* `TauCeti.ramificationGroupGradedConj_zero`: inertia acts trivially on
  `G_0/G_1`.
* `TauCeti.ramificationGroupGradedToResidueField_conj`: at depth `i > 0`, conjugation scales the
  residue coordinate by the `i`th power of the tame character.
* `TauCeti.tameCharacter_conj` and `TauCeti.tameCharacterGraded_ramificationGroupGradedConj`:
  the tame character is equivariant for conjugation by `G` and the action of `G` on the residue
  field.
* `TauCeti.tameCharacter_conj_of_smul_eq_pow` and
  `TauCeti.tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow`: conjugation by an
  element acting on the residue field as the `q`-th power map raises the tame character to the
  `q`-th power.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2, Proposition 9.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField TauCeti.IsLocalRing

namespace TauCeti

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]

/-- The change from `π` to `σ⁻¹ • π` is the inverse tame-character coordinate of `σ`. -/
private theorem residue_uniformizerChangeUnit_inv_smul {π : 𝒪[L]} (hπ : Irreducible π)
    (σ : ramificationGroup G 𝒪[L] 0) (hπ' : Irreducible ((σ : G)⁻¹ • π)) :
    residue 𝒪[L] (uniformizerChangeUnit π ((σ : G)⁻¹ • π) hπ hπ' : 𝒪[L]) =
      ((tameCharacter G 𝒪[L] σ : 𝓀[L]ˣ)⁻¹ : 𝓀[L]) := by
  have ha : ((σ⁻¹ : ramificationGroup G 𝒪[L] 0) : G) • π =
      π * (uniformizerChangeUnit π ((σ : G)⁻¹ • π) hπ hπ' : 𝒪[L]) := by
    rw [mul_uniformizerChangeUnit, Subgroup.coe_inv]
  rw [← Units.val_inv_eq_inv_val, ← map_inv, coe_tameCharacter_of_smul_eq_mul hπ ha]

/-- Conjugation by inertia acts trivially on the tame quotient `G_0/G_1`. -/
@[simp]
theorem ramificationGroupGradedConj_zero
    (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    ramificationGroupGradedConj G 𝒪[L] (σ : G) 0 τ = τ := by
  apply tameCharacterGraded_injective (G := G) (FixedPoints.subalgebra ℤ 𝒪[L] G)
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    simp only [ramificationGroupGradedConj_mk]
    rw [tameCharacterGraded_mk, tameCharacterGraded_mk, MulAut.conjNormal_val, MulAut.conj_apply,
      map_mul, map_mul, map_inv, mul_comm (tameCharacter G 𝒪[L] σ) (tameCharacter G 𝒪[L] τ),
      mul_assoc, mul_inv_cancel, mul_one]

/-- **The conjugation action formula on positive ramification quotients.** In the residue
coordinate `TauCeti.IsLocalRing.ramificationGroupGradedToResidueField` determined by `π`,
conjugation by `σ ∈ G_0` acts on `G_i/G_{i+1}` as multiplication by `theta_0(σ)^i`, where
`theta_0` is the tame character. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) {π : 𝒪[L]}
    (hπ : Irreducible π) (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) :
    (ramificationGroupGradedToResidueField hπ n
        (ramificationGroupGradedConj G 𝒪[L] (σ : G) ((n : ℤ) + 1) τ)).toAdd =
      (tameCharacter G 𝒪[L] σ : 𝓀[L]) ^ (n + 1) *
        (ramificationGroupGradedToResidueField hπ n τ).toAdd := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    have hπ' : Irreducible (g⁻¹ • π) := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] g⁻¹)
    have hmove : (τ : G) • (g⁻¹ • π) - g⁻¹ • π ∈ maximalIdeal 𝒪[L] ^ (n + 2) :=
      (mem_ramificationGroup_natCast_iff.mp τ.property) _
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    -- The coordinate of `τ` at the moved uniformizer `π' = g⁻¹ • π` is the residue of `y`, and
    -- `g τ g⁻¹` moves `π` by `g • y * π ^ (n + 2)`, with the same residue.
    have hτcoord : (ramificationGroupToResidueField hπ' n τ).toAdd = residue 𝒪[L] y := by
      rw [ramificationGroupToResidueField_apply_of_smul_sub_eq hπ' (c := y)
        (by rw [← hy, mul_comm]), toAdd_ofAdd]
    have hconjMove :
        ((MulAut.conjNormal g τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) : G) • π - π =
          π ^ (n + 2) * g • y := by
      calc
        _ = g • ((τ : G) • (g⁻¹ • π) - g⁻¹ • π) := by
          simp [MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * (g⁻¹ • π) ^ (n + 2)) := by rw [hy]
        _ = π ^ (n + 2) * g • y := by rw [smul_mul', smul_pow', smul_inv_smul, mul_comm]
    have hresidue : residue 𝒪[L] (g • y) = residue 𝒪[L] y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G 𝒪[L] σ.property y
    -- Changing back from `π'` to `π` contributes the inverse tame-character factor.
    have hchange := toAdd_ramificationGroupToResidueField_of_mul_eq hπ hπ'
      (mul_uniformizerChangeUnit π _ hπ hπ') τ
    rw [residue_uniformizerChangeUnit_inv_smul hπ σ hπ'] at hchange
    simp only [ramificationGroupGradedConj_mk]
    rw [ramificationGroupGradedToResidueField_mk, ramificationGroupGradedToResidueField_mk,
      ramificationGroupToResidueField_apply_of_smul_sub_eq hπ hconjMove, toAdd_ofAdd, hresidue,
      ← hτcoord, hchange, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (Units.ne_zero _), one_pow,
      one_mul]

/-! ### Equivariance of the tame character -/

/-- **The tame character is equivariant.** For `g ∈ G` and `σ ∈ G_0`, the tame character of
`g σ g⁻¹` is the image of the tame character of `σ` under the automorphism of the residue field
induced by `g`: `theta_0(g σ g⁻¹) = g • theta_0(σ)`. -/
@[simp]
theorem tameCharacter_conj (g : G) (σ : ramificationGroup G 𝒪[L] 0) :
    (tameCharacter G 𝒪[L] (MulAut.conjNormal g σ) : 𝓀[L]) =
      g • (tameCharacter G 𝒪[L] σ : 𝓀[L]) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[L])
  have hσπ : Irreducible ((σ : G) • π) := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] σ)
  have hgπ : Irreducible (g • π) := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] g)
  -- Write `σ π = π u` with `u` a unit of `𝒪[L]`; then `(g σ g⁻¹) (g π) = (g π) (g u)`.
  set u : 𝒪[L] := (uniformizerChangeUnit π ((σ : G) • π) hπ hσπ : 𝒪[L])
  have hu : π * u = (σ : G) • π := mul_uniformizerChangeUnit π _ hπ hσπ
  have hgu : (MulAut.conjNormal g σ : G) • (g • π) = g • π * g • u := by
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_smul, ← hu, smul_mul']
  rw [coe_tameCharacter_of_smul_eq_mul hgπ hgu, coe_tameCharacter_of_smul_eq_mul hπ hu.symm,
    ResidueField.residue_smul]

/-- **The tame character twisted by a power map.** If `g ∈ G` acts on the residue field as the
`q`-th power map, then `theta_0(g σ g⁻¹) = theta_0(σ) ^ q` for every `σ ∈ G_0`. This applies with
`q` the cardinality of the residue field of a base field to any automorphism of a finite
extension inducing the arithmetic Frobenius on residue fields. -/
theorem tameCharacter_conj_of_smul_eq_pow {g : G} {q : ℕ} (hg : ∀ x : 𝓀[L], g • x = x ^ q)
    (σ : ramificationGroup G 𝒪[L] 0) :
    tameCharacter G 𝒪[L] (MulAut.conjNormal g σ) = tameCharacter G 𝒪[L] σ ^ q :=
  Units.ext (by rw [tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

/-- The equivariance of the tame character, read on the tame quotient `G_0/G_1`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj (g : G)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    (tameCharacterGraded G 𝒪[L] (ramificationGroupGradedConj G 𝒪[L] g 0 τ) : 𝓀[L]) =
      g • (tameCharacterGraded G 𝒪[L] τ : 𝓀[L]) := by
  induction τ using QuotientGroup.induction_on with
  | _ σ => rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

/-- The power-map twist of the tame character, read on the tame quotient `G_0/G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {g : G} {q : ℕ}
    (hg : ∀ x : 𝓀[L], g • x = x ^ q) (τ : RamificationGroupGraded G 𝒪[L] 0) :
    tameCharacterGraded G 𝒪[L] (ramificationGroupGradedConj G 𝒪[L] g 0 τ) =
      tameCharacterGraded G 𝒪[L] τ ^ q :=
  Units.ext (by rw [tameCharacterGraded_ramificationGroupGradedConj, hg,
    Units.val_pow_eq_pow_val])

end TauCeti
