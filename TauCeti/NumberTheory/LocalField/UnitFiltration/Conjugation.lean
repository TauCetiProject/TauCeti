/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.RamificationGroup

/-!
# Conjugation on ramification quotients

Let a group `G` act on a nonarchimedean local field `L`, preserving its ring of integers.
Conjugation by an element `σ` of inertia acts on every ramification quotient `G_i/G_{i+1}`.
At depth zero this action is trivial. At positive depth, the embedding into the additive residue
field transforms by the `i`th power of the tame character:

`theta_i(σ τ σ⁻¹) = theta_0(σ)^i * theta_i(τ)`.

Here the positive-depth maps are read in the residue coordinate associated to a uniformizer.
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
  TauCeti.IsDiscreteValuationRing

namespace TauCeti

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]

/-- The change from `π` to `σ⁻¹ • π` is the inverse tame-character coordinate of `σ`. -/
private theorem residue_uniformizerChangeUnit_inv_smul
    (π π' : 𝒪[L]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (σ : ramificationGroup G 𝒪[L] 0) (hπ'eq : π' = (σ : G)⁻¹ • π) :
    residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) =
      ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) := by
  have ha : (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) * π =
      (σ⁻¹ : ramificationGroup G 𝒪[L] 0) • π := by
    rw [mul_comm, mul_uniformizerChangeUnit, hπ'eq]
    rfl
  calc
    residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L])
        = (tameCharacter hπ σ⁻¹ : ResidueField 𝒪[L]) :=
          (coe_tameCharacter_of_mul_eq hπ σ⁻¹ ha).symm
    _ = ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) := by
          rw [map_inv]
          exact Units.val_inv_eq_inv_val (tameCharacter hπ σ)

/-- Conjugation by inertia acts trivially on the tame quotient `G_0/G_1`. -/
@[simp]
theorem ramificationGroupGradedConj_zero
    (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    ramificationGroupGradedConj G 𝒪[L] (σ : G) 0 τ = τ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[L])
  apply TauCeti.ramificationGroupGradedToUnitFiltrationGraded_injective (i := 0) hπ
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    simp only [ramificationGroupGradedConj_mk]
    rw [TauCeti.ramificationGroupGradedToUnitFiltrationGraded_mk (i := 0),
      TauCeti.ramificationGroupGradedToUnitFiltrationGraded_mk (i := 0),
      ← TauCeti.ramificationGroupToUnitFiltrationGraded_apply (i := 0),
      ← TauCeti.ramificationGroupToUnitFiltrationGraded_apply (i := 0),
      MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
      mul_comm _ (TauCeti.ramificationGroupToUnitFiltrationGraded 0 hπ τ), mul_assoc,
      mul_inv_cancel, mul_one]

/-- The residue coordinate of a conjugate of `τ` at the uniformizer `π`: if `τ` moves `g⁻¹ • π` by
`y * (g⁻¹ • π) ^ (n + 2)`, then `g τ g⁻¹` moves `π` by `g • y * π ^ (n + 2)`. -/
private theorem ramificationGroupGradedToResidueField_conjNormal (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) (g : G) (τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) (y : 𝒪[L])
    (hy : (τ : G) • (g⁻¹ • π) - g⁻¹ • π = y * (g⁻¹ • π) ^ (n + 2)) :
    ramificationGroupGradedToResidueField G 𝒪[L] n π hπ
        (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g τ))) =
      residue 𝒪[L] (g • y) := by
  have hgπ' : g • g⁻¹ • π = π := by simp
  have hconjMove :
      ((MulAut.conjNormal g τ : ramificationGroup G 𝒪[L] ((n : ℤ) + 1)) : G) • π - π =
        g • y * π ^ (n + 2) := by
    calc
      _ = g • ((τ : G) • (g⁻¹ • π) - g⁻¹ • π) := by
        simp [MulAut.conjNormal_apply, mul_smul, smul_sub]
      _ = g • (y * (g⁻¹ • π) ^ (n + 2)) := by rw [hy]
      _ = g • y * π ^ (n + 2) := by rw [smul_mul', smul_pow', hgπ']
  exact ramificationGroupGradedToResidueField_of_smul_sub_eq n π hπ _ (g • y) hconjMove

/-- **The conjugation action formula on positive ramification quotients.** In the residue
coordinate determined by `π`, conjugation by `σ ∈ G_0` acts on `G_i/G_{i+1}` as
multiplication by `theta_0(σ)^i`, where `theta_0` is the tame character. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField G 𝒪[L] n π hπ
        (Additive.ofMul (ramificationGroupGradedConj G 𝒪[L]
          (σ : G) ((n : ℤ) + 1) τ)) =
      (tameCharacter hπ σ : IsLocalRing.ResidueField 𝒪[L]) ^ (n + 1) *
        ramificationGroupGradedToResidueField G 𝒪[L] n π hπ
          (Additive.ofMul τ) := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let π' : 𝒪[L] := g⁻¹ • π
    have hπ' : Irreducible π' := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] g⁻¹)
    have hmove : (τ : G) • π' - π' ∈ maximalIdeal 𝒪[L] ^ (n + 2) :=
      (mem_ramificationGroup_natCast_iff.mp τ.property) π'
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    -- First compute the coordinate of `τ` using the moved uniformizer `π' = g⁻¹ • π`.
    have hτcoord :
        ramificationGroupGradedToResidueField G 𝒪[L] n π' hπ'
            (Additive.ofMul (QuotientGroup.mk τ)) = residue 𝒪[L] y := by
      exact ramificationGroupGradedToResidueField_of_smul_sub_eq n π' hπ' τ y hy.symm
    have hconjCoord := ramificationGroupGradedToResidueField_conjNormal n π hπ g τ y hy.symm
    have hresidue : residue 𝒪[L] (g • y) = residue 𝒪[L] y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G 𝒪[L] σ.property y
    -- Changing back from `π'` to `π` contributes the inverse tame-character factor.
    have haResidue :
        residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) =
        ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) :=
      residue_uniformizerChangeUnit_inv_smul π π' hπ hπ' σ rfl
    have hchange' := ramificationGroupGradedToResidueField_change
      (G := G) n π π' hπ hπ' (QuotientGroup.mk τ)
    rw [haResidue] at hchange'
    simp only [ramificationGroupGradedConj_mk]
    rw [hconjCoord, hresidue, ← hτcoord]
    calc
      ramificationGroupGradedToResidueField G 𝒪[L] n π' hπ'
          (Additive.ofMul (QuotientGroup.mk τ)) =
          (tameCharacter hπ σ : ResidueField 𝒪[L]) ^ (n + 1) *
            (((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) ^
              (n + 1) *
                ramificationGroupGradedToResidueField G 𝒪[L] n π' hπ'
                  (Additive.ofMul (QuotientGroup.mk τ))) := by simp
      _ = (tameCharacter hπ σ : ResidueField 𝒪[L]) ^ (n + 1) *
            ramificationGroupGradedToResidueField G 𝒪[L] n π hπ
              (Additive.ofMul (QuotientGroup.mk τ)) := by rw [← hchange']

/-! ### Equivariance of the tame character -/

/-- **The tame character is equivariant.** For `g ∈ G` and `σ ∈ G_0`, the tame character of
`g σ g⁻¹` is the image of the tame character of `σ` under the automorphism of the residue field
induced by `g`: `theta_0(g σ g⁻¹) = g • theta_0(σ)`. -/
@[simp]
theorem tameCharacter_conj {π : 𝒪[L]} (hπ : Irreducible π) (g : G)
    (σ : ramificationGroup G 𝒪[L] 0) :
    (tameCharacter hπ (MulAut.conjNormal g σ) : 𝓀[L]) = g • (tameCharacter hπ σ : 𝓀[L]) := by
  have hσπ : Irreducible ((σ : G) • π) := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] σ)
  have hgπ : Irreducible (g • π) := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] g)
  -- Write `σ π = u π` with `u` a unit of `𝒪[L]`; then `(g σ g⁻¹) (g π) = (g u) (g π)`.
  set u : 𝒪[L] := (uniformizerChangeUnit π ((σ : G) • π) hπ hσπ : 𝒪[L])
  have hu : u * π = (σ : G) • π := by
    rw [mul_comm]
    exact mul_uniformizerChangeUnit π _ hπ hσπ
  have hgu : (g • u) * (g • π) = (MulAut.conjNormal g σ : G) • (g • π) := by
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_smul, ← smul_mul', hu]
  rw [congrArg (· (MulAut.conjNormal g σ)) (tameCharacter_eq_of_irreducible hπ hgπ),
    coe_tameCharacter_of_mul_eq hgπ _ hgu,
    coe_tameCharacter_of_mul_eq hπ σ hu, ResidueField.residue_smul]

/-- **The tame character twisted by a power map.** If `g ∈ G` acts on the residue field as the
`q`-th power map, then `theta_0(g σ g⁻¹) = theta_0(σ) ^ q` for every `σ ∈ G_0`. This applies with
`q` the cardinality of the residue field of a base field to any automorphism of a finite
extension inducing the arithmetic Frobenius on residue fields. -/
theorem tameCharacter_conj_of_smul_eq_pow {π : 𝒪[L]} (hπ : Irreducible π) {g : G} {q : ℕ}
    (hg : ∀ x : 𝓀[L], g • x = x ^ q) (σ : ramificationGroup G 𝒪[L] 0) :
    tameCharacter hπ (MulAut.conjNormal g σ) = tameCharacter hπ σ ^ q :=
  Units.ext (by rw [tameCharacter_conj, hg, Units.val_pow_eq_pow_val])

/-- The equivariance of the tame character, read on the tame quotient `G_0/G_1`. -/
@[simp]
theorem tameCharacterGraded_ramificationGroupGradedConj {π : 𝒪[L]} (hπ : Irreducible π) (g : G)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    (tameCharacterGraded hπ (ramificationGroupGradedConj G 𝒪[L] g 0 τ) : 𝓀[L]) =
      g • (tameCharacterGraded hπ τ : 𝓀[L]) := by
  induction τ using QuotientGroup.induction_on with
  | _ σ => rw [ramificationGroupGradedConj_mk, tameCharacterGraded_mk, tameCharacterGraded_mk,
      tameCharacter_conj]

/-- The power-map twist of the tame character, read on the tame quotient `G_0/G_1`. -/
theorem tameCharacterGraded_ramificationGroupGradedConj_of_smul_eq_pow {π : 𝒪[L]}
    (hπ : Irreducible π)
    {g : G} {q : ℕ} (hg : ∀ x : 𝓀[L], g • x = x ^ q) (τ : RamificationGroupGraded G 𝒪[L] 0) :
    tameCharacterGraded hπ (ramificationGroupGradedConj G 𝒪[L] g 0 τ) =
      tameCharacterGraded hπ τ ^ q :=
  Units.ext (by rw [tameCharacterGraded_ramificationGroupGradedConj, hg,
    Units.val_pow_eq_pow_val])

end TauCeti
