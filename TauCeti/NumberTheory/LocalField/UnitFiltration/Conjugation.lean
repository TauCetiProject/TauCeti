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

namespace TauCeti

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]
variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- Coercion from the invariant integer ring to the ambient field respects the group action. -/
private theorem coe_smul_integer (g : G) (x : 𝒪[L]) :
    ((g • x : 𝒪[L]) : L) = g • (x : L) :=
  map_smul (IsInvariantSubring.subtypeHom G 𝒪[L]) g x

/-- The change from `π` to `g⁻¹ • π` is the inverse tame-character coordinate of `g`. -/
private theorem residue_uniformizerChangeUnit_inv_smul
    (π π' : 𝒪[L]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (σ : ramificationGroup G 𝒪[L] 0)
    (hπ'coe : (π' : L) = (σ : G)⁻¹ • (π : L)) :
    residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) =
      ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) := by
  let a := uniformizerChangeUnit π π' hπ hπ'
  have hπ0 : (π : L) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have haRing := mul_uniformizerChangeUnit π π' hπ hπ'
  have haField : (π : L) * ((a : 𝒪[L]) : L) = (π' : L) := by
    exact congrArg (fun z : 𝒪[L] ↦ (z : L)) haRing
  have ha : ((a : 𝒪[L]) : L) = (σ : G)⁻¹ • (π : L) / (π : L) := by
    apply mul_left_cancel₀ hπ0
    rw [mul_div_cancel₀ _ hπ0, ← hπ'coe]
    exact haField
  calc
    residue 𝒪[L] (a : 𝒪[L]) =
        (tameCharacter hπ σ⁻¹ : ResidueField 𝒪[L]) :=
      (coe_tameCharacter_of_val_eq_smul_div hπ σ⁻¹ ha).symm
    _ = ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ :
        ResidueField 𝒪[L]) := by
      rw [map_inv]
      exact Units.val_inv_eq_inv_val (tameCharacter hπ σ)

/-- Conjugation by inertia acts trivially on the tame quotient `G_0/G_1`. -/
@[simp]
theorem ramificationGroupGradedConj_zero
    (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] 0) :
    ramificationGroupGradedConj G 𝒪[L] (σ : G) 0 τ = τ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[L])
  apply tameCharacterGraded_injective hπ
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    simp only [ramificationGroupGradedConj_mk, tameCharacterGraded_mk]
    rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
      mul_comm (tameCharacter hπ σ) (tameCharacter hπ τ), mul_assoc, mul_inv_cancel,
      mul_one]

/-- **The conjugation action formula on positive ramification quotients.** In the residue
coordinate determined by `π`, conjugation by `σ ∈ G_0` acts on `G_i/G_{i+1}` as
multiplication by `theta_0(σ)^i`, where `theta_0` is the tame character. -/
@[simp]
theorem ramificationGroupGradedToResidueField_conj (n : ℕ) (π : 𝒪[L])
    (hπ : Irreducible π) (σ : ramificationGroup G 𝒪[L] 0)
    (τ : RamificationGroupGraded G 𝒪[L] ((n : ℤ) + 1)) :
    ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
        (Additive.ofMul (ramificationGroupGradedConj G 𝒪[L]
          (σ : G) ((n : ℤ) + 1) τ)) =
      (tameCharacter hπ σ : IsLocalRing.ResidueField 𝒪[L]) ^ (n + 1) *
        ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
          (Additive.ofMul τ) := by
  induction τ using QuotientGroup.induction_on with
  | _ τ =>
    let g : G := σ
    let π' : 𝒪[L] := g⁻¹ • π
    have hπ' : Irreducible π' := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] g⁻¹)
    have hmove : (τ : G) • π' - π' ∈ maximalIdeal 𝒪[L] ^ (n + 2) :=
      (mem_ramificationGroup_natCast_iff.mp τ.2) π'
    rw [hπ'.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmove
    obtain ⟨y, hy⟩ := hmove
    -- First compute the coordinate of `τ` using the moved uniformizer `π' = g⁻¹ • π`.
    have hτcoord :
        ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
            (Additive.ofMul (QuotientGroup.mk τ)) = residue 𝒪[L] y := by
      exact ramificationGroupGradedToResidueField_of_smul_sub_eq n π' hπ' τ y hy.symm
    let τ' : ramificationGroup G 𝒪[L] ((n : ℤ) + 1) :=
      MulAut.conjNormal g τ
    have hgπ' : g • π' = π := by simp [π', g]
    -- Conjugating transports the displacement coefficient `y` to `g • y`.
    have hconjMove : (τ' : G) • π - π = g • y * π ^ (n + 2) := by
      calc
        (τ' : G) • π - π = g • ((τ : G) • π' - π') := by
          simp [τ', π', g, MulAut.conjNormal_apply, mul_smul, smul_sub]
        _ = g • (y * π' ^ (n + 2)) := by rw [hy]
        _ = g • y * π ^ (n + 2) := by rw [smul_mul', smul_pow', hgπ']
    have hconjCoord :
        ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
            (Additive.ofMul (QuotientGroup.mk τ')) = residue 𝒪[L] (g • y) := by
      exact ramificationGroupGradedToResidueField_of_smul_sub_eq n π hπ τ' (g • y) hconjMove
    have hresidue : residue 𝒪[L] (g • y) = residue 𝒪[L] y :=
      residue_smul_eq_of_mem_ramificationGroup_zero G 𝒪[L] σ.2 y
    -- Changing back from `π'` to `π` contributes the inverse tame-character factor.
    have hπ'coe : (π' : L) = (σ : G)⁻¹ • (π : L) := by
      simpa only [π', g] using coe_smul_integer ((σ : G)⁻¹) π
    have haResidue :
        residue 𝒪[L] (uniformizerChangeUnit π π' hπ hπ' : 𝒪[L]) =
        ((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) := by
      exact residue_uniformizerChangeUnit_inv_smul π π' hπ hπ' σ hπ'coe
    have hchange' := ramificationGroupGradedToResidueField_change
      (G := G) n π π' hπ hπ' (QuotientGroup.mk τ)
    rw [haResidue] at hchange'
    have hconjCoord' :
        ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
            (Additive.ofMul (QuotientGroup.mk (MulAut.conjNormal g τ))) =
          residue 𝒪[L] (g • y) := by
      simpa only [τ'] using hconjCoord
    simp only [ramificationGroupGradedConj_mk]
    rw [hconjCoord', hresidue, ← hτcoord]
    calc
      ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
          (Additive.ofMul (QuotientGroup.mk τ)) =
          (tameCharacter hπ σ : ResidueField 𝒪[L]) ^ (n + 1) *
            (((tameCharacter hπ σ : (ResidueField 𝒪[L])ˣ)⁻¹ : ResidueField 𝒪[L]) ^
              (n + 1) *
                ramificationGroupGradedToResidueField (G := G) (L := L) n π' hπ'
                  (Additive.ofMul (QuotientGroup.mk τ))) := by simp
      _ = (tameCharacter hπ σ : ResidueField 𝒪[L]) ^ (n + 1) *
            ramificationGroupGradedToResidueField (G := G) (L := L) n π hπ
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
  have hπ0 : (π : L) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hgπ0 : ((g • π : 𝒪[L]) : L) ≠ 0 := fun h ↦ hgπ.ne_zero (Subtype.ext h)
  -- Write `σ π = π u` with `u` a unit of `𝒪[L]`; then `(g σ g⁻¹) (g π) = (g π) (g u)`.
  set u : 𝒪[L] := (uniformizerChangeUnit π ((σ : G) • π) hπ hσπ : 𝒪[L])
  have hu : π * u = (σ : G) • π := mul_uniformizerChangeUnit π _ hπ hσπ
  have hgu : (MulAut.conjNormal g σ : G) • (g • π) = g • π * g • u := by
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, inv_smul_smul, ← hu, smul_mul']
  have hσ : (u : L) = (σ : G) • (π : L) / (π : L) := by
    rw [eq_div_iff hπ0, mul_comm, ← coe_smul_integer, ← hu, MulMemClass.coe_mul]
  have hconj : ((g • u : 𝒪[L]) : L) =
      (MulAut.conjNormal g σ : G) • ((g • π : 𝒪[L]) : L) / ((g • π : 𝒪[L]) : L) := by
    rw [eq_div_iff hgπ0, mul_comm, ← coe_smul_integer, hgu, MulMemClass.coe_mul]
  rw [congrArg (· (MulAut.conjNormal g σ)) (tameCharacter_eq_of_irreducible hπ hgπ),
    coe_tameCharacter_of_val_eq_smul_div hgπ _ hconj,
    coe_tameCharacter_of_val_eq_smul_div hπ σ hσ, ResidueField.residue_smul]

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
