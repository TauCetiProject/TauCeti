/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.CMTypeWeight
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Residue

/-!
# Critical pairs for characters of the norm-one torus

A critical pair consists of an automorphic character and a positive integer bounded by each
component of its negative weight. The weight and a tame presentation certify criticality; they
are not extra data in the pair. Lowering the integer keeps the same character and weight. This
is used to compare ratios at successive critical points of the same character.

The definitions follow `New.Data.CriticalPair` and `New.Data.CriticalPair.lowerPoint` in
`New/Derivatives/Field/ChosenPlaces.lean` and `New/OneLift/HeckeValues/TwistedRatio.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open NumberField IsDedekindDomain
open IsDedekindDomain.FiniteAdeleRing (integralUnits)
open TauCeti.GlobalNumberFields

namespace TauCeti

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

local notation "U" => MonoidHom.ker
  (ContinuousMonoidHom.toMonoidHom (ideleNormMap (maximalRealSubfield E) E))

/-- A critical point `z` for an automorphic character of weight `-c` and tame part supported on
`Q`, with `1 ≤ z ≤ t` and `z ≤ c(w) ≤ B` at every infinite place. The exponents are read in
the embeddings chosen by the CM type `Φ`. -/
@[ext]
structure CriticalPair (Φ : CMType E) (Q : Finset (HeightOneSpectrum (𝓞 E))) (t B : ℕ) where
  /-- The continuous character on the relative norm-one ideles. -/
  character : U →ₜ* Circle
  /-- The critical point. -/
  point : ℕ
  /-- The character is trivial on rational norm-one points. -/
  apply_principal (x : U) (hx : x.val ∈ IdeleGroup.principalSubgroup (𝓞 E) E) : character x = 1
  /-- The critical point is positive. -/
  point_pos : 0 < point
  /-- The critical point is at most the cutoff. -/
  point_le : point ≤ t
  /-- The character has an admissible weight and residue characters at the selected places. -/
  exists_presentation : ∃ (c : InfinitePlace E → ℕ)
    (ψ : (v : Q) → (IsLocalRing.ResidueField (v.val.adicCompletionIntegers E))ˣ →* Circle),
    (∀ w, point ≤ c w ∧ c w ≤ B) ∧
    ∀ (x : U) (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E),
      character x = Φ.normOneWeightCharacter (fun w ↦ -(c w : ℤ)) x *
        ∏ v : Q, ψ v (v.val.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩)

namespace CriticalPair

variable {Φ : CMType E} {Q : Finset (HeightOneSpectrum (𝓞 E))} {t B : ℕ}

/-- The nonnegative function whose negative is the character's archimedean weight. -/
noncomputable def negWeight (p : CriticalPair Φ Q t B) : InfinitePlace E → ℕ :=
  p.exists_presentation.choose

/-- Every component of the negative weight lies between the critical point and the weight bound. -/
theorem negWeight_mem_Icc (p : CriticalPair Φ Q t B) (w : InfinitePlace E) :
    p.negWeight w ∈ Set.Icc p.point B :=
  p.exists_presentation.choose_spec.choose_spec.1 w

/-- A critical pair has a tame presentation with its intrinsic negative weight. -/
theorem exists_residueCharacter (p : CriticalPair Φ Q t B) : ∃
    (ψ : (v : Q) → (IsLocalRing.ResidueField (v.val.adicCompletionIntegers E))ˣ →* Circle),
    ∀ (x : U) (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E),
      p.character x = Φ.normOneWeightCharacter (fun w ↦ -(p.negWeight w : ℤ)) x *
        ∏ v : Q, ψ v
          (v.val.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx⟩) := by
  obtain ⟨ψ, -, hψ⟩ := p.exists_presentation.choose_spec
  exact ⟨ψ, hψ⟩

/-- On ideles with trivial finite part, only the weight contributes to the character. -/
theorem character_apply_of_toFiniteIdele_eq_one (p : CriticalPair Φ Q t B) (x : U)
    (hx : IdeleGroup.toFiniteIdele (𝓞 E) E x.val = 1) :
    p.character x = Φ.normOneWeightCharacter (fun w ↦ -(p.negWeight w : ℤ)) x := by
  have hx' : IdeleGroup.toFiniteIdele (𝓞 E) E x.val ∈ integralUnits (𝓞 E) E :=
    hx ▸ (integralUnits (𝓞 E) E).one_mem
  have hone : (⟨IdeleGroup.toFiniteIdele (𝓞 E) E x.val, hx'⟩ : integralUnits (𝓞 E) E) = 1 :=
    Subtype.ext hx
  obtain ⟨ψ, hψ⟩ := p.exists_residueCharacter
  rw [hψ x hx']
  simp [hone]

/-- The negative weight is determined by the restriction of the character to ideles with
trivial finite part, even for pairs with different tame supports and bounds. -/
theorem negWeight_eq_of_character_eq_on_trivialFinite
    {Q' : Finset (HeightOneSpectrum (𝓞 E))} {t' B' : ℕ}
    (p : CriticalPair Φ Q t B) (p' : CriticalPair Φ Q' t' B')
    (h : ∀ x : U, IdeleGroup.toFiniteIdele (𝓞 E) E x.val = 1 → p.character x = p'.character x) :
    p.negWeight = p'.negWeight := by
  have hw : (fun w ↦ -(p.negWeight w : ℤ)) = (fun w ↦ -(p'.negWeight w : ℤ)) :=
    Φ.eq_of_normOneWeightCharacter_eq_on_trivialFinite (fun x hx ↦ by
      rw [← p.character_apply_of_toFiniteIdele_eq_one x hx,
        ← p'.character_apply_of_toFiniteIdele_eq_one x hx, h x hx])
  funext w
  exact_mod_cast neg_injective (congrFun hw w)

/-- A critical point can be lowered to any positive integer at most the original point. -/
def lowerPoint (p : CriticalPair Φ Q t B) (z : ℕ) (hz : 0 < z) (hzp : z ≤ p.point) :
    CriticalPair Φ Q t B where
  character := p.character
  point := z
  apply_principal := p.apply_principal
  point_pos := hz
  point_le := hzp.trans p.point_le
  exists_presentation := by
    obtain ⟨c, ψ, hc, hψ⟩ := p.exists_presentation
    exact ⟨c, ψ, fun w ↦ ⟨hzp.trans (hc w).1, (hc w).2⟩, hψ⟩

/-- Lowering a critical point leaves the character unchanged. -/
@[simp] theorem lowerPoint_character (p : CriticalPair Φ Q t B) (z : ℕ) (hz : 0 < z)
    (hzp : z ≤ p.point) : (p.lowerPoint z hz hzp).character = p.character := (rfl)

/-- The point of the lowered pair is the prescribed integer. -/
@[simp] theorem lowerPoint_point (p : CriticalPair Φ Q t B) (z : ℕ) (hz : 0 < z)
    (hzp : z ≤ p.point) : (p.lowerPoint z hz hzp).point = z := (rfl)

/-- Lowering a critical point leaves the negative weight unchanged. -/
@[simp] theorem lowerPoint_negWeight (p : CriticalPair Φ Q t B) (z : ℕ) (hz : 0 < z)
    (hzp : z ≤ p.point) : (p.lowerPoint z hz hzp).negWeight = p.negWeight :=
  (p.lowerPoint z hz hzp).negWeight_eq_of_character_eq_on_trivialFinite p fun x _ ↦ by simp

end CriticalPair

end TauCeti
