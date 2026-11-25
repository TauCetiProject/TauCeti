/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Complex.ArchimedeanCharacter
public import TauCeti.NumberTheory.ClassFieldTheory.WeilGroup.Archimedean.Basic
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Descent

/-!
# Characters of the real Weil group

The continuous characters of the real Weil group `W_ℝ = ℂˣ ⊔ jℂˣ` all factor through the norm
`W_ℝ → ℝˣ`, `z ↦ |z|²`, `j ↦ -1`, which identifies the abelianization of `W_ℝ` with `ℝˣ`. Since
the continuous characters of `ℝˣ` are the characters `x ↦ |x| ^ s * sgn(x) ^ ε`
(`TauCeti.realUnitsCharacterEquiv`), the continuous characters of `W_ℝ` are the pullbacks
`TauCeti.ClassFieldTheory.WeilGroupReal.character s ε`, for unique `s : ℂ` and `ε : ZMod 2`
(`TauCeti.ClassFieldTheory.WeilGroupReal.characterEquiv`). The pullback takes the value
`|z| ^ (2 * s)` at `z ∈ ℂˣ` and `(-1) ^ ε` at `j`; the factor two comes from the norm.

These are the one-dimensional continuous representations of `W_ℝ`, the first family in the
classification of its irreducible finite-dimensional continuous representations.

## Main definitions

* `TauCeti.ClassFieldTheory.WeilGroupReal.character s ε`: the character
  `w ↦ |norm w| ^ s * sgn(norm w) ^ ε` of `W_ℝ`.
* `TauCeti.ClassFieldTheory.WeilGroupReal.characterEquiv`: the continuous characters of `W_ℝ` are
  the characters `character s ε`, for unique `(s, ε)`.

## Main results

* `TauCeti.ClassFieldTheory.WeilGroupReal.exists_eq_comp_normHom`: every continuous homomorphism
  from `W_ℝ` to a commutative topological group factors through the norm.
* `TauCeti.ClassFieldTheory.WeilGroupReal.character_includeComplex`,
  `TauCeti.ClassFieldTheory.WeilGroupReal.character_j`: `character s ε` is `|z| ^ (2 * s)` on
  `z ∈ ℂˣ` and `(-1) ^ ε` at `j`.

## References

* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, §3, pp.401–403.
-/

public section

namespace TauCeti.ClassFieldTheory.WeilGroupReal

/-- **Continuous homomorphisms from `W_ℝ` to a commutative group factor through the norm.** The
kernel of the norm is the commutator subgroup, which every homomorphism into a commutative group
kills, and the norm is a quotient map. -/
theorem exists_eq_comp_normHom {A : Type*} [CommGroup A] [TopologicalSpace A]
    (χ : WeilGroupReal →ₜ* A) : ∃ ψ : ℝˣ →ₜ* A, χ = ψ.comp normHom := by
  have hker : (normHom : WeilGroupReal →* ℝˣ).ker ≤ (χ : WeilGroupReal →* A).ker :=
    ker_norm.trans_le (Group.Abelianization.commutator_le_ker _)
  exact ⟨.liftOfIsQuotientMap normHom isQuotientMap_norm χ hker,
    (ContinuousMonoidHom.liftOfIsQuotientMap_comp normHom isQuotientMap_norm χ hker).symm⟩

/-- **The character `w ↦ |norm w| ^ s * sgn(norm w) ^ ε` of `W_ℝ`**, the pullback along the norm of
the character `x ↦ |x| ^ s * sgn(x) ^ ε` of `ℝˣ`. Every continuous character of `W_ℝ` is one of
these (`TauCeti.ClassFieldTheory.WeilGroupReal.characterEquiv`). -/
noncomputable def character (s : ℂ) (ε : ZMod 2) : WeilGroupReal →ₜ* ℂˣ :=
  (realUnitsCharacter s ε).comp normHom

theorem character_apply (s : ℂ) (ε : ZMod 2) (w : WeilGroupReal) :
    character s ε w = realUnitsCharacter s ε (norm w) :=
  (rfl)

/-- On `z ∈ ℂˣ`, the character `character s ε` is `z ↦ |z| ^ (2 * s)`: the norm is `|z|²`, a
positive real number. -/
@[simp]
theorem character_includeComplex (s : ℂ) (ε : ZMod 2) (z : WeilGroupComplex) :
    character s ε (includeComplex z) = complexUnitsCharacter (2 * s) 0 z := by
  rw [character_apply, norm_includeComplex, realUnitsCharacter_map_normSq]

/-- At `j`, the character `character s ε` is `(-1) ^ ε`: the norm of `j` is `-1`. -/
@[simp]
theorem character_j (s : ℂ) (ε : ZMod 2) : (character s ε j : ℂ) = (-1) ^ ε.val := by
  rw [character_apply, norm_j, realUnitsCharacter_neg_one]

/-- Multiplying characters of `W_ℝ` adds their parameters. -/
@[simp]
theorem character_add (s t : ℂ) (ε η : ZMod 2) :
    character (s + t) (ε + η) = character s ε * character t η := by
  ext w
  simp [character_apply, ContinuousMonoidHom.mul_apply]

/-- **Every continuous character of `W_ℝ` is `character s ε`.** -/
theorem exists_eq_character (χ : WeilGroupReal →ₜ* ℂˣ) :
    ∃ (s : ℂ) (ε : ZMod 2), χ = character s ε := by
  obtain ⟨ψ, rfl⟩ := exists_eq_comp_normHom χ
  obtain ⟨s, ε, rfl⟩ := exists_eq_realUnitsCharacter ψ
  exact ⟨s, ε, rfl⟩

/-- The parameters of `character s ε` are determined by the character, since the norm is
surjective. -/
theorem character_injective2 : Function.Injective2 character := by
  intro s t ε η h
  refine realUnitsCharacter_injective2 (ContinuousMonoidHom.ext fun x ↦ ?_)
  obtain ⟨w, rfl⟩ := norm_surjective x
  exact DFunLike.congr_fun h w

@[simp]
theorem character_inj {s t : ℂ} {ε η : ZMod 2} :
    character s ε = character t η ↔ s = t ∧ ε = η :=
  character_injective2.eq_iff

/-- **Classification of the continuous characters of `W_ℝ`.** They are exactly the characters
`character s ε`, for unique `s : ℂ` and `ε : ZMod 2`, and multiplying characters adds their
parameters. -/
noncomputable def characterEquiv : Multiplicative (ℂ × ZMod 2) ≃* (WeilGroupReal →ₜ* ℂˣ) :=
  MulEquiv.ofBijective
    ({ toFun p := character p.toAdd.1 p.toAdd.2
       map_one' := by
         ext w
         simp [character_apply]
       map_mul' _ _ := character_add _ _ _ _ } : Multiplicative (ℂ × ZMod 2) →* _)
    ⟨character_injective2.uncurry.comp Multiplicative.toAdd.injective, fun χ ↦
      let ⟨s, ε, h⟩ := exists_eq_character χ
      ⟨.ofAdd (s, ε), h.symm⟩⟩

@[simp]
theorem characterEquiv_apply (s : ℂ) (ε : ZMod 2) :
    characterEquiv (.ofAdd (s, ε)) = character s ε :=
  (rfl)

@[simp]
theorem characterEquiv_symm_apply (s : ℂ) (ε : ZMod 2) :
    characterEquiv.symm (character s ε) = .ofAdd (s, ε) := by
  rw [MulEquiv.symm_apply_eq, characterEquiv_apply]

end TauCeti.ClassFieldTheory.WeilGroupReal
