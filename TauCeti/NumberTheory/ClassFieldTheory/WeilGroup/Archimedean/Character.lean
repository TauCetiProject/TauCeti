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

* `TauCeti.ClassFieldTheory.WeilGroupReal.compNormHomEquiv A`: precomposition with the norm
  identifies continuous homomorphisms `ℝˣ → A` with continuous homomorphisms `W_ℝ → A`, for any
  commutative topological group `A`.
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

/-- **Continuous homomorphisms from `W_ℝ` to a commutative group are those of `ℝˣ`.**
Precomposition with the norm identifies them: the kernel of the norm is the commutator subgroup,
which every homomorphism into a commutative group kills, and the norm is a quotient map. -/
noncomputable def compNormHomEquiv (A : Type*) [CommGroup A] [TopologicalSpace A] :
    (ℝˣ →ₜ* A) ≃ (WeilGroupReal →ₜ* A) :=
  (ContinuousMonoidHom.homEquivOfIsQuotientMap normHom isQuotientMap_normHom).trans <|
    Equiv.subtypeUnivEquiv fun χ ↦ by
      rw [toMonoidHom_normHom, ker_norm]
      exact Group.Abelianization.commutator_le_ker _

@[simp]
theorem compNormHomEquiv_apply {A : Type*} [CommGroup A] [TopologicalSpace A] (ψ : ℝˣ →ₜ* A) :
    compNormHomEquiv A ψ = ψ.comp normHom := by
  simp [compNormHomEquiv]

/-- The inverse of `compNormHomEquiv` is the factorization through the norm. -/
theorem compNormHomEquiv_symm_comp_normHom {A : Type*} [CommGroup A] [TopologicalSpace A]
    (χ : WeilGroupReal →ₜ* A) : ((compNormHomEquiv A).symm χ).comp normHom = χ := by
  rw [← compNormHomEquiv_apply, Equiv.apply_symm_apply]

@[simp]
theorem compNormHomEquiv_symm_apply_norm {A : Type*} [CommGroup A] [TopologicalSpace A]
    (χ : WeilGroupReal →ₜ* A) (w : WeilGroupReal) :
    (compNormHomEquiv A).symm χ (norm w) = χ w := by
  simpa using DFunLike.congr_fun (compNormHomEquiv_symm_comp_normHom χ) w

/-- **Continuous homomorphisms from `W_ℝ` to a commutative group factor through the norm.** -/
theorem exists_eq_comp_normHom {A : Type*} [CommGroup A] [TopologicalSpace A]
    (χ : WeilGroupReal →ₜ* A) : ∃ ψ : ℝˣ →ₜ* A, χ = ψ.comp normHom :=
  ⟨(compNormHomEquiv A).symm χ, (compNormHomEquiv_symm_comp_normHom χ).symm⟩

/-- **The character `w ↦ |norm w| ^ s * sgn(norm w) ^ ε` of `W_ℝ`**, the pullback along the norm of
the character `x ↦ |x| ^ s * sgn(x) ^ ε` of `ℝˣ`. Every continuous character of `W_ℝ` is one of
these (`TauCeti.ClassFieldTheory.WeilGroupReal.characterEquiv`). -/
noncomputable def character (s : ℂ) (ε : ZMod 2) : WeilGroupReal →ₜ* ℂˣ :=
  (realUnitsCharacter s ε).comp normHom

theorem character_apply (s : ℂ) (ε : ZMod 2) (w : WeilGroupReal) :
    character s ε w = realUnitsCharacter s ε (norm w) := by
  rw [character, ContinuousMonoidHom.coe_comp, Function.comp_apply, normHom_apply]

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

/-- **Classification of the continuous characters of `W_ℝ`.** They are exactly the characters
`character s ε`, for unique `s : ℂ` and `ε : ZMod 2`, and multiplying characters adds their
parameters: the classification `TauCeti.realUnitsCharacterEquiv` of the characters of `ℝˣ`,
followed by precomposition with the norm. -/
noncomputable def characterEquiv : Multiplicative (ℂ × ZMod 2) ≃* (WeilGroupReal →ₜ* ℂˣ) :=
  realUnitsCharacterEquiv.trans <| .mk' (compNormHomEquiv ℂˣ) fun ψ φ ↦ by
    ext w
    simp

@[simp]
theorem characterEquiv_apply (s : ℂ) (ε : ZMod 2) :
    characterEquiv (.ofAdd (s, ε)) = character s ε := by
  rw [characterEquiv, MulEquiv.trans_apply, realUnitsCharacterEquiv_apply]
  exact compNormHomEquiv_apply _

@[simp]
theorem characterEquiv_symm_apply (s : ℂ) (ε : ZMod 2) :
    characterEquiv.symm (character s ε) = .ofAdd (s, ε) := by
  rw [MulEquiv.symm_apply_eq, characterEquiv_apply]

/-- **Every continuous character of `W_ℝ` is `character s ε`.** -/
theorem exists_eq_character (χ : WeilGroupReal →ₜ* ℂˣ) :
    ∃ (s : ℂ) (ε : ZMod 2), χ = character s ε := by
  obtain ⟨p, rfl⟩ := characterEquiv.surjective χ
  exact ⟨p.toAdd.1, p.toAdd.2, characterEquiv_apply p.toAdd.1 p.toAdd.2⟩

/-- The parameters of `character s ε` are determined by the character. -/
theorem character_injective2 : Function.Injective2 character := fun s t ε η h ↦ by
  simpa using characterEquiv.injective <|
    (characterEquiv_apply s ε).trans (h.trans (characterEquiv_apply t η).symm)

@[simp]
theorem character_inj {s t : ℂ} {ε η : ZMod 2} :
    character s ε = character t η ↔ s = t ∧ ε = η :=
  character_injective2.eq_iff

end TauCeti.ClassFieldTheory.WeilGroupReal
