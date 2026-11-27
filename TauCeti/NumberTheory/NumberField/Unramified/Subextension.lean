/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.FieldTheory.IntermediateField.Lift
import TauCeti.RingTheory.Unramified.AlgEquiv
import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure

/-!
# Unramifiedness in subextensions

Let `K` be a number field and `Ω` an arbitrary extension of `K`. This file compares
unramifiedness of an ideal `p` of `𝓞 K` in the finite subextensions of `Ω / K`:

* `IntermediateField.isUnramifiedIn_restrict_iff`: unramifiedness in `L` does not depend on the
  intermediate field `E ≥ L` in which `L` is viewed;
* `IntermediateField.isUnramifiedIn_sup_iff`: `p` is unramified in a compositum `L₁ ⊔ L₂` exactly
  when it is unramified in `L₁` and in `L₂`;
* `IntermediateField.isUnramifiedIn_of_le`: unramifiedness descends to subextensions;
* `IntermediateField.isUnramifiedIn_bot`: every ideal of `𝓞 K` is unramified in `⊥`.

Invariance under `K`-embeddings, in particular under conjugation, is
`Ideal.isUnramifiedIn_map_iff`. Together these show that the finite subextensions of `Ω / K`
unramified outside a set of places are closed under composita, subextensions and conjugation, and
contain `⊥`: this is what the compositum `TauCeti.RestrictedRamification.maxUnramifiedOutside` of
these subextensions needs.
-/

public section

open Module

open scoped NumberField

open NumberField.RingOfIntegers (mapAlgEquiv)

namespace IntermediateField

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

omit [NumberField K] in
/-- **Unramifiedness does not depend on the ambient field.** For `L ≤ E`, an ideal of `𝓞 K` is
unramified in `L` viewed as a subextension of `E` exactly when it is unramified in `L`. -/
theorem isUnramifiedIn_restrict_iff {L E : IntermediateField K Ω} (h : L ≤ E) (p : Ideal (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 (restrict h)) p ↔ Algebra.IsUnramifiedIn (𝓞 L) p :=
  ((mapAlgEquiv (restrictAlgEquiv h)).isUnramifiedIn_iff p).symm

/-- Unramifiedness in a compositum, inside a Galois extension `Ω / K`: the three fields are compared
inside the normal closure of `L₁ ⊔ L₂`, a finite Galois extension of `K`, where unramifiedness is
read on inertia groups. -/
private theorem isUnramifiedIn_sup_iff_of_isGalois [IsGalois K Ω] (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] (p : Ideal (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(L₁ ⊔ L₂)) p ↔
      Algebra.IsUnramifiedIn (𝓞 L₁) p ∧ Algebra.IsUnramifiedIn (𝓞 L₂) p := by
  set M := normalClosure K ↥(L₁ ⊔ L₂) Ω
  have : NumberField M := NumberField.of_module_finite K M
  have h : L₁ ⊔ L₂ ≤ M := le_normalClosure _
  have h₁ : L₁ ≤ M := le_sup_left.trans h
  have h₂ : L₂ ≤ M := le_sup_right.trans h
  calc Algebra.IsUnramifiedIn (𝓞 ↥(L₁ ⊔ L₂)) p
      ↔ Algebra.IsUnramifiedIn (𝓞 ↥(restrict h₁ ⊔ restrict h₂)) p := by
        rw [← restrict_sup, isUnramifiedIn_restrict_iff]
    _ ↔ _ := Ideal.isUnramifiedIn_sup_iff p _ _
    _ ↔ _ := and_congr (isUnramifiedIn_restrict_iff h₁ p) (isUnramifiedIn_restrict_iff h₂ p)

/-- **Unramifiedness in a compositum.** For finite subextensions `L₁` and `L₂` of `Ω / K`, an
ideal of `𝓞 K` is unramified in `L₁ ⊔ L₂` exactly when it is unramified in `L₁` and in `L₂`. -/
theorem isUnramifiedIn_sup_iff (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] (p : Ideal (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(L₁ ⊔ L₂)) p ↔
      Algebra.IsUnramifiedIn (𝓞 L₁) p ∧ Algebra.IsUnramifiedIn (𝓞 L₂) p := by
  set E := L₁ ⊔ L₂
  let Ω' := AlgebraicClosure E
  have : IsAlgClosure K Ω' := ⟨inferInstance, .trans K E Ω'⟩
  let ι : E →ₐ[K] Ω' := IsScalarTower.toAlgHom K E Ω'
  have h₁ : L₁ ≤ E := le_sup_left
  have h₂ : L₂ ≤ E := le_sup_right
  -- `L ≤ E` is isomorphic to its image in `Ω'`
  let e {L : IntermediateField K Ω} (h : L ≤ E) : L ≃ₐ[K] (restrict h).map ι :=
    (restrictAlgEquiv h).trans ((restrict h).equivMap ι)
  have : FiniteDimensional K ((restrict h₁).map ι) := (e h₁).toLinearEquiv.finiteDimensional
  have : FiniteDimensional K ((restrict h₂).map ι) := (e h₂).toLinearEquiv.finiteDimensional
  -- unramifiedness in `L ≤ E` is read on the image of `L` in `Ω'`
  have key {L : IntermediateField K Ω} (h : L ≤ E) :
      Algebra.IsUnramifiedIn (𝓞 ↥((restrict h).map ι)) p ↔ Algebra.IsUnramifiedIn (𝓞 L) p :=
    (Ideal.isUnramifiedIn_map_iff p _ ι).trans (isUnramifiedIn_restrict_iff h p)
  calc Algebra.IsUnramifiedIn (𝓞 E) p
      ↔ Algebra.IsUnramifiedIn (𝓞 ↥((restrict h₁).map ι ⊔ (restrict h₂).map ι)) p := by
        rw [← IntermediateField.map_sup, ← restrict_sup, key]
    _ ↔ _ := isUnramifiedIn_sup_iff_of_isGalois _ _ p
    _ ↔ _ := and_congr (key h₁) (key h₂)

/-- **Unramifiedness descends to subextensions.** For `L ≤ E` with `E` finite over `K`, an ideal of
`𝓞 K` unramified in `E` is unramified in `L`. -/
theorem isUnramifiedIn_of_le {L E : IntermediateField K Ω} (h : L ≤ E)
    [FiniteDimensional K E] {p : Ideal (𝓞 K)} (hE : Algebra.IsUnramifiedIn (𝓞 E) p) :
    Algebra.IsUnramifiedIn (𝓞 L) p := by
  have : FiniteDimensional K L :=
    .of_injective (inclusion h).toLinearMap (inclusion h).injective
  rw [← sup_eq_right.2 h, isUnramifiedIn_sup_iff] at hE
  exact hE.1

omit [NumberField K] in
variable (K Ω) in
/-- **The bottom field is unramified.** Every ideal of `𝓞 K` is unramified in `⊥`. -/
@[simp]
theorem isUnramifiedIn_bot (p : Ideal (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 (⊥ : IntermediateField K Ω)) p := by
  intro Q _ _
  have : Algebra.FormallyUnramified (𝓞 K) (𝓞 (⊥ : IntermediateField K Ω)) :=
    .of_surjective (Algebra.ofId (𝓞 K) _) (mapAlgEquiv (botEquiv K Ω)).symm.surjective
  exact inferInstance

end IntermediateField
