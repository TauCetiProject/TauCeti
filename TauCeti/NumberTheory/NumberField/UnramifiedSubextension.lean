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
import TauCeti.RingTheory.Unramified.AlgEquiv
import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure

/-!
# Unramifiedness in subextensions

Let `K` be a number field and `Ω` an arbitrary extension of `K`. This file compares
unramifiedness of an ideal `p` of `𝓞 K` in the finite subextensions of `Ω / K`:

* `IntermediateField.isUnramifiedIn_map_iff`: `p` is unramified in a conjugate `σ L` exactly when
  it is unramified in `L`;
* `IntermediateField.isUnramifiedIn_sup_iff`: `p` is unramified in a compositum `L₁ ⊔ L₂` exactly
  when it is unramified in `L₁` and in `L₂`;
* `IntermediateField.isUnramifiedIn_of_le`: unramifiedness descends to subextensions;
* `IntermediateField.isUnramifiedIn_bot`: every finite place is unramified in `⊥`.

Unramifiedness is invariant under isomorphisms of extensions (`AlgEquiv.isUnramifiedIn_iff`,
applied to `NumberField.RingOfIntegers.mapAlgEquiv`). The compositum statement moves the fields
into an algebraic closure of `L₁ ⊔ L₂`, where they lie in a finite Galois extension of `K`, and
there reads unramifiedness on inertia groups (`Ideal.isUnramifiedIn_sup_iff`).
-/

public section

open IsDedekindDomain Module

open scoped NumberField

open NumberField.RingOfIntegers (mapAlgEquiv)

namespace IntermediateField

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

omit [NumberField K] in
/-- **Unramifiedness in a conjugate field.** For `σ : Ω →ₐ[K] Ω`, a place is unramified in
`σ L` exactly when it is unramified in `L`. -/
theorem isUnramifiedIn_map_iff (L : IntermediateField K Ω) (σ : Ω →ₐ[K] Ω) (p : Ideal (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 (L.map σ)) p ↔ Algebra.IsUnramifiedIn (𝓞 L) p :=
  (mapAlgEquiv (L.equivMap σ)).isUnramifiedIn_iff p |>.symm

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
  have hsup : restrict h = restrict h₁ ⊔ restrict h₂ :=
    lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_restrict])
  rw [(mapAlgEquiv (restrictAlgEquiv h)).isUnramifiedIn_iff,
    (mapAlgEquiv (restrictAlgEquiv h₁)).isUnramifiedIn_iff,
    (mapAlgEquiv (restrictAlgEquiv h₂)).isUnramifiedIn_iff, hsup, Ideal.isUnramifiedIn_sup_iff]

/-- **Unramifiedness in a compositum.** For finite subextensions `L₁` and `L₂` of `Ω / K`, an
ideal of `𝓞 K` is unramified in `L₁ ⊔ L₂` exactly when it is unramified in `L₁` and in `L₂`.
The fields are moved into an algebraic closure `Ω'` of `L₁ ⊔ L₂`, which is Galois over `K`. -/
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
  have hsup : restrict (le_refl E) = restrict h₁ ⊔ restrict h₂ :=
    lift_injective _ (by rw [lift_sup, lift_restrict, lift_restrict, lift_restrict])
  rw [(mapAlgEquiv (e (le_refl E))).isUnramifiedIn_iff,
    (mapAlgEquiv (e h₁)).isUnramifiedIn_iff, (mapAlgEquiv (e h₂)).isUnramifiedIn_iff, hsup,
    IntermediateField.map_sup, isUnramifiedIn_sup_iff_of_isGalois]

/-- **Unramifiedness descends to subextensions.** For `L ≤ E` with `E` finite over `K`, an ideal of
`𝓞 K` unramified in `E` is unramified in `L`. -/
theorem isUnramifiedIn_of_le {L E : IntermediateField K Ω} (h : L ≤ E)
    [FiniteDimensional K E] {p : Ideal (𝓞 K)} (hE : Algebra.IsUnramifiedIn (𝓞 E) p) :
    Algebra.IsUnramifiedIn (𝓞 L) p := by
  have : FiniteDimensional K L :=
    .of_injective (inclusion h).toLinearMap (inclusion h).injective
  rw [← sup_eq_right.2 h, isUnramifiedIn_sup_iff] at hE
  exact hE.1

variable (K Ω) in
/-- **The bottom field is unramified outside every set of places.** -/
theorem isUnramifiedIn_bot (v : HeightOneSpectrum (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 (⊥ : IntermediateField K Ω)) v.asIdeal := by
  rw [(mapAlgEquiv (botEquiv K Ω)).isUnramifiedIn_iff]
  intro Q _ _
  refine TauCeti.NumberField.isUnramifiedAway_ramifiedSupport (K := K) (L := K) v ?_ Q
  rw [TauCeti.NumberField.ramifiedSupport_self]
  exact Finset.notMem_empty v

end IntermediateField
