/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.NumberTheory.NumberField.AlgEquiv
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Hermite
import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure

/-!
# The maximal extension unramified outside a set of places

Let `K` be a number field, `Ω` an extension of `K` and `S` a set of finite places of `K`. A finite
subextension `L` of `Ω / K` is *unramified outside `S`* when every place `v ∉ S` is unramified in
`𝓞 L`, in the sense of Mathlib's `Algebra.IsUnramifiedIn`; archimedean places impose nothing. As
in the roadmap, this quantified statement is used directly and no wrapper predicate is defined.

This file defines the compositum `K_S` of these subextensions,
`TauCeti.RestrictedRamification.maxUnramifiedOutside`, and its Galois group
`G_{K,S} = Gal(K_S / K)`, `TauCeti.RestrictedRamification.galoisGroupS`, with its Krull topology.
When `Ω` is a separable closure of `K`, `K_S` is the maximal extension of `K` unramified outside
`S`.

Unramifiedness at a place `v` is read on the inertia groups of a finite Galois extension containing
the fields in question (`Ideal.isUnramifiedIn_iff_forall_inertia_le`), so it passes to composita
and subextensions. It is also invariant under isomorphisms of extensions, in particular under
conjugation by `Gal(Ω / K)`. So a finite subextension lies in `K_S` exactly when it is
unramified outside `S`, and `K_S / K` is Galois when `Ω / K` is normal.

For finite `S`, Hermite's theorem
`TauCeti.NumberField.finite_of_finrank_le_of_ramifiedSupport_subset` says that only finitely many
subextensions of bounded degree are unramified outside `S`.

## Main definitions

* `TauCeti.RestrictedRamification.maxUnramifiedOutside`: the compositum `K_S` in `Ω` of the finite
  subextensions of `Ω / K` unramified outside `S`.
* `TauCeti.RestrictedRamification.galoisGroupS`: `G_{K,S} = Gal(K_S / K)`.

## Main results

* `TauCeti.RestrictedRamification.isUnramifiedIn_sup_iff`: a place is unramified in a compositum
  of finite subextensions exactly when it is unramified in both.
* `TauCeti.RestrictedRamification.le_maxUnramifiedOutside_iff`: a finite subextension lies in
  `K_S` exactly when it is unramified outside `S`.
* `TauCeti.RestrictedRamification.isGalois_maxUnramifiedOutside`: `K_S / K` is Galois.
* `TauCeti.RestrictedRamification.finite_unramifiedOutside_of_finrank_le`: Hermite's theorem, for
  finite `S` there are finitely many subextensions of bounded degree unramified outside `S`.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
-/

public section

open IntermediateField IsDedekindDomain Module

open scoped NumberField

namespace TauCeti.RestrictedRamification

variable (K Ω : Type*) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

/-- **The maximal extension unramified outside `S`.** `K_S` is the compositum in `Ω` of the
finite subextensions `L / K` that are unramified at every finite place `v ∉ S`, in the sense of
Mathlib's `Algebra.IsUnramifiedIn`: every prime of `𝓞 L` over `v` is unramified. Infinite places
impose nothing. -/
noncomputable def maxUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K Ω :=
  ⨆ (L : IntermediateField K Ω) (_ : FiniteDimensional K L)
    (_ : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal), L

omit [NumberField K] in
/-- The definition of `K_S` as a compositum. -/
theorem maxUnramifiedOutside_def (S : Set (HeightOneSpectrum (𝓞 K))) :
    maxUnramifiedOutside K Ω S = ⨆ (L : IntermediateField K Ω) (_ : FiniteDimensional K L)
      (_ : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal), L :=
  (rfl)

/-- **The Galois group `G_{K,S}`** of the maximal extension `K_S` of `K` unramified outside `S`,
with its Krull topology. -/
abbrev galoisGroupS (S : Set (HeightOneSpectrum (𝓞 K))) :=
  maxUnramifiedOutside K Ω S ≃ₐ[K] maxUnramifiedOutside K Ω S

variable {K Ω}

omit [NumberField K] in
/-- A finite subextension unramified outside `S` lies in `K_S`. -/
theorem le_maxUnramifiedOutside {S : Set (HeightOneSpectrum (𝓞 K))} {L : IntermediateField K Ω}
    [FiniteDimensional K L] (hL : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) :
    L ≤ maxUnramifiedOutside K Ω S := by
  rw [maxUnramifiedOutside_def]
  exact le_iSup₂_of_le L ‹_› (le_iSup_of_le hL le_rfl)

omit [NumberField K] in
/-- **Enlarging `S` enlarges `K_S`.** -/
theorem maxUnramifiedOutside_mono {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') :
    maxUnramifiedOutside K Ω S ≤ maxUnramifiedOutside K Ω S' :=
  iSup₂_le fun _ _ ↦ iSup_le fun hL ↦ le_maxUnramifiedOutside fun v hv ↦ hL v (mt (@h v) hv)

omit [NumberField K] in
/-- **Unramifiedness in a conjugate field.** For `σ : Ω →ₐ[K] Ω`, a place is unramified in
`σ L` exactly when it is unramified in `L`. -/
theorem isUnramifiedIn_map_iff (L : IntermediateField K Ω) (σ : Ω →ₐ[K] Ω) (p : Ideal (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 (L.map σ)) p ↔ Algebra.IsUnramifiedIn (𝓞 L) p :=
  (L.equivMap σ).isUnramifiedIn_iff p |>.symm

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
  rw [(restrictAlgEquiv h).isUnramifiedIn_iff, (restrictAlgEquiv h₁).isUnramifiedIn_iff,
    (restrictAlgEquiv h₂).isUnramifiedIn_iff, hsup, Ideal.isUnramifiedIn_sup_iff]

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
  rw [(e (le_refl E)).isUnramifiedIn_iff, (e h₁).isUnramifiedIn_iff, (e h₂).isUnramifiedIn_iff,
    hsup, IntermediateField.map_sup, isUnramifiedIn_sup_iff_of_isGalois]

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
  rw [(botEquiv K Ω).isUnramifiedIn_iff]
  intro Q _ _
  refine TauCeti.NumberField.isUnramifiedAway_ramifiedSupport (K := K) (L := K) v ?_ Q
  rw [TauCeti.NumberField.ramifiedSupport_self]
  exact Finset.notMem_empty v

/-- **The finite subextensions of `K_S`.** A finite subextension `L` of `Ω / K` lies in `K_S`
exactly when it is unramified at every finite place outside `S`. -/
theorem le_maxUnramifiedOutside_iff {S : Set (HeightOneSpectrum (𝓞 K))}
    {L : IntermediateField K Ω} [FiniteDimensional K L] :
    L ≤ maxUnramifiedOutside K Ω S ↔ ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  refine ⟨fun hL ↦ ?_, le_maxUnramifiedOutside⟩
  -- the generating family, indexed by a subtype
  let ι := {E : IntermediateField K Ω //
    FiniteDimensional K E ∧ ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal}
  let f : ι → IntermediateField K Ω := fun E ↦ E.1
  replace hL : L ≤ ⨆ E, f E := hL.trans <| iSup₂_le fun E hE ↦ iSup_le fun hE' ↦
    le_iSup_of_le (f := f) ⟨E, hE, hE'⟩ le_rfl
  -- `L` is finitely generated, hence a compact element, so it lies in a finite subcompositum
  obtain ⟨t, rfl⟩ : ∃ t : Finset Ω, adjoin K (t : Set Ω) = L :=
    (essFiniteType_iff.1 inferInstance).imp fun _ h ↦ h
  obtain ⟨s, hs⟩ := (adjoin_finset_isCompactElement t).exists_finset_of_le_iSup _ hL
  intro v hv
  suffices FiniteDimensional K ↥(⨆ E ∈ s, f E) ∧
      Algebra.IsUnramifiedIn (𝓞 ↥(⨆ E ∈ s, f E)) v.asIdeal by
    obtain ⟨_, h⟩ := this
    exact isUnramifiedIn_of_le hs h
  clear hs hL
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [show ⨆ E ∈ (∅ : Finset ι), f E = ⊥ by simp]
    exact ⟨inferInstance, isUnramifiedIn_bot K Ω v⟩
  | insert E s _ ih =>
    rw [Finset.iSup_insert]
    have := E.2.1
    have := ih.1
    exact ⟨inferInstance, (isUnramifiedIn_sup_iff _ _ _).2 ⟨E.2.2 v hv, ih.2⟩⟩

/-- **`K_S / K` is Galois** when `Ω / K` is normal: conjugation by `Gal(Ω / K)` permutes the finite
subextensions unramified outside `S`. -/
theorem isGalois_maxUnramifiedOutside [Normal K Ω] (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsGalois K (maxUnramifiedOutside K Ω S) := by
  have : Normal K (maxUnramifiedOutside K Ω S) := by
    refine normal_iff_forall_map_le'.2 fun σ ↦ ?_
    rw [maxUnramifiedOutside_def, IntermediateField.map_iSup]
    refine iSup_le fun L ↦ ?_
    rw [IntermediateField.map_iSup]
    refine iSup_le fun _ ↦ ?_
    rw [IntermediateField.map_iSup]
    refine iSup_le fun hL ↦ ?_
    have : FiniteDimensional K (L.map (σ : Ω →ₐ[K] Ω)) :=
      (L.equivMap (σ : Ω →ₐ[K] Ω)).toLinearEquiv.finiteDimensional
    exact le_maxUnramifiedOutside fun v hv ↦ (isUnramifiedIn_map_iff _ _ _).2 (hL v hv)
  exact IsGalois.mk

/-- **Hermite's theorem.** For a finite set `S` of finite places of `K` and `n : ℕ`, only finitely
many subextensions of `Ω / K` of degree at most `n` are unramified outside `S`. The fields are
counted as subfields of the fixed `Ω`, as in Mathlib's `NumberField.finite_of_discr_bdd`. -/
theorem finite_unramifiedOutside_of_finrank_le (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) (n : ℕ) :
    {L : IntermediateField K Ω | FiniteDimensional K L ∧ finrank K L ≤ n ∧
      ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal}.Finite := by
  refine ((TauCeti.NumberField.finite_of_finrank_le_of_ramifiedSupport_subset Ω n
    hS.toFinset).image Subtype.val).subset ?_
  rintro L ⟨hfin, hn, hL⟩
  have : NumberField L := NumberField.of_module_finite K L
  refine ⟨⟨L, hfin⟩, ⟨hn, fun v hv ↦ ?_⟩, rfl⟩
  rw [Set.Finite.mem_toFinset]
  by_contra hvS
  obtain ⟨P, hP⟩ := TauCeti.NumberField.mem_ramifiedSupport_iff_exists.1 hv
  have := P.2.1
  exact hP.ne' ((hL v hvS).ramificationIdx_eq_one P.2.2)

end TauCeti.RestrictedRamification
