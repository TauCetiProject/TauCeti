/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Hermite
import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
import TauCeti.NumberTheory.NumberField.Unramified.Subextension

/-!
# The maximal extension unramified outside a set of places

Let `K` be a number field, `Ω` an extension of `K` and `S` a set of finite places of `K`. A finite
subextension `L` of `Ω / K` is *unramified outside `S`* when every place `v ∉ S` is unramified in
`𝓞 L`, in the sense of Mathlib's `Algebra.IsUnramifiedIn`; archimedean places impose nothing. This
quantified statement is used directly; no wrapper predicate is defined.

This file defines the compositum `K_S` of these subextensions,
`TauCeti.RestrictedRamification.maxUnramifiedOutside`, and its Galois group
`G_{K,S} = Gal(K_S / K)`, `TauCeti.RestrictedRamification.galoisGroupS`, with its Krull topology.
When `Ω` is a separable closure of `K`, `K_S` is the maximal extension of `K` unramified outside
`S`.

Unramifiedness at a place `v` is read on the inertia groups of a finite Galois extension containing
the fields in question (`Ideal.isUnramifiedIn_iff_forall_inertia_le`), so it passes to composita
and subextensions. It is also invariant under isomorphisms of extensions, in particular under
conjugation by `Gal(Ω / K)` (`Ideal.isUnramifiedIn_map_iff`). The facts about composita and
subextensions are in `TauCeti/NumberTheory/NumberField/Unramified/Subextension.lean`. So a finite
subextension lies in `K_S` exactly when it is unramified outside `S`, and `K_S / K` is Galois when
`Ω / K` is normal.

For finite `S`, Hermite's theorem
`TauCeti.NumberField.finite_of_finrank_le_of_ramifiedSupport_subset` says that only finitely many
subextensions of bounded degree are unramified outside `S`.

## Main definitions

* `TauCeti.RestrictedRamification.maxUnramifiedOutside`: the compositum `K_S` in `Ω` of the finite
  subextensions of `Ω / K` unramified outside `S`.
* `TauCeti.RestrictedRamification.galoisGroupS`: `G_{K,S} = Gal(K_S / K)`.

## Main results

* `TauCeti.RestrictedRamification.mem_maxUnramifiedOutside_iff`: an element lies in `K_S` exactly
  when it lies in a finite subextension unramified outside `S`.
* `TauCeti.RestrictedRamification.le_maxUnramifiedOutside_iff`: a finite subextension lies in
  `K_S` exactly when it is unramified outside `S`.
* `TauCeti.RestrictedRamification.maxUnramifiedOutside_le_iff`: `K_S` lies in an intermediate
  field `M` exactly when every finite subextension unramified outside `S` does.
* `TauCeti.RestrictedRamification.maxUnramifiedOutside_univ`: for `S` the set of all finite places
  and `Ω / K` algebraic, `K_S = Ω`.
* `TauCeti.RestrictedRamification.isGalois_maxUnramifiedOutside`: `K_S / K` is Galois when
  `Ω / K` is normal.
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
/-- **The universal property of `K_S`.** If every finite subextension unramified outside `S` lies
in `M`, then `K_S` lies in `M`. -/
theorem maxUnramifiedOutside_le {S : Set (HeightOneSpectrum (𝓞 K))} {M : IntermediateField K Ω}
    (h : ∀ L : IntermediateField K Ω, FiniteDimensional K L →
      (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) → L ≤ M) :
    maxUnramifiedOutside K Ω S ≤ M := by
  rw [maxUnramifiedOutside_def]
  exact iSup₂_le fun L hL ↦ iSup_le (h L hL)

omit [NumberField K] in
/-- `K_S` lies in `M` exactly when every finite subextension unramified outside `S` does. -/
theorem maxUnramifiedOutside_le_iff {S : Set (HeightOneSpectrum (𝓞 K))}
    {M : IntermediateField K Ω} :
    maxUnramifiedOutside K Ω S ≤ M ↔ ∀ L : IntermediateField K Ω, FiniteDimensional K L →
      (∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) → L ≤ M :=
  ⟨fun h _ _ hL ↦ (le_maxUnramifiedOutside hL).trans h, maxUnramifiedOutside_le⟩

omit [NumberField K] in
/-- **Enlarging `S` enlarges `K_S`.** -/
theorem maxUnramifiedOutside_mono {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') :
    maxUnramifiedOutside K Ω S ≤ maxUnramifiedOutside K Ω S' :=
  maxUnramifiedOutside_le fun _ _ hL ↦ le_maxUnramifiedOutside fun v hv ↦ hL v (mt (@h v) hv)

omit [NumberField K] in
/-- **`K_S` for the set of all finite places** is the whole of `Ω`, for `Ω / K` algebraic: every
element generates a finite subextension, and the condition outside `S` is empty. -/
theorem maxUnramifiedOutside_univ [Algebra.IsAlgebraic K Ω] :
    maxUnramifiedOutside K Ω Set.univ = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  have := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) x)
  exact le_maxUnramifiedOutside (L := K⟮x⟯) (fun v hv ↦ absurd (Set.mem_univ v) hv)
    (mem_adjoin_simple_self K x)

/-- **Finitely generated subextensions of `K_S`.** A subextension of `Ω / K` generated by a finite
set `t` lies in `K_S` exactly when it lies in a finite subextension unramified outside `S`. -/
theorem adjoin_le_maxUnramifiedOutside_iff {S : Set (HeightOneSpectrum (𝓞 K))} (t : Finset Ω) :
    adjoin K (t : Set Ω) ≤ maxUnramifiedOutside K Ω S ↔ ∃ E : IntermediateField K Ω,
      adjoin K (t : Set Ω) ≤ E ∧ FiniteDimensional K E ∧
        ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := by
  refine ⟨fun ht ↦ ?_, fun ⟨E, ht, hE, hES⟩ ↦ ht.trans (le_maxUnramifiedOutside (L := E) hES)⟩
  -- the generating family, indexed by a subtype
  let ι := {E : IntermediateField K Ω //
    FiniteDimensional K E ∧ ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal}
  let f : ι → IntermediateField K Ω := fun E ↦ E.val
  replace ht : adjoin K (t : Set Ω) ≤ ⨆ E, f E := ht.trans <| iSup₂_le fun E hE ↦ iSup_le fun hE' ↦
    le_iSup_of_le (f := f) ⟨E, hE, hE'⟩ le_rfl
  -- `adjoin K t` is a compact element, so it lies in a finite subcompositum
  obtain ⟨s, hs⟩ := (adjoin_finset_isCompactElement t).exists_finset_of_le_iSup _ ht
  refine ⟨⨆ E ∈ s, f E, hs, ?_⟩
  clear hs ht
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [← Finset.sup_eq_iSup, Finset.sup_empty]
    exact ⟨inferInstance, fun v _ ↦ isUnramifiedIn_bot K Ω v.asIdeal⟩
  | insert E s _ ih =>
    rw [Finset.iSup_insert]
    have := E.property.1
    have := ih.1
    exact ⟨inferInstance, fun v hv ↦
      (isUnramifiedIn_sup_iff _ _ _).2 ⟨E.property.2 v hv, ih.2 v hv⟩⟩

/-- **The elements of `K_S`.** An element of `Ω` lies in `K_S` exactly when it lies in a finite
subextension of `Ω / K` unramified outside `S`. -/
theorem mem_maxUnramifiedOutside_iff {S : Set (HeightOneSpectrum (𝓞 K))} {x : Ω} :
    x ∈ maxUnramifiedOutside K Ω S ↔ ∃ E : IntermediateField K Ω,
      x ∈ E ∧ FiniteDimensional K E ∧ ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := by
  have h := adjoin_le_maxUnramifiedOutside_iff (K := K) (S := S) {x}
  simp only [Finset.coe_singleton, adjoin_simple_le_iff] at h
  exact h

/-- **The finite subextensions of `K_S`.** A finite subextension `L` of `Ω / K` lies in `K_S`
exactly when it is unramified at every finite place outside `S`. -/
theorem le_maxUnramifiedOutside_iff {S : Set (HeightOneSpectrum (𝓞 K))}
    {L : IntermediateField K Ω} [FiniteDimensional K L] :
    L ≤ maxUnramifiedOutside K Ω S ↔ ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  refine ⟨fun hL ↦ ?_, le_maxUnramifiedOutside⟩
  -- `L` is generated by a finite set, so it lies in a finite subextension unramified outside `S`
  obtain ⟨t, rfl⟩ : ∃ t : Finset Ω, adjoin K (t : Set Ω) = L :=
    (essFiniteType_iff.1 inferInstance).imp fun _ h ↦ h
  obtain ⟨E, hle, _, hE⟩ := (adjoin_le_maxUnramifiedOutside_iff t).1 hL
  exact fun v hv ↦ isUnramifiedIn_of_le hle (hE v hv)

/-- **`K_S / K` is Galois** when `Ω / K` is normal. -/
instance isGalois_maxUnramifiedOutside [Normal K Ω] (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsGalois K (maxUnramifiedOutside K Ω S) := by
  -- conjugation by `Gal(Ω / K)` permutes the finite subextensions unramified outside `S`
  have : Normal K (maxUnramifiedOutside K Ω S) := by
    refine normal_iff_forall_map_le'.2 fun σ ↦ ?_
    simp only [maxUnramifiedOutside_def, IntermediateField.map_iSup, iSup_le_iff]
    intro L _ hL
    have : FiniteDimensional K (L.map (σ : Ω →ₐ[K] Ω)) :=
      (L.equivMap (σ : Ω →ₐ[K] Ω)).toLinearEquiv.finiteDimensional
    exact le_maxUnramifiedOutside fun v hv ↦
      (Ideal.isUnramifiedIn_map_iff v.asIdeal L (σ : Ω →ₐ[K] Ω)).2 (hL v hv)
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
  have := P.property.1
  exact hP.ne' ((hL v hvS).ramificationIdx_eq_one P.property.2)

end TauCeti.RestrictedRamification
