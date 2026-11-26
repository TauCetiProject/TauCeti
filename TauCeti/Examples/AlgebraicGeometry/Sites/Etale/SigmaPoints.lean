/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Infinitely many points over a field: étale but not quasi-compact

For a field `k`, the fold map `⨿_{n ∈ ℕ} Spec k ⟶ Spec k` is étale, since it is the identity on
each summand, but its source is not quasi-compact: it is homeomorphic to the topological disjoint
union of infinitely many points, a discrete space that is not finite. So the fold map is not
quasi-compact and its source is not Noetherian. As an object of the small étale site
`(Spec k).Etale`, its structure morphism is therefore not quasi-compact, so it lies outside any
subsite of `(Spec k).Etale` made of quasi-compact étale `Spec k`-schemes.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.Examples.SigmaPoints

variable (k : Type) [Field k]

/-- The fold map `⨿_{n ∈ ℕ} Spec k ⟶ Spec k`. -/
noncomputable def fold : (∐ fun _ : ℕ ↦ Spec (.of k)) ⟶ Spec (.of k) :=
  Sigma.desc fun _ ↦ 𝟙 _

/-- The fold map is the identity on each summand. -/
@[reassoc (attr := simp)]
theorem ι_fold (n : ℕ) : Sigma.ι (fun _ : ℕ ↦ Spec (.of k)) n ≫ fold k = 𝟙 _ :=
  Sigma.ι_comp_desc _ _

instance etale_fold : Etale (fold k) :=
  -- Instance search does not find Zariski-locality of `Etale` at the source, so it is supplied
  -- from the ring-hom property.
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- The fold map, as an object of the small étale site of `Spec k`. -/
@[expose] noncomputable def etaleObj : (Spec (.of k)).Etale :=
  MorphismProperty.Over.mk ⊤ (fold k) inferInstance

@[simp]
theorem etaleObj_left : (etaleObj k).left = ∐ fun _ : ℕ ↦ Spec (.of k) :=
  rfl

@[simp]
theorem etaleObj_hom : (etaleObj k).hom = fold k :=
  rfl

/-- The coproduct of countably many copies of `Spec k` is not quasi-compact. -/
theorem not_compactSpace : ¬ CompactSpace (∐ fun _ : ℕ ↦ Spec (.of k) :) := fun _ ↦ by
  have := (sigmaMk fun _ : ℕ ↦ Spec (.of k)).symm.compactSpace
  have := finite_of_compact_of_discrete (X := Σ _ : ℕ, Spec (.of k))
  have := Finite.of_injective (fun n ↦ (⟨n, default⟩ : Σ _ : ℕ, Spec (.of k)))
    fun _ _ h ↦ congrArg Sigma.fst h
  exact not_finite ℕ

/-- The fold map is not quasi-compact. -/
theorem not_quasiCompact_fold : ¬ QuasiCompact (fold k) :=
  fun _ ↦ not_compactSpace k (QuasiCompact.compactSpace_of_compactSpace (fold k))

/-- The coproduct of countably many copies of `Spec k` is not Noetherian. -/
theorem not_isNoetherian : ¬ IsNoetherian (∐ fun _ : ℕ ↦ Spec (.of k)) :=
  fun h ↦ not_compactSpace k h.toCompactSpace

/-- The structure morphism of the étale `Spec k`-scheme `⨿_{n ∈ ℕ} Spec k` is not quasi-compact. -/
theorem not_quasiCompact_etaleObj_hom : ¬ QuasiCompact (etaleObj k).hom := by
  rw [etaleObj_hom]
  exact not_quasiCompact_fold k

end TauCeti.Examples.SigmaPoints
