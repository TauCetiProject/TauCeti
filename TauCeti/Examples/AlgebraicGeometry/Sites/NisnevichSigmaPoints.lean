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
each summand, but its source is not quasi-compact: the summands form an open cover with no finite
subcover. So the fold map is not quasi-compact and its source is not Noetherian. As an object of
the small étale site `(Spec k).Etale` it is therefore not an object of the quasi-compact basis on
which the Nisnevich sheaf condition is tested by elementary distinguished squares
(SchemeAndStackFoundations §2.13, Check "`⨿_{n∈ℕ} Spec k → Spec k` is étale but neither
quasi-compact nor Noetherian").
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.Examples.SigmaPoints

variable (k : Type) [Field k]

/-- The spectrum of `k`. -/
noncomputable abbrev pt : Scheme.{0} :=
  Spec (.of k)

/-- The fold map `⨿_{n ∈ ℕ} Spec k ⟶ Spec k`. -/
noncomputable def fold : (∐ fun _ : ℕ ↦ Spec (.of k)) ⟶ Spec (.of k) :=
  Sigma.desc fun _ ↦ 𝟙 _

instance etale_fold : Etale (fold k) :=
  -- Instance search does not find Zariski-locality of `Etale` at the source, so it is supplied
  -- from the ring-hom property.
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- The fold map, as an object of the small étale site of `Spec k`. -/
noncomputable def etaleObj : (Spec (.of k)).Etale :=
  MorphismProperty.Over.mk ⊤ (fold k) inferInstance

/-- The coproduct of countably many copies of `Spec k` is not quasi-compact. -/
theorem not_compactSpace : ¬ CompactSpace (∐ fun _ : ℕ ↦ Spec (.of k) :) := by
  intro h
  have : CompactSpace (Σ _ : ℕ, pt k) :=
    (sigmaMk fun _ : ℕ ↦ pt k).symm.compactSpace
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun n : ℕ ↦ Set.range (@Sigma.mk ℕ (fun _ ↦ pt k) n))
    (fun _ ↦ isOpen_range_sigmaMk) (fun x _ ↦ Set.mem_iUnion.2 ⟨x.1, x.2, rfl⟩)
  obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset t
  obtain ⟨n, hn, y, hy⟩ := Set.mem_iUnion₂.1
    (ht (Set.mem_univ (⟨m, Classical.arbitrary _⟩ : Σ _ : ℕ, pt k)))
  have hnm : n = m := congrArg Sigma.fst hy
  exact hm (hnm ▸ hn)

/-- The fold map is étale but not quasi-compact. -/
theorem not_quasiCompact_fold : ¬ QuasiCompact (fold k) :=
  fun _ ↦ not_compactSpace k (QuasiCompact.compactSpace_of_compactSpace (fold k))

/-- The coproduct of countably many copies of `Spec k` is not Noetherian. -/
theorem not_isNoetherian : ¬ IsNoetherian (∐ fun _ : ℕ ↦ Spec (.of k)) :=
  fun h ↦ not_compactSpace k h.toCompactSpace

/-- The structure morphism of the étale `Spec k`-scheme `⨿_{n ∈ ℕ} Spec k` is not quasi-compact. -/
theorem not_quasiCompact_etaleObj_hom : ¬ QuasiCompact (etaleObj k).hom :=
  not_quasiCompact_fold k

end TauCeti.Examples.SigmaPoints
