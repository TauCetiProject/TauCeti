/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.KrullDimension.Irreducible
public import TauCeti.Topology.KrullDimension.Basic
public import Mathlib.Topology.LocallyClosed

/-!
# Krull dimension and closed covers

The dimension of a space is the supremum of the dimensions of its irreducible components.
For a finite closed cover it is likewise the supremum of the dimensions of the covering
sets. These statements allow dimension arguments to treat reducible spaces componentwise.

In a nonempty Noetherian space of finite dimension, the complement of a dense open subset
has strictly smaller dimension. This is the topological dimension estimate used for
boundaries of locally closed algebraic orbits, including orbits of disconnected groups.

The chain restriction argument uses Mathlib's `IrreducibleCloseds` and `Order.LTSeries`.
The strict estimate uses `IsIrreducible.topologicalKrullDim_lt`.
-/

public section

open Set Order Topology TopologicalSpace

namespace TauCeti

/-- The dimension of a space is the supremum of the dimensions of its irreducible components.
No finiteness assumption is needed. -/
theorem topologicalKrullDim_eq_iSup_irreducibleComponents
    (X : Type*) [TopologicalSpace X] :
    topologicalKrullDim X = ⨆ C : irreducibleComponents X, topologicalKrullDim C.1 := by
  refine le_antisymm (iSup_le fun p ↦ ?_)
    (iSup_le fun C ↦ topologicalKrullDim_subspace_le X C.1)
  obtain ⟨C, hC, hpC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ p.last.isIrreducible
  have hsub (j) : (p j : Set X) ⊆ C := fun _ hx ↦ hpC (p.monotone (Fin.le_last j) hx)
  have hirr (j) : IsIrreducible (Subtype.val ⁻¹' (p j : Set X) : Set C) := by
    have := Subtype.irreducibleSpace (p j).isIrreducible
    have := (IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa using hsub j)).irreducibleSpace_iff.mpr
        (inferInstance : IrreducibleSpace (p j))
    exact IsIrreducible.of_subtype
  -- Restrict the whole chain to a component containing its largest member.
  let q : LTSeries (IrreducibleCloseds C) :=
    ⟨p.length, fun j ↦ ⟨Subtype.val ⁻¹' (p j : Set X), hirr j,
      (p j).isClosed.preimage continuous_subtype_val⟩, fun j ↦ by
        refine lt_of_le_of_ne (Set.preimage_mono (p.step j).le) ?_
        intro h
        have hp : p j.castSucc < p j.succ := p.step j
        apply hp.ne
        apply IrreducibleCloseds.ext
        ext x
        by_cases hx : x ∈ C
        · exact Set.ext_iff.mp h ⟨x, hx⟩
        · exact iff_of_false (fun hp ↦ hx (hsub _ hp)) (fun hp ↦ hx (hsub _ hp))⟩
  exact le_iSup_of_le ⟨C, hC⟩ q.length_le_krullDim

/-- The dimension of a finite closed cover is the supremum of the dimensions of its members. -/
theorem topologicalKrullDim_eq_iSup_of_isClosed {X ι : Type*} [TopologicalSpace X]
    [Finite ι] (Z : ι → Set X) (hZ : ∀ i, IsClosed (Z i))
    (hcover : ∀ x, ∃ i, x ∈ Z i) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Z i) := by
  classical
  refine le_antisymm ?_ (iSup_le fun i ↦ topologicalKrullDim_subspace_le X (Z i))
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
  refine iSup_le fun C ↦ ?_
  obtain ⟨W, hW, hCW⟩ := isIrreducible_iff_sUnion_isClosed.mp C.2.1
    (Set.finite_range Z).toFinset (by simpa using hZ) (by
      intro x _
      obtain ⟨i, hi⟩ := hcover x
      exact Set.mem_sUnion.mpr ⟨Z i, by simp, hi⟩)
  obtain ⟨i, rfl⟩ : W ∈ Set.range Z := by simpa using hW
  exact le_iSup_of_le i (IsEmbedding.inclusion hCW).isInducing.topologicalKrullDim_le

end TauCeti

namespace IsOpen

/-- In a nonempty Noetherian space of finite dimension, the complement of a dense open
subset has strictly smaller dimension than the space. -/
theorem topologicalKrullDim_compl_lt {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [Nonempty X] {U : Set X} (hU : IsOpen U) (hdense : Dense U)
    (hdim : topologicalKrullDim X ≠ ⊤) :
    topologicalKrullDim ↥(Uᶜ) < topologicalKrullDim X := by
  classical
  let := (NoetherianSpace.finite_irreducibleComponents (α := X)).fintype
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (irreducibleComponents X) :=
    ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩⟩
  have hcover : topologicalKrullDim ↥(Uᶜ) =
      ⨆ C : irreducibleComponents X, topologicalKrullDim ↥(C.1 \ U) := by
    rw [TauCeti.topologicalKrullDim_eq_iSup_of_isClosed
      (fun C : irreducibleComponents X ↦ (Subtype.val : ↥(Uᶜ) → X) ⁻¹' C.1)
      (fun C ↦ (isClosed_of_mem_irreducibleComponents _ C.2).preimage continuous_subtype_val)
      (fun y ↦ ⟨⟨irreducibleComponent y.1,
        irreducibleComponent_mem_irreducibleComponents y.1⟩, mem_irreducibleComponent⟩)]
    apply iSup_congr
    intro C
    have h := (IsEmbedding.subtypeVal (p := (· ∈ Uᶜ))).topologicalKrullDim_preimage C.1
    rw [Subtype.range_val] at h
    exact h
  rw [hcover]
  obtain ⟨C, hC⟩ := exists_eq_ciSup_of_finite
    (f := fun C : irreducibleComponents X ↦ topologicalKrullDim ↥(C.1 \ U))
  rw [← hC]
  obtain ⟨V, hV, hVne, hVC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C.1 C.2
  obtain ⟨y, hyV, hyU⟩ := hdense.inter_open_nonempty V hV hVne
  have hCc := isClosed_of_mem_irreducibleComponents _ C.2
  exact (C.2.1.topologicalKrullDim_lt (hCc.sdiff hU)
    (Set.sdiff_ssubset_left_iff.mpr ⟨y, hVC hyV, hyU⟩)
    (ne_top_of_le_ne_top hdim (topologicalKrullDim_subspace_le X C.1))).trans_le
      (topologicalKrullDim_subspace_le X C.1)

end IsOpen

namespace IsLocallyClosed

/-- The boundary of a nonempty locally closed subset of a Noetherian space has strictly
smaller dimension than its closure, provided that closure has finite dimension. -/
theorem topologicalKrullDim_closure_sdiff_lt {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {s : Set X} (hs : IsLocallyClosed s) (hne : s.Nonempty)
    (hdim : topologicalKrullDim (closure s) ≠ ⊤) :
    topologicalKrullDim ↥(closure s \ s) < topologicalKrullDim (closure s) := by
  have : Nonempty (closure s) := hne.closure.to_subtype
  have hd : Dense ((Subtype.val : closure s → X) ⁻¹' s) := by
    rw [Subtype.dense_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr (subset_closure (s := s))]
  have h := hs.isOpen_preimage_val_closure.topologicalKrullDim_compl_lt hd hdim
  have he := (IsEmbedding.subtypeVal (p := (· ∈ closure s))).topologicalKrullDim_preimage sᶜ
  rw [Subtype.range_val, ← sdiff_eq_compl_inter] at he
  exact he ▸ h

end IsLocallyClosed
