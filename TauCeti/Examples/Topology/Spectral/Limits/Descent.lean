/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Spectral.Limits.Descent
import Mathlib.Topology.Category.Profinite.Product

/-!
# Finite-coordinate descent in Cantor space

Constructible subsets of the Boolean product depend on finitely many coordinates. In
particular this applies to every clopen subset of Cantor space. The open complement of a
point does not depend on finitely many coordinates and is not compact.

The finite-coordinate presentation is Mathlib's `Profinite.indexCone_isLimit`, applied to
the whole Boolean product; the descent statement exercises the spectral-limit API.
-/

open Set Topology CategoryTheory CategoryTheory.Limits

namespace TauCeti.Examples.SpectralDescent

example :
    (∀ (U : Set (ℕ → Bool)), IsConstructible U →
      ∃ (s : Finset ℕ) (V : Set (s → Bool)),
        ∀ x, x ∈ U ↔ (fun i : s ↦ x i) ∈ V) ∧
    (∀ x : ℕ → Bool, IsOpen (({x} : Set (ℕ → Bool))ᶜ) ∧
      ¬ IsCompact (({x} : Set (ℕ → Bool))ᶜ) ∧
      ¬ ∃ (s : Finset ℕ) (V : Set (s → Bool)),
        ∀ y, y ∈ ({x} : Set (ℕ → Bool))ᶜ ↔ (fun i : s ↦ y i) ∈ V) := by
  -- Realize the Boolean product as the limit of its finite-coordinate images.
  have hfinite {U : Set (ℕ → Bool)} (hU : IsConstructible U) :
      ∃ (s : Finset ℕ) (V : Set (s → Bool)),
        ∀ x, x ∈ U ↔ (fun i : s ↦ x i) ∈ V := by
    let C : Set (ℕ → Bool) := univ
    have hC : IsCompact C := isCompact_univ
    let F := Profinite.indexFunctor hC ⋙ Profinite.toTopCat
    let c := Profinite.toTopCat.mapCone (Profinite.indexCone hC)
    have hc : IsLimit c := isLimitOfPreserves Profinite.toTopCat
      (Profinite.indexCone_isLimit hC)
    have : ∀ j, Finite (F.obj j) := fun j ↦
      inferInstanceAs (Finite (Profinite.IndexFunctor.obj C (· ∈ j.unop)))
    have : ∀ j, SpectralSpace (F.obj j) := fun j ↦ by
      have : T2Space (F.obj j) := inferInstanceAs
        (T2Space ((Profinite.indexFunctor hC).obj j))
      exact {}
    have hF {i j} (f : i ⟶ j) : IsSpectralMap (F.map f) :=
      ⟨(F.map f).hom.continuous, fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
    have hUc : IsConstructible ((Subtype.val : C → (ℕ → Bool)) ⁻¹' U) :=
      hU.preimage_of_isOpenEmbedding isOpen_univ.isOpenEmbedding_subtypeVal
    obtain ⟨j, V, _, hV⟩ := TopCat.exists_constructible_preimage_of_isLimit F
      (fun f ↦ hF f) c hc hUc
    refine ⟨j.unop, Subtype.val '' V, fun x ↦ ?_⟩
    have hx := Set.ext_iff.mp hV (⟨x, mem_univ x⟩ : C)
    refine hx.trans ?_
    -- The specified cone projects by restricting the sequence to the finite coordinate set.
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨y, hy, he⟩
      have he' : y = c.π.app j ⟨x, mem_univ x⟩ := Subtype.ext he
      exact (he' ▸ hy : c.π.app j ⟨x, mem_univ x⟩ ∈ V)
  refine ⟨fun _ hU ↦ hfinite hU, fun x ↦ ?_⟩
  -- A modification outside the chosen coordinates has the same projection but is not `x`.
  have hnot : ¬ ∃ (s : Finset ℕ) (V : Set (s → Bool)),
      ∀ y, y ∈ ({x} : Set (ℕ → Bool))ᶜ ↔ (fun i : s ↦ y i) ∈ V := by
    rintro ⟨s, V, hV⟩
    obtain ⟨n, -, hn⟩ := Set.infinite_univ.exists_notMem_finset s
    let y := Function.update x n (!(x n))
    have hxy : y ≠ x := by
      intro h
      have := congrFun h n
      simp [y] at this
    have heq : (fun i : s ↦ y i) = fun i : s ↦ x i := by
      funext i
      have hi : (i : ℕ) ≠ n := fun h ↦ hn (h ▸ i.2)
      exact Function.update_of_ne hi _ _
    have hy := (hV y).mp (by simpa using hxy)
    rw [heq, ← hV x] at hy
    simp at hy
  exact ⟨isClosed_singleton.isOpen_compl,
    fun hc ↦ hnot (hfinite (hc.isConstructible isClosed_singleton.isOpen_compl)), hnot⟩

end TauCeti.Examples.SpectralDescent
