/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.MonoidAlgebra.Basic

/-!
# Monoid algebras over a local ring

For a finite monoid `G` (for instance a finite group) and a local ring `R` with residue field `k`,
the free module `R[G]^ι` of finite rank is a finitely generated `R`-module, so Nakayama's lemma
over `R` detects surjectivity of its endomorphisms after reduction to `k[G]^ι`.
The Orzech property then upgrades surjectivity to bijectivity.

## Main results

* `TauCeti.MonoidAlgebra.bijective_of_forall_exists_mapRingHom_residue_eq`: an `R[G]`-linear
  endomorphism of `R[G]^ι` that is onto modulo the maximal ideal is bijective.
-/

public section

open MonoidAlgebra IsLocalRing

namespace TauCeti.MonoidAlgebra

variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Monoid G] [Finite G] {ι : Type*}
  [Finite ι]

/-- **Nakayama's lemma for `R[G]^ι`.** An `R[G]`-linear endomorphism of `R[G]^ι` that is onto
modulo the maximal ideal is bijective. -/
theorem bijective_of_forall_exists_mapRingHom_residue_eq
    (θ : (ι → MonoidAlgebra R G) →ₗ[MonoidAlgebra R G] (ι → MonoidAlgebra R G))
    (h : ∀ y : ι → MonoidAlgebra R G, ∃ x, ∀ i,
      mapRingHom G (residue R) (θ x i) = mapRingHom G (residue R) (y i)) :
    Function.Bijective θ := by
  classical
  have := Fintype.ofFinite ι
  -- `R[G]^ι` is a finitely generated `R`-module and `θ` is onto modulo `𝔪 • R[G]^ι`.
  have hle : (⊤ : Submodule R (ι → MonoidAlgebra R G)) ≤
      LinearMap.range (θ.restrictScalars R) ⊔ maximalIdeal R • ⊤ := by
    intro y _
    obtain ⟨x, hx⟩ := h y
    refine Submodule.mem_sup.mpr ⟨θ x, ⟨x, rfl⟩, y - θ x, ?_, add_sub_cancel _ _⟩
    rw [← Finset.univ_sum_single (y - θ x)]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_top_le_comap_smul_top _
      (LinearMap.single R (fun _ ↦ MonoidAlgebra R G) i) ?_
    rw [← ker_residue, ← mapRingHom_eq_zero_iff, Pi.sub_apply, map_sub, hx, sub_self]
  have hsurj : Function.Surjective θ := LinearMap.range_eq_top.mp (top_unique
    (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)
      hle))
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism (θ.restrictScalars R) hsurj, hsurj⟩

end TauCeti.MonoidAlgebra
