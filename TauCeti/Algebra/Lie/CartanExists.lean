/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanExists
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# A semisimple element lies in a Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra over an infinite field. Mathlib proves that `L` has a
Cartan subalgebra, namely the Engel subalgebra of a regular element
(`LieAlgebra.exists_isCartanSubalgebra_engel`). This file proves that every element `x` with
semisimple adjoint action lies in some Cartan subalgebra
(`TauCeti.exists_isCartanSubalgebra_mem_of_isSemisimple_ad`).

The Cartan subalgebra is a Cartan subalgebra of the Engel subalgebra `engel K x`, viewed inside
`L`. This is the step that places the neutral element of an `sl₂` triple in a Cartan subalgebra.

## Main results

* `TauCeti.exists_isCartanSubalgebra_mem_of_isSemisimple_ad`: an element with semisimple adjoint
  action lies in a Cartan subalgebra.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Springer GTM 9
  (1972), §15.
-/

public section

open LieAlgebra LieSubalgebra Module

namespace TauCeti

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- **A semisimple element lies in a Cartan subalgebra.** In a finite-dimensional Lie algebra over
an infinite field, an element whose adjoint action is semisimple lies in some Cartan
subalgebra. -/
theorem exists_isCartanSubalgebra_mem_of_isSemisimple_ad [Infinite K] [FiniteDimensional K L]
    {x : L} (hx : (ad K L x).IsSemisimple) :
    ∃ H : LieSubalgebra K L, H.IsCartanSubalgebra ∧ x ∈ H := by
  -- take a Cartan subalgebra `C` of `E = engel K x`; it contains `x`, which is central in `E`, and
  -- an element normalizing `C` in `L` lies in `E`, so `C` is self-normalizing in `L`
  let E := engel K x
  obtain ⟨y, hy⟩ := exists_isCartanSubalgebra_engel K E
  let C : LieSubalgebra K E := engel K y
  have hinj : Function.Injective E.incl := Subtype.val_injective
  have hC : C.IsCartanSubalgebra := hy
  have hmemC {w : E} : (w : L) ∈ C.map E.incl ↔ w ∈ C := by
    refine ⟨fun h ↦ ?_, fun h ↦ (C.mem_map E.incl _).mpr ⟨w, h, rfl⟩⟩
    obtain ⟨w', hw', hw⟩ := (C.mem_map E.incl _).mp h
    rwa [← hinj hw]
  -- `x` is central in its Engel subalgebra, because the generalized kernel of `ad x` is its kernel
  have hxE : x ∈ E := self_mem_engel K x
  have hcentral (w : E) : ⁅(⟨x, hxE⟩ : E), w⁆ = 0 := by
    have hw : (w : L) ∈ (ad K L x).maxGenEigenspace 0 := by
      obtain ⟨n, hn⟩ := (mem_engel_iff K x w).mp w.2
      exact (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨n, by simpa using hn⟩
    rw [hx.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff,
      zero_smul] at hw
    exact Subtype.ext hw
  have hxC : (⟨x, hxE⟩ : E) ∈ C := by
    rw [← hC.self_normalizing, mem_normalizer_iff]
    intro w _
    simp [hcentral w]
  refine ⟨C.map E.incl, ⟨?_, ?_⟩, hmemC.mpr hxC⟩
  · exact (LieSubalgebra.equivMapOfInjective E.incl C hinj).nilpotent_iff_equiv_nilpotent.mp
      hC.nilpotent
  · refine le_antisymm (fun z hz ↦ ?_) (le_normalizer _)
    -- a normalizing element lies in `E`: `⁅x, z⁆ ∈ E`, so a power of `ad x` kills `z`
    have hxz : ⁅x, z⁆ ∈ C.map E.incl :=
      (mem_normalizer_iff' (C.map E.incl) z).mp hz x (hmemC.mpr hxC)
    have hzE : z ∈ E := by
      obtain ⟨w, -, hw⟩ := (C.mem_map E.incl _).mp hxz
      obtain ⟨n, hn⟩ := (mem_engel_iff K x w).mp w.2
      refine (mem_engel_iff K x z).mpr ⟨n + 1, ?_⟩
      rw [pow_succ, Module.End.mul_apply, ad_apply, ← hw]
      simpa using hn
    -- and it normalizes `C` inside `E`
    refine (hmemC (w := ⟨z, hzE⟩)).mpr ?_
    rw [← hC.self_normalizing, mem_normalizer_iff]
    intro w hw
    refine hmemC.mp ?_
    rw [LieSubalgebra.coe_bracket]
    exact (mem_normalizer_iff (C.map E.incl) z).mp hz w (hmemC.mpr hw)

end TauCeti
