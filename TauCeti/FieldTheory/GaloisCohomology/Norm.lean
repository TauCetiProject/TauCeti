/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import TauCeti.RingTheory.Norm.Units

/-!
# The representation norm on units of a Galois extension

For a finite Galois extension `L/K`, the norm of the representation of `Gal(L/K)` on `Lˣ`
agrees with the field norm. This file records the resulting identification between the range of
the representation norm on elements from `Kˣ` and the field-theoretic norm group
`N_{L/K}(Lˣ)`.

## Main results

* `TauCeti.mem_range_rep_norm_iff_mem_normGroup`: the representation norm on `Lˣ` has the same
  range on elements of `Kˣ` as the field norm.
-/

public section

namespace TauCeti

open groupCohomology

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The image of `a ∈ Kˣ` in `Lˣ` lies in the range of the representation norm for
`Gal(L/K)` exactly when `a` lies in the field norm group `N_{L/K}(Lˣ)`. -/
theorem mem_range_rep_norm_iff_mem_normGroup (a : Kˣ) :
    (Rep.toAdditive.symm (Additive.ofMul (Units.map (algebraMap K L : K →* L) a)) :
        Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ) ∈
        LinearMap.range (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) Lˣ).norm.hom.toLinearMap ↔
      a ∈ normGroup K L := by
  rw [mem_normGroup_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(Rep.toAdditive y).toMul, (algebraMap K L).injective ?_⟩
    rw [← norm_ofAlgebraAutOnUnits_eq]
    exact congr(((Additive.toMul (Rep.toAdditive $hy) : Lˣ) : L)).trans (by simp)
  · rintro ⟨y, hy⟩
    refine ⟨Rep.toAdditive.symm (Additive.ofMul y), ?_⟩
    apply Rep.toAdditive.injective
    apply Additive.toMul.injective
    apply Units.ext
    have h := norm_ofAlgebraAutOnUnits_eq (K := K) y
    simp only [hy] at h
    exact h

end TauCeti
