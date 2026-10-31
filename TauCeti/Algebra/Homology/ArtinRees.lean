/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.RingTheory.Ideal.ArtinRees

/-!
# Artin–Rees and vanishing of homology maps

Let `K` be a complex over a Noetherian ring, finite in degree `i`, and suppose an ideal `J`
annihilates `Hᵢ(K)`. Every chain map into `K` whose degree-`i` image is sufficiently deep in the
`J`-adic filtration induces zero on `Hᵢ`. The bound depends only on `K`, `i` and `J`, and the
source complex need not be finite.

This is the Artin–Rees argument used to prove pro-vanishing of higher Koszul homology. We use
`TauCeti.ArtinRees.exists_controlled_lift` on the inclusion of cycles.

## References

* The Stacks Project, Tag 0921 (the homology-vanishing step of the proof).
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

universe u v w

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {ι : Type w} {c : ComplexShape ι}

/-- If `J` annihilates the homology of `K` in degree `i`, a sufficiently deep degree-`i` image
forces any chain map into `K` to induce zero on that homology. Only `K.X i` must be finite. -/
theorem exists_homologyMap_eq_zero_of_range_le_pow_smul
    (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι) [Module.Finite R (K.X i)]
    (J : Ideal R) (hJ : ∀ r ∈ J, ∀ z : K.homology i, r • z = 0) :
    ∃ t : ℕ, ∀ (L : HomologicalComplex (ModuleCat.{v} R) c) (f : L ⟶ K),
      LinearMap.range (f.f i).hom ≤ J ^ t • (⊤ : Submodule R (K.X i)) →
        homologyMap f i = 0 := by
  let a := (K.iCycles i).hom
  obtain ⟨t, ht⟩ := TauCeti.ArtinRees.exists_controlled_lift J (LinearMap.range a)
  refine ⟨1 + t, fun L f hf ↦ ?_⟩
  have hπ : J • (⊤ : Submodule R (K.cycles i)) ≤ LinearMap.ker (K.homologyπ i).hom := by
    refine Submodule.smul_le.mpr fun r hr z _ ↦ ?_
    simp only [LinearMap.mem_ker, map_smul]
    exact hJ r hr _
  apply (cancel_epi (L.homologyπ i)).mp
  rw [homologyπ_naturality, comp_zero]
  ext z
  let y := (cyclesMap f i) z
  have hy : a y = (f.f i) ((L.iCycles i) z) := by
    exact congrArg (fun q ↦ q.hom z) (cyclesMap_i f i)
  have hv : a y ∈ J ^ (1 + t) • (⊤ : Submodule R (K.X i)) := by
    rw [hy]
    exact hf (LinearMap.mem_range_self _ _)
  obtain ⟨w, hw, he⟩ := ht a.rangeRestrict a.surjective_rangeRestrict 1
    ⟨a y, LinearMap.mem_range_self _ y⟩ hv
  have hwy : w = y :=
    (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance (congrArg Subtype.val he)
  have : y ∈ J • (⊤ : Submodule R (K.cycles i)) := by
    simpa only [pow_one, hwy] using hw
  exact hπ this

end HomologicalComplex
