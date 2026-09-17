/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Images of Sylow subgroups of profinite groups

A continuous surjection of profinite groups carries a Sylow pro-`p` subgroup onto a Sylow
pro-`p` subgroup. At each finite quotient of the target, pull the quotient back to the source.
The induced map between the two finite quotients is surjective, so the index of the image divides
the original prime-to-`p` index.

This is the profinite counterpart of the finite-group fact that a surjective homomorphism carries
a Sylow subgroup onto a Sylow subgroup. Unlike invariance under a topological isomorphism, proved
in `TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic`, it must account for the kernel of the
homomorphism.

## Main result

* `TauCeti.IsProPSylow.map_of_surjective`: the image of a Sylow pro-`p` subgroup under a
  continuous surjection is Sylow pro-`p`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H] [T2Space H]
variable {P : Subgroup G}

namespace IsProPSylow

/-- **Surjective functoriality of Sylow pro-`p` subgroups.** The image of a Sylow pro-`p`
subgroup under a continuous surjection of profinite groups is again Sylow pro-`p`. -/
theorem map_of_surjective (hP : IsProPSylow p P) (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsProPSylow p (P.map f) := by
  refine isProPSylow_iff.mpr ⟨?_, ?_, fun U hpU ↦ ?_⟩
  · rw [Subgroup.coe_map]
    exact (hP.isClosed.isCompact.image hf).isClosed
  · exact hP.isProP.of_surjective (f.subgroupMap P)
      (continuous_induced_rng.mpr (hf.comp continuous_subtype_val))
      (f.subgroupMap_surjective P)
  · let V := OpenNormalSubgroup.comap U f hf
    let _ : V.toSubgroup.Normal := V.isNormal'
    have hVU : V.toSubgroup ≤ U.toSubgroup.comap f := by simp [V]
    let q : G ⧸ V.toSubgroup →* H ⧸ U.toSubgroup :=
      QuotientGroup.map V.toSubgroup U.toSubgroup f hVU
    have hqsurj : Function.Surjective q :=
      QuotientGroup.map_surjective_of_surjective V.toSubgroup U.toSubgroup f
        ((QuotientGroup.mk'_surjective U.toSubgroup).comp hsurj) hVU
    rw [← Subgroup.map_quotientGroupMap_map_mk' P f hVU] at hpU
    exact hP.not_dvd_index V (hpU.trans ((P.map (QuotientGroup.mk' V.toSubgroup)).index_map_dvd
      hqsurj))

end IsProPSylow

end TauCeti
