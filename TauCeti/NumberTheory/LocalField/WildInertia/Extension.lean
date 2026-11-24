/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Extension
public import TauCeti.NumberTheory.LocalField.WildInertia.Basic
import TauCeti.Topology.Algebra.Group.ClosedSubgroup
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup

/-!
# Wild inertia along a finite extension of local fields

Let `L/K` be a finite extension of nonarchimedean local fields, embedded in a separable closure of
`K` by `ι`, and let `absoluteGaloisGroupExtend K L ι : G_L →* G_K` be the resulting embedding of
absolute Galois groups. The wild inertia subgroup of `L` is the preimage of that of `K`,
`P_L = P_K ∩ G_L`, as for the inertia subgroups
(`TauCeti.comap_absoluteGaloisGroupExtend_inertiaSubgroup`).

Both inclusions come from the characterization of wild inertia as the largest pro-`p` subgroup of
inertia, `p` the common residue characteristic (`TauCeti.le_wildInertiaSubgroup_of_isProP`). The
image of `P_L` is a pro-`p` subgroup of `I_L ⊆ I_K`, hence lies in `P_K`. Conversely the preimage
of `P_K` lies in `I_L`, and it is pro-`p` because the embedding is an isomorphism of topological
groups onto its image, which carries the preimage onto a subgroup of `P_K`.

## Main results

* `TauCeti.comap_absoluteGaloisGroupExtend_wildInertiaSubgroup`: `P_L` is the preimage of `P_K`.
* `TauCeti.absoluteGaloisGroupExtend_mem_wildInertiaSubgroup_iff`: an element of `G_L` lies in
  `P_L` exactly when its image lies in `P_K`.
* `TauCeti.map_absoluteGaloisGroupExtend_wildInertiaSubgroup`: the image of `P_L` is
  `P_K ∩ G_L`.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §1, Proposition 2.
-/

public section

noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (ι : L →ₐ[K] SeparableClosure K)

omit [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] in
/-- The preimage of `P_K` in `G_L` is pro-`p`, for `p` the residue characteristic of `K`. -/
private theorem isProP_comap_absoluteGaloisGroupExtend_wildInertiaSubgroup (p : ℕ)
    [CharP 𝓀[K] p] :
    IsProP p ((wildInertiaSubgroup K).comap (absoluteGaloisGroupExtend K L ι)) := by
  set U := (absoluteGaloisGroupExtend K L ι).range
  set e := absoluteGaloisGroupExtendEquiv K L ι (U := U) rfl
  -- Along `e`, the preimage of `P_K` is the trace of `P_K` on the image of `G_L`.
  have hR : ((wildInertiaSubgroup K).comap (absoluteGaloisGroupExtend K L ι)).map
      ((e : Field.absoluteGaloisGroup L ≃* U) : Field.absoluteGaloisGroup L →* U) =
      (wildInertiaSubgroup K ⊓ U).subgroupOf U := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have he (g : Field.absoluteGaloisGroup L) :
        ((e g : U) : Field.absoluteGaloisGroup K) = absoluteGaloisGroupExtend K L ι g :=
      coe_absoluteGaloisGroupExtendEquiv_apply K L ι rfl g
    refine ⟨?_, fun h ↦ ⟨e.symm x, ?_, e.apply_symm_apply x⟩⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(he g).symm ▸ Subgroup.mem_comap.mp hg, (e g).property⟩
    · rw [Subgroup.mem_comap, ← he, e.apply_symm_apply]
      exact h.1
  rw [isProP_congr (e.subgroupMap _), hR,
    Subgroup.isProP_subgroupOf_iff inf_le_right]
  exact (isProP_wildInertiaSubgroup K p).mono inf_le_left

/-- **Wild inertia along a finite extension, as a preimage.** The wild inertia subgroup of `L` is
the preimage of that of `K` under the embedding `G_L → G_K`. -/
@[simp]
theorem comap_absoluteGaloisGroupExtend_wildInertiaSubgroup :
    (wildInertiaSubgroup K).comap (absoluteGaloisGroupExtend K L ι) = wildInertiaSubgroup L := by
  have : CharP 𝓀[L] (ringChar 𝓀[K]) :=
    charP_of_injective_algebraMap (algebraMap 𝓀[K] 𝓀[L]).injective _
  refine le_antisymm (le_wildInertiaSubgroup_of_isProP (ringChar 𝓀[K])
    (isProP_comap_absoluteGaloisGroupExtend_wildInertiaSubgroup ι _) ?_) ?_
  · rw [← comap_absoluteGaloisGroupExtend_inertiaSubgroup ι]
    exact Subgroup.comap_mono (wildInertiaSubgroup_le_inertiaSubgroup K)
  · -- The image of `P_L` is a pro-`p` subgroup of `I_K`.
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_wildInertiaSubgroup_of_isProP (ringChar 𝓀[K])
      ((isProP_wildInertiaSubgroup L _).of_surjective
        ((absoluteGaloisGroupExtend K L ι).subgroupMap _)
        (((continuous_absoluteGaloisGroupExtend K L ι).comp continuous_subtypeVal).subtype_mk _)
        ((absoluteGaloisGroupExtend K L ι).subgroupMap_surjective _)) ?_
    rw [Subgroup.map_le_iff_le_comap, comap_absoluteGaloisGroupExtend_inertiaSubgroup ι]
    exact wildInertiaSubgroup_le_inertiaSubgroup L

/-- **Wild inertia along a finite extension.** An element of `G_L` lies in the wild inertia
subgroup of `L` exactly when its image in `G_K` lies in the wild inertia subgroup of `K`. -/
theorem absoluteGaloisGroupExtend_mem_wildInertiaSubgroup_iff {τ : Field.absoluteGaloisGroup L} :
    absoluteGaloisGroupExtend K L ι τ ∈ wildInertiaSubgroup K ↔ τ ∈ wildInertiaSubgroup L := by
  rw [← Subgroup.mem_comap, comap_absoluteGaloisGroupExtend_wildInertiaSubgroup]

/-- **Wild inertia along a finite extension, as an image.** The image of the wild inertia subgroup
of `L` in `G_K` is the part of the wild inertia subgroup of `K` lying in the image of `G_L`. -/
@[simp]
theorem map_absoluteGaloisGroupExtend_wildInertiaSubgroup :
    (wildInertiaSubgroup L).map (absoluteGaloisGroupExtend K L ι) =
      wildInertiaSubgroup K ⊓ (absoluteGaloisGroupExtend K L ι).range := by
  rw [← comap_absoluteGaloisGroupExtend_wildInertiaSubgroup ι, Subgroup.map_comap_eq, inf_comm]

end TauCeti
