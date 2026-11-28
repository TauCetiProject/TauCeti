/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.CompactQuotient
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Compactness of the adelic quotient of a rational subspace

Let `K` be a number field with adele ring `𝔸[K]`, let `ι` be a type and let `Z` be a
`K`-subspace of `ι → K`. Its *adelic points* `Z(𝔸)` are the `𝔸[K]`-span of the coordinatewise
image of `Z` in `ι → 𝔸[K]`, and its *rational points* `Z(K)` are the image of `Z` itself, an
additive subgroup of `Z(𝔸)`. When `Z` is finite-dimensional, the quotient `Z(𝔸) / Z(K)` is
compact.

A basis `b₁, …, b_d` of `Z` makes every adelic point a combination `∑ aⱼ bⱼ` with `aⱼ ∈ 𝔸[K]`.
Translating each coefficient by an element of `K` into the compact set of representatives of
`𝔸[K] / K` moves the point by a rational point into the image of a compact box `D^d` under the
continuous map `a ↦ ∑ aⱼ bⱼ`. When `ι` is finite every subspace is finite-dimensional, so the
compactness holds for all subspaces of `K^ι`.

## Main definitions

* `Submodule.adelicPoints`: the adelic points `Z(𝔸)` of a subspace `Z`.
* `Submodule.rationalPoints`: the rational points `Z(K)` as a subgroup of `Z(𝔸)`.

## Main results

* `Submodule.adelicPoints_le_iff`: `Z(𝔸)` lies in an `𝔸[K]`-submodule exactly when the images
  of the vectors of `Z` do.
* `Submodule.mem_adelicPoints_iff_exists_sum_smul`: the adelic points of `Z` are the
  `𝔸[K]`-combinations of the images of a basis of `Z`.
* `Submodule.exists_isCompact_forall_exists_sub_mem_rationalPoints`: a compact set of
  representatives for `Z(𝔸) / Z(K)`.
* `Submodule.compactSpace_adelicPoints_quotient`: the quotient `Z(𝔸) / Z(K)` is compact.

## References

* The statement is the compactness of `Z(𝔸)/Z(E)` used by the formal proof in the folder `grh`
  of https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (`New.Space.adelicPoints`, `New.Space.ratPoints`,
  `New.Space.compactSpace_adelicPoints_quotient`).
* It extends `TauCeti.GlobalNumberFields.compactSpace_quotient_principalSubgroup`, the case of
  the line.
-/

public section

open NumberField TauCeti.GlobalNumberFields
open scoped NumberField.AdeleRing Pointwise

namespace Submodule

variable {K : Type*} [Field K] [NumberField K] {ι : Type*}

/-- The *adelic points* `Z(𝔸)` of a `K`-subspace `Z` of `ι → K`: the `𝔸[K]`-span in
`ι → 𝔸[K]` of the coordinatewise images `i ↦ algebraMap K 𝔸[K] (z i)` of the vectors `z ∈ Z`. -/
noncomputable def adelicPoints (Z : Submodule K (ι → K)) : Submodule 𝔸[K] (ι → 𝔸[K]) :=
  span 𝔸[K] (Z.map ((Algebra.linearMap K 𝔸[K]).compLeft ι))

/-- The *rational points* `Z(K)` of a `K`-subspace `Z` of `ι → K`, as an additive subgroup of
its adelic points: the coordinatewise images of the vectors of `Z`. -/
noncomputable def rationalPoints (Z : Submodule K (ι → K)) : AddSubgroup Z.adelicPoints :=
  (Z.map ((Algebra.linearMap K 𝔸[K]).compLeft ι)).toAddSubgroup.comap
    Z.adelicPoints.subtype.toAddMonoidHom

/-- The coordinatewise image of a vector of `Z` is an adelic point of `Z`. -/
theorem algebraMap_comp_mem_adelicPoints {Z : Submodule K (ι → K)} {z : ι → K} (hz : z ∈ Z) :
    (fun i ↦ algebraMap K 𝔸[K] (z i)) ∈ Z.adelicPoints :=
  subset_span ⟨z, hz, rfl⟩

/-- The adelic points of `Z` lie in an `𝔸[K]`-submodule `N` of `ι → 𝔸[K]` if and only if the
coordinatewise images of all vectors of `Z` do. -/
theorem adelicPoints_le_iff {Z : Submodule K (ι → K)} {N : Submodule 𝔸[K] (ι → 𝔸[K])} :
    Z.adelicPoints ≤ N ↔ ∀ z ∈ Z, (fun i ↦ algebraMap K 𝔸[K] (z i)) ∈ N :=
  span_le.trans ⟨fun h z hz ↦ h ⟨z, hz, rfl⟩, fun h _ ⟨z, hz, hx⟩ ↦ hx ▸ h z hz⟩

/-- Taking adelic points is monotone in the subspace. -/
theorem adelicPoints_mono {Z W : Submodule K (ι → K)} (h : Z ≤ W) :
    Z.adelicPoints ≤ W.adelicPoints :=
  adelicPoints_le_iff.mpr fun _ hz ↦ algebraMap_comp_mem_adelicPoints (h hz)

/-- An adelic point of `Z` is a rational point if and only if it is the coordinatewise image of
a vector of `Z`. -/
@[simp]
theorem mem_rationalPoints_iff {Z : Submodule K (ι → K)} {x : Z.adelicPoints} :
    x ∈ Z.rationalPoints ↔ ∃ z ∈ Z, (fun i ↦ algebraMap K 𝔸[K] (z i)) = (x : ι → 𝔸[K]) :=
  Iff.rfl

/-- The adelic points of `Z` are the `𝔸[K]`-combinations of the coordinatewise images of a
basis `b` of `Z`. -/
theorem mem_adelicPoints_iff_exists_sum_smul {Z : Submodule K (ι → K)} {d : Type*}
    [Fintype d] (b : Module.Basis d K Z) {x : ι → 𝔸[K]} :
    x ∈ Z.adelicPoints ↔
      ∃ a : d → 𝔸[K], ∑ j, a j • (fun i ↦ algebraMap K 𝔸[K] ((b j : ι → K) i)) = x := by
  classical
  refine ⟨fun hx ↦ ?_, ?_⟩
  · refine (mem_span_range_iff_exists_fun 𝔸[K]).mp ?_
    refine span_le.mpr ?_ hx
    rintro _ ⟨z, hz, rfl⟩
    -- Expand `z` in the basis `b`; the coordinatewise image is `K`-linear.
    have hsum : z = ∑ j, b.repr ⟨z, hz⟩ j • (b j : ι → K) := by
      simpa only [coe_sum, coe_smul] using congrArg Subtype.val (b.sum_repr ⟨z, hz⟩).symm
    rw [hsum, map_sum]
    exact Submodule.sum_mem _ fun j _ ↦ by
      rw [map_smul]
      exact smul_of_tower_mem _ _ (subset_span ⟨j, rfl⟩)
  · rintro ⟨a, rfl⟩
    exact Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (algebraMap_comp_mem_adelicPoints (b j).property)

/-- **A compact set of representatives for `Z(𝔸) / Z(K)`.** For a finite-dimensional subspace `Z`
of `ι → K` there is a compact set `C` of adelic points of `Z` such that every adelic point of `Z`
is a rational point plus an element of `C`. -/
theorem exists_isCompact_forall_exists_sub_mem_rationalPoints (Z : Submodule K (ι → K))
    [FiniteDimensional K Z] :
    ∃ C : Set Z.adelicPoints, IsCompact C ∧
      ∀ x : Z.adelicPoints, ∃ y ∈ Z.rationalPoints, x - y ∈ C := by
  classical
  obtain ⟨D, hD, hcover⟩ := exists_isCompact_forall_exists_sub_algebraMap_mem K
  let b := Module.finBasis K Z
  let v : Fin (Module.finrank K Z) → ι → 𝔸[K] := fun j i ↦ algebraMap K 𝔸[K] ((b j : ι → K) i)
  let F : (Fin (Module.finrank K Z) → 𝔸[K]) → Z.adelicPoints := fun a ↦
    ⟨∑ j, a j • v j, (mem_adelicPoints_iff_exists_sum_smul b).mpr ⟨a, rfl⟩⟩
  have hF : Continuous F := (continuous_finsetSum _ fun j _ ↦
    (continuous_apply j).smul continuous_const).subtype_mk _
  refine ⟨F '' Set.univ.pi fun _ ↦ D, (isCompact_univ_pi fun _ ↦ hD).image hF, fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := (mem_adelicPoints_iff_exists_sum_smul b).mp x.property
  choose k hk using fun j ↦ hcover (a j)
  -- The rational point to subtract is the image of `w = ∑ kⱼ bⱼ ∈ Z`.
  let w : ι → K := ∑ j, k j • (b j : ι → K)
  have hw : w ∈ Z := Z.sum_mem fun j _ ↦ Z.smul_mem _ (b j).property
  refine ⟨⟨_, algebraMap_comp_mem_adelicPoints hw⟩, mem_rationalPoints_iff.mpr ⟨w, hw, rfl⟩,
    fun j ↦ a j - algebraMap K 𝔸[K] (k j), fun j _ ↦ hk j, Subtype.ext ?_⟩
  -- Both sides are `∑ (aⱼ - kⱼ) • vⱼ`; the image of `w` is `∑ kⱼ • vⱼ`.
  have hwv : (fun i ↦ algebraMap K 𝔸[K] (w i)) = ∑ j, algebraMap K 𝔸[K] (k j) • v j := by
    ext i
    simp [w, v, Finset.sum_apply, Algebra.smul_def]
  simp only [F, v, AddSubgroupClass.coe_sub, hwv, ← ha, sub_smul, Finset.sum_sub_distrib]

/-- **The adelic quotient of a rational subspace is compact.** For a finite-dimensional subspace
`Z` of `ι → K`, the quotient `Z(𝔸) / Z(K)` of its adelic points by its rational points is
compact. -/
instance compactSpace_adelicPoints_quotient (Z : Submodule K (ι → K)) [FiniteDimensional K Z] :
    CompactSpace (Z.adelicPoints ⧸ Z.rationalPoints) := by
  obtain ⟨C, hC, hcover⟩ := Z.exists_isCompact_forall_exists_sub_mem_rationalPoints
  have hCZ : C + (Z.rationalPoints : Set Z.adelicPoints) = Set.univ :=
    Set.eq_univ_of_forall fun x ↦
      let ⟨y, hy, hxy⟩ := hcover x
      ⟨x - y, hxy, y, hy, sub_add_cancel x y⟩
  exact ⟨QuotientAddGroup.image_mk_eq_univ_iff.mpr hCZ ▸ hC.image QuotientAddGroup.continuous_mk⟩

end Submodule
