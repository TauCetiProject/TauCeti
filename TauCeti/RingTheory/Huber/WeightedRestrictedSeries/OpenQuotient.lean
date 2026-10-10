/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.FirstCountable
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Surjective

import Mathlib.Data.Finsupp.Encodable
import TauCeti.Topology.Algebra.Nonarchimedean.Completion.Surjective
import TauCeti.Topology.LiftTendstoCofinite

/-!
# Restricted series preserve open quotient maps

An open quotient map `φ : A → B` of nonarchimedean rings, with `𝓝 (0 : A)` countably generated,
induces open quotient maps `A⟨X₁, …, Xₖ⟩ → B⟨X₁, …, Xₖ⟩` coefficientwise, both on the rings of
restricted power series (`TauCeti.Huber.weightedRestrictedSubring` at the trivial weight) and on
their separated completions (`TauCeti.Huber.restrictedMvPowerSeriesCompletion`).

Surjectivity on the uncompleted rings is
`IsOpenQuotientMap.weightedMap_one_weight_surjective`. Openness is the additional point: a
restricted series over `B` whose coefficients all lie in `φ(U)`, for an open subgroup `U` of `A`,
lifts to a restricted series over `A` whose coefficients all lie in `U`. The completed statement
then follows from the general fact that the completion of a continuous open surjection out of a
first-countable nonarchimedean group is again open and surjective
(`AddMonoidHom.isOpenMap_completion`, `AddMonoidHom.surjective_completion`).

This is what makes strict topological finite type stable under composition: the coefficientwise
map `A⟨X⟩⟨Y⟩ → B⟨Y⟩` induced by a presentation `A⟨X⟩ ↠ B` is again a presentation.

## Main results

* `IsOpenQuotientMap.weightedMap_one_weight`: the coefficientwise map on restricted power series
  is an open quotient map.
* `IsOpenQuotientMap.weightedMapCompletion_one_weight`: so is the induced map on the completed
  algebras `A⟨X₁, …, Xₖ⟩ → B⟨X₁, …, Xₖ⟩`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §5.6 and Proposition 6.33.
-/

public section

open Filter Topology UniformSpace

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]

/-- **An open quotient map induces an open quotient map on restricted power series**, provided
`𝓝 (0 : A)` is countably generated. Besides surjectivity
(`IsOpenQuotientMap.weightedMap_one_weight_surjective`), the content is that a restricted series
over `B` with every coefficient in `φ(U)`, for an open subgroup `U` of `A`, is the image of a
restricted series over `A` with every coefficient in `U`. -/
theorem _root_.IsOpenQuotientMap.weightedMap_one_weight [(𝓝 (0 : A)).IsCountablyGenerated]
    {φ : A →+* B} (hq : IsOpenQuotientMap φ) :
    IsOpenQuotientMap (weightedMap (k := k) hq.continuous isWeightFamily_one_weight
      isWeightFamily_one_weight fun _ ↦ by simp) := by
  set F := weightedMap (k := k) hq.continuous isWeightFamily_one_weight
    isWeightFamily_one_weight fun _ ↦ by simp
  refine ⟨hq.weightedMap_one_weight_surjective, continuous_weightedMap .., ?_⟩
  -- openness of an additive map is decided at zero, on the basic neighbourhoods `U⟨X⟩`
  refine IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr <|
    ((hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).map F).ge_iff.mpr
      fun U _ ↦ ?_
  let V : OpenAddSubgroup B :=
    { U.toAddSubgroup.map (φ : A →+ B) with
      isOpen' := hq.isOpenMap _ U.isOpen }
  refine Filter.mem_of_superset
    ((hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).mem_of_mem (i := V) trivial)
    fun g hg ↦ ?_
  -- every coefficient of `g` has a preimage in `U`
  have hgU : ∀ ν, ∃ u ∈ U, φ u = MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B) := by
    intro ν
    simpa [V] using mem_weightedNhd.mp hg ν
  choose u huU hu using hgU
  -- a family of preimages tending to zero, which then lies in `U` for almost all indices
  obtain ⟨L, hL, hL0⟩ := exists_lift_tendsto_cofinite_nhds φ hq.surjective
    (map_zero φ ▸ hq.isOpenMap.nhds_le 0)
    (fun ν ↦ MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B))
    ((isWeightedRestricted_one_weight_iff (A := B)).mp (mem_weightedRestrictedSubring.mp g.2))
  classical
  let L' : MvPowerSeries (Fin k) A := fun ν ↦ if L ν ∈ U then L ν else u ν
  have hL' : ∀ ν, MvPowerSeries.coeff ν L' = if L ν ∈ U then L ν else u ν :=
    MvPowerSeries.coeff_apply L'
  have hL'U : ∀ ν, MvPowerSeries.coeff ν L' ∈ U := fun ν ↦ by
    by_cases h : L ν ∈ U <;> simp [hL', h, huU]
  have hL'φ : ∀ ν, φ (MvPowerSeries.coeff ν L') = MvPowerSeries.coeff ν
      (g : MvPowerSeries (Fin k) B) := fun ν ↦ by
    by_cases h : L ν ∈ U <;> simp [hL', h, hL, hu]
  have hL'0 : Tendsto (fun ν ↦ MvPowerSeries.coeff ν L') cofinite (𝓝 0) :=
    hL0.congr' <| (hL0.eventually_mem (U.isOpen.mem_nhds U.zero_mem)).mono fun ν h ↦
      ((hL' ν).trans (ite_eq_left h)).symm
  refine ⟨⟨L', mem_weightedRestrictedSubring.mpr
    ((isWeightedRestricted_one_weight_iff (A := A)).mpr hL'0)⟩,
    mem_weightedNhd.mpr fun ν ↦ by simpa using hL'U ν, Subtype.ext ?_⟩
  ext ν
  simp [F, hL'φ]

/-- **An open quotient map induces an open quotient map `A⟨X₁, …, Xₖ⟩ → B⟨X₁, …, Xₖ⟩` on the
completed restricted power-series algebras**, provided `𝓝 (0 : A)` is countably generated. -/
theorem _root_.IsOpenQuotientMap.weightedMapCompletion_one_weight
    [(𝓝 (0 : A)).IsCountablyGenerated] {φ : A →+* B} (hq : IsOpenQuotientMap φ) :
    IsOpenQuotientMap (weightedMapCompletion (k := k) hq.continuous isWeightFamily_one_weight
      isWeightFamily_one_weight fun _ ↦ by simp) := by
  have hF := hq.weightedMap_one_weight (k := k)
  set F := weightedMap (k := k) hq.continuous isWeightFamily_one_weight
    isWeightFamily_one_weight fun _ ↦ by simp
  -- the completed map is the completion of `F` as an additive group homomorphism
  have heq : ⇑(weightedMapCompletion (k := k) hq.continuous isWeightFamily_one_weight
      isWeightFamily_one_weight fun _ ↦ by simp) =
      ⇑(F.toAddMonoidHom.completion hF.continuous) :=
    Completion.ext (continuous_weightedMapCompletion ..)
      (AddMonoidHom.continuous_completion _ _) fun a ↦ by simp [F]
  rw [heq]
  exact ⟨F.toAddMonoidHom.surjective_completion hF.continuous hF.surjective hF.isOpenMap,
    AddMonoidHom.continuous_completion _ _,
    F.toAddMonoidHom.isOpenMap_completion hF.continuous hF.isOpenMap⟩

end TauCeti.Huber
