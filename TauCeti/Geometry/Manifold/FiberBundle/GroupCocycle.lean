/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.GroupCocycle

/-!
# Smooth fibre bundles glued from smooth cocycles

Let `G` be a group modelled on `IG`, acting `C^n`-smoothly on a manifold `F` modelled on `IF`, and
let `c i j : B → G` be a cocycle on an open cover `U` of a manifold `B` modelled on `IB`, with the
composition convention `c j k b * c i j b = c i k b` of `TauCeti.fiberBundleCoreOfGroupCocycle`.
When the transition functions `c i j` are `C^n` on the overlaps, the bundle glued from `c` is a
`C^n` fibre bundle (`TauCeti.contMDiffFiberBundle_fiberBundleCoreOfGroupCocycle`). Hence, when
`B` and `F` are `C^n` manifolds, its total space, charted through the fibre by
`TauCeti.ManifoldTotalSpace`, is a `C^n` manifold whose projection is a `C^n` submersion.

With `F = G` acted on by left multiplication, the glued bundle is a principal `G`-bundle
(`TauCeti.principalBundle_fiberBundleCoreOfGroupCocycle`). Thus a `C^n` cocycle with values in a
`C^n` Lie group glues to a `C^n` principal bundle, whose charts have the transition functions `c`,
and whose right action and division map are `C^n`.

Changing the charts by a `C^n` `0`-cochain `h` with values in a `C^n` Lie group replaces `c` by the
cohomologous cocycle `c' i j b = (h j b)⁻¹ * c i j b * h i b`. The homeomorphism
`TauCeti.homeomorphOfCohomologous` between the two glued bundles, acting by `(h i b)⁻¹` on the
fibre coordinates of chart `i`, is then a `C^n` diffeomorphism of total spaces
(`TauCeti.diffeomorphOfCohomologous`), which is equivariant when `F = G`
(`TauCeti.homeomorphOfCohomologous_mk_smul`). Neither statement needs smoothness of `c` or `c'`.

## Main results

* `TauCeti.contMDiffFiberBundle_fiberBundleCoreOfGroupCocycle`: a `C^n` cocycle glues to a `C^n`
  fibre bundle.
* `TauCeti.diffeomorphOfCohomologous`: bundles glued from cocycles that are cohomologous through a
  `C^n` `0`-cochain are `C^n` diffeomorphic over the base.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.2 and Corollary 10.8 (principal bundles from cocycles, and the change of cocycle under a
  change of local sections).
-/

public section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace TauCeti

universe u v w t

variable {n : ℕ∞ω} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG}
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF}
  {ι : Type u} {B : Type v} {G : Type w} [Group G] [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace G] [ChartedSpace HG G]
  {F : Type t} [TopologicalSpace F] [ChartedSpace HF F] [MulAction G F] [ContinuousSMul G F]
  (U : ι → Set B) (c : ι → ι → B → G)
  (hc : ∀ i j k b, b ∈ U i ∩ U j ∩ U k → c j k b * c i j b = c i k b)
  (hU : ∀ i, IsOpen (U i)) (indexAt : B → ι) (hindex : ∀ b, b ∈ U (indexAt b))
  (hcontinuous : ∀ i j, ContinuousOn (c i j) (U i ∩ U j))

variable (n IB IF F) in
/-- **A `C^n` cocycle glues to a `C^n` fibre bundle.** If `G` acts `C^n`-smoothly on `F` and the
transition functions `c i j` are `C^n` on the overlaps, then the bundle glued from `c` is a `C^n`
fibre bundle. -/
theorem contMDiffFiberBundle_fiberBundleCoreOfGroupCocycle [ContMDiffSMul IG IF n G F]
    (hsmooth : ∀ i j, ContMDiffOn IB IG n (c i j) (U i ∩ U j)) :
    ContMDiffFiberBundle n F
      (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber IB IF where
  contMDiffOn_coordChange e e' he he' := by
    obtain ⟨i, rfl⟩ := he.out
    obtain ⟨j, rfl⟩ := he'.out
    simp only [fiberBundleCoreOfGroupCocycle_localTriv_baseSet]
    refine (((hsmooth i j).comp contMDiffOn_fst fun p hp ↦ (mem_prod.1 hp).1).smul
      contMDiffOn_snd).congr ?_
    rintro ⟨b, v⟩ ⟨hb, -⟩
    exact fiberBundleCoreOfGroupCocycle_localTriv_coordChange U c hc F hU indexAt hindex
      hcontinuous i j hb v

variable {U c hc hU indexAt hindex hcontinuous} (c' : ι → ι → B → G)
  (hc' : ∀ i j k b, b ∈ U i ∩ U j ∩ U k → c' j k b * c' i j b = c' i k b)
  (hcontinuous' : ∀ i j, ContinuousOn (c' i j) (U i ∩ U j))

/-- A fibrewise map between bundles glued from `c` and `c'`, which acts by `k i b` on the fibre
coordinates of chart `i`, is `C^n` for the charts through the fibre when the `k i` are `C^n` on the
charts. -/
private theorem contMDiff_of_localTriv_snd [ContMDiffSMul IG IF n G F]
    (f : TotalSpace F (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber →
      TotalSpace F (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').Fiber)
    (k : ι → B → G) (hk : ∀ i, ContMDiffOn IB IG n (k i) (U i)) (hproj : ∀ p, (f p).proj = p.proj)
    (hf : ∀ i b (v : F), b ∈ U i →
      ((fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').localTriv i
          (f ⟨b, v⟩)).2 =
        k i b •
          ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv i
            ⟨b, v⟩).2) :
    ContMDiff (IB.prod IF) (IB.prod IF) n
      fun x ↦
        ManifoldTotalSpace.homeomorph F _ (f ((ManifoldTotalSpace.homeomorph F _).symm x)) := by
  -- The trivialization of a glued bundle at a base point is the chart chosen there.
  have htriv : ∀ b, trivializationAt F
      (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber b =
        (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv
          (indexAt b) := fun b ↦
    congrArg (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv
      (congrFun (fiberBundleCoreOfGroupCocycle_indexAt U c hc F hU indexAt hindex hcontinuous) b)
  have htriv' : ∀ b, trivializationAt F
      (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').Fiber b =
        (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').localTriv
          (indexAt b) := fun b ↦
    congrArg (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').localTriv
      (congrFun (fiberBundleCoreOfGroupCocycle_indexAt U c' hc' F hU indexAt hindex hcontinuous') b)
  intro x₀
  have hproj₀ : ContMDiffAt (IB.prod IF) IB n
      (fun x ↦ ((ManifoldTotalSpace.homeomorph F _).symm x).proj) x₀ :=
    ManifoldTotalSpace.contMDiff_proj n F
      (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber IB IF x₀
  refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨?_, ?_⟩
  · simpa only [hproj] using hproj₀
  · set i := indexAt ((ManifoldTotalSpace.homeomorph F _).symm x₀).proj
    have hU₀ : (fun x ↦ ((ManifoldTotalSpace.homeomorph F _).symm x).proj) ⁻¹' U i ∈ 𝓝 x₀ :=
      hproj₀.continuousAt.preimage_mem_nhds ((hU i).mem_nhds (hindex _))
    have hsnd := ManifoldTotalSpace.contMDiffAt_trivializationAt_snd n IB IF x₀
    rw [htriv] at hsnd
    rw [hproj, htriv']
    refine ContMDiffAt.congr_of_eventuallyEq ?_
      (eventually_of_mem hU₀ fun x hx ↦ hf i _ ((ManifoldTotalSpace.homeomorph F _).symm x).2 hx)
    exact (((hk i).contMDiffAt ((hU i).mem_nhds (hindex _))).comp x₀ hproj₀).smul hsnd

variable [LieGroup IG n G] [ContMDiffSMul IG IF n G F] (h : ι → B → G)
  (hh : ∀ i, ContMDiffOn IB IG n (h i) (U i))
  (hcc' : ∀ i j b, b ∈ U i ∩ U j → c' i j b = (h j b)⁻¹ * c i j b * h i b)

variable (IF) in
/-- **Cohomologous cocycles glue to diffeomorphic bundles.** If `c' i j = (h j)⁻¹ * c i j * h i`
on the overlaps for a `C^n` `0`-cochain `h` with values in a `C^n` Lie group acting `C^n`-smoothly
on `F`, then the total spaces of the bundles glued from `c` and `c'`, charted through the fibre,
are `C^n` diffeomorphic over the base, by the map acting by `(h i b)⁻¹` on the fibre coordinates of
chart `i`. -/
def diffeomorphOfCohomologous :
    ManifoldTotalSpace F
        (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber
      ≃ₘ^n⟮IB.prod IF, IB.prod IF⟯
    ManifoldTotalSpace F
      (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').Fiber :=
  haveI := topologicalGroup_of_lieGroup IG n (G := G)
  { toEquiv := ((ManifoldTotalSpace.homeomorph F _).symm.trans
      ((homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h
        (fun i ↦ (hh i).continuousOn) hcc').trans (ManifoldTotalSpace.homeomorph F _))).toEquiv
    contMDiff_toFun := contMDiff_of_localTriv_snd c' hc' hcontinuous'
      (homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h _ hcc')
      (fun i b ↦ (h i b)⁻¹) (fun i ↦ (hh i).inv)
      (proj_homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h _
        hcc')
      fun i _ v hb ↦ congrArg Prod.snd
        (localTriv_homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc'
          hcontinuous' h _ hcc' i hb v)
    contMDiff_invFun := contMDiff_of_localTriv_snd c hc hcontinuous
      (homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h _
        hcc').symm h hh
      (proj_homeomorphOfCohomologous_symm U c hc hU indexAt hindex hcontinuous c' hc'
        hcontinuous' h _ hcc')
      fun i _ v hb ↦ congrArg Prod.snd
        (localTriv_homeomorphOfCohomologous_symm U c hc hU indexAt hindex hcontinuous c' hc'
          hcontinuous' h _ hcc' i hb v) }

@[simp]
theorem diffeomorphOfCohomologous_apply (b : B) (v : F) :
    diffeomorphOfCohomologous IF c' hc' hcontinuous' h hh hcc'
        (ManifoldTotalSpace.homeomorph F
          (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber ⟨b, v⟩) =
      ManifoldTotalSpace.homeomorph F
        (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').Fiber
        ⟨b, (h (indexAt b) b)⁻¹ • v⟩ := by
  rw [← Diffeomorph.coe_toEquiv]
  simp [diffeomorphOfCohomologous]

@[simp]
theorem diffeomorphOfCohomologous_symm_apply (b : B) (v : F) :
    (diffeomorphOfCohomologous IF c' hc' hcontinuous' h hh hcc').symm
        (ManifoldTotalSpace.homeomorph F
          (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').Fiber ⟨b, v⟩) =
      ManifoldTotalSpace.homeomorph F
        (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber
        ⟨b, h (indexAt b) b • v⟩ := by
  rw [← Diffeomorph.toEquiv_coe_symm]
  simp [diffeomorphOfCohomologous]

end TauCeti
