/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Principal.Basic

/-!
# Fiber bundles from group-valued transition functions

A continuous group action on an arbitrary topological fiber turns a continuous group-valued
cocycle on an open cover into native `FiberBundleCore` data. The composition convention is
`c j k b * c i j b = c i k b`: the transition from chart `i` to chart `j` acts on the left.
Normalization and inverse identities follow from this cocycle equation.

`TauCeti.fiberBundleCoreOfGroupCocycle` delegates the bundle topology, local trivializations,
and joint coordinate changes to Mathlib's `FiberBundleCore` construction. Its transition
functions and inverses act jointly continuously on the base and fiber; no topology on the
homeomorphism group of the fiber, and no point in the fiber, is needed. The resulting core's
native `localTriv` and `fiberBundle` provide the actual bundle and its charts.

Changing the charts by a continuous `0`-cochain `h` replaces the cocycle `c` by the cohomologous
cocycle `c' i j b = (h j b)⁻¹ * c i j b * h i b`, and does not change the bundle:
`TauCeti.homeomorphOfCohomologous` is a homeomorphism between the two glued total spaces which
covers the identity of the base and acts by `(h i b)⁻¹` on the fibre coordinates of chart `i`.

When the fibre is the group itself, acted on by left multiplication, the right multiplication of
the group on each fibre makes the glued bundle a principal bundle (the instance
`TauCeti.principalBundle_fiberBundleCoreOfGroupCocycle`), and the homeomorphism between the bundles
glued from cohomologous cocycles is equivariant. The local section `s j` of chart `j`, the point
with fibre coordinate `1` there, has fibre coordinate `c j i b` in chart `i`
(`TauCeti.fiberBundleCoreOfGroupCocycle_localTriv_symm_apply`); by equivariance of the charts, the
local sections of the charts thus satisfy `s j = s i • c j i`. In terms of the cocycle
`g i j = c j i`, they satisfy `s j = s i • g i j`, the cocycle condition reads
`g i j * g j k = g i k`, and the cohomologous cocycle is `h i⁻¹ * g i j * h j`, the cocycle of the
sections `s i • h i`.

## Main definitions

* `TauCeti.fiberBundleCoreOfGroupCocycle`: the bundle glued from a group-valued cocycle.
* `TauCeti.homeomorphOfCohomologous`: the bundles glued from cohomologous cocycles are
  homeomorphic over the base.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.2 and Corollary 10.8 (principal bundles from cocycles, and the change of cocycle under a
  change of local sections).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2–§3
  (construction of a bundle from coordinate transformations, and equivalent coordinate bundles).
-/

public section

universe u v w t

open Bundle MulOpposite Set Topology

namespace TauCeti

variable {ι : Type u} {B : Type v} {G : Type w} [Group G]
    (U : ι → Set B) (c : ι → ι → B → G)
    (hc : ∀ i j k b, b ∈ U i ∩ U j ∩ U k → c j k b * c i j b = c i k b)

include hc

/-- A group-valued transition cocycle is the identity on each diagonal chart. -/
lemma groupCocycle_self (i : ι) {b : B} (hb : b ∈ U i) : c i i b = 1 :=
  mul_eq_left.mp (hc i i i b ⟨⟨hb, hb⟩, hb⟩)

/-- Reversing an overlap transition inverts the group element. -/
lemma groupCocycle_symm (i j : ι) {b : B} (hb : b ∈ U i ∩ U j) :
    c j i b = (c i j b)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  exact (hc i j i b ⟨hb, hb.1⟩).trans (groupCocycle_self U c hc i hb.1)

variable [TopologicalSpace B] [TopologicalSpace G]
    (F : Type t) [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F]
    (hU : ∀ i, IsOpen (U i)) (indexAt : B → ι) (hindex : ∀ b, b ∈ U (indexAt b))
    (hcontinuous : ∀ i j, ContinuousOn (c i j) (U i ∩ U j))

/-- The native fiber bundle core whose transition from chart `i` to chart `j` acts by `c i j`.
The supplied index chooses a cover member at every base point. Only continuity of the action
is required; the fiber may be empty or have no separation properties. -/
def fiberBundleCoreOfGroupCocycle : FiberBundleCore ι B F where
  baseSet := U
  isOpen_baseSet := hU
  indexAt := indexAt
  mem_baseSet_at := hindex
  coordChange i j b v := c i j b • v
  coordChange_self i b hb v := by rw [groupCocycle_self U c hc i hb, one_smul]
  continuousOn_coordChange i j :=
    continuous_smul.comp_continuousOn ((hcontinuous i j).prodMap continuousOn_id)
  coordChange_comp i j k b hb v := by rw [← mul_smul, hc i j k b hb]

/-- Each native local trivialization has the supplied cover member as its base. -/
@[simp]
lemma fiberBundleCoreOfGroupCocycle_localTriv_baseSet (i : ι) :
    ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv i).baseSet =
      U i := (rfl)

/-- The bundle core retains the supplied choice of chart. -/
@[simp]
lemma fiberBundleCoreOfGroupCocycle_indexAt :
    (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).indexAt =
      indexAt := (rfl)

/-- The trivialization of the glued bundle at a base point is the chart chosen there. -/
@[simp]
lemma trivializationAt_fiberBundleCoreOfGroupCocycle (b : B) :
    trivializationAt F (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber
        b =
      (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv
        (indexAt b) := (rfl)

/-- The core's coordinate change is the given group action. -/
@[simp]
lemma fiberBundleCoreOfGroupCocycle_coordChange (i j : ι) (b : B) (v : F) :
    (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).coordChange i j b v =
      c i j b • v := (rfl)

/-- The joint forward coordinate change fixes the base and acts by the overlap cocycle. -/
lemma fiberBundleCoreOfGroupCocycle_trivChange_apply (i j : ι) (p : B × F) :
    (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).trivChange i j p =
      (p.1, c i j p.1 • p.2) := (rfl)

/-- On an overlap, the inverse joint coordinate change acts by the inverse group element. -/
lemma fiberBundleCoreOfGroupCocycle_trivChange_symm_apply (i j : ι) (p : B × F)
    (hp : p.1 ∈ U i ∩ U j) :
    ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).trivChange i j).symm
        p = (p.1, (c i j p.1)⁻¹ • p.2) := by
  exact congrArg (fun g : G ↦ (p.1, g • p.2)) (groupCocycle_symm U c hc i j hp)

/-- The actual native bundle charts have the prescribed group-valued transition function. -/
lemma fiberBundleCoreOfGroupCocycle_localTriv_coordChange (i j : ι) {b : B}
    (hb : b ∈ U i ∩ U j) (v : F) :
    ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv i).coordChange
      ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv j) b v =
        c i j b • v := by
  simp only [Bundle.Trivialization.coordChange, FiberBundleCore.localTriv_symm_apply,
    FiberBundleCore.localTriv_apply, fiberBundleCoreOfGroupCocycle_coordChange,
    fiberBundleCoreOfGroupCocycle_indexAt]
  rw [← mul_smul, hc i (indexAt b) j b ⟨⟨hb.1, hindex b⟩, hb.2⟩]

/-- The point with fibre coordinate `v` in chart `j` has fibre coordinate `c j i b • v` in chart
`i`. -/
lemma fiberBundleCoreOfGroupCocycle_localTriv_symm_apply (i j : ι) {b : B} (hb : b ∈ U i ∩ U j)
    (v : F) :
    ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv
        j).toOpenPartialHomeomorph.symm (b, v) =
      ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv
        i).toOpenPartialHomeomorph.symm (b, c j i b • v) := by
  simp only [FiberBundleCore.localTriv_symm_apply, fiberBundleCoreOfGroupCocycle_coordChange,
    fiberBundleCoreOfGroupCocycle_indexAt, smul_smul, hc j i (indexAt b) b ⟨⟨hb.2, hb.1⟩, hindex b⟩]

/-! ### Cohomologous cocycles -/

section Cohomologous

variable {F} (c' : ι → ι → B → G)
    (hc' : ∀ i j k b, b ∈ U i ∩ U j ∩ U k → c' j k b * c' i j b = c' i k b)
    (hcontinuous' : ∀ i j, ContinuousOn (c' i j) (U i ∩ U j))

/-- A fibrewise map between bundles glued from `c` and `c'`, which acts by `k i b` on the fibre
coordinates of chart `i`, is continuous when the `k i` are continuous on the charts. -/
private lemma continuous_of_localTriv_snd
    (f : TotalSpace F (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber →
      TotalSpace F (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').Fiber)
    (k : ι → B → G) (hk : ∀ i, ContinuousOn (k i) (U i)) (hproj : ∀ p, (f p).proj = p.proj)
    (hf : ∀ i b (v : F), b ∈ U i →
      ((fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').localTriv i
          (f ⟨b, v⟩)).2 =
        k i b •
          ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv i
            ⟨b, v⟩).2) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ (FiberBundle.continuousAt_totalSpace F f).2
    ⟨?_, ?_⟩
  · simp_rw [hproj]
    exact (FiberBundle.continuous_proj F _).continuousAt
  · -- The trivialization at the base point is the chart `i` chosen there.
    set i := indexAt p₀.proj
    have hU₀ : (fun p ↦ TotalSpace.proj p) ⁻¹' U i ∈ 𝓝 p₀ :=
      (FiberBundle.continuous_proj F _).continuousAt.preimage_mem_nhds
        ((hU i).mem_nhds (hindex _))
    rw [hproj]
    refine ContinuousAt.congr ?_ (Filter.eventually_of_mem hU₀ fun p hp ↦ (hf i _ p.2 hp).symm)
    refine ContinuousAt.smul (((hk i).continuousAt ((hU i).mem_nhds (hindex _))).comp
      (FiberBundle.continuous_proj F _).continuousAt) ?_
    exact continuous_snd.continuousAt.comp
      (((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv
        i).continuousAt ((Trivialization.mem_source _).2 (hindex _)))

variable [IsTopologicalGroup G] (h : ι → B → G) (hh : ∀ i, ContinuousOn (h i) (U i))
    (hcc' : ∀ i j b, b ∈ U i ∩ U j → c' i j b = (h j b)⁻¹ * c i j b * h i b)

/-- **Cohomologous cocycles glue to homeomorphic bundles.** If `c' i j = (h j)⁻¹ * c i j * h i` on
the overlaps for a continuous `0`-cochain `h`, then the bundles glued from `c` and `c'` are
homeomorphic over the base, by the map acting by `(h i b)⁻¹` on the fibre coordinates of chart
`i`. -/
def homeomorphOfCohomologous :
    TotalSpace F (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber ≃ₜ
      TotalSpace F (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').Fiber
    where
  -- The fibres are type synonyms of `F`, so the action of `G` on `F` is supplied explicitly.
  toFun p := ⟨p.proj, @HSMul.hSMul G F F _ (h (indexAt p.proj) p.proj)⁻¹ p.2⟩
  invFun p := ⟨p.proj, @HSMul.hSMul G F F _ (h (indexAt p.proj) p.proj) p.2⟩
  left_inv := fun ⟨b, v⟩ ↦ congrArg (TotalSpace.mk b) (smul_inv_smul (α := F) _ v)
  right_inv := fun ⟨b, v⟩ ↦ congrArg (TotalSpace.mk b) (inv_smul_smul (α := F) _ v)
  continuous_toFun := by
    refine continuous_of_localTriv_snd U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' _
      (fun i b ↦ (h i b)⁻¹) (fun i ↦ (hh i).inv) (fun _ ↦ rfl) fun i b v hb ↦ ?_
    simp only [FiberBundleCore.localTriv_apply, fiberBundleCoreOfGroupCocycle_coordChange,
      fiberBundleCoreOfGroupCocycle_indexAt, smul_smul, hcc' _ i b ⟨hindex b, hb⟩,
      mul_inv_cancel_right]
  continuous_invFun := by
    refine continuous_of_localTriv_snd U c' hc' hU indexAt hindex hcontinuous' c hc hcontinuous _
      h hh (fun _ ↦ rfl) fun i b v hb ↦ ?_
    simp only [FiberBundleCore.localTriv_apply, fiberBundleCoreOfGroupCocycle_coordChange,
      fiberBundleCoreOfGroupCocycle_indexAt, smul_smul, hcc' _ i b ⟨hindex b, hb⟩, mul_assoc,
      mul_inv_cancel_left]

@[simp]
lemma homeomorphOfCohomologous_apply (b : B) (v : F) :
    homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h hh hcc'
        ⟨b, v⟩ = ⟨b, (h (indexAt b) b)⁻¹ • v⟩ :=
  (rfl)

@[simp]
lemma homeomorphOfCohomologous_symm_apply (b : B) (v : F) :
    (homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h hh
        hcc').symm ⟨b, v⟩ = ⟨b, h (indexAt b) b • v⟩ :=
  (rfl)

/-- The homeomorphism between the bundles glued from cohomologous cocycles covers the identity of
the base. -/
@[simp]
lemma proj_homeomorphOfCohomologous (p : TotalSpace F
      (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).Fiber) :
    (homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h hh hcc'
      p).proj = p.proj :=
  (rfl)

/-- The inverse of the homeomorphism between the bundles glued from cohomologous cocycles covers
the identity of the base. -/
@[simp]
lemma proj_homeomorphOfCohomologous_symm (p : TotalSpace F
      (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').Fiber) :
    ((homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h hh
      hcc').symm p).proj = p.proj :=
  (rfl)

/-- Over the chart `i`, the homeomorphism between the bundles glued from cohomologous cocycles acts
by `(h i b)⁻¹` on the fibre coordinates of chart `i`. -/
lemma localTriv_homeomorphOfCohomologous (i : ι) {b : B} (hb : b ∈ U i) (v : F) :
    (fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').localTriv i
        (homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h hh
          hcc' ⟨b, v⟩) =
      (b, (h i b)⁻¹ •
        ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv i
          ⟨b, v⟩).2) := by
  simp only [homeomorphOfCohomologous_apply, FiberBundleCore.localTriv_apply,
    fiberBundleCoreOfGroupCocycle_coordChange, fiberBundleCoreOfGroupCocycle_indexAt, smul_smul,
    hcc' _ i b ⟨hindex b, hb⟩, mul_inv_cancel_right]

/-- Over the chart `i`, the inverse homeomorphism acts by `h i b` on the fibre coordinates of chart
`i`. -/
lemma localTriv_homeomorphOfCohomologous_symm (i : ι) {b : B} (hb : b ∈ U i) (v : F) :
    (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv i
        ((homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h hh
          hcc').symm ⟨b, v⟩) =
      (b, h i b •
        ((fiberBundleCoreOfGroupCocycle U c' hc' F hU indexAt hindex hcontinuous').localTriv i
          ⟨b, v⟩).2) := by
  simp only [homeomorphOfCohomologous_symm_apply, FiberBundleCore.localTriv_apply,
    fiberBundleCoreOfGroupCocycle_coordChange, fiberBundleCoreOfGroupCocycle_indexAt, smul_smul,
    hcc' _ i b ⟨hindex b, hb⟩, mul_assoc, mul_inv_cancel_left]

end Cohomologous

/-! ### Principal bundles from cocycles -/

section Principal

variable [ContinuousMul G]

/-- The fibres of the bundle glued from a cocycle, with the group itself as fibre acted on by left
multiplication, carry the right action of the group by right multiplication. -/
instance (b : B) :
    MulAction Gᵐᵒᵖ
      ((fiberBundleCoreOfGroupCocycle U c hc G hU indexAt hindex hcontinuous).Fiber b) :=
  inferInstanceAs (MulAction Gᵐᵒᵖ G)

/-- The bundle glued from a cocycle, with the group itself as fibre acted on by left
multiplication, is a principal bundle for the right multiplication on its fibres: the charts act
on fibre coordinates by left multiplications, which commute with right multiplications. -/
instance principalBundle_fiberBundleCoreOfGroupCocycle :
    PrincipalBundle G (fiberBundleCoreOfGroupCocycle U c hc G hU indexAt hindex hcontinuous).Fiber
    where
  isEquivariant_trivialization' e he := by
    obtain ⟨i, rfl⟩ := he.out
    exact ⟨fun b _ v g ↦ (mul_assoc _ _ _).symm⟩

end Principal

/-- The homeomorphism between the principal bundles glued from cohomologous cocycles is
equivariant for the right actions on the fibres. -/
lemma homeomorphOfCohomologous_mk_smul [IsTopologicalGroup G] (c' : ι → ι → B → G)
    (hc' : ∀ i j k b, b ∈ U i ∩ U j ∩ U k → c' j k b * c' i j b = c' i k b)
    (hcontinuous' : ∀ i j, ContinuousOn (c' i j) (U i ∩ U j)) (h : ι → B → G)
    (hh : ∀ i, ContinuousOn (h i) (U i))
    (hcc' : ∀ i j b, b ∈ U i ∩ U j → c' i j b = (h j b)⁻¹ * c i j b * h i b)
    (p : TotalSpace G (fiberBundleCoreOfGroupCocycle U c hc G hU indexAt hindex hcontinuous).Fiber)
    (g : G) :
    homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h hh hcc'
        ⟨p.proj, op g • p.2⟩ =
      ⟨(homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h hh
          hcc' p).proj,
        op g • (homeomorphOfCohomologous U c hc hU indexAt hindex hcontinuous c' hc' hcontinuous' h
          hh hcc' p).2⟩ :=
  -- Left multiplication by `(h i b)⁻¹` commutes with right multiplication by `g`.
  congrArg (TotalSpace.mk p.proj) (mul_assoc (h (indexAt p.proj) p.proj)⁻¹ (p.2 : G) g).symm

end TauCeti
