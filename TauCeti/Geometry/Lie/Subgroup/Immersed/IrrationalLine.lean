/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Immersed.Basic
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.Algebra.TypeTags
public import Mathlib.NumberTheory.Real.Irrational
import TauCeti.Analysis.Fourier.Kronecker
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.NumberTheory.Real.Irrational
import TauCeti.Topology.Algebra.Group.Subgroup
import TauCeti.Topology.LocallyConstant.Lindelof

/-!
# The irrational line as an immersed Lie subgroup

For an irrational real slope `θ`, the map `t ↦ (t mod ℤ, θt mod ℤ)` is an injective smooth
immersion of the real line into the two-dimensional torus. Its image is a connected immersed
Lie subgroup, dense and not closed. The source retains its ordinary real topology. In contrast,
the image with the inherited subspace topology is neither locally compact nor locally connected.

All torus and real-line manifolds use their existing native charts. Multiplicative type tags
express the additive groups in the multiplicative immersed-subgroup interface.

## Main declarations

* `TauCeti.Lie.IrrationalLine.hom`: the line of real slope `θ` in the torus.
* `TauCeti.Lie.IrrationalLine.hom_apply`: its two circle coordinates.
* `TauCeti.Lie.IrrationalLine.hom_injective`: injectivity for irrational slope.
* `TauCeti.Lie.IrrationalLine.isImmersion_hom`: smooth immersion for every real slope.
* `TauCeti.Lie.IrrationalLine.subgroup`: the image as a subgroup of the multiplicative torus.
* `TauCeti.Lie.IrrationalLine.mem_subgroup_iff`: membership in the image in real coordinates.
* `TauCeti.Lie.IrrationalLine.immersedData`: the native connected immersed presentation.
* `TauCeti.Lie.IrrationalLine.isImmersedLieSubgroup`: the native immersed-subgroup predicate.
* `TauCeti.Lie.IrrationalLine.denseRange_hom`: density for irrational slope.
* `TauCeti.Lie.IrrationalLine.half_notMem_range`: a point outside the image.
* `TauCeti.Lie.IrrationalLine.not_isClosed_range_hom`: nonclosedness of the image.
* `TauCeti.Lie.IrrationalLine.not_locallyCompactSpace_subgroup`: the subtype is not locally compact.
* `TauCeti.Lie.IrrationalLine.not_locallyConnectedSpace_subgroup`: the subtype is not locally
  connected.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Example 4.20 (the irrational line in the torus).
-/

public section

open Set Function Filter Topology TopologicalSpace
open scoped Real ContDiff Manifold

noncomputable section

namespace TauCeti.Lie.IrrationalLine

local notation "C" => AddCircle (1 : ℝ)
local notation "P" => C × C

/-- The line of slope `θ` in the torus, parametrized by its first real coordinate. -/
def hom (θ : ℝ) : ℝ →+ P where
  toFun t := (((t : ℝ) : C), ((θ * t : ℝ) : C))
  map_zero' := by ext <;> simp
  map_add' s t := by ext <;> simp [mul_add]

/-- The line homomorphism has the original quotient coordinates. -/
@[simp]
theorem hom_apply (θ t : ℝ) : hom θ t = (((t : ℝ) : C), ((θ * t : ℝ) : C)) := by
  rw [hom]
  rfl

private theorem coe_eq_zero_iff_int (x : ℝ) :
    ((x : ℝ) : C) = 0 ↔ ∃ n : ℤ, (n : ℝ) = x := by
  simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ) (x := x))

/-- An irrational line is injectively parametrized by its first real coordinate. -/
theorem hom_injective {θ : ℝ} (hθ : Irrational θ) : Injective (hom θ) := by
  intro s t h
  have hz : hom θ (s - t) = 0 := by rw [map_sub, h, sub_self]
  have hc0 : ((s - t : ℝ) : C) = 0 := by
    simpa only [hom_apply, Prod.fst_zero] using congrArg Prod.fst hz
  have hc1 : ((θ * (s - t) : ℝ) : C) = 0 := by
    simpa only [hom_apply, Prod.snd_zero] using congrArg Prod.snd hz
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff_int _).mp hc0
  obtain ⟨m, hm⟩ := (coe_eq_zero_iff_int _).mp hc1
  have hr : ((-m : ℤ) : ℝ) + (n : ℝ) * θ = 0 := by
    push_cast
    rw [hn]
    linarith
  obtain ⟨_, hn0⟩ := hθ.intCast_add_mul_eq_zero_iff.mp hr
  apply sub_eq_zero.mp
  simpa only [hn0, Int.cast_zero] using hn.symm

/-- The line of every real slope is a smooth immersion into the torus. -/
theorem isImmersion_hom (θ : ℝ) :
    Manifold.IsImmersion 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) ∞ (hom θ) := by
  have hq : Manifold.IsImmersion 𝓘(ℝ) 𝓘(ℝ) ∞ ((↑) : ℝ → C) := by
    apply (AddCircle.contMDiff_coe 1 ∞).isImmersion_of_injective_mfderiv (by simp)
    intro t
    rw [AddCircle.mfderiv_coe]
    exact Function.injective_id
  have hs : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ fun t : ℝ ↦ ((θ * t : ℝ) : C) :=
    (AddCircle.contMDiff_coe 1 ∞).comp ((contDiff_const.mul contDiff_id).contMDiff)
  exact hq.prodMk hs (by simp)

/-- The image of the line, expressed in the multiplicative torus. -/
def subgroup (θ : ℝ) : Subgroup (Multiplicative P) := (hom θ).toMultiplicative.range

/-- Image membership is existence of a real parameter with the given quotient coordinates. -/
@[simp]
theorem mem_subgroup_iff (θ : ℝ) (x : Multiplicative P) :
    x ∈ subgroup θ ↔ ∃ t : ℝ, hom θ t = x.toAdd := by
  rw [subgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.toAdd, congrArg Multiplicative.toAdd ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨Multiplicative.ofAdd t, congrArg Multiplicative.ofAdd ht⟩

/-- The ordinary real line presents the irrational line as a connected immersed Lie subgroup. -/
-- The concrete source type, topology and atlas are part of this presentation's interface.
@[expose]
def immersedData {θ : ℝ} (hθ : Irrational θ) :
    ImmersedLieSubgroupData (𝓘(ℝ).prod 𝓘(ℝ)) (subgroup θ) where
  X := Multiplicative ℝ
  E' := ℝ
  H' := ℝ
  I' := 𝓘(ℝ)
  lieGroup := inferInstanceAs (LieGroup 𝓘(ℝ) ∞ (Multiplicative ℝ))
  connectedSpace := inferInstanceAs (ConnectedSpace ℝ)
  toHom := (hom θ).toMultiplicative
  injective := by
    intro s t h
    apply Multiplicative.toAdd.injective
    apply hom_injective hθ
    exact congrArg Multiplicative.toAdd h
  range_eq := by rw [subgroup]
  isImmersion := isImmersion_hom θ

/-- The irrational line satisfies the native immersed Lie-subgroup predicate. -/
theorem isImmersedLieSubgroup {θ : ℝ} (hθ : Irrational θ) :
    IsImmersedLieSubgroup (I := (𝓘(ℝ).prod 𝓘(ℝ))) (subgroup θ) :=
  (immersedData hθ).isImmersedLieSubgroup

private def velocity (θ : ℝ) : Fin 2 → ℝ := ![1, θ]

/-- The line of irrational slope is dense in the torus. -/
theorem denseRange_hom {θ : ℝ} (hθ : Irrational θ) : DenseRange (hom θ) := by
  have hd := (TauCeti.AddCircle.denseRange_coe_add_mul_iff
    (ι := Fin 2) (p := (1 : ℝ)) one_ne_zero (fun _ ↦ 0) (velocity θ)).mpr ?_
  · have heq : (hom θ : ℝ → P) = (Homeomorph.finTwoArrow (X := C)) ∘
        (fun t i ↦ ((0 + velocity θ i * t : ℝ) : C)) := by
      funext t
      simp [hom_apply, velocity]
    rw [DenseRange, heq, range_comp]
    exact (Homeomorph.finTwoArrow (X := C)).isDenseEmbedding.dense_image.mpr hd
  intro k hk
  have hrel : (k 0 : ℝ) + (k 1 : ℝ) * θ = 0 := by
    simpa [Fin.sum_univ_two, velocity] using hk
  obtain ⟨h0, h1⟩ := hθ.intCast_add_mul_eq_zero_iff.mp hrel
  ext i
  fin_cases i <;> assumption

/-- The point with coordinates zero and one half is outside every irrational line. -/
theorem half_notMem_range {θ : ℝ} (hθ : Irrational θ) :
    (0, ((1 / 2 : ℝ) : C)) ∉ range (hom θ) := by
  rintro ⟨t, ht⟩
  rw [hom_apply] at ht
  have hc0 : ((t : ℝ) : C) = 0 := congrArg Prod.fst ht
  have hc1 : ((θ * t - 1 / 2 : ℝ) : C) = 0 := by
    simpa only [AddCircle.coe_sub] using
      sub_eq_zero.mpr (congrArg Prod.snd ht)
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff_int _).mp hc0
  obtain ⟨m, hm⟩ := (coe_eq_zero_iff_int _).mp hc1
  have hn0 : n = 0 := by
    by_contra hnonzero
    apply (hθ.mul_intCast hnonzero).ne_rat ((m : ℚ) + 1 / 2)
    push_cast
    rw [hn]
    linarith
  have ht0 : t = 0 := by simpa only [hn0, Int.cast_zero] using hn.symm
  have hm2 : (2 : ℤ) * m = -1 := by
    exact_mod_cast (by rw [ht0] at hm; linarith : (2 : ℝ) * m = -1)
  omega

/-- The dense irrational line is not closed in the torus. -/
theorem not_isClosed_range_hom {θ : ℝ} (hθ : Irrational θ) : ¬ IsClosed (range (hom θ)) := by
  intro hc
  have h := denseRange_hom hθ (0, ((1 / 2 : ℝ) : C))
  rw [hc.closure_eq] at h
  exact half_notMem_range hθ h

/-- The image subtype of the irrational line is not locally compact. -/
theorem not_locallyCompactSpace_subgroup {θ : ℝ} (hθ : Irrational θ) :
    ¬ LocallyCompactSpace (subgroup θ) := by
  intro h
  let _ : LocallyCompactSpace (subgroup θ) := h
  have hc := (subgroup θ).isClosed_of_weaklyLocallyCompactSpace
  apply not_isClosed_range_hom hθ
  have hc' := hc.preimage (continuous_ofAdd (X := P))
  convert hc' using 1
  ext x
  exact (mem_subgroup_iff θ (Multiplicative.ofAdd x)).symm

private def paramEquiv {θ : ℝ} (hθ : Irrational θ) :
    Multiplicative ℝ ≃* subgroup θ :=
  MonoidHom.ofInjective (immersedData hθ).injective

private def parameter {θ : ℝ} (hθ : Irrational θ) (x : subgroup θ) : ℝ :=
  ((paramEquiv hθ).symm x).toAdd

private theorem hom_parameter {θ : ℝ} (hθ : Irrational θ) (x : subgroup θ) :
    hom θ (parameter hθ x) = x.val.toAdd :=
  congrArg (fun y : subgroup θ ↦ y.val.toAdd) ((paramEquiv hθ).apply_symm_apply x)

private abbrev circleChart := chartAt ℝ (0 : C)

private def lift (x : C) : ℝ := circleChart x - circleChart 0

private theorem lift_zero : lift 0 = 0 := sub_self _

private theorem coe_lift (x : C) (hx : x ∈ circleChart.source) : ((lift x : ℝ) : C) = x := by
  have hcoe (y : C) (hy : y ∈ circleChart.source) : ((circleChart y : ℝ) : C) = y :=
    AddCircle.coe_apply_of_mem_atlas (chart_mem_atlas ℝ (0 : C)) hy
  rw [lift, AddCircle.coe_sub, hcoe x hx, hcoe 0 (mem_chart_source ℝ (0 : C)), sub_zero]

private def domain (θ : ℝ) : Opens (subgroup θ) :=
  ⟨{x | x.val.toAdd.1 ∈ circleChart.source ∧ x.val.toAdd.2 ∈ circleChart.source}, by
    have hc : Continuous (fun x : subgroup θ ↦ x.val.toAdd) :=
      continuous_toAdd.comp continuous_subtype_val
    exact (circleChart.open_source.preimage hc.fst).inter
      (circleChart.open_source.preimage hc.snd)⟩

private def localZero (θ : ℝ) : domain θ :=
  ⟨1, mem_chart_source ℝ (0 : C), mem_chart_source ℝ (0 : C)⟩

private def firstLift (θ : ℝ) (x : domain θ) : ℝ := lift x.val.val.toAdd.1

private def secondLift (θ : ℝ) (x : domain θ) : ℝ := lift x.val.val.toAdd.2

private theorem continuousOn_lift : ContinuousOn lift circleChart.source :=
  circleChart.continuousOn.sub continuousOn_const

@[fun_prop]
private theorem continuous_domainCoord (θ : ℝ) :
    Continuous (fun x : domain θ ↦ x.val.val.toAdd) :=
  continuous_toAdd.comp (continuous_subtype_val.comp continuous_subtype_val)

@[fun_prop]
private theorem continuous_firstLift (θ : ℝ) : Continuous (firstLift θ) := by
  exact continuousOn_lift.comp_continuous (continuous_domainCoord θ).fst fun x ↦ x.property.1

@[fun_prop]
private theorem continuous_secondLift (θ : ℝ) : Continuous (secondLift θ) := by
  exact continuousOn_lift.comp_continuous (continuous_domainCoord θ).snd fun x ↦ x.property.2

-- The quotient equations determine both local lifts up to integer translations.
private theorem integer_offsets {θ : ℝ} (hθ : Irrational θ) (x : domain θ) :
    ∃ n m : ℤ, firstLift θ x = parameter hθ x.val + n ∧
      secondLift θ x = θ * parameter hθ x.val + m := by
  have h1 : ((parameter hθ x.val : ℝ) : C) = x.val.val.toAdd.1 := by
    simpa only [hom_apply] using congrArg Prod.fst (hom_parameter hθ x.val)
  have h2 : ((θ * parameter hθ x.val : ℝ) : C) = x.val.val.toAdd.2 := by
    simpa only [hom_apply] using congrArg Prod.snd (hom_parameter hθ x.val)
  have ha0 : ((firstLift θ x - parameter hθ x.val : ℝ) : C) = 0 := by
    rw [AddCircle.coe_sub, firstLift, coe_lift _ x.property.1, h1, sub_self]
  have hb0 : ((secondLift θ x - θ * parameter hθ x.val : ℝ) : C) = 0 := by
    rw [AddCircle.coe_sub, secondLift, coe_lift _ x.property.2, h2, sub_self]
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff_int _).mp ha0
  obtain ⟨m, hm⟩ := (coe_eq_zero_iff_int _).mp hb0
  exact ⟨n, m, by linarith, by linarith⟩

private def transverse (θ : ℝ) (x : domain θ) : ℝ := secondLift θ x - θ * firstLift θ x

@[fun_prop]
private theorem continuous_transverse (θ : ℝ) : Continuous (transverse θ) :=
  (continuous_secondLift θ).sub (continuous_const.mul (continuous_firstLift θ))

private theorem range_transverse_countable {θ : ℝ} (hθ : Irrational θ) :
    (range (transverse θ)).Countable := by
  apply (Set.countable_range (fun z : ℤ × ℤ ↦ (z.2 : ℝ) - θ * z.1)).mono
  rintro y ⟨x, rfl⟩
  obtain ⟨n, m, hn, hm⟩ := integer_offsets hθ x
  refine ⟨(n, m), ?_⟩
  dsimp only [transverse]
  rw [hn, hm]
  ring

private theorem transverse_zero (θ : ℝ) : transverse θ (localZero θ) = 0 := by
  simp [transverse, firstLift, secondLift, localZero, lift_zero]

-- Local connectedness makes the transverse offset locally constant, hence zero near identity.
private theorem continuousAt_parameter {θ : ℝ} (hθ : Irrational θ)
    [LocallyConnectedSpace (subgroup θ)] : ContinuousAt (parameter hθ) 1 := by
  let _ : LocallyConnectedSpace (domain θ) := (domain θ).isOpen.locallyConnectedSpace
  have hloc : IsLocallyConstant (transverse θ) :=
    (continuous_transverse θ).isLocallyConstant_of_countable_range (range_transverse_countable hθ)
  have htnear : (fun x : domain θ ↦ parameter hθ x.val) =ᶠ[𝓝 (localZero θ)] firstLift θ := by
    filter_upwards [hloc.eventually_eq (localZero θ)] with x hx
    have hx0 : transverse θ x = 0 := hx.trans (transverse_zero θ)
    obtain ⟨n, m, hn, hm⟩ := integer_offsets hθ x
    have hrel : (m : ℝ) + ((-n : ℤ) : ℝ) * θ = 0 := by
      dsimp only [transverse] at hx0
      rw [hn, hm] at hx0
      push_cast
      nlinarith
    obtain ⟨_, hn0⟩ := hθ.intCast_add_mul_eq_zero_iff.mp hrel
    have hnzero : n = 0 := neg_eq_zero.mp hn0
    simpa only [hnzero, Int.cast_zero, add_zero] using hn.symm
  have ht : ContinuousAt (fun x : domain θ ↦ parameter hθ x.val) (localZero θ) :=
    (continuous_firstLift θ).continuousAt.congr htnear.symm
  exact ((domain θ).isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff
    (g := parameter hθ) (x := localZero θ)).mp ht

@[fun_prop]
private theorem continuous_paramEquiv_symm {θ : ℝ} (hθ : Irrational θ)
    [LocallyConnectedSpace (subgroup θ)] :
    Continuous ((paramEquiv hθ).symm : subgroup θ → Multiplicative ℝ) := by
  apply continuous_of_continuousAt_one (paramEquiv hθ).symm
  simpa only [Function.comp_def, parameter, ofAdd_toAdd] using
    (continuous_ofAdd.continuousAt.comp (continuousAt_parameter hθ))

/-- The image subtype of the irrational line is not locally connected. -/
theorem not_locallyConnectedSpace_subgroup {θ : ℝ} (hθ : Irrational θ) :
    ¬ LocallyConnectedSpace (subgroup θ) := by
  intro hLC
  let _ : LocallyConnectedSpace (subgroup θ) := hLC
  have hforward : Continuous (paramEquiv hθ : Multiplicative ℝ → subgroup θ) :=
    (isImmersion_hom θ).contMDiff.continuous.subtype_mk _
  let e : Multiplicative ℝ ≃ₜ subgroup θ :=
    { (paramEquiv hθ).toEquiv with
      continuous_toFun := hforward
      continuous_invFun := continuous_paramEquiv_symm hθ }
  exact not_locallyCompactSpace_subgroup hθ (e.locallyCompactSpace_iff.mp inferInstance)

end TauCeti.Lie.IrrationalLine
