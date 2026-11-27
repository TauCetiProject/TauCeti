/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Killing
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.Topology.Algebra.Lie.NormedModel
import TauCeti.Analysis.Normed.Algebra.Derivation.Exponential
import TauCeti.Geometry.Lie.Subgroup.Image
import TauCeti.Topology.Algebra.Lie.Bracket

/-!
# The automorphism Lie group of a real Lie algebra

The bracket-preserving units in the algebra of continuous linear endomorphisms form the
closed subgroup `TauCeti.Lie.automorphismSubgroup`. Its Lie algebra consists of the Lie
derivations: an exponential line preserves the bracket precisely when its generator
satisfies the Lie Leibniz rule.

For a finite-dimensional real Lie algebra with nondegenerate Killing form, the identity
component is the analytic inner automorphism group. It is the unique closed connected
subgroup whose Lie algebra is the range of the adjoint map. This realizes the Lie algebra
as the infinitesimal algebra of its adjoint group.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, 2nd ed., Ch. VI, §§1–2.
-/

public section

noncomputable section

open NormedSpace
open scoped Manifold ContDiff

namespace TauCeti.Lie

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

variable [FiniteDimensional ℝ L]

local notation "V" => NormedModel L
local notation "End" => (V →L[ℝ] V)

attribute [local instance] TauCeti.normedAlgebraRatOfReal
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] ContMDiffMul.boundarylessManifold

variable (L) in
/-- The subgroup of invertible continuous linear maps preserving the Lie bracket. -/
def automorphismSubgroup : Subgroup Endˣ where
  carrier := {g | ∀ x y : V, (g : End) ⁅x, y⁆ = ⁅(g : End) x, (g : End) y⁆}
  one_mem' := by simp
  mul_mem' {g h} hg hh x y := by
    simp only [Units.val_mul, mul_apply_eq_comp]
    rw [hh, hg]
  inv_mem' {g} hg x y := by
    have hInv (z : V) : (g : End) ((↑g⁻¹ : End) z) = z := by
      rw [← mul_apply_eq_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq_self]
    apply (ContinuousLinearEquiv.unitsEquiv ℝ V g).injective
    simpa only [ContinuousLinearEquiv.unitsEquiv_apply, hInv] using
      (hg ((↑g⁻¹ : End) x) ((↑g⁻¹ : End) y)).symm

/-- Membership in the automorphism subgroup is bracket preservation. -/
@[simp]
theorem mem_automorphismSubgroup {g : Endˣ} :
    g ∈ automorphismSubgroup L ↔
      ∀ x y : V, (g : End) ⁅x, y⁆ = ⁅(g : End) x, (g : End) y⁆ :=
  (Iff.rfl)

/-- The bracket-preserving units and the Lie automorphisms are equivalent. -/
def automorphismSubgroupEquiv : automorphismSubgroup L ≃ (V ≃ₗ⁅ℝ⁆ V) where
  toFun g :=
    { (ContinuousLinearEquiv.unitsEquiv ℝ V g.val).toLinearEquiv with
      map_lie' := fun {x y} ↦ (mem_automorphismSubgroup.mp g.property) x y }
  invFun e :=
    ⟨e.toLinearEquiv.toContinuousLinearEquiv.toUnit, mem_automorphismSubgroup.mpr e.map_lie⟩
  left_inv _ := Subtype.ext (Units.ext (ContinuousLinearMap.ext fun _ ↦ rfl))
  right_inv _ := LieEquiv.ext fun _ ↦ rfl

/-- The Lie equivalence acts by the underlying operator. -/
@[simp]
theorem automorphismSubgroupEquiv_apply (g : automorphismSubgroup L) (x : V) :
    automorphismSubgroupEquiv g x = (g.val : End) x :=
  (rfl)

/-- Multiplication of bracket-preserving units acts by composition, with the right factor first. -/
@[simp]
theorem automorphismSubgroupEquiv_mul (g h : automorphismSubgroup L) :
    automorphismSubgroupEquiv (g * h) =
      (automorphismSubgroupEquiv h).trans (automorphismSubgroupEquiv g) :=
  LieEquiv.ext fun _ ↦ rfl

/-- The unit associated to a Lie equivalence acts by that equivalence. -/
@[simp]
theorem automorphismSubgroupEquiv_symm_apply (e : V ≃ₗ⁅ℝ⁆ V) (x : V) :
    ((automorphismSubgroupEquiv.symm e).val : End) x = e x :=
  (rfl)

variable (L) in
/-- The subgroup of bracket-preserving units is closed in the group of linear units. -/
theorem isClosed_automorphismSubgroup :
    IsClosed (automorphismSubgroup L : Set Endˣ) := by
  let b := TauCeti.lieL ℝ V V
  have hset : (automorphismSubgroup L : Set Endˣ) =
      ⋂ (x : V) (y : V), {g : Endˣ | (g : End) (b x y) =
        b ((g : End) x) ((g : End) y)} := by
    ext g
    simp [b]
  rw [hset]
  have hEval (z : V) : Continuous (fun g : Endˣ ↦ (g : End) z) :=
    (ContinuousLinearMap.apply ℝ V z).continuous.comp Units.continuous_val
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
    isClosed_eq (hEval (b x y)) ((b.continuous.comp (hEval x)).clm_apply (hEval y))

variable (L) in
/-- The automorphism subgroup is an embedded Lie subgroup of the group of linear units. -/
theorem isEmbeddedLieSubgroup_automorphismSubgroup :
    IsEmbeddedLieSubgroup (I := 𝓘(ℝ, End)) (automorphismSubgroup L) :=
  isEmbeddedLieSubgroup_of_isClosed (isClosed_automorphismSubgroup L)

local instance : CompleteSpace V := FiniteDimensional.completeSpace ℝ V

/-- In operator coordinates, the Lie algebra of the automorphism group is given by the
Leibniz rule for the bracket. -/
theorem mem_linearLieSubalgebra_automorphismSubgroup {D : End} :
    D ∈ (automorphismSubgroup L).linearLieSubalgebra ↔
      ∀ x y : V, D ⁅x, y⁆ = ⁅x, D y⁆ + ⁅D x, y⁆ := by
  rw [Subgroup.mem_linearLieSubalgebra_iff (isClosed_automorphismSubgroup L),
    Subgroup.mem_linearLieAlgebra_iff]
  simpa only [mem_automorphismSubgroup, expUnit_coe, TauCeti.lieL_apply, add_comm] using
    (TauCeti.lieL ℝ V V).forall_exp_smul_apply_bilinear_iff D D D

local notation "adV" => (continuousAd (L := L))
local notation "AmbientLieAlgebra" => LeftInvariantDerivation 𝓘(ℝ, End) Endˣ

variable (L) in
/-- The analytic inner automorphism subgroup is generated by the exponentials of the adjoint
operators. -/
def innerAutomorphismSubgroup : Subgroup Endˣ :=
  Subgroup.closure (Set.range fun x : V ↦ expUnit (adV x))

/-- Exponentiating any adjoint operator gives an inner automorphism. -/
theorem expUnit_continuousAd_mem_innerAutomorphismSubgroup (x : V) :
    expUnit (adV x) ∈ innerAutomorphismSubgroup L :=
  Subgroup.subset_closure ⟨x, rfl⟩

/-- A subgroup contains the analytic inner automorphism subgroup exactly when it contains
every adjoint exponential. -/
theorem innerAutomorphismSubgroup_le_iff {H : Subgroup Endˣ} :
    innerAutomorphismSubgroup L ≤ H ↔ ∀ x : V, expUnit (adV x) ∈ H :=
  (Subgroup.closure_le H).trans Set.range_subset_iff

/-- The adjoint operators are infinitesimal automorphisms. -/
theorem continuousAd_mem_linearLieSubalgebra_automorphismSubgroup (x : V) :
    adV x ∈ (automorphismSubgroup L).linearLieSubalgebra := by
  apply mem_linearLieSubalgebra_automorphismSubgroup.mpr
  intro y z
  simpa only [continuousAd_apply, add_comm] using leibniz_lie x y z

/-- The analytic inner automorphism group acts by Lie automorphisms. -/
theorem innerAutomorphismSubgroup_le : innerAutomorphismSubgroup L ≤ automorphismSubgroup L := by
  apply innerAutomorphismSubgroup_le_iff.mpr
  intro x
  have hx := continuousAd_mem_linearLieSubalgebra_automorphismSubgroup x
  rw [Subgroup.mem_linearLieSubalgebra_iff (isClosed_automorphismSubgroup L),
    Subgroup.mem_linearLieAlgebra_iff] at hx
  simpa only [SetLike.mem_coe, one_smul] using hx 1

/-- The analytic inner automorphism subgroup of a finite-dimensional real Lie algebra is
connected. -/
theorem isConnected_innerAutomorphismSubgroup :
    IsConnected (innerAutomorphismSubgroup L : Set Endˣ) := by
  let G := innerAutomorphismSubgroup L
  let f : V → Endˣ := fun x ↦ expUnit (adV x)
  have hf : Continuous f :=
    continuous_expUnit.comp (adV).toLinearMap.continuous_of_finiteDimensional
  have hone : 1 ∈ Set.range f := ⟨0, by simp [f]⟩
  have hsub : Set.range f ⊆ (G : Set Endˣ) :=
    Set.range_subset_iff.mpr expUnit_continuousAd_mem_innerAutomorphismSubgroup
  have hle : G ≤ G.ambientConnectedComponentOfOne :=
    (Subgroup.closure_le _).mpr (G.range_subset_ambientConnectedComponentOfOne hf hone hsub)
  -- Read the goal as connectedness of the subgroup used in the containment argument.
  change IsConnected (G : Set Endˣ)
  rw [le_antisymm hle G.ambientConnectedComponentOfOne_le]
  exact ⟨⟨1, G.ambientConnectedComponentOfOne.one_mem⟩,
    G.isPreconnected_ambientConnectedComponentOfOne⟩

private def adjointRange : LieSubalgebra ℝ AmbientLieAlgebra :=
  (adV).range.comap unitsLieAlgebraLieEquiv.toLieHom

private theorem lieExp_image_adjointRange :
    lieExp '' (adjointRange (L := L) : Set AmbientLieAlgebra) =
      Set.range (fun x : V ↦ expUnit (adV x)) := by
  ext g
  constructor
  · rintro ⟨X, ⟨x, hx⟩, rfl⟩
    refine ⟨x, ?_⟩
    rw [lieExp_eq_expUnit, ← unitsLieAlgebraLieEquiv_apply]
    exact congrArg expUnit (show adV x = unitsLieAlgebraLieEquiv X from hx)
  · rintro ⟨x, rfl⟩
    refine ⟨unitsLieAlgebraLieEquiv.symm (adV x), ?_, ?_⟩
    · exact ⟨x, (LieEquiv.apply_symm_apply unitsLieAlgebraLieEquiv _).symm⟩
    · rw [lieExp_eq_expUnit, ← unitsLieAlgebraLieEquiv_apply, LieEquiv.apply_symm_apply]

variable [LieAlgebra.IsKilling ℝ L]

local instance : LieAlgebra.IsKilling ℝ V :=
  LieAlgebra.isKilling_of_equiv NormedModel.lieEquiv.symm

/-- Every infinitesimal automorphism of a real Lie algebra with nondegenerate Killing form
is inner. -/
theorem linearLieSubalgebra_automorphismSubgroup_eq_range_continuousAd :
    (automorphismSubgroup L).linearLieSubalgebra = (adV).range := by
  ext D
  constructor
  · intro h
    have hl := mem_linearLieSubalgebra_automorphismSubgroup.mp h
    let δ : LieDerivation ℝ V V :=
      { D.toLinearMap with
        leibniz' := fun x y ↦ by simpa [sub_eq_add_neg, lie_skew y (D x)] using hl x y }
    obtain ⟨x, hx⟩ := LieDerivation.IsKilling.exists_eq_ad δ
    refine ⟨x, ContinuousLinearMap.ext fun y ↦ ?_⟩
    have hmap := congrArg LieDerivation.toLinearMap hx
    simpa [continuousAd_apply, δ, LieAlgebra.ad_apply] using LinearMap.congr_fun hmap y
  · rintro ⟨x, rfl⟩
    exact continuousAd_mem_linearLieSubalgebra_automorphismSubgroup x

/-- For a finite-dimensional real Lie algebra with nondegenerate Killing form, the group
generated by the adjoint exponentials is the identity component of the automorphism group. -/
theorem innerAutomorphismSubgroup_eq_ambientConnectedComponentOfOne :
    innerAutomorphismSubgroup L = (automorphismSubgroup L).ambientConnectedComponentOfOne := by
  let A := (automorphismSubgroup L).ambientConnectedComponentOfOne
  have hA : IsClosed (A : Set Endˣ) :=
    Subgroup.isClosed_ambientConnectedComponentOfOne (isClosed_automorphismSubgroup L)
  let d := EmbeddedLieSubgroupData.ofIsClosed (I := 𝓘(ℝ, End)) hA
  let _ := d.chartedSpace
  let _ := d.lieGroup
  let _ : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp
    (Subgroup.isPreconnected_ambientConnectedComponentOfOne (automorphismSubgroup L))
  have hLie : A.linearLieSubalgebra = (adV).range :=
    (Subgroup.linearLieSubalgebra_ambientConnectedComponentOfOne _).trans
      linearLieSubalgebra_automorphismSubgroup_eq_range_continuousAd
  have hRange : d.lieMapSubtypeVal.range = adjointRange (L := L) := by
    rw [d.range_lieMapSubtypeVal_eq]
    ext X
    -- Read membership in the adjoint range in operator coordinates.
    change X ∈ lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) A ↔
      unitsLieAlgebraLieEquiv X ∈ (adV).range
    rw [← hLie, Subgroup.mem_linearLieSubalgebra, LieEquiv.symm_apply_apply]
  have hGen := d.subtypeVal.range_eq_closure_lieExp_image
  have hMap : lieMap d.subtypeVal = d.lieMapSubtypeVal :=
    LieHom.ext fun X ↦ (d.lieMapSubtypeVal_apply X).symm
  rw [d.toMonoidHom_subtypeVal, Subgroup.range_subtype, hMap, hRange, lieExp_image_adjointRange]
    at hGen
  exact hGen.symm

/-- The analytic inner automorphism subgroup of a Lie algebra with nondegenerate Killing form
is closed in the group of linear units. -/
theorem isClosed_innerAutomorphismSubgroup :
    IsClosed (innerAutomorphismSubgroup L : Set Endˣ) := by
  rw [innerAutomorphismSubgroup_eq_ambientConnectedComponentOfOne]
  exact Subgroup.isClosed_ambientConnectedComponentOfOne (isClosed_automorphismSubgroup L)

variable (L) in
/-- For a Lie algebra with nondegenerate Killing form, the analytic inner automorphism subgroup
is embedded, with model space its Lie algebra inside the ambient group of linear units. -/
def innerAutomorphismSubgroupData :
    EmbeddedLieSubgroupData 𝓘(ℝ, End) (innerAutomorphismSubgroup L)
      (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) (innerAutomorphismSubgroup L)).toSubmodule :=
  EmbeddedLieSubgroupData.ofIsClosed isClosed_innerAutomorphismSubgroup

/-- The Lie algebra of the inner automorphism group of a real Lie algebra with nondegenerate
Killing form is the range of the adjoint map. -/
theorem linearLieSubalgebra_innerAutomorphismSubgroup_eq_range_continuousAd :
    (innerAutomorphismSubgroup L).linearLieSubalgebra = (adV).range := by
  rw [innerAutomorphismSubgroup_eq_ambientConnectedComponentOfOne,
    Subgroup.linearLieSubalgebra_ambientConnectedComponentOfOne,
    linearLieSubalgebra_automorphismSubgroup_eq_range_continuousAd]

/-- For a Lie algebra with nondegenerate Killing form, a closed connected subgroup with Lie
algebra equal to the adjoint image is the analytic inner automorphism group. -/
theorem eq_innerAutomorphismSubgroup_of_linearLieSubalgebra
    {G : Subgroup Endˣ} (hG : IsClosed (G : Set Endˣ))
    (hconn : IsPreconnected (G : Set Endˣ))
    (hLie : G.linearLieSubalgebra = (adV).range) :
    G = innerAutomorphismSubgroup L := by
  have heq := hLie.trans linearLieSubalgebra_innerAutomorphismSubgroup_eq_range_continuousAd.symm
  exact le_antisymm
    (Subgroup.le_of_linearLieSubalgebra_le hG hconn isClosed_innerAutomorphismSubgroup heq.le)
    (Subgroup.le_of_linearLieSubalgebra_le isClosed_innerAutomorphismSubgroup
      isConnected_innerAutomorphismSubgroup.isPreconnected hG heq.ge)

local notation "IntModel" =>
  LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) (innerAutomorphismSubgroup L))

/-- The analytic inner automorphism group has the charts of its embedded subgroup structure
when the Killing form is nondegenerate. -/
instance innerAutomorphismSubgroupChartedSpace :
    ChartedSpace IntModel (innerAutomorphismSubgroup L) :=
  (innerAutomorphismSubgroupData L).chartedSpace

/-- With nondegenerate Killing form, the analytic inner automorphism group is a smooth Lie group
with the subspace topology. -/
instance innerAutomorphismSubgroupLieGroup :
    LieGroup 𝓘(ℝ, IntModel) ∞ (innerAutomorphismSubgroup L) :=
  (innerAutomorphismSubgroupData L).lieGroup

private def adjointRangeEquiv :
    lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) (innerAutomorphismSubgroup L) ≃ₗ⁅ℝ⁆ (adV).range :=
  unitsLieAlgebraLieEquiv.ofSubalgebras _ _ <|
    (Subgroup.linearLieSubalgebra_eq_map (innerAutomorphismSubgroup L)).symm.trans
      linearLieSubalgebra_innerAutomorphismSubgroup_eq_range_continuousAd

private theorem coe_adjointRangeEquiv
    (X : lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) (innerAutomorphismSubgroup L)) :
    (adjointRangeEquiv X : End) = unitsLieAlgebraLieEquiv X :=
  LieEquiv.ofSubalgebras_apply _ _ _ _ _

/-- For a Lie algebra with nondegenerate Killing form, the adjoint map identifies the original
Lie algebra with the Lie algebra of its analytic inner automorphism group. -/
def adjointLieEquivInnerAutomorphismSubgroup :
    L ≃ₗ⁅ℝ⁆ LeftInvariantDerivation 𝓘(ℝ, IntModel) (innerAutomorphismSubgroup L) := by
  have had : Function.Injective adV := by
    intro x y h
    apply LieDerivation.injective_ad_of_center_eq_bot (R := ℝ) (L := V) (by simp)
    ext z
    simpa using DFunLike.congr_fun h z
  exact NormedModel.lieEquiv.symm.trans <|
    ((adV).equivRangeOfInjective had).trans <|
      adjointRangeEquiv.symm.trans
        (innerAutomorphismSubgroupData L).lieEquivLieSubalgebraOfSubgroup.symm

/-- For a Lie algebra with nondegenerate Killing form, the adjoint identification followed by
the inclusion differential is the continuous adjoint operator in ambient operator coordinates. -/
theorem unitsLieAlgebraLieEquiv_lieMapSubtypeVal_adjointLieEquivInnerAutomorphismSubgroup
    (x : L) :
    unitsLieAlgebraLieEquiv
      ((innerAutomorphismSubgroupData L).lieMapSubtypeVal
        (adjointLieEquivInnerAutomorphismSubgroup (L := L) x)) =
      adV (NormedModel.lieEquiv.symm x) := by
  rw [← EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup_apply, ← coe_adjointRangeEquiv]
  simp only [adjointLieEquivInnerAutomorphismSubgroup, LieEquiv.trans_apply,
    LieEquiv.apply_symm_apply]
  exact congrArg Subtype.val ((adV).equivRangeOfInjective_apply _ _)

/-- For a Lie algebra with nondegenerate Killing form, its intrinsic inner automorphism
exponential acts by the exponential of the corresponding adjoint operator. -/
@[simp]
theorem coe_lieExp_adjointLieEquivInnerAutomorphismSubgroup (x : L) :
    (lieExp (I := 𝓘(ℝ, IntModel)) (G := innerAutomorphismSubgroup L)
      (adjointLieEquivInnerAutomorphismSubgroup (L := L) x) : Endˣ) =
      expUnit (adV (NormedModel.lieEquiv.symm x)) := by
  let d := innerAutomorphismSubgroupData L
  rw [← d.subtypeVal_apply, map_lieExp, ← d.lieMapSubtypeVal_apply, lieExp_eq_expUnit,
    ← unitsLieAlgebraLieEquiv_apply,
    unitsLieAlgebraLieEquiv_lieMapSubtypeVal_adjointLieEquivInnerAutomorphismSubgroup]

end TauCeti.Lie
