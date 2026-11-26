/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Killing
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.Units
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Normed.Algebra.Derivation.Exponential
import TauCeti.Geometry.Lie.Subgroup.CartanChart

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

/-- A copy of a finite-dimensional real Lie algebra on which to place a norm.
The model uses the norm of the coordinates in a chosen finite basis. -/
def NormedModel (L : Type*) := L

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

instance : LieRing (NormedModel L) := inferInstanceAs (LieRing L)

instance : LieAlgebra ℝ (NormedModel L) := inferInstanceAs (LieAlgebra ℝ L)

namespace NormedModel

/-- The normed model has the original Lie algebra structure. -/
def lieEquiv : NormedModel L ≃ₗ⁅ℝ⁆ L := LieEquiv.refl

variable [FiniteDimensional ℝ L]

instance : FiniteDimensional ℝ (NormedModel L) := inferInstanceAs (FiniteDimensional ℝ L)

/-- Coordinates for the normed model in the chosen finite basis. -/
def coordinates : NormedModel L ≃ₗ[ℝ] (Fin (Module.finrank ℝ L) → ℝ) :=
  lieEquiv.toLinearEquiv.trans (Module.finBasis ℝ L).equivFun

instance : NormedAddCommGroup (NormedModel L) :=
  NormedAddCommGroup.induced _ _ (coordinates (L := L)) coordinates.injective

instance : NormedSpace ℝ (NormedModel L) :=
  NormedSpace.induced ℝ _ _ (coordinates (L := L))

end NormedModel

variable [FiniteDimensional ℝ L]

local notation "V" => NormedModel L
local notation "End" => (V →L[ℝ] V)

attribute [local instance] TauCeti.normedAlgebraRatOfReal
attribute [local instance 100] LieRing.ofAssociativeRing

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

/-- The unit associated to a Lie equivalence acts by that equivalence. -/
@[simp]
theorem automorphismSubgroupEquiv_symm_apply (e : V ≃ₗ⁅ℝ⁆ V) (x : V) :
    ((automorphismSubgroupEquiv.symm e).val : End) x = e x :=
  (rfl)

variable (L) in
/-- The subgroup of bracket-preserving units is closed in the group of linear units. -/
theorem isClosed_automorphismSubgroup :
    IsClosed (automorphismSubgroup L : Set Endˣ) := by
  let b := (LieAlgebra.ad ℝ V).toLinearMap.toContinuousBilinearMap
  have hset : (automorphismSubgroup L : Set Endˣ) =
      ⋂ (x : V) (y : V), {g : Endˣ | (g : End) (b x y) =
        b ((g : End) x) ((g : End) y)} := by
    ext g
    simp [b, LieAlgebra.ad_apply]
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
  simpa only [mem_automorphismSubgroup, expUnit_coe, LinearMap.toContinuousBilinearMap_apply,
    LieHom.coe_toLinearMap, LieAlgebra.ad_apply] using
    ((LieAlgebra.ad ℝ V).toLinearMap.toContinuousBilinearMap).forall_exp_smul_apply_bilinear_iff D

/-- The adjoint map with values in continuous linear endomorphisms. -/
def continuousAd : V →ₗ⁅ℝ⁆ End where
  toLinearMap := LinearMap.toContinuousLinearMap.toLinearMap.comp (LieAlgebra.ad ℝ V).toLinearMap
  map_lie' := by
    intro x y
    ext z
    exact DFunLike.congr_fun ((LieAlgebra.ad ℝ V).map_lie x y) z

/-- The continuous adjoint acts by the Lie bracket. -/
@[simp]
theorem continuousAd_apply (x y : V) : continuousAd x y = ⁅x, y⁆ :=
  (rfl)

variable (L) in
/-- The analytic inner automorphism subgroup is generated by the exponentials of the adjoint
operators. -/
def innerAutomorphismSubgroup : Subgroup Endˣ :=
  Subgroup.closure (Set.range fun x : V ↦ expUnit (continuousAd x))

/-- Exponentiating any adjoint operator gives an inner automorphism. -/
theorem expUnit_continuousAd_mem_innerAutomorphismSubgroup (x : V) :
    expUnit (continuousAd x) ∈ innerAutomorphismSubgroup L :=
  Subgroup.subset_closure ⟨x, rfl⟩

/-- A subgroup contains the analytic inner automorphism subgroup exactly when it contains
every adjoint exponential. -/
theorem innerAutomorphismSubgroup_le_iff {H : Subgroup Endˣ} :
    innerAutomorphismSubgroup L ≤ H ↔ ∀ x : V, expUnit (continuousAd x) ∈ H :=
  (Subgroup.closure_le H).trans Set.range_subset_iff

/-- The adjoint operators are infinitesimal automorphisms. -/
theorem continuousAd_mem_linearLieSubalgebra_automorphismSubgroup (x : V) :
    continuousAd x ∈ (automorphismSubgroup L).linearLieSubalgebra := by
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
  let f : V → Endˣ := fun x ↦ expUnit (continuousAd x)
  have hconn : IsPreconnected (Set.range f) :=
    isPreconnected_range (continuous_expUnit.comp
      (continuousAd (L := L)).toLinearMap.continuous_of_finiteDimensional)
  have h₁ : 1 ∈ Set.range f := ⟨0, by simp [f]⟩
  have hsub : Set.range f ⊆ (G : Set Endˣ) :=
    Set.range_subset_iff.mpr expUnit_continuousAd_mem_innerAutomorphismSubgroup
  have hle : G ≤ G.ambientConnectedComponentOfOne := by
    apply innerAutomorphismSubgroup_le_iff.mpr
    intro x
    rw [← SetLike.mem_coe, Subgroup.coe_ambientConnectedComponentOfOne]
    exact hconn.subset_connectedComponentIn h₁ hsub ⟨x, rfl⟩
  have hG : IsPreconnected (G : Set Endˣ) := by
    rw [le_antisymm hle G.ambientConnectedComponentOfOne_le]
    exact G.isPreconnected_ambientConnectedComponentOfOne
  exact ⟨⟨1, G.one_mem⟩, hG⟩

variable [LieAlgebra.IsKilling ℝ L]

local instance : LieAlgebra.IsKilling ℝ V :=
  LieAlgebra.isKilling_of_equiv NormedModel.lieEquiv.symm

/-- Every infinitesimal automorphism of a real Lie algebra with nondegenerate Killing form
is inner. -/
theorem linearLieSubalgebra_automorphismSubgroup_eq_range_ad :
    (automorphismSubgroup L).linearLieSubalgebra = (continuousAd (L := L)).range := by
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
  have hLie : A.linearLieSubalgebra = (continuousAd (L := L)).range :=
    (Subgroup.linearLieSubalgebra_ambientConnectedComponentOfOne
      (isClosed_automorphismSubgroup L)).trans
      linearLieSubalgebra_automorphismSubgroup_eq_range_ad
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, rfl⟩
    have hx : continuousAd x ∈ A.linearLieSubalgebra := hLie.symm ▸ ⟨x, rfl⟩
    simpa only [A, SetLike.mem_coe, one_smul] using
      Subgroup.mem_linearLieAlgebra_iff.mp ((Subgroup.mem_linearLieSubalgebra_iff hA).mp hx) 1
  · -- Near the identity, each element of the closed subgroup is a single Lie exponential.
    let _ : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp
      (Subgroup.isPreconnected_ambientConnectedComponentOfOne (automorphismSubgroup L))
    obtain ⟨U, hU, hUexp⟩ :=
      exists_mem_nhds_one_iff_exists_mem_lieSubalgebraOfSubgroup_and_lieExp_eq_of_isClosed
        (I := 𝓘(ℝ, End)) hA
    have hopen : IsOpen ((innerAutomorphismSubgroup L).subgroupOf A : Set A) := by
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
      rw [nhds_subtype_eq_comap]
      refine ⟨U, hU, fun g hg ↦ ?_⟩
      obtain ⟨X, hX, hXg⟩ := (hUexp g hg).mp g.property
      have hDX : unitsLieAlgebraLieEquiv X ∈ A.linearLieSubalgebra :=
        Subgroup.mem_linearLieSubalgebra.mpr (by simpa only [LieEquiv.symm_apply_apply] using hX)
      have hRange : unitsLieAlgebraLieEquiv X ∈ (continuousAd (L := L)).range := hLie ▸ hDX
      rw [LieHom.mem_range] at hRange
      obtain ⟨x, hx⟩ := hRange
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← hXg, lieExp_eq_expUnit,
        ← unitsLieAlgebraLieEquiv_apply, ← hx]
      exact expUnit_continuousAd_mem_innerAutomorphismSubgroup x
    have hall := IsClopen.eq_univ
      ⟨((innerAutomorphismSubgroup L).subgroupOf A).isClosed_of_isOpen hopen, hopen⟩
      ⟨1, ((innerAutomorphismSubgroup L).subgroupOf A).one_mem⟩
    exact fun g hg ↦ Subgroup.mem_subgroupOf.mp (Set.eq_univ_iff_forall.mp hall (⟨g, hg⟩ : A))

/-- The analytic inner automorphism subgroup of a Lie algebra with nondegenerate Killing form
is closed in the group of linear units. -/
theorem isClosed_innerAutomorphismSubgroup :
    IsClosed (innerAutomorphismSubgroup L : Set Endˣ) := by
  rw [innerAutomorphismSubgroup_eq_ambientConnectedComponentOfOne]
  exact Subgroup.isClosed_ambientConnectedComponentOfOne (isClosed_automorphismSubgroup L)

variable (L) in
/-- The analytic inner automorphism subgroup is an embedded Lie subgroup with model space the
infinitesimal Lie algebra inside the ambient group of linear units. -/
def innerAutomorphismSubgroupData :
    EmbeddedLieSubgroupData 𝓘(ℝ, End) (innerAutomorphismSubgroup L)
      (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) (innerAutomorphismSubgroup L)).toSubmodule :=
  EmbeddedLieSubgroupData.ofIsClosed isClosed_innerAutomorphismSubgroup

/-- The Lie algebra of the inner automorphism group of a real Lie algebra with nondegenerate
Killing form is the range of the adjoint map. -/
theorem linearLieSubalgebra_innerAutomorphismSubgroup_eq_range_ad :
    (innerAutomorphismSubgroup L).linearLieSubalgebra = (continuousAd (L := L)).range := by
  rw [innerAutomorphismSubgroup_eq_ambientConnectedComponentOfOne,
    Subgroup.linearLieSubalgebra_ambientConnectedComponentOfOne (isClosed_automorphismSubgroup L),
    linearLieSubalgebra_automorphismSubgroup_eq_range_ad]

/-- A closed connected subgroup with Lie algebra equal to the adjoint image is precisely
the analytic inner automorphism group. -/
theorem eq_innerAutomorphismSubgroup_of_linearLieSubalgebra
    {G : Subgroup Endˣ} (hG : IsClosed (G : Set Endˣ))
    (hconn : IsPreconnected (G : Set Endˣ))
    (hLie : G.linearLieSubalgebra = (continuousAd (L := L)).range) :
    G = innerAutomorphismSubgroup L := by
  have heq := hLie.trans linearLieSubalgebra_innerAutomorphismSubgroup_eq_range_ad.symm
  exact le_antisymm
    (Subgroup.le_of_linearLieSubalgebra_le hG hconn isClosed_innerAutomorphismSubgroup heq.le)
    (Subgroup.le_of_linearLieSubalgebra_le isClosed_innerAutomorphismSubgroup
      isConnected_innerAutomorphismSubgroup.isPreconnected hG heq.ge)

local notation "IntModel" =>
  LieSubalgebra.toSubmodule (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) (innerAutomorphismSubgroup L))

/-- The adjoint map identifies the original Lie algebra with the Lie algebra of its analytic
inner automorphism group. -/
def adjointLieEquivInnerAutomorphismSubgroup :
    let d := innerAutomorphismSubgroupData L
    let _ : ChartedSpace IntModel (innerAutomorphismSubgroup L) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, IntModel) ∞ (innerAutomorphismSubgroup L) := d.lieGroup
    L ≃ₗ⁅ℝ⁆ LeftInvariantDerivation 𝓘(ℝ, IntModel) (innerAutomorphismSubgroup L) := by
  let d := innerAutomorphismSubgroupData L
  let _ : ChartedSpace IntModel (innerAutomorphismSubgroup L) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, IntModel) ∞ (innerAutomorphismSubgroup L) := d.lieGroup
  dsimp only
  have had : Function.Injective (continuousAd (L := L)) := by
    intro x y h
    apply LieDerivation.injective_ad_of_center_eq_bot (R := ℝ) (L := V) (by simp)
    ext z
    simpa using DFunLike.congr_fun h z
  let S := lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) (innerAutomorphismSubgroup L)
  let e := S.equivMapOfInjective (unitsLieAlgebraLieEquiv (R := End)).toLieHom
    unitsLieAlgebraLieEquiv.injective
  have hrange : S.map (unitsLieAlgebraLieEquiv (R := End)).toLieHom =
      (continuousAd (L := L)).range :=
    (Subgroup.linearLieSubalgebra_eq_map (innerAutomorphismSubgroup L)).symm.trans
      linearLieSubalgebra_innerAutomorphismSubgroup_eq_range_ad
  let e' := LieEquiv.ofEq _ _ (congrArg SetLike.coe hrange.symm)
  exact NormedModel.lieEquiv.symm.trans
    (((continuousAd (L := L)).equivRangeOfInjective had).trans
      (e'.trans (e.symm.trans d.lieEquivLieSubalgebraOfSubgroup.symm)))

/-- Under the differential of inclusion, the Lie-algebra identification acts by the
continuous adjoint operator. -/
theorem adjointLieEquivInnerAutomorphismSubgroup_apply (x : L) :
    let d := innerAutomorphismSubgroupData L
    let _ : ChartedSpace IntModel (innerAutomorphismSubgroup L) := d.chartedSpace
    let _ : LieGroup 𝓘(ℝ, IntModel) ∞ (innerAutomorphismSubgroup L) := d.lieGroup
    unitsLieAlgebraLieEquiv
      (d.lieMapSubtypeVal (adjointLieEquivInnerAutomorphismSubgroup (L := L) x)) =
      continuousAd (NormedModel.lieEquiv.symm x) := by
  let d := innerAutomorphismSubgroupData L
  let _ : ChartedSpace IntModel (innerAutomorphismSubgroup L) := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, IntModel) ∞ (innerAutomorphismSubgroup L) := d.lieGroup
  dsimp only
  rw [← d.lieEquivLieSubalgebraOfSubgroup_apply]
  simp only [adjointLieEquivInnerAutomorphismSubgroup, d, id_eq, LieEquiv.trans_apply,
    LieEquiv.apply_symm_apply]
  let S := lieSubalgebraOfSubgroup (I := 𝓘(ℝ, End)) (innerAutomorphismSubgroup L)
  let e := S.equivMapOfInjective (unitsLieAlgebraLieEquiv (R := End)).toLieHom
    unitsLieAlgebraLieEquiv.injective
  have he (y : S) : (e y : End) = unitsLieAlgebraLieEquiv y := rfl
  rw [← he, LieEquiv.apply_symm_apply, LieEquiv.ofEq_apply]
  rfl

end TauCeti.Lie
