/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
public import TauCeti.Topology.Algebra.QuadraticForm.Continuity

/-!
# Continuity of Eichler transvections

For continuous families of an isotropic vector `u` and an orthogonal parameter `w`, the Eichler
transvection `E_{u,w}` varies continuously in the canonical topology on linear automorphisms. The
forward endomorphisms are continuous directly from the explicit transvection formula. Their
inverses vary continuously because `E_{u,w}⁻¹ = E_{u,-w}`.

For fixed `u`, this continuity descends through the quotient topology on `u⊥ / K ∙ u`. Thus the
additive homomorphism `QuadraticMap.transvectionHom Q hu` is a continuous homomorphism into the
special orthogonal group.

## Main results

* `QuadraticMap.continuous_transvection` proves continuity for families in both parameters.
* `QuadraticMap.continuous_transvectionHom` proves continuity of the quotient homomorphism.

## References

* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
* `CliffordAlgebra.continuous_lipschitzVectorAction_toLinearMap`, for the finite-basis
  endomorphism-continuity argument factored through `Module.Basis.continuous_iff_apply`.
* `CliffordAlgebra.continuous_spinTransvectionHom`, for the quotient-descent argument.
-/

public section

open QuadraticMap

namespace QuadraticMap

open TauCeti

universe u v w

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [TopologicalSpace V] [IsModuleTopology K V]
  {Q : QuadraticForm K V}

private theorem continuous_transvection_toLinearMap {X : Type w} [TopologicalSpace X]
    (u w : X → V) (hu : ∀ x, Q (u x) = 0)
    (huw : ∀ x, polar Q (u x) (w x) = 0)
    (huc : Continuous u) (hwc : Continuous w) :
    Continuous (fun x ↦ (transvection Q (hu x) (huw x) : Module.End K V)) := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  let b := Module.finBasis K V
  rw [b.continuous_iff_apply]
  intro j
  have hpolar : Continuous (Q.polarBilin (b j)) :=
    IsModuleTopology.continuous_of_linearMap (Q.polarBilin (b j))
  have hpu : Continuous (fun x ↦ polar Q (b j) (u x)) := hpolar.comp huc
  have hpw : Continuous (fun x ↦ polar Q (b j) (w x)) := hpolar.comp hwc
  have hQw : Continuous (fun x ↦ Q (w x)) := Q.continuous.comp hwc
  have hformula : Continuous (fun x ↦
      b j + polar Q (b j) (u x) • w x - polar Q (b j) (w x) • u x -
        (Q (w x) * polar Q (b j) (u x)) • u x) := by
    exact (continuous_const.add (hpu.smul hwc)).sub (hpw.smul huc) |>.sub
      ((hQw.mul hpu).smul huc)
  exact hformula.congr fun x ↦ (transvection_apply (hu x) (huw x) (b j)).symm

/-- Continuously varying isotropic vectors and orthogonal parameters determine continuously
varying Eichler transvections. -/
@[fun_prop]
theorem continuous_transvection {X : Type w} [TopologicalSpace X] (u w : X → V)
    (hu : ∀ x, Q (u x) = 0) (huw : ∀ x, polar Q (u x) (w x) = 0)
    (huc : Continuous u) (hwc : Continuous w) :
    Continuous (fun x ↦ transvection Q (hu x) (huw x)) := by
  let _ : IsTopologicalAddGroup V := IsModuleTopology.isTopologicalAddGroup K V
  rw [TauCeti.continuous_linearEquiv_iff]
  constructor
  · exact continuous_transvection_toLinearMap u w hu huw huc hwc
  · have hneg : Continuous (fun x ↦ -w x) := hwc.neg
    have hu_neg : ∀ x, polar Q (u x) (-w x) = 0 := by
      intro x
      simp [huw x]
    have h := continuous_transvection_toLinearMap u (fun x ↦ -w x) hu hu_neg huc hneg
    convert h using 1
    funext x
    exact congrArg LinearEquiv.toLinearMap (transvection_neg (hu x) (huw x)).symm

/-- The canonical homomorphism from `u⊥ / K ∙ u` to the special orthogonal group is continuous. -/
@[fun_prop]
theorem continuous_transvectionHom {u : V} (hu : Q u = 0) :
    Continuous (transvectionHom Q hu) := by
  let S : Submodule K (LinearMap.ker (Q.polarBilin u)) :=
    (K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype
  rw [S.isQuotientMap_mkQ.continuous_iff]
  have hw : ∀ w : LinearMap.ker (Q.polarBilin u), polar Q u (w : V) = 0 := fun w ↦ by
    simpa only [QuadraticMap.polarBilin_apply_apply] using LinearMap.mem_ker.mp w.2
  apply Continuous.subtype_mk
  exact (continuous_transvection (fun _ ↦ u)
    (fun w : LinearMap.ker (Q.polarBilin u) ↦ (w : V)) (fun _ ↦ hu) hw
    continuous_const continuous_subtype_val).congr fun w ↦
      (coe_transvectionHom_mk hu (hw w)).symm

end QuadraticMap
