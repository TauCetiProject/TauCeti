/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic

/-!
# Continuity of Spin transvection lifts

The canonical Clifford lift `spinTransvection hQ hu huw` of an Eichler transvection has carrier
`1 + ι Q w * ι Q u`. Consequently it varies continuously with the isotropic vector `u` and its
orthogonal parameter `w`. For fixed `u`, this continuity descends through the quotient topology on
`u^⊥ / K ∙ u`, making `spinTransvectionHom hQ hu` a continuous root-subgroup homomorphism.

## Main results

* `CliffordAlgebra.continuous_spinTransvection` proves continuity for families in both parameters.
* `CliffordAlgebra.continuous_spinTransvectionHom` proves continuity of the quotient homomorphism.

## References

* M. Eichler, *Quadratische Formen und orthogonale Gruppen*, Springer (1952).
-/

public section

open QuadraticMap

namespace CliffordAlgebra

universe u v w

variable {K : Type u} [Field K] [TopologicalSpace K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]
  {Q : QuadraticForm K V} [ContinuousMul (CliffordAlgebra Q)]

/-- Continuously varying isotropic vectors and orthogonal parameters determine continuously varying
Spin lifts of Eichler transvections. -/
@[fun_prop]
theorem continuous_spinTransvection {X : Type w} [TopologicalSpace X] (u w : X → V)
    (hQ : Q.Nondegenerate) (hu : ∀ x, Q (u x) = 0)
    (huw : ∀ x, polar Q (u x) (w x) = 0)
    (huc : Continuous u) (hwc : Continuous w) :
    Continuous (fun x ↦ spinTransvection hQ (hu x) (huw x)) := by
  apply continuous_induced_rng.mpr
  have hval : Continuous (fun x ↦ 1 + ι Q (w x) * ι Q (u x)) :=
    continuous_const.add (((continuous_ι Q).comp hwc).mul ((continuous_ι Q).comp huc))
  convert hval using 1
  funext x
  exact coe_spinTransvection hQ (hu x) (huw x)

/-- The canonical homomorphism from `u^⊥ / K ∙ u` to the Spin group is continuous. -/
@[fun_prop]
theorem continuous_spinTransvectionHom {u : V} (hQ : Q.Nondegenerate) (hu : Q u = 0) :
    Continuous (spinTransvectionHom hQ hu) := by
  let S : Submodule K (LinearMap.ker (Q.polarBilin u)) :=
    (K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype
  rw [S.isQuotientMap_mkQ.continuous_iff]
  have hw : ∀ w : LinearMap.ker (Q.polarBilin u), polar Q u (w : V) = 0 := fun w ↦ by
    simpa only [QuadraticMap.polarBilin_apply_apply] using LinearMap.mem_ker.mp w.2
  have hraw : Continuous (fun w : LinearMap.ker (Q.polarBilin u) ↦
      Additive.ofMul (spinTransvection hQ hu (hw w))) :=
    continuous_spinTransvection (fun _ ↦ u)
      (fun w : LinearMap.ker (Q.polarBilin u) ↦ (w : V)) hQ (fun _ ↦ hu)
      hw continuous_const continuous_subtype_val
  convert hraw using 1
  funext w
  apply Additive.toMul.injective
  rw [Function.comp_apply, Submodule.mkQ_apply,
    toMul_spinTransvectionHom_mk hQ hu (hw w), toMul_ofMul]

end CliffordAlgebra
