/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Transvection
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Projection
public import TauCeti.Topology.Algebra.QuadraticForm.Transvection

/-!
# Continuity and noncompactness of Spin transvection lifts

The canonical Clifford lift `spinTransvection hQ hu huw` of an Eichler transvection has carrier
`1 + ι Q w * ι Q u`. Consequently it varies continuously with the isotropic vector `u` and its
orthogonal parameter `w`. For fixed `u`, this continuity descends through the quotient topology on
`u^⊥ / K ∙ u`, making `spinTransvectionHom hQ hu` a continuous root-subgroup homomorphism.

Over a nontrivially normed field, the Spin root subgroup of `u` maps continuously onto the Eichler
root subgroup of `SO(Q)`, so it is compact exactly when the parameter space `u^⊥ / K ∙ u` is
trivial. For a nonzero isotropic vector this happens exactly when `dim V ≤ 2`.

## Main results

* `CliffordAlgebra.continuous_spinTransvection` proves continuity for families in both parameters.
* `CliffordAlgebra.continuous_spinTransvectionHom` proves continuity of the quotient homomorphism.
* `CliffordAlgebra.isCompact_range_spinTransvectionHom_iff`: the Spin root subgroup is compact
  exactly when its parameter space is trivial.
* `CliffordAlgebra.isCompact_range_spinTransvectionHom_iff_finrank_le_two`: for a nonzero isotropic
  vector, the Spin root subgroup is compact exactly when `dim V ≤ 2`.

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

section Noncompact

variable {K : Type u} [NontriviallyNormedField K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {u : V}

/-- **Compactness of a Spin root subgroup.** For a nondegenerate form and an isotropic vector `u`
outside the polar radical, the image of the Spin root-subgroup homomorphism
`u^⊥ / K ∙ u → Spin(Q)` is compact exactly when the parameter space `u^⊥ / K ∙ u` is trivial. -/
theorem isCompact_range_spinTransvectionHom_iff (hQ : Q.Nondegenerate) (hu : Q u = 0)
    (hpolar : Q.polarBilin u ≠ 0) :
    IsCompact (Set.range (spinTransvectionHom hQ hu)) ↔
      Subsingleton (LinearMap.ker (Q.polarBilin u) ⧸
        (K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype) := by
  refine ⟨fun hcpt ↦ (isCompact_range_transvectionHom_iff hu hpolar).mp ?_,
    fun _ ↦ (Set.subsingleton_range _).isCompact⟩
  have hcont : Continuous (spinToSpecialOrthogonal Q).toAdditive :=
    continuous_ofMul.comp ((TauCeti.CliffordAlgebra.continuous_spinToSpecialOrthogonal Q).comp
      continuous_toMul)
  rw [← spinToSpecialOrthogonal_comp_spinTransvectionHom hQ hu, AddMonoidHom.coe_comp,
    Set.range_comp]
  exact hcpt.image hcont

/-- **Spin root subgroups are noncompact from dimension three on.** For a nonzero isotropic vector
`u` of a nondegenerate quadratic form on a finite-dimensional space, the Spin root subgroup of `u`
is compact exactly when `dim V ≤ 2`, where it is trivial. -/
theorem isCompact_range_spinTransvectionHom_iff_finrank_le_two (hQ : Q.Nondegenerate)
    (hu : Q u = 0) (hu₀ : u ≠ 0) :
    IsCompact (Set.range (spinTransvectionHom hQ hu)) ↔ Module.finrank K V ≤ 2 := by
  have hpolar := hQ.polarBilin_ne_zero hu₀
  rw [isCompact_range_spinTransvectionHom_iff hQ hu hpolar, ← Module.finrank_zero_iff (R := K),
    finrank_transvectionParameter hu hpolar]
  omega

end Noncompact

end CliffordAlgebra
