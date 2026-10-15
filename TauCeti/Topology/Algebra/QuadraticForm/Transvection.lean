/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic
public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
public import TauCeti.Topology.Algebra.QuadraticForm.Continuity
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Continuity and unboundedness of Eichler transvections

For continuous families of an isotropic vector `u` and an orthogonal parameter `w`, the Eichler
transvection `E_{u,w}` varies continuously in the canonical topology on linear automorphisms. The
forward endomorphisms are continuous directly from the explicit transvection formula. Their
inverses vary continuously because `E_{u,w}⁻¹ = E_{u,-w}`.

For fixed `u`, this continuity descends through the quotient topology on `u⊥ / K ∙ u`. Thus the
additive homomorphism `QuadraticMap.transvectionHom Q hu` is a continuous homomorphism into the
special orthogonal group.

Over a nontrivially normed field, such as `ℝ` or `ℚ_p`, a nonzero parameter class `w` gives a
one-parameter family `t ↦ E_{u,t w}` that leaves every compact set of linear automorphisms, since a
suitable matrix coefficient of `E_{u,t w}` is an affine function of `t` with nonzero slope.
Consequently, the Eichler root subgroup of `u` is compact exactly when its parameter space
`u^⊥ / K ∙ u` is trivial. For a nonzero isotropic vector of a nondegenerate form
that parameter space has dimension `dim V - 2`, so the root subgroups are noncompact exactly in
dimension at least three. In dimension two they are trivial, and noncompactness of an isotropic
orthogonal group is witnessed by the split torus instead
(`TauCeti.QuadraticMap.not_isCompact_orthogonalGroup`).

## Main results

* `QuadraticMap.continuous_transvection` proves continuity for families in both parameters.
* `QuadraticMap.continuous_transvectionHom` proves continuity of the quotient homomorphism.
* `QuadraticMap.tendsto_transvection_smul_cobounded_cocompact`: the family `t ↦ E_{u,t w}`
  leaves every compact set of linear automorphisms when `w ∉ K ∙ u`.
* `QuadraticMap.tendsto_transvectionHom_smul_cobounded_cocompact`: the same for the root-subgroup
  homomorphism along a nonzero parameter class.
* `QuadraticMap.isCompact_range_transvectionHom_iff`: the root subgroup is compact exactly when its
  parameter space is trivial.
* `QuadraticMap.isCompact_range_transvectionHom_iff_finrank_le_two`: for a nonzero isotropic
  vector of a nondegenerate form, the root subgroup is compact exactly when `dim V ≤ 2`.

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

section Unbounded

open Filter Bornology TauCeti.QuadraticMap

section NontriviallyNormedField

variable {K : Type u} [NontriviallyNormedField K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {u w : V}

/-- **Eichler transvections are unbounded.** For an isotropic vector `u` outside the polar radical
and a vector `w` orthogonal to `u` but not a multiple of it, the Eichler transvections `E_{u,t w}`
eventually leave every compact set of linear automorphisms as `t` tends to infinity in `K`.
The field is nontrivially normed so that `cobounded K` is a nontrivial filter: over a trivially
normed field it is `⊥` and the statement would hold vacuously. -/
theorem tendsto_transvection_smul_cobounded_cocompact (hu : Q u = 0) (huw : polar Q u w = 0)
    (hpolar : Q.polarBilin u ≠ 0) (hw : w ∉ K ∙ u) :
    Tendsto (fun t : K ↦ transvection Q hu (w := t • w)
        (by rw [polar_smul_right, huw, smul_zero]))
      (cobounded K) (cocompact (V ≃ₗ[K] V)) := by
  obtain ⟨x, hx⟩ : ∃ x, polar Q x u ≠ 0 := by
    by_contra! H
    exact hpolar (LinearMap.ext fun x ↦ by simpa [polar_comm Q u x] using H x)
  obtain ⟨f, hfw, hfu⟩ := Submodule.exists_le_ker_of_notMem hw
  have hfu' : f u = 0 := hfu (Submodule.mem_span_singleton_self u)
  -- The coordinate `f (g x)` is continuous in `g` and grows linearly along the family.
  let φ : Module.End K V →ₗ[K] K := f.comp (LinearMap.applyₗ x)
  have hφ : Continuous fun g : V ≃ₗ[K] V ↦ φ g :=
    (IsModuleTopology.continuous_of_linearMap φ).comp continuous_linearEquiv_toLinearMap
  have hφE (t : K) : φ (transvection Q hu (w := t • w)
      (by rw [polar_smul_right, huw, smul_zero]) : V ≃ₗ[K] V) =
        f x + t * (polar Q x u * f w) := by
    simp [φ, transvection_apply, hfu']
    ring
  refine (tendsto_comap_iff.mpr ?_).mono_right (comap_cocompact_le hφ)
  refine (((tendsto_const_add_cobounded (f x)).comp
    (tendsto_mul_right_cobounded (mul_ne_zero hx hfw))).mono_right
    Metric.cobounded_le_cocompact).congr fun t ↦ ?_
  simp [hφE]

/-- **Eichler root subgroups are unbounded.** Along a nonzero class `q` in the parameter space
`u^⊥ / K ∙ u` of an isotropic vector outside the polar radical, the Eichler transvections
`t ↦ E_{u, t q}` eventually leave every compact subset of the special orthogonal group. -/
theorem tendsto_transvectionHom_smul_cobounded_cocompact (hu : Q u = 0)
    (hpolar : Q.polarBilin u ≠ 0)
    {q : LinearMap.ker (Q.polarBilin u) ⧸
      (K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype} (hq : q ≠ 0) :
    Tendsto (fun t : K ↦ transvectionHom Q hu (t • q)) (cobounded K)
      (cocompact (Additive (specialOrthogonalGroup Q))) := by
  induction q using Submodule.Quotient.induction_on with | H w => ?_
  obtain ⟨w, hw⟩ := w
  have huw : polar Q u w = 0 := by simpa using hw
  have hwu : w ∉ K ∙ u := by
    rwa [ne_eq, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at hq
  let ι : Additive (specialOrthogonalGroup Q) → V ≃ₗ[K] V := fun g ↦
    ((Additive.toMul g : specialOrthogonalGroup Q) : V ≃ₗ[K] V)
  have hι : Continuous ι := continuous_subtype_val.comp continuous_toMul
  refine (tendsto_comap_iff.mpr ?_).mono_right (comap_cocompact_le hι)
  refine (tendsto_transvection_smul_cobounded_cocompact hu huw hpolar hwu).congr fun t ↦ ?_
  rw [Function.comp_apply, ← Submodule.Quotient.mk_smul]
  exact (coe_transvectionHom_mk hu _).symm

/-- **Compactness of an Eichler root subgroup.** For an isotropic vector `u` outside the polar
radical, the image of the root-subgroup homomorphism `u^⊥ / K ∙ u → SO(Q)` is compact exactly when
the parameter space `u^⊥ / K ∙ u` is trivial. -/
theorem isCompact_range_transvectionHom_iff (hu : Q u = 0) (hpolar : Q.polarBilin u ≠ 0) :
    IsCompact (Set.range (transvectionHom Q hu)) ↔
      Subsingleton (LinearMap.ker (Q.polarBilin u) ⧸
        (K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype) := by
  refine ⟨fun hcpt ↦ ?_, fun _ ↦ (Set.subsingleton_range _).isCompact⟩
  by_contra hsub
  have := not_subsingleton_iff_nontrivial.mp hsub
  obtain ⟨q, hq⟩ := exists_ne (0 : LinearMap.ker (Q.polarBilin u) ⧸
    (K ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype)
  obtain ⟨t, ht⟩ :=
    ((tendsto_transvectionHom_smul_cobounded_cocompact hu hpolar hq).eventually_mem
      hcpt.compl_mem_cocompact).exists
  exact ht ⟨t • q, rfl⟩

/-- **Eichler root subgroups are noncompact from dimension three on.** For a nonzero isotropic
vector `u` of a nondegenerate quadratic form on a finite-dimensional space, the Eichler root
subgroup of `u` in `SO(Q)` is compact exactly when `dim V ≤ 2`, where it is trivial. -/
theorem isCompact_range_transvectionHom_iff_finrank_le_two [FiniteDimensional K V]
    (hQ : Q.Nondegenerate) (hu : Q u = 0) (hu₀ : u ≠ 0) :
    IsCompact (Set.range (transvectionHom Q hu)) ↔ Module.finrank K V ≤ 2 := by
  have hpolar : Q.polarBilin u ≠ 0 := fun h ↦ by
    have hmem : u ∈ Q.radical := ⟨hu, h⟩
    rw [hQ.radical_eq_bot, Submodule.mem_bot] at hmem
    exact hu₀ hmem
  rw [isCompact_range_transvectionHom_iff hu hpolar, ← Module.finrank_zero_iff (R := K),
    finrank_transvectionParameter hu hpolar]
  omega

end NontriviallyNormedField

end Unbounded

end QuadraticMap
