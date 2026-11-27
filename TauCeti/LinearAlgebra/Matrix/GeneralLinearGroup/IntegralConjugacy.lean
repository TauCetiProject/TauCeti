/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
import TauCeti.RepresentationTheory.Lattice

/-!
# Integral conjugates of finite matrix groups

`Subgroup.exists_map_conj_le_range_of_isFractionRing` conjugates a finite matrix group over the
fraction field of a principal ideal domain into the image of the integral general linear group.
It uses `TauCeti.exists_isFullLattice_subrepresentation` to find an invariant full lattice,
`TauCeti.mem_stabilizer_set_iff_mapsTo` to identify its stabilizing automorphisms, and
`Module.Basis.mem_stabilizer_iff_exists_map_eq_toMatrix` to read their action in a lattice basis.

For the rational case, see J.-P. Serre, *Bounds for the orders of the finite subgroups of G(k)*,
arXiv:1011.0346, §1.3.1.
-/

public section

open scoped MatrixGroups Pointwise
open Module

/-- Over the fraction field `K` of a principal ideal domain `R`, every finite subgroup of
`GL ι K` has a conjugate contained in the image of `GL ι R`. In particular, every finite
subgroup of `GL ι ℚ` is conjugate to a group of invertible integer matrices. -/
theorem Subgroup.exists_map_conj_le_range_of_isFractionRing
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (H : Subgroup (GL ι K)) [Finite H]
    (R : Type*) [CommRing R] [IsPrincipalIdealRing R] [Algebra R K] [IsFractionRing R K] :
    ∃ g : GL ι K, H.map (MulAut.conj g).toMonoidHom ≤
      (Matrix.GeneralLinearGroup.map (algebraMap R K)).range := by
  classical
  let : IsDomain R := IsDomain.of_faithfulSMul R K
  let b₀ := Pi.basisFun K ι
  let ρ : Representation K H (ι → K) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (b₀.toGL.symm.toMonoidHom.comp H.subtype)
  obtain ⟨L, hL⟩ := TauCeti.exists_isFullLattice_subrepresentation (O := R) K ρ
  let : L.toSubmodule.IsFullLattice K := hL
  let : Module.Finite R L.toSubmodule := Submodule.IsLattice.finite K _
  -- Index the lattice basis by the same type as the standard basis.
  let b := Module.Free.chooseBasis R L.toSubmodule
  let c := b.reindex ((b.extendOfIsFullLattice K).indexEquiv b₀)
  let d := c.extendOfIsFullLattice K
  let e := b₀.equiv d (Equiv.refl ι)
  refine ⟨(b₀.toGL e)⁻¹, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  let f := b₀.toGL.symm h
  -- The lattice is preserved by both the automorphism and its inverse.
  have hf : f ∈ MulAction.stabilizer ((ι → K) ≃ₗ[K] (ι → K))
      (L.toSubmodule : Set (ι → K)) := by
    have hact (k : H) {x : ι → K} (hx : x ∈ L.toSubmodule) :
        b₀.toGL.symm (k : GL ι K) x ∈ L.toSubmodule := by
      simpa only [Representation.restrictScalars_apply, ρ, MonoidHom.comp_apply,
        LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, LinearEquiv.coe_coe,
        MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply] using L.apply_mem_toSubmodule k hx
    refine TauCeti.mem_stabilizer_set_iff_mapsTo.mpr ⟨?_, ?_⟩
    · intro x hx
      simpa only [LinearEquiv.smul_def, SetLike.mem_coe, f] using hact ⟨h, hh⟩ hx
    · intro x hx
      simpa only [LinearEquiv.smul_def, SetLike.mem_coe, Subgroup.coe_inv, map_inv, f]
        using hact (⟨h, hh⟩ : H)⁻¹ hx
  obtain ⟨u, hu⟩ := (c.mem_stabilizer_iff_exists_map_eq_toMatrix f).mp hf
  refine ⟨u, Units.ext ?_⟩
  have hmatrix : LinearMap.toMatrix d d f =
      LinearMap.toMatrix b₀ b₀ (e⁻¹ * f * e : (ι → K) ≃ₗ[K] (ι → K)) := by
    have hd : b₀.map e = d := by simp only [e, Basis.map_equiv, Equiv.refl_symm, Basis.reindex_refl]
    have heinv : e⁻¹ = e.symm := LinearEquiv.ext (congrFun (LinearEquiv.coe_inv e))
    simp only [heinv, ← hd, LinearMap.toMatrix_map_left, LinearMap.toMatrix_map_right,
      LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]
  have hconj : b₀.toGL (e⁻¹ * f * e) = MulAut.conj (b₀.toGL e)⁻¹ h := by
    rw [MulAut.conj_apply]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, inv_inv, f]
  rw [MulEquiv.coe_toMonoidHom, ← hconj, Basis.coe_toGL, ← hmatrix]
  exact hu
