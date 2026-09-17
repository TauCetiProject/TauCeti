/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Weights
import Mathlib.LinearAlgebra.Determinant

/-!
# Joint weights of the commutator subgroup

For a reduced connected affine group of finite type over an algebraically closed field, every
nonzero joint weight of the commutator subgroup in a finite-dimensional rational representation
is trivial.

The ambient group preserves the joint weight space. On that space a commutator acts by a scalar
whose power, with exponent the dimension of the weight space, is its determinant and hence one.
Fixing one argument of the commutator makes that scalar a regular function on the connected
group. Its image is finite, so it is constant and equal to one. This is the determinant step in
the Lie--Kolchin induction; no characteristic-zero hypothesis is needed.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. E. Humphreys, *Linear Algebraic Groups*, §17.6.
-/

public section

namespace TauCeti.Comodule

open WithConv
open scoped commutatorElement

noncomputable section

variable {k H V : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [AddCommGroup V] [Module k V] [Comodule k H V] [FiniteDimensional k V]

private theorem commutator_weight_pow_finrank_eq_one
    (χ : NonzeroJointWeight (commutator (WithConv (H →ₐ[k] k)))
      (basePointsRepresentation (R := k) (H := H) V))
    (g h : WithConv (H →ₐ[k] k)) :
    (χ.1 ⟨⁅g, h⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
      (Subgroup.mem_top h)⟩ : k) ^
        Module.finrank k (normalWeightSubcomodule _ χ).toSubmodule = 1 := by
  let ρ : _root_.Representation k (WithConv (H →ₐ[k] k)) V :=
    basePointsRepresentation (R := k) (H := H) V
  let W := normalWeightSubcomodule _ χ
  let σ := ρ.subrepresentation W.toSubmodule
    (fun x _ hv ↦ basePointsRepresentation_mem W x hv)
  have hscalar (n : commutator (WithConv (H →ₐ[k] k))) :
      σ n = (χ.1 n : k) • (1 : Module.End k W.toSubmodule) := by
    ext v
    exact (mem_normalWeightSubcomodule _ χ v).mp v.2 n
  let δ := (Units.map (LinearMap.det : Module.End k W.toSubmodule →* k)).comp σ.asGroupHom
  have hdet : LinearMap.det (σ ⁅g, h⁆) = 1 := by
    have heq : δ ⁅g, h⁆ = 1 := by
      rw [map_commutatorElement]
      exact Commute.commutator_eq (Commute.all _ _)
    exact congrArg Units.val heq
  rw [hscalar ⟨⁅g, h⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
    (Subgroup.mem_top h)⟩, LinearMap.det_smul, map_one, mul_one] at hdet
  exact hdet

private theorem commutator_weight_apply_commutator_eq_one
    (χ : NonzeroJointWeight (commutator (WithConv (H →ₐ[k] k)))
      (basePointsRepresentation (R := k) (H := H) V))
    (g h : WithConv (H →ₐ[k] k)) :
    χ.1 ⟨⁅g, h⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
      (Subgroup.mem_top h)⟩ = 1 := by
  classical
  let W := normalWeightSubcomodule _ χ
  have hW : W.toSubmodule ≠ ⊥ := by
    rw [ne_eq, Subcomodule.toSubmodule_eq_bot]
    exact normalWeightSubcomodule_ne_bot _ χ
  let _ : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hW
  obtain ⟨v, hv, hv0⟩ := W.toSubmodule.ne_bot_iff.mp hW
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hv0
  -- A generic first argument realizes the scalar of the commutator as a regular function.
  let u : WithConv (H →ₐ[k] H) := toConv (AlgHom.id k H)
  let q := ⁅u, AlgHom.mapValue (H := H) (Algebra.ofId k H) h⁆
  let a := q.ofConv (matrixCoefficient (R := k) (C := H) φ v)
  have heval (x : WithConv (H →ₐ[k] k)) :
      x.ofConv a = (χ.1 ⟨⁅x, h⁆, Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top h)⟩ : k) := by
    have hq : AlgHom.mapValue (H := H) x.ofConv q = ⁅x, h⁆ := by
      simp only [q, map_commutatorElement]
      rw [AlgHom.mapValue_algebraOfId]
      simp [u, AlgHom.mapValue_apply]
    have he := congrArg (fun y : WithConv (H →ₐ[k] k) ↦
      y.ofConv (matrixCoefficient (R := k) (C := H) φ v)) hq
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply] at he
    rw [he, apply_matrixCoefficient]
    have hvn := (mem_normalWeightSubcomodule _ χ v).mp hv
      ⟨⁅x, h⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top h)⟩
    exact (congrArg φ hvn).trans (by simp [hφ])
  -- The determinant bounds the image by the finite set of roots of unity of this degree.
  have hfinite : (Set.range fun f : H →ₐ[k] k ↦ f a).Finite := by
    apply (Polynomial.nthRootsFinset (Module.finrank k W.toSubmodule) (1 : k)).finite_toSet.subset
    rintro _ ⟨f, rfl⟩
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (Module.finrank_pos (R := k))]
    exact (congrArg (fun z : k ↦ z ^ Module.finrank k W.toSubmodule)
      (heval (toConv f))).trans (commutator_weight_pow_finrank_eq_one χ (toConv f) h)
  have ha := eq_algebraMap_of_finite_range_eval a hfinite (1 : WithConv (H →ₐ[k] k)).ofConv
  have hc : g.ofConv a = (1 : WithConv (H →ₐ[k] k)).ofConv a := by
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      congrArg g.ofConv ha
  rw [heval, heval] at hc
  apply Units.ext
  have hunit : (⟨⁅(1 : WithConv (H →ₐ[k] k)), h⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top 1) (Subgroup.mem_top h)⟩ :
      commutator (WithConv (H →ₐ[k] k))) = 1 := by
    apply Subtype.ext
    exact commutatorElement_one_left h
  simpa only [hunit, map_one, Units.val_one] using hc

/-- Every character of the commutator subgroup having a nonzero joint weight space in a
finite-dimensional rational representation of a reduced connected affine group is trivial. -/
@[simp]
theorem nonzeroJointWeight_commutator_eq_one
    (χ : NonzeroJointWeight (commutator (WithConv (H →ₐ[k] k)))
      (basePointsRepresentation (R := k) (H := H) V)) : χ.1 = 1 := by
  let N := commutator (WithConv (H →ₐ[k] k))
  have hle : N ≤ χ.1.ker.map N.subtype := by
    apply Subgroup.commutator_le.mpr
    intro g _ h _
    exact ⟨⟨⁅g, h⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
      (Subgroup.mem_top h)⟩, commutator_weight_apply_commutator_eq_one χ g h, rfl⟩
  apply MonoidHom.ext
  intro n
  obtain ⟨m, hm, hmn⟩ := hle n.2
  have hmn' : m = n := Subtype.ext hmn
  exact MonoidHom.mem_ker.mp (hmn' ▸ hm)

end

end TauCeti.Comodule
