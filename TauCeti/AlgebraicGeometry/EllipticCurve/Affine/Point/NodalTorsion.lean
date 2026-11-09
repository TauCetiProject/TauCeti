/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Singular
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
public import TauCeti.NumberTheory.LocalField.Unramified.Reduction
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Torsion on a nodal cubic over finite extensions

A nodal Weierstrass cubic has a nonsingular point of every order invertible in the field
once the field is algebraically closed: its nonsingular point group is the multiplicative
group, and primitive roots of unity supply the points. Over a finite field each such point
is already defined over a finite extension.

For a nodal cubic over the residue field of a nonarchimedean local field, we realize this
finite extension as the residue field of a finite unramified extension. This provides the
residue torsion points to which prime-to-residue-characteristic torsion lifting applies
at multiplicative reduction. No ellipticity assumption is appropriate for the residue cubic.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.5 and VII.5.
* [J.-P. Serre, *Corps Locaux*][serre1968], III, §5.
-/

public section

open Polynomial

namespace WeierstrassCurve

open Affine.Point

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- Over an algebraically closed field, a nodal cubic has a nonsingular point of every order
invertible in the field. -/
theorem exists_point_addOrderOf_eq_of_nodal [DecidableEq F] [IsAlgClosed F]
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    ∃ P : W.toAffine.Point, addOrderOf P = n := by
  obtain ⟨x₀, y₀, h⟩ := Affine.exists_isSingular_of_Δ_eq_zero W.toAffine hΔ
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
    (C 1 * X ^ 2 + C W.a₁ * X + C (-(3 * x₀ + W.a₂)))
    (by rw [degree_quadratic one_ne_zero]; decide)
  have hα' : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0 := by
    simpa [sub_eq_add_neg] using hα
  have hnode : 2 * α + W.a₁ ≠ 0 := by
    intro hz
    have heq := Affine.c₄_eq_of_isSingular h hα'
    exact hc₄ (by simpa [hz] using heq)
  have : NeZero (n : F) := ⟨hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F n
  have hn₀ : n ≠ 0 := fun hz ↦ hn (by simp [hz])
  let u : Fˣ := (hζ.isUnit hn₀).unit
  have hu : orderOf u = n := by
    rw [← orderOf_units, IsUnit.unit_spec]
    exact hζ.eq_orderOf.symm
  let e := nodeAddEquiv h hα' hnode
  refine ⟨e.symm (Additive.ofMul u), ?_⟩
  rw [← e.addOrderOf_eq, e.apply_symm_apply]
  exact hu

/-- A nodal cubic acquires a point of any prescribed invertible order over a finite normal
subextension of its algebraic closure. -/
theorem exists_finiteDimensional_normal_point_addOrderOf_eq_of_nodal
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    ∃ M : IntermediateField F (AlgebraicClosure F), FiniteDimensional F M ∧ Normal F M ∧
      ∀ [DecidableEq M], ∃ P : (W⁄M).toAffine.Point, addOrderOf P = n := by
  classical
  have hΔ' : (W⁄(AlgebraicClosure F)).Δ = 0 := by
    simp [WeierstrassCurve.baseChange, hΔ]
  have hc₄' : (W⁄(AlgebraicClosure F)).c₄ ≠ 0 := by
    simpa [WeierstrassCurve.baseChange] using hc₄
  obtain ⟨P, hP⟩ := exists_point_addOrderOf_eq_of_nodal (W⁄(AlgebraicClosure F)) hΔ' hc₄'
    (n := n) (by
      simpa only [← map_natCast (algebraMap F (AlgebraicClosure F)), _root_.map_ne_zero] using hn)
  obtain ⟨M, hM, hnormal, hQ⟩ := P.exists_finiteDimensional_normal_map_val_eq
  refine ⟨M, hM, hnormal, ?_⟩
  intro
  obtain ⟨Q, hQ⟩ := hQ
  exact ⟨Q, (addOrderOf_injective (Affine.Point.map M.val)
    (Affine.Point.map_injective M.val) Q).symm.trans
    ((congrArg addOrderOf hQ).trans hP)⟩

open ValuativeRel TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A nodal cubic over the residue field acquires a point of any prescribed order prime to the
residue characteristic in the residue field of a finite unramified extension. The extension is
the canonical `unramifiedExtension` of some positive degree; it need not be minimal. -/
theorem exists_unramifiedExtension_residue_addOrderOf_eq_of_nodal
    (W : WeierstrassCurve 𝓀[K]) (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ ≠ 0)
    {n : ℕ} (hn : (n : 𝓀[K]) ≠ 0) :
    ∃ f : ℕ, f ≠ 0 ∧
      let L := unramifiedExtension K Ω f
      letI := finiteIntermediateFieldValuativeRel K Ω L
      letI := finiteIntermediateFieldTopology K Ω L
      letI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
      letI := finiteIntermediateField_valuativeExtension K Ω L
      ∀ [DecidableEq 𝓀[L]], ∃ P : (W⁄𝓀[L]).toAffine.Point, addOrderOf P = n := by
  classical
  obtain ⟨M, hM, _, hP⟩ := W.exists_finiteDimensional_normal_point_addOrderOf_eq_of_nodal
    hΔ hc₄ hn
  have := hM
  let f := Module.finrank 𝓀[K] M
  refine ⟨f, Module.finrank_pos.ne', ?_⟩
  dsimp only
  let L := unramifiedExtension K Ω f
  let := finiteIntermediateFieldValuativeRel K Ω L
  let := finiteIntermediateFieldTopology K Ω L
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have := finiteIntermediateField_valuativeExtension K Ω L
  intro
  obtain ⟨e⟩ := nonempty_residueFieldAlgEquiv_unramifiedExtension K Ω M
  obtain ⟨P, hP⟩ := hP
  refine ⟨Affine.Point.map e.symm.toAlgHom P, ?_⟩
  exact (addOrderOf_injective (Affine.Point.map e.symm.toAlgHom)
    (Affine.Point.map_injective e.symm.toAlgHom) P).trans hP

end WeierstrassCurve
