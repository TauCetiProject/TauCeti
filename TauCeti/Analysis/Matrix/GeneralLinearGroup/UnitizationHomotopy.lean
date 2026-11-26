/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Unitization

/-!
# Homotopy invariance and zero maps for `K₁` of nonunital C⋆-algebras

For C⋆-algebras `A` and `B`, `K₁(A) = TauCeti.UnitizationKOne ℂ A` is functorial for star
homomorphisms (`TauCeti.UnitizationKOne.map`). This file proves two properties of this
functoriality (OperatorKTheory K2.2):

* **homotopy invariance**: a point-norm continuous path `t ↦ φₜ` of star homomorphisms
  `A → B`, `t ∈ [0, 1]`, induces the same map `K₁(A) → K₁(B)` at both ends
  (`TauCeti.UnitizationKOne.map_eq_of_continuous`). For an invertible matrix `u` over `A⁺`, the
  invertible matrices obtained by applying `φₜ⁺` to the entries form a path in `GLₙ(B⁺)`, so the
  two ends have the same class;
* **zero maps**: the zero star homomorphism induces the trivial map
  (`TauCeti.UnitizationKOne.map_zero_eq_one`), since its unitization sends every invertible
  matrix to its scalar part, whose class comes from `π₀GL_∞(ℂ)`, which is trivial.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Mathematical Sciences Research
  Institute Publications 5, Cambridge University Press (1998), 8.1.5 and Corollary 8.3.7.
-/

public section

open Matrix

namespace TauCeti.UnitizationKOne

open scoped CStarAlgebra

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- For a point-norm continuous path `t ↦ φₜ` of star homomorphisms, applying `φₜ⁺` to the
entries of an invertible matrix over `A⁺` gives a continuous path in `GLₙ(B⁺)`. -/
theorem continuous_units_map_starMap {φ : unitInterval → A →⋆ₙₐ[ℂ] B}
    (hφ : ∀ a, Continuous fun t ↦ φ t a) {n : Type*} [Fintype n] [DecidableEq n]
    (u : GL n (Unitization ℂ A)) :
    Continuous fun t ↦ Units.map ((Unitization.starMap (φ t) :
      Unitization ℂ A →+* Unitization ℂ B).mapMatrix (m := n)).toMonoidHom u := by
  have hentry (v : Matrix n n (Unitization ℂ A)) :
      Continuous fun t ↦ (v.map (Unitization.starMap (φ t)) : Matrix n n (Unitization ℂ B)) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    refine Unitization.continuous_iff.2 ⟨?_, ?_⟩
    · simp only [Matrix.map_apply, Unitization.fst_starMap]
      exact continuous_const
    · simp only [Matrix.map_apply, Unitization.snd_starMap]
      exact hφ _
  refine Units.continuous_iff.2 ⟨hentry (u : Matrix n n (Unitization ℂ A)), ?_⟩
  simp only [← map_inv]
  exact hentry ((u⁻¹ : GL n (Unitization ℂ A)) : Matrix n n (Unitization ℂ A))

/-- **Homotopy invariance of `K₁`.** A point-norm continuous path `t ↦ φₜ`, `t ∈ [0, 1]`, of star
homomorphisms `A → B` induces the same map `K₁(A) → K₁(B)` at `t = 0` and `t = 1`. -/
theorem map_eq_of_continuous {φ : unitInterval → A →⋆ₙₐ[ℂ] B}
    (hφ : ∀ a, Continuous fun t ↦ φ t a) : map (φ 0) = map (φ 1) := by
  ext x
  obtain ⟨n, u, hu⟩ := StableComponentGroup.exists_mk (x : StableComponentGroup (Unitization ℂ A))
  rw [coe_map, coe_map, ← hu, StableComponentGroup.map_mk, StableComponentGroup.map_mk,
    StableComponentGroup.mk_eq_mk_iff]
  refine ⟨n, le_rfl, ?_⟩
  rw [stabilizeGL_refl, MonoidHom.id_apply]
  have hpath : Joined
      (Units.map ((Unitization.starMap (φ 0) :
        Unitization ℂ A →+* Unitization ℂ B).mapMatrix (m := Fin n)).toMonoidHom u)
      (Units.map ((Unitization.starMap (φ 1) :
        Unitization ℂ A →+* Unitization ℂ B).mapMatrix (m := Fin n)).toMonoidHom u) :=
    ⟨⟨⟨_, continuous_units_map_starMap hφ u⟩, rfl, rfl⟩⟩
  exact hpath.inv_mul_mem_connectedComponentOfOne

/-- **Zero maps on `K₁`.** The zero star homomorphism induces the trivial map on `K₁`. -/
@[simp]
theorem map_zero_eq_one : map (0 : A →⋆ₙₐ[ℂ] B) = 1 := by
  ext x
  obtain ⟨n, u, hu⟩ := StableComponentGroup.exists_mk (x : StableComponentGroup (Unitization ℂ A))
  rw [coe_map, ← hu, StableComponentGroup.map_mk, MonoidHom.one_apply, OneMemClass.coe_one]
  have h : Units.map ((Unitization.starMap (0 : A →⋆ₙₐ[ℂ] B) :
      Unitization ℂ A →+* Unitization ℂ B).mapMatrix (m := Fin n)).toMonoidHom u =
        unitizationGLInl ℂ B (Fin n) (unitizationGLFst ℂ A (Fin n) u) := by
    refine Units.ext (Matrix.ext fun i j ↦ Unitization.ext ?_ ?_) <;> simp
  rw [h, ← map_inlRingHom_mk, Subsingleton.elim (StableComponentGroup.mk ℂ n _) 1, map_one]

end TauCeti.UnitizationKOne
