/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Polar
public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Unitization.Basic

/-!
# Unitary representatives of `K₁` of a nonunital C⋆-algebra

For a nonunital C⋆-algebra `A`, `K₁(A)` (`TauCeti.UnitizationKOne ℂ A`) is the kernel of the map
`π₀GL_∞(A⁺) → π₀GL_∞(ℂ)` induced by the scalar part of the unitization. This file gives its
classical description by unitaries of `A⁺` whose scalar part is the identity (Blackadar 8.1.5):

* every class of `π₀GL_∞(A⁺)`, which is all of `K₁(A)` (`TauCeti.UnitizationKOne.eq_top`), is the
  class of a unitary matrix over `A⁺` with scalar part `1`
  (`TauCeti.UnitizationKOne.exists_mem_unitary_mk_eq`);
* two unitary matrices over `A⁺` with scalar part `1` have the same class exactly when, after a
  common stabilization, they are joined by a path of unitary matrices with scalar part `1`
  (`TauCeti.UnitizationKOne.mk_eq_mk_iff_exists_path_unitary`).

Both come from the unitary description of `π₀GL_∞(A⁺)` for the unital C⋆-algebra `A⁺`
(`TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq`,
`TauCeti.StableComponentGroup.mk_eq_mk_iff_exists_path_unitary`) and the retraction
`g ↦ g · s(g)⁻¹` onto the matrices with scalar part `1` (`TauCeti.unitizationGLRetract`), which
preserves classes (`TauCeti.UnitizationKOne.mk_unitizationGLRetract`) and unitary matrices
(`TauCeti.coe_unitizationGLRetract_mem_unitary`): the scalar part of a unitary matrix is a unitary
scalar matrix.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Mathematical Sciences Research
  Institute Publications 5, Cambridge University Press (1998), 8.1.5.
-/

public section

open Matrix

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A]

namespace UnitizationKOne

/-- **Unitary representatives of `K₁(A)`.** Every class of `π₀GL_∞(A⁺)`, which is all of `K₁(A)`
by `TauCeti.UnitizationKOne.eq_top`, is the class of a unitary matrix over `A⁺` whose scalar part is
the identity. -/
theorem exists_mem_unitary_mk_eq (x : StableComponentGroup (Unitization ℂ A)) :
    ∃ m, ∃ u ∈ unitizationGLFstOne ℂ A (Fin m),
      (u : Matrix (Fin m) (Fin m) (Unitization ℂ A)) ∈ unitary _ ∧
        StableComponentGroup.mk _ m u = x := by
  obtain ⟨m, g, hg, rfl⟩ := StableComponentGroup.exists_mem_unitary_mk_eq x
  exact ⟨m, unitizationGLRetract ℂ A (Fin m) g, unitizationGLRetract_mem_unitizationGLFstOne g,
    coe_unitizationGLRetract_mem_unitary hg, mk_unitizationGLRetract (by rw [eq_top]; trivial)⟩

/-- **The stable homotopy criterion for `K₁(A)` in unitary form.** Two unitary matrices over
`A⁺` with scalar part `1` have the same class exactly when, after a common stabilization, they
are joined by a path of unitary matrices with scalar part `1`. -/
theorem mk_eq_mk_iff_exists_path_unitary {m : ℕ} {u v : GL (Fin m) (Unitization ℂ A)}
    (hu₁ : u ∈ unitizationGLFstOne ℂ A (Fin m)) (hv₁ : v ∈ unitizationGLFstOne ℂ A (Fin m))
    (hu : (u : Matrix (Fin m) (Fin m) (Unitization ℂ A)) ∈ unitary _)
    (hv : (v : Matrix (Fin m) (Fin m) (Unitization ℂ A)) ∈ unitary _) :
    StableComponentGroup.mk _ m u = StableComponentGroup.mk _ m v ↔
      ∃ k, ∃ h : m ≤ k, ∃ γ : Path (stabilizeGL _ h u) (stabilizeGL _ h v),
        ∀ t, γ t ∈ unitizationGLFstOne ℂ A (Fin k) ∧
          (γ t : Matrix (Fin k) (Fin k) (Unitization ℂ A)) ∈ unitary _ := by
  rw [StableComponentGroup.mk_eq_mk_iff_exists_path_unitary hu hv]
  refine exists_congr fun k ↦ exists_congr fun h ↦ ⟨fun ⟨γ, hγ⟩ ↦ ?_, fun ⟨γ, hγ⟩ ↦
    ⟨γ, fun t ↦ (hγ t).2⟩⟩
  have hu' := unitizationGLRetract_of_mem (stabilizeGL_mem_unitizationGLFstOne h hu₁)
  have hv' := unitizationGLRetract_of_mem (stabilizeGL_mem_unitizationGLFstOne h hv₁)
  refine ⟨(γ.map (continuous_unitizationGLRetract ℂ A (Fin k))).cast hu'.symm hv'.symm,
    fun t ↦ ⟨unitizationGLRetract_mem_unitizationGLFstOne _,
      coe_unitizationGLRetract_mem_unitary (hγ t)⟩⟩

end UnitizationKOne

end TauCeti
