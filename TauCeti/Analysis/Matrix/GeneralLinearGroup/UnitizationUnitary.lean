/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Polar
public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Unitization

/-!
# Unitary representatives of `K₁` of a nonunital C⋆-algebra

For a nonunital C⋆-algebra `A`, `K₁(A)` (`TauCeti.UnitizationKOne ℂ A`) is the kernel of the map
`π₀GL_∞(A⁺) → π₀GL_∞(ℂ)` induced by the scalar part of the unitization. This file gives its
classical description by unitaries of `A⁺` whose scalar part is the identity (Blackadar 8.1.5):

* every class of `K₁(A)` is the class of a unitary matrix over `A⁺` with scalar part `1`
  (`TauCeti.UnitizationKOne.exists_mem_unitary_mk_eq`);
* two unitary matrices over `A⁺` with scalar part `1` have the same class exactly when, after a
  common stabilization, they are joined by a path of unitary matrices with scalar part `1`
  (`TauCeti.UnitizationKOne.mk_eq_mk_iff_exists_path_unitary`).

Both come from main's unitary description of `π₀GL_∞(A⁺)` for the unital C⋆-algebra `A⁺`
(`TauCeti.StableComponentGroup.exists_mem_unitary_mk_eq`,
`TauCeti.StableComponentGroup.mk_eq_mk_iff_exists_path_unitary`) and the retraction
`g ↦ g · s(g)⁻¹` onto the matrices with scalar part `1` (`TauCeti.unitizationGLRetract`), which
preserves unitary matrices (`TauCeti.coe_unitizationGLRetract_mem_unitary`): the scalar part of a
unitary matrix is a unitary scalar matrix.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Mathematical Sciences Research
  Institute Publications 5, Cambridge University Press (1998), 8.1.5.
-/

public section

open Matrix

namespace TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] {n : Type*} [Fintype n] [DecidableEq n]

/-- Applying a star-preserving ring homomorphism entrywise preserves unitary matrices. -/
theorem _root_.Matrix.map_mem_unitary {R S : Type*} [Semiring R] [StarRing R] [Semiring S]
    [StarRing S] (f : R →+* S) (hf : ∀ x, f (star x) = star (f x)) {M : Matrix n n R}
    (hM : M ∈ unitary (Matrix n n R)) : M.map f ∈ unitary (Matrix n n S) := by
  have hs : star (M.map f) = (star M).map f := by
    ext i j
    simp [star_apply, hf]
  rw [Unitary.mem_iff] at hM ⊢
  rw [hs, ← Matrix.map_mul, ← Matrix.map_mul, hM.1, hM.2, Matrix.map_one _ f.map_zero f.map_one]
  exact ⟨rfl, rfl⟩

/-- The scalar part of a unitary matrix over `A⁺` is a unitary scalar matrix. -/
theorem coe_unitizationGLFst_mem_unitary {g : GL n (Unitization ℂ A)}
    (hg : (g : Matrix n n (Unitization ℂ A)) ∈ unitary _) :
    ((unitizationGLFst ℂ A n g : GL n ℂ) : Matrix n n ℂ) ∈ unitary (Matrix n n ℂ) := by
  rw [coe_unitizationGLFst]
  exact Matrix.map_mem_unitary (Unitization.fstHom ℂ A : Unitization ℂ A →+* ℂ)
    (fun x ↦ Unitization.fst_star x) hg

/-- A unitary scalar matrix stays unitary over `A⁺`. -/
theorem coe_unitizationGLInl_mem_unitary {g : GL n ℂ}
    (hg : (g : Matrix n n ℂ) ∈ unitary (Matrix n n ℂ)) :
    ((unitizationGLInl ℂ A n g : GL n (Unitization ℂ A)) : Matrix n n (Unitization ℂ A)) ∈
      unitary _ := by
  rw [coe_unitizationGLInl]
  exact Matrix.map_mem_unitary (Unitization.inlRingHom ℂ A) (fun x ↦ Unitization.inl_star x) hg

/-- The inverse of an invertible unitary matrix is unitary. -/
theorem coe_inv_mem_unitary {R : Type*} [Ring R] [StarRing R] {g : GL n R}
    (hg : (g : Matrix n n R) ∈ unitary (Matrix n n R)) :
    ((g⁻¹ : GL n R) : Matrix n n R) ∈ unitary (Matrix n n R) := by
  have h : ((g⁻¹ : GL n R) : Matrix n n R) = star (g : Matrix n n R) :=
    Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem hg)
  rw [h]
  exact Unitary.star_mem hg

/-- The retraction `g ↦ g · s(g)⁻¹` onto the matrices with scalar part `1` preserves unitary
matrices. -/
theorem coe_unitizationGLRetract_mem_unitary {g : GL n (Unitization ℂ A)}
    (hg : (g : Matrix n n (Unitization ℂ A)) ∈ unitary _) :
    ((unitizationGLRetract ℂ A n g : GL n (Unitization ℂ A)) : Matrix n n (Unitization ℂ A)) ∈
      unitary _ := by
  rw [unitizationGLRetract_def, Units.val_mul]
  exact mul_mem hg (coe_inv_mem_unitary
    (coe_unitizationGLInl_mem_unitary (coe_unitizationGLFst_mem_unitary hg)))

namespace UnitizationKOne

/-- **Unitary representatives of `K₁(A)`.** Every class of `K₁(A)` is the class of a unitary
matrix over `A⁺` whose scalar part is the identity. -/
theorem exists_mem_unitary_mk_eq {x : StableComponentGroup (Unitization ℂ A)}
    (hx : x ∈ UnitizationKOne ℂ A) :
    ∃ m, ∃ u ∈ unitizationGLFstOne ℂ A (Fin m),
      (u : Matrix (Fin m) (Fin m) (Unitization ℂ A)) ∈ unitary _ ∧
        StableComponentGroup.mk _ m u = x := by
  obtain ⟨m, g, hg, rfl⟩ := StableComponentGroup.exists_mem_unitary_mk_eq x
  refine ⟨m, unitizationGLRetract ℂ A (Fin m) g, unitizationGLRetract_mem_unitizationGLFstOne g,
    coe_unitizationGLRetract_mem_unitary hg, ?_⟩
  have h₁ : StableComponentGroup.mk ℂ m (unitizationGLFst ℂ A (Fin m) g) = 1 :=
    Subsingleton.elim _ _
  have h₂ : StableComponentGroup.mk _ m
      (unitizationGLInl ℂ A (Fin m) (unitizationGLFst ℂ A (Fin m) g)) = 1 := by
    rw [← map_inlRingHom_mk, h₁, map_one]
  rw [unitizationGLRetract_def, map_mul, map_inv, h₂, inv_one, mul_one]

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
