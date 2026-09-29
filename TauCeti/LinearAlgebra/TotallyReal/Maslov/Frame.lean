/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index
public import TauCeti.Topology.Circle.Determinant

/-!
# Changing the frame of a totally real loop

A closed path of complex-linear automorphisms acts pointwise on a loop of maximal totally real
subspaces. Its Maslov index changes by twice the winding number of the determinant of that path.
This is the change-of-trivialization formula used when the boundary Maslov index of a bundle pair
is defined from a choice of frame.

The Maslov phase is `det / conj det`, so the factor of two follows by writing it as the square of
the normalized determinant `det / ‖det‖`. See McDuff--Salamon, *J-holomorphic Curves and
Symplectic Topology*, 2nd ed., Appendix C.3.
-/

public section

open scoped ComplexConjugate unitInterval

namespace TauCeti.TotallyRealLoop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Change of frame for the Maslov index.** A closed complex-linear frame path `B` changes the
Maslov index of a loop of maximal totally real subspaces by twice the winding number of the
normalized determinant of `B`. -/
theorem maslovIndex_map (Λ : TotallyRealLoop E) (B : I → E ≃L[ℂ] E)
    (hB : Continuous fun t => (B t : E →L[ℂ] E)) (hB01 : B 0 = B 1) :
    (Λ.map B hB hB01).maslovIndex =
      Λ.maslovIndex + 2 * Circle.degree (normalizedDetPath B hB hB01) := by
  let hL₀ := Λ.isMaximalTotallyReal 0
  let x : Circle := ⟨hL₀.maslovPhase (Λ.isMaximalTotallyReal 0),
    mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩
  let γ : Path x x :=
    { toFun := fun t => ⟨hL₀.maslovPhase (Λ.isMaximalTotallyReal t),
        mem_sphere_zero_iff_norm.2 (IsMaximalTotallyReal.norm_maslovPhase _ _)⟩
      continuous_toFun := (Λ.continuous_maslovPhase hL₀).subtype_mk _
      source' := rfl
      target' := Circle.ext (hL₀.maslovPhase_congr _ _ Λ.toFun_zero_eq_toFun_one.symm) }
  let δ := normalizedDetPath B hB hB01
  have hphase (t : I) :
      hL₀.maslovPhase ((Λ.map B hB hB01).isMaximalTotallyReal t) =
        hL₀.maslovPhase (Λ.isMaximalTotallyReal t) *
          (LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E) /
            conj (LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E))) := by
    rw [← hL₀.maslovPhase_mul_maslovPhase (Λ.isMaximalTotallyReal t)
      ((Λ.map B hB hB01).isMaximalTotallyReal t)]
    rw [(Λ.isMaximalTotallyReal t).maslovPhase_congr _
      ((Λ.isMaximalTotallyReal t).map_linearEquiv (B t).toLinearEquiv)
      (Λ.map_apply B hB hB01 t)]
    rw [IsMaximalTotallyReal.maslovPhase_map]
  have hδphase (t : I) :
      (δ t : ℂ) * (δ t : ℂ) =
        LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E) /
          conj (LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E)) := by
    rw [normalizedDetPath_apply]
    symm
    exact Complex.div_conj_eq_normalized_mul _
  have hμ : Λ.maslovIndex = Circle.degree γ :=
    Λ.maslovIndex_eq_degree hL₀ γ (fun _ => rfl)
  have hμmap : (Λ.map B hB hB01).maslovIndex = Circle.degree (γ.mul (δ.mul δ)) := by
    apply (Λ.map B hB hB01).maslovIndex_eq_degree hL₀ _
    intro t
    simp only [Path.mul_apply, Circle.coe_mul]
    rw [hphase, ← hδphase]
    rfl
  rw [hμmap, Circle.degree_mul, Circle.degree_mul, ← hμ]
  ring

end TauCeti.TotallyRealLoop

end
