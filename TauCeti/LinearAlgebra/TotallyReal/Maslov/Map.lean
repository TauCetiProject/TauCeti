/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index

/-!
# The Maslov index of a loop moved by a loop of automorphisms

Let `Λ` be a loop of maximal totally real subspaces of a finite-dimensional complex normed space
`E` and `B` a loop of complex-linear automorphisms of `E`. The pointwise image
`t ↦ B t (Λ t)` (`TauCeti.TotallyRealLoop.map`) is again such a loop, and its Maslov index is

`μ(B Λ) = μ(Λ) + 2 deg (det B)`,

where `deg (det B)` is the winding number of the loop of determinants, read as the degree of the
circle loop `t ↦ det (B t) / ‖det (B t)‖`
(`TauCeti.TotallyRealLoop.maslovIndex_map`). The reason is that the Maslov phase
`ρ(L₀, A L₀) = det A / conj (det A)` is multiplicative and that `z / conj z = (z / ‖z‖) ^ 2`
for `z ≠ 0`. In particular a constant automorphism does not change the Maslov index
(`TauCeti.TotallyRealLoop.maslovIndex_map_const`).

This is the product axiom of the Maslov index of totally real loops, complementing homotopy
invariance and the normalization (`TauCeti.LinearAlgebra.TotallyReal.Maslov.Index`) and the
direct-sum axiom (`TauCeti.LinearAlgebra.TotallyReal.Maslov.Prod`). It is the formula that
controls a change of trivialization: the boundary Maslov index of a bundle pair over a surface
with boundary is computed from the boundary loop in a trivialization, and two trivializations of a
bundle over a disk differ along the boundary by a loop of automorphisms that extends over the disk,
whose determinant therefore has degree zero.

## Main declarations

* `TauCeti.TotallyRealLoop.maslovIndex_map`: `μ(B Λ) = μ(Λ) + 2 deg (det B)`.
* `TauCeti.TotallyRealLoop.maslovIndex_map_const`: a constant automorphism preserves the Maslov
  index.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (the product axiom of the Maslov index of
  loops of totally real subspaces).
-/

public section

open scoped ComplexConjugate unitInterval

namespace TauCeti

namespace TotallyRealLoop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (Λ : TotallyRealLoop E)

/-- **The Maslov index under a loop of automorphisms.** If `B` is a loop of complex-linear
automorphisms and `δ` is the circle loop of normalized determinants,
`det (B t) = ‖det (B t)‖ δ t`, then `μ(B Λ) = μ(Λ) + 2 deg δ`. -/
theorem maslovIndex_map (B : I → E ≃L[ℂ] E) (hB : Continuous fun t => (B t : E →L[ℂ] E))
    (hB01 : B 0 = B 1) {x : Circle} (δ : Path x x)
    (hδ : ∀ t, LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E) =
      ‖LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E)‖ * δ t) :
    (Λ.map B hB hB01).maslovIndex = Λ.maslovIndex + 2 * Circle.degree δ := by
  have hL₀ := Λ.isMaximalTotallyReal 0
  -- The determinant phase of `B t` is the square of its normalized determinant `δ t`.
  have hdet (t : I) : LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E) /
      conj (LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E)) = δ t * δ t := by
    have hd : LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E) ≠ 0 :=
      (B t).toLinearEquiv.isUnit_det'.ne_zero
    have hn : ((‖LinearMap.det ((B t).toLinearEquiv : E →ₗ[ℂ] E)‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using hd
    rw [hδ t]
    simp [← Circle.coe_inv_eq_conj, mul_div_mul_left _ _ hn]
  -- Hence the phases of `B Λ` are those of `Λ` times the square of `δ`.
  have hμ := (Λ.map B hB hB01).maslovIndex_eq_degree hL₀
    (Λ.maslovPhasePath.mul (δ.mul δ)) fun t => by
      rw [Path.mul_apply, Path.mul_apply, Circle.coe_mul, Circle.coe_mul, maslovPhasePath_apply,
        ← hdet, ← (Λ.isMaximalTotallyReal t).maslovPhase_map (B t).toLinearEquiv,
        hL₀.maslovPhase_mul_maslovPhase]
      exact hL₀.maslovPhase_congr _ _ (Λ.map_apply B hB hB01 t).symm
  rw [hμ, Circle.degree_mul, Circle.degree_mul,
    ← Λ.maslovIndex_eq_degree hL₀ Λ.maslovPhasePath Λ.maslovPhasePath_apply]
  ring

/-- **Naturality of the Maslov index.** Moving a loop of maximal totally real subspaces by a fixed
complex-linear automorphism does not change its Maslov index. -/
@[simp]
theorem maslovIndex_map_const (A : E ≃L[ℂ] E) :
    (Λ.map (fun _ => A) continuous_const rfl).maslovIndex = Λ.maslovIndex := by
  have hd : LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
  let x : Circle := ⟨LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E) /
      ‖LinearMap.det (A.toLinearEquiv : E →ₗ[ℂ] E)‖,
    mem_sphere_zero_iff_norm.2 (by simp [hd])⟩
  rw [Λ.maslovIndex_map _ _ _ (Path.refl x) fun _ => ?_, Circle.degree_refl, mul_zero, add_zero]
  rw [Path.refl_apply, mul_div_cancel₀ _ (by simpa using hd)]

end TotallyRealLoop

end TauCeti
