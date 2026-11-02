/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star

/-!
# Real Clifford algebras acting on complex and Hermitian modules

Let `Q` be a real quadratic form on `M` and `W` a complex vector space carrying a real algebra
map `ρ : CliffordAlgebra Q → End_ℂ W`; write `c(v) = ρ (ι Q v)`. The Clifford relation gives
`c(v)² = Q v`, so `c(v)` is invertible when `Q v ≠ 0`, and for an anisotropic form and a nonzero
`ψ` the real-linear map `v ↦ c(v) ψ` is injective.

When `W` is a finite-dimensional complex inner product space and the generators act
skew-adjointly, `c(v)* = -c(v)`, `W` is a Hermitian Clifford module, such as a fibre of the
spinor bundle of a `Spinᶜ` manifold. Skew-adjointness of the generators then propagates to the
whole algebra: the adjoint of `ρ a` is `ρ (star a)`, where `star = reverse ∘ involute` is
Mathlib's Clifford conjugation. For the negative-definite form `Q v = -‖v‖²` of a real inner
product space, `c(v)* c(v) = -c(v)² = ‖v‖²`, so Clifford multiplication by `v` scales every norm
by `‖v‖`.

## Main results

* `CliffordAlgebra.map_ι_mul_map_ι`, `CliffordAlgebra.map_ι_apply_map_ι_apply`:
  `c(v) c(v) = Q v`, as operators and pointwise.
* `CliffordAlgebra.map_ι_injective`: `c(v)` is injective when `Q v ≠ 0`.
* `CliffordAlgebra.map_ι_apply_left_injective`: `v ↦ c(v) ψ` is injective for `ψ ≠ 0` and an
  anisotropic `Q`.
* `CliffordAlgebra.adjoint_map_eq_map_star`: `(ρ a)* = ρ (star a)` on a Hermitian Clifford
  module.
* `CliffordAlgebra.norm_map_ι_apply_sq`: `‖c(v) ψ‖² = -Q v ‖ψ‖²` on a Hermitian Clifford module,
  and `CliffordAlgebra.norm_map_ι_apply`: `‖c(v) ψ‖ = ‖v‖ ‖ψ‖` when `Q v = -‖v‖²`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

namespace CliffordAlgebra

variable {M : Type*} {W : Type*}

section Module

variable [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M} [AddCommGroup W] [Module ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

/-- The Clifford relation in a module: `c(v) c(v) = Q v`. -/
theorem map_ι_mul_map_ι (v : M) : ρ (ι Q v) * ρ (ι Q v) = ((Q v : ℝ) : ℂ) • 1 := by
  rw [← map_mul, ι_sq_scalar, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    Complex.coe_smul]

/-- The Clifford relation applied to a vector of the module: `c(v) (c(v) ψ) = Q v ψ`. -/
@[simp]
theorem map_ι_apply_map_ι_apply (v : M) (ψ : W) :
    ρ (ι Q v) (ρ (ι Q v) ψ) = ((Q v : ℝ) : ℂ) • ψ := by
  rw [← Module.End.mul_apply, map_ι_mul_map_ι, LinearMap.smul_apply, Module.End.one_apply]

/-- Clifford multiplication by a vector `v` with `Q v ≠ 0` is injective. -/
theorem map_ι_injective {v : M} (hv : Q v ≠ 0) : Function.Injective (ρ (ι Q v)) := by
  refine (injective_iff_map_eq_zero _).2 fun ψ hψ ↦ ?_
  have h := map_ι_apply_map_ι_apply ρ v ψ
  rw [hψ, map_zero] at h
  exact (smul_eq_zero.1 h.symm).resolve_left (by exact_mod_cast hv)

/-- For an anisotropic form and a nonzero `ψ`, Clifford multiplication `v ↦ c(v) ψ` is
injective. -/
theorem map_ι_apply_left_injective (hQ : Q.Anisotropic) {ψ : W} (hψ : ψ ≠ 0) :
    Function.Injective fun v ↦ ρ (ι Q v) ψ := by
  intro v w h
  by_contra hvw
  have hne : Q (v - w) ≠ 0 := fun h0 ↦ hvw (sub_eq_zero.1 (hQ _ h0))
  refine hψ (map_ι_injective ρ hne ?_)
  simp only [map_sub, LinearMap.sub_apply, map_zero]
  exact sub_eq_zero.2 h

end Module

section Hermitian

variable [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

section Module

variable [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- If the generators act skew-adjointly, `c(v)* = -c(v)`, then the adjoint of the action of any
Clifford element `a` is the action of its Clifford conjugate: `(ρ a)* = ρ (star a)`. -/
theorem adjoint_map_eq_map_star (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (a : CliffordAlgebra Q) : LinearMap.adjoint (ρ a) = ρ (star a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r =>
    rw [star_algebraMap, AlgHom.commutes, Module.algebraMap_end_eq_smul_id,
      ← Complex.coe_smul, map_smulₛₗ, LinearMap.adjoint_id, Complex.conj_ofReal]
  | ι v => rw [hρ, star_ι, map_neg]
  | mul a b ha hb =>
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.adjoint_comp, ha, hb, star_mul, map_mul,
      Module.End.mul_eq_comp]
  | add a b ha hb => rw [map_add, map_add, ha, hb, star_add, map_add]

/-- On a Hermitian Clifford module, `‖c(v) ψ‖² = -Q v ‖ψ‖²`. -/
theorem norm_map_ι_apply_sq (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (v : M)
    (ψ : W) : ‖ρ (ι Q v) ψ‖ ^ 2 = -Q v * ‖ψ‖ ^ 2 := by
  -- `‖c(v) ψ‖² = Re ⟪ψ, c(v)* c(v) ψ⟫ = Re ⟪ψ, -c(v)² ψ⟫ = -Q v ‖ψ‖²`.
  rw [← RCLike.ofReal_inj (K := ℂ), RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K,
    ← LinearMap.adjoint_inner_left, hρ, LinearMap.neg_apply, map_ι_apply_map_ι_apply,
    inner_neg_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.conj_ofReal]
  push_cast
  ring

end Module

variable [SeminormedAddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- For the negative-definite form `Q v = -‖v‖²` and skew-adjoint generators, Clifford
multiplication by `v` scales norms by `‖v‖`: `‖c(v) ψ‖ = ‖v‖ ‖ψ‖`. -/
theorem norm_map_ι_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (v : M) (ψ : W) :
    ‖ρ (ι Q v) ψ‖ = ‖v‖ * ‖ψ‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [norm_map_ι_apply_sq hρ, hQ]
  ring

end Hermitian

end CliffordAlgebra
