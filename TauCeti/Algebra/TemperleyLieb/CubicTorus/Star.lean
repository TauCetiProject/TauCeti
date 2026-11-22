/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Star
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.RingTheory.TraceFunctional.Radical

/-!
# The adjoint on the cubic quantum torus and the trace radical at `δ = √3`

The factor set `α(a, b) = ω ^ (2 B(a, b))` of the cubic quantum torus `G_N = CubicTorus N` takes
values in the cube roots of unity, so `G_N` carries the conjugate-linear, product-reversing
involution of a twisted group algebra with unitary factor set
(`TauCeti.TwistedMonoidAlgebra.instStarRing`). Since `B(a, -a) = 0`, it is
`(Σ z_a W(a))† = Σ conj(z_a) W(-a)`: every `W(a)` is unitary with `W(a)† = W(-a)`, the site
unitaries satisfy `U_j† = U_j ^ 2`, and the cubic projections `p_j = 3⁻¹ (1 + U_j + U_j ^ 2)` are
self-adjoint. The adjoint commutes with the inversion `θ_N` and with the inclusions
`I_N : G_N → G_(N+1)`, so the fixed subalgebra `C_N` is star-stable. The scalar coefficient
`s_N` satisfies `s_N(x† x) = Σ_a |x_a|²`, so it is a faithful positive trace.

For the analytic adjoint of `TemperleyLieb ℂ (√3 : ℂ) m`, which fixes the generators, the cubic
comparison map `F_m = cubicHom m` is therefore a star homomorphism. Every Markov trace at
`δ = √3` is `(√3) ^ m s_(m-1) ∘ F_m`, a faithful positive functional pulled back along `F_m`, so
its trace radical `{x | ∀ y, tr (x y) = 0}` is exactly the kernel of `F_m`. This does not use
surjectivity of `F_m`: it identifies the Jones quotient at `δ = √3` with the image of `F_m`.

## Main results

* `TauCeti.TemperleyLieb.star_weyl`, `TauCeti.TemperleyLieb.star_cubicSite` and
  `TauCeti.TemperleyLieb.isSelfAdjoint_cubicProjection`: the adjoint on the cubic quantum torus.
* `TauCeti.TemperleyLieb.cubicInversion_star`, `TauCeti.TemperleyLieb.star_mem_cubicFixed` and
  `TauCeti.TemperleyLieb.cubicIncl_star`: compatibility with the inversion and the inclusions.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient_star_mul_self_eq_zero_iff`: the scalar
  coefficient is faithful.
* `TauCeti.TemperleyLieb.coe_cubicHom_star`: the cubic comparison map preserves the adjoint.
* `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicHom`: the trace radical of a
  Markov trace at `δ = √3` is the kernel of the cubic comparison map.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), §4.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, for the trace radical and the Jones
  quotients.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

open TwistedMonoidAlgebra

/-! ### The adjoint on the cubic quantum torus -/

section CubicTorus

variable {N : ℕ}

/-- The cube roots of unity `ω ^ x` are unitary. -/
theorem cubeRootPow_mem_unitary (x : ZMod 3) : (cubeRootPow x : ℂ) ∈ unitary ℂ := by
  rw [coe_cubeRootPow, ZMod.stdAddChar_apply, Unitary.mem_iff, Complex.star_def,
    ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← Circle.coe_mul, inv_mul_cancel, mul_inv_cancel,
    Circle.coe_one, and_self]

/-- The factor set of the cubic quantum torus takes values in the cube roots of unity, so it is
unitary and `CubicTorus N` is a star algebra. -/
instance : IsUnitaryFactorSet (cubicFactor N) :=
  ⟨fun _ _ ↦ by rw [cubicFactor_apply]; exact cubeRootPow_mem_unitary _⟩

/-- The adjoint of a basis element: `W(a)† = W(-a)`. -/
@[simp]
theorem star_weyl (a : Fin N → ZMod 3) : star (weyl N a) = weyl N (-a) := by
  rw [weyl_def, star_of, cubicFactor_apply]
  simp [weyl_def]

/-- The basis elements of the cubic quantum torus are unitary. -/
theorem weyl_mem_unitary (a : Fin N → ZMod 3) : weyl N a ∈ unitary (CubicTorus N) := by
  rw [weyl_def]
  exact of_mem_unitary _

/-- The adjoint of a site unitary is its inverse `U_j ^ 2`. -/
@[simp]
theorem star_cubicSite (j : Fin N) : star (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [← cubicInversion_cubicSite, cubicSite_def, star_weyl, cubicInversion_weyl]

/-- The cubic projections are self-adjoint. -/
theorem isSelfAdjoint_cubicProjection (j : Fin N) : IsSelfAdjoint (cubicProjection N j) := by
  have h4 : cubicSite N j ^ 4 = cubicSite N j := by
    rw [pow_succ, cubicSite_pow_three, one_mul]
  simp [IsSelfAdjoint, cubicProjection_def, star_pow, ← pow_mul, h4, add_right_comm]

/-- The inversion commutes with the adjoint. -/
theorem cubicInversion_star (x : CubicTorus N) :
    cubicInversion N (star x) = star (cubicInversion N x) :=
  TwistedMonoidAlgebra.map_star_iff.2
    (fun g ↦ by rw [of_eq_weyl, cubicInversion_weyl]; exact weyl_mem_unitary _) x

/-- The inversion-fixed subalgebra is stable under the adjoint. -/
theorem star_mem_cubicFixed {x : CubicTorus N} (hx : x ∈ cubicFixed N) : star x ∈ cubicFixed N := by
  rw [mem_cubicFixed] at hx ⊢
  rw [cubicInversion_star, hx]

/-- The scalar coefficient conjugates under the adjoint. -/
@[simp]
theorem cubicScalarCoefficient_star (x : CubicTorus N) :
    cubicScalarCoefficient N (star x) = star (cubicScalarCoefficient N x) := by
  simp [cubicScalarCoefficient_apply, repr_star_apply, IsFactorSet.one_left]

/-- The scalar coefficient is a positive functional: `0 ≤ s_N(x† x)`. -/
theorem cubicScalarCoefficient_star_mul_self_nonneg (x : CubicTorus N) :
    0 ≤ cubicScalarCoefficient N (star x * x) := by
  rw [cubicScalarCoefficient_apply]
  exact repr_star_mul_self_apply_one_nonneg x

/-- The scalar coefficient is faithful: `s_N(x† x) = 0` only for `x = 0`. -/
@[simp]
theorem cubicScalarCoefficient_star_mul_self_eq_zero_iff {x : CubicTorus N} :
    cubicScalarCoefficient N (star x * x) = 0 ↔ x = 0 := by
  rw [cubicScalarCoefficient_apply, repr_star_mul_self_apply_one_eq_zero_iff]

/-- The inclusion of cubic quantum tori preserves the adjoint. -/
@[simp]
theorem cubicIncl_star (x : CubicTorus N) : cubicIncl N (star x) = star (cubicIncl N x) :=
  TwistedMonoidAlgebra.map_star_iff.2
    (fun g ↦ by rw [of_eq_weyl, cubicIncl_weyl]; exact weyl_mem_unitary _) x

end CubicTorus

/-! ### The comparison map and the trace radical -/

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact`, so that
`TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m` carries the analytic adjoint
`TemperleyLieb.instStarRing`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

/-- **The cubic comparison map preserves the adjoint**: `F_m(x†) = F_m(x)†`. -/
@[simp]
theorem coe_cubicHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (cubicHom m (star x) : CubicTorus (m - 1)) = star (cubicHom m x : CubicTorus (m - 1)) :=
  TemperleyLieb.map_star_iff (F := (cubicFixed (m - 1)).val.comp (cubicHom m)) |>.2 (fun j ↦ by
    rw [AlgHom.comp_apply, Subalgebra.coe_val, coe_cubicHom_e]
    exact IsSelfAdjoint.smul Fact.out (isSelfAdjoint_cubicProjection j)) x

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- **The trace radical at `δ = √3` is the kernel of the cubic comparison map.** -/
theorem traceRadical_eq_ker_cubicHom (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicHom m) := by
  -- This is `LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot` for the faithful positive
  -- functional `(√3) ^ m s_(m-1)`, argued directly: that lemma needs the `NonUnitalRing` structure
  -- of `CubicTorus (m - 1)`, whose instance search exceeds the default budget at this index.
  have hc0 : (Real.sqrt 3 : ℂ) ^ m ≠ 0 :=
    pow_ne_zero m (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 three_pos))
  ext x
  simp only [LinearMap.mem_traceRadical, RingHom.mem_ker,
    htr.apply_eq_mul_cubicScalarCoefficient_cubicHom, map_mul, Subalgebra.coe_mul, mul_eq_zero,
    hc0, false_or]
  refine ⟨fun h ↦ Subtype.ext ?_, fun h y ↦ by simp [h]⟩
  -- Test against `y = x†`: `s(F x F(x)†) = s(F(x)† F x)` vanishes only when `F x = 0`.
  have hx := h (star x)
  rwa [coe_cubicHom_star, cubicScalarCoefficient_mul_comm,
    cubicScalarCoefficient_star_mul_self_eq_zero_iff] at hx

end IsMarkovTrace

end TauCeti.TemperleyLieb
