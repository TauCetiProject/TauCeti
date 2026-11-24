/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Star
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# The adjoint on the cubic quantum torus and the trace radical at `δ = √3`

The factor set `α(a, b) = ω ^ (2 B(a, b))` of the cubic quantum torus `G_N = CubicTorus N` takes
values in the cube roots of unity, so `G_N` carries the conjugate-linear, product-reversing
involution of a twisted group algebra with unitary factor set
(`TauCeti.TwistedMonoidAlgebra.instStarRing`). Since `B(a, -a) = 0`, it is
`(Σ z_a W(a))† = Σ conj(z_a) W(-a)`: every `W(a)` is unitary with `W(a)† = W(-a)`, the site
unitaries satisfy `U_j† = U_j ^ 2`, and the cubic projections `p_j = 3⁻¹ (1 + U_j + U_j ^ 2)` are
self-adjoint. The adjoint commutes with the inversion `θ_N` and with the inclusions
`I_N : G_N → G_(N+1)`, so the fixed subalgebra `C_N` is star-stable and is itself a star algebra,
with `C_N → G_N` a star algebra homomorphism. The scalar coefficient `s_N` satisfies
`s_N(x† x) = Σ_a |x_a|²`, so it is a faithful positive trace.

For the analytic adjoint of `TemperleyLieb ℂ (√3 : ℂ) m`, which fixes the generators, the cubic
comparison map `F_m = cubicHom m : TL_m(√3) → C_(m-1)` is therefore a star homomorphism. Every
Markov trace at `δ = √3` is `(√3) ^ m s_(m-1) ∘ F_m`, a faithful positive functional pulled back
along `F_m`, so its trace radical `{x | ∀ y, tr (x y) = 0}` is exactly the kernel of `F_m`
(`LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot`). This does not use
surjectivity of `F_m`: it identifies the Jones quotient at `δ = √3` with the image of `F_m`.

## Main results

* `TauCeti.TemperleyLieb.star_weyl`, `TauCeti.TemperleyLieb.star_cubicSite` and
  `TauCeti.TemperleyLieb.isSelfAdjoint_cubicProjection`: the adjoint on the cubic quantum torus.
* `TauCeti.TemperleyLieb.cubicInversion_star`, `TauCeti.TemperleyLieb.star_mem_cubicFixed` and
  `TauCeti.TemperleyLieb.cubicIncl_star`: compatibility with the inversion and the inclusions.
* `TauCeti.TemperleyLieb.coe_star_cubicFixed` and `TauCeti.TemperleyLieb.cubicFixedSubtype`: the
  star structure on `C_N`, and the inclusion `C_N → G_N` as a star algebra homomorphism.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient_star_mul_self_eq_zero_iff`: the scalar
  coefficient is faithful.
* `TauCeti.TemperleyLieb.coe_cubicHom_star` and `TauCeti.TemperleyLieb.cubicStarHom`: the cubic
  comparison map preserves the adjoint, and is bundled as a star algebra homomorphism
  `TL_m(√3) →⋆ₐ[ℂ] C_(m-1)`.
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
  rw [coe_cubeRootPow, ZMod.stdAddChar_apply]
  exact Circle.coe_mem_unitary _

/-- The factor set of the cubic quantum torus takes values in the cube roots of unity, so it is
unitary and `CubicTorus N` is a star algebra. -/
instance : IsUnitaryFactorSet (cubicFactor N) :=
  ⟨fun _ _ ↦ by rw [cubicFactor_apply]; exact cubeRootPow_mem_unitary _⟩

/-- The star ring structure of `CubicTorus N`, recorded at a variable index `N`. Without it,
instance search for the star structure at an index such as `m - 1`, the codomain of the cubic
comparison map, exceeds the default budget while unifying the ring structures of the
subalgebra. -/
noncomputable instance : StarRing (CubicTorus N) :=
  inferInstance

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
@[simp]
theorem cubicInversion_star (x : CubicTorus N) :
    cubicInversion N (star x) = star (cubicInversion N x) :=
  TwistedMonoidAlgebra.map_star_iff.2
    (fun g ↦ by rw [of_eq_weyl, cubicInversion_weyl]; exact weyl_mem_unitary _) x

/-- The inversion-fixed subalgebra is stable under the adjoint. -/
theorem star_mem_cubicFixed {x : CubicTorus N} (hx : x ∈ cubicFixed N) : star x ∈ cubicFixed N := by
  rw [mem_cubicFixed] at hx ⊢
  rw [cubicInversion_star, hx]

/-- The ring structure of the fixed subalgebra `C_N`, recorded as a non-unital semiring at a
variable index `N`. Without it, instance search for the star structure on `C_N`, a subalgebra of a
subalgebra, exceeds the default budget. -/
noncomputable instance : NonUnitalNonAssocSemiring (cubicFixed N) :=
  (cubicFixed N).toRing.toNonUnitalNonAssocSemiring

/-- The adjoint on the fixed subalgebra `C_N`, restricted from `G_N`. Declared directly, so that
instance search at an index such as `m - 1` does not first try to read `C_N` as a star-closed
subset of the endomorphisms underlying `G_N`. -/
noncomputable instance : Star (cubicFixed N) :=
  ⟨fun x ↦ ⟨star (x : CubicTorus N), star_mem_cubicFixed x.property⟩⟩

/-- The adjoint makes `C_N` a star ring. -/
noncomputable instance : StarRing (cubicFixed N) where
  star_involutive x := Subtype.ext (star_star (x : CubicTorus N))
  star_mul x y := Subtype.ext (star_mul (x : CubicTorus N) y)
  star_add x y := Subtype.ext (star_add (x : CubicTorus N) y)

/-- The adjoint on `C_N` is conjugate-linear. -/
instance : StarModule ℂ (cubicFixed N) where
  star_smul r x := Subtype.ext (star_smul r (x : CubicTorus N))

/-- The adjoint on `C_N` is computed in `G_N`. -/
@[simp, norm_cast]
theorem coe_star_cubicFixed (x : cubicFixed N) :
    ((star x : cubicFixed N) : CubicTorus N) = star (x : CubicTorus N) :=
  (rfl)

/-- The inclusion `C_N → G_N` as a star algebra homomorphism. -/
noncomputable def cubicFixedSubtype (N : ℕ) : cubicFixed N →⋆ₐ[ℂ] CubicTorus N where
  toAlgHom := (cubicFixed N).val
  map_star' _ := (rfl)

/-- `cubicFixedSubtype N` evaluates as the coercion. -/
@[simp]
theorem cubicFixedSubtype_apply (x : cubicFixed N) : cubicFixedSubtype N x = x :=
  (rfl)

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

/-- **The cubic comparison map preserves the adjoint**: `F_m(x†) = F_m(x)†`. -/
@[simp]
theorem coe_cubicHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (cubicHom m (star x) : CubicTorus (m - 1)) = star (cubicHom m x : CubicTorus (m - 1)) :=
  TemperleyLieb.map_star_iff (F := (cubicFixed (m - 1)).val.comp (cubicHom m)) |>.2 (fun j ↦ by
    rw [AlgHom.comp_apply, Subalgebra.coe_val, coe_cubicHom_e]
    exact IsSelfAdjoint.smul Fact.out (isSelfAdjoint_cubicProjection j)) x

/-- The cubic comparison map `F_m : TL_m(√3) → C_(m-1)` as a star algebra homomorphism. -/
noncomputable def cubicStarHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1) where
  toAlgHom := cubicHom m
  map_star' x := Subtype.ext (coe_cubicHom_star x)

/-- `cubicStarHom m` evaluates as `F_m`. -/
@[simp]
theorem cubicStarHom_apply {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicStarHom m x = cubicHom m x :=
  (rfl)

/-- The star homomorphism `cubicStarHom m` has the same kernel as `F_m`. -/
@[simp]
theorem ker_cubicStarHom (m : ℕ) : RingHom.ker (cubicStarHom m) = RingHom.ker (cubicHom m) := by
  ext x
  simp [RingHom.mem_ker]

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- **The trace radical at `δ = √3` is the kernel of the cubic comparison map.** -/
theorem traceRadical_eq_ker_cubicHom (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicHom m) := by
  -- Pull back the faithful positive functional `(√3) ^ m s_(m-1)` along `F_m`, read in `G_(m-1)`.
  have hc : (0 : ℂ) < (Real.sqrt 3 : ℂ) ^ m :=
    pow_pos (Complex.zero_lt_real.2 (Real.sqrt_pos.2 three_pos)) m
  have hψ : ((identityCoefficient : StarPositiveFunctional (CubicTorus (m - 1))).smulOfNonneg
      hc.le).nullSubmodule = ⊥ := by
    rw [StarPositiveFunctional.nullSubmodule_smulOfNonneg _ hc, nullSubmodule_identityCoefficient]
  rw [LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot _ _ _ hψ
    ((cubicFixedSubtype (m - 1)).comp (cubicStarHom m)) fun x ↦ by
      simp [htr.apply_eq_mul_cubicScalarCoefficient_cubicHom, cubicScalarCoefficient_apply]]
  ext x
  simp [RingHom.mem_ker]

end IsMarkovTrace

end TauCeti.TemperleyLieb
