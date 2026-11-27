/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.Geometry.Toric.Algebraic.Fan.Divisor.Weights

/-!
# Graded cones of invariant divisors

Let `D = ∑ a_ρ D_ρ` be an invariant divisor with integer coefficients on the toric variety of a
fan. Its *graded cone* consists of the pairs `(u, j)` of a character `u` and a degree `j` with
`u v_ρ + j a_ρ ≥ 0` for the primitive generator `v_ρ` of every ray `ρ`. Over `ℤ`, the pairs of
degree `j` are the character weights of the divisor `j D`, so the monomials of the graded cone
index the sections of all the powers of `O(D)` at once, and adding pairs multiplies sections and
adds degrees. This is the cone underlying the homogeneous coordinate algebra of `O(D)`: Scholze
completes the monoid algebra of its points with coordinates in `ℤ[1/p]` to obtain a perfectoid
graded algebra, through which sections over a perfectoid field are approximated from its tilt.

Characters and degrees take values in an arbitrary ordered commutative ring `R`, so that one
definition covers both the real cone in `M_ℝ × ℝ` (for `R = ℝ`, with `M_ℝ = Hom(N, ℝ)`) and its
`p`-local points in `M[1/p] × ℤ[1/p]` (for `R = ℤ[1/p]`, with `M[1/p] = Hom(N, ℤ[1/p])`). The
points over `R` are the points over `S` with coordinates in `R` whenever `R → S` preserves and
reflects nonnegativity. Over any `R` the graded cone is a pointed cone: it is closed under addition,
and under multiplication by nonnegative scalars, in particular under division by `p` when `p` is
invertible with `0 ≤ p⁻¹` (e.g. `p > 0` in a linearly ordered `R` such as `ℤ[1/p]`).

Adding the divisor of a character `χ ^ m` shears the graded cone by the transvection
`(u, j) ↦ (u - j m, j)`, which preserves degrees. When the fan is complete, the only point of
degree `0` is the origin: a character nonnegative on every ray of a complete fan vanishes, because
some positive multiple of every lattice point is a sum of primitive ray generators of one cone. In
particular the graded cone of the zero divisor is `{0} × R`, with all degrees, negative ones
included.

## Main declarations

* `TauCeti.Toric.Fan.gradedDivisorCone`: the graded cone of an invariant divisor, as a pointed cone
  in `Hom(N, R) × R`.
* `TauCeti.Toric.Fan.mk_mem_gradedDivisorCone_int_iff`: over `ℤ`, the points of degree `j` are
  the character weights of `j D`.
* `TauCeti.Toric.Fan.mk_comp_mem_gradedDivisorCone_iff`: the points over `R` are the points over
  `S` with coordinates in `R`.
* `TauCeti.Toric.Fan.gradedDivisorCone_add_characterDivisor` and
  `TauCeti.Toric.Fan.map_transvection_gradedDivisorCone`: adding the divisor of `χ ^ m` shears the
  graded cone by `(u, j) ↦ (u - j m, j)`.
* `TauCeti.Toric.Fan.IsComplete.mk_zero_mem_gradedDivisorCone_iff` and
  `TauCeti.Toric.Fan.IsComplete.mem_gradedDivisorCone_zero_iff`: for a complete fan the degree-zero
  part is the origin, and the graded cone of the zero divisor is `{0} × R`.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §8, proof of Proposition 8.7.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §4.3 and §5.4.
-/

public section

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Phi : Fan i}

/-! ### The graded cone -/

section OrderedRing

variable (Phi) (R : Type*) [CommRing R] [PartialOrder R] [IsOrderedRing R]

/-- The graded cone of the invariant divisor with integer ray coefficients `a`, with coordinates in
an ordered commutative ring `R`: the pairs `(u, j)` of a character `u : N →+ R` and a degree
`j : R` with `u v_ρ + j a_ρ ≥ 0` for the primitive generator `v_ρ` of every ray `ρ`. Over `ℤ`, its
points of degree `j` are the character weights of `j D` (`mk_mem_gradedDivisorCone_int_iff`). -/
def gradedDivisorCone (a : Phi.Ray → ℤ) : PointedCone R ((N →+ R) × R) where
  carrier := {x | ∀ rho, 0 ≤ x.1 rho.primitiveGenerator + x.2 * a rho}
  add_mem' {x y} hx hy rho := by
    simpa [add_mul, add_add_add_comm] using add_nonneg (hx rho) (hy rho)
  zero_mem' rho := by simp
  smul_mem' c x hx rho := by
    simpa [← Nonneg.coe_smul, mul_add, mul_assoc] using mul_nonneg c.property (hx rho)

variable {Phi R}

@[simp]
theorem mem_gradedDivisorCone {a : Phi.Ray → ℤ} {x : (N →+ R) × R} :
    x ∈ Phi.gradedDivisorCone R a ↔ ∀ rho, 0 ≤ x.1 rho.primitiveGenerator + x.2 * a rho :=
  Iff.rfl

/-- Over `ℤ`, the points of the graded cone of `D` of degree `j` are the character weights of
`j D`. -/
theorem mk_mem_gradedDivisorCone_int_iff {a : Phi.Ray → ℤ} {u : N →+ ℤ} {j : ℤ} :
    (u, j) ∈ Phi.gradedDivisorCone ℤ a ↔ u ∈ Phi.divisorWeights (j • a) := by
  simp only [mem_gradedDivisorCone, Int.cast_id, mem_divisorWeights_iff_add_nonneg, Pi.smul_apply,
    smul_eq_mul]

/-- The points of the graded cone over `R` are the points over `S` with coordinates in `R`, for a
ring map `f : R →+* S` which preserves and reflects nonnegativity. For `ℤ[1/p] ⊆ ℝ` this exhibits
the `p`-local points of the real graded cone. -/
theorem mk_comp_mem_gradedDivisorCone_iff {S : Type*} [CommRing S] [PartialOrder S]
    [IsOrderedRing S] (f : R →+* S) (hf : ∀ x, 0 ≤ f x ↔ 0 ≤ x) {a : Phi.Ray → ℤ}
    {u : N →+ R} {j : R} :
    (f.toAddMonoidHom.comp u, f j) ∈ Phi.gradedDivisorCone S a ↔
      (u, j) ∈ Phi.gradedDivisorCone R a := by
  simp only [mem_gradedDivisorCone]
  refine forall_congr' fun rho ↦ Iff.trans ?_ (hf _)
  simp

/-- Adding the divisor of the character `χ ^ m` shears the graded cone: `(u, j)` is a point for
`D + div χ ^ m` exactly when `(u + j m, j)` is a point for `D`. -/
theorem mem_gradedDivisorCone_add_characterDivisor {a : Phi.Ray → ℤ} {m : N →+ ℤ}
    {x : (N →+ R) × R} :
    x ∈ Phi.gradedDivisorCone R (a + Phi.characterDivisor m) ↔
      LinearMap.transvection (LinearMap.snd R (N →+ R) R) ((Int.castAddHom R).comp m, 0) x ∈
        Phi.gradedDivisorCone R a := by
  simp only [mem_gradedDivisorCone]
  refine forall_congr' fun _ ↦ ?_
  congr! 1
  simp [LinearMap.transvection.apply, characterDivisor_apply]
  ring

/-- Adding the divisor of the character `χ ^ m` pulls the graded cone back along the
degree-preserving transvection `(u, j) ↦ (u + j m, j)`. -/
theorem gradedDivisorCone_add_characterDivisor (a : Phi.Ray → ℤ) (m : N →+ ℤ) :
    Phi.gradedDivisorCone R (a + Phi.characterDivisor m) =
      (Phi.gradedDivisorCone R a).comap
        (LinearMap.transvection (LinearMap.snd R (N →+ R) R) ((Int.castAddHom R).comp m, 0)) := by
  ext x
  rw [PointedCone.mem_comap, mem_gradedDivisorCone_add_characterDivisor]

/-- The degree-preserving transvection `(u, j) ↦ (u - j m, j)`, the inverse of the one in
`TauCeti.Toric.Fan.gradedDivisorCone_add_characterDivisor`, carries the graded cone of `D` onto
that of `D + div χ ^ m`. -/
theorem map_transvection_gradedDivisorCone (a : Phi.Ray → ℤ) (m : N →+ ℤ) :
    (Phi.gradedDivisorCone R a).map
        (LinearMap.transvection (LinearMap.snd R (N →+ R) R) (-(Int.castAddHom R).comp m, 0)) =
      Phi.gradedDivisorCone R (a + Phi.characterDivisor m) := by
  have h : LinearMap.snd R (N →+ R) R (-(Int.castAddHom R).comp m, 0) = 0 := by simp
  rw [gradedDivisorCone_add_characterDivisor, ← LinearEquiv.transvection.coe_toLinearMap h]
  refine (Submodule.map_equiv_eq_comap_symm
    ((LinearEquiv.transvection h).restrictScalars (Nonneg R)) _).trans
    (congrArg (Submodule.comap · _) (LinearMap.ext fun x ↦ ?_))
  simp [LinearEquiv.transvection.symm_eq h (by simp)]

end OrderedRing

/-! ### Degree zero on a complete fan -/

section Complete

variable {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- For a complete fan, the only point of degree `0` of the graded cone of a divisor is the origin.
-/
theorem IsComplete.mk_zero_mem_gradedDivisorCone_iff (hPhi : Phi.IsComplete)
    {a : Phi.Ray → ℤ} {u : N →+ R} : (u, 0) ∈ Phi.gradedDivisorCone R a ↔ u = 0 := by
  refine ⟨fun hu ↦ hPhi.eq_zero_of_forall_ray_nonneg fun rho ↦ by
    simpa using mem_gradedDivisorCone.1 hu rho, ?_⟩
  rintro rfl
  exact (Phi.gradedDivisorCone R a).zero_mem

/-- For a complete fan, the graded cone of the zero divisor is `{0} × R`: every degree occurs, but
only with the trivial character. -/
theorem IsComplete.mem_gradedDivisorCone_zero_iff (hPhi : Phi.IsComplete) {x : (N →+ R) × R} :
    x ∈ Phi.gradedDivisorCone R 0 ↔ x.1 = 0 := by
  refine ⟨fun hx ↦ hPhi.eq_zero_of_forall_ray_nonneg fun rho ↦ by
    simpa using mem_gradedDivisorCone.1 hx rho, fun hx ↦ mem_gradedDivisorCone.2 fun rho ↦ ?_⟩
  simp [hx]

end Complete

end TauCeti.Toric.Fan
