/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.NormForm
-- `Mathlib.LinearAlgebra.Trace` is imported publicly for `LinearMap.trace`, which occurs in the
-- statement of `QuaternionAlgebra.trace_mulLeft`.
public import Mathlib.LinearAlgebra.Trace

/-!
# Algebra equivalences of quaternion algebras

An algebra equivalence between two quaternion algebras is compatible with all of their
quadratic-form structure: it commutes with quaternion conjugation, preserves the reduced trace
and the reduced norm, maps the pure quaternions onto the pure quaternions, and therefore restricts
to an isometry of pure norm forms. In the classical presentation `ℍ[R,a,b]`, this turns an
isomorphism `ℍ[R,a,b] ≃ₐ[R] ℍ[R,c,d]` into an isometry of ternary diagonal forms
`⟨-a, -b, ab⟩ ≅ ⟨-c, -d, cd⟩`. It is the step that lets an equality of quaternion algebras up to
isomorphism be read back as an isometry of quadratic forms, as in the classification of forms of
dimension three by their determinant and their quaternion algebra.

The one input is intrinsic: the trace of left multiplication by `x` on the free module
`ℍ[R,c₁,c₂,c₃]` is twice the reduced trace `x + star x = 2 x.re + c₂ x.imI`
(`QuaternionAlgebra.trace_mulLeft`). An algebra equivalence conjugates left multiplication by `x`
into left multiplication by its image, so it preserves this trace; once `2` is cancellable it
preserves the reduced trace, and `star x = (x + star x) - x` is then preserved as well. Everything
else follows formally from `QuaternionAlgebra.self_mul_star`.

## Main results

* `QuaternionAlgebra.trace_mulLeft`: the trace of left multiplication by a quaternion.
* `QuaternionAlgebra.map_star_of_algEquiv`: an algebra equivalence of quaternion algebras commutes
  with conjugation, so that `StarAlgEquiv.ofAlgEquiv` makes it a `⋆`-algebra equivalence.
* `QuaternionAlgebra.normForm_eq_of_algEquiv`: it preserves the reduced norm, and
  `QuaternionAlgebra.normFormIsometryEquivOfAlgEquiv` is the resulting isometry of norm forms.
* `QuaternionAlgebra.re_eq_of_algEquiv` and `QuaternionAlgebra.map_ker_reₗ_of_algEquiv`: between
  algebras `ℍ[R,a,b]` it preserves real parts and maps the pure quaternions onto the pure
  quaternions.
* `QuaternionAlgebra.pureNormFormIsometryEquivOfAlgEquiv`: the restricted isometry of pure norm
  forms, and `QuaternionAlgebra.equivalent_weightedSumSquares_of_algEquiv`: isomorphic quaternion
  algebras `ℍ[R,a,b]` and `ℍ[R,c,d]` have isometric forms `⟨-a, -b, ab⟩` and `⟨-c, -d, cd⟩`.

## Implementation notes

Everything is stated over a commutative ring in which `2` is left regular, which is exactly what
the proof consumes; over a field this is the standing hypothesis that `2` is invertible. Some such
hypothesis is needed for the argument: when `2 = 0` and `c₂ = 0` the trace of left multiplication
vanishes identically, so it carries no information about conjugation.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, §2.
* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §1.1.
-/

public section

open QuadraticMap

open scoped Quaternion

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R]

section General

variable {c₁ c₂ c₃ d₁ d₂ d₃ : R}

/-- The trace of left multiplication by a quaternion `x` is twice its reduced trace
`x + star x = 2 x.re + c₂ x.imI`. -/
theorem trace_mulLeft (x : ℍ[R,c₁,c₂,c₃]) :
    LinearMap.trace R _ (LinearMap.mulLeft R x) = 2 * (2 * x.re + c₂ * x.imI) := by
  rw [LinearMap.trace_eq_matrix_trace R (basisOneIJK c₁ c₂ c₃), Matrix.trace, Fin.sum_univ_four]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, coe_basisOneIJK_repr]
  simp [basisOneIJK, Module.Basis.ofEquivFun]
  ring

/-- An algebra equivalence of quaternion algebras preserves the reduced trace, in coordinates. -/
private theorem two_mul_re_add_mul_imI_of_algEquiv (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,d₁,d₂,d₃]) (x : ℍ[R,c₁,c₂,c₃]) :
    2 * (f x).re + d₂ * (f x).imI = 2 * x.re + c₂ * x.imI := by
  refine h2 ?_
  have hconj : f.toLinearEquiv.conj (LinearMap.mulLeft R x) = LinearMap.mulLeft R (f x) :=
    LinearMap.ext fun y => by simp
  simp only [← trace_mulLeft, ← hconj, LinearMap.trace_conj']

/-- **An algebra equivalence of quaternion algebras commutes with conjugation**, once `2` is left
regular. Together with `StarAlgEquiv.ofAlgEquiv` this makes every such equivalence a
`⋆`-algebra equivalence. -/
theorem map_star_of_algEquiv (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,d₁,d₂,d₃]) (x : ℍ[R,c₁,c₂,c₃]) :
    f (star x) = star (f x) := by
  rw [star_eq_two_re_sub, star_eq_two_re_sub, two_mul_re_add_mul_imI_of_algEquiv h2, map_sub,
    ← coe_algebraMap, ← coe_algebraMap, AlgEquiv.commutes]

/-- **An algebra equivalence of quaternion algebras preserves the reduced norm.** -/
@[simp]
theorem normForm_eq_of_algEquiv (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,d₁,d₂,d₃]) (x : ℍ[R,c₁,c₂,c₃]) :
    normForm d₁ d₂ d₃ (f x) = normForm c₁ c₂ c₃ x := by
  refine coe_injective (c₁ := d₁) (c₂ := d₂) (c₃ := d₃) ?_
  calc ((normForm d₁ d₂ d₃ (f x) : R) : ℍ[R,d₁,d₂,d₃])
      _ = f (x * star x) := by rw [map_mul, map_star_of_algEquiv h2, self_mul_star]
      _ = normForm c₁ c₂ c₃ x := by
        rw [self_mul_star, ← coe_algebraMap, AlgEquiv.commutes, coe_algebraMap]

/-- An algebra equivalence of quaternion algebras, viewed as an isometry of their norm forms. -/
def normFormIsometryEquivOfAlgEquiv (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,d₁,d₂,d₃]) :
    (normForm c₁ c₂ c₃).IsometryEquiv (normForm d₁ d₂ d₃) where
  __ := f.toLinearEquiv
  map_app' := normForm_eq_of_algEquiv h2 f

@[simp]
theorem normFormIsometryEquivOfAlgEquiv_apply (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,c₁,c₂,c₃] ≃ₐ[R] ℍ[R,d₁,d₂,d₃]) (x : ℍ[R,c₁,c₂,c₃]) :
    normFormIsometryEquivOfAlgEquiv h2 f x = f x := (rfl)

end General

section Diagonal

variable {a b c d : R}

/-- **An algebra equivalence between quaternion algebras `ℍ[R,a,b]` preserves real parts.** -/
@[simp]
theorem re_eq_of_algEquiv (h2 : IsLeftRegular (2 : R)) (f : ℍ[R,a,b] ≃ₐ[R] ℍ[R,c,d])
    (x : ℍ[R,a,b]) : (f x).re = x.re := by
  refine h2 ?_
  simpa using two_mul_re_add_mul_imI_of_algEquiv h2 f x

/-- **An algebra equivalence between quaternion algebras `ℍ[R,a,b]` maps the pure quaternions onto
the pure quaternions.** -/
theorem map_ker_reₗ_of_algEquiv (h2 : IsLeftRegular (2 : R)) (f : ℍ[R,a,b] ≃ₐ[R] ℍ[R,c,d]) :
    (LinearMap.ker (reₗ a (0 : R) b)).map (f.toLinearEquiv : ℍ[R,a,b] →ₗ[R] ℍ[R,c,d]) =
      LinearMap.ker (reₗ c (0 : R) d) := by
  ext y
  obtain ⟨x, rfl⟩ := f.surjective y
  simp [Submodule.mem_map_equiv, re_eq_of_algEquiv h2 f]

/-- An algebra equivalence `ℍ[R,a,b] ≃ₐ[R] ℍ[R,c,d]`, restricted to the pure quaternions, as an
isometry of the pure norm forms. -/
def pureNormFormIsometryEquivOfAlgEquiv (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,a,b] ≃ₐ[R] ℍ[R,c,d]) :
    (pureNormForm a b).IsometryEquiv (pureNormForm c d) where
  __ := f.toLinearEquiv.ofSubmodules _ _ (map_ker_reₗ_of_algEquiv h2 f)
  map_app' x := by
    simpa [LinearEquiv.ofSubmodules_apply] using normForm_eq_of_algEquiv h2 f x

@[simp]
theorem coe_pureNormFormIsometryEquivOfAlgEquiv_apply (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,a,b] ≃ₐ[R] ℍ[R,c,d]) (x : LinearMap.ker (reₗ a (0 : R) b)) :
    (pureNormFormIsometryEquivOfAlgEquiv h2 f x : ℍ[R,c,d]) = f x := (rfl)

/-- **Isomorphic quaternion algebras have isometric pure norm forms.** -/
theorem equivalent_pureNormForm_of_algEquiv (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,a,b] ≃ₐ[R] ℍ[R,c,d]) : (pureNormForm a b).Equivalent (pureNormForm c d) :=
  ⟨pureNormFormIsometryEquivOfAlgEquiv h2 f⟩

/-- **Isomorphic quaternion algebras `ℍ[R,a,b]` and `ℍ[R,c,d]` have isometric ternary forms
`⟨-a, -b, ab⟩` and `⟨-c, -d, cd⟩`**, the diagonalizations of their pure norm forms. -/
theorem equivalent_weightedSumSquares_of_algEquiv (h2 : IsLeftRegular (2 : R))
    (f : ℍ[R,a,b] ≃ₐ[R] ℍ[R,c,d]) :
    (weightedSumSquares R ![-a, -b, a * b]).Equivalent (weightedSumSquares R ![-c, -d, c * d]) :=
  ((equivalent_pureNormForm_weightedSumSquares a b).symm.trans
    (equivalent_pureNormForm_of_algEquiv h2 f)).trans
    (equivalent_pureNormForm_weightedSumSquares c d)

end Diagonal

end QuaternionAlgebra

end
