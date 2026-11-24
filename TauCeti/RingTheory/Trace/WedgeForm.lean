/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Trace.Basic

/-!
# The trace symplectic forms on `S²`

For an algebra `S` over a commutative ring `R` and a parameter `a : S`, the trace symplectic form
on row vectors `x = (x₀, x₁)` and `y = (y₀, y₁)` of `S²` is

```text
ψ_a(x, y) = Tr_{S/R}(a (x₀ y₁ - x₁ y₀)) = Tr_{S/R}(a · det [x; y]).
```

For a totally real field `S = F` and `R = ℚ` these are the rational alternating forms of the
Hilbert modular Shimura datum: `ψ₁` is the trace form of the rational representation of
`Res_{F/ℚ} GL₂` on `F²`, and the family `a ↦ ψ_a` restricted to the polarization lattices
`𝓞_F ⊕ c⁻¹𝔡⁻¹` gives the integral polarization forms of Hilbert–Blumenthal abelian varieties
(`TauCeti.HilbertModular.integralTraceWedgeForm`).

The family is `R`-linear in `a` (`traceWedgeForm` is bundled as a linear map), each `ψ_a` is
alternating, the parameter can be moved into either argument (`traceWedgeForm_mul_smul_left`,
`traceWedgeForm_mul_smul_right`), and a matrix `γ` acting on rows multiplies the parameter by
`det γ` (`traceWedgeForm_vecMul_vecMul`). For a finite separable field extension, `ψ_a` is
nondegenerate exactly when `a ≠ 0` (`nondegenerate_traceWedgeForm_iff`).

## Main definitions

* `TauCeti.traceWedgeForm R`: the `R`-linear family `a ↦ ψ_a` of `R`-bilinear forms on `S²`.

## Main statements

* `TauCeti.traceWedgeForm_apply_eq_det`: `ψ_a(x, y) = Tr(a · det [x; y])`.
* `TauCeti.isAlt_traceWedgeForm`: each `ψ_a` is alternating.
* `TauCeti.traceWedgeForm_vecMul_vecMul`: `ψ_a(x γ, y γ) = ψ_{a det γ}(x, y)`.
* `TauCeti.nondegenerate_traceWedgeForm_iff`: for a finite separable field extension `L / K`,
  `ψ_a` is nondegenerate if and only if `a ≠ 0`.

## References

* C. Birkbeck, B. Heuer and C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, Ann. Inst. Fourier 73 (2023), Notation 5.1.
* M. Rapoport, *Compactifications de l'espace de modules de Hilbert–Blumenthal*, Compositio
  Math. 36 (1978), §1.
-/

public section

open Module Matrix

namespace TauCeti

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The trace symplectic forms on row vectors of `S²`: the parameter `a : S` gives the
`R`-bilinear form `ψ_a(x, y) = Tr_{S/R}(a (x₀ y₁ - x₁ y₀))`, and `a ↦ ψ_a` is `R`-linear. -/
noncomputable def traceWedgeForm : S →ₗ[R] LinearMap.BilinForm R (Fin 2 → S) where
  toFun a := LinearMap.mk₂ R (fun x y ↦ Algebra.trace R S (a * (x 0 * y 1 - x 1 * y 0)))
    (fun x x' y ↦ by rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring)
    (fun r x y ↦ by
      rw [← map_smul]; congr 1; simp only [Pi.smul_apply, Algebra.smul_def]; ring)
    (fun x y y' ↦ by rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring)
    (fun r x y ↦ by
      rw [← map_smul]; congr 1; simp only [Pi.smul_apply, Algebra.smul_def]; ring)
  map_add' a b := LinearMap.ext₂ fun x y ↦ by
    simp only [LinearMap.mk₂_apply, LinearMap.add_apply, ← map_add, add_mul]
  map_smul' r a := LinearMap.ext₂ fun x y ↦ by
    simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [← map_smul, smul_mul_assoc]

variable {R}

theorem traceWedgeForm_apply (a : S) (x y : Fin 2 → S) :
    traceWedgeForm R a x y = Algebra.trace R S (a * (x 0 * y 1 - x 1 * y 0)) :=
  (rfl)

/-- The trace symplectic form is the trace of `a` times the determinant of the matrix with rows
`x` and `y`. -/
theorem traceWedgeForm_apply_eq_det (a : S) (x y : Fin 2 → S) :
    traceWedgeForm R a x y = Algebra.trace R S (a * (Matrix.of ![x, y]).det) := by
  simp [traceWedgeForm_apply, Matrix.det_fin_two]

/-- The value of `ψ_a` on the two standard basis vectors is `Tr(a)`. -/
theorem traceWedgeForm_single_zero_single_one (a : S) :
    traceWedgeForm R a (Pi.single 0 1) (Pi.single 1 1) = Algebra.trace R S a := by
  simp [traceWedgeForm_apply]

@[simp]
theorem traceWedgeForm_self (a : S) (x : Fin 2 → S) : traceWedgeForm R a x x = 0 := by
  simp [traceWedgeForm_apply, mul_comm (x 0)]

theorem isAlt_traceWedgeForm (a : S) : (traceWedgeForm R a).IsAlt :=
  traceWedgeForm_self a

theorem traceWedgeForm_swap (a : S) (x y : Fin 2 → S) :
    traceWedgeForm R a y x = -traceWedgeForm R a x y := by
  simp only [traceWedgeForm_apply, ← map_neg]
  congr 1
  ring

/-- The parameter of `ψ` can be moved into the first argument: `ψ_{b a}(x, y) = ψ_a(b x, y)`. -/
theorem traceWedgeForm_mul_smul_left (a b : S) (x y : Fin 2 → S) :
    traceWedgeForm R (b * a) x y = traceWedgeForm R a (b • x) y := by
  simp only [traceWedgeForm_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  ring

/-- The parameter of `ψ` can be moved into the second argument: `ψ_{b a}(x, y) = ψ_a(x, b y)`. -/
theorem traceWedgeForm_mul_smul_right (a b : S) (x y : Fin 2 → S) :
    traceWedgeForm R (b * a) x y = traceWedgeForm R a x (b • y) := by
  simp only [traceWedgeForm_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  ring

/-- A matrix acting on row vectors multiplies the parameter of `ψ` by its determinant:
`ψ_a(x γ, y γ) = ψ_{a det γ}(x, y)`. -/
theorem traceWedgeForm_vecMul_vecMul (a : S) (γ : Matrix (Fin 2) (Fin 2) S) (x y : Fin 2 → S) :
    traceWedgeForm R a (x ᵥ* γ) (y ᵥ* γ) = traceWedgeForm R (a * γ.det) x y := by
  have h : Matrix.of ![x ᵥ* γ, y ᵥ* γ] = Matrix.of ![x, y] * γ := by
    simp [Matrix.cons_mul]
  rw [traceWedgeForm_apply_eq_det, traceWedgeForm_apply_eq_det, h, Matrix.det_mul, mul_comm _ γ.det,
    mul_assoc]

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- For a finite separable extension `L / K`, the trace symplectic form `ψ_a` is nondegenerate
exactly when its parameter `a` is nonzero. -/
theorem nondegenerate_traceWedgeForm_iff [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {a : L} : (traceWedgeForm K a).Nondegenerate ↔ a ≠ 0 := by
  refine ⟨fun h ha ↦ ?_, fun ha ↦ ?_⟩
  · rw [ha, map_zero] at h
    exact LinearMap.BilinForm.not_nondegenerate_zero K (Fin 2 → L) h
  -- A vector orthogonal to every vector has both coordinates zero, by testing against the
  -- vectors `(0, t)` and `(-t, 0)` and using the nondegeneracy of the trace form.
  have hleft : (traceWedgeForm K a).SeparatingLeft := by
    intro x hx
    have h₀ : a * x 0 = 0 := (traceForm_nondegenerate K L).1 _ fun t ↦ by
      simpa [traceWedgeForm_apply, mul_assoc] using hx ![0, t]
    have h₁ : a * x 1 = 0 := (traceForm_nondegenerate K L).1 _ fun t ↦ by
      simpa [traceWedgeForm_apply, mul_assoc] using hx ![-t, 0]
    ext i
    fin_cases i
    · exact (mul_eq_zero.1 h₀).resolve_left ha
    · exact (mul_eq_zero.1 h₁).resolve_left ha
  refine ⟨hleft, fun y hy ↦ hleft y fun x ↦ ?_⟩
  rw [traceWedgeForm_swap, hy, neg_zero]

end TauCeti
