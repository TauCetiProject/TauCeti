/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.Germ.MvPolynomial
import TauCeti.Order.Filter.Germ.RingHom
public import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Real polynomial relations for complex-valued germs

If a complex-valued function of real coordinates satisfies a nonzero polynomial relation
with complex polynomial coefficients, its real and imaginary parts each satisfy a nonzero
relation with real polynomial coefficients. No regularity or nonsingularity is required.
The coefficient extension from real to complex polynomials is integral; algebraicity
therefore descends, and conjugation preserves algebraicity over the real coordinates.
-/

public section

open Filter Polynomial

namespace Polynomial

section Helpers

variable {σ : Type*} {l : Filter (σ → ℝ)}

/-- A polynomial relation satisfied eventually along `l` holds for the germ of `f`, with the
coefficients `MvPolynomial σ ℂ` acting as germs of their evaluations at the coordinates. -/
private theorem eval₂_coeRingHom_eq_zero (P : (MvPolynomial σ ℂ)[X]) {f : (σ → ℝ) → ℂ}
    (hrel : ∀ᶠ y in l, (P.map (MvPolynomial.eval fun i ↦ (y i : ℂ))).eval (f y) = 0) :
    P.eval₂ ((Germ.coeRingHom l).comp
      (RingHom.pi fun y : σ → ℝ ↦ MvPolynomial.eval fun i ↦ (y i : ℂ))) (f : Germ l ℂ) = 0 := by
  have hu (y : σ → ℝ) : (Pi.evalRingHom (fun _ : σ → ℝ ↦ ℂ) y).comp
      (RingHom.pi fun y : σ → ℝ ↦ MvPolynomial.eval fun i ↦ (y i : ℂ)) =
      MvPolynomial.eval (fun i ↦ (y i : ℂ)) := by
    ext <;> rfl
  rw [Germ.eval₂_coeRingHom_comp_coe, ← Germ.coe_zero, Germ.coe_eq]
  simp only [hu]
  exact hrel

end Helpers

end Polynomial

namespace Filter.Germ

/-- The real and imaginary parts of a complex germ are algebraic over `R` once the germ, its
conjugate and all constant germs are: `re f = (f + conj f) / 2` and `im f = (f - conj f) / (2 i)`
are built from them by sums and products. -/
theorem isAlgebraic_re_im {α : Type*} {l : Filter α} {R : Type*} [CommRing R] [NoZeroDivisors R]
    [Algebra R (Germ l ℂ)] {f : α → ℂ} (hf : IsAlgebraic R (f : Germ l ℂ))
    (hconj : IsAlgebraic R ((fun y ↦ star (f y) : α → ℂ) : Germ l ℂ))
    (hc : ∀ z : ℂ, IsAlgebraic R ((fun _ : α ↦ z : α → ℂ) : Germ l ℂ)) :
    IsAlgebraic R ((fun y ↦ (((f y).re : ℝ) : ℂ) : α → ℂ) : Germ l ℂ) ∧
      IsAlgebraic R ((fun y ↦ (((f y).im : ℝ) : ℂ) : α → ℂ) : Germ l ℂ) := by
  constructor
  · convert (hf.add hconj).mul (hc (1 / 2)) using 1
    rw [← Germ.coe_add f (fun y ↦ star (f y)), ← Germ.coe_mul]
    congr 1
    funext y
    rw [Complex.re_eq_add_conj]
    simp [div_eq_mul_inv]
  · convert (hf.sub hconj).mul (hc (-(Complex.I / 2))) using 1
    rw [← Germ.coe_sub f (fun y ↦ star (f y)), ← Germ.coe_mul]
    congr 1
    funext y
    rw [Complex.im_eq_sub_conj]
    simp
    field_simp
    rw [Complex.I_sq]
    ring

end Filter.Germ

namespace Polynomial

/-- The real and imaginary parts of a complex-valued germ algebraic over the coordinate
polynomials have real polynomial relations, including at singular points of the relation. -/
theorem exists_real_polynomial_relations {σ : Type*} {l : Filter (σ → ℝ)}
    (P : (MvPolynomial σ ℂ)[X]) (hP : P ≠ 0) {f : (σ → ℝ) → ℂ}
    (hrel : ∀ᶠ y in l, (P.map (MvPolynomial.eval fun i ↦ (y i : ℂ))).eval (f y) = 0) :
    (∃ Q : (MvPolynomial σ ℝ)[X], Q ≠ 0 ∧
      ∀ᶠ y in l, (Q.map (MvPolynomial.eval y)).eval (f y).re = 0) ∧
    (∃ Q : (MvPolynomial σ ℝ)[X], Q ≠ 0 ∧
      ∀ᶠ y in l, (Q.map (MvPolynomial.eval y)).eval (f y).im = 0) := by
  -- Keep the two coefficient actions local: real coordinate polynomials act through
  -- their complex coefficients, and the latter extension is integral.
  let R := MvPolynomial σ ℝ
  let S := MvPolynomial σ ℂ
  let B := Germ l ℂ
  let s : S →+* B := (Germ.coeRingHom l).comp
    (RingHom.pi fun y : σ → ℝ ↦ MvPolynomial.eval fun i ↦ (y i : ℂ))
  let : Algebra R S := MvPolynomial.algebraMvPolynomial
  let : Algebra S B := s.toAlgebra
  let : Algebra R B := (s.comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra.IsIntegral R S := ⟨fun p ↦
    MvPolynomial.isIntegral_iff_isIntegral_coeff.mpr fun _ ↦
      Algebra.IsIntegral.isIntegral _⟩
  have hs (p : S) : s p =
      ((fun y : σ → ℝ ↦ MvPolynomial.eval (fun i ↦ (y i : ℂ)) p) : B) := by
    simp only [s, RingHom.comp_apply, Germ.coe_coeRingHom]
    congr 1
  have hB (p : R) :
      algebraMap R B p = ((fun y : σ → ℝ ↦ (MvPolynomial.eval y p : ℂ)) : B) := by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hs]
    congr 1
    funext y
    rw [MvPolynomial.algebraMap_def]
    exact (MvPolynomial.map_eval (algebraMap ℝ ℂ) y p).symm
  -- Read the given relation as algebraicity, then descend the coefficient field.
  have halg : IsAlgebraic S (f : B) := by
    refine ⟨P, hP, ?_⟩
    rw [aeval_def, RingHom.algebraMap_toAlgebra]
    exact eval₂_coeRingHom_eq_zero P hrel
  have halgR : IsAlgebraic R (f : B) := halg.restrictScalars_of_isIntegral R
  let : Algebra R (Germ l ℝ) := Germ.mvPolynomialAlgebra l
  -- The real inclusion and conjugation act on germs over the real coordinate polynomials.
  let g : Germ l ℝ →ₐ[R] B := (algebraMap ℝ ℂ).mapGermAlgHom l fun p ↦ by
    rw [Germ.mvPolynomialAlgebra_algebraMap_apply, hB, RingHom.mapGerm_coe,
      Complex.coe_algebraMap, Function.comp_def]
  -- `show` unfolds the local `g`, so that `RingHom.coe_mapGermAlgHom` applies.
  have hg_apply (u : (σ → ℝ) → ℝ) : g (u : Germ l ℝ) = ((fun y ↦ (u y : ℂ) : (σ → ℝ) → ℂ) : B) := by
    rw [show ⇑g = (algebraMap ℝ ℂ).mapGerm l from RingHom.coe_mapGermAlgHom _ _ _,
      RingHom.mapGerm_coe, Function.comp_def]
    simp only [Complex.coe_algebraMap]
  have hg : Function.Injective g := by
    -- The `show` turns the opaque local `g` into its definition, so that
    -- `RingHom.coe_mapGermAlgHom` identifies `⇑g` with `(algebraMap ℝ ℂ).mapGerm l`.
    rw [show ⇑g = (algebraMap ℝ ℂ).mapGerm l from RingHom.coe_mapGermAlgHom _ _ _]
    exact (algebraMap ℝ ℂ).mapGerm_injective l Complex.ofReal_injective
  let j : B →ₐ[R] B := (starRingEnd ℂ).mapGermAlgHom l fun p ↦ by
    rw [hB, RingHom.mapGerm_coe, Function.comp_def]
    simp only [Complex.conj_ofReal]
  -- `show` unfolds the local `j`, so that `RingHom.coe_mapGermAlgHom` applies.
  have hj_apply (u : (σ → ℝ) → ℂ) : j (u : B) = ((fun y ↦ star (u y) : (σ → ℝ) → ℂ) : B) := by
    rw [show ⇑j = (starRingEnd ℂ).mapGerm l from RingHom.coe_mapGermAlgHom _ _ _,
      RingHom.mapGerm_coe, Function.comp_def]
    simp only [starRingEnd_apply]
  have hc (z : ℂ) : IsAlgebraic R ((fun _ : σ → ℝ ↦ z) : B) := by
    have hz' : IsIntegral R (MvPolynomial.C z : S) := Algebra.IsIntegral.isIntegral _
    convert hz'.isAlgebraic.algHom (IsScalarTower.toAlgHom R S B) using 1
    simp only [IsScalarTower.toAlgHom_apply, RingHom.algebraMap_toAlgebra, hs,
      MvPolynomial.eval_C]
  -- Recover the two components from f and its conjugate, then reflect along the real inclusion.
  have hconj : IsAlgebraic R ((fun y ↦ star (f y) : (σ → ℝ) → ℂ) : B) := by
    simpa only [hj_apply] using halgR.algHom j
  obtain ⟨hre, him⟩ := Germ.isAlgebraic_re_im halgR hconj hc
  exact ⟨Germ.isAlgebraic_coe_iff.mp ((isAlgebraic_algHom_iff g hg).mp
      (by rw [hg_apply]; exact hre)),
    Germ.isAlgebraic_coe_iff.mp ((isAlgebraic_algHom_iff g hg).mp
      (by rw [hg_apply]; exact him))⟩

end Polynomial
