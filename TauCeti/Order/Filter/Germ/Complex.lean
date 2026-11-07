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

/-- Real germs embed into complex germs as an injective algebra map over the coordinate
polynomials. -/
private theorem exists_injective_algHom_germ_ofReal
    [Algebra (MvPolynomial σ ℝ) (Germ l ℝ)] [Algebra (MvPolynomial σ ℝ) (Germ l ℂ)]
    (hA : ∀ p : MvPolynomial σ ℝ, algebraMap _ (Germ l ℝ) p =
      ((fun y ↦ MvPolynomial.eval y p : (σ → ℝ) → ℝ) : Germ l ℝ))
    (hB : ∀ p : MvPolynomial σ ℝ, algebraMap _ (Germ l ℂ) p =
      ((fun y ↦ (MvPolynomial.eval y p : ℂ) : (σ → ℝ) → ℂ) : Germ l ℂ)) :
    ∃ g : Germ l ℝ →ₐ[MvPolynomial σ ℝ] Germ l ℂ, Function.Injective g ∧
      ∀ u : (σ → ℝ) → ℝ, g (u : Germ l ℝ) = ((fun y ↦ (u y : ℂ) : (σ → ℝ) → ℂ) : Germ l ℂ) := by
  obtain ⟨g, hg⟩ := RingHom.exists_algHom_mapGerm (A := MvPolynomial σ ℝ) (algebraMap ℝ ℂ)
    (l := l) fun p ↦ by
      rw [hA, hB, RingHom.mapGerm_coe]
      rfl
  exact ⟨g, fun a b hab ↦ (algebraMap ℝ ℂ).mapGerm_injective l Complex.ofReal_injective
      (by rwa [hg, hg] at hab), fun u ↦ by rw [hg]; exact RingHom.mapGerm_coe _ _ _⟩

/-- Complex conjugation of germs is an algebra automorphism over the real coordinate
polynomials. -/
private theorem exists_algHom_germ_star [Algebra (MvPolynomial σ ℝ) (Germ l ℂ)]
    (hB : ∀ p : MvPolynomial σ ℝ, algebraMap _ (Germ l ℂ) p =
      ((fun y ↦ (MvPolynomial.eval y p : ℂ) : (σ → ℝ) → ℂ) : Germ l ℂ)) :
    ∃ j : Germ l ℂ →ₐ[MvPolynomial σ ℝ] Germ l ℂ,
      ∀ u : (σ → ℝ) → ℂ,
        j (u : Germ l ℂ) = ((fun y ↦ star (u y) : (σ → ℝ) → ℂ) : Germ l ℂ) := by
  obtain ⟨j, hj⟩ := RingHom.exists_algHom_mapGerm (A := MvPolynomial σ ℝ) (starRingEnd ℂ)
    (l := l) fun p ↦ by
      rw [hB, RingHom.mapGerm_coe]
      congr 1
      funext y
      exact Complex.conj_ofReal _
  exact ⟨j, fun u ↦ by rw [hj]; exact RingHom.mapGerm_coe _ _ _⟩

/-- The real and imaginary parts of a complex germ are algebraic over `R` once the germ, its
conjugate and all constant germs are: `re f = (f + conj f) / 2` and `im f = (f - conj f) / (2 i)`
are built from them by sums and products. -/
theorem isAlgebraic_re_im_germ {R : Type*} [CommRing R] [NoZeroDivisors R]
    [Algebra R (Germ l ℂ)] {f : (σ → ℝ) → ℂ} (hf : IsAlgebraic R (f : Germ l ℂ))
    (hconj : IsAlgebraic R ((fun y ↦ star (f y) : (σ → ℝ) → ℂ) : Germ l ℂ))
    (hc : ∀ z : ℂ, IsAlgebraic R ((fun _ : σ → ℝ ↦ z : (σ → ℝ) → ℂ) : Germ l ℂ)) :
    IsAlgebraic R ((fun y ↦ (((f y).re : ℝ) : ℂ) : (σ → ℝ) → ℂ) : Germ l ℂ) ∧
      IsAlgebraic R ((fun y ↦ (((f y).im : ℝ) : ℂ) : (σ → ℝ) → ℂ) : Germ l ℂ) := by
  constructor
  · convert (hf.add hconj).mul (hc (1 / 2)) using 1
    rw [← Germ.coe_add f (fun y ↦ star (f y)), ← Germ.coe_mul]
    congr 1
    funext y
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  · convert (hf.sub hconj).mul (hc (-(Complex.I / 2))) using 1
    rw [← Germ.coe_sub f (fun y ↦ star (f y)), ← Germ.coe_mul]
    congr 1
    funext y
    simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im]
    ring

end Helpers

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
  obtain ⟨g, hg, hg_apply⟩ := exists_injective_algHom_germ_ofReal
    (Germ.mvPolynomialAlgebra_algebraMap_apply l) hB
  obtain ⟨j, hj_apply⟩ := exists_algHom_germ_star hB
  have hc (z : ℂ) : IsAlgebraic R ((fun _ : σ → ℝ ↦ z) : B) := by
    have hz' : IsIntegral R (MvPolynomial.C z : S) := Algebra.IsIntegral.isIntegral _
    convert hz'.isAlgebraic.algHom (IsScalarTower.toAlgHom R S B) using 1
    simp only [IsScalarTower.toAlgHom_apply, RingHom.algebraMap_toAlgebra, hs,
      MvPolynomial.eval_C]
  -- Recover the two components from f and its conjugate, then reflect along the real inclusion.
  obtain ⟨hre, him⟩ := isAlgebraic_re_im_germ halgR (hj_apply f ▸ halgR.algHom j) hc
  exact ⟨Germ.isAlgebraic_coe_iff.mp ((isAlgebraic_algHom_iff g hg).mp
      (by rwa [hg_apply])),
    Germ.isAlgebraic_coe_iff.mp ((isAlgebraic_algHom_iff g hg).mp (by rwa [hg_apply]))⟩

end Polynomial
