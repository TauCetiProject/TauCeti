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
  let c : ℂ →+* B := (Germ.coeRingHom l).comp (Pi.constRingHom (σ → ℝ) ℂ)
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
  have hRS : algebraMap R S = MvPolynomial.map (algebraMap ℝ ℂ) :=
    MvPolynomial.algebraMap_def
  have hevalreal (p : R) (y : σ → ℝ) :
      MvPolynomial.eval (fun i ↦ (y i : ℂ)) (algebraMap R S p) =
        (MvPolynomial.eval y p : ℂ) := by
    rw [hRS]
    exact (MvPolynomial.map_eval (algebraMap ℝ ℂ) y p).symm
  have hr (p : R) : algebraMap R B p = s (algebraMap R S p) := (rfl)
  -- Read the given relation as algebraicity, then descend the coefficient field.
  have halg : IsAlgebraic S (f : B) := by
    refine ⟨P, hP, ?_⟩
    rw [aeval_def, RingHom.algebraMap_toAlgebra]
    let u : S →+* ((σ → ℝ) → ℂ) :=
      RingHom.pi fun y ↦ MvPolynomial.eval fun i ↦ (y i : ℂ)
    have heval : P.eval₂ u f =
        (fun y ↦ (P.map (MvPolynomial.eval fun i ↦ (y i : ℂ))).eval (f y)) := by
      funext y
      have hu : (Pi.evalRingHom (fun _ : σ → ℝ ↦ ℂ) y).comp u =
          MvPolynomial.eval (fun i ↦ (y i : ℂ)) := by
        ext <;> rfl
      simpa only [hu, eval_map, Pi.evalRingHom_apply] using
        (hom_eval₂ P u (Pi.evalRingHom (fun _ : σ → ℝ ↦ ℂ) y) f)
    calc
      P.eval₂ s (f : B) = Germ.coeRingHom l (P.eval₂ u f) :=
        (hom_eval₂ P u (Germ.coeRingHom l) f).symm
      _ = 0 := by
        rw [heval, Germ.coe_coeRingHom, ← Germ.coe_zero, Germ.coe_eq]
        exact hrel
  have halgR : IsAlgebraic R (f : B) := halg.restrictScalars_of_isIntegral R
  let : Algebra R (Germ l ℝ) := Germ.mvPolynomialAlgebra l
  -- Real inclusion is injective, while conjugation fixes the real polynomial action.
  let g : Germ l ℝ →ₐ[R] B :=
    { (algebraMap ℝ ℂ).mapGerm l with
      commutes' := by
        intro p
        -- Present the inherited ring-homomorphism field explicitly.
        change (algebraMap ℝ ℂ).mapGerm l (algebraMap R (Germ l ℝ) p) = _
        rw [Germ.mvPolynomialAlgebra_algebraMap_apply, RingHom.mapGerm_coe, hr, hs]
        congr 1
        funext y
        rw [hRS]
        exact MvPolynomial.map_eval (algebraMap ℝ ℂ) y p }
  have hg : Function.Injective g := (algebraMap ℝ ℂ).mapGerm_injective l
    Complex.ofReal_injective
  let j : B →ₐ[R] B :=
    { (starRingEnd ℂ).mapGerm l with
      commutes' := by
        intro p
        -- Present the inherited ring-homomorphism field explicitly.
        change (starRingEnd ℂ).mapGerm l (algebraMap R B p) = _
        rw [hr, hs, RingHom.mapGerm_coe]
        congr 1
        funext y
        dsimp only [Function.comp_apply]
        rw [hevalreal p y]
        exact Complex.conj_ofReal _ }
  have hconj : IsAlgebraic R (j (f : B)) := halgR.algHom j
  have hc (z : ℂ) : IsAlgebraic R (c z) := by
    have hz' : IsIntegral R (MvPolynomial.C z : S) := Algebra.IsIntegral.isIntegral _
    convert hz'.isAlgebraic.algHom (IsScalarTower.toAlgHom R S B) using 1
    simp only [IsScalarTower.toAlgHom_apply, RingHom.algebraMap_toAlgebra, hs,
      MvPolynomial.eval_C]
    rfl
  have hg_apply (u : (σ → ℝ) → ℝ) : g (u : Germ l ℝ) =
      ((fun y ↦ (u y : ℂ)) : B) := RingHom.mapGerm_coe _ _ _
  have hj_apply (u : (σ → ℝ) → ℂ) : j (u : B) =
      ((fun y ↦ star (u y)) : B) := RingHom.mapGerm_coe _ _ _
  have hc_apply (z : ℂ) : c z = ((fun _ : σ → ℝ ↦ z) : B) := (rfl)
  -- Algebraicity is closed under sums and products; recover the two components
  -- from f and its conjugate, then reflect along the real inclusion.
  have hreal : IsAlgebraic R (g ((fun y ↦ (f y).re) : Germ l ℝ)) := by
    convert (halgR.add hconj).mul (hc (1 / 2)) using 1
    rw [hg_apply, hj_apply, hc_apply]
    rw [← Germ.coe_add f (fun y ↦ star (f y)), ← Germ.coe_mul]
    congr 1
    funext y
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  have himag : IsAlgebraic R (g ((fun y ↦ (f y).im) : Germ l ℝ)) := by
    convert (halgR.sub hconj).mul (hc (-(Complex.I / 2))) using 1
    rw [hg_apply, hj_apply, hc_apply]
    rw [← Germ.coe_sub f (fun y ↦ star (f y)), ← Germ.coe_mul]
    congr 1
    funext y
    simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im]
    ring
  exact ⟨Germ.isAlgebraic_coe_iff.mp ((isAlgebraic_algHom_iff g hg).mp hreal),
    Germ.isAlgebraic_coe_iff.mp ((isAlgebraic_algHom_iff g hg).mp himag)⟩

end Polynomial
