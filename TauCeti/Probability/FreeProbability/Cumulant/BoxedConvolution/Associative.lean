/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import TauCeti.Probability.FreeProbability.Cumulant.BoxedConvolution.Basic
public import TauCeti.Probability.FreeProbability.Cumulant.Realization

/-!
# Associativity of scalar boxed convolution

Realize three normalized series as the cumulants of freely independent algebraic variables.
Grouping the first two or the last two variables computes the two parenthesizations as the
cumulants of the same product. This proves associativity without positivity, traciality, or
invertibility assumptions on the linear coefficients.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 17
  (boxed convolution and its algebraic realization).
-/

public section

open Finset PowerSeries

namespace TauCeti

private theorem boxedConvolution_assoc_of_free {R A : Type*} [CommRing R] [Ring A]
    [Algebra R A] {φ : A →ₗ[R] R} {a : Fin 3 → A}
    (h : IsFreelyIndependentElements φ a) (hφ : φ 1 = 1) :
    ((freeCumulantSeries φ (a 0)).boxedConvolution (freeCumulantSeries φ (a 1))).boxedConvolution
        (freeCumulantSeries φ (a 2)) =
      (freeCumulantSeries φ (a 0)).boxedConvolution
        ((freeCumulantSeries φ (a 1)).boxedConvolution (freeCumulantSeries φ (a 2))) := by
  have hm (i : Fin 3) : a i ∈ Algebra.adjoin R {a i} := Algebra.self_mem_adjoin_singleton R _
  let B (g : Fin 3 → Bool) (b : Bool) := ⨆ (i : Fin 3) (_ : g i = b), Algebra.adjoin R {a i}
  have hB (g : Fin 3 → Bool) : IsFreelyIndependent φ (B g) :=
    (isFreelyIndependentElements_iff.mp h).iSup_fiber hφ g
  have hmem (g : Fin 3 → Bool) (i : Fin 3) : a i ∈ B g (g i) :=
    (le_iSup₂ (f := fun j (_ : g j = g i) => Algebra.adjoin R {a j}) i rfl) (hm i)
  have hleft : freeCumulantSeries φ ((a 0 * a 1) * a 2) =
      (freeCumulantSeries φ (a 0 * a 1)).boxedConvolution (freeCumulantSeries φ (a 2)) := by
    let g : Fin 3 → Bool := fun i => i == 2
    exact (hB g).freeCumulantSeries_mul hφ (i := false) (j := true) (by decide)
      ((B g false).mul_mem (hmem g 0) (hmem g 1)) (hmem g 2)
  have hright : freeCumulantSeries φ (a 0 * (a 1 * a 2)) =
      (freeCumulantSeries φ (a 0)).boxedConvolution (freeCumulantSeries φ (a 1 * a 2)) := by
    let g : Fin 3 → Bool := fun i => i == 0
    exact (hB g).freeCumulantSeries_mul hφ (i := true) (j := false) (by decide)
      (hmem g 0) ((B g false).mul_mem (hmem g 1) (hmem g 2))
  rw [← h.freeCumulantSeries_mul hφ (i := 0) (j := 1) (by decide),
    ← h.freeCumulantSeries_mul hφ (i := 1) (j := 2) (by decide),
    ← hleft, ← hright, mul_assoc]

end TauCeti

namespace PowerSeries

open TauCeti

private theorem boxedConvolution_assoc_of_constantCoeff_eq_one {R : Type*} [CommRing R]
    (f g h : R⟦X⟧) (hf : constantCoeff f = 1) (hg : constantCoeff g = 1)
    (hh : constantCoeff h = 1) :
    (f.boxedConvolution g).boxedConvolution h = f.boxedConvolution (g.boxedConvolution h) := by
  let F : Fin 3 → R⟦X⟧ := ![f, g, h]
  obtain ⟨φ, hφ, hfree, hseries⟩ := exists_freeProduct_freeCumulantSeries_eq F (by
    intro i
    fin_cases i <;> assumption)
  simpa [hseries, F] using boxedConvolution_assoc_of_free hfree hφ

private theorem boxedConvolution_assoc_ring {R : Type*} [CommRing R] (f g h : R⟦X⟧) :
    (f.boxedConvolution g).boxedConvolution h = f.boxedConvolution (g.boxedConvolution h) := by
  let N (s : R⟦X⟧) := s + C (1 - constantCoeff s)
  have hN (s : R⟦X⟧) : constantCoeff (N s) = 1 := by simp [N]
  have hcoeff (s : R⟦X⟧) (k : ℕ) (hk : k ≠ 0) : coeff k s = coeff k (N s) := by
    simp [N, coeff_C, hk]
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mul_assoc]
  calc
    coeff n ((f.boxedConvolution g).boxedConvolution h) =
        coeff n (((N f).boxedConvolution (N g)).boxedConvolution (N h)) :=
      coeff_boxedConvolution_congr hn
        (fun k hk => coeff_boxedConvolution_congr hk (hcoeff f) (hcoeff g)) (hcoeff h)
    _ = coeff n ((N f).boxedConvolution ((N g).boxedConvolution (N h))) :=
      congrArg (coeff n) (boxedConvolution_assoc_of_constantCoeff_eq_one _ _ _ (hN f) (hN g) (hN h))
    _ = coeff n (f.boxedConvolution (g.boxedConvolution h)) :=
      (coeff_boxedConvolution_congr hn (hcoeff f)
        (fun k hk => coeff_boxedConvolution_congr hk (hcoeff g) (hcoeff h))).symm

/-- Scalar boxed convolution is associative over every commutative semiring. The constant
coefficients are arbitrary; no invertibility of the linear coefficients is required. -/
theorem boxedConvolution_assoc {R : Type*} [CommSemiring R] (f g h : R⟦X⟧) :
    (f.boxedConvolution g).boxedConvolution h = f.boxedConvolution (g.boxedConvolution h) := by
  -- Prove the universal polynomial identity over the integers, descend injectively to
  -- natural coefficients, and evaluate at the coefficients of the three given series.
  let F : Fin 3 → (MvPolynomial (Fin 3 × ℕ) ℕ)⟦X⟧ :=
    fun i => mk fun n => MvPolynomial.X (i, n)
  let j : MvPolynomial (Fin 3 × ℕ) ℕ →+* MvPolynomial (Fin 3 × ℕ) ℤ :=
    MvPolynomial.map (Nat.castRingHom ℤ)
  have hj : Function.Injective j :=
    MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective
  have H : ((F 0).boxedConvolution (F 1)).boxedConvolution (F 2) =
      (F 0).boxedConvolution ((F 1).boxedConvolution (F 2)) := by
    apply map_injective j hj
    simpa only [map_boxedConvolution] using
      boxedConvolution_assoc_ring (map j (F 0)) (map j (F 1)) (map j (F 2))
  let e : MvPolynomial (Fin 3 × ℕ) ℕ →+* R :=
    MvPolynomial.eval₂Hom (Nat.castRingHom R) (fun p => coeff p.2 (![f, g, h] p.1))
  have he (i : Fin 3) : map e (F i) = ![f, g, h] i := by
    ext n
    simp [F, e]
  simpa [map_boxedConvolution, he] using congrArg (map e) H

end PowerSeries
