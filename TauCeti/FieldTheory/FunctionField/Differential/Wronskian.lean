/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.FieldTheory.FunctionField.Place.Expansion.Laurent.Derivative
public import TauCeti.RingTheory.Derivation.Wronskian.Rescale
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Wronskians in function fields

Using the constant-field criterion for differentiation with respect to a separating element
from `TauCeti.FieldTheory.FunctionField.Differential.Kaehler`, this file proves that the
Wronskian of a finite family of functions is nonzero precisely when the family is linearly
independent over the exact constant field in characteristic zero. It also proves the
Wronskian transformation law for arbitrary derivations relative to a separating parameter,
in every characteristic and without an exact-constant-field hypothesis.

In particular, the elements of any basis of a Riemann--Roch space have nonzero Wronskian.
For the canonical series, this is the nonvanishing prerequisite for describing Weierstrass
weights by a ramification divisor. Changing a separating parameter from `x` to `y`
multiplies an `n`-function Wronskian by `(dx/dy) ^ (n * (n - 1) / 2)`. This is the
transformation law used to make the associated differential tensor independent of
that parameter.

At a rational place `P` with a separating prime element `t`, the file computes the order of the
Wronskian with respect to `t`. If the functions `f₀, …, fₙ₋₁` vanish to orders `a₀, …, aₙ₋₁`, then
the entry `dⁱfⱼ/dtⁱ` has leading term `aⱼ (aⱼ - 1) ⋯ (aⱼ - i + 1) fⱼ / tⁱ`, so after scaling rows
and columns the Wronskian matrix reduces modulo `P` to a Vandermonde matrix in the `aⱼ`. Hence

`ord_P W(f₀, …, fₙ₋₁) ≥ a₀ + ⋯ + aₙ₋₁ - n (n - 1) / 2`

in every characteristic, with equality, and a nonzero Wronskian, as soon as the orders `aⱼ` are
pairwise distinct in `k`; in characteristic zero, as soon as they are pairwise distinct. This is
the local computation behind the description of Weierstrass weights by orders of Wronskians.

## Main results

* `TauCeti.wronskian_derivativeOfSeparating_ne_zero_iff`: in characteristic zero over the exact
  constant field, the Wronskian detects linear independence.
* `TauCeti.wronskian_eq_pow_mul_wronskian_derivativeOfSeparating`: the change-of-parameter law.
* `TauCeti.Place.wronskian_derivativeOfSeparating_mem_filtration`: the lower bound on the order of
  the Wronskian at a rational place, in every characteristic.
* `TauCeti.Place.ord_wronskian_derivativeOfSeparating`: the order of the Wronskian of functions
  whose orders at a rational place are pairwise distinct in `k`.

## References

* D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215, Springer, 2003,
  the Wronskian treatment of Weierstrass points.
-/

public section

namespace TauCeti

open scoped IntermediateField

section CharZero

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero k]
variable {x : F} [Algebra.IsSeparable k⟮x⟯ F]

/-- The Wronskian with respect to a separating parameter detects linear independence over
the exact constant field in characteristic zero. -/
theorem wronskian_derivativeOfSeparating_ne_zero_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    {n : ℕ} (f : Fin n → F) :
    (derivativeOfSeparating hx).wronskian f ≠ 0 ↔ LinearIndependent k f :=
  (derivativeOfSeparating hx).wronskian_ne_zero_iff
    (fun y hy ↦ (derivativeOfSeparating_eq_zero_iff hF hex hx y).mp hy) f

end CharZero

/-- Relative to differentiation with respect to a separating parameter `x`, the Wronskian
of any derivation `D` is multiplied by `D x ^ (n * (n - 1) / 2)`. Taking `D = d/dy`
gives the change-of-parameter factor `(dx/dy) ^ (n * (n - 1) / 2)`. No characteristic or
exact-constant-field hypothesis is needed. -/
theorem wronskian_eq_pow_mul_wronskian_derivativeOfSeparating {k F : Type*}
    [Field k] [Field F] [Algebra k F] {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (D : Derivation k F F) {n : ℕ} (f : Fin n → F) :
    D.wronskian f = D x ^ (n * (n - 1) / 2) * (derivativeOfSeparating hx).wronskian f := by
  have hder : D = D x • derivativeOfSeparating hx := by
    ext z
    simpa only [Derivation.smul_apply, smul_eq_mul, mul_comm] using
      D.apply_eq_derivativeOfSeparating_smul hx z
  calc
    _ = (D x • derivativeOfSeparating hx).wronskian f :=
      congrArg (fun D : Derivation k F F ↦ D.wronskian f) hder
    _ = _ := Derivation.wronskian_smul _ _ f

namespace Place

open Matrix

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F) {t : F}
  (hP : P.degree = 1) (ht : P.ord t = 1) (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ F]

include hP ht in
/-- **A lower bound for the order of a Wronskian.** At a rational place `P` with a separating
prime element `t`, if each `f j` vanishes to order at least `m j`, then the Wronskian with respect
to `t` vanishes to order at least `∑ j, m j - n (n - 1) / 2`. This holds in every
characteristic. -/
theorem wronskian_derivativeOfSeparating_mem_filtration {n : ℕ} {f : Fin n → F} {m : Fin n → ℤ}
    (hf : ∀ j, f j ∈ P.filtration (m j)) :
    (derivativeOfSeparating htr).wronskian f ∈
      P.filtration (∑ j, m j - (n * (n - 1) / 2 : ℕ)) := by
  rw [Derivation.wronskian_def, det_apply, ← Finset.sum_range_id, Nat.cast_sum,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ (i : ℤ))]
  -- Each term `∏ⱼ d^{σ j} fⱼ / dt^{σ j}` of the Leibniz expansion vanishes to that order.
  refine Submodule.sum_mem _ fun σ _ ↦ ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  have h := P.prod_mem_filtration Finset.univ (a := fun j ↦ m j - ((σ j : ℕ) : ℤ))
    (z := fun j ↦ (⇑(derivativeOfSeparating htr))^[σ j] (f j))
    (fun j _ ↦ P.iterate_derivativeOfSeparating_mem_filtration hP ht htr (hf j) (σ j))
  rwa [Finset.sum_sub_distrib, Equiv.sum_comp σ (fun i ↦ ((i : ℕ) : ℤ))] at h

include hP ht in
/-- Scaling row `i` of the Wronskian matrix by `t ^ i` and column `j` by `(f j)⁻¹` gives a matrix
integral at `P` whose reduction is a Vandermonde matrix in the orders of the `f j`; when these are
distinct in `k`, its determinant is a unit at `P`. -/
private lemma det_normalized {n : ℕ} {f : Fin n → F} (hf : ∀ j, f j ≠ 0)
    (hinj : Function.Injective fun j ↦ (P.ord (f j) : k)) :
    (of fun i j : Fin n ↦ t ^ (i : ℕ) *
      ((f j)⁻¹ * (⇑(derivativeOfSeparating htr))^[i] (f j))).det ≠ 0 ∧
    P.ord (of fun i j : Fin n ↦ t ^ (i : ℕ) *
      ((f j)⁻¹ * (⇑(derivativeOfSeparating htr))^[i] (f j))).det = 0 := by
  generalize hNdef : (of fun i j : Fin n ↦ t ^ (i : ℕ) *
      ((f j)⁻¹ * (⇑(derivativeOfSeparating htr))^[i] (f j))) = N
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  let c : Matrix (Fin n) (Fin n) ℤ := of fun i j ↦ (descPochhammer ℤ i).eval (P.ord (f j))
  -- Each normalized entry is congruent to the integer `(ord f_j)(ord f_j - 1)⋯` modulo `𝔪_P`.
  have hentry (i j : Fin n) : N i j - (c i j : F) ∈ P.filtration 1 := by
    have hE := P.iterate_derivativeOfSeparating_sub_zsmul_mem_filtration hP ht htr
      (P.mem_filtration_ord (f j)) i
    have hw : t ^ (i : ℕ) * (f j)⁻¹ ∈ P.filtration (i - P.ord (f j)) := by
      convert P.mul_mem_filtration (P.mem_filtration_ord (t ^ (i : ℕ)))
        (P.mem_filtration_ord (f j)⁻¹) using 2
      simp [ht, sub_eq_add_neg]
    convert P.mul_mem_filtration hw hE using 1
    · congr 1
      omega
    · have := hf j
      simp only [← hNdef, c, of_apply, zsmul_eq_mul, inv_pow]
      field_simp
  have hint (i j : Fin n) : N i j ∈ P.integers := by
    rw [← mem_filtration_zero_iff, ← sub_add_cancel (N i j) (c i j : F)]
    refine add_mem (P.filtration_antitone (by omega) (hentry i j)) ?_
    rw [mem_filtration_zero_iff]
    exact intCast_mem _ _
  let N' : Matrix (Fin n) (Fin n) P.integers := of fun i j ↦ ⟨N i j, hint i j⟩
  have hdet : N.det = (N'.det : F) := by
    -- The entries of `N'` are those of `N`, viewed in `𝒪_P`.
    rw [← ValuationSubring.algebraMap_apply, RingHom.map_det]
    congr 1
  have hres : IsLocalRing.residue P.integers N'.det =
      IsLocalRing.residue P.integers ((c.det : ℤ) : P.integers) := by
    have hcast : ((c.det : ℤ) : P.integers) =
        ((Int.castRingHom P.integers).mapMatrix c).det := by
      rw [← RingHom.map_det, eq_intCast]
    rw [hcast, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    exact (residue_eq_iff_sub_mem_filtration_one P).mpr (by simpa [N'] using hentry i j)
  have hc : ((c.det : ℤ) : k) ≠ 0 := by
    -- The reduction of `c` is the transpose of a Vandermonde matrix in the orders.
    have hv : ((c.det : ℤ) : k) = (vandermonde fun j ↦ (P.ord (f j) : k)).det := by
      have h := RingHom.map_det (Int.castRingHom k) cᵀ
      rw [eq_intCast, det_transpose] at h
      rw [h, det_eval_matrixOfPolynomials_eq_det_vandermonde _ (fun i ↦ descPochhammer k i)
        (fun i ↦ descPochhammer_natDegree k i) (fun i ↦ monic_descPochhammer k i)]
      congr 1
      ext i j
      simp [c, descPochhammer_eval_cast]
    rw [hv]
    exact det_vandermonde_ne_zero_iff.mpr hinj
  have hcmem : ((c.det : ℤ) : F) ∉ P.filtration 1 := by
    rw [← map_intCast (algebraMap k F),
      P.mem_filtration_iff_le_ord ((map_ne_zero _).mpr hc), ord_algebraMap]
    omega
  have hsub : N.det - ((c.det : ℤ) : F) ∈ P.filtration 1 := by
    simpa [hdet] using (residue_eq_iff_sub_mem_filtration_one P).mp hres
  have hN1 : N.det ∉ P.filtration 1 := fun h ↦ hcmem (by simpa using sub_mem h hsub)
  have hN0 : N.det ∈ P.filtration 0 := by
    rw [mem_filtration_zero_iff, hdet]
    exact N'.det.2
  have hne : N.det ≠ 0 := by
    rintro h
    exact hN1 (h ▸ zero_mem _)
  refine ⟨hne, ?_⟩
  have h0 := (P.mem_filtration_iff_le_ord hne).mp hN0
  have h1 := (P.mem_filtration_iff_le_ord hne).not.mp hN1
  omega

/-- The determinant of the normalized Wronskian matrix of `TauCeti.Place.det_normalized`. -/
private lemma det_normalized_eq {n : ℕ} (f : Fin n → F) :
    (of fun i j : Fin n ↦ t ^ (i : ℕ) *
      ((f j)⁻¹ * (⇑(derivativeOfSeparating htr))^[i] (f j))).det =
      (∏ i : Fin n, t ^ (i : ℕ)) * ((∏ j, (f j)⁻¹) *
        (derivativeOfSeparating htr).wronskian f) := by
  have h := det_mul_column (fun i : Fin n ↦ t ^ (i : ℕ))
    (of fun i j ↦ (f j)⁻¹ * (⇑(derivativeOfSeparating htr))^[i] (f j))
  simp only [of_apply] at h
  rw [h, Derivation.wronskian_def, ← det_mul_row (fun j ↦ (f j)⁻¹)]
  simp only [of_apply]

include hP ht in
/-- At a rational place with a separating prime element `t`, nonzero functions whose orders are
pairwise distinct in `k` have a nonzero Wronskian with respect to `t`. -/
theorem wronskian_derivativeOfSeparating_ne_zero {n : ℕ} {f : Fin n → F} (hf : ∀ j, f j ≠ 0)
    (hinj : Function.Injective fun j ↦ (P.ord (f j) : k)) :
    (derivativeOfSeparating htr).wronskian f ≠ 0 := by
  have h := (P.det_normalized hP ht htr hf hinj).1
  rw [det_normalized_eq] at h
  exact right_ne_zero_of_mul (right_ne_zero_of_mul h)

include hP ht in
/-- **The order of a Wronskian at a rational place.** If `t` is a separating prime element at a
rational place `P` and the nonzero functions `f j` have orders at `P` that are pairwise distinct in
`k`, then the Wronskian with respect to `t` has order `∑ j, ord_P (f j) - n (n - 1) / 2`. -/
theorem ord_wronskian_derivativeOfSeparating {n : ℕ} {f : Fin n → F} (hf : ∀ j, f j ≠ 0)
    (hinj : Function.Injective fun j ↦ (P.ord (f j) : k)) :
    P.ord ((derivativeOfSeparating htr).wronskian f) =
      ∑ j, P.ord (f j) - (n * (n - 1) / 2 : ℕ) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have h := (P.det_normalized hP ht htr hf hinj).2
  have hW := P.wronskian_derivativeOfSeparating_ne_zero hP ht htr hf hinj
  rw [det_normalized_eq, P.ord_mul (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ ht0)
      (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ ↦ inv_ne_zero (hf j)) hW),
    P.ord_mul (Finset.prod_ne_zero_iff.mpr fun j _ ↦ inv_ne_zero (hf j)) hW,
    P.ord_prod _ fun i _ ↦ pow_ne_zero _ ht0, P.ord_prod _ fun j _ ↦ inv_ne_zero (hf j)] at h
  simp only [ord_pow, ht, mul_one, ord_inv, Finset.sum_neg_distrib] at h
  rw [← Finset.sum_range_id, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i ↦ (i : ℤ))]
  omega

include hP ht in
/-- At a rational place with a separating prime element `t`, in characteristic zero, nonzero
functions with pairwise distinct orders at `P` have a nonzero Wronskian with respect to `t`. -/
theorem wronskian_derivativeOfSeparating_ne_zero_of_injective [CharZero k] {n : ℕ}
    {f : Fin n → F} (hf : ∀ j, f j ≠ 0) (hinj : Function.Injective fun j ↦ P.ord (f j)) :
    (derivativeOfSeparating htr).wronskian f ≠ 0 :=
  P.wronskian_derivativeOfSeparating_ne_zero hP ht htr hf (Int.cast_injective.comp hinj)

include hP ht in
/-- **The order of a Wronskian at a rational place, in characteristic zero**: nonzero functions
with pairwise distinct orders at `P` have a Wronskian of order `∑ j, ord_P (f j) - n (n - 1) / 2`.
-/
theorem ord_wronskian_derivativeOfSeparating_of_injective [CharZero k] {n : ℕ} {f : Fin n → F}
    (hf : ∀ j, f j ≠ 0) (hinj : Function.Injective fun j ↦ P.ord (f j)) :
    P.ord ((derivativeOfSeparating htr).wronskian f) =
      ∑ j, P.ord (f j) - (n * (n - 1) / 2 : ℕ) :=
  P.ord_wronskian_derivativeOfSeparating hP ht htr hf (Int.cast_injective.comp hinj)

end Place

end TauCeti
