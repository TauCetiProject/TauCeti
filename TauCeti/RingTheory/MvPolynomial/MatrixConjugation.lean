/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.Linarith

/-!
# Matrix conjugation on multivariate polynomials and weight vanishing

Let `ι : W →+* O` be a homomorphism of commutative rings and `a ∈ GL (Fin k) W`. Conjugation of
a generic `k × k` matrix of variables `X` by `ι(a)` defines an `O`-algebra endomorphism
`TauCeti.matrixConjSubst ι a` of `MvPolynomial (Fin k × Fin k) O`, sending
`X (i, j)` to `∑ s t, ι (a⁻¹ i s) * ι (a t j) • X (s, t)`.

## Main definitions and results

* `TauCeti.matrixConjSubst`: the `O`-algebra endomorphism `X ↦ ι(a⁻¹) * X * ι(a)` on polynomials
  in the entries of a `k × k` matrix.
* `TauCeti.eval_one_matrixConjSubst`: evaluation at the identity matrix is invariant under
  `TauCeti.matrixConjSubst ι a`.
* `TauCeti.matrixConjSubst_diagGL_zpow_monomial`: conjugation by the diagonal unit matrix
  `diag (u ^ ρ i)` scales `monomial α 1` by `ι(u)` raised to column weight minus row weight.
* `TauCeti.apply_monomial_eq_zero_of_weight_ne`: over a local ring `W` and a characteristic-zero
  domain `O` in which some `p > 0` is not a unit, any `O`-linear form invariant under conjugation
  by diagonal matrices vanishes on every monomial whose row weight and column weight differ.

## References

* Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`),
  `src/New/UpperBound/ElementaryDivisors/InvariantAverage.lean`
  (`New.Average.conjSubst`, `New.Average.evalAtOne_conjSubst`,
  `New.Average.conjSubst_diagGL_zpow_monomial`, `New.Average.apply_monomial_eq_zero_of_weight_ne`).
-/

public section

namespace TauCeti

open MvPolynomial Matrix Finsupp

/-- The diagonal matrix in `GL (Fin k) W` with unit diagonal entries `d : Fin k → Wˣ`. -/
def diagGL {k : ℕ} {W : Type*} [CommRing W] (d : Fin k → Wˣ) : GL (Fin k) W :=
  ⟨diagonal (fun i ↦ (d i).val), diagonal (fun i ↦ (d i)⁻¹.val), by simp, by simp⟩

/-- The `O`-algebra endomorphism of `MvPolynomial (Fin k × Fin k) O` sending the matrix of
variables `X` to `ι(a⁻¹) * X * ι(a)`. -/
noncomputable def matrixConjSubst {k : ℕ} {W O : Type*} [CommRing W] [CommRing O] (ι : W →+* O)
    (a : GL (Fin k) W) :
    MvPolynomial (Fin k × Fin k) O →ₐ[O] MvPolynomial (Fin k × Fin k) O :=
  aeval fun p : Fin k × Fin k ↦
    ∑ s : Fin k, ∑ t : Fin k, C (ι (a⁻¹.val p.fst s) * ι (a.val t p.snd)) * X (s, t)

/-- Evaluation at the identity matrix is invariant under conjugation `matrixConjSubst ι a`. -/
theorem eval_one_matrixConjSubst {k : ℕ} {W O : Type*} [CommRing W] [CommRing O] (ι : W →+* O)
    (a : GL (Fin k) W) (ψ : MvPolynomial (Fin k × Fin k) O) :
    eval (fun p : Fin k × Fin k ↦ (1 : Matrix (Fin k) (Fin k) O) p.fst p.snd)
      (matrixConjSubst ι a ψ) =
    eval (fun p : Fin k × Fin k ↦ (1 : Matrix (Fin k) (Fin k) O) p.fst p.snd) ψ := by
  let f : MvPolynomial (Fin k × Fin k) O →ₐ[O] O :=
    aeval fun p : Fin k × Fin k ↦ (1 : Matrix (Fin k) (Fin k) O) p.fst p.snd
  have hev : f.comp (matrixConjSubst ι a) = f := by
    ext ⟨i, j⟩
    calc f (matrixConjSubst ι a (X (i, j)))
        = ∑ s : Fin k, ι (a⁻¹.val i s) * ι (a.val s j) := by
          simp [f, matrixConjSubst, Matrix.one_apply]
      _ = ι ((a⁻¹ * a).val i j) := by simp only [Units.val_mul, Matrix.mul_apply, map_sum, map_mul]
      _ = f (X (i, j)) := by simp [f, Matrix.one_apply]
  simpa [f] using AlgHom.congr_fun hev ψ

/-- Conjugating a monomial `monomial α 1` by the diagonal matrix `diagGL (fun i ↦ u ^ ρ i)`
multiplies it by `ι(u) ^ e`, where `e` is the column weight minus the row weight of `α`. -/
theorem matrixConjSubst_diagGL_zpow_monomial {k : ℕ} {W O : Type*} [CommRing W] [CommRing O]
    (ι : W →+* O) (u : Wˣ) (ρ : Fin k → ℤ) (α : Fin k × Fin k →₀ ℕ) :
    matrixConjSubst ι (diagGL fun i : Fin k ↦ u ^ ρ i) (monomial α 1) =
    (Units.map (ι : W →* O) u ^ (weight (fun v : Fin k × Fin k ↦ ρ v.snd) α -
      weight (fun v : Fin k × Fin k ↦ ρ v.fst) α) : Oˣ).val •
        (monomial α 1 : MvPolynomial (Fin k × Fin k) O) := by
  set u' : Oˣ := Units.map (ι : W →* O) u
  set e : ℤ := weight (fun v : Fin k × Fin k ↦ ρ v.snd) α -
    weight (fun v : Fin k × Fin k ↦ ρ v.fst) α
  have hX (v : Fin k × Fin k) :
      matrixConjSubst ι (diagGL fun i : Fin k ↦ u ^ ρ i) (X v) =
        C (u' ^ (ρ v.snd - ρ v.fst) : Oˣ).val * (X v : MvPolynomial (Fin k × Fin k) O) := by
    have hf : ι ((u ^ ρ v.fst)⁻¹.val * (u ^ ρ v.snd).val) =
        (u' ^ (ρ v.snd - ρ v.fst) : Oˣ).val := by
      simp [u', zpow_sub, mul_comm, ← map_zpow]
    simp [matrixConjSubst, diagGL, Matrix.diagonal_apply, apply_ite ι, apply_ite C, ← map_mul, hf]
  have h_prod : ∏ v : Fin k × Fin k, (u' ^ (ρ v.snd - ρ v.fst)) ^ α v = u' ^ e := by
    have h_zpow (s : Finset (Fin k × Fin k)) (g : Fin k × Fin k → ℤ) :
        ∏ v ∈ s, u' ^ g v = u' ^ ∑ v ∈ s, g v := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => simp [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
    simp only [← zpow_natCast, ← zpow_mul, h_zpow]
    congr 1
    simp [e, weight_eq_sum, sub_mul, mul_comm (α _ : ℤ)]
  rw [monomial_eq, C_1, one_mul, prod_fintype _ _ fun _ ↦ pow_zero _, map_prod]
  simp only [map_pow, hX, mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul]
  congr 1
  simp only [← map_pow, ← map_prod]
  congr 1
  simpa [Units.coe_prod, Units.val_pow_eq_pow_val] using congrArg Units.val h_prod

/-- Let `ι : W →+* O` map a local ring `W` to a characteristic-zero domain `O` in which some
`p > 0` is not a unit. Any `O`-linear form `I` on `MvPolynomial (Fin k × Fin k) O` invariant under
conjugation by diagonal matrices vanishes on every monomial whose row weight and column weight
differ. -/
theorem apply_monomial_eq_zero_of_weight_ne {k : ℕ} {W O : Type*} [CommRing W] [IsLocalRing W]
    [CommRing O] [IsDomain O] [CharZero O] (ι : W →+* O) {p : ℕ} (hp_pos : 0 < p)
    (hp : ¬IsUnit (p : O)) (ρ : Fin k → ℤ) {I : Module.Dual O (MvPolynomial (Fin k × Fin k) O)}
    (hI : ∀ (d : Fin k → Wˣ) (ψ : MvPolynomial (Fin k × Fin k) O),
      I (matrixConjSubst ι (diagGL d) ψ) = I ψ)
    {α : Fin k × Fin k →₀ ℕ}
    (hα : weight (fun v : Fin k × Fin k ↦ ρ v.fst) α ≠
      weight (fun v : Fin k × Fin k ↦ ρ v.snd) α) :
    I (monomial α 1) = 0 := by
  have h_unit : IsUnit (1 + (p : W)) := by
    simpa using (IsLocalRing.isUnit_or_isUnit_one_sub_self (-(p : W))).resolve_left
      fun h ↦ hp (by simpa using h.map ι)
  let u : Oˣ := Units.map (ι : W →* O) h_unit.unit
  have h_order : ¬IsOfFinOrder u := fun h ↦ by
    obtain ⟨m, hm_pos, hm⟩ := h.exists_pow_eq_one
    have h_cast : (((1 + p) ^ m : ℕ) : O) = (1 : ℕ) := by simpa [u] using congrArg Units.val hm
    exact (Nat.one_lt_pow hm_pos.ne' (by linarith)).ne' (Nat.cast_injective h_cast)
  let e : ℤ := weight (fun v : Fin k × Fin k ↦ ρ v.snd) α -
    weight (fun v : Fin k × Fin k ↦ ρ v.fst) α
  have h_ne : (u ^ e : Oˣ).val ≠ 1 := fun h ↦
    h_order (isOfFinOrder_iff_zpow_eq_one.mpr ⟨e, sub_ne_zero.mpr hα.symm, Units.ext h⟩)
  have h_inv : (u ^ e : Oˣ).val * I (monomial α 1) = I (monomial α 1) := by
    rw [← smul_eq_mul, ← map_smul, ← matrixConjSubst_diagGL_zpow_monomial, hI]
  exact (mul_left_eq_self₀.mp h_inv).resolve_left h_ne

end TauCeti
