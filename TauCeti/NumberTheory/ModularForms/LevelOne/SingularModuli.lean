/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.HilbertClassPolynomial
public import TauCeti.NumberTheory.ModularForms.LevelOne.CyclicIsogenyPolynomial
public import TauCeti.NumberTheory.ModularForms.LevelOne.WeaklyHolomorphic
public import TauCeti.NumberTheory.ModularForms.QExpansion.Affine
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.RingTheory.HahnSeries.Map

/-!
# Singular moduli are algebraic integers

If `τ` in the upper half-plane is an imaginary quadratic number, a root of an integral quadratic
equation `a τ² + b τ + c = 0`, then the value `j(τ)` of the modular invariant is an algebraic
integer (`TauCeti.ModularForm.isIntegral_j_of_quadratic`). In particular the singular moduli of
every negative discriminant are algebraic integers, and the Hilbert class polynomial has
algebraic integer coefficients
(`TauCeti.BinaryQuadraticForm.isIntegral_coeff_hilbertClassPolynomial`).
This integrality is what makes the values of modular functions at imaginary quadratic points
algebraic integers, as needed for the norms of Siegel functions in the class number one problem.

The proof is the classical one through the modular equation. For a positive integer `n`, let
`Φ_n(X, j(τ)) = ∏ (X - j(A τ))` be the polynomial over the cyclic `n`-isogenies
(`TauCeti.ModularForm.cyclicIsogenyPolynomial`), the product over the primitive upper-triangular
representatives `A = (a b; 0 d)` of determinant `n`.

1. The diagonal value `Φ_n(j(τ), j(τ)) = ∏ (j(τ) - j(A τ))` is a holomorphic `SL(2, ℤ)`-invariant
   function. Its Laurent `q`-expansion is computed from that of `j`: at period `n`, the expansion
   of `j(A τ)` is the expansion `∑ₘ cₘ qᵐ` of `j` rescaled by the root of unity `e^{2πib/d}` and
   expanded by `q ↦ q^{a²}`, so it has algebraic integer coefficients. By the integral
   `q`-expansion principle in level one (`TauCeti.ModularForm.exists_aeval_j_eq`),
   `Φ_n(j(τ), j(τ)) = P(j(τ))` for a polynomial `P` with algebraic integer coefficients
   (`TauCeti.ModularForm.exists_aeval_j_eq_eval_cyclicIsogenyPolynomial`).
2. If `n` is not a square, no factor `j(τ) - j(A τ)` has cancelling leading terms at `i∞`: the
   pole of `j(τ)` has order `n` and that of `j(A τ)` has order `a²` in `q^{1/n}`. The leading
   coefficient of `P` is therefore a product of roots of unity and signs, a unit of the algebraic
   integers (`TauCeti.ModularForm.isUnit_leadingCoeff_of_aeval_j_eq_eval_cyclicIsogenyPolynomial`).
3. If `a τ² + b τ + c = 0` with `a > 0`, then for `x = 1 + a (|b| + 4ac - b²)` the primitive
   matrix `(x - b, -c; a, x)` fixes `τ` and has a nonsquare determinant `n = x² - b x + a c`. So
   `j(τ)` is a root of `Φ_n(X, j(τ))`, hence of `P`, and it is integral over the algebraic integers
   (`TauCeti.ModularForm.isIntegral_j_of_isPrimitive`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, 2nd ed., Wiley, 2013, §11: Theorem 11.18 (the
  modular equation; for nonsquare `m` the leading coefficient of `Φ_m(X, X)` is `±1`) and the
  proof of Theorem 11.1 (the `j`-invariant of a proper ideal of an imaginary quadratic order is
  an algebraic integer).
* S. Lang, *Elliptic Functions*, 2nd ed., GTM 112, Springer, 1987, Chapter 5, §2.
-/

public section

open Polynomial UpperHalfPlane Filter
open scoped MatrixGroups Manifold LaurentSeries

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti.ModularForm

open FixedDetMatrices TauCeti.UpperHalfPlane

variable {n : ℕ} [NeZero n]

/-! ### The modular invariant along a cyclic isogeny -/

section Reps

variable {A : FixedDetMatrix (Fin 2) ℤ n}

/-- The exponent `a ^ 2` of the expansion along a representative `(a b; 0 d)`. -/
private abbrev repsExponent (A : FixedDetMatrix (Fin 2) ℤ n) : ℕ+ :=
  ((A.val 0 0).natAbs ^ 2).toPNat'

/-- The root of unity `exp (2 π i b / d)` of the expansion along a representative `(a b; 0 d)`. -/
private noncomputable abbrev repsTwist (A : FixedDetMatrix (Fin 2) ℤ n) : ℂˣ :=
  Units.mk0 (𝕢 1 ((A.val 0 1 / A.val 1 1 : ℝ) : ℂ)) (Function.Periodic.qParam_ne_zero _)

private theorem natCast_pos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n

/-- The function `τ ↦ j ((a τ + b) / d)` has a meromorphic cusp function at period `n`. -/
private theorem meromorphicAt_cuspFunction_j_toGLReal_smul (hA : A ∈ reps (n : ℤ)) :
    MeromorphicAt (cuspFunction n fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 :=
  meromorphicAt_cuspFunction_comp_toGLReal_smul natCast_pos hA
    periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j

/-- The Laurent expansion of `τ ↦ j ((a τ + b) / d)` at period `n`. -/
private theorem laurentQExpansion_j_toGLReal_smul (hA : A ∈ reps (n : ℤ)) :
    laurentQExpansion n (fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      LaurentSeries.expand ℂ (repsExponent A)
        (LaurentSeries.rescale (repsTwist A) (laurentQExpansion 1 j)) :=
  laurentQExpansion_comp_toGLReal_smul natCast_pos hA
    periodic_j_comp_ofComplex meromorphicAt_cuspFunction_j

/-- The twist `exp (2 π i b / d)` of a representative `(a b; 0 d)` is a `d`-th root of unity. -/
private theorem repsTwist_pow (hA : A ∈ reps (n : ℤ)) :
    (repsTwist A : ℂ) ^ (A.val 1 1).toNat = 1 := by
  have hd : (0 : ℤ) < A.val 1 1 := pos_val_one_one_of_mem_reps natCast_pos hA
  have hd' : ((A.val 1 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Units.val_mk0, Function.Periodic.qParam, ← Complex.exp_natCast_mul,
    ← Complex.exp_int_mul_two_pi_mul_I (A.val 0 1)]
  congr 1
  rw [show (((A.val 1 1).toNat : ℕ) : ℂ) = ((A.val 1 1 : ℝ) : ℂ) by
    rw [Complex.ofReal_intCast, ← Int.cast_natCast, Int.toNat_of_nonneg hd.le]]
  push_cast at hd' ⊢
  field_simp

/-- **The Laurent `q`-expansion of `j` along a cyclic isogeny has algebraic integer
coefficients**: they are integers times roots of unity. -/
theorem isIntegral_coeff_laurentQExpansion_j_toGLReal_smul (hA : A ∈ reps (n : ℤ)) (k : ℤ) :
    IsIntegral ℤ
      ((laurentQExpansion n fun τ ↦ j (toGLReal (NeZero.ne (n : ℤ)) A • τ)).coeff k) := by
  rw [laurentQExpansion_j_toGLReal_smul hA]
  by_cases hk : ((repsExponent A : ℕ) : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [LaurentSeries.coeff_expand_mul, LaurentSeries.coeff_rescale]
    obtain ⟨z, hz⟩ := exists_laurentQExpansion_j_coeff_eq_intCast m
    rw [hz]
    refine IsIntegral.mul ?_ (isIntegral_intCast z)
    -- a power of a root of unity is a root of unity, hence integral
    have hd : 0 < (A.val 1 1).toNat := by
      have := pos_val_one_one_of_mem_reps natCast_pos hA
      omega
    refine IsIntegral.of_pow hd ?_
    rw [Units.val_zpow_eq_zpow_val, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, repsTwist_pow hA, one_zpow]
    exact isIntegral_one
  · rw [LaurentSeries.coeff_expand_of_not_dvd _ _ hk]
    exact isIntegral_zero

end Reps

/-! ### `Φ_n(j(τ), j(τ))` is an integral polynomial in `j(τ)` -/

/-- The Laurent series with algebraic integer coefficients. -/
private noncomputable def integralLaurentSeries : Subring (LaurentSeries ℂ) :=
  (HahnSeries.mapRingHom (Γ := ℤ) (algebraMap (integralClosure ℤ ℂ) ℂ)).range

private theorem mem_integralLaurentSeries_iff {x : LaurentSeries ℂ} :
    x ∈ integralLaurentSeries ↔ ∀ k, IsIntegral ℤ (x.coeff k) := by
  have := HahnSeries.mem_map_rangeS (f := algebraMap (integralClosure ℤ ℂ) ℂ) (x := x)
  simp only [RingHom.mem_rangeS] at this
  rw [integralLaurentSeries, RingHom.mem_range, this]
  refine forall_congr' fun k ↦ ⟨?_, fun hk ↦ ⟨⟨_, hk⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.property

variable (n) in
/-- The positive integer `n`. -/
private abbrev nPNat : ℕ+ := ⟨n, NeZero.pos n⟩

/-- The diagonal value `Φ_n(j(τ), j(τ)) = ∏ (j(τ) - j(A τ))` over the cyclic `n`-isogenies. -/
private theorem eval_cyclicIsogenyPolynomial_j_eq_prod :
    (fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)) =
      ∏ A ∈ primitiveReps (n : ℤ), fun τ ↦ j τ - j (toGLReal (NeZero.ne (n : ℤ)) A • τ) := by
  funext τ
  simp [cyclicIsogenyPolynomial_def, eval_prod, Finset.prod_apply]

private theorem meromorphicAt_cuspFunction_j_nat :
    MeromorphicAt (cuspFunction n j) 0 := by
  simpa [nPNat] using meromorphicAt_cuspFunction_pnat_mul one_pos periodic_j_comp_ofComplex
    meromorphicAt_cuspFunction_j (nPNat n)

private theorem laurentQExpansion_j_nat :
    laurentQExpansion n j = LaurentSeries.expand ℂ (nPNat n) (laurentQExpansion 1 j) := by
  simpa [nPNat] using laurentQExpansion_pnat_mul periodic_j_comp_ofComplex
    meromorphicAt_cuspFunction_j (nPNat n)

private theorem meromorphicAt_cuspFunction_sub_j_toGLReal_smul
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    MeromorphicAt (cuspFunction n fun τ ↦ j τ - j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) 0 :=
  meromorphicAt_cuspFunction_sub meromorphicAt_cuspFunction_j_nat
    (meromorphicAt_cuspFunction_j_toGLReal_smul hA)

private theorem laurentQExpansion_sub_j_toGLReal_smul
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    laurentQExpansion n (fun τ ↦ j τ - j (toGLReal (NeZero.ne (n : ℤ)) A • τ)) =
      LaurentSeries.expand ℂ (nPNat n) (laurentQExpansion 1 j) -
        LaurentSeries.expand ℂ (repsExponent A)
          (LaurentSeries.rescale (repsTwist A) (laurentQExpansion 1 j)) := by
  rw [← laurentQExpansion_j_nat,
    ← laurentQExpansion_j_toGLReal_smul hA]
  exact laurentQExpansion_sub meromorphicAt_cuspFunction_j_nat
    (meromorphicAt_cuspFunction_j_toGLReal_smul hA)

/-- `Φ_n(j(τ), j(τ))` is holomorphic. -/
private theorem mdifferentiable_eval_cyclicIsogenyPolynomial_j :
    MDiff (fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)) := by
  rw [eval_cyclicIsogenyPolynomial_j_eq_prod]
  refine Finset.prod_induction _ (fun f : ℍ → ℂ ↦ MDiff f) (fun f g hf hg ↦ hf.mul hg)
    mdifferentiable_const fun A _ ↦ j_mdifferentiable.sub ?_
  exact j_mdifferentiable.comp (mdifferentiable_toGLReal_smul natCast_pos A)

/-- `Φ_n(j(τ), j(τ))` is `SL(2, ℤ)`-invariant. -/
private theorem eval_cyclicIsogenyPolynomial_j_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    (cyclicIsogenyPolynomial n j (γ • τ)).eval (j (γ • τ)) =
      (cyclicIsogenyPolynomial n j τ).eval (j τ) := by
  rw [cyclicIsogenyPolynomial_smul j_smul_SL2Z, j_smul_SL2Z]

/-- `Φ_n(j(τ), j(τ))` has a meromorphic cusp function at period `n`. -/
private theorem meromorphicAt_cuspFunction_nat_eval_cyclicIsogenyPolynomial_j :
    MeromorphicAt (cuspFunction n fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)) 0 := by
  rw [eval_cyclicIsogenyPolynomial_j_eq_prod]
  exact meromorphicAt_cuspFunction_prod fun A hA ↦
    meromorphicAt_cuspFunction_sub_j_toGLReal_smul ((mem_primitiveReps.1 hA).1)

/-- The Laurent expansion of `Φ_n(j(τ), j(τ))` at period `n` has algebraic integer
coefficients: it is the product over the cyclic `n`-isogenies `A` of the expansions of
`j(τ) - j(A τ)`, which have algebraic integer coefficients. -/
private theorem laurentQExpansion_nat_eval_cyclicIsogenyPolynomial_j_mem :
    laurentQExpansion n (fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)) ∈
      integralLaurentSeries := by
  rw [eval_cyclicIsogenyPolynomial_j_eq_prod, laurentQExpansion_prod fun A hA ↦
    meromorphicAt_cuspFunction_sub_j_toGLReal_smul ((mem_primitiveReps.1 hA).1)]
  refine prod_mem fun A hA ↦ ?_
  have hA' := (mem_primitiveReps.1 hA).1
  rw [laurentQExpansion_sub_j_toGLReal_smul hA']
  refine sub_mem (mem_integralLaurentSeries_iff.2 fun k ↦ ?_) ?_
  · by_cases hk : ((nPNat n : ℕ) : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hk
      obtain ⟨z, hz⟩ := exists_laurentQExpansion_j_coeff_eq_intCast m
      rw [LaurentSeries.coeff_expand_mul, hz]
      exact isIntegral_intCast z
    · rw [LaurentSeries.coeff_expand_of_not_dvd _ _ hk]
      exact isIntegral_zero
  · rw [← laurentQExpansion_j_toGLReal_smul hA']
    exact mem_integralLaurentSeries_iff.2 (isIntegral_coeff_laurentQExpansion_j_toGLReal_smul hA')

/-- `Φ_n(j(τ), j(τ))` is `1`-periodic, read on `ℂ` through `ofComplex`. -/
private theorem periodic_eval_cyclicIsogenyPolynomial_j :
    Function.Periodic
      ((fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)) ∘ ofComplex) 1 := by
  refine periodic_comp_ofComplex_iff.mpr fun τ ↦ ?_
  rw [← modular_T_smul]
  exact eval_cyclicIsogenyPolynomial_j_smul _ τ

/-- `Φ_n(j(τ), j(τ))` has a meromorphic cusp function at period `1`. -/
private theorem meromorphicAt_cuspFunction_eval_cyclicIsogenyPolynomial_j :
    MeromorphicAt (cuspFunction 1 fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)) 0 :=
  meromorphicAt_cuspFunction_of_pnat_mul one_pos periodic_eval_cyclicIsogenyPolynomial_j
    mdifferentiable_eval_cyclicIsogenyPolynomial_j (nPNat n)
    (by simpa [nPNat] using meromorphicAt_cuspFunction_nat_eval_cyclicIsogenyPolynomial_j)

/-- The Laurent expansion of `Φ_n(j(τ), j(τ))` at period `n` is its expansion at period `1`,
expanded by `X ↦ X ^ n`. -/
private theorem laurentQExpansion_nat_eval_cyclicIsogenyPolynomial_j :
    laurentQExpansion n (fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)) =
      LaurentSeries.expand ℂ (nPNat n)
        (laurentQExpansion 1 fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)) := by
  simpa [nPNat] using laurentQExpansion_pnat_mul periodic_eval_cyclicIsogenyPolynomial_j
    meromorphicAt_cuspFunction_eval_cyclicIsogenyPolynomial_j (nPNat n)

variable (n) in
/-- **`Φ_n(j(τ), j(τ))` is a polynomial in `j(τ)` with algebraic integer coefficients.** The
product `∏ (j(τ) - j(A τ))` over the cyclic `n`-isogenies `A` is `P(j(τ))` for a polynomial `P`
whose coefficients are algebraic integers. -/
theorem exists_aeval_j_eq_eval_cyclicIsogenyPolynomial :
    ∃ P : (integralClosure ℤ ℂ)[X],
      ∀ τ, aeval (j τ) P = (cyclicIsogenyPolynomial n j τ).eval (j τ) := by
  refine exists_aeval_j_eq mdifferentiable_eval_cyclicIsogenyPolynomial_j
    eval_cyclicIsogenyPolynomial_j_smul meromorphicAt_cuspFunction_eval_cyclicIsogenyPolynomial_j
    fun m _ ↦ ?_
  have hm := mem_integralLaurentSeries_iff.1
    (laurentQExpansion_nat_eval_cyclicIsogenyPolynomial_j_mem (n := n)) ((nPNat n : ℕ) * m)
  rw [laurentQExpansion_nat_eval_cyclicIsogenyPolynomial_j, LaurentSeries.coeff_expand_mul] at hm
  exact ⟨⟨_, hm⟩, rfl⟩

/-! ### The leading coefficient for a nonsquare `n` -/

/-- The Laurent `q`-expansion of `j` has leading coefficient `1`. -/
private theorem leadingCoeff_laurentQExpansion_j : (laurentQExpansion 1 j).leadingCoeff = 1 := by
  have hne : laurentQExpansion 1 j ≠ 0 := by
    rw [← HahnSeries.orderTop_ne_top, orderTop_laurentQExpansion_j]
    exact WithTop.coe_ne_top
  have hord : (laurentQExpansion 1 j).order = -1 := by
    apply WithTop.coe_injective
    rw [HahnSeries.order_eq_orderTop_of_ne_zero hne, orderTop_laurentQExpansion_j]
    rfl
  rw [HahnSeries.leadingCoeff_eq, hord, laurentQExpansion_j_coeff_neg_one]

/-- A root of unity, as a unit of the ring of algebraic integers. -/
private def unitOfPowEqOne {u : ℂˣ} {d : ℕ} (hd : 0 < d) (hu : (u : ℂ) ^ d = 1) :
    (integralClosure ℤ ℂ)ˣ where
  val := ⟨u, IsIntegral.of_pow hd (hu ▸ isIntegral_one)⟩
  inv := ⟨(u⁻¹ : ℂˣ), IsIntegral.of_pow hd (by
    rw [← Units.val_pow_eq_pow_val, inv_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      hu, inv_one]
    exact isIntegral_one)⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

/-- For `n` not a square, the leading coefficient of the Laurent expansion of `j(τ) - j(A τ)` at
period `n` is a unit of the algebraic integers: it is `1` if `a ^ 2 < n` and `-e^{-2πib/d}` if
`a ^ 2 > n`. -/
private theorem exists_units_eq_leadingCoeff (hn : ¬ IsSquare n)
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps (n : ℤ)) :
    ∃ w : (integralClosure ℤ ℂ)ˣ, ((w : integralClosure ℤ ℂ) : ℂ) =
      (LaurentSeries.expand ℂ (nPNat n) (laurentQExpansion 1 j) -
        LaurentSeries.expand ℂ (repsExponent A)
          (LaurentSeries.rescale (repsTwist A) (laurentQExpansion 1 j))).leadingCoeff := by
  set L := laurentQExpansion 1 j
  set x := LaurentSeries.expand ℂ (nPNat n) L
  set y := LaurentSeries.expand ℂ (repsExponent A) (LaurentSeries.rescale (repsTwist A) L)
  have hLo : L.orderTop = ((-1 : ℤ) : WithTop ℤ) := orderTop_laurentQExpansion_j
  have hxo : x.orderTop = ((-(n : ℤ) : ℤ) : WithTop ℤ) := by
    rw [LaurentSeries.orderTop_expand, hLo, ← WithTop.coe_nsmul]
    simp [nPNat]
  have hyo : y.orderTop = ((-((repsExponent A : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [LaurentSeries.orderTop_expand, LaurentSeries.orderTop_rescale, hLo, ← WithTop.coe_nsmul]
    simp
  have hne : (repsExponent A : ℕ) ≠ n := fun h ↦
    hn ⟨(A.val 0 0).natAbs, h.symm.trans (by
      rw [PNat.toPNat'_coe (pow_pos (Int.natAbs_pos.mpr hA.2.1.ne') 2), sq])⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- the pole of `j(τ)` dominates
    refine ⟨1, ?_⟩
    have hxy : x.orderTop < y.orderTop := by
      rw [hxo, hyo, WithTop.coe_lt_coe, neg_lt_neg_iff]
      exact_mod_cast hlt
    rw [HahnSeries.leadingCoeff_sub hxy, LaurentSeries.leadingCoeff_expand,
      leadingCoeff_laurentQExpansion_j]
    rfl
  · -- the pole of `j(A τ)` dominates
    have hd : 0 < (A.val 1 1).toNat := by
      have := pos_val_one_one_of_mem_reps natCast_pos hA
      omega
    have hu : ((repsTwist A)⁻¹ : ℂˣ).val ^ (A.val 1 1).toNat = 1 := by
      rw [← Units.val_pow_eq_pow_val, inv_pow, Units.val_inv_eq_inv_val,
        Units.val_pow_eq_pow_val, repsTwist_pow hA, inv_one]
    refine ⟨-unitOfPowEqOne hd hu, ?_⟩
    have hyx : y.orderTop < x.orderTop := by
      rw [hxo, hyo, WithTop.coe_lt_coe, neg_lt_neg_iff]
      exact_mod_cast hgt
    have hord : L.order = -1 := by
      have hne : L ≠ 0 := by
        rw [← HahnSeries.orderTop_ne_top, hLo]
        exact WithTop.coe_ne_top
      exact WithTop.coe_injective (by rw [HahnSeries.order_eq_orderTop_of_ne_zero hne, hLo])
    rw [← neg_sub, HahnSeries.leadingCoeff_neg, HahnSeries.leadingCoeff_sub hyx,
      LaurentSeries.leadingCoeff_expand, LaurentSeries.leadingCoeff_rescale, hord,
      leadingCoeff_laurentQExpansion_j, mul_one]
    simp [unitOfPowEqOne]

/-- **For `n` not a square, `Φ_n(j(τ), j(τ))` is a polynomial in `j(τ)` with unit leading
coefficient.** Any polynomial `P` over the algebraic integers with `P(j(τ)) = Φ_n(j(τ), j(τ))`
has a leading coefficient that is a unit of the algebraic integers. The leading term of
`j(τ) - j(A τ)` at `i∞` is that of `j(τ)` or of `j(A τ)` according as `a ^ 2 < n` or
`a ^ 2 > n`, and equality is excluded because `n` is not a square. -/
theorem isUnit_leadingCoeff_of_aeval_j_eq_eval_cyclicIsogenyPolynomial (hn : ¬ IsSquare n)
    {P : (integralClosure ℤ ℂ)[X]}
    (hP : ∀ τ, aeval (j τ) P = (cyclicIsogenyPolynomial n j τ).eval (j τ)) :
    IsUnit P.leadingCoeff := by
  have hreps {A} (hA : A ∈ primitiveReps (n : ℤ)) : A ∈ reps (n : ℤ) :=
    (mem_primitiveReps.1 hA).1
  have hLo : (laurentQExpansion 1 j).orderTop < 0 := by
    rw [orderTop_laurentQExpansion_j]
    exact WithTop.coe_lt_coe.mpr (by norm_num)
  have hinj : Function.Injective (algebraMap (integralClosure ℤ ℂ) ℂ) := Subtype.val_injective
  -- the leading coefficient at `i∞`, read from `P(j)`
  have h1 : (laurentQExpansion n fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)).leadingCoeff =
      algebraMap _ ℂ P.leadingCoeff := by
    rw [laurentQExpansion_nat_eval_cyclicIsogenyPolynomial_j, LaurentSeries.leadingCoeff_expand,
      ← funext hP, laurentQExpansion_aeval_j, ← eval₂_map, LaurentSeries.leadingCoeff_eval₂_C hLo,
      leadingCoeff_map_of_injective hinj, leadingCoeff_laurentQExpansion_j, one_pow, mul_one]
  -- the leading coefficient at `i∞`, read from the product over the cyclic `n`-isogenies
  choose w hw using fun (A : FixedDetMatrix (Fin 2) ℤ n) (hA : A ∈ primitiveReps (n : ℤ)) ↦
    exists_units_eq_leadingCoeff hn (hreps hA)
  have h2 : (laurentQExpansion n fun τ ↦ (cyclicIsogenyPolynomial n j τ).eval (j τ)).leadingCoeff =
      algebraMap _ ℂ ((∏ A ∈ (primitiveReps (n : ℤ)).attach, w A.val A.property :
        (integralClosure ℤ ℂ)ˣ) : integralClosure ℤ ℂ) := by
    rw [eval_cyclicIsogenyPolynomial_j_eq_prod, laurentQExpansion_prod fun A hA ↦
      meromorphicAt_cuspFunction_sub_j_toGLReal_smul (hreps hA), hahnSeries_leadingCoeff_prod,
      ← Finset.prod_attach, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun A _ ↦ ?_
    rw [laurentQExpansion_sub_j_toGLReal_smul (hreps A.property), ← hw]
    rfl
  rw [hinj (h1.symm.trans h2)]
  exact Units.isUnit _

/-! ### Singular moduli -/

/-- If `j(A τ) = j(τ)` for a primitive integral matrix `A` of nonsquare determinant `n`, then
`j(τ)` is an algebraic integer: it is a root of `Φ_n(X, X)`, whose leading coefficient is a unit
of the algebraic integers. -/
theorem isIntegral_j_of_isPrimitive (hn : ¬ IsSquare n) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : IsPrimitive A.val) {τ : ℍ} (hτ : j (toGLReal (NeZero.ne (n : ℤ)) A • τ) = j τ) :
    IsIntegral ℤ (j τ) := by
  obtain ⟨P, hP⟩ := exists_aeval_j_eq_eval_cyclicIsogenyPolynomial n
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_of_aeval_j_eq_eval_cyclicIsogenyPolynomial hn hP
  have hroot : aeval (j τ) P = 0 := by
    rw [hP, ← hτ]
    exact isRoot_cyclicIsogenyPolynomial j_smul_SL2Z hA τ
  have hint : IsIntegral (integralClosure ℤ ℂ) (j τ) :=
    ⟨P * C ↑u⁻¹, monic_mul_C_of_leadingCoeff_mul_eq_one (by rw [← hu, Units.mul_inv]), by
      rw [← aeval_def, map_mul, hroot, zero_mul]⟩
  exact isIntegral_trans _ hint

/-- The `n` for the singular modulus argument: with `x = 1 + a (|b| + 4 a c - b ^ 2)`, the matrix
`(x - b, -c; a, x)` fixes `τ`, and its determinant `x ^ 2 - b x + a c` is positive and not a
perfect square. -/
private theorem not_isSquare_det {a b c x : ℤ} (hD : 0 < 4 * a * c - b ^ 2) (ha : 0 < a)
    (hx : x = 1 + a * (|b| + (4 * a * c - b ^ 2))) :
    0 < x * x - b * x + a * c ∧ ∀ s : ℤ, x * x - b * x + a * c ≠ s * s := by
  set D := 4 * a * c - b ^ 2
  have hy : D < 2 * x - b := by
    have : |b| + D ≤ a * (|b| + D) := le_mul_of_one_le_left (by positivity) ha
    have := neg_abs_le b
    have := le_abs_self b
    have := abs_nonneg b
    omega
  refine ⟨by nlinarith, fun s hs ↦ ?_⟩
  -- `4 s ^ 2 = (2 x - b) ^ 2 + D` with `0 < D < 2 x - b` has no solution
  have h4 : (2 * |s|) * (2 * |s|) = (2 * x - b) * (2 * x - b) + D := by
    rw [show (2 * |s|) * (2 * |s|) = 4 * (s * s) by rw [← abs_mul_abs_self s]; ring, ← hs]
    ring
  rcases le_or_gt (2 * |s|) (2 * x - b) with hle | hgt
  · nlinarith [abs_nonneg s]
  · nlinarith

/-- **Singular moduli are algebraic integers.** If `τ` in the upper half-plane satisfies an
integral quadratic equation `a τ² + b τ + c = 0` with `a ≠ 0`, that is, if `τ` is an imaginary
quadratic number, then `j(τ)` is an algebraic integer. -/
theorem isIntegral_j_of_quadratic {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) : IsIntegral ℤ (j τ) := by
  wlog ha' : 0 < a generalizing a b c
  · exact this (a := -a) (b := -b) (c := -c) (neg_ne_zero.mpr ha)
      (by push_cast; linear_combination -hτ) (by omega)
  have hD : 0 < 4 * a * c - b ^ 2 := by
    have := BinaryQuadraticForm.discrim_neg_of_quadratic_upperHalfPlane ha hτ
    rw [BinaryQuadraticForm.discrim_def, discrim] at this
    linarith
  set x := 1 + a * (|b| + (4 * a * c - b ^ 2)) with hx
  obtain ⟨hpos, hsq⟩ := not_isSquare_det hD ha' hx
  set N := x * x - b * x + a * c
  have : NeZero N.toNat := ⟨by omega⟩
  have hN : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hpos.le
  let M : FixedDetMatrix (Fin 2) ℤ N.toNat :=
    ⟨!![x - b, -c; a, x], by rw [Matrix.det_fin_two_of, hN]; ring⟩
  have hM : IsPrimitive M.val := by
    refine isPrimitive_def.2 ⟨-(|b| + (4 * a * c - b ^ 2)) •
      (Matrix.entryAddMonoidHom ℤ 1 0).toIntLinearMap +
        (Matrix.entryAddMonoidHom ℤ 1 1).toIntLinearMap, ?_⟩
    simp [M, hx]
    ring
  have hfix : toGLReal (NeZero.ne ((N.toNat : ℕ) : ℤ)) M • τ = τ := by
    have hdet : 0 < (toGLReal (NeZero.ne ((N.toNat : ℕ) : ℤ)) M).det.val := by
      rw [det_toGLReal]
      exact_mod_cast hpos.trans_eq hN.symm
    have hden : (a : ℂ) * τ + x ≠ 0 := by
      intro h0
      have := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
        zero_mul, add_zero, Complex.zero_im] at this
      exact (mul_pos (by exact_mod_cast ha' : (0 : ℝ) < a) τ.im_pos).ne' this
    ext
    rw [coe_smul_of_det_pos hdet]
    simp only [num, denom, toGLReal_apply]
    simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [div_eq_iff hden]
    linear_combination -hτ
  refine isIntegral_j_of_isPrimitive (fun ⟨r, hr⟩ ↦ hsq r ?_) hM (by rw [hfix])
  rw [← hN, hr]
  push_cast
  ring

end TauCeti.ModularForm

open TauCeti.ModularForm in
/-- The value of `j` at the root `τ = (-b + i √D) / (2 a)` of a positive definite integral form
`a x² + b x y + c y²` is an algebraic integer. -/
theorem TauCeti.BinaryQuadraticForm.isIntegral_j_root {D : ℕ} [NeZero D] (f : posDef D) :
    IsIntegral ℤ (j (root f)) :=
  isIntegral_j_of_quadratic (mem_posDef.1 f.property).2.ne' ((eq_root_iff f _).1 rfl)

namespace TauCeti.BinaryQuadraticForm

variable {n : ℕ} [NeZero n]

/-- **The singular moduli of discriminant `-n` are algebraic integers.** -/
theorem isIntegral_singularModulus (q : PosDefProperClass n) :
    IsIntegral ℤ (singularModulus n q) := by
  induction q using Quotient.inductionOn with
  | h f =>
    rw [singularModulus_mk]
    exact isIntegral_j_root _

/-- **The Hilbert class polynomial has algebraic integer coefficients**, as it is the product of
`X - j(τ)` over singular moduli `j(τ)`, which are algebraic integers. -/
theorem isIntegral_coeff_hilbertClassPolynomial (k : ℕ) :
    IsIntegral ℤ ((hilbertClassPolynomial n).coeff k) := by
  have := Fintype.ofFinite (PosDefProperClass n)
  set P : (integralClosure ℤ ℂ)[X] :=
    ∏ q : PosDefProperClass n, (X - C ⟨_, isIntegral_singularModulus q⟩)
  have hP : P.map (algebraMap (integralClosure ℤ ℂ) ℂ) = hilbertClassPolynomial n := by
    simp [P, hilbertClassPolynomial_eq_prod, Polynomial.map_prod]
  rw [← hP, coeff_map]
  exact (P.coeff k).property

end TauCeti.BinaryQuadraticForm
