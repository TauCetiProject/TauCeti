/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.BasedChart.Exchange
public import TauCeti.Algebra.Cluster.BasedChart.OrderedProduct
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Sharpness and worked examples for ordered chart products and one-step exchange

Over `B = LaurentRing ℚ Unit` with integer coefficient subsemiring `intSubsemiring = ℤ` and
coordinate `X = LaurentRing.unitX ()`, exchanging `X` against a nonzero integer scalar `d` (`y =
d * X⁻¹`) requires every negative Laurent coefficient `a * X^{-s}` (`s > 0`) in `ℤ[y^{±1}]` to
be divisible by `d ^ s` in `ℤ` (`intCast_mul_zpow_neg_mem_laurentAdjoin_iff`). In particular, when
`d` is not a unit in `ℤ`, `X⁻¹` lies outside `ℤ[(d * X⁻¹)^{±1}]`
(`inv_unitX_notMem_laurentAdjoin_of_not_isUnit`), witnessing sharpness of the divisibility
criterion `Subsemiring.mem_laurentAdjoin_mul_inv_iff`.

Additional `example` blocks verify the rank-`2` quantum ordered-product formula for
`!![0, 1; -1, 0]` and the length-`2` quantum binomial exchange product
`exchangeProduct x (1 + z) 2 = (1 + z) * (1 + v^{-2} • z)`.
-/

public section

open scoped Pointwise

namespace TauCeti.OneExchange.Examples

/-- The integer scalar subsemiring inside the rational single-variable Laurent ring
`LaurentRing ℚ Unit`. -/
noncomputable def intSubsemiring : Subsemiring (LaurentRing ℚ Unit) :=
  (algebraMap ℤ (LaurentRing ℚ Unit)).rangeS

/-- The ambient unit in `LaurentRing ℚ Unit` corresponding to a nonzero rational scalar `q`. -/
noncomputable def ratUnit {q : ℚ} (hq : q ≠ 0) : (LaurentRing ℚ Unit)ˣ :=
  Units.map (algebraMap ℚ (LaurentRing ℚ Unit)).toMonoidHom (Units.mk0 q hq)

private theorem algebraMap_int_laurentRing_unit (z : ℤ) :
    algebraMap ℤ (LaurentRing ℚ Unit) z = AddMonoidAlgebra.single 0 (z : ℚ) := by
  rw [IsScalarTower.algebraMap_apply ℤ ℚ (LaurentRing ℚ Unit), eq_intCast,
    Algebra.algebraMap_eq_smul_one, AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single',
    mul_one]

/-- Left Laurent expansions over `intSubsemiring` in `LaurentRing.unitX ()` have unique
coefficients. -/
theorem skewLaurentSum_intSubsemiring_unitX_injective :
    Function.Injective (intSubsemiring.skewLaurentSum (LaurentRing.unitX ())) := by
  let X := LaurentRing.unitX (R := ℚ) ()
  have heval (f : ℤ →₀ intSubsemiring) (m : ℤ) :
      (intSubsemiring.skewLaurentSum X f).coeff (Finsupp.single () m) =
        ((f m : intSubsemiring) : LaurentRing ℚ Unit).coeff 0 := by
    have hcoeff : (intSubsemiring.skewLaurentSum X f).coeff =
        f.sum fun k c ↦
          Finsupp.single (Finsupp.single () k) ((c : LaurentRing ℚ Unit).coeff 0) := by
      rw [Subsemiring.skewLaurentSum_apply, Finsupp.sum, Finsupp.sum, AddMonoidAlgebra.coeff_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      obtain ⟨z, hz⟩ := (f k).property
      rw [← hz, algebraMap_int_laurentRing_unit z, LaurentRing.val_unitX_zpow () k,
        AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
      simp
    rw [hcoeff]
    exact Finsupp.sum_single_apply_of_injective f (Finsupp.single_injective ())
      (fun _ c ↦ (c : LaurentRing ℚ Unit).coeff 0) rfl
  intro f₁ f₂ h
  ext m
  have hm := congrArg (fun p : LaurentRing ℚ Unit ↦ p.coeff (Finsupp.single () m)) h
  rw [heval, heval] at hm
  obtain ⟨z₁, hz₁⟩ := (f₁ m).property
  obtain ⟨z₂, hz₂⟩ := (f₂ m).property
  have hz : z₁ = z₂ := Int.cast_injective (α := ℚ)
    (by rw [← hz₁, ← hz₂, algebraMap_int_laurentRing_unit, algebraMap_int_laurentRing_unit] at hm
        simpa using hm)
  rw [← hz₁, ← hz₂, hz]

/-- In `ℚ[X^{±1}]` over `ℤ`, a negative monomial `a * X^{-s}` (`s > 0`) lies in
`ℤ[(d * X⁻¹)^{±1}]` for nonzero `d : ℤ` if and only if `d ^ s ∣ a` in `ℤ`. -/
theorem intCast_mul_zpow_neg_mem_laurentAdjoin_iff {d : ℤ} (hd : (d : ℚ) ≠ 0) (a : ℤ) {s : ℕ}
    (hs : 0 < s) :
    (a : LaurentRing ℚ Unit) *
        ((LaurentRing.unitX () ^ (-(s : ℤ)) : (LaurentRing ℚ Unit)ˣ) : LaurentRing ℚ Unit) ∈
      intSubsemiring.laurentAdjoin (ratUnit hd * (LaurentRing.unitX ())⁻¹) ↔ d ^ s ∣ a := by
  let B := LaurentRing ℚ Unit
  let X : Bˣ := LaurentRing.unitX ()
  let E : Bˣ := ratUnit hd
  have hnorm (u : Bˣ) : ConjAct.toConjAct u • intSubsemiring = intSubsemiring := by
    ext
    simp [Subsemiring.mem_smul_pointwise_iff_exists, ConjAct.units_smul_def, mul_comm, mul_assoc]
  have hE_val : (E : B) = (d : B) := by simp [E, ratUnit]
  have hP (r : ℕ) : ((exchangeProduct X E r : Bˣ) : B) = (d : B) ^ r := by
    rw [exchangeProduct_eq_pow X E, Units.val_pow_eq_pow_val, hE_val]
  let ca : intSubsemiring := ⟨(a : B), a, map_intCast _ a⟩
  have hf : (a : B) * ((X ^ (-(s : ℤ)) : Bˣ) : B) =
      intSubsemiring.skewLaurentSum X (Finsupp.single (-(s : ℤ)) ca) := by simp [ca]
  rw [hf, Subsemiring.mem_laurentAdjoin_mul_inv_iff (hnorm X) (hnorm E)
    ⟨d, by rw [eq_intCast, hE_val]⟩ skewLaurentSum_intSubsemiring_unitX_injective]
  refine ⟨fun hall ↦ ?_, fun ⟨z, hz⟩ r _ ↦ ?_⟩
  · obtain ⟨⟨_, z, rfl⟩, hz⟩ := hall s hs
    rw [Finsupp.single_eq_same, hP] at hz
    have hev := congrArg (LaurentRing.aeval (R := ℚ) fun _ : Unit ↦ (1 : ℚˣ)) hz
    dsimp only [ca] at hev
    rw [map_intCast, map_mul, eq_intCast, map_intCast, map_pow, map_intCast] at hev
    exact ⟨z, mul_comm z (d ^ s) ▸ (by exact_mod_cast hev)⟩
  · subst hz
    by_cases hrs : r = s
    · subst hrs
      exact ⟨⟨(z : B), z, map_intCast _ z⟩, by
        rw [Finsupp.single_eq_same, hP]
        dsimp only [ca]
        push_cast
        exact mul_comm (d ^ r : B) (z : B)⟩
    · exact ⟨0, by simp [Finsupp.single_eq_of_ne (by omega : -(r : ℤ) ≠ -(s : ℤ))]⟩

/-- When a nonzero integer `d` is not a unit in `ℤ`, `X⁻¹` does not belong to
`ℤ[(d * X⁻¹)^{±1}]`. -/
theorem inv_unitX_notMem_laurentAdjoin_of_not_isUnit {d : ℤ} (hd : (d : ℚ) ≠ 0)
    (hdu : ¬ IsUnit d) :
    (((LaurentRing.unitX ())⁻¹ : (LaurentRing ℚ Unit)ˣ) : LaurentRing ℚ Unit) ∉
      intSubsemiring.laurentAdjoin (ratUnit hd * (LaurentRing.unitX ())⁻¹) := by
  intro h
  have hx1 : (((LaurentRing.unitX ())⁻¹ : (LaurentRing ℚ Unit)ˣ) : LaurentRing ℚ Unit) =
      (1 : ℤ) * ((LaurentRing.unitX () ^ (-((1 : ℕ) : ℤ)) : (LaurentRing ℚ Unit)ˣ) :
        LaurentRing ℚ Unit) := by
    rw [Int.cast_one, one_mul, Nat.cast_one, zpow_neg_one]
  rw [hx1] at h
  have hdvd : d ^ 1 ∣ 1 :=
    (intCast_mul_zpow_neg_mem_laurentAdjoin_iff hd 1 (by omega)).mp h
  exact hdu (isUnit_of_dvd_one (by simpa using hdvd))

/-- Concrete `d = 2` check: `2 * X⁻¹` and `4 * X⁻²` lie in `ℤ[X^{±1}] ⊓ ℤ[(2 * X⁻¹)^{±1}]`, while
`X⁻¹` and `2 * X⁻²` lie outside `ℤ[(2 * X⁻¹)^{±1}]`. -/
example :
    let B := LaurentRing ℚ Unit
    let X : Bˣ := LaurentRing.unitX ()
    let E : Bˣ := ratUnit (q := 2) (by norm_num)
    (2 : B) * ((X⁻¹ : Bˣ) : B) ∈ intSubsemiring.laurentAdjoin X ⊓
        intSubsemiring.laurentAdjoin (E * X⁻¹) ∧
      (4 : B) * ((X ^ (-2 : ℤ) : Bˣ) : B) ∈ intSubsemiring.laurentAdjoin X ⊓
        intSubsemiring.laurentAdjoin (E * X⁻¹) ∧
      ((X⁻¹ : Bˣ) : B) ∉ intSubsemiring.laurentAdjoin (E * X⁻¹) ∧
      (2 : B) * ((X ^ (-2 : ℤ) : Bˣ) : B) ∉ intSubsemiring.laurentAdjoin (E * X⁻¹) := by
  intro B X E
  have hd : ((2 : ℤ) : ℚ) ≠ 0 := by norm_num
  have hx1 : ((X⁻¹ : Bˣ) : B) = ((X ^ (-((1 : ℕ) : ℤ)) : Bˣ) : B) := by
    rw [Nat.cast_one, zpow_neg_one]
  refine ⟨Subsemiring.mem_inf.mpr ⟨mul_mem (intSubsemiring.le_laurentAdjoin X ⟨2, map_ofNat _ 2⟩)
      (intSubsemiring.coe_inv_mem_laurentAdjoin X), hx1 ▸
        (intCast_mul_zpow_neg_mem_laurentAdjoin_iff hd 2 (s := 1) (by omega)).mpr ⟨1, by ring⟩⟩,
    Subsemiring.mem_inf.mpr ⟨mul_mem (intSubsemiring.le_laurentAdjoin X ⟨4, map_ofNat _ 4⟩)
      (intSubsemiring.coe_zpow_mem_laurentAdjoin X (-2)),
        (intCast_mul_zpow_neg_mem_laurentAdjoin_iff hd 4 (s := 2) (by omega)).mpr ⟨1, by ring⟩⟩,
    inv_unitX_notMem_laurentAdjoin_of_not_isUnit hd (by decide),
    fun h ↦ ?_⟩
  obtain ⟨z, hz⟩ := (intCast_mul_zpow_neg_mem_laurentAdjoin_iff hd 2 (s := 2) (by omega)).mp h
  omega

/-- Rank-2 ordered-product check for exponent `(-1, 2)` and skew matrix `!![0, 1; -1, 0]`:
`M(-e_0 + 2 e_1) = u^2 • (X_0⁻¹ * X_1^2)`. -/
example {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B] {u : Rˣ}
    (M : BasedChart u (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ).finsuppBilinForm B) :
    M.monomial (-Finsupp.single 0 1 + 2 • Finsupp.single 1 1) =
      Units.map (algebraMap R B) (u ^ 2) *
        ((M.coordinate Finsupp.basisSingleOne 0)⁻¹ *
          M.coordinate Finsupp.basisSingleOne 1 ^ 2) := by
  set a : Fin 2 →₀ ℤ := -Finsupp.single 0 1 + 2 • Finsupp.single 1 1
  have hsort : (Finset.univ : Finset (Fin 2)).sort (· ≤ ·) = [0, 1] := by
    have huniv : ([0, 1] : List (Fin 2)).toFinset = Finset.univ := by decide
    rw [← huniv]
    exact (List.toFinset_sort (r := (· ≤ ·)) (by decide)).mpr (by decide)
  rw [M.monomial_eq_orderedMonomial (fun i ↦ by fin_cases i <;> rfl) a, orderedMonomial_def,
    orderedCoordProd_eq_univ_sort, hsort, Matrix.finsuppBilinForm_apply_eq_dotProduct]
  have ha : a 0 = -1 ∧ a 1 = 2 := by simp [a]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, ha.1, ha.2]

/-- Quantum `r = 2` exchange-product check: if `x * z = v^2 • (z * x)` and `E = 1 + z`, then
`exchangeProduct x E 2 = (1 + z) * (1 + v^{-2} • z)`. -/
example {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]
    {v : Rˣ} {x E : Bˣ} {z : B}
    (hxz : (x : B) * z = algebraMap R B ((v ^ 2 : Rˣ) : R) * (z * (x : B)))
    (hE : (E : B) = 1 + z) :
    ((exchangeProduct x E 2 : Bˣ) : B) =
      (1 + z) * (1 + algebraMap R B ((v ^ (-2 : ℤ) : Rˣ) : R) * z) := by
  have hconj : ((x⁻¹ : Bˣ) : B) * z * (x : B) = algebraMap R B ((v ^ (-2 : ℤ) : Rˣ) : R) * z := by
    simpa [zpow_neg] using Units.inv_mul_mul_of_mul_eq_algebraMap_mul hxz
  rw [exchangeProduct_two, Units.val_mul, Units.val_mul, Units.val_mul, hE]
  congr 1
  rw [mul_add, mul_one, add_mul, Units.inv_mul, hconj]

end TauCeti.OneExchange.Examples
