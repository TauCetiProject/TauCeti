/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.NumberTheory.Padics.AnnularRing.Presentation
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import TauCeti.Algebra.Order.Archimedean.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Local structure and boundary quotient of `ℤ_p⟦T, p/T⟧`

Building on the presentation `TauCeti.AnnularRing.ofMvPowerSeries` from
`TauCeti.NumberTheory.Padics.AnnularRing.Presentation`, the `U`-coefficients `uCoeff x n`
(`p ^ n * uCoeff x n = x.coeff (-n)`) yield
`quotientSpanTEquiv : AnnularRing p ⧸ (T) ≃+* (ZMod p)⟦X⟧`, `isPrime_span_T`,
`residueTU : AnnularRing p →+* ZMod p`, and `maximalIdeal_eq_span_T_U`.

## References
* R. Liu, D. Wan and L. Xiao, *The eigencurve over the boundary of weight space*, Duke Math. J.
  166 (2017), §§2–3.
-/

public noncomputable section

open Filter Topology PowerSeries

namespace TauCeti.AnnularRing

variable {p : ℕ} [Fact p.Prime]
private theorem one_lt_p : (1 : ℝ) < p := mod_cast (Fact.out : p.Prime).one_lt
private theorem p_ne_zero : (p : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero

/-! ### `U`-coefficients, boundary quotient `AnnularRing p ⧸ (T)`, and local structure -/

private theorem exists_eq_ofPowerSeriesU_add_T_mul (x : AnnularRing p) :
    ∃ g : ℤ_[p]⟦X⟧, ∃ z : AnnularRing p, x = ofPowerSeriesU g + T * z := by
  obtain ⟨⟨f, g⟩, rfl⟩ := normalForm.surjective x; refine ⟨C (constantCoeff f) + X * g,
    ofPowerSeriesT (PowerSeries.mk fun n ↦ PowerSeries.coeff (n + 1) f), ?_⟩
  (conv_lhs => rw [normalForm_apply, eq_X_mul_shift_add_const f]); simp only [map_add, map_mul,
    ofPowerSeriesT_X, ofPowerSeriesU_X, C_eq_algebraMap, AlgHom.commutes]; ring

/-- The `n`-th `U`-coefficient of `x`, satisfying `p ^ n * uCoeff x n = x.coeff (-n)`. -/
def uCoeff (x : AnnularRing p) (n : ℕ) : ℤ_[p] := (x.pow_dvd_coeff_neg n).choose
@[simp] theorem pow_mul_uCoeff (x : AnnularRing p) (n : ℕ) :
    (p : ℤ_[p]) ^ n * uCoeff x n = x.coeff (-n) := (x.pow_dvd_coeff_neg n).choose_spec.symm
/-- Uniqueness of `uCoeff`: if `p ^ n * c = x.coeff (-n)`, then `uCoeff x n = c`. -/
theorem uCoeff_eq_of_mul_eq {x : AnnularRing p} {n : ℕ} {c : ℤ_[p]}
    (h : (p : ℤ_[p]) ^ n * c = x.coeff (-n)) : uCoeff x n = c :=
  mul_left_cancel₀ (pow_ne_zero n (p_ne_zero (p := p))) ((pow_mul_uCoeff x n).trans h.symm)
@[simp] theorem uCoeff_zero_right (x : AnnularRing p) : uCoeff x 0 = x.coeff 0 := by
  simpa using pow_mul_uCoeff x 0
@[simp] theorem uCoeff_zero (n : ℕ) :
    uCoeff (0 : AnnularRing p) n = 0 := uCoeff_eq_of_mul_eq (by simp)
@[simp] theorem uCoeff_one (n : ℕ) : uCoeff (1 : AnnularRing p) n = if n = 0 then 1 else 0 :=
  uCoeff_eq_of_mul_eq (by rw [coeff_one]; by_cases hn : n = 0 <;> simp [hn])
@[simp] theorem uCoeff_add (x y : AnnularRing p) (n : ℕ) :
    uCoeff (x + y) n = uCoeff x n + uCoeff y n :=
  uCoeff_eq_of_mul_eq (by rw [mul_add, pow_mul_uCoeff, pow_mul_uCoeff, coeff_add])
@[simp] theorem uCoeff_smul (c : ℤ_[p]) (x : AnnularRing p) (n : ℕ) :
    uCoeff (c • x) n = c * uCoeff x n :=
  uCoeff_eq_of_mul_eq (by rw [mul_left_comm, pow_mul_uCoeff, coeff_smul])
@[simp] theorem uCoeff_ofPowerSeriesU (g : ℤ_[p]⟦X⟧) (n : ℕ) :
    uCoeff (ofPowerSeriesU g) n = PowerSeries.coeff n g :=
  uCoeff_eq_of_mul_eq (coeff_ofPowerSeriesU_neg_natCast g n).symm
@[simp] theorem uCoeff_T (n : ℕ) : uCoeff (T : AnnularRing p) n = 0 :=
  uCoeff_eq_of_mul_eq (by rw [coeff_T, ite_eq_right (by omega), mul_zero])
/-- Multiplication by `T` shifts `uCoeff` up by one index and multiplies by `p`. -/
@[simp] theorem uCoeff_T_mul (y : AnnularRing p) (n : ℕ) :
    uCoeff (T * y) n = (p : ℤ_[p]) * uCoeff y (n + 1) := uCoeff_eq_of_mul_eq <| by
  rw [coeff_T_mul, show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega, ← pow_mul_uCoeff, pow_succ,
    mul_assoc]
@[simp] theorem uCoeff_U (n : ℕ) : uCoeff (U : AnnularRing p) n = if n = 1 then 1 else 0 :=
  uCoeff_eq_of_mul_eq (by rw [coeff_U]; by_cases hn : n = 1 <;> simp [hn])

/-- `uCoeff (ofPowerSeriesU (PowerSeries.mk 1))` is constantly `1`, so it does not tend to `0`. -/
theorem not_tendsto_uCoeff_ofPowerSeriesU_mk_one :
    ¬ Tendsto (uCoeff (ofPowerSeriesU (PowerSeries.mk 1 : ℤ_[p]⟦X⟧))) atTop (𝓝 0) := by
  rw [show uCoeff (ofPowerSeriesU (PowerSeries.mk 1 : ℤ_[p]⟦X⟧)) = fun _ ↦ 1 from
    funext fun _ ↦ by simp, tendsto_const_nhds_iff]; exact one_ne_zero

private theorem uCoeff_ofPowerSeriesT_mul_U_pow_of_lt (f : ℤ_[p]⟦X⟧) {k n : ℕ} (hk : k < n) :
    uCoeff (ofPowerSeriesT f * U ^ k) n = 0 := uCoeff_eq_of_mul_eq <| by
  rw [mul_comm (ofPowerSeriesT f), coeff_mul_of_coeff_eq_zero (k := -(k : ℤ)) fun i hi ↦ by
    rw [coeff_U_pow, ite_eq_right hi], coeff_ofPowerSeriesT_of_neg f (by omega)]; simp

private theorem uCoeff_eval₂_of_natDegree_lt (P : Polynomial (ℤ_[p]⟦X⟧)) {n : ℕ}
    (hn : P.natDegree < n) : uCoeff (P.eval₂ ofPowerSeriesT.toRingHom U) n = 0 := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact (map_sum (AddMonoidHom.mk' (uCoeff · n) (uCoeff_add · · n)) _ _).trans
    (Finset.sum_eq_zero fun k hk ↦
      uCoeff_ofPowerSeriesT_mul_U_pow_of_lt _ ((Finset.mem_range.1 hk).trans_le hn))

/-- Elements `x` approximable mod every `p ^ N` by `ℤ_p⟦T⟧[U]` satisfy `uCoeff x n → 0`. -/
theorem tendsto_uCoeff_of_forall_pow_dvd_eval₂ {x : AnnularRing p}
    (hx : ∀ N : ℕ, ∃ P : Polynomial (ℤ_[p]⟦X⟧),
      (p : AnnularRing p) ^ N ∣ x - P.eval₂ ofPowerSeriesT.toRingHom U) :
    Tendsto (uCoeff x) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := TauCeti.exists_zpow_neg_lt (one_lt_p (p := p)) hε
  obtain ⟨P, y, hy⟩ := hx N; refine ⟨P.natDegree + 1, fun n hn ↦ ?_⟩
  rw [dist_zero_right, show uCoeff x n = (p : ℤ_[p]) ^ N * uCoeff y n by
    rw [show x = P.eval₂ ofPowerSeriesT.toRingHom U + ((p : ℤ_[p]) ^ N : ℤ_[p]) • y by
        rw [Algebra.smul_def, map_pow, map_natCast, ← hy, add_sub_cancel],
      uCoeff_add, uCoeff_eval₂_of_natDegree_lt P (by omega), zero_add, uCoeff_smul]]
  exact ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).2
    (Ideal.mem_span_singleton.2 ⟨uCoeff y n, rfl⟩)).trans_lt hN

/-- `∑ U ^ n` is not approximable modulo every `p ^ N` by polynomials in `U` over `ℤ_p⟦T⟧`. -/
theorem not_forall_pow_dvd_ofPowerSeriesU_mk_one : ¬ ∀ N : ℕ, ∃ P : Polynomial (ℤ_[p]⟦X⟧),
    (p : AnnularRing p) ^ N ∣ ofPowerSeriesU (PowerSeries.mk 1 : ℤ_[p]⟦X⟧) -
      P.eval₂ ofPowerSeriesT.toRingHom U :=
  fun h ↦ not_tendsto_uCoeff_ofPowerSeriesU_mk_one (tendsto_uCoeff_of_forall_pow_dvd_eval₂ h)

private theorem norm_coeff_add_one_le {x : AnnularRing p}
    (h : ∀ n : ℕ, (p : ℤ_[p]) ∣ uCoeff x n) (m : ℤ) : ‖x.coeff (m + 1)‖ ≤ (p : ℝ) ^ min 0 m := by
  refine norm_le_zpow_min_iff_pow_dvd.2 ?_; rcases le_or_gt 0 m with hm | hm
  · simp [Int.toNat_of_nonpos (by omega : -m ≤ 0)]
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, m + 1 = -n := ⟨(-(m + 1)).toNat, by omega⟩
    obtain ⟨c, hc⟩ := h n
    exact ⟨c, by rw [show (-m).toNat = n + 1 by omega, pow_succ, mul_assoc, ← hc,
      pow_mul_uCoeff, ← hn]⟩

/-- `T ∣ x` iff `p ∣ uCoeff x n` for all `n : ℕ` (i.e. `‖x.coeff (-n)‖ ≤ p ^ -(n + 1)`). -/
theorem T_dvd_iff {x : AnnularRing p} :
    (T : AnnularRing p) ∣ x ↔ ∀ n : ℕ, (p : ℤ_[p]) ∣ uCoeff x n :=
  ⟨fun ⟨y, hy⟩ n ↦ ⟨uCoeff y (n + 1), hy ▸ uCoeff_T_mul y n⟩,
   fun h ↦ ⟨⟨fun m ↦ x.coeff (m + 1), norm_coeff_add_one_le h⟩, by ext m : 2; simp [coeff_T_mul]⟩⟩

private theorem toZMod_uCoeff_T_mul (z : AnnularRing p) (n : ℕ) :
    PadicInt.toZMod (uCoeff (T * z) n) = 0 :=
  (PadicInt.toZMod_eq_zero_iff_dvd _).2 (T_dvd_iff.1 (dvd_mul_right T z) n)

/-- Boundary reduction `AnnularRing p →+* (ZMod p)⟦X⟧` (`T ↦ 0`, `U ↦ X`). -/
def modT : AnnularRing p →+* (ZMod p)⟦X⟧ where
  toFun x := PowerSeries.mk fun n ↦ PadicInt.toZMod (uCoeff x n)
  map_zero' := by ext n; simp
  map_one' := by ext n; by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  map_add' x y := by ext n; simp
  map_mul' x y := by
    obtain ⟨gx, zx, rfl⟩ := exists_eq_ofPowerSeriesU_add_T_mul x
    obtain ⟨gy, zy, rfl⟩ := exists_eq_ofPowerSeriesU_add_T_mul y
    have hmap (g : ℤ_[p]⟦X⟧) (z : AnnularRing p) : (PowerSeries.mk fun n ↦
        PadicInt.toZMod (uCoeff (ofPowerSeriesU g + T * z) n)) = map PadicInt.toZMod g := by
      ext n; simp [-uCoeff_T_mul, toZMod_uCoeff_T_mul]
    rw [show (ofPowerSeriesU gx + T * zx) * (ofPowerSeriesU gy + T * zy) = ofPowerSeriesU (gx * gy)
      + T * (zx * ofPowerSeriesU gy + ofPowerSeriesU gx * zy + T * zx * zy) by rw [map_mul]; ring,
      hmap, hmap, hmap, map_mul]
@[simp] theorem coeff_modT (x : AnnularRing p) (n : ℕ) :
    PowerSeries.coeff n (modT x) = PadicInt.toZMod (uCoeff x n) := by simp [modT]
@[simp] theorem modT_T : modT (T : AnnularRing p) = 0 := by ext n; simp
@[simp] theorem modT_U : modT (U : AnnularRing p) = PowerSeries.X := by
  ext n; rw [coeff_modT, PowerSeries.coeff_X, uCoeff_U]; by_cases hn : n = 1 <;> simp [hn]
@[simp] theorem modT_ofPowerSeriesU (g : ℤ_[p]⟦X⟧) :
    modT (ofPowerSeriesU g) = PowerSeries.map PadicInt.toZMod g := by ext n; simp
/-- `modT` sends `c : ℤ_p` to the constant power series of its reduction modulo `p`. -/
@[simp] theorem modT_algebraMap (c : ℤ_[p]) :
    modT (algebraMap ℤ_[p] (AnnularRing p) c) = PowerSeries.C (PadicInt.toZMod c) := by
  rw [← ofPowerSeriesU.commutes c, modT_ofPowerSeriesU, ← C_eq_algebraMap, PowerSeries.map_C]
/-- The boundary reduction `modT : AnnularRing p →+* (ZMod p)⟦X⟧` is surjective. -/
theorem modT_surjective : Function.Surjective (modT (p := p)) := fun φ ↦
  ⟨ofPowerSeriesU (PowerSeries.mk fun n ↦ ((PowerSeries.coeff n φ).val : ℤ_[p])), by ext n; simp⟩

/-- The kernel of the boundary reduction `modT` is the principal ideal `(T)`. -/
theorem ker_modT : RingHom.ker (modT (p := p)) = Ideal.span {T} := by
  ext x; rw [RingHom.mem_ker, Ideal.mem_span_singleton, T_dvd_iff, PowerSeries.ext_iff]
  exact forall_congr' fun n ↦ by rw [coeff_modT, map_zero, PadicInt.toZMod_eq_zero_iff_dvd]

/-- Killing `T` (i.e. `(p, T)`) identifies `AnnularRing p ⧸ (T)` with `(ZMod p)⟦X⟧`. -/
def quotientSpanTEquiv : (AnnularRing p ⧸ Ideal.span {(T : AnnularRing p)}) ≃+* (ZMod p)⟦X⟧ :=
  (Ideal.quotEquivOfEq ker_modT.symm).trans (RingHom.quotientKerEquivOfSurjective modT_surjective)
@[simp] theorem quotientSpanTEquiv_mk (x : AnnularRing p) :
    quotientSpanTEquiv (Ideal.Quotient.mk _ x) = modT x := (rfl)

/-- `(T) = (p, T)` is prime in `AnnularRing p`, since `(ZMod p)⟦X⟧` is an integral domain. -/
theorem isPrime_span_T : (Ideal.span {(T : AnnularRing p)}).IsPrime :=
  (Ideal.Quotient.isDomain_iff_prime _).1 quotientSpanTEquiv.toMulEquiv.isDomain

instance : IsLocalRing (AnnularRing p) :=
  IsLocalRing.of_surjective' ofMvPowerSeries.toRingHom ofMvPowerSeries_surjective

/-- The residue homomorphism `AnnularRing p →+* ZMod p` sending `x ↦ x.coeff 0 mod p`. -/
def residueTU : AnnularRing p →+* ZMod p := (PowerSeries.constantCoeff (R := ZMod p)).comp modT
theorem residueTU_apply (x : AnnularRing p) : residueTU x = PadicInt.toZMod (x.coeff 0) := by
  simp [residueTU, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
@[simp] theorem residueTU_T : residueTU (T : AnnularRing p) = 0 := by
  simp [residueTU_apply, coeff_T]
@[simp] theorem residueTU_U : residueTU (U : AnnularRing p) = 0 := by
  simp [residueTU_apply, coeff_U]
@[simp] theorem residueTU_algebraMap (c : ℤ_[p]) :
    residueTU (algebraMap ℤ_[p] (AnnularRing p) c) = PadicInt.toZMod c := by simp [residueTU_apply]
/-- The residue homomorphism `residueTU : AnnularRing p →+* ZMod p` is surjective. -/
theorem residueTU_surjective : Function.Surjective (residueTU (p := p)) :=
  ZMod.ringHom_surjective residueTU
/-- The kernel of `residueTU` is the unique maximal ideal of the local ring `AnnularRing p`. -/
theorem ker_residueTU :
    RingHom.ker (residueTU (p := p)) = IsLocalRing.maximalIdeal (AnnularRing p) :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective residueTU residueTU_surjective)

/-- Unit criterion: `x ∈ AnnularRing p` is a unit iff its constant term `x.coeff 0` is a unit. -/
theorem isUnit_iff {x : AnnularRing p} : IsUnit x ↔ IsUnit (x.coeff 0) := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← ker_residueTU, RingHom.mem_ker, residueTU_apply,
    ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.notMem_maximalIdeal]
/-- `T` is not a unit in `AnnularRing p`, since its constant term is `0`. -/
@[simp] theorem not_isUnit_T : ¬ IsUnit (T : AnnularRing p) := by simp [isUnit_iff, coeff_T]
/-- `U` is not a unit in `AnnularRing p`, since its constant term is `0`. -/
@[simp] theorem not_isUnit_U : ¬ IsUnit (U : AnnularRing p) := by simp [isUnit_iff, coeff_U]
/-- The prime `p` is not a unit in `AnnularRing p`, since `p ∈ ℤ_p` is not a unit. -/
theorem not_isUnit_p : ¬ IsUnit (p : AnnularRing p) := by
  simpa [isUnit_iff, mem_nonunits_iff] using PadicInt.p_nonunit (p := p)

/-- The maximal ideal of `AnnularRing p` is `(T, U)` (containing `p = T U`). -/
theorem maximalIdeal_eq_span_T_U :
    IsLocalRing.maximalIdeal (AnnularRing p) = Ideal.span {T, U} := by
  rw [← ker_residueTU]; refine le_antisymm (fun x hx ↦ ?_) (Ideal.span_le.2 fun y hy ↦ ?_)
  · obtain ⟨c₀, hc₀⟩ := (PadicInt.toZMod_eq_zero_iff_dvd _).1 (by
      simpa [residueTU_apply] using RingHom.mem_ker.1 hx)
    obtain ⟨⟨f, g⟩, rfl⟩ := normalForm.surjective x
    rw [normalForm_apply, eq_X_mul_shift_add_const f, map_add, map_mul, ofPowerSeriesT_X,
      C_eq_algebraMap, AlgHom.commutes, show constantCoeff f = (p : ℤ_[p]) * c₀ by
        simpa [coeff_zero_eq_constantCoeff_apply] using
          (coeff_normalForm_natCast f g 0).symm.trans hc₀,
      map_mul, map_natCast, ← T_mul_U, mul_assoc]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rcases hy with rfl | rfl <;> simp [RingHom.mem_ker]

end TauCeti.AnnularRing
