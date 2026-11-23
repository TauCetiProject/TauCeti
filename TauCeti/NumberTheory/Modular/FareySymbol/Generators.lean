/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ConjJ
public import TauCeti.NumberTheory.Modular.FareySymbol.Basic
public import TauCeti.NumberTheory.Modular.Generators
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Modular
import Mathlib.Tactic.IntervalCases
import TauCeti.Analysis.Complex.UpperHalfPlane.Rho
import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.OrderOf
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Modular generators attached to a Farey symbol

To each side `(a / b, c / d)` of a Farey symbol `F` (`c * b - a * d = 1`) and each free-paired
couple of sides `(a / b, c / d)`, `(a' / b', c' / d')`, Kulkarni attaches determinant-one integral
matrices `evenGenerator`, `oddGenerator`, and `freeGenerator`, factored via `M = !![a, c; b, d]` as
`M · S · M⁻¹`, `M · !![1, -1; 1, 0] · M⁻¹`, `M' · S · M⁻¹`, or via `sideSL = !![-a, c; -b, d]` in
`SL(2, ℤ)` as `sideSL · S⁻¹ · sideSL⁻¹`, `sideSL · R⁻¹ · sideSL⁻¹`, `sideSL' · S⁻¹ · sideSL⁻¹`.

## Main definitions and results

* `TauCeti.FareySymbol.evenGenerator`, `TauCeti.FareySymbol.oddGenerator`,
  `TauCeti.FareySymbol.freeGenerator`: `2 × 2` integral side generator matrices.
* `TauCeti.FareySymbol.sideSL`, `TauCeti.FareySymbol.evenSL`, `TauCeti.FareySymbol.oddSL`,
  `TauCeti.FareySymbol.freeSL`: `SL(2, ℤ)` lifts, projective orders `2` and `3`, and `freeSL_inv`.
* `TauCeti.FareySymbol.cuspOfEndpoint`, `TauCeti.FareySymbol.evenFixedPoint`,
  `TauCeti.FareySymbol.oddFixedPoint`: `OnePoint ℚ` cusps and `ℍ` elliptic fixed points.
* `TauCeti.FareySymbol.isParabolic_coe_freeSideSL_iff`,
  `TauCeti.FareySymbol.isHyperbolic_coe_freeSideSL_iff`,
  `TauCeti.FareySymbol.not_isOfFinOrder_coe_freeSideSL`: parabolic/hyperbolic dichotomy.
* `TauCeti.FareySymbol.group`, `TauCeti.FareySymbol.group_translate`,
  `TauCeti.FareySymbol.group_reflect`, `TauCeti.FareySymbol.group_levelOne`,
  `TauCeti.FareySymbol.comap_group_gamma0Two`, `TauCeti.FareySymbol.comap_group_gammaTwo`.

## References

* R. S. Kulkarni, *An arithmetic-geometric method in the study of the subgroups of the modular
  group*, Amer. J. Math. **113** (1991), no. 6, 1053–1133, §§2–3.
* C. A. Kurth and L. Long, *Computations with finite index subgroups of `PSL₂(ℤ)` using Farey
  symbols*, in *Advances in Algebra and Combinatorics* (World Scientific, 2008), 225–242,
  `arXiv:0710.1835v1`, §3.3, Theorem 3.
-/

public section

open Matrix OnePoint
open scoped MatrixGroups UpperHalfPlane

namespace TauCeti.FareySymbol

/-! ### Integral side generator matrices -/

/-- The even generator matrix `M · S · M⁻¹` (`M = !![a, c; b, d]`) of a side `(a / b, c / d)`. -/
def evenGenerator (a b c d : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-(a * b + c * d), a ^ 2 + c ^ 2; -(b ^ 2 + d ^ 2), a * b + c * d]
theorem evenGenerator_def (a b c d : ℤ) : evenGenerator a b c d =
    !![-(a * b + c * d), a ^ 2 + c ^ 2; -(b ^ 2 + d ^ 2), a * b + c * d] := (rfl)

/-- The odd generator matrix `M · !![1, -1; 1, 0] · M⁻¹` of a side `(a / b, c / d)`. -/
def oddGenerator (a b c d : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-(a * b + a * d + c * d), a ^ 2 + a * c + c ^ 2;
     -(b ^ 2 + b * d + d ^ 2), a * b + b * c + c * d]
theorem oddGenerator_def (a b c d : ℤ) : oddGenerator a b c d =
    !![-(a * b + a * d + c * d), a ^ 2 + a * c + c ^ 2;
       -(b ^ 2 + b * d + d ^ 2), a * b + b * c + c * d] := (rfl)

/-- The free generator matrix `M' · S · M⁻¹` pairing `(a / b, c / d)` and `(a' / b', c' / d')`. -/
def freeGenerator (a b c d a' b' c' d' : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-(a' * b + c' * d), a * a' + c * c'; -(b * b' + d * d'), a * b' + c * d']
theorem freeGenerator_def (a b c d a' b' c' d' : ℤ) : freeGenerator a b c d a' b' c' d' =
    !![-(a' * b + c' * d), a * a' + c * c'; -(b * b' + d * d'), a * b' + c * d'] := (rfl)

@[simp] theorem trace_evenGenerator (a b c d : ℤ) : (evenGenerator a b c d).trace = 0 := by
  simp [evenGenerator, Matrix.trace_fin_two]
@[simp] theorem det_evenGenerator (a b c d : ℤ) :
    (evenGenerator a b c d).det = (c * b - a * d) ^ 2 := by
  simp [evenGenerator, Matrix.det_fin_two]; ring
@[simp] theorem trace_oddGenerator (a b c d : ℤ) :
    (oddGenerator a b c d).trace = c * b - a * d := by
  simp [oddGenerator, Matrix.trace_fin_two]; ring
@[simp] theorem det_oddGenerator (a b c d : ℤ) :
    (oddGenerator a b c d).det = (c * b - a * d) ^ 2 := by
  simp [oddGenerator, Matrix.det_fin_two]; ring
@[simp] theorem trace_freeGenerator (a b c d a' b' c' d' : ℤ) :
    (freeGenerator a b c d a' b' c' d').trace = a * b' + c * d' - a' * b - c' * d := by
  simp [freeGenerator, Matrix.trace_fin_two]; ring
@[simp] theorem det_freeGenerator (a b c d a' b' c' d' : ℤ) :
    (freeGenerator a b c d a' b' c' d').det = (c * b - a * d) * (c' * b' - a' * d') := by
  simp [freeGenerator, Matrix.det_fin_two]; ring
@[simp] theorem freeGenerator_self (a b c d : ℤ) :
    freeGenerator a b c d a b c d = evenGenerator a b c d := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [freeGenerator, evenGenerator, sq]

/-- Factorization `M · S · (-adjugate M) = evenGenerator a b c d` for `M = !![a, c; b, d]`. -/
theorem evenGenerator_eq_mul_S_mul_neg_adjugate (a b c d : ℤ) : evenGenerator a b c d =
    !![a, c; b, d] * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * -adjugate !![a, c; b, d] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenGenerator, ModularGroup.coe_S, Matrix.adjugate_fin_two] <;> ring
/-- Factorization `M · !![1, -1; 1, 0] · (-adjugate M) = oddGenerator a b c d`. -/
theorem oddGenerator_eq_mul_mul_neg_adjugate (a b c d : ℤ) :
    oddGenerator a b c d = !![a, c; b, d] * !![1, -1; 1, 0] * -adjugate !![a, c; b, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [oddGenerator, Matrix.adjugate_fin_two] <;> ring
/-- Factorization `M' · S · (-adjugate M) = freeGenerator a b c d a' b' c' d'`. -/
theorem freeGenerator_eq_mul_S_mul_neg_adjugate (a b c d a' b' c' d' : ℤ) :
    freeGenerator a b c d a' b' c' d' = !![a', c'; b', d'] *
      (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * -adjugate !![a, c; b, d] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [freeGenerator, ModularGroup.coe_S, Matrix.adjugate_fin_two] <;> ring

/-! ### Unimodular `SL(2, ℤ)` lifts and projective orders -/

/-- Positive-determinant lift `!![-a, c; -b, d] ∈ SL(2, ℤ)` mapping `(∞, 0)` to `(a / b, c / d)`. -/
def sideSL {a b c d : ℤ} (h : c * b - a * d = 1) : SL(2, ℤ) :=
  .mk !![-a, c; -b, d] (by simp [Matrix.det_fin_two]; linarith)
@[simp] theorem coe_sideSL {a b c d : ℤ} (h : c * b - a * d = 1) :
    (sideSL h : Matrix (Fin 2) (Fin 2) ℤ) = !![-a, c; -b, d] := (rfl)

/-- `S⁻¹` is the positive-determinant lift `sideSL` of the side `(0 / 1, 1 / 0)`. -/
theorem S_inv_eq_sideSL :
    ModularGroup.S⁻¹ = sideSL (a := 0) (b := 1) (c := 1) (d := 0) (by ring) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sideSL, ModularGroup.coe_S]
/-- `R⁻¹` is the positive-determinant lift `sideSL` of the side `(-1 / 1, 1 / 0)`. -/
theorem R_inv_eq_sideSL :
    TauCeti.ModularGroup.R⁻¹ = sideSL (a := -1) (b := 1) (c := 1) (d := 0) (by ring) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sideSL, TauCeti.ModularGroup.coe_R]

/-- The `SL(2, ℤ)` lift of `evenGenerator` on a unimodular side `c * b - a * d = 1`. -/
def evenSL {a b c d : ℤ} (h : c * b - a * d = 1) : SL(2, ℤ) :=
  .mk (evenGenerator a b c d) (by rw [det_evenGenerator, h, one_pow])
@[simp] theorem coe_evenSL {a b c d : ℤ} (h : c * b - a * d = 1) :
    (evenSL h : Matrix (Fin 2) (Fin 2) ℤ) = evenGenerator a b c d := (rfl)
/-- The `SL(2, ℤ)` lift of `oddGenerator` on a unimodular side `c * b - a * d = 1`. -/
def oddSL {a b c d : ℤ} (h : c * b - a * d = 1) : SL(2, ℤ) :=
  .mk (oddGenerator a b c d) (by rw [det_oddGenerator, h, one_pow])
@[simp] theorem coe_oddSL {a b c d : ℤ} (h : c * b - a * d = 1) :
    (oddSL h : Matrix (Fin 2) (Fin 2) ℤ) = oddGenerator a b c d := (rfl)
/-- The `SL(2, ℤ)` lift of `freeGenerator` on two unimodular sides. -/
def freeSL {a b c d a' b' c' d' : ℤ} (h : c * b - a * d = 1)
    (h' : c' * b' - a' * d' = 1) : SL(2, ℤ) :=
  .mk (freeGenerator a b c d a' b' c' d') (by rw [det_freeGenerator, h, h', mul_one])
@[simp] theorem coe_freeSL {a b c d a' b' c' d' : ℤ} (h : c * b - a * d = 1)
    (h' : c' * b' - a' * d' = 1) :
    (freeSL h h' : Matrix (Fin 2) (Fin 2) ℤ) = freeGenerator a b c d a' b' c' d' := (rfl)

/-- Conjugation factorization `evenSL h = sideSL h · S⁻¹ · (sideSL h)⁻¹` in `SL(2, ℤ)`. -/
theorem evenSL_eq_conj_S_inv {a b c d : ℤ} (h : c * b - a * d = 1) :
    evenSL h = sideSL h * ModularGroup.S⁻¹ * (sideSL h)⁻¹ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [evenGenerator, ModularGroup.coe_S, Matrix.adjugate_fin_two] <;> ring

/-- Conjugation factorization `oddSL h = sideSL h · R⁻¹ · (sideSL h)⁻¹` in `SL(2, ℤ)`. -/
theorem oddSL_eq_conj_R_inv {a b c d : ℤ} (h : c * b - a * d = 1) :
    oddSL h = sideSL h * TauCeti.ModularGroup.R⁻¹ * (sideSL h)⁻¹ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [oddGenerator, TauCeti.ModularGroup.coe_R, Matrix.adjugate_fin_two] <;> ring

/-- Factorization `freeSL h h' = sideSL h' · S⁻¹ · (sideSL h)⁻¹` in `SL(2, ℤ)`. -/
theorem freeSL_eq_sideSL_mul_S_inv_mul_inv {a b c d a' b' c' d' : ℤ}
    (h : c * b - a * d = 1) (h' : c' * b' - a' * d' = 1) :
    freeSL h h' = sideSL h' * ModularGroup.S⁻¹ * (sideSL h)⁻¹ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [freeGenerator, ModularGroup.coe_S, Matrix.adjugate_fin_two] <;> ring

@[simp] theorem evenSL_sq {a b c d : ℤ} (h : c * b - a * d = 1) :
    evenSL h ^ 2 = (-1 : SL(2, ℤ)) := by
  rw [evenSL_eq_conj_S_inv, ← MulAut.conj_apply, ← map_pow, inv_pow, TauCeti.ModularGroup.S_sq]
  ext i j; fin_cases i <;> fin_cases j <;> simp
@[simp] theorem coe_evenSL_sq {a b c d : ℤ} (h : c * b - a * d = 1) :
    (evenSL h : PSL(2, ℤ)) ^ 2 = 1 := by
  rw [← QuotientGroup.mk_pow, evenSL_sq, Matrix.ProjectiveSpecialLinearGroup.mk_neg]; rfl
@[simp] theorem coe_evenSL_inv {a b c d : ℤ} (h : c * b - a * d = 1) :
    (evenSL h : PSL(2, ℤ))⁻¹ = evenSL h :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, coe_evenSL_sq])
@[simp] theorem oddSL_pow_three {a b c d : ℤ} (h : c * b - a * d = 1) :
    oddSL h ^ 3 = (-1 : SL(2, ℤ)) := by
  rw [oddSL_eq_conj_R_inv, ← MulAut.conj_apply, ← map_pow, inv_pow,
    TauCeti.ModularGroup.R_pow_three]
  ext i j; fin_cases i <;> fin_cases j <;> simp
@[simp] theorem coe_oddSL_pow_three {a b c d : ℤ} (h : c * b - a * d = 1) :
    (oddSL h : PSL(2, ℤ)) ^ 3 = 1 := by
  rw [← QuotientGroup.mk_pow, oddSL_pow_three, Matrix.ProjectiveSpecialLinearGroup.mk_neg]; rfl
/-- Reversing the order of a free pair replaces `freeSL` by `-freeSL⁻¹` in `SL(2, ℤ)`. -/
@[simp] theorem freeSL_inv {a b c d a' b' c' d' : ℤ}
    (h : c * b - a * d = 1) (h' : c' * b' - a' * d' = 1) : (freeSL h h')⁻¹ = -freeSL h' h := by
  rw [freeSL_eq_sideSL_mul_S_inv_mul_inv h h', freeSL_eq_sideSL_mul_S_inv_mul_inv h' h]
  simp [ModularGroup.S_inv, mul_assoc]
@[simp] theorem coe_freeSL_inv {a b c d a' b' c' d' : ℤ}
    (h : c * b - a * d = 1) (h' : c' * b' - a' * d' = 1) :
    (freeSL h h' : PSL(2, ℤ))⁻¹ = freeSL h' h := by
  rw [← QuotientGroup.mk_inv, freeSL_inv, Matrix.ProjectiveSpecialLinearGroup.mk_neg]

/-- Every even side generator has exact order `2` in `PSL(2, ℤ)`. -/
@[simp] theorem orderOf_coe_evenSL {a b c d : ℤ} (h : c * b - a * d = 1) :
    orderOf (evenSL h : PSL(2, ℤ)) = 2 := by
  rw [evenSL_eq_conj_S_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_inv,
    TauCeti.ModularGroup.orderOf_coe_S]

/-- Every odd side generator has exact order `3` in `PSL(2, ℤ)`. -/
@[simp] theorem orderOf_coe_oddSL {a b c d : ℤ} (h : c * b - a * d = 1) :
    orderOf (oddSL h : PSL(2, ℤ)) = 3 := by
  rw [oddSL_eq_conj_R_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_inv,
    TauCeti.ModularGroup.orderOf_coe_R]

/-! ### Möbius action on rational cusps and `∞` -/

/-- The cusp in `OnePoint ℚ` of `(a, b) ∈ ℤ × ℤ`: `∞` when `b = 0` and `a / b` otherwise. -/
def cuspOfEndpoint (p : ℤ × ℤ) : OnePoint ℚ := if p.2 = 0 then ∞ else ((p.1 : ℚ) / (p.2 : ℚ))
theorem cuspOfEndpoint_def (p : ℤ × ℤ) :
    cuspOfEndpoint p = if p.2 = 0 then ∞ else ((p.1 : ℚ) / (p.2 : ℚ)) := (rfl)
@[simp] theorem cuspOfEndpoint_zero_right (a : ℤ) : cuspOfEndpoint (a, 0) = ∞ := (rfl)
theorem cuspOfEndpoint_of_ne_zero {a b : ℤ} (hb : b ≠ 0) :
    cuspOfEndpoint (a, b) = (((a : ℚ) / (b : ℚ) : ℚ) : OnePoint ℚ) := ite_eq_right hb

/-- Nonzero pairs `(a, b)` and `(c, d)` represent the same cusp iff `c * b - a * d = 0`. -/
theorem cuspOfEndpoint_eq_iff {p q : ℤ × ℤ} (hp : p ≠ (0, 0)) (hq : q ≠ (0, 0)) :
    cuspOfEndpoint p = cuspOfEndpoint q ↔ q.1 * p.2 - p.1 * q.2 = 0 := by
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩; by_cases hb : b = 0 <;> by_cases hd : d = 0
  · simp [cuspOfEndpoint, hb, hd]
  · simp only [cuspOfEndpoint, hb, hd, ↓reduceIte, OnePoint.infty_ne_coe, false_iff, mul_zero,
      zero_sub, neg_eq_zero, mul_eq_zero, or_false]; rintro rfl; exact hp (Prod.ext rfl hb)
  · simp only [cuspOfEndpoint, hb, hd, ↓reduceIte, OnePoint.coe_ne_infty, false_iff, mul_zero,
      sub_zero, mul_eq_zero, or_false]; rintro rfl; exact hq (Prod.ext rfl hd)
  · simp only [cuspOfEndpoint_of_ne_zero hb, cuspOfEndpoint_of_ne_zero hd, OnePoint.coe_eq_coe,
      div_eq_div_iff ((Int.cast_ne_zero (α := ℚ)).mpr hb) ((Int.cast_ne_zero (α := ℚ)).mpr hd)]
    norm_cast; omega

/-- `sideSL h` maps `∞ ∈ OnePoint ℚ` to the left endpoint `a / b`. -/
@[simp] theorem sideSL_smul_infty {a b c d : ℤ} (h : c * b - a * d = 1) :
    SpecialLinearGroup.mapGL ℚ (sideSL h) • (∞ : OnePoint ℚ) = cuspOfEndpoint (a, b) := by
  rw [OnePoint.smul_infty_eq_ite, SpecialLinearGroup.coe_mapGL_int_rat_fin_two]
  simp only [coe_sideSL, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one, Int.cast_neg]
  rcases eq_or_ne b 0 with rfl | hb <;> simp [cuspOfEndpoint, neg_div_neg_eq, *]

/-- `sideSL h` maps `0 ∈ OnePoint ℚ` to the right endpoint `c / d`. -/
@[simp] theorem sideSL_smul_zero {a b c d : ℤ} (h : c * b - a * d = 1) :
    SpecialLinearGroup.mapGL ℚ (sideSL h) • ((0 : ℚ) : OnePoint ℚ) = cuspOfEndpoint (c, d) := by
  rw [OnePoint.smul_some_eq_ite, SpecialLinearGroup.coe_mapGL_int_rat_fin_two]
  simp only [coe_sideSL, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one, mul_zero,
    zero_add]
  rcases eq_or_ne d 0 with rfl | hd <;> simp [cuspOfEndpoint, *]

/-- `sideSL h` maps `-1 ∈ OnePoint ℚ` to the mediant `(a + c) / (b + d)`. -/
@[simp] theorem sideSL_smul_neg_one {a b c d : ℤ} (h : c * b - a * d = 1) :
    SpecialLinearGroup.mapGL ℚ (sideSL h) • ((-1 : ℚ) : OnePoint ℚ) =
      cuspOfEndpoint (a + c, b + d) := by
  rw [OnePoint.smul_some_eq_ite, SpecialLinearGroup.coe_mapGL_int_rat_fin_two]
  simp only [coe_sideSL, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one, Int.cast_neg,
    neg_mul_neg, mul_one]
  rcases eq_or_ne (b + d) 0 with hbd | hbd <;>
    [simp [cuspOfEndpoint, hbd, (by exact_mod_cast hbd : (b : ℚ) + d = 0)];
     simp [cuspOfEndpoint, hbd, (by exact_mod_cast hbd : (b : ℚ) + d ≠ 0)]]

/-- `evenSL` carries the left endpoint `a / b` to the right endpoint `c / d`. -/
@[simp] theorem evenSL_smul_left {a b c d : ℤ} (h : c * b - a * d = 1) :
    SpecialLinearGroup.mapGL ℚ (evenSL h) • cuspOfEndpoint (a, b) = cuspOfEndpoint (c, d) := by
  rw [← sideSL_smul_infty h, evenSL_eq_conj_S_inv, map_mul, map_mul, map_inv _ (sideSL h),
    mul_smul, mul_smul, inv_smul_smul, S_inv_eq_sideSL, sideSL_smul_infty]; simp [cuspOfEndpoint]
/-- `evenSL` carries the right endpoint `c / d` back to the left endpoint `a / b`. -/
@[simp] theorem evenSL_smul_right {a b c d : ℤ} (h : c * b - a * d = 1) :
    SpecialLinearGroup.mapGL ℚ (evenSL h) • cuspOfEndpoint (c, d) = cuspOfEndpoint (a, b) := by
  rw [← sideSL_smul_zero h, evenSL_eq_conj_S_inv, map_mul, map_mul, map_inv _ (sideSL h),
    mul_smul, mul_smul, inv_smul_smul, S_inv_eq_sideSL, sideSL_smul_zero]
  exact sideSL_smul_infty h
/-- `oddSL` carries `a / b` to the mediant `(a + c) / (b + d)`. -/
@[simp] theorem oddSL_smul_left {a b c d : ℤ} (h : c * b - a * d = 1) :
    SpecialLinearGroup.mapGL ℚ (oddSL h) • cuspOfEndpoint (a, b) =
      cuspOfEndpoint (a + c, b + d) := by
  rw [← sideSL_smul_infty h, oddSL_eq_conj_R_inv, map_mul, map_mul, map_inv _ (sideSL h),
    mul_smul, mul_smul, inv_smul_smul, R_inv_eq_sideSL, sideSL_smul_infty]; simp [cuspOfEndpoint]
/-- `oddSL` carries the mediant `(a + c) / (b + d)` to `c / d`. -/
@[simp] theorem oddSL_smul_mediant {a b c d : ℤ} (h : c * b - a * d = 1) :
    SpecialLinearGroup.mapGL ℚ (oddSL h) • cuspOfEndpoint (a + c, b + d) =
      cuspOfEndpoint (c, d) := by
  rw [← sideSL_smul_neg_one h, oddSL_eq_conj_R_inv, map_mul, map_mul, map_inv _ (sideSL h),
    mul_smul, mul_smul, inv_smul_smul, R_inv_eq_sideSL, sideSL_smul_neg_one]; simp [cuspOfEndpoint]
/-- `oddSL` carries `c / d` back to `a / b`. -/
@[simp] theorem oddSL_smul_right {a b c d : ℤ} (h : c * b - a * d = 1) :
    SpecialLinearGroup.mapGL ℚ (oddSL h) • cuspOfEndpoint (c, d) = cuspOfEndpoint (a, b) := by
  rw [← sideSL_smul_zero h, oddSL_eq_conj_R_inv, map_mul, map_mul, map_inv _ (sideSL h),
    mul_smul, mul_smul, inv_smul_smul, R_inv_eq_sideSL, sideSL_smul_zero]
  exact sideSL_smul_infty h
/-- `freeSL` carries `a / b` to `c' / d'`. -/
@[simp] theorem freeSL_smul_left {a b c d a' b' c' d' : ℤ}
    (h : c * b - a * d = 1) (h' : c' * b' - a' * d' = 1) :
    SpecialLinearGroup.mapGL ℚ (freeSL h h') • cuspOfEndpoint (a, b) = cuspOfEndpoint (c', d') := by
  rw [← sideSL_smul_infty h, freeSL_eq_sideSL_mul_S_inv_mul_inv, map_mul, map_mul,
    map_inv _ (sideSL h), mul_smul, mul_smul, inv_smul_smul, S_inv_eq_sideSL, sideSL_smul_infty]
  simp [cuspOfEndpoint]
/-- `freeSL` carries `c / d` to `a' / b'`. -/
@[simp] theorem freeSL_smul_right {a b c d a' b' c' d' : ℤ}
    (h : c * b - a * d = 1) (h' : c' * b' - a' * d' = 1) :
    SpecialLinearGroup.mapGL ℚ (freeSL h h') • cuspOfEndpoint (c, d) = cuspOfEndpoint (a', b') := by
  rw [← sideSL_smul_zero h, freeSL_eq_sideSL_mul_S_inv_mul_inv, map_mul, map_mul,
    map_inv _ (sideSL h), mul_smul, mul_smul, inv_smul_smul, S_inv_eq_sideSL, sideSL_smul_zero]
  exact sideSL_smul_infty h'

/-! ### Elliptic fixed points in `ℍ` -/

/-- The fixed point `M · (-i) ∈ ℍ` of `evenSL h` on the geodesic `(a / b, c / d)`. -/
noncomputable def evenFixedPoint {a b c d : ℤ} (h : c * b - a * d = 1) : ℍ :=
  sideSL h • UpperHalfPlane.I
theorem evenFixedPoint_def {a b c d : ℤ} (h : c * b - a * d = 1) :
    evenFixedPoint h = sideSL h • UpperHalfPlane.I := (rfl)

/-- Complex coordinate `M · (-i)` of `evenFixedPoint h` (`M = !![a, c; b, d]`). -/
theorem coe_evenFixedPoint {a b c d : ℤ} (h : c * b - a * d = 1) :
    (evenFixedPoint h : ℂ) = ((a : ℂ) * (-Complex.I) + c) / ((b : ℂ) * (-Complex.I) + d) := by
  rw [evenFixedPoint, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [sideSL, mul_neg, neg_mul]

/-- On the side `(-1 / 0, 0 / 1)`, `evenFixedPoint` is `i ∈ ℍ`. -/
@[simp] theorem evenFixedPoint_neg_one_zero_zero_one :
    evenFixedPoint (a := -1) (b := 0) (c := 0) (d := 1) (by ring) = UpperHalfPlane.I :=
  UpperHalfPlane.ext (by simp [coe_evenFixedPoint])

-- Not `@[simp]`: `simpNF` rewrites the LHS via `ModularGroup.sl_moeb` to the `GL (Fin 2) ℝ` action.
/-- `evenSL h` fixes `evenFixedPoint h` in `ℍ`. -/
theorem evenSL_smul_evenFixedPoint {a b c d : ℤ} (h : c * b - a * d = 1) :
    evenSL h • evenFixedPoint h = evenFixedPoint h := by
  have hSI : ModularGroup.S⁻¹ • UpperHalfPlane.I = UpperHalfPlane.I :=
    inv_smul_eq_iff.mpr (ModularGroup.stabilizer_I.mpr (by simp)).symm
  rw [evenFixedPoint, evenSL_eq_conj_S_inv, mul_smul, mul_smul, inv_smul_smul, hSI]

/-- The fixed point `M · e^{-πi/3} ∈ ℍ` of `oddSL h` associated to an odd side `(a / b, c / d)`. -/
noncomputable def oddFixedPoint {a b c d : ℤ} (h : c * b - a * d = 1) : ℍ :=
  sideSL h • UpperHalfPlane.ρ
theorem oddFixedPoint_def {a b c d : ℤ} (h : c * b - a * d = 1) :
    oddFixedPoint h = sideSL h • UpperHalfPlane.ρ := (rfl)

/-- Complex coordinate `M · e^{-πi/3}` of `oddFixedPoint h` (`M = !![a, c; b, d]`). -/
theorem coe_oddFixedPoint {a b c d : ℤ} (h : c * b - a * d = 1) :
    (oddFixedPoint h : ℂ) =
      ((a : ℂ) * Complex.exp (-((Real.pi / 3 : ℝ) : ℂ) * Complex.I) + c) /
        ((b : ℂ) * Complex.exp (-((Real.pi / 3 : ℝ) : ℂ) * Complex.I) + d) := by
  have hρ : (UpperHalfPlane.ρ : ℂ) = -Complex.exp (-((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    simpa [neg_mul, Complex.exp_neg, div_eq_mul_inv, UpperHalfPlane.ρ_add_one_eq_exp] using
      UpperHalfPlane.neg_one_div_ρ_add_one.symm
  rw [oddFixedPoint, UpperHalfPlane.coe_specialLinearGroup_apply, hρ]
  simp only [coe_sideSL, of_apply, cons_val_zero, cons_val_one, cons_val_fin_one,
    algebraMap_int_eq, Int.coe_castRingHom, Int.cast_neg, Complex.ofReal_neg,
    Complex.ofReal_intCast]
  ring

-- Not `@[simp]`: `simpNF` rewrites the LHS via `ModularGroup.sl_moeb` to the `GL (Fin 2) ℝ` action.
/-- `oddSL h` fixes `oddFixedPoint h` in `ℍ`. -/
theorem oddSL_smul_oddFixedPoint {a b c d : ℤ} (h : c * b - a * d = 1) :
    oddSL h • oddFixedPoint h = oddFixedPoint h := by
  have hRρ : TauCeti.ModularGroup.R⁻¹ • UpperHalfPlane.ρ = UpperHalfPlane.ρ :=
    inv_smul_eq_iff.mpr (ModularGroup.stabilizer_ρ.mpr (by simp [TauCeti.ModularGroup.R_def])).symm
  rw [oddFixedPoint, oddSL_eq_conj_R_inv, mul_smul, mul_smul, inv_smul_smul, hRρ]

/-! ### Side-indexed generators and the hyperbolic/parabolic dichotomy -/

/-- The `SL(2, ℤ)` lift carrying `(∞, 0)` to side `i` of `F`. -/
def sideLiftSL (F : FareySymbol) (i : Fin F.labels.length) : SL(2, ℤ) :=
  sideSL (F.unimodular_endpoints i)
theorem sideLiftSL_def (F : FareySymbol) (i : Fin F.labels.length) :
    F.sideLiftSL i = sideSL (F.unimodular_endpoints i) := (rfl)
/-- The even generator in `SL(2, ℤ)` attached to side `i` of `F`. -/
def evenSideSL (F : FareySymbol) (i : Fin F.labels.length) : SL(2, ℤ) :=
  evenSL (F.unimodular_endpoints i)
theorem evenSideSL_def (F : FareySymbol) (i : Fin F.labels.length) :
    F.evenSideSL i = evenSL (F.unimodular_endpoints i) := (rfl)
/-- The odd generator in `SL(2, ℤ)` attached to side `i` of `F`. -/
def oddSideSL (F : FareySymbol) (i : Fin F.labels.length) : SL(2, ℤ) :=
  oddSL (F.unimodular_endpoints i)
theorem oddSideSL_def (F : FareySymbol) (i : Fin F.labels.length) :
    F.oddSideSL i = oddSL (F.unimodular_endpoints i) := (rfl)
/-- The free generator in `SL(2, ℤ)` pairing side `i` with side `j` of `F`. -/
def freeSideSL (F : FareySymbol) (i j : Fin F.labels.length) : SL(2, ℤ) :=
  freeSL (F.unimodular_endpoints i) (F.unimodular_endpoints j)
theorem freeSideSL_def (F : FareySymbol) (i j : Fin F.labels.length) :
    F.freeSideSL i j = freeSL (F.unimodular_endpoints i) (F.unimodular_endpoints j) := (rfl)
/-- Reversing the order of a side pair negates the inverse of `freeSideSL` in `SL(2, ℤ)`. -/
@[simp] theorem freeSideSL_inv (F : FareySymbol) (i j : Fin F.labels.length) :
    (F.freeSideSL i j)⁻¹ = -F.freeSideSL j i := freeSL_inv _ _
/-- Reversing the order of a side pair inverts `freeSideSL` in `PSL(2, ℤ)`. -/
@[simp] theorem coe_freeSideSL_inv (F : FareySymbol) (i j : Fin F.labels.length) :
    (F.freeSideSL i j : PSL(2, ℤ))⁻¹ = F.freeSideSL j i := coe_freeSL_inv _ _

/-- The left cusp in `OnePoint ℚ` of side `i` of `F`. -/
def leftCusp (F : FareySymbol) (i : Fin F.labels.length) : OnePoint ℚ :=
  cuspOfEndpoint (F.leftEndpoint i)
theorem leftCusp_def (F : FareySymbol) (i : Fin F.labels.length) :
    F.leftCusp i = cuspOfEndpoint (F.leftEndpoint i) := (rfl)
/-- The right cusp in `OnePoint ℚ` of side `i` of `F`. -/
def rightCusp (F : FareySymbol) (i : Fin F.labels.length) : OnePoint ℚ :=
  cuspOfEndpoint (F.rightEndpoint i)
theorem rightCusp_def (F : FareySymbol) (i : Fin F.labels.length) :
    F.rightCusp i = cuspOfEndpoint (F.rightEndpoint i) := (rfl)

@[simp] theorem sideLiftSL_smul_infty (F : FareySymbol) (i : Fin F.labels.length) :
    SpecialLinearGroup.mapGL ℚ (F.sideLiftSL i) • (∞ : OnePoint ℚ) = F.leftCusp i :=
  sideSL_smul_infty _
@[simp] theorem sideLiftSL_smul_zero (F : FareySymbol) (i : Fin F.labels.length) :
    SpecialLinearGroup.mapGL ℚ (F.sideLiftSL i) • ((0 : ℚ) : OnePoint ℚ) = F.rightCusp i :=
  sideSL_smul_zero _
@[simp] theorem evenSideSL_smul_leftCusp (F : FareySymbol) (i : Fin F.labels.length) :
    SpecialLinearGroup.mapGL ℚ (F.evenSideSL i) • F.leftCusp i = F.rightCusp i :=
  evenSL_smul_left _
@[simp] theorem evenSideSL_smul_rightCusp (F : FareySymbol) (i : Fin F.labels.length) :
    SpecialLinearGroup.mapGL ℚ (F.evenSideSL i) • F.rightCusp i = F.leftCusp i :=
  evenSL_smul_right _
@[simp] theorem oddSideSL_smul_leftCusp (F : FareySymbol) (i : Fin F.labels.length) :
    SpecialLinearGroup.mapGL ℚ (F.oddSideSL i) • F.leftCusp i =
      cuspOfEndpoint ((F.leftEndpoint i).1 + (F.rightEndpoint i).1,
        (F.leftEndpoint i).2 + (F.rightEndpoint i).2) := oddSL_smul_left _
@[simp] theorem oddSideSL_smul_rightCusp (F : FareySymbol) (i : Fin F.labels.length) :
    SpecialLinearGroup.mapGL ℚ (F.oddSideSL i) • F.rightCusp i = F.leftCusp i :=
  oddSL_smul_right _
@[simp] theorem freeSideSL_smul_leftCusp (F : FareySymbol) (i j : Fin F.labels.length) :
    SpecialLinearGroup.mapGL ℚ (F.freeSideSL i j) • F.leftCusp i = F.rightCusp j :=
  freeSL_smul_left _ _
@[simp] theorem freeSideSL_smul_rightCusp (F : FareySymbol) (i j : Fin F.labels.length) :
    SpecialLinearGroup.mapGL ℚ (F.freeSideSL i j) • F.rightCusp i = F.leftCusp j :=
  freeSL_smul_right _ _

/-- Two sides `i` and `j` of `F` share a cusp in `OnePoint ℚ`. -/
def SharesCusp (F : FareySymbol) (i j : Fin F.labels.length) : Prop :=
  F.leftCusp i = F.leftCusp j ∨ F.leftCusp i = F.rightCusp j ∨
    F.rightCusp i = F.leftCusp j ∨ F.rightCusp i = F.rightCusp j
theorem sharesCusp_def (F : FareySymbol) (i j : Fin F.labels.length) :
    F.SharesCusp i j ↔ F.leftCusp i = F.leftCusp j ∨ F.leftCusp i = F.rightCusp j ∨
      F.rightCusp i = F.leftCusp j ∨ F.rightCusp i = F.rightCusp j := Iff.rfl

theorem SharesCusp.symm {F : FareySymbol} {i j : Fin F.labels.length}
    (h : F.SharesCusp i j) : F.SharesCusp j i := by
  rcases h with h | h | h | h <;> simp [SharesCusp, h.symm]

theorem sharesCusp_comm {F : FareySymbol} {i j : Fin F.labels.length} :
    F.SharesCusp i j ↔ F.SharesCusp j i := ⟨SharesCusp.symm, SharesCusp.symm⟩

/-- For `i < j`, `F.SharesCusp i j` iff `i + 1 = j` or `(i, j) = (0, F.xs.length)` (at `∞`). -/
theorem sharesCusp_iff_of_lt {F : FareySymbol} {i j : Fin F.labels.length} (hij : i < j) :
    F.SharesCusp i j ↔ i.val + 1 = j.val ∨ (i.val = 0 ∧ j.val = F.xs.length) := by
  have := F.labels_length; have := F.endpoints_length
  have hep {k l : ℕ} (hkl : k ≤ l) (hl : l < F.endpoints.length) :
      cuspOfEndpoint (F.endpoints[k]'(hkl.trans_lt hl)) = cuspOfEndpoint (F.endpoints[l]'hl) ↔
        k = l ∨ (k = 0 ∧ l = F.xs.length + 1) :=
    (cuspOfEndpoint_eq_iff (F.endpoints_ne_zero _ _) (F.endpoints_ne_zero _ _)).trans
      (F.det_endpoints_eq_zero_iff hkl hl)
  rw [SharesCusp, leftCusp, leftCusp, rightCusp, rightCusp, leftEndpoint_def, leftEndpoint_def,
    rightEndpoint_def, rightEndpoint_def, hep hij.le, hep (by omega), hep (by omega),
    hep (by omega)]
  omega

/-- For `i < j` and `1 < F.xs.length`, `F.freeSideSL i j ≠ -1` in `SL(2, ℤ)`. -/
theorem freeSideSL_ne_neg_one {F : FareySymbol} {i j : Fin F.labels.length}
    (hxs : 1 < F.xs.length) (hij : i < j) : F.freeSideSL i j ≠ -1 := by
  intro hneg; have := F.labels_length; have := F.endpoints_length
  have h10 : -((F.endpoints[i.val]'(by omega)).2 * (F.endpoints[j.val]'(by omega)).2 +
      (F.endpoints[i.val + 1]'(by omega)).2 * (F.endpoints[j.val + 1]'(by omega)).2) = 0 := by
    simpa [freeSideSL_def, coe_freeSL, freeGenerator_def, leftEndpoint_def, rightEndpoint_def]
      using congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) hneg
  have hpos {k : ℕ} (hk0 : k ≠ 0) (hkl : k < F.xs.length + 1) :
      0 < (F.endpoints[k]'(by omega)).2 :=
    lt_of_le_of_ne (F.snd_endpoints_nonneg k (by omega)) (Ne.symm fun hz ↦ by
      have := (F.snd_endpoints_eq_zero_iff k (by omega)).mp hz; omega)
  have hb0 := F.snd_endpoints_nonneg i.val (by omega)
  have hd'0 := F.snd_endpoints_nonneg (j.val + 1) (by omega)
  have hd0 := hpos (k := i.val + 1) (by omega) (by omega)
  have hb'0 := hpos (k := j.val) (by omega) (by omega)
  have hi0 : i.val = 0 := by
    have := (F.snd_endpoints_eq_zero_iff i.val (by omega)).mp (by nlinarith); omega
  have hjlast : j.val = F.xs.length := by
    have := (F.snd_endpoints_eq_zero_iff (j.val + 1) (by omega)).mp (by nlinarith); omega
  have h01 : (F.leftEndpoint i).1 * (F.leftEndpoint j).1 +
      (F.rightEndpoint i).1 * (F.rightEndpoint j).1 = 0 := by
    simpa [freeSideSL_def, coe_freeSL, freeGenerator_def] using
      congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) hneg
  have hj_succ : j.val = F.xs.length - 1 + 1 := by omega
  have hli : F.leftEndpoint i = (-1, 0) := by simp [leftEndpoint_def, hi0]
  have hri : (F.rightEndpoint i).1 = (F.xs[0]'F.xs_length_pos).num := by
    simp [rightEndpoint_def, hi0, endpoints_succ F 0 F.xs_length_pos]
  have hlj : (F.leftEndpoint j).1 = (F.xs[F.xs.length - 1]'(by omega)).num := by
    simp [leftEndpoint_def, hj_succ, endpoints_succ F (F.xs.length - 1) (by omega)]
  have hrj : F.rightEndpoint j = (1, 0) := by simp [rightEndpoint_def, hjlast]
  rw [hli, hri, hlj, hrj] at h01
  have hlt_xs :=
    F.getElem_xs_lt_getElem_xs_of_lt F.xs_length_pos (j := F.xs.length - 1) (by omega) (by omega)
  rw [← Rat.intCast_num_of_den_eq_one F.den_xs_zero,
    ← Rat.intCast_num_of_den_eq_one F.den_xs_pred_length, Int.cast_lt] at hlt_xs; omega

private def sideCross (p q : ℤ × ℤ) : ℤ := q.1 * p.2 - p.1 * q.2

private theorem plucker_freeSideSL_of_lt {F : FareySymbol} {i j : Fin F.labels.length}
    (hij : i < j) :
    1 ≤ sideCross (F.leftEndpoint i) (F.leftEndpoint j) ∧
    1 ≤ sideCross (F.rightEndpoint i) (F.rightEndpoint j) ∧
    sideCross (F.leftEndpoint i) (F.leftEndpoint j) *
      sideCross (F.rightEndpoint i) (F.rightEndpoint j) -
      sideCross (F.leftEndpoint i) (F.rightEndpoint j) *
        sideCross (F.rightEndpoint i) (F.leftEndpoint j) = 1 ∧
    (F.freeSideSL i j : Matrix (Fin 2) (Fin 2) ℤ).trace =
      -(sideCross (F.leftEndpoint i) (F.leftEndpoint j) +
        sideCross (F.rightEndpoint i) (F.rightEndpoint j)) := by
  have := F.labels_length; have := F.endpoints_length; refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [sideCross, leftEndpoint_def]
    have := F.det_endpoints_pos hij (by omega) (by omega); omega
  · simp only [sideCross, rightEndpoint_def]
    have := F.det_endpoints_pos (Nat.add_lt_add_right hij 1) (by omega) (by omega); omega
  · calc _ = sideCross (F.leftEndpoint i) (F.rightEndpoint i) *
              sideCross (F.leftEndpoint j) (F.rightEndpoint j) := by simp [sideCross]; ring
      _ = 1 := by simp [sideCross, F.unimodular_endpoints]
  · rw [freeSideSL_def, coe_freeSL, trace_freeGenerator]; simp [sideCross]; ring

private theorem trace_freeSideSL_of_lt_of_sharesCusp {F : FareySymbol}
    {i j : Fin F.labels.length} (hij : i < j) (hsc : F.SharesCusp i j) :
    (F.freeSideSL i j : Matrix (Fin 2) (Fin 2) ℤ).trace = -2 := by
  obtain ⟨hX, hY, hid, htr⟩ := plucker_freeSideSL_of_lt hij
  have hPN : sideCross (F.leftEndpoint i) (F.rightEndpoint j) *
      sideCross (F.rightEndpoint i) (F.leftEndpoint j) = 0 := by
    rcases (F.sharesCusp_iff_of_lt hij).mp hsc with hadj | ⟨hi0, hjlast⟩
    · simp [sideCross, leftEndpoint_def, rightEndpoint_def, ← hadj]
    · simp [sideCross, leftEndpoint_def, rightEndpoint_def, hi0, hjlast]
  rw [hPN, sub_zero] at hid
  have hX1 : sideCross (F.leftEndpoint i) (F.leftEndpoint j) = 1 := le_antisymm (by
    by_contra! hlt; have := mul_le_mul hlt hY (by omega) (by omega); omega) hX
  have hY1 : sideCross (F.rightEndpoint i) (F.rightEndpoint j) = 1 := by simpa [hX1] using hid
  rw [htr, hX1, hY1]; rfl

/-- Ordered sides `i < j` sharing a cusp (`1 < F.xs.length`) give a parabolic `F.freeSideSL i j`. -/
theorem isParabolic_coe_freeSideSL_of_lt_of_sharesCusp {F : FareySymbol}
    {i j : Fin F.labels.length} (hxs : 1 < F.xs.length) (hij : i < j) (hsc : F.SharesCusp i j) :
    Matrix.ProjectiveSpecialLinearGroup.IsParabolic (F.freeSideSL i j : PSL(2, ℤ)) := by
  have htr := trace_freeSideSL_of_lt_of_sharesCusp hij hsc
  refine (Matrix.ProjectiveSpecialLinearGroup.eq_one_or_isParabolic_of_trace_sq_eq_four
    (by rw [htr]; ring)).resolve_left ?_
  rw [QuotientGroup.eq_one_iff, SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  rintro (hone | hneg)
  · simpa [htr] using congrArg (fun g : SL(2, ℤ) ↦ (g : Matrix (Fin 2) (Fin 2) ℤ).trace) hone
  · exact F.freeSideSL_ne_neg_one hxs hij hneg

/-- Ordered sides `i < j` with `¬ F.SharesCusp i j` give hyperbolic `F.freeSideSL i j`. -/
theorem isHyperbolic_coe_freeSideSL_of_lt_of_not_sharesCusp {F : FareySymbol}
    {i j : Fin F.labels.length} (hij : i < j) (hnsc : ¬ F.SharesCusp i j) :
    (F.freeSideSL i j : Matrix (Fin 2) (Fin 2) ℤ).IsHyperbolic := by
  have := F.labels_length; have := F.endpoints_length
  have := mt (F.sharesCusp_iff_of_lt hij).mpr hnsc
  obtain ⟨hX, hY, hid, htr⟩ := plucker_freeSideSL_of_lt hij
  have hP1 : 1 ≤ sideCross (F.leftEndpoint i) (F.rightEndpoint j) := by
    simp only [sideCross, leftEndpoint_def, rightEndpoint_def]
    have := F.det_endpoints_pos (by omega : i.val < j.val + 1) (by omega) (by omega); omega
  have hN1 : 1 ≤ sideCross (F.rightEndpoint i) (F.leftEndpoint j) := by
    simp only [sideCross, leftEndpoint_def, rightEndpoint_def]
    have := F.det_endpoints_pos (by omega : i.val + 1 < j.val) (by omega) (by omega); omega
  have hPN1 := mul_le_mul hP1 hN1 zero_le_one (by omega)
  have hsum3 : 3 ≤ sideCross (F.leftEndpoint i) (F.leftEndpoint j) +
      sideCross (F.rightEndpoint i) (F.rightEndpoint j) := by
    rcases eq_or_ne (sideCross (F.leftEndpoint i) (F.leftEndpoint j)) 1 with h1 | _ <;>
      [rw [h1] at hid; skip] <;> omega
  rw [isHyperbolic_iff_two_lt_abs_trace (F.freeSideSL i j).det_coe, htr, abs_neg,
    abs_of_nonneg (by omega)]; omega

/-- For `i ≠ j` and `1 < F.xs.length`, `F.freeSideSL i j` is parabolic iff `F.SharesCusp i j`. -/
theorem isParabolic_coe_freeSideSL_iff {F : FareySymbol} {i j : Fin F.labels.length}
    (hxs : 1 < F.xs.length) (hne : i ≠ j) :
    Matrix.ProjectiveSpecialLinearGroup.IsParabolic (F.freeSideSL i j : PSL(2, ℤ)) ↔
      F.SharesCusp i j := by
  suffices ∀ {i j : Fin F.labels.length}, i < j →
      (Matrix.ProjectiveSpecialLinearGroup.IsParabolic (F.freeSideSL i j : PSL(2, ℤ)) ↔
        F.SharesCusp i j) by
    rcases lt_or_gt_of_ne hne with hij | hji; · exact this hij
    rw [← coe_freeSideSL_inv, Matrix.ProjectiveSpecialLinearGroup.isParabolic_inv_iff,
      sharesCusp_comm]; exact this hji
  intro i j hij; by_cases hsc : F.SharesCusp i j
  · exact ⟨fun _ ↦ hsc, fun _ ↦ F.isParabolic_coe_freeSideSL_of_lt_of_sharesCusp hxs hij hsc⟩
  · refine ⟨fun hpar ↦ False.elim ?_, fun h ↦ False.elim (hsc h)⟩
    rw [Matrix.ProjectiveSpecialLinearGroup.isParabolic_mk_iff,
      GeneralLinearGroup.IsParabolic, SpecialLinearGroup.coe_GL_coe_matrix] at hpar
    exact (F.isHyperbolic_coe_freeSideSL_of_lt_of_not_sharesCusp hij hsc).ne hpar.2.symm

/-- `F.freeSideSL i j` is hyperbolic iff sides `i` and `j` do not share a cusp. -/
theorem isHyperbolic_coe_freeSideSL_iff {F : FareySymbol} {i j : Fin F.labels.length} :
    (F.freeSideSL i j : Matrix (Fin 2) (Fin 2) ℤ).IsHyperbolic ↔ ¬ F.SharesCusp i j := by
  rcases eq_or_ne i j with rfl | hne
  · rw [isHyperbolic_iff_two_lt_abs_trace (F.freeSideSL i i).det_coe, freeSideSL_def]
    simp [SharesCusp]
  suffices ∀ {i j : Fin F.labels.length}, i < j →
      ((F.freeSideSL i j : Matrix (Fin 2) (Fin 2) ℤ).IsHyperbolic ↔ ¬ F.SharesCusp i j) by
    rcases lt_or_gt_of_ne hne with hij | hji; · exact this hij
    have htr : |(F.freeSideSL i j : Matrix (Fin 2) (Fin 2) ℤ).trace| =
        |(F.freeSideSL j i : Matrix (Fin 2) (Fin 2) ℤ).trace| := by
      rw [freeSideSL_def, freeSideSL_def, coe_freeSL, coe_freeSL, trace_freeGenerator,
        trace_freeGenerator, ← abs_neg]; congr 1; ring
    rw [isHyperbolic_iff_two_lt_abs_trace (F.freeSideSL i j).det_coe, htr,
      ← isHyperbolic_iff_two_lt_abs_trace (F.freeSideSL j i).det_coe, sharesCusp_comm]
    exact this hji
  intro i j hij; by_cases hsc : F.SharesCusp i j
  · simp [hsc, isHyperbolic_iff_two_lt_abs_trace (F.freeSideSL i j).det_coe,
      trace_freeSideSL_of_lt_of_sharesCusp hij hsc]
  · exact ⟨fun _ ↦ hsc, fun _ ↦ F.isHyperbolic_coe_freeSideSL_of_lt_of_not_sharesCusp hij hsc⟩

/-- For `i ≠ j` and `1 < F.xs.length`, `F.freeSideSL i j` is either hyperbolic or parabolic. -/
theorem isHyperbolic_coe_freeSideSL_or_isParabolic_coe_freeSideSL {F : FareySymbol}
    {i j : Fin F.labels.length} (hxs : 1 < F.xs.length) (hne : i ≠ j) :
    (F.freeSideSL i j : Matrix (Fin 2) (Fin 2) ℤ).IsHyperbolic ∨
      Matrix.ProjectiveSpecialLinearGroup.IsParabolic (F.freeSideSL i j : PSL(2, ℤ)) :=
  (em (F.SharesCusp i j)).symm.imp
    F.isHyperbolic_coe_freeSideSL_iff.mpr (F.isParabolic_coe_freeSideSL_iff hxs hne).mpr

/-- Every free-pair generator of `F` is either hyperbolic or parabolic. -/
theorem isHyperbolic_coe_freeSideSL_or_isParabolic_coe_freeSideSL_of_free_pair {F : FareySymbol}
    {i j : Fin F.labels.length} {l : ℕ} (hne : i ≠ j) (hi : F.labels[i] = .free l) :
    (F.freeSideSL i j : Matrix (Fin 2) (Fin 2) ℤ).IsHyperbolic ∨
      Matrix.ProjectiveSpecialLinearGroup.IsParabolic (F.freeSideSL i j : PSL(2, ℤ)) :=
  F.isHyperbolic_coe_freeSideSL_or_isParabolic_coe_freeSideSL
    (F.one_lt_xs_length_of_free_mem (hi ▸ List.getElem_mem ..)) hne

/-- For `i ≠ j` and `1 < F.xs.length`, `(F.freeSideSL i j : PSL(2, ℤ))` has infinite order. -/
theorem not_isOfFinOrder_coe_freeSideSL {F : FareySymbol} {i j : Fin F.labels.length}
    (hxs : 1 < F.xs.length) (hne : i ≠ j) : ¬ IsOfFinOrder (F.freeSideSL i j : PSL(2, ℤ)) :=
  (F.isHyperbolic_coe_freeSideSL_or_isParabolic_coe_freeSideSL hxs hne).elim
    Matrix.ProjectiveSpecialLinearGroup.not_isOfFinOrder_mk_of_isHyperbolic
    Matrix.ProjectiveSpecialLinearGroup.IsParabolic.not_isOfFinOrder

/-! ### The generated modular subgroup and its symmetries -/

/-- The generating set of `F` in `PSL(2, ℤ)` (even, odd, and distinct free-paired generators). -/
def generatorSet (F : FareySymbol) : Set PSL(2, ℤ) :=
  {g | ∃ i, (F.labels[i] = .even ∧ g = F.evenSideSL i) ∨
    (F.labels[i] = .odd ∧ g = F.oddSideSL i) ∨
    ∃ j l, i ≠ j ∧ F.labels[i] = .free l ∧ F.labels[j] = .free l ∧ g = F.freeSideSL i j}
theorem generatorSet_def (F : FareySymbol) : F.generatorSet =
    {g : PSL(2, ℤ) | ∃ i, (F.labels[i] = .even ∧ g = F.evenSideSL i) ∨
      (F.labels[i] = .odd ∧ g = F.oddSideSL i) ∨
      ∃ j l, i ≠ j ∧ F.labels[i] = .free l ∧ F.labels[j] = .free l ∧ g = F.freeSideSL i j} := (rfl)
@[simp] theorem mem_generatorSet_iff {F : FareySymbol} {g : PSL(2, ℤ)} :
    g ∈ F.generatorSet ↔ ∃ i, (F.labels[i] = .even ∧ g = F.evenSideSL i) ∨
      (F.labels[i] = .odd ∧ g = F.oddSideSL i) ∨
      ∃ j l, i ≠ j ∧ F.labels[i] = .free l ∧ F.labels[j] = .free l ∧ g = F.freeSideSL i j := Iff.rfl

/-- The oriented generating set of `F` in `PSL(2, ℤ)`, taking only `i < j` for each free pair. -/
def orderedGeneratorSet (F : FareySymbol) : Set PSL(2, ℤ) :=
  {g | ∃ i, (F.labels[i] = .even ∧ g = F.evenSideSL i) ∨
    (F.labels[i] = .odd ∧ g = F.oddSideSL i) ∨
    ∃ j l, i < j ∧ F.labels[i] = .free l ∧ F.labels[j] = .free l ∧ g = F.freeSideSL i j}
theorem orderedGeneratorSet_def (F : FareySymbol) : F.orderedGeneratorSet =
    {g : PSL(2, ℤ) | ∃ i, (F.labels[i] = .even ∧ g = F.evenSideSL i) ∨
      (F.labels[i] = .odd ∧ g = F.oddSideSL i) ∨
      ∃ j l, i < j ∧ F.labels[i] = .free l ∧ F.labels[j] = .free l ∧ g = F.freeSideSL i j} := (rfl)
@[simp] theorem mem_orderedGeneratorSet_iff {F : FareySymbol} {g : PSL(2, ℤ)} :
    g ∈ F.orderedGeneratorSet ↔ ∃ i, (F.labels[i] = .even ∧ g = F.evenSideSL i) ∨
      (F.labels[i] = .odd ∧ g = F.oddSideSL i) ∨
      ∃ j l, i < j ∧ F.labels[i] = .free l ∧ F.labels[j] = .free l ∧ g = F.freeSideSL i j := Iff.rfl

/-- **The modular subgroup generated by a Farey symbol `F`** inside `PSL(2, ℤ)`. -/
def group (F : FareySymbol) : Subgroup PSL(2, ℤ) := Subgroup.closure F.generatorSet
theorem group_def (F : FareySymbol) : F.group = Subgroup.closure F.generatorSet := (rfl)
theorem coe_evenSideSL_mem_group {F : FareySymbol} {i : Fin F.labels.length}
    (hi : F.labels[i] = .even) : (F.evenSideSL i : PSL(2, ℤ)) ∈ F.group :=
  Subgroup.subset_closure ⟨i, Or.inl ⟨hi, rfl⟩⟩
theorem coe_oddSideSL_mem_group {F : FareySymbol} {i : Fin F.labels.length}
    (hi : F.labels[i] = .odd) : (F.oddSideSL i : PSL(2, ℤ)) ∈ F.group :=
  Subgroup.subset_closure ⟨i, Or.inr (Or.inl ⟨hi, rfl⟩)⟩
theorem coe_freeSideSL_mem_group {F : FareySymbol} {i j : Fin F.labels.length} {l : ℕ}
    (hne : i ≠ j) (hi : F.labels[i] = .free l) (hj : F.labels[j] = .free l) :
    (F.freeSideSL i j : PSL(2, ℤ)) ∈ F.group :=
  Subgroup.subset_closure ⟨i, Or.inr (Or.inr ⟨j, l, hne, hi, hj, rfl⟩)⟩

/-- Keeping only `i < j` for each free pair generates the same subgroup `F.group`. -/
theorem group_eq_closure_orderedGeneratorSet (F : FareySymbol) :
    F.group = Subgroup.closure F.orderedGeneratorSet := by
  refine le_antisymm (by
    rw [group_def, Subgroup.closure_le]
    rintro g ⟨i, ⟨hi, rfl⟩ | ⟨hi, rfl⟩ | ⟨j, l, hne, hi, hj, rfl⟩⟩
    · exact Subgroup.subset_closure ⟨i, Or.inl ⟨hi, rfl⟩⟩
    · exact Subgroup.subset_closure ⟨i, Or.inr (Or.inl ⟨hi, rfl⟩)⟩
    · rcases lt_or_gt_of_ne hne with hij | hji
      · exact Subgroup.subset_closure ⟨i, Or.inr (Or.inr ⟨j, l, hij, hi, hj, rfl⟩)⟩
      · rw [← coe_freeSideSL_inv]
        exact inv_mem (Subgroup.subset_closure ⟨j, Or.inr (Or.inr ⟨i, l, hji, hj, hi, rfl⟩)⟩))
    (Subgroup.closure_mono fun g ⟨i, h⟩ ↦ ⟨i, h.imp id (Or.imp id fun ⟨j, l, hij, hi, hj, hg⟩ ↦
      ⟨j, l, hij.ne, hi, hj, hg⟩)⟩)

/-- Agreement of `F.group` with closure of the matrix-equality specification in `SL(2, ℤ)`. -/
theorem group_eq_closure_matrix (F : FareySymbol) :
    F.group = Subgroup.closure (((↑) : SL(2, ℤ) → PSL(2, ℤ)) '' {g : SL(2, ℤ) |
      ∃ i : Fin F.labels.length,
        let a := F.leftEndpoint i; let b := F.rightEndpoint i
        (F.labels[i] = .even ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) = evenGenerator a.1 a.2 b.1 b.2) ∨
        (F.labels[i] = .odd ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) = oddGenerator a.1 a.2 b.1 b.2) ∨
        ∃ j l, i ≠ j ∧ F.labels[i] = .free l ∧ F.labels[j] = .free l ∧
          (g : Matrix (Fin 2) (Fin 2) ℤ) = freeGenerator a.1 a.2 b.1 b.2
            (F.leftEndpoint j).1 (F.leftEndpoint j).2
            (F.rightEndpoint j).1 (F.rightEndpoint j).2}) := by
  rw [group_def]; refine congrArg Subgroup.closure (Set.ext fun x ↦ ⟨?_, ?_⟩)
  · rintro ⟨i, ⟨hi, rfl⟩ | ⟨hi, rfl⟩ | ⟨j, l, hne, hi, hj, rfl⟩⟩
    · exact ⟨F.evenSideSL i, ⟨i, Or.inl ⟨hi, rfl⟩⟩, rfl⟩
    · exact ⟨F.oddSideSL i, ⟨i, Or.inr (Or.inl ⟨hi, rfl⟩)⟩, rfl⟩
    · exact ⟨F.freeSideSL i j, ⟨i, Or.inr (Or.inr ⟨j, l, hne, hi, hj, rfl⟩)⟩, rfl⟩
  · rintro ⟨g, ⟨i, ⟨hi, hg⟩ | ⟨hi, hg⟩ | ⟨j, l, hne, hi, hj, hg⟩⟩, rfl⟩
    · exact ⟨i, Or.inl ⟨hi, congrArg _ (Subtype.ext hg)⟩⟩
    · exact ⟨i, Or.inr (Or.inl ⟨hi, congrArg _ (Subtype.ext hg)⟩)⟩
    · exact ⟨i, Or.inr (Or.inr ⟨j, l, hne, hi, hj, congrArg _ (Subtype.ext hg)⟩)⟩

/-- Translating `F` by `k ∈ ℤ` multiplies every `sideLiftSL` on the left by `T ^ k`. -/
theorem sideLiftSL_translate (k : ℤ) (F : FareySymbol) (i : Fin (F.translate k).labels.length) :
    (F.translate k).sideLiftSL i = ModularGroup.T ^ k * F.sideLiftSL (i.cast (by simp)) := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [sideLiftSL_def, ModularGroup.coe_T_zpow, leftEndpoint_translate, rightEndpoint_translate]
  ring

/-- Translating `F` by `k ∈ ℤ` conjugates `evenSideSL` by `T ^ k` in `SL(2, ℤ)`. -/
theorem evenSideSL_translate (k : ℤ) (F : FareySymbol) (i : Fin (F.translate k).labels.length) :
    (F.translate k).evenSideSL i =
      ModularGroup.T ^ k * F.evenSideSL (i.cast (by simp)) * (ModularGroup.T ^ k)⁻¹ := by
  rw [evenSideSL_def, evenSideSL_def, evenSL_eq_conj_S_inv, evenSL_eq_conj_S_inv, ← sideLiftSL_def,
    sideLiftSL_translate, _root_.mul_inv_rev]; simp [sideLiftSL_def, mul_assoc]
/-- Translating `F` by `k ∈ ℤ` conjugates `oddSideSL` by `T ^ k` in `SL(2, ℤ)`. -/
theorem oddSideSL_translate (k : ℤ) (F : FareySymbol) (i : Fin (F.translate k).labels.length) :
    (F.translate k).oddSideSL i =
      ModularGroup.T ^ k * F.oddSideSL (i.cast (by simp)) * (ModularGroup.T ^ k)⁻¹ := by
  rw [oddSideSL_def, oddSideSL_def, oddSL_eq_conj_R_inv, oddSL_eq_conj_R_inv, ← sideLiftSL_def,
    sideLiftSL_translate, _root_.mul_inv_rev]; simp [sideLiftSL_def, mul_assoc]
/-- Translating `F` by `k ∈ ℤ` conjugates `freeSideSL` by `T ^ k` in `SL(2, ℤ)`. -/
theorem freeSideSL_translate (k : ℤ) (F : FareySymbol) (i j : Fin (F.translate k).labels.length) :
    (F.translate k).freeSideSL i j =
      ModularGroup.T ^ k * F.freeSideSL (i.cast (by simp)) (j.cast (by simp)) *
        (ModularGroup.T ^ k)⁻¹ := by
  rw [freeSideSL_def, freeSideSL_def, freeSL_eq_sideSL_mul_S_inv_mul_inv,
    freeSL_eq_sideSL_mul_S_inv_mul_inv, ← sideLiftSL_def, ← sideLiftSL_def, sideLiftSL_translate,
    sideLiftSL_translate, _root_.mul_inv_rev]; simp [sideLiftSL_def, mul_assoc]

/-- **Translation covariance**: `(F.translate k).group` is `F.group` conjugated by `T ^ k`. -/
theorem group_translate (k : ℤ) (F : FareySymbol) : (F.translate k).group =
    F.group.map (MulAut.conj ((ModularGroup.T : PSL(2, ℤ)) ^ k)).toMonoidHom := by
  suffices hle : ∀ (m : ℤ) (G : FareySymbol), (G.translate m).group ≤
      G.group.map (MulAut.conj ((ModularGroup.T : PSL(2, ℤ)) ^ m)).toMonoidHom by
    refine le_antisymm (hle k F) ?_
    have h := Subgroup.map_mono
      (f := (MulAut.conj ((ModularGroup.T : PSL(2, ℤ)) ^ k)).toMonoidHom) (hle (-k) (F.translate k))
    rw [← translate_add, neg_add_cancel, translate_zero, Subgroup.map_map] at h
    have hcomp : (MulAut.conj ((ModularGroup.T : PSL(2, ℤ)) ^ k)).toMonoidHom.comp
        (MulAut.conj ((ModularGroup.T : PSL(2, ℤ)) ^ (-k))).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun x ↦ by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
          ← MulAut.mul_apply, ← map_mul, ← _root_.zpow_add, add_neg_cancel, _root_.zpow_zero,
          map_one]; rfl
    rwa [hcomp, Subgroup.map_id] at h
  intro m G; rw [group_def, Subgroup.closure_le]
  rintro x ⟨i, ⟨hi, rfl⟩ | ⟨hi, rfl⟩ | ⟨j, l, hne, hi, hj, rfl⟩⟩
  · refine ⟨_, G.coe_evenSideSL_mem_group (i := i.cast (by simp)) (by simpa using hi), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; simp [evenSideSL_translate]
  · refine ⟨_, G.coe_oddSideSL_mem_group (i := i.cast (by simp)) (by simpa using hi), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; simp [oddSideSL_translate]
  · refine ⟨_, G.coe_freeSideSL_mem_group (i := i.cast (by simp)) (j := j.cast (by simp))
      (fun h ↦ hne (Fin.ext (by simpa using congrArg Fin.val h)))
      (by simpa using hi) (by simpa using hj), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; simp [freeSideSL_translate]

/-- Reflecting `F` replaces side `i`'s lift by `conjJ (F.sideLiftSL i.rev) * S⁻¹`. -/
theorem sideLiftSL_reflect (F : FareySymbol) (i : Fin F.reflect.labels.length) :
    F.reflect.sideLiftSL i =
      SpecialLinearGroup.conjJ (F.sideLiftSL (i.rev.cast (by simp))) * ModularGroup.S⁻¹ := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [sideLiftSL_def, S_inv_eq_sideSL, F.leftEndpoint_reflect i, F.rightEndpoint_reflect i]

/-- Reflecting `F` sends `evenSideSL i` to `-conjJ (F.evenSideSL i.rev)` in `SL(2, ℤ)`. -/
theorem evenSideSL_reflect (F : FareySymbol) (i : Fin F.reflect.labels.length) :
    F.reflect.evenSideSL i = -SpecialLinearGroup.conjJ (F.evenSideSL (i.rev.cast (by simp))) := by
  rw [evenSideSL_def, evenSideSL_def, evenSL_eq_conj_S_inv, evenSL_eq_conj_S_inv, ← sideLiftSL_def,
    ← sideLiftSL_def, sideLiftSL_reflect]; simp [_root_.mul_inv_rev, mul_assoc]
/-- Reflecting `F` sends `oddSideSL i` to `(conjJ (F.oddSideSL i.rev))⁻¹` in `SL(2, ℤ)`. -/
theorem oddSideSL_reflect (F : FareySymbol) (i : Fin F.reflect.labels.length) :
    F.reflect.oddSideSL i = SpecialLinearGroup.conjJ (F.oddSideSL (i.rev.cast (by simp)))⁻¹ := by
  rw [oddSideSL_def, oddSideSL_def, oddSL_eq_conj_R_inv, oddSL_eq_conj_R_inv, ← sideLiftSL_def,
    ← sideLiftSL_def, sideLiftSL_reflect]
  simp only [_root_.mul_inv_rev, inv_inv, SpecialLinearGroup.conjJ_mul,
    SpecialLinearGroup.conjJ_inv, ← TauCeti.ModularGroup.S_inv_mul_R_inv_mul_S, mul_assoc]
/-- Reflecting `F` sends `freeSideSL i j` to `-conjJ (F.freeSideSL i.rev j.rev)` in `SL(2, ℤ)`. -/
theorem freeSideSL_reflect (F : FareySymbol) (i j : Fin F.reflect.labels.length) :
    F.reflect.freeSideSL i j =
      -SpecialLinearGroup.conjJ (F.freeSideSL (i.rev.cast (by simp)) (j.rev.cast (by simp))) := by
  rw [freeSideSL_def, freeSideSL_def, freeSL_eq_sideSL_mul_S_inv_mul_inv,
    freeSL_eq_sideSL_mul_S_inv_mul_inv, ← sideLiftSL_def, ← sideLiftSL_def, ← sideLiftSL_def,
    ← sideLiftSL_def, sideLiftSL_reflect, sideLiftSL_reflect]; simp [_root_.mul_inv_rev, mul_assoc]

/-- **Reflection covariance**: reflecting `F` maps `F.group` by `conjJ` descended to `PSL(2, ℤ)`. -/
theorem group_reflect (F : FareySymbol) :
    F.reflect.group = F.group.map (QuotientGroup.congr _ _ SpecialLinearGroup.conjJMulAut
      (Subgroup.characteristic_iff_map_eq.1 inferInstance _)).toMonoidHom := by
  let φ : PSL(2, ℤ) ≃* PSL(2, ℤ) := QuotientGroup.congr _ _ SpecialLinearGroup.conjJMulAut
    (Subgroup.characteristic_iff_map_eq.1 inferInstance _)
  have hφ_mk (A : SL(2, ℤ)) : φ (A : PSL(2, ℤ)) = (SpecialLinearGroup.conjJ A : PSL(2, ℤ)) :=
    (QuotientGroup.congr_mk (x := A) ..).trans (congrArg _ (SpecialLinearGroup.conjJMulAut_apply A))
  suffices hle : ∀ G : FareySymbol, G.reflect.group ≤ G.group.map φ.toMonoidHom by
    refine le_antisymm (hle F) ?_
    have h := Subgroup.map_mono (f := φ.toMonoidHom) (hle F.reflect)
    rw [reflect_reflect, Subgroup.map_map] at h
    have hφ_comp : φ.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id _ := by
      ext A; simp [QuotientGroup.mk'_apply, hφ_mk]
    rwa [hφ_comp, Subgroup.map_id] at h
  intro G; rw [group_def, Subgroup.closure_le]
  rintro x ⟨i, ⟨hi, rfl⟩ | ⟨hi, rfl⟩ | ⟨j, l, hne, hi, hj, rfl⟩⟩
  · rw [evenSideSL_reflect, Matrix.ProjectiveSpecialLinearGroup.mk_neg, ← hφ_mk]
    exact Subgroup.mem_map_of_mem _ (G.coe_evenSideSL_mem_group (G.getElem_reflect_labels i ▸ hi))
  · rw [oddSideSL_reflect, ← hφ_mk, QuotientGroup.mk_inv, map_inv]
    exact inv_mem (Subgroup.mem_map_of_mem _
      (G.coe_oddSideSL_mem_group (G.getElem_reflect_labels i ▸ hi)))
  · rw [freeSideSL_reflect, Matrix.ProjectiveSpecialLinearGroup.mk_neg, ← hφ_mk]
    rw [G.getElem_reflect_labels] at hi hj
    exact Subgroup.mem_map_of_mem _ (G.coe_freeSideSL_mem_group
      (fun h ↦ hne (Fin.rev_injective (Fin.ext (by simpa using congrArg Fin.val h)))) hi hj)

/-! ### Concrete subgroup identifications -/

/-- If `-1 ∈ K` and `F.orderedGeneratorSet` maps into `K / {±1}`, the `SL(2, ℤ)` preimage of
`F.group` is contained in `K`. -/
theorem comap_group_le {F : FareySymbol} {K : Subgroup SL(2, ℤ)}
    (hneg : (-1 : SL(2, ℤ)) ∈ K) (hgen : F.orderedGeneratorSet ⊆
      (K.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) : Set PSL(2, ℤ))) :
    F.group.comap (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) ≤ K := by
  have hsub : F.group ≤ K.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) := by
    rwa [group_eq_closure_orderedGeneratorSet, Subgroup.closure_le]
  intro g hg; obtain ⟨u, hu, hug⟩ := hsub hg
  rcases SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one.mp (QuotientGroup.eq.mp hug) with
    h1 | hneg1
  · rwa [← inv_mul_eq_one.mp h1]
  · rw [inv_mul_eq_iff_eq_mul.mp hneg1, mul_neg_one, neg_eq_neg_one_mul]; exact mul_mem hneg hu

private theorem neg_one_mem_comap_group (F : FareySymbol) :
    (-1 : SL(2, ℤ)) ∈ F.group.comap (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) := by
  simp [Subgroup.mem_comap, QuotientGroup.mk'_apply, one_mem]

/-- The even generator on side `0` of `levelOne` (`(-1 / 0, 0 / 1)`) is `S⁻¹`. -/
theorem evenSideSL_levelOne_zero : levelOne.evenSideSL ⟨0, by simp⟩ = ModularGroup.S⁻¹ := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [evenSideSL_def, evenGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def,
      ModularGroup.coe_S]
/-- The odd generator on side `1` of `levelOne` (`(0 / 1, 1 / 0)`) is `-U`. -/
theorem oddSideSL_levelOne_one : levelOne.oddSideSL ⟨1, by simp⟩ = -TauCeti.ModularGroup.U := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [oddSideSL_def, oddGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def]

/-- The level-one Farey symbol generates the full modular group `PSL(2, ℤ)`. -/
@[simp] theorem group_levelOne : levelOne.group = ⊤ := by
  rw [eq_top_iff, ← TauCeti.ModularGroup.closure_coe_S_coe_T, Subgroup.closure_le]
  have hS : (ModularGroup.S : PSL(2, ℤ)) ∈ levelOne.group := by
    rw [← TauCeti.ModularGroup.coe_S_inv, ← QuotientGroup.mk_inv, ← evenSideSL_levelOne_zero]
    exact levelOne.coe_evenSideSL_mem_group (by simp)
  have hU : (TauCeti.ModularGroup.U : PSL(2, ℤ)) ∈ levelOne.group := by
    rw [← Matrix.ProjectiveSpecialLinearGroup.mk_neg, ← oddSideSL_levelOne_one]
    exact levelOne.coe_oddSideSL_mem_group (by simp)
  have hTinv : ((ModularGroup.T : PSL(2, ℤ)))⁻¹ =
      (ModularGroup.S : PSL(2, ℤ))⁻¹ * TauCeti.ModularGroup.U := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      TauCeti.ModularGroup.S_inv_mul_U]
  refine Set.pair_subset hS ?_
  rw [← inv_inv (ModularGroup.T : PSL(2, ℤ)), hTinv]
  exact inv_mem (mul_mem (inv_mem hS) hU)

/-- The free generator pairing sides `0` and `2` of `gamma0Two` is `-T`. -/
theorem freeSideSL_gamma0Two :
    gamma0Two.freeSideSL ⟨0, by simp⟩ ⟨2, by simp⟩ = -ModularGroup.T := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [freeSideSL_def, freeGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def,
      ModularGroup.coe_T]
/-- The even generator on side `1` (`(0 / 1, 1 / 1)`) of `gamma0Two` is `!![-1, 1; -2, 1]`. -/
theorem coe_evenSideSL_gamma0Two :
    (gamma0Two.evenSideSL ⟨1, by simp⟩ : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 1; -2, 1] := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [evenSideSL_def, evenGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def]

/-- The preimage of `gamma0Two.group` in `SL(2, ℤ)` is `CongruenceSubgroup.Gamma0 2`. -/
theorem comap_group_gamma0Two :
    gamma0Two.group.comap (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) =
      CongruenceSubgroup.Gamma0 2 := by
  set H := gamma0Two.group.comap (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))
  let B : SL(2, ℤ) := .mk !![-1, 1; -2, 1] (by decide)
  have hB : gamma0Two.evenSideSL ⟨1, by simp⟩ = B := Subtype.ext coe_evenSideSL_gamma0Two
  have hle : H ≤ CongruenceSubgroup.Gamma0 2 := by
    refine comap_group_le CongruenceSubgroup.neg_one_mem_Gamma0 ?_
    rintro x ⟨⟨i, hi⟩, h⟩; have : i < 3 := by simpa using hi
    rcases h with ⟨hlab, rfl⟩ | ⟨hlab, rfl⟩ | ⟨⟨j, hj⟩, l, hij, hli, hlj, rfl⟩
    · rw [Fin.getElem_fin] at hlab; interval_cases i <;> simp at hlab
      exact ⟨B, CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr ⟨-1, by decide⟩, by simp [hB]⟩
    · rw [Fin.getElem_fin] at hlab; interval_cases i <;> simp at hlab
    · rw [Fin.getElem_fin] at hli hlj; rw [Fin.mk_lt_mk] at hij; have : j < 3 := by simpa using hj
      interval_cases i <;> interval_cases j <;> try omega
      · simp at hlj
      · exact ⟨(-ModularGroup.T : SL(2, ℤ)),
          CongruenceSubgroup.mem_Gamma0_iff_dvd.mpr ⟨0, by decide⟩,
          by rw [freeSideSL_gamma0Two]; rfl⟩
      · simp at hli
  have ha : -ModularGroup.T ∈ H := freeSideSL_gamma0Two ▸ Subgroup.mem_comap.mpr
    (gamma0Two.coe_freeSideSL_mem_group (l := 1) (by decide) (by simp) (by simp))
  have hb : B ∈ H := hB ▸ Subgroup.mem_comap.mpr (gamma0Two.coe_evenSideSL_mem_group (by simp))
  have hneg1 : (-1 : SL(2, ℤ)) ∈ H := neg_one_mem_comap_group _
  have e {x y : SL(2, ℤ)} (hxy : x = y) (hy : y ∈ H) : x ∈ H := hxy ▸ hy
  refine TauCeti.Matrix.SpecialLinearGroup.eq_of_le_of_perm_S_T hle
    ![1, ModularGroup.S, ModularGroup.T * ModularGroup.S] rfl
    (fun i hi ↦ by fin_cases i <;>
      first | rfl | exact absurd (CongruenceSubgroup.mem_Gamma0_iff_dvd.mp hi) (by decide))
    ⟨Equiv.swap 0 1, fun i ↦ by fin_cases i <;>
      first | exact e (by decide) (one_mem H) | exact e (by decide) hneg1 |
        exact e (by decide) (inv_mem hb)⟩
    ⟨Equiv.swap 1 2, fun i ↦ by fin_cases i <;>
      first | exact e (by decide) (mul_mem hneg1 ha) | exact e (by decide) (one_mem H) |
        exact e (by decide) (mul_mem (inv_mem ha) (inv_mem hb))⟩

/-- The index of `gamma0Two.group` in `PSL(2, ℤ)` is `3`. -/
@[simp] theorem index_group_gamma0Two : gamma0Two.group.index = 3 := by
  rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
    comap_group_gamma0Two]
  exact CongruenceSubgroup.Gamma0_prime_index 2 Nat.prime_two

/-- The outer free generator pairing sides `0` and `3` of `gammaTwo` is `-T²`. -/
theorem freeSideSL_gammaTwo_outer :
    gammaTwo.freeSideSL ⟨0, by simp⟩ ⟨3, by simp⟩ = -(ModularGroup.T ^ 2) := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [freeSideSL_def, freeGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def,
      ModularGroup.coe_T, sq]
/-- The inner free generator pairing sides `1` and `2` of `gammaTwo` is `-!![3, -2; 2, -1]`. -/
theorem coe_freeSideSL_gammaTwo_inner :
    (gammaTwo.freeSideSL ⟨1, by simp⟩ ⟨2, by simp⟩ : Matrix (Fin 2) (Fin 2) ℤ) =
      -!![3, -2; 2, -1] := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [freeSideSL_def, freeGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def]

/-- The preimage of `gammaTwo.group` in `SL(2, ℤ)` is `CongruenceSubgroup.Gamma 2`. -/
theorem comap_group_gammaTwo :
    gammaTwo.group.comap (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) =
      CongruenceSubgroup.Gamma 2 := by
  set H := gammaTwo.group.comap (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))
  let B : SL(2, ℤ) := .mk (-!![3, -2; 2, -1]) (by decide)
  have hB : gammaTwo.freeSideSL ⟨1, by simp⟩ ⟨2, by simp⟩ = B :=
    Subtype.ext coe_freeSideSL_gammaTwo_inner
  have hle : H ≤ CongruenceSubgroup.Gamma 2 := by
    refine comap_group_le (CongruenceSubgroup.Gamma_mem.mpr (by decide)) ?_
    rintro x ⟨⟨i, hi⟩, h⟩; have : i < 4 := by simpa using hi
    rcases h with ⟨hlab, rfl⟩ | ⟨hlab, rfl⟩ | ⟨⟨j, hj⟩, l, hij, hli, hlj, rfl⟩
    · rw [Fin.getElem_fin] at hlab; interval_cases i <;> simp at hlab
    · rw [Fin.getElem_fin] at hlab; interval_cases i <;> simp at hlab
    · rw [Fin.getElem_fin] at hli hlj; rw [Fin.mk_lt_mk] at hij; have : j < 4 := by simpa using hj
      interval_cases i <;> interval_cases j <;> try omega
      all_goals simp only [gammaTwo_labels, List.getElem_cons_zero, List.getElem_cons_succ,
        SideLabel.free.injEq] at hli hlj
      all_goals try omega
      · exact ⟨(-(ModularGroup.T ^ 2) : SL(2, ℤ)), CongruenceSubgroup.Gamma_mem.mpr (by decide),
          by rw [freeSideSL_gammaTwo_outer]; rfl⟩
      · exact ⟨B, CongruenceSubgroup.Gamma_mem.mpr (by decide), by rw [hB]; rfl⟩
  have ha : -(ModularGroup.T ^ 2) ∈ H := freeSideSL_gammaTwo_outer ▸ Subgroup.mem_comap.mpr
    (gammaTwo.coe_freeSideSL_mem_group (l := 2) (by decide) (by simp) (by simp))
  have hb : B ∈ H := hB ▸ Subgroup.mem_comap.mpr
    (gammaTwo.coe_freeSideSL_mem_group (l := 1) (by decide) (by simp) (by simp))
  have hneg1 : (-1 : SL(2, ℤ)) ∈ H := neg_one_mem_comap_group _
  have e {x y : SL(2, ℤ)} (hxy : x = y) (hy : y ∈ H) : x ∈ H := hxy ▸ hy
  refine TauCeti.Matrix.SpecialLinearGroup.eq_of_le_of_perm_S_T hle
    ![1, ModularGroup.S, ModularGroup.T, ModularGroup.S * ModularGroup.T,
      ModularGroup.T * ModularGroup.S, ModularGroup.S * ModularGroup.T * ModularGroup.S] rfl
    (fun i hi ↦ by fin_cases i <;>
      first | rfl | exact absurd (CongruenceSubgroup.Gamma_mem.mp hi) (by decide))
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5, fun i ↦ by fin_cases i <;>
      first | exact e (by decide) (one_mem H) | exact e (by decide) hneg1⟩
    ⟨Equiv.swap 0 2 * Equiv.swap 1 4 * Equiv.swap 3 5, fun i ↦ by fin_cases i <;>
      first | exact e (by decide) (one_mem H) | exact e (by decide) (mul_mem hneg1 ha) |
        exact e (by decide) (mul_mem (inv_mem hb) ha) |
        exact e (by decide) (mul_mem (mul_mem hneg1 (inv_mem ha)) hb) |
        exact e (by decide) (mul_mem hneg1 (inv_mem ha))⟩

/-- The even generator on side `0` (`(-1 / 0, 0 / 1)`) of `indexSeven43` is `S⁻¹`. -/
theorem evenSideSL_indexSeven43 : indexSeven43.evenSideSL ⟨0, by simp⟩ = ModularGroup.S⁻¹ := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [evenSideSL_def, evenGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def,
      ModularGroup.coe_S]
/-- The free generator pairing sides `1` and `3` of `indexSeven43` is `-!![3, -1; 1, 0]`. -/
theorem coe_freeSideSL_indexSeven43 :
    (indexSeven43.freeSideSL ⟨1, by simp⟩ ⟨3, by simp⟩ : Matrix (Fin 2) (Fin 2) ℤ) =
      -!![3, -1; 1, 0] := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [freeSideSL_def, freeGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def]
/-- The odd generator on side `2` (`(1 / 1, 2 / 1)`) of `indexSeven43` is `!![-4, 7; -3, 5]`. -/
theorem coe_oddSideSL_indexSeven43 :
    (indexSeven43.oddSideSL ⟨2, by simp⟩ : Matrix (Fin 2) (Fin 2) ℤ) = !![-4, 7; -3, 5] := by
  ext p q; fin_cases p <;> fin_cases q <;>
    simp [oddSideSL_def, oddGenerator_def, leftEndpoint_def, rightEndpoint_def, endpoints_def]

end TauCeti.FareySymbol
