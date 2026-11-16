/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Khintchine.Dual
public import TauCeti.Analysis.CStarAlgebra.Schatten

import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.LinearAlgebra.Span.Basic
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
import TauCeti.Analysis.InnerProductSpace.Polar.Finite
import TauCeti.Analysis.InnerProductSpace.Trace.Free

/-!
# The `p = 1` noncommutative Khintchine inequality for matrices

For a finite family `a : ι → CStarMatrix m m ℂ` of `m × m` complex matrices, the noncommutative
`Lᵖ` Rademacher sum gauge and the row/column sum gauge are
$$\mathrm{randomSumGauge}_p(a)
    = \Bigl(\frac{1}{|2^\iota|} \sum_{\varepsilon : \iota \to \mathrm{Bool}}
        \Bigl\|\sum_k (\pm 1)_{\varepsilon_k} a_k\Bigr\|_{S^p}^p\Bigr)^{1/p},$$
$$\mathrm{rowColumnSumGauge}_p(a)
    = \inf_{a = b + c} \bigl(\|\mathrm{columnSquare}(b)\|_{S^p}
        + \|\mathrm{rowSquare}(c)\|_{S^p}\bigr).$$

At the endpoint `p = 1`, Lust-Piquard and Pisier proved that these two norms are equivalent
uniformly in the matrix dimension and the number of Rademacher signs, and Haagerup–Musat / Pisier
established the sharp lower constant `(√3)⁻¹` (with upper constant `1`).

This file proves this equivalence by combining three ingredients:
1. **Rectangular Schatten realization of the row/column sum gauge**: viewing a family
   `b : ι → CStarMatrix m m ℂ` as a column operator
   `EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ m)` identifies its finite
   modulus with `columnSquare b`, hence `matrixLpGauge p (columnSquare b)` with the rectangular
   Schatten `p`-seminorm for all `1 ≤ p`. By star symmetry the same holds for `rowSquare c`, so
   `rowColumnSumGauge p` is a `ℂ`-seminorm for all `1 ≤ p`.
2. **Trace-pairing duality between `L¹(ℓ²_C) + L¹(ℓ²_R)` and `L^∞(ℓ²_R) ∩ L^∞(ℓ²_C)`**:
   the canonical finite-dimensional polar decomposition of the column operator yields
   `‖∑_k tr(x_k b_k)‖ ≤ ‖rowSquare x‖ · matrixLpGauge 1 (columnSquare b)`, while testing against
   rank-one families recovers `‖rowSquare x‖` (and by star symmetry `‖columnSquare x‖`) from the
   dual norm.
3. **Hahn–Banach and dual Rademacher factorization**: extending the norming functional at `a`
   under `rowColumnSumGauge 1` produces a dual witness `x` with
   `max ‖columnSquare x‖ ‖rowSquare x‖ ≤ 1` and `∑_k tr(x_k a_k) = rowColumnSumGauge 1 a`;
   applying `TauCeti.exists_expect_units_smul_eq_and_norm_le` to `x` yields `(√3)⁻¹` as the lower
   constant, while sign-cube Bessel duality gives the upper constant `1`.

## Main declarations

* `TauCeti.randomSumGauge`: the Rademacher `Lᵖ` sum gauge on `ι → CStarMatrix m m ℂ`.
* `TauCeti.rowColumnSumGauge`, `TauCeti.rowColumnSumSeminorm`: the infimal row/column `Lᵖ` sum
  gauge and its `ℂ`-seminorm structure for `1 ≤ p`.
* `TauCeti.norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare`,
  `TauCeti.norm_rowSquare_le_of_forall_norm_sum_trace_mul_le`: trace-pairing duality between
  `matrixLpGauge 1 ∘ columnSquare` and `‖rowSquare ·‖`.
* `TauCeti.khintchine_one`: the `p = 1` noncommutative Khintchine inequality with constants
  `(√3)⁻¹` and `1` for arbitrary finite index types `ι` and `m`.
* `TauCeti.matrix_khintchine_one`: specialization to `Fin n → CStarMatrix (Fin d) (Fin d) ℂ`.

## References

* F. Lust-Piquard and G. Pisier, *Non commutative Khintchine and Paley inequalities*,
  Ark. Mat. 29 (1991), 241–260.
* U. Haagerup and M. Musat, *On the best constants in noncommutative Khintchine-type
  inequalities*, J. Funct. Anal. 250 (2007), 588–624, Theorem 2.11.
* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  Theorem 9.1.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexOrder ComplexStarModule CStarModule InnerProductSpace NNReal
  ENNReal WithCStarModule

namespace TauCeti

/-! ### The Rademacher `Lᵖ` sum gauge -/

section RandomSumGauge

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]

/-- The Rademacher `Lᵖ` sum gauge `(𝔼_ε ‖∑_k (±1)_{ε_k} a_k‖_p^p)^(1/p)` of a finite family of
matrices, with uniform measure on the Boolean sign cube `ι → Bool`. -/
def randomSumGauge (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) : ℝ :=
  ((∑ ε : ι → Bool,
      matrixLpGauge p (∑ k, (if ε k then (1 : ℂ) else -1) • a k) ^ (p : ℝ)) /
    (Fintype.card (ι → Bool) : ℝ)) ^ (1 / (p : ℝ))

/-- Unfolding definition of `randomSumGauge`. -/
theorem randomSumGauge_def (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge p a =
      ((∑ ε : ι → Bool,
          matrixLpGauge p (∑ k, (if ε k then (1 : ℂ) else -1) • a k) ^ (p : ℝ)) /
        (Fintype.card (ι → Bool) : ℝ)) ^ (1 / (p : ℝ)) :=
  (rfl)

/-- `randomSumGauge` is nonnegative. -/
theorem randomSumGauge_nonneg (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    0 ≤ randomSumGauge p a :=
  Real.rpow_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (matrixLpGauge_nonneg p _) _) (Nat.cast_nonneg _)) _

/-- At `p = 1`, `randomSumGauge 1 a` equals the expectation
`𝔼 ε : ι → ℤˣ, matrixLpGauge 1 (∑ k, ε k • a k)` over the multiplicative sign cube. -/
theorem randomSumGauge_one_eq_expect_units (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 a =
      𝔼 ε : ι → ℤˣ, matrixLpGauge 1 (∑ k, ε k • a k) := by
  let b2u : Bool ≃ ℤˣ :=
    ⟨fun b => if b then 1 else -1, fun u => decide (u = 1),
      fun b => by cases b <;> decide,
      fun u => by rcases Int.units_eq_one_or u with rfl | rfl <;> decide⟩
  let e : (ι → Bool) ≃ (ι → ℤˣ) := Equiv.piCongrRight fun _ => b2u
  have hsum :
      (∑ ε : ι → Bool,
        matrixLpGauge 1 (∑ k, (if ε k then (1 : ℂ) else -1) • a k) ^ ((1 : ℝ≥0) : ℝ)) =
        ∑ ε : ι → ℤˣ, matrixLpGauge 1 (∑ k, ε k • a k) :=
    Fintype.sum_equiv e _ _ fun ε => by
      simp only [NNReal.coe_one, Real.rpow_one]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      cases h : ε k <;> simp [h, e, b2u, Units.smul_def]
  rw [randomSumGauge_def, hsum, Fintype.card_congr e, Finset.expect_eq_sum_div_card,
    Finset.card_univ]
  simp

/-- Triangle inequality for `randomSumGauge 1`. -/
theorem randomSumGauge_one_add_le (a b : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 (a + b) ≤ randomSumGauge 1 a + randomSumGauge 1 b := by
  rw [randomSumGauge_one_eq_expect_units, randomSumGauge_one_eq_expect_units,
    randomSumGauge_one_eq_expect_units, ← Finset.expect_add_distrib]
  refine Finset.expect_le_expect fun ε _ => ?_
  simpa only [Pi.add_apply, smul_add, Finset.sum_add_distrib] using
    matrixLpGauge_add_le le_rfl (∑ k, ε k • a k) (∑ k, ε k • b k)

end RandomSumGauge

/-! ### Rectangular Schatten realization and the row/column sum seminorm -/

section RowColumnSumGauge

private def columnEuclideanLM {ι m : Type*} [Fintype m] [DecidableEq m] :
    (ι → CStarMatrix m m ℂ) →ₗ[ℂ]
      (EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 fun _ : ι => EuclideanSpace ℂ m) where
  toFun b := (WithLp.linearEquiv 2 ℂ (ι → EuclideanSpace ℂ m)).symm.toLinearMap.comp
    (LinearMap.pi fun k => (CStarMatrix.toEuclideanCLM (b k)).toLinearMap)
  map_add' _ _ := by ext v k; simp
  map_smul' _ _ := by ext v k; simp

variable {ι m : Type*} [Fintype ι] [Fintype m]

/-- The infimal row/column `Lᵖ` sum gauge
`inf {matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c) | a = b + c}` on finite
families of matrices. -/
def rowColumnSumGauge (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) : ℝ :=
  sInf {r : ℝ | ∃ b c : ι → CStarMatrix m m ℂ, a = b + c ∧
    r = matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c)}

/-- Unfolding definition of `rowColumnSumGauge`. -/
theorem rowColumnSumGauge_def (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p a =
      sInf {r : ℝ | ∃ b c : ι → CStarMatrix m m ℂ, a = b + c ∧
        r = matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c)} :=
  (rfl)

private theorem adjoint_comp_columnEuclideanLM [DecidableEq m] (b : ι → CStarMatrix m m ℂ) :
    (columnEuclideanLM b).adjoint ∘ₗ columnEuclideanLM b =
      (CStarMatrix.toEuclideanCLM (∑ k, star (b k) * b k)).toLinearMap := by
  refine LinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  have hof (w : EuclideanSpace ℂ m) (k : ι) :
      (columnEuclideanLM b w).ofLp k = CStarMatrix.toEuclideanCLM (b k) w := rfl
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, PiLp.inner_apply, hof, map_sum,
    ContinuousLinearMap.coe_coe, sum_apply, inner_sum, map_mul, map_star, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

private theorem operatorAbs_columnEuclideanLM [DecidableEq m] (b : ι → CStarMatrix m m ℂ) :
    (columnEuclideanLM b).operatorAbs =
      (CStarMatrix.toEuclideanCLM (columnSquare b)).toLinearMap := by
  have hnonneg : 0 ≤ CStarMatrix.toEuclideanCLM (columnSquare b) :=
    map_zero (CStarMatrix.toEuclideanCLM (n := m)) ▸
      OrderHomClass.mono CStarMatrix.toEuclideanCLM (columnSquare_nonneg b)
  have hsq : CStarMatrix.toEuclideanCLM (columnSquare b) *
      CStarMatrix.toEuclideanCLM (columnSquare b) =
        (columnEuclideanLM b).adjoint.toContinuousLinearMap ∘L
          (columnEuclideanLM b).toContinuousLinearMap := by
    rw [← map_mul, columnSquare_mul_self]
    exact ContinuousLinearMap.ext fun v => by
      simpa [LinearMap.comp_apply] using
        (LinearMap.congr_fun (adjoint_comp_columnEuclideanLM b) v).symm
  exact LinearMap.ext fun v => DFunLike.congr_fun
    ((LinearMap.toContinuousLinearMap_operatorAbs _).trans (CFC.sqrt_unique hsq hnonneg)) v

private theorem matrixLpGauge_columnSquare_eq_schatten [DecidableEq m] (p : ℝ≥0)
    [Fact (1 ≤ (p : ℝ≥0∞))] (b : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (columnSquare b) =
      UnitarilyInvariantSeminorm.schatten ℂ (EuclideanSpace ℂ m)
        (PiLp 2 fun _ : ι => EuclideanSpace ℂ m) p (columnEuclideanLM b) := by
  rw [matrixLpGauge_eq_schatten p, ← operatorAbs_columnEuclideanLM,
    UnitarilyInvariantSeminorm.schatten_apply, UnitarilyInvariantSeminorm.schatten_apply]
  simp_rw [(columnEuclideanLM b).singularValues_operatorAbs]

/-- Subadditivity of `b ↦ matrixLpGauge p (columnSquare b)` for `1 ≤ p`. -/
theorem matrixLpGauge_columnSquare_add_le {p : ℝ≥0} (hp : 1 ≤ p)
    (b₁ b₂ : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (columnSquare (b₁ + b₂)) ≤
      matrixLpGauge p (columnSquare b₁) + matrixLpGauge p (columnSquare b₂) := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  simp only [matrixLpGauge_columnSquare_eq_schatten p, map_add]
  exact map_add_le_add _ _ _

/-- Absolute homogeneity of `b ↦ matrixLpGauge p (columnSquare b)` for `1 ≤ p`. -/
theorem matrixLpGauge_columnSquare_smul {p : ℝ≥0} (hp : 1 ≤ p) (c : ℂ)
    (b : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (columnSquare (c • b)) = ‖c‖ * matrixLpGauge p (columnSquare b) := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  simp only [matrixLpGauge_columnSquare_eq_schatten p, map_smul]
  exact (UnitarilyInvariantSeminorm.schatten ℂ (EuclideanSpace ℂ m)
    (PiLp 2 fun _ : ι => EuclideanSpace ℂ m) p).toSeminorm.smul' c _

/-- Subadditivity of `c ↦ matrixLpGauge p (rowSquare c)` for `1 ≤ p`. -/
theorem matrixLpGauge_rowSquare_add_le {p : ℝ≥0} (hp : 1 ≤ p)
    (c₁ c₂ : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (rowSquare (c₁ + c₂)) ≤
      matrixLpGauge p (rowSquare c₁) + matrixLpGauge p (rowSquare c₂) := by
  rw [rowSquare_eq_columnSquare_star, rowSquare_eq_columnSquare_star,
    rowSquare_eq_columnSquare_star,
    show (fun k => star ((c₁ + c₂) k)) = (fun k => star (c₁ k)) + (fun k => star (c₂ k)) from
      funext fun k => star_add _ _]
  exact matrixLpGauge_columnSquare_add_le hp _ _

/-- Absolute homogeneity of `c ↦ matrixLpGauge p (rowSquare c)` for `1 ≤ p`. -/
theorem matrixLpGauge_rowSquare_smul {p : ℝ≥0} (hp : 1 ≤ p) (z : ℂ)
    (c : ι → CStarMatrix m m ℂ) :
    matrixLpGauge p (rowSquare (z • c)) = ‖z‖ * matrixLpGauge p (rowSquare c) := by
  rw [rowSquare_eq_columnSquare_star, rowSquare_eq_columnSquare_star,
    show (fun k => star ((z • c) k)) = star z • fun k => star (c k) by ext k; simp,
    matrixLpGauge_columnSquare_smul hp, norm_star]

/-- `rowColumnSumGauge` is nonnegative. -/
theorem rowColumnSumGauge_nonneg (p : ℝ≥0) (a : ι → CStarMatrix m m ℂ) :
    0 ≤ rowColumnSumGauge p a :=
  Real.sInf_nonneg fun _ ⟨_, _, _, h⟩ =>
    h ▸ add_nonneg (matrixLpGauge_nonneg p _) (matrixLpGauge_nonneg p _)

/-- Any decomposition `a = b + c` bounds `rowColumnSumGauge p a` above. -/
theorem rowColumnSumGauge_le_of_eq_add (p : ℝ≥0) {a b c : ι → CStarMatrix m m ℂ}
    (h : a = b + c) :
    rowColumnSumGauge p a ≤
      matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c) :=
  csInf_le ⟨0, fun _ ⟨_, _, _, hr⟩ =>
    hr ▸ add_nonneg (matrixLpGauge_nonneg p _) (matrixLpGauge_nonneg p _)⟩ ⟨b, c, h, rfl⟩

/-- Choosing `a = a + 0` bounds `rowColumnSumGauge p a` by the column `Lᵖ` gauge when `0 < p`. -/
theorem rowColumnSumGauge_le_columnSquare {p : ℝ≥0} (hp : 0 < p) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p a ≤ matrixLpGauge p (columnSquare a) := by
  simpa only [rowSquare_zero, matrixLpGauge_zero hp, add_zero] using
    rowColumnSumGauge_le_of_eq_add p (add_zero a).symm

/-- Choosing `a = 0 + a` bounds `rowColumnSumGauge p a` by the row `Lᵖ` gauge when `0 < p`. -/
theorem rowColumnSumGauge_le_rowSquare {p : ℝ≥0} (hp : 0 < p) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p a ≤ matrixLpGauge p (rowSquare a) := by
  simpa only [columnSquare_zero, matrixLpGauge_zero hp, zero_add] using
    rowColumnSumGauge_le_of_eq_add p (zero_add a).symm

/-- At `0`, `rowColumnSumGauge p` vanishes for `0 < p`. -/
@[simp]
theorem rowColumnSumGauge_zero {p : ℝ≥0} (hp : 0 < p) :
    rowColumnSumGauge p (0 : ι → CStarMatrix m m ℂ) = 0 :=
  le_antisymm
    ((rowColumnSumGauge_le_columnSquare hp 0).trans_eq (by simp [matrixLpGauge_zero hp]))
    (rowColumnSumGauge_nonneg p 0)

/-- Subadditivity of `rowColumnSumGauge p` for `1 ≤ p`. -/
theorem rowColumnSumGauge_add_le {p : ℝ≥0} (hp : 1 ≤ p)
    (a₁ a₂ : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (a₁ + a₂) ≤ rowColumnSumGauge p a₁ + rowColumnSumGauge p a₂ := by
  have hne (x : ι → CStarMatrix m m ℂ) : {r : ℝ | ∃ b c, x = b + c ∧
      r = matrixLpGauge p (columnSquare b) + matrixLpGauge p (rowSquare c)}.Nonempty :=
    ⟨_, x, 0, (add_zero x).symm, rfl⟩
  rw [rowColumnSumGauge_def p a₁, rowColumnSumGauge_def p a₂, ← sub_le_iff_le_add']
  refine le_csInf (hne a₂) fun _ ⟨b₂, c₂, h₂, hr₂⟩ => ?_
  rw [hr₂, sub_le_iff_le_add', ← sub_le_iff_le_add]
  refine le_csInf (hne a₁) fun _ ⟨b₁, c₁, h₁, hr₁⟩ => ?_
  rw [hr₁, sub_le_iff_le_add, h₁, h₂]
  refine (rowColumnSumGauge_le_of_eq_add p (add_add_add_comm b₁ c₁ b₂ c₂)).trans ?_
  linarith [matrixLpGauge_columnSquare_add_le hp b₁ b₂,
    matrixLpGauge_rowSquare_add_le hp c₁ c₂]

/-- Absolute homogeneity of `rowColumnSumGauge p` for `1 ≤ p`. -/
theorem rowColumnSumGauge_smul {p : ℝ≥0} (hp : 1 ≤ p) (z : ℂ)
    (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumGauge p (z • a) = ‖z‖ * rowColumnSumGauge p a := by
  by_cases hz : z = 0
  · simp [hz, rowColumnSumGauge_zero (zero_lt_one.trans_le hp)]
  · have hle {w : ℂ} (hw : w ≠ 0) (x : ι → CStarMatrix m m ℂ) :
        rowColumnSumGauge p (w • x) ≤ ‖w‖ * rowColumnSumGauge p x := by
      have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
      rw [rowColumnSumGauge_def p x, ← inv_mul_le_iff₀ hwn]
      refine le_csInf ⟨_, x, 0, (add_zero x).symm, rfl⟩ fun _ ⟨b, c, h, hr⟩ => ?_
      rw [hr, inv_mul_le_iff₀ hwn, h]
      refine (rowColumnSumGauge_le_of_eq_add p (smul_add w b c)).trans_eq ?_
      rw [matrixLpGauge_columnSquare_smul hp, matrixLpGauge_rowSquare_smul hp, mul_add]
    refine le_antisymm (hle hz a) ?_
    calc ‖z‖ * rowColumnSumGauge p a
        = ‖z‖ * rowColumnSumGauge p (z⁻¹ • (z • a)) := by rw [inv_smul_smul₀ hz]
      _ ≤ ‖z‖ * (‖z⁻¹‖ * rowColumnSumGauge p (z • a)) :=
          mul_le_mul_of_nonneg_left (hle (inv_ne_zero hz) (z • a)) (norm_nonneg z)
      _ = rowColumnSumGauge p (z • a) := by
          rw [norm_inv, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_mul]

variable (ι m) in
/-- For `1 ≤ p`, `rowColumnSumGauge p` bundled as a `ℂ`-seminorm on `ι → CStarMatrix m m ℂ`. -/
def rowColumnSumSeminorm (p : ℝ≥0) (hp : 1 ≤ p) : Seminorm ℂ (ι → CStarMatrix m m ℂ) :=
  Seminorm.of (rowColumnSumGauge p) (rowColumnSumGauge_add_le hp) (rowColumnSumGauge_smul hp)

@[simp]
theorem rowColumnSumSeminorm_apply (p : ℝ≥0) (hp : 1 ≤ p) (a : ι → CStarMatrix m m ℂ) :
    rowColumnSumSeminorm ι m p hp a = rowColumnSumGauge p a :=
  (rfl)

end RowColumnSumGauge

/-! ### Trace-pairing duality for column and row spaces -/

section TraceDuality

variable {ι m : Type*} [Fintype ι] [Fintype m]

/-- Polar decomposition of a finite matrix family through its column square function: every
`b : ι → CStarMatrix m m ℂ` factors as `b k = u k * columnSquare b` for some contraction family
`u` satisfying `‖columnSquare u‖ ≤ 1`. -/
theorem exists_mul_columnSquare_and_norm_columnSquare_le_one (b : ι → CStarMatrix m m ℂ) :
    ∃ u : ι → CStarMatrix m m ℂ,
      (∀ k, b k = u k * columnSquare b) ∧ ‖columnSquare u‖ ≤ 1 := by
  classical
  set A := columnEuclideanLM b
  let U := A.polarFactor
  let u : ι → CStarMatrix m m ℂ := fun k => CStarMatrix.toEuclideanCLM.symm
    ((PiLp.projₗ 2 (fun _ : ι => EuclideanSpace ℂ m) k).comp U).toContinuousLinearMap
  refine ⟨u, fun k => EquivLike.injective CStarMatrix.toEuclideanCLM ?_, ?_⟩
  · rw [map_mul, StarAlgEquiv.apply_symm_apply]
    refine ContinuousLinearMap.ext fun v => ?_
    have hpol := congrArg (fun w : PiLp 2 fun _ : ι => EuclideanSpace ℂ m => w k)
      (A.polarFactor_operatorAbs_apply v)
    rw [operatorAbs_columnEuclideanLM] at hpol
    exact hpol.symm
  · rw [norm_columnSquare, Real.sqrt_le_one, ← CStarMatrix.norm_toEuclideanCLM]
    have hgram : CStarMatrix.toEuclideanCLM (∑ k, star (u k) * u k) =
        (U.adjoint ∘ₗ U).toContinuousLinearMap :=
      ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => by
        rw [map_sum, sum_apply, inner_sum, LinearMap.coe_toContinuousLinearMap',
          LinearMap.comp_apply, LinearMap.adjoint_inner_right, PiLp.inner_apply]
        exact Finset.sum_congr rfl fun k _ => by
          rw [map_mul, map_star, StarAlgEquiv.apply_symm_apply, mul_apply_eq_comp,
            ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
          rfl
    rw [hgram]
    exact (LinearMap.isStarProjection_toContinuousLinearMap_iff.mpr
      A.isPartialIsometry_polarFactor.isStarProjection_adjoint_comp_self).norm_le

private def traceLM {n : Type*} [Fintype n] : CStarMatrix n n ℂ →ₗ[ℂ] ℂ where
  toFun M := Matrix.trace (CStarMatrix.ofMatrix.symm M)
  map_add' _ _ := Matrix.trace_add _ _
  map_smul' c M := Matrix.trace_smul c (CStarMatrix.ofMatrix.symm M)

@[simp]
private theorem traceLM_apply {n : Type*} [Fintype n] (M : CStarMatrix n n ℂ) :
    traceLM M = Matrix.trace (CStarMatrix.ofMatrix.symm M) := rfl

private theorem norm_sum_trace_star_mul_star (x y : ι → CStarMatrix m m ℂ) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (star (x k) * star (y k)))‖ =
      ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * y k))‖ := by
  rw [← norm_star (∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * y k))), star_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by
    rw [← Matrix.trace_conjTranspose, ← CStarMatrix.ofMatrix_symm_star, star_mul,
      CStarMatrix.ofMatrix_symm_mul, CStarMatrix.ofMatrix_symm_mul, Matrix.trace_mul_comm]

/-- **Column-row trace-pairing Hölder inequality**:
`‖∑ k, tr(x k * b k)‖ ≤ ‖rowSquare x‖ * matrixLpGauge 1 (columnSquare b)`. -/
theorem norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare
    (x b : ι → CStarMatrix m m ℂ) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k))‖ ≤
      ‖rowSquare x‖ * matrixLpGauge 1 (columnSquare b) := by
  obtain ⟨u, hbu, hu_norm⟩ := exists_mul_columnSquare_and_norm_columnSquare_le_one b
  have htr : (∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k))) =
      Matrix.trace (CStarMatrix.ofMatrix.symm ((∑ k, x k * u k) * columnSquare b)) := by
    simp_rw [hbu, ← mul_assoc]
    simpa only [traceLM_apply, Finset.sum_mul] using
      (map_sum (traceLM (n := m)) (fun k => (x k * u k) * columnSquare b) Finset.univ).symm
  have hcs : ‖∑ k, x k * u k‖ ≤ ‖rowSquare x‖ := by
    let w := (WithCStarModule.equiv (CStarMatrix m m ℂ) (ι → CStarMatrix m m ℂ)).symm
      fun k => star (u k)
    let v := (WithCStarModule.equiv (CStarMatrix m m ℂ) (ι → CStarMatrix m m ℂ)).symm x
    have hinner : inner (CStarMatrix m m ℂ) w v = ∑ k, x k * u k := by
      rw [WithCStarModule.pi_inner]
      exact Finset.sum_congr rfl fun k _ => by simp [w, v, WithCStarModule.inner_def]
    have hw : ‖w‖ = ‖columnSquare u‖ := by
      rw [WithCStarModule.pi_norm, norm_columnSquare]
      congr 2; exact Finset.sum_congr rfl fun k _ => by simp [w, WithCStarModule.inner_def]
    have hv : ‖v‖ = ‖rowSquare x‖ := by rw [WithCStarModule.pi_norm, norm_rowSquare]; rfl
    rw [← hinner]
    exact (CStarModule.norm_inner_le _).trans <| by
      rw [hw, hv]; exact mul_le_of_le_one_left (norm_nonneg _) hu_norm
  rw [htr]
  exact (norm_trace_mul_le_norm_mul_matrixLpGauge_one _ _).trans
    (mul_le_mul_of_nonneg_right hcs (matrixLpGauge_nonneg 1 _))

/-- **Row-column trace-pairing Hölder inequality**:
`‖∑ k, tr(x k * c k)‖ ≤ ‖columnSquare x‖ * matrixLpGauge 1 (rowSquare c)`. -/
theorem norm_sum_trace_mul_le_norm_columnSquare_mul_matrixLpGauge_one_rowSquare
    (x c : ι → CStarMatrix m m ℂ) :
    ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * c k))‖ ≤
      ‖columnSquare x‖ * matrixLpGauge 1 (rowSquare c) := by
  simpa only [norm_sum_trace_star_mul_star, ← rowSquare_eq_columnSquare_star,
    ← columnSquare_eq_rowSquare_star] using
    norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare
      (fun k => star (x k)) (fun k => star (c k))

private theorem norm_rowSquare_apply_sq_eq [DecidableEq m] (x : ι → CStarMatrix m m ℂ)
    (ξ : EuclideanSpace ℂ m) :
    ‖CStarMatrix.toEuclideanCLM (rowSquare x) ξ‖ ^ 2 =
      ∑ k, ‖CStarMatrix.toEuclideanCLM (star (x k)) ξ‖ ^ 2 := by
  set R := CStarMatrix.toEuclideanCLM (rowSquare x)
  have h1 : ⟪R ξ, R ξ⟫_ℂ =
      ∑ k, ⟪CStarMatrix.toEuclideanCLM (star (x k)) ξ,
        CStarMatrix.toEuclideanCLM (star (x k)) ξ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      ← mul_apply_eq_comp, ← map_star, ← map_mul, (isSelfAdjoint_rowSquare x).star_eq,
      rowSquare_mul_self, map_sum, sum_apply, inner_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ← ContinuousLinearMap.adjoint_inner_left]
  simpa only [inner_self_eq_norm_sq, map_sum] using congrArg RCLike.re h1

private theorem matrixLpGauge_one_columnSquare_rankOne [DecidableEq m]
    (η : ι → EuclideanSpace ℂ m) {ξ : EuclideanSpace ℂ m} (hξ : ‖ξ‖ = 1) {s : ℝ}
    (hs_nonneg : 0 ≤ s) (hs_sq : s ^ 2 = ∑ k, ‖η k‖ ^ 2) :
    matrixLpGauge 1
      (columnSquare fun k =>
        CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ (η k) ξ)) = s := by
  let P := CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ ξ ξ)
  let b := fun k => CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ (η k) ξ)
  have hP : IsStarProjection P :=
    (InnerProductSpace.isStarProjection_rankOne_self hξ).map CStarMatrix.toEuclideanCLM.symm
  have hgram : (∑ k, star (b k) * b k) = (s ^ 2) • P :=
    EquivLike.injective CStarMatrix.toEuclideanCLM <| by
      rw [map_sum, hs_sq, Finset.sum_smul, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (‖η k‖ ^ 2) • P = ((‖η k‖ : ℂ) ^ 2) • P by ext i j; simp, map_mul, map_star,
        map_smul, StarAlgEquiv.apply_symm_apply, StarAlgEquiv.apply_symm_apply,
        ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne,
        ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne,
        inner_self_eq_norm_sq_to_K]
      simp
  have hcol : columnSquare b = s • P := CFC.sqrt_unique
    (by rw [hgram, smul_mul_assoc, mul_smul_comm, smul_smul, ← sq, hP.isIdempotentElem.eq])
    (smul_nonneg hs_nonneg hP.nonneg)
  have htrP : Matrix.trace (CStarMatrix.ofMatrix.symm P) = 1 := by
    rw [← CStarMatrix.trace_toEuclideanCLM, StarAlgEquiv.apply_symm_apply,
      InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, hξ]
    norm_num
  rw [hcol, matrixLpGauge_one_of_nonneg (smul_nonneg hs_nonneg hP.nonneg),
    show CStarMatrix.ofMatrix.symm (s • P) = s • CStarMatrix.ofMatrix.symm P from rfl,
    Matrix.trace_smul, htrP]
  simp

/-- **Converse trace-pairing bound (row norm)**: if
`‖∑ k, tr(x k * b k)‖ ≤ C * matrixLpGauge 1 (columnSquare b)` for every `b`, then
`‖rowSquare x‖ ≤ C`. -/
theorem norm_rowSquare_le_of_forall_norm_sum_trace_mul_le
    {x : ι → CStarMatrix m m ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ b : ι → CStarMatrix m m ℂ,
      ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k))‖ ≤
        C * matrixLpGauge 1 (columnSquare b)) :
    ‖rowSquare x‖ ≤ C := by
  classical
  set R := CStarMatrix.toEuclideanCLM (rowSquare x)
  rw [← CStarMatrix.norm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun ξ hξ => ?_
  let η (k : ι) := CStarMatrix.toEuclideanCLM (star (x k)) ξ
  let b := fun k => CStarMatrix.toEuclideanCLM.symm (InnerProductSpace.rankOne ℂ (η k) ξ)
  have hR_sq : ‖R ξ‖ ^ 2 = ∑ k, ‖η k‖ ^ 2 := norm_rowSquare_apply_sq_eq x ξ
  have hpair :
      ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k)) = ((‖R ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [hR_sq, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← CStarMatrix.trace_toEuclideanCLM, map_mul, StarAlgEquiv.apply_symm_apply,
      ContinuousLinearMap.toLinearMap_mul, InnerProductSpace.trace_mul_rankOne,
      show ⟪ξ, CStarMatrix.toEuclideanCLM (x k) (η k)⟫_ℂ = ⟪η k, η k⟫_ℂ by
        dsimp only [η]
        rw [map_star, ContinuousLinearMap.star_eq_adjoint,
          ← ContinuousLinearMap.adjoint_inner_left],
      inner_self_eq_norm_sq_to_K]
    norm_cast
  have hbound := h b
  rw [hpair, matrixLpGauge_one_columnSquare_rankOne η hξ (norm_nonneg _) hR_sq, Complex.norm_real,
    Real.norm_of_nonneg (sq_nonneg _), sq] at hbound
  by_cases h0 : ‖R ξ‖ = 0
  · linarith
  · exact le_of_mul_le_mul_right hbound (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))

/-- **Converse trace-pairing bound (column norm)**: if
`‖∑ k, tr(x k * c k)‖ ≤ C * matrixLpGauge 1 (rowSquare c)` for every `c`, then
`‖columnSquare x‖ ≤ C`. -/
theorem norm_columnSquare_le_of_forall_norm_sum_trace_mul_le
    {x : ι → CStarMatrix m m ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ c : ι → CStarMatrix m m ℂ,
      ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * c k))‖ ≤
        C * matrixLpGauge 1 (rowSquare c)) :
    ‖columnSquare x‖ ≤ C := by
  rw [columnSquare_eq_rowSquare_star]
  refine norm_rowSquare_le_of_forall_norm_sum_trace_mul_le hC fun b => ?_
  simpa only [← norm_sum_trace_star_mul_star x (fun k => star (b k)), star_star,
    rowSquare_eq_columnSquare_star] using h (fun k => star (b k))

end TraceDuality

/-! ### Hahn–Banach trace representation and the `p = 1` Khintchine inequality -/

section KhintchineOne

private theorem exists_dual_eq_seminorm_and_norm_le {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) (a : E) :
    ∃ g : Module.Dual ℂ E, g a = (p a : ℂ) ∧ ∀ y, ‖g y‖ ≤ p y := by
  by_cases hpa : p a = 0
  · exact ⟨0, by simp [hpa], fun y => by simp [apply_nonneg p y]⟩
  · have ha : a ≠ 0 := fun h => hpa (h ▸ map_zero p)
    let f : Module.Dual ℂ (ℂ ∙ a) := (p a : ℂ) • (LinearEquiv.coord ℂ E a ha).toLinearMap
    have hf (y : ℂ ∙ a) : ‖f y‖ ≤ p y := by
      rw [← LinearEquiv.coord_apply_smul ℂ E a ha y, map_smul_eq_mul p]
      simp [f, Real.norm_of_nonneg (apply_nonneg p a), mul_comm]
    obtain ⟨g, hg, hgle⟩ := Module.Dual.exists_extension_of_le_seminorm (ℂ ∙ a) f hf
    exact ⟨g,
      by simpa [f, LinearEquiv.coord_self] using hg ⟨a, Submodule.mem_span_singleton_self a⟩, hgle⟩

private theorem exists_trace_rep_of_dual {ι m : Type*} [Fintype ι] [Fintype m]
    (φ : Module.Dual ℂ (ι → CStarMatrix m m ℂ)) :
    ∃ x : ι → CStarMatrix m m ℂ, ∀ b : ι → CStarMatrix m m ℂ,
      φ b = ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (x k * b k)) := by
  classical
  let emb (k : ι) : Matrix m m ℂ →ₗ[ℂ] (ι → CStarMatrix m m ℂ) :=
    { toFun := fun M => Pi.single (M := fun _ : ι => CStarMatrix m m ℂ) k (CStarMatrix.ofMatrix M)
      map_add' := fun _ _ => by ext k' i j; by_cases hk : k' = k <;> simp [hk]
      map_smul' := fun _ _ => by ext k' i j; by_cases hk : k' = k <;> simp [hk] }
  refine ⟨fun k => CStarMatrix.ofMatrix fun p q => φ (emb k (Matrix.single q p 1)), fun b => ?_⟩
  have hb : b = ∑ k, emb k (∑ q, ∑ p, (b k q p) • Matrix.single q p 1) := by
    conv_lhs => rw [← Finset.univ_sum_single b]
    refine Finset.sum_congr rfl fun k _ => ?_
    change emb k (CStarMatrix.ofMatrix.symm (b k)) = _
    exact congrArg (emb k) (by
      simpa [Matrix.smul_single] using
        Matrix.matrix_eq_sum_single (CStarMatrix.ofMatrix.symm (b k)))
  conv_lhs => rw [hb]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag_apply, CStarMatrix.ofMatrix_symm_mul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => mul_comm _ _

private theorem sum_trace_expect_units_smul_mul {ι m : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype m] (Φ : (ι → ℤˣ) → CStarMatrix m m ℂ) (b : ι → CStarMatrix m m ℂ) :
    (∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm ((𝔼 ε : ι → ℤˣ, ε k • Φ ε) * b k))) =
      𝔼 ε : ι → ℤˣ, Matrix.trace (CStarMatrix.ofMatrix.symm (Φ ε * ∑ k, ε k • b k)) := by
  let f (M₀ : CStarMatrix m m ℂ) : CStarMatrix m m ℂ →ₗ[ℚ≥0] ℂ :=
    { toFun := fun M => traceLM (M * M₀)
      map_add' := fun _ _ => by rw [add_mul, map_add]
      map_smul' := fun _ _ => by simp [CStarMatrix.smul_mul] }
  have hcomm (ε : ι → ℤˣ) (k : ι) : (ε k • Φ ε) * b k = Φ ε * (ε k • b k) := by
    rcases Int.units_eq_one_or (ε k) with h | h <;> simp [h]
  have hlhs (k : ι) :
      Matrix.trace (CStarMatrix.ofMatrix.symm ((𝔼 ε : ι → ℤˣ, ε k • Φ ε) * b k)) =
        𝔼 ε : ι → ℤˣ, Matrix.trace (CStarMatrix.ofMatrix.symm (Φ ε * (ε k • b k))) := by
    simpa only [f, traceLM_apply, LinearMap.coe_mk, AddHom.coe_mk, hcomm] using
      map_expect (f (b k)) (fun ε : ι → ℤˣ => ε k • Φ ε) Finset.univ
  simp_rw [hlhs]
  rw [← Finset.expect_sum_comm]
  refine Finset.expect_congr rfl fun ε _ => ?_
  simpa only [traceLM_apply, Finset.mul_sum] using
    (map_sum (traceLM (n := m)) (fun k => Φ ε * (ε k • b k)) Finset.univ).symm

/-- Upper bound in the `p = 1` noncommutative Khintchine inequality:
`randomSumGauge 1 a ≤ rowColumnSumGauge 1 a`. -/
theorem randomSumGauge_one_le_rowColumnSumGauge {ι m : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype m] (a : ι → CStarMatrix m m ℂ) :
    randomSumGauge 1 a ≤ rowColumnSumGauge 1 a := by
  have hcol_le (b : ι → CStarMatrix m m ℂ) :
      randomSumGauge 1 b ≤ matrixLpGauge 1 (columnSquare b) := by
    choose Φ hΦ_norm hΦ_tr using fun ε : ι → ℤˣ =>
      exists_norm_le_one_and_trace_mul_eq_matrixLpGauge_one (∑ k, ε k • b k)
    let y : ι → CStarMatrix m m ℂ := fun k => 𝔼 ε : ι → ℤˣ, ε k • Φ ε
    have hexp_eq : ((randomSumGauge 1 b : ℝ) : ℂ) =
        ∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (y k * b k)) := by
      rw [randomSumGauge_one_eq_expect_units,
        show (((𝔼 ε : ι → ℤˣ, matrixLpGauge 1 (∑ k, ε k • b k)) : ℝ) : ℂ) =
            𝔼 ε : ι → ℤˣ, ((matrixLpGauge 1 (∑ k, ε k • b k) : ℝ) : ℂ) from
          map_expect (Complex.ofRealLI.toLinearMap.restrictScalars ℚ≥0) _ _]
      simp_rw [← hΦ_tr]
      exact (sum_trace_expect_units_smul_mul Φ b).symm
    calc randomSumGauge 1 b
        = ‖((randomSumGauge 1 b : ℝ) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_of_nonneg (randomSumGauge_nonneg 1 b)]
      _ = ‖∑ k, Matrix.trace (CStarMatrix.ofMatrix.symm (y k * b k))‖ := by rw [hexp_eq]
      _ ≤ ‖rowSquare y‖ * matrixLpGauge 1 (columnSquare b) :=
            norm_sum_trace_mul_le_norm_rowSquare_mul_matrixLpGauge_one_columnSquare y b
      _ ≤ matrixLpGauge 1 (columnSquare b) :=
            mul_le_of_le_one_left (matrixLpGauge_nonneg 1 _)
              (norm_rowSquare_expect_units_smul_le zero_le_one hΦ_norm)
  have hrow_le (c : ι → CStarMatrix m m ℂ) :
      randomSumGauge 1 c ≤ matrixLpGauge 1 (rowSquare c) := by
    have hstar : randomSumGauge 1 c = randomSumGauge 1 (fun k => star (c k)) := by
      rw [randomSumGauge_one_eq_expect_units, randomSumGauge_one_eq_expect_units]
      refine Finset.expect_congr rfl fun ε _ => ?_
      rw [← matrixLpGauge_star 1 (∑ k, ε k • c k), star_sum]
      congr 1; exact Finset.sum_congr rfl fun k _ => by
        rcases Int.units_eq_one_or (ε k) with h | h <;> simp [h]
    rw [hstar, rowSquare_eq_columnSquare_star]
    exact hcol_le (fun k => star (c k))
  refine le_csInf ⟨_, a, 0, (add_zero a).symm, rfl⟩ fun _ ⟨b, c, h, hr⟩ => ?_
  rw [hr, h]
  exact (randomSumGauge_one_add_le b c).trans (add_le_add (hcol_le b) (hrow_le c))

/-- Lower bound in the `p = 1` noncommutative Khintchine inequality:
`(Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a`. -/
theorem inv_sqrt_three_mul_rowColumnSumGauge_le_randomSumGauge_one {ι m : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype m] (a : ι → CStarMatrix m m ℂ) :
    (Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a := by
  obtain ⟨φ, hφ_a, hφ_le⟩ :=
    exists_dual_eq_seminorm_and_norm_le (rowColumnSumSeminorm ι m 1 le_rfl) a
  obtain ⟨x, hφ_tr⟩ := exists_trace_rep_of_dual φ
  have hx_row : ‖rowSquare x‖ ≤ 1 :=
    norm_rowSquare_le_of_forall_norm_sum_trace_mul_le zero_le_one fun b => by
      rw [one_mul, ← hφ_tr b]
      exact (hφ_le b).trans (rowColumnSumGauge_le_columnSquare zero_lt_one b)
  have hx_col : ‖columnSquare x‖ ≤ 1 :=
    norm_columnSquare_le_of_forall_norm_sum_trace_mul_le zero_le_one fun c => by
      rw [one_mul, ← hφ_tr c]
      exact (hφ_le c).trans (rowColumnSumGauge_le_rowSquare zero_lt_one c)
  obtain ⟨Φ, hΦ_exp, hΦ_norm⟩ := exists_expect_units_smul_eq_and_norm_le x
  have hΦ_le (ε : ι → ℤˣ) : ‖Φ ε‖ ≤ Real.sqrt 3 :=
    (hΦ_norm ε).trans (mul_le_of_le_one_right (Real.sqrt_nonneg 3) (max_le hx_col hx_row))
  have hpair : (rowColumnSumGauge 1 a : ℂ) =
      𝔼 ε : ι → ℤˣ, Matrix.trace (CStarMatrix.ofMatrix.symm (Φ ε * ∑ k, ε k • a k)) := by
    rw [← show φ a = (rowColumnSumGauge 1 a : ℂ) from hφ_a, hφ_tr a]
    simp_rw [← hΦ_exp]
    exact sum_trace_expect_units_smul_mul Φ a
  have hbound : rowColumnSumGauge 1 a ≤ Real.sqrt 3 * randomSumGauge 1 a := by
    have hre : rowColumnSumGauge 1 a =
        𝔼 ε : ι → ℤˣ, (Matrix.trace (CStarMatrix.ofMatrix.symm (Φ ε * ∑ k, ε k • a k))).re :=
      (Complex.ofReal_re _).symm.trans ((congrArg Complex.re hpair).trans
        (map_expect (Complex.reLm.restrictScalars ℚ≥0) _ _))
    rw [hre, randomSumGauge_one_eq_expect_units, Finset.mul_expect]
    exact Finset.expect_le_expect fun ε _ =>
      (le_abs_self _).trans <| (abs_re_trace_mul_le_norm_mul_matrixLpGauge_one _ _).trans
        (mul_le_mul_of_nonneg_right (hΦ_le ε) (matrixLpGauge_nonneg 1 _))
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact (inv_mul_le_iff₀ hsqrt_pos).mpr hbound

/-- **The `p = 1` noncommutative Khintchine inequality for matrices** (Lust-Piquard–Pisier,
Haagerup–Musat): for any finite index types `ι` and `m` and any family
`a : ι → CStarMatrix m m ℂ`,
`(√3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a ≤ rowColumnSumGauge 1 a`. -/
theorem khintchine_one {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
    (a : ι → CStarMatrix m m ℂ) :
    (Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a ∧
      randomSumGauge 1 a ≤ rowColumnSumGauge 1 a :=
  ⟨inv_sqrt_three_mul_rowColumnSumGauge_le_randomSumGauge_one a,
    randomSumGauge_one_le_rowColumnSumGauge a⟩

/-- Specialization of `TauCeti.khintchine_one` to `Fin n → CStarMatrix (Fin d) (Fin d) ℂ`. -/
theorem matrix_khintchine_one (d n : ℕ) (a : Fin n → CStarMatrix (Fin d) (Fin d) ℂ) :
    (Real.sqrt 3)⁻¹ * rowColumnSumGauge 1 a ≤ randomSumGauge 1 a ∧
      randomSumGauge 1 a ≤ rowColumnSumGauge 1 a :=
  khintchine_one a

end KhintchineOne

end TauCeti
