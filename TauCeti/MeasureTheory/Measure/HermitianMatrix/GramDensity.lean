/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.MeasureTheory.Measure.HermitianMatrix.Corner
public import TauCeti.MeasureTheory.Measure.Lebesgue.Matrix
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.MeasureTheory.Measure.Haar.Matrix.Complex

/-!
# The density of the Gram map near the identity, and the volume of `U(n)`

The volume of the unitary group `U(n)` is
`vol U(n) = ∏_{1 ≤ i ≤ n} 2 π ^ i / (i - 1)!` (`TauCeti.unitaryGroupVolume`), the product of
the areas of the unit spheres of `ℂ, ℂ², …, ℂⁿ`. It is the constant in the image of Lebesgue
measure under the Gram map `Y ↦ Yᴴ Y` (`Matrix.hermitianGram`) of complex `n × n` matrices: near
the identity, this image is `vol U(n) / 2 ^ n` times Lebesgue measure `TauCeti.hermitianLebesgue n`
on Hermitian matrices, in the coordinates `T_aa`, `Re T_ab`, `Im T_ab` (`a < b`)
(`TauCeti.exists_lintegral_hermitianGram_eq`, and as an equality of measures
`TauCeti.exists_restrict_map_hermitianGram_eq`).

The proof is by induction on `n`, adding one column `v` at a time. A unitary matrix moves `v` to
`√r` times the last basis vector, where `r = ∑ ‖v i‖²`
(`Matrix.exists_mem_unitaryGroup_mulVec_eq`). The other `n - 1` columns then consist of a square
matrix `X` of size `n - 1` and a row `wᴴ`, and their Gram matrix is `Xᴴ X + w wᴴ`, so the case
`n - 1` applies to `X` after a translation. Splitting a Hermitian matrix into its upper left
block, last column and corner (`TauCeti.hermitianCornerEquiv`) matches the Gram matrix of all `n`
columns with `(Xᴴ X + w wᴴ, √r w, r)`. The squared norm `r` of `v` has density
`π ^ n r ^ (n - 1) / (n - 1)!` (`TauCeti.measurePreserving_sum_norm_sq`), whose power of `r`
cancels the Jacobian `r ^ (n - 1)` of `w ↦ √r w`; this leaves the factor
`π ^ n / (n - 1)! = (2 π ^ n / (n - 1)!) / 2` by which `vol U(n) / 2 ^ n` grows.

## Main definitions

* `TauCeti.unitaryGroupVolume n`: the number `vol U(n)`.
* `Matrix.hermitianGram Y`: the Gram matrix `Yᴴ Y`, as a Hermitian matrix.

## Main results

* `TauCeti.exists_lintegral_hermitianGram_eq`: there is an open set `W` of Hermitian matrices
  containing `1` such that `∫ G (Yᴴ Y) dY = (vol U(n) / 2 ^ n) ∫ G(T) dT` for every measurable
  `G ≥ 0` supported in `W`.
* `TauCeti.exists_restrict_map_hermitianGram_eq`: the same statement for measures.
* `TauCeti.volume_sum_norm_sq_lt`, `TauCeti.measurePreserving_sum_norm_sq`: the volume of the
  ball `∑ ‖ω i‖² < a` of `ℂ ^ k`, and the law of `∑ ‖ω i‖²` under Lebesgue measure.
* `Matrix.exists_mem_unitaryGroup_mulVec_eq`: two vectors of the same length differ by a unitary
  matrix.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC): `New.volU` (`src/Lib/DiscreteSeries/Haar/CayleyChart.lean`) and
`New.exists_hasGramDensity`, `New.HasGramDensity.succ`,
`New.HasGramDensity.lintegral_conjTranspose_mulVec`, `New.measurePreserving_normSq_sphereDensity`,
`New.volume_map_normSq_Iio` and `New.exists_unitary_mulVec_eq`
(`src/Lib/DiscreteSeries/Haar/TotalMass.lean`). There the Hermitian matrices carry real
coordinates of their own (`gramCoords`, `hermOfReal`) and the index type is arbitrary; here the
statements use `TauCeti.hermitianLebesgue` on the Hermitian submodule and induct along `Fin`.

## References

* L. K. Hua, *Harmonic analysis of functions of several complex variables in the classical
  domains*, Translations of Mathematical Monographs 6, AMS (1963), Chapter III.
* I. G. Macdonald, *The volume of a compact Lie group*, Invent. Math. 56 (1980), 93–95.
-/

public section

noncomputable section

open MeasureTheory Matrix Set Real
open scoped ENNReal Nat

namespace TauCeti

/-- The volume of the unitary group `U(n)`, `∏_{1 ≤ i ≤ n} 2 π ^ i / (i - 1)!`: the product of the
areas of the unit spheres of `ℂ, ℂ², …, ℂⁿ`. -/
def unitaryGroupVolume (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, 2 * π ^ (i + 1) / i !

/-- The volume of `U(0)` is `1`. -/
@[simp] theorem unitaryGroupVolume_zero : unitaryGroupVolume 0 = 1 := by
  simp [unitaryGroupVolume]

/-- `vol U(n + 1)` is `vol U(n)` times the area `2 π ^ (n + 1) / n!` of the unit sphere of
`ℂ ^ (n + 1)`. -/
theorem unitaryGroupVolume_succ (n : ℕ) :
    unitaryGroupVolume (n + 1) = unitaryGroupVolume n * (2 * π ^ (n + 1) / n !) :=
  Finset.prod_range_succ _ n

/-- The volume of `U(n)` is positive. -/
theorem unitaryGroupVolume_pos (n : ℕ) : 0 < unitaryGroupVolume n :=
  Finset.prod_pos fun i _ ↦ by positivity

/-- The volume of the set `∑ ‖ω i‖² < a` in `ℂ ^ ι` is `a ^ k π ^ k / k!`, `k = card ι`. -/
theorem volume_sum_norm_sq_lt {ι : Type*} [Fintype ι] [Nonempty ι] {a : ℝ} (ha : 0 ≤ a) :
    volume {ω : ι → ℂ | ∑ i, ‖ω i‖ ^ 2 < a} =
      ENNReal.ofReal (a ^ Fintype.card ι * (π ^ Fintype.card ι / (Fintype.card ι)!)) := by
  have h_set : {ω : ι → ℂ | ∑ i, ‖ω i‖ ^ 2 < a} =
      {ω : ι → ℂ | (∑ i, ‖ω i‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) < √a} := by
    ext ω
    rw [mem_ofPred_eq, mem_ofPred_eq, ← Real.sqrt_eq_rpow, Real.sqrt_lt_sqrt_iff (by positivity)]
    simp only [Real.rpow_two]
  rw [h_set, Complex.volume_sum_rpow_lt _ one_le_two, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), pow_mul, Real.sq_sqrt ha]
  congr 2
  have h2 : Real.Gamma (2 / 2 + 1) = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  rw [h2, mul_one, mul_div_cancel_left₀ _ two_ne_zero, Real.Gamma_nat_eq_factorial]

/-- The map `ω ↦ ∑ ‖ω i‖²` carries Lebesgue measure on `ℂ ^ ι` to the measure on `(0, ∞)` with
density `π ^ k r ^ (k - 1) / (k - 1)!`, where `k = card ι ≥ 1`: the sphere of radius `√r` has
area `2 π ^ k r ^ (k - 1 / 2) / (k - 1)!`. -/
theorem measurePreserving_sum_norm_sq {ι : Type*} [Fintype ι] [Nonempty ι] :
    MeasurePreserving (fun ω : ι → ℂ ↦ ∑ i, ‖ω i‖ ^ 2) volume
      ((volume.restrict (Ioi 0)).withDensity fun r ↦
        ENNReal.ofReal (π ^ Fintype.card ι * r ^ (Fintype.card ι - 1) /
          (Fintype.card ι - 1)!)) := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  rw [hm, Nat.add_sub_cancel]
  have h_pre (a : ℝ) :
      (fun ω : ι → ℂ ↦ ∑ i, ‖ω i‖ ^ 2) ⁻¹' Iio a = {ω | ∑ i, ‖ω i‖ ^ 2 < a} := (rfl)
  -- Both measures give `Iio a` the volume of the ball of radius `√a`.
  refine ⟨by fun_prop, Measure.ext_of_generateFrom_of_iUnion _ (fun n : ℕ ↦ Iio (n : ℝ))
    (borel_eq_generateFrom_Iio ℝ) isPiSystem_Iio (iUnion_eq_univ_iff.2 exists_nat_gt) ?_ ?_ ?_⟩
  · simp
  · intro n
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio, h_pre,
      volume_sum_norm_sq_lt n.cast_nonneg]
    exact ENNReal.ofReal_ne_top
  rintro _ ⟨a, rfl⟩
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio, withDensity_apply _ measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  rcases le_or_gt a 0 with ha | ha
  · have h_empty : (fun ω : ι → ℂ ↦ ∑ i, ‖ω i‖ ^ 2) ⁻¹' Iio a = ∅ :=
      eq_empty_of_forall_notMem fun ω (hω : _ < a) ↦ hω.not_ge (ha.trans (by positivity))
    have h_inter : Iio a ∩ Ioi (0 : ℝ) = ∅ :=
      eq_empty_of_forall_notMem fun r ⟨h₁, h₂⟩ ↦ (lt_trans h₂ h₁).not_ge ha
    simp [h_empty, h_inter]
  rw [h_pre, volume_sum_norm_sq_lt ha.le, hm, inter_comm, Ioi_inter_Iio,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (Continuous.integrableOn_Ioc (by fun_prop))
      (ae_restrict_of_forall_mem measurableSet_Ioc fun r hr ↦ by have := hr.1.le; positivity),
    ← intervalIntegral.integral_of_le ha.le]
  congr 1
  simp only [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
  push_cast [Nat.factorial_succ]
  field_simp
  ring

end TauCeti

namespace Matrix

variable {l m : Type*} [Fintype l]

/-- The Gram matrix `Yᴴ Y` of the columns of a complex matrix `Y`, as a Hermitian matrix. -/
def hermitianGram (Y : Matrix l m ℂ) : selfAdjoint.submodule ℝ (Matrix m m ℂ) :=
  ⟨Yᴴ * Y, (isHermitian_conjTranspose_mul_self Y).isSelfAdjoint⟩

/-- The underlying matrix of `hermitianGram Y` is `Yᴴ * Y`. -/
@[simp] theorem coe_hermitianGram (Y : Matrix l m ℂ) :
    (hermitianGram Y : Matrix m m ℂ) = Yᴴ * Y := (rfl)

/-- The Gram map is continuous. -/
@[fun_prop] theorem continuous_hermitianGram :
    Continuous (hermitianGram : Matrix l m ℂ → _) :=
  (Continuous.matrix_mul (by fun_prop) continuous_id).subtype_mk _

/-- The Gram map is measurable. -/
@[fun_prop] theorem measurable_hermitianGram [Finite m] :
    Measurable (hermitianGram : Matrix l m ℂ → _) :=
  continuous_hermitianGram.measurable

/-- Two vectors of `ℂ ^ ι` of the same length differ by a unitary matrix. -/
theorem exists_mem_unitaryGroup_mulVec_eq [DecidableEq l] {x y : l → ℂ}
    (h : ∑ i, ‖x i‖ ^ 2 = ∑ i, ‖y i‖ ^ 2) : ∃ u ∈ unitaryGroup l ℂ, u *ᵥ x = y := by
  obtain ⟨e, he⟩ := TauCeti.exists_linearIsometryEquiv_of_inner_eq (𝕜 := ℂ)
    (v := fun _ : Unit ↦ WithLp.toLp 2 x) (w := fun _ : Unit ↦ WithLp.toLp 2 y) fun _ _ ↦ by
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
      have hx := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 x)
      have hy := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 y)
      exact_mod_cast hx.trans (h.trans hy.symm)
  refine ⟨UnitaryGroup.ofLinearIsometryEquiv e, SetLike.coe_mem _, ?_⟩
  have := UnitaryGroup.toLinearIsometryEquiv_apply (UnitaryGroup.ofLinearIsometryEquiv e)
    (WithLp.toLp 2 x)
  rw [UnitaryGroup.toLinearIsometryEquiv_ofLinearIsometryEquiv, he ()] at this
  exact congrArg WithLp.ofLp this.symm

end Matrix

namespace TauCeti

open Matrix

variable {k : ℕ}

/-- The Hermitian matrix `w wᴴ`. -/
private def outer (w : Fin k → ℂ) : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ) :=
  hermitianGram (replicateRow (Fin 1) (star w))

private theorem coe_outer (w : Fin k → ℂ) :
    (outer w : Matrix (Fin k) (Fin k) ℂ) = vecMulVec w (star w) := by
  simp only [outer, coe_hermitianGram, conjTranspose_replicateRow, star_star]
  exact (vecMulVec_eq (Fin 1) _ _).symm

@[fun_prop] private theorem continuous_outer : Continuous (outer : (Fin k → ℂ) → _) :=
  continuous_hermitianGram.comp (by fun_prop)

/-- The Gram map `Y ↦ Yᴴ Y` of square matrices of size `k` has density `c` on `W`: on `W` it
carries Lebesgue measure to `c` times `hermitianLebesgue k`. -/
private def HasGramDensity (k : ℕ) (W : Set (selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ)))
    (c : ℝ≥0∞) : Prop :=
  ∀ G : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ) → ℝ≥0∞, Measurable G → G.support ⊆ W →
    ∫⁻ Y : Matrix (Fin k) (Fin k) ℂ, G (hermitianGram Y) = c * ∫⁻ T, G T ∂hermitianLebesgue k

/-- The matrix with the rows of `X` followed by the row `wᴴ`. -/
private def snocRow (X : Matrix (Fin k) (Fin k) ℂ) (w : Fin k → ℂ) :
    Matrix (Fin (k + 1)) (Fin k) ℂ :=
  of fun i j ↦ Fin.lastCases (star (w j)) (fun i ↦ X i j) i

private theorem measurePreserving_snocRow :
    MeasurePreserving (fun p : Matrix (Fin k) (Fin k) ℂ × (Fin k → ℂ) ↦ snocRow p.1 p.2) := by
  have h_star : MeasurePreserving (star : (Fin k → ℂ) → (Fin k → ℂ)) :=
    volume_preserving_pi fun _ ↦ Complex.conjLIE.measurePreserving
  have h := (Matrix.volume_preserving_ofMeasurableEquiv _ _ ℂ).comp <|
    ((volume_preserving_piFinSuccAbove (fun _ ↦ Fin k → ℂ) (Fin.last k)).symm _).comp <|
      (h_star.prod ((Matrix.volume_preserving_ofMeasurableEquiv _ _ ℂ).symm _)).comp
        (Measure.measurePreserving_swap (μ := volume) (ν := volume))
  convert h using 1
  funext p
  ext i j
  cases i using Fin.lastCases <;>
    simp [snocRow, Matrix.ofMeasurableEquiv_apply]

private theorem conjTranspose_snocRow_mul_snocRow (X : Matrix (Fin k) (Fin k) ℂ)
    (w : Fin k → ℂ) : (snocRow X w)ᴴ * snocRow X w = Xᴴ * X + vecMulVec w (star w) := by
  ext a b
  simp [snocRow, Matrix.mul_apply, Fin.sum_univ_castSucc, vecMulVec_apply, mul_comm]

private theorem enorm_det_of_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : Matrix ι ι ℂ} (hu : u ∈ unitaryGroup ι ℂ) : ‖u.det‖ₑ = 1 := by
  rw [← ofReal_norm, CStarRing.norm_of_mem_unitary (det_of_mem_unitary hu), ENNReal.ofReal_one]

/-- Left multiplication by a unitary matrix preserves Lebesgue measure on matrices. -/
private theorem lintegral_unitary_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {u : Matrix ι ι ℂ} (hu : u ∈ unitaryGroup ι ℂ) (g : Matrix ι κ ℂ → ℝ≥0∞) :
    ∫⁻ Y, g (u * Y) = ∫⁻ Y, g Y := by
  classical
  have hdet : u.det ≠ 0 := fun h ↦ by simpa [h] using enorm_det_of_mem_unitaryGroup hu
  conv_rhs => rw [lintegral_eq_enorm_det_pow_mul_enorm_det_pow_mul_lintegral_comp_matrix_mul_mul
    hdet (Q := (1 : Matrix κ κ ℂ)) (by simp) g]
  simp [enorm_det_of_mem_unitaryGroup hu]

/-- Scaling `ℂ ^ k` by `t > 0` multiplies Lebesgue measure by `t ^ (2 k)`. -/
private theorem lintegral_ofReal_smul {t : ℝ} (ht : 0 < t) (g : (Fin k → ℂ) → ℝ≥0∞) :
    ∫⁻ w, g ((t : ℂ) • w) = ENNReal.ofReal (t ^ (2 * k))⁻¹ * ∫⁻ w, g w := by
  have h := lintegral_comp_mulVec (u := (t : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ))
    (by simp [ht.ne']) g
  simp only [smul_mulVec, one_mulVec, det_smul, det_one, mul_one, Fintype.card_fin, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h
  rw [h, ← inv_pow, ← pow_mul, mul_comm k 2, inv_pow]

private theorem hermitianGram_mul_snocRow {u : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hu : u ∈ unitaryGroup (Fin (k + 1)) ℂ) (X : Matrix (Fin k) (Fin k) ℂ) (w : Fin k → ℂ) :
    hermitianGram (u * snocRow X w) = hermitianGram X + outer w := by
  refine Subtype.ext ?_
  rw [coe_hermitianGram, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff'.1 hu, Matrix.one_mul, Submodule.coe_add,
    coe_hermitianGram, coe_outer, conjTranspose_snocRow_mul_snocRow]

private theorem conjTranspose_mul_snocRow_mulVec {u : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hu : u ∈ unitaryGroup (Fin (k + 1)) ℂ) (X : Matrix (Fin k) (Fin k) ℂ) (w : Fin k → ℂ)
    (t : ℝ) : (u * snocRow X w)ᴴ *ᵥ (u *ᵥ Pi.single (Fin.last k) (t : ℂ)) = (t : ℂ) • w := by
  rw [conjTranspose_mul, mulVec_mulVec, Matrix.mul_assoc, ← star_eq_conjTranspose u,
    mem_unitaryGroup_iff'.1 hu, Matrix.mul_one]
  ext a
  simp [snocRow, mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]

private theorem inv_sq_smul_outer_smul {t : ℝ} (ht : t ≠ 0) (w : Fin k → ℂ) :
    (t ^ 2)⁻¹ • outer ((t : ℂ) • w) = outer w := by
  refine Subtype.ext ?_
  ext a b
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  simp only [Submodule.coe_smul, coe_outer, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
    Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal,
    Complex.real_smul]
  push_cast
  field_simp

/-- The step from `k` columns to `k + 1` rows, for one fixed last column `v`: fix `v` with
`r = ∑ ‖v i‖² > 0`, and suppose that the Gram map in size `k` has density `c` on `W`. The map
sending a matrix `Y` with `k + 1` rows and `k` columns to its Gram matrix and to `Yᴴ v` carries
Lebesgue measure to `c / r ^ k` times Lebesgue measure, on the set where the Gram matrix minus
`r⁻¹ (Yᴴ v) (Yᴴ v)ᴴ` lies in `W`. -/
private theorem HasGramDensity.lintegral_conjTranspose_mulVec
    {W : Set (selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ))} {c : ℝ≥0∞}
    (hW : HasGramDensity k W c) {v : Fin (k + 1) → ℂ} (hv : 0 < ∑ i, ‖v i‖ ^ 2)
    {F : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ) × (Fin k → ℂ) → ℝ≥0∞}
    (hF : Measurable F) (h_supp : ∀ p, F p ≠ 0 → p.1 - (∑ i, ‖v i‖ ^ 2)⁻¹ • outer p.2 ∈ W) :
    ENNReal.ofReal ((∑ i, ‖v i‖ ^ 2) ^ k) *
        ∫⁻ Y : Matrix (Fin (k + 1)) (Fin k) ℂ, F (hermitianGram Y, Yᴴ *ᵥ v) =
      c * ∫⁻ p, F p ∂((hermitianLebesgue k).prod volume) := by
  set r := ∑ i, ‖v i‖ ^ 2
  -- Rotate `v` to `√r` times the last basis vector. Then `Y` consists of a square matrix `X` and
  -- a last row `wᴴ`; its Gram matrix is `Xᴴ X + w wᴴ` and its product with `v` is `√r w`.
  obtain ⟨u, hu, huv⟩ := exists_mem_unitaryGroup_mulVec_eq
    (x := Pi.single (Fin.last k) (√r : ℂ)) (y := v) (by
      rw [Finset.sum_eq_single (Fin.last k) (fun i _ hi ↦ by simp [hi]) (by simp)]
      simp [Real.sq_sqrt hv.le, r])
  have h_gram := hermitianGram_mul_snocRow hu
  have h_prod (X : Matrix (Fin k) (Fin k) ℂ) (w : Fin k → ℂ) :
      (u * snocRow X w)ᴴ *ᵥ v = (√r : ℂ) • w := by
    rw [← huv, conjTranspose_mul_snocRow_mulVec hu]
  have h_outer (w : Fin k → ℂ) : r⁻¹ • outer ((√r : ℂ) • w) = outer w := by
    simpa [Real.sq_sqrt hv.le] using inv_sq_smul_outer_smul (Real.sqrt_pos.2 hv).ne' w
  -- For fixed `w`, the translate of `F` by `outer w` is supported in `W`.
  have h_inner (w : Fin k → ℂ) :
      ∫⁻ X : Matrix (Fin k) (Fin k) ℂ, F (hermitianGram X + outer w, (√r : ℂ) • w) =
        c * ∫⁻ T, F (T, (√r : ℂ) • w) ∂hermitianLebesgue k := by
    rw [hW (fun T ↦ F (T + outer w, (√r : ℂ) • w)) (by fun_prop) fun T hT ↦ by
        simpa only [h_outer, add_sub_cancel_right] using h_supp _ hT,
      lintegral_add_right_eq_self (fun T ↦ F (T, (√r : ℂ) • w))]
  calc _ = ENNReal.ofReal (r ^ k) *
        ∫⁻ w, ∫⁻ X : Matrix (Fin k) (Fin k) ℂ, F (hermitianGram X + outer w, (√r : ℂ) • w) := by
        rw [← lintegral_unitary_mul hu, ← measurePreserving_snocRow.lintegral_comp (by fun_prop)]
        simp only [h_gram, h_prod]
        rw [Measure.volume_eq_prod, lintegral_prod_symm' _ (by fun_prop)]
    _ = ENNReal.ofReal (r ^ k) * ∫⁻ w, c * ∫⁻ T, F (T, (√r : ℂ) • w) ∂hermitianLebesgue k := by
        simp only [h_inner]
    _ = ∫⁻ w, c * ∫⁻ T, F (T, w) ∂hermitianLebesgue k := by
        rw [lintegral_ofReal_smul (Real.sqrt_pos.2 hv)
          (fun w ↦ c * ∫⁻ T, F (T, w) ∂hermitianLebesgue k), ← mul_assoc,
          pow_mul, Real.sq_sqrt hv.le, ← ENNReal.ofReal_mul (by positivity),
          mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
    _ = c * ∫⁻ p, F p ∂((hermitianLebesgue k).prod volume) := by
        rw [lintegral_prod_symm' _ hF, lintegral_const_mul c (by fun_prop)]

/-- The square matrix with the columns of `Y` followed by the column `v`. -/
private def snocCol (Y : Matrix (Fin (k + 1)) (Fin k) ℂ) (v : Fin (k + 1) → ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  of fun i j ↦ Fin.lastCases (v i) (fun j ↦ Y i j) j

private theorem measurePreserving_snocCol :
    MeasurePreserving
      (fun p : Matrix (Fin (k + 1)) (Fin k) ℂ × (Fin (k + 1) → ℂ) ↦ snocCol p.1 p.2) := by
  have h_rows : MeasurePreserving fun (z : Fin (k + 1) → ℂ × (Fin k → ℂ)) i ↦
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℂ) (Fin.last k)).symm (z i) :=
    volume_preserving_pi fun _ ↦ (volume_preserving_piFinSuccAbove (fun _ ↦ ℂ) (Fin.last k)).symm _
  have h := (Matrix.volume_preserving_ofMeasurableEquiv _ _ ℂ).comp <| h_rows.comp <|
    ((volume_measurePreserving_arrowProdEquivProdArrow ℂ (Fin k → ℂ) (Fin (k + 1))).symm _).comp <|
      (Measure.measurePreserving_swap (μ := volume) (ν := volume)).comp
        (((Matrix.volume_preserving_ofMeasurableEquiv _ _ ℂ).symm _).prod (.id volume))
  convert h using 1
  funext p
  ext i j
  cases j using Fin.lastCases <;>
    simp [snocCol, Matrix.ofMeasurableEquiv_apply] <;> rfl

/-- The Gram matrix of `snocCol Y v`, split by `hermitianCornerEquiv`: the Gram matrix of `Y`, the
products `Yᴴ v` and the squared norm of `v`. -/
private theorem hermitianCornerEquiv_hermitianGram_snocCol (Y : Matrix (Fin (k + 1)) (Fin k) ℂ)
    (v : Fin (k + 1) → ℂ) :
    hermitianCornerEquiv k (hermitianGram (snocCol Y v)) =
      (hermitianGram Y, Yᴴ *ᵥ v, ∑ i, ‖v i‖ ^ 2) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · rw [coe_hermitianCornerEquiv_fst]
    ext a b
    simp [snocCol, Matrix.mul_apply]
  · rw [hermitianCornerEquiv_snd_fst]
    ext a
    simp [snocCol, Matrix.mul_apply, mulVec, dotProduct]
  · rw [hermitianCornerEquiv_snd_snd]
    simp [snocCol, Matrix.mul_apply, Complex.sq_norm, Complex.normSq_apply]

/-- Lebesgue integrals over `M_{k+1}(ℂ)`, with the last column integrated last. -/
private theorem lintegral_hermitianGram_eq_lintegral_snocCol
    {G : selfAdjoint.submodule ℝ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ Z : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, G (hermitianGram Z) =
      ∫⁻ v : Fin (k + 1) → ℂ, ∫⁻ Y : Matrix (Fin (k + 1)) (Fin k) ℂ,
        G (hermitianGram (snocCol Y v)) := by
  rw [← measurePreserving_snocCol.lintegral_comp
    (show Measurable fun Z ↦ G (hermitianGram Z) from hG.comp measurable_hermitianGram),
    Measure.volume_eq_prod, lintegral_prod_symm' _ (show Measurable fun p : _ × _ ↦
      G (hermitianGram (snocCol p.1 p.2)) from
        hG.comp (measurable_hermitianGram.comp measurePreserving_snocCol.measurable))]

/-- Integrals for `hermitianLebesgue (k + 1)`, with the corner integrated last. -/
private theorem lintegral_hermitianLebesgue_succ
    {G : selfAdjoint.submodule ℝ (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ T, G T ∂hermitianLebesgue (k + 1) =
      ∫⁻ r : ℝ, ∫⁻ p, G ((hermitianCornerEquiv k).symm (p.1, p.2, r))
        ∂(hermitianLebesgue k).prod (volume : Measure (Fin k → ℂ)) := by
  set e := hermitianCornerEquiv k
  rw [← ((measurePreserving_hermitianCornerEquiv k).symm e).lintegral_comp hG,
    Measure.volume_eq_prod, ← (measurePreserving_prodAssoc (hermitianLebesgue k)
      (volume : Measure (Fin k → ℂ)) (volume : Measure ℝ)).lintegral_comp
      (show Measurable fun q ↦ G (e.symm q) from hG.comp e.symm.measurable),
    lintegral_prod_symm' _ (show Measurable fun q ↦ G (e.symm (MeasurableEquiv.prodAssoc q))
      from hG.comp (e.symm.measurable.comp MeasurableEquiv.prodAssoc.measurable))]
  rfl

/-- The step from size `k` to size `k + 1`. If the Gram map in size `k` has density `c` on `W`,
then in size `k + 1` it has density `π ^ (k + 1) / k! * c` on the set of `T` whose corner
`r = T_{k k}` is positive and whose upper left block minus `r⁻¹ w wᴴ` lies in `W`, `w` the last
column of `T`. One column `v` ranges over the sphere `∑ ‖v i‖² = r`, of mass
`π ^ (k + 1) r ^ k / k!`, which cancels the power of `r` from the other `k` columns. -/
private theorem HasGramDensity.succ
    {W : Set (selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ))} {c : ℝ≥0∞}
    (hW : HasGramDensity k W c) :
    HasGramDensity (k + 1) (hermitianCornerEquiv k ⁻¹'
        {p | 0 < p.2.2 ∧ p.1 - p.2.2⁻¹ • outer p.2.1 ∈ W})
      (ENNReal.ofReal (π ^ (k + 1) / k !) * c) := by
  intro G hG h_supp
  set e := hermitianCornerEquiv k
  set μ := (hermitianLebesgue k).prod (volume : Measure (Fin k → ℂ))
  let F (r : ℝ) (p : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ) × (Fin k → ℂ)) :
      ℝ≥0∞ := G (e.symm (p.1, p.2, r))
  have hF : Measurable (Function.uncurry F) :=
    hG.comp (e.symm.measurable.comp (by fun_prop))
  have hF_supp (r : ℝ) (p) (hp : F r p ≠ 0) : 0 < r ∧ p.1 - r⁻¹ • outer p.2 ∈ W := by
    simpa [e] using h_supp hp
  let H (r : ℝ) : ℝ≥0∞ := ENNReal.ofReal (r ^ k)⁻¹ * (c * ∫⁻ p, F r p ∂μ)
  have h_column (v : Fin (k + 1) → ℂ) (hv : v ≠ 0) :
      ∫⁻ Y : Matrix (Fin (k + 1)) (Fin k) ℂ, G (hermitianGram (snocCol Y v)) =
        H (∑ i, ‖v i‖ ^ 2) := by
    set r := ∑ i, ‖v i‖ ^ 2
    have hr : 0 < r := by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
      exact Finset.sum_pos' (fun _ _ ↦ by positivity)
        ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
    have hFr : Measurable (F r) := hF.comp measurable_prodMk_left
    have h := hW.lintegral_conjTranspose_mulVec hr hFr fun p hp ↦ (hF_supp _ p hp).2
    have h_eq (Y : Matrix (Fin (k + 1)) (Fin k) ℂ) :
        G (hermitianGram (snocCol Y v)) = F r (hermitianGram Y, Yᴴ *ᵥ v) := by
      simp only [F, ← hermitianCornerEquiv_hermitianGram_snocCol, e,
        MeasurableEquiv.symm_apply_apply, r]
    simp only [h_eq, H]
    rw [← h, ← mul_assoc, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.inv_mul_cancel (by simp [hr]) ENNReal.ofReal_ne_top, one_mul]
  have h_mass (r : ℝ) (hr : 0 < r) :
      π ^ (k + 1) * r ^ k / k ! * (r ^ k)⁻¹ = π ^ (k + 1) / k ! := by
    field_simp
  have hF_subset : (fun r : ℝ ↦ ∫⁻ p, F r p ∂μ).support ⊆ Ioi 0 := fun r hr ↦ by
    obtain ⟨p, hp⟩ : ∃ p, F r p ≠ 0 := by
      by_contra! h
      exact hr (by simp [h])
    exact (hF_supp r p hp).1
  have hF_int : Measurable fun r ↦ ∫⁻ p, F r p ∂μ := hF.lintegral_prod_right'
  have hH : Measurable H := (by fun_prop : Measurable fun r : ℝ ↦ ENNReal.ofReal (r ^ k)⁻¹).mul
    (measurable_const.mul hF_int)
  calc ∫⁻ Z, G (hermitianGram Z) = ∫⁻ v : Fin (k + 1) → ℂ, H (∑ i, ‖v i‖ ^ 2) := by
        rw [lintegral_hermitianGram_eq_lintegral_snocCol hG]
        have h_ne : ∀ᵐ v : Fin (k + 1) → ℂ, v ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
        exact lintegral_congr_ae (h_ne.mono h_column)
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (π ^ (k + 1) * r ^ k / k !) * H r := by
        have h := (measurePreserving_sum_norm_sq (ι := Fin (k + 1))).lintegral_comp hH
        simp only [Fintype.card_fin, Nat.add_sub_cancel] at h
        rw [h, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hH]
        rfl
    _ = ∫⁻ r in Ioi 0, ENNReal.ofReal (π ^ (k + 1) / k !) * c * ∫⁻ p, F r p ∂μ := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
        rw [← h_mass r hr, ENNReal.ofReal_mul (by positivity), mul_assoc, mul_assoc]
    _ = ENNReal.ofReal (π ^ (k + 1) / k !) * c * ∫⁻ r, ∫⁻ p, F r p ∂μ := by
        rw [lintegral_const_mul _ hF_int, setLIntegral_eq_of_support_subset hF_subset]
    _ = ENNReal.ofReal (π ^ (k + 1) / k !) * c * ∫⁻ T, G T ∂hermitianLebesgue (k + 1) := by
        rw [lintegral_hermitianLebesgue_succ hG]

/-- The set of `(B, w, r)` with `r > 0` and `B - r⁻¹ w wᴴ ∈ W` is open when `W` is. -/
private theorem isOpen_cornerSet {W : Set (selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ))}
    (hW : IsOpen W) :
    IsOpen {p : selfAdjoint.submodule ℝ (Matrix (Fin k) (Fin k) ℂ) × (Fin k → ℂ) × ℝ |
      0 < p.2.2 ∧ p.1 - p.2.2⁻¹ • outer p.2.1 ∈ W} := by
  refine ContinuousOn.isOpen_inter_preimage (fun p hp ↦ ContinuousAt.continuousWithinAt ?_)
    (isOpen_Ioi.preimage continuous_snd.snd) hW
  exact continuousAt_fst.sub ((continuous_snd.snd.continuousAt.inv₀ (ne_of_gt hp)).smul
    (continuous_outer.comp continuous_snd.fst).continuousAt)

private theorem hermitianCornerEquiv_one :
    hermitianCornerEquiv k ⟨1, IsSelfAdjoint.one _⟩ = (⟨1, IsSelfAdjoint.one _⟩, 0, 1) := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
  · rw [coe_hermitianCornerEquiv_fst]
    exact submatrix_one _ (Fin.castSucc_injective k)
  · rw [hermitianCornerEquiv_snd_fst]
    ext a
    simp [Fin.castSucc_ne_last]
  · rw [hermitianCornerEquiv_snd_snd]
    simp

/-- **The density of the Gram map near the identity.** There is an open set `W` of Hermitian
`n × n` matrices containing `1` such that, for every measurable `G ≥ 0` supported in `W`,
`∫ G (Yᴴ Y) dY = (vol U(n) / 2 ^ n) ∫ G(T) dT`, where `dY` is Lebesgue measure on `M_n(ℂ)`,
`dT` is `hermitianLebesgue n` and `vol U(n) = unitaryGroupVolume n`. -/
theorem exists_lintegral_hermitianGram_eq (n : ℕ) :
    ∃ W : Set (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)),
      IsOpen W ∧ ⟨1, IsSelfAdjoint.one _⟩ ∈ W ∧
      ∀ G : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ) → ℝ≥0∞, Measurable G →
        G.support ⊆ W →
        ∫⁻ Y : Matrix (Fin n) (Fin n) ℂ, G (hermitianGram Y) =
          ENNReal.ofReal (unitaryGroupVolume n / 2 ^ n) * ∫⁻ T, G T ∂hermitianLebesgue n := by
  induction n with
  | zero =>
    refine ⟨univ, isOpen_univ, trivial, fun G _ _ ↦ ?_⟩
    have hY (Y : Matrix (Fin 0) (Fin 0) ℂ) : hermitianGram Y = 0 := Subsingleton.elim _ _
    have h_univ : volume (univ : Set (Matrix (Fin 0) (Fin 0) ℂ)) = 1 := by
      rw [← (Matrix.volume_preserving_ofMeasurableEquiv (Fin 0) (Fin 0) ℂ).measure_preimage
        MeasurableSet.univ.nullMeasurableSet, volume_pi, preimage_univ, Measure.pi_univ]
      simp
    simp [hY, hermitianLebesgue_zero, h_univ]
  | succ k ih =>
    obtain ⟨W, hW_open, hW_one, hW⟩ := ih
    have h_const : ENNReal.ofReal (unitaryGroupVolume (k + 1) / 2 ^ (k + 1)) =
        ENNReal.ofReal (π ^ (k + 1) / k !) * ENNReal.ofReal (unitaryGroupVolume k / 2 ^ k) := by
      rw [← ENNReal.ofReal_mul (by positivity), unitaryGroupVolume_succ]
      congr 1
      field_simp
      ring
    refine ⟨_, (isOpen_cornerSet hW_open).preimage (continuous_hermitianCornerEquiv k), ?_, ?_⟩
    · have h_outer : outer (0 : Fin k → ℂ) = 0 := Subtype.ext (by simp [coe_outer])
      simpa [hermitianCornerEquiv_one, h_outer] using hW_one
    · rw [h_const]
      exact HasGramDensity.succ hW

/-- **The density of the Gram map near the identity**, as an equality of measures: on an open
neighbourhood `W` of `1`, the image of Lebesgue measure on `M_n(ℂ)` under `Y ↦ Yᴴ Y` is
`vol U(n) / 2 ^ n` times `hermitianLebesgue n`. -/
theorem exists_restrict_map_hermitianGram_eq (n : ℕ) :
    ∃ W : Set (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)),
      IsOpen W ∧ ⟨1, IsSelfAdjoint.one _⟩ ∈ W ∧
      ((volume : Measure (Matrix (Fin n) (Fin n) ℂ)).map hermitianGram).restrict W =
        ENNReal.ofReal (unitaryGroupVolume n / 2 ^ n) • (hermitianLebesgue n).restrict W := by
  obtain ⟨W, hW_open, hW_one, hW⟩ := exists_lintegral_hermitianGram_eq n
  refine ⟨W, hW_open, hW_one, Measure.ext fun s hs ↦ ?_⟩
  have hsW := hs.inter hW_open.measurableSet
  have h := hW ((s ∩ W).indicator 1) (measurable_one.indicator hsW)
    (Set.support_indicator_subset.trans inter_subset_right)
  rw [lintegral_indicator_one hsW] at h
  rw [Measure.restrict_apply hs, Measure.map_apply measurable_hermitianGram hsW, FunLike.coe_smul,
    Pi.smul_apply,
    Measure.restrict_apply hs, smul_eq_mul, ← h, ← lintegral_indicator_one
      (measurable_hermitianGram (l := Fin n) (m := Fin n) hsW)]
  rfl

end TauCeti
