/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted
public import Mathlib.NumberTheory.ModularForms.QExpansion
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.Analysis.SpecialFunctions.Exp.Summable
import TauCeti.Topology.Algebra.InfiniteSum.NatInt
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Weight-two Eisenstein series weighted by a function of residues

For `k ≥ 3` the residue-weighted Eisenstein series `∑_x W(x mod N) (x₀ z + x₁)^(-k)` of
`TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted` converges absolutely. In weight two
it does not, and the residue-class series `G₂^{a}(z) = ∑_{x ≡ a mod N} (x₀ z + x₁)⁻²` are only
conditionally convergent; like Mathlib's level-one `EisensteinSeries.G2` they fail to be modular.
Their differences with `N⁻² G₂` are modular, and are values of the Weierstrass function: pairing
each `x ≡ a` with the multiple `x - ã` of `N`, formally

`N² G₂^{a}(z) - G₂(z) = ℘((a₀ z + a₁) / N; ℤ z + ℤ)`,

where the right side is an absolutely convergent lattice sum. Accordingly, for a weight
`W : (Fin 2 → ZMod N) → ℂ` we define

`G₂^W(z) = N⁻² ∑_a W(a) ℘((a₀ z + a₁) / N; ℤ z + ℤ)`

(`TauCeti.EisensteinSeries.weightedG2`), with `a₀, a₁` the least nonnegative representatives. It
is the series `∑_y ∑_a W(a) ((ã - N y)₀ z + (ã - N y)₁)⁻²` regularized by subtracting the total
mass `∑_a W(a)` times `N⁻² G₂` (`TauCeti.EisensteinSeries.hasSum_weightedG2`); when `W` has total
mass zero, as for the weights of Eisenstein series with a nontrivial character, no regularization
occurs (`TauCeti.EisensteinSeries.hasSum_weightedG2_of_sum_eq_zero`).

As in weight `k ≥ 3`, slashing by `γ ∈ SL(2, ℤ)` replaces the weight by `a ↦ W (a γ⁻¹)`
(`TauCeti.EisensteinSeries.weightedG2_slash_apply`): the lattice of `γ z` is `(c z + d)⁻¹` times
that of `z`, and `℘` is periodic, so it only sees the division point modulo the lattice. Hence
`G₂^W` is a modular form of weight two and level `Γ(N)`
(`TauCeti.EisensteinSeries.weightedG2MF`). Holomorphy follows from the absolute convergence of the
lattice sum, locally uniformly in `z`. Boundedness at `i∞` sums the lattice series along its rows,
each of which decays like `e^(-2π |Im|)`.

By dominated convergence along the same rows, `G₂^W` tends at `i∞` to
`∑_{n ∈ ℤ} W(0, n) n⁻² - N⁻² (∑_a W(a)) · 2 ζ(2)`: the sum of the row `x₀ = 0` of the formal series,
as in weight `k ≥ 3`, minus the regularization, `2 ζ(2)` being the value at `i∞` of Mathlib's
`EisensteinSeries.G2` (`TauCeti.EisensteinSeries.tendsto_weightedG2_atImInfty`). Together with the
slash action this gives the value at `i∞` of every `SL(2, ℤ)`-translate, hence the constant terms
of `G₂^W` at all cusps.

## Main definitions

* `TauCeti.EisensteinSeries.weightedG2`: the weight-two series weighted by `W`.
* `TauCeti.EisensteinSeries.weightedG2MF`: it is a modular form of weight two and level `Γ(N)`.
* `TauCeti.EisensteinSeries.weightedG2MFₗ`: the same, as a linear map in the weight.
* `TauCeti.EisensteinSeries.weightedG2ₗ`: the series as a linear map to functions on `ℍ`.

## Main results

* `TauCeti.EisensteinSeries.hasSum_weightedG2`: the series over integer pairs.
* `TauCeti.EisensteinSeries.hasSum_weightedG2_of_sum_eq_zero`: for a weight of total mass zero,
  the weighted series itself.
* `TauCeti.EisensteinSeries.weightedG2_slash_apply`: the slash action.
* `TauCeti.EisensteinSeries.weightedG2_comp_neg`: the series is unchanged when the residues are
  negated.
* `TauCeti.EisensteinSeries.weightedG2_mdifferentiable`: holomorphy on `ℍ`.
* `TauCeti.EisensteinSeries.isBoundedAtImInfty_weightedG2_slash`: every `SL(2, ℤ)`-translate is
  bounded at `i∞`.
* `TauCeti.EisensteinSeries.tendsto_weightedG2_atImInfty`,
  `TauCeti.EisensteinSeries.valueAtInfty_weightedG2`: the limit at `i∞`.
* `TauCeti.EisensteinSeries.valueAtInfty_weightedG2_slash`: the value at `i∞` of every
  `SL(2, ℤ)`-translate.
* `TauCeti.EisensteinSeries.weightedG2_eq_zero_of_forall_vecMul_eq`: an `SL(2, ℤ)`-invariant
  weight has the zero series, by Mathlib's `ModularForm.levelOne_weight_two_rank_zero`.
* `TauCeti.EisensteinSeries.weightedG2_comp_castHom`: for `M ∣ N`, the series of `W` modulo `M`
  and of `c ↦ W(c mod M)` modulo `N` agree.
* `TauCeti.EisensteinSeries.weightedG2_single_eq_of_val_eq`: if `c = g e` with `N = g M`, the
  series of the single residues `c` modulo `N` and `e` modulo `M` agree up to `g²`, both being
  values of `℘` at the same division point.
* `TauCeti.EisensteinSeries.weightedG2_eq_sum_single`: the series as a combination of
  single-residue series.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §4.6, where
  the weight-two Eisenstein series of level `N` are constructed by Hecke's trick instead.
* The locally uniform convergence follows Mathlib's
  `EisensteinSeries.eisensteinSeries_tendstoLocallyUniformly` (Chris Birkbeck and David Loeffler),
  with the summands bounded by Mathlib's `PeriodPair.weierstrassP_bound`.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Complex Filter Set PeriodPair
open EisensteinSeries
open TauCeti.UpperHalfPlane (rowSum rowSum_zero hasSum_rowSum summable_one_div_add_intCast_sq
  norm_rowSum_le_of_le_abs_im tendsto_rowSum_atImInfty)

open scoped MatrixGroups Topology Manifold Real

namespace TauCeti.EisensteinSeries

variable {N : ℕ} [NeZero N]

/-- The weight-two Eisenstein series weighted by `W : (Fin 2 → ZMod N) → ℂ`:
`N⁻² ∑_a W(a) ℘((a₀ z + a₁) / N; ℤ z + ℤ)`, with `a₀, a₁` the least nonnegative representatives
of the residues. -/
def weightedG2 (W : (Fin 2 → ZMod N) → ℂ) (z : ℍ) : ℂ :=
  ((N : ℂ) ^ 2)⁻¹ * ∑ a, W a * ℘[z.periodPair] (((a 0).val * (z : ℂ) + (a 1).val) / N)

lemma weightedG2_def (W : (Fin 2 → ZMod N) → ℂ) (z : ℍ) :
    weightedG2 W z =
      ((N : ℂ) ^ 2)⁻¹ * ∑ a, W a * ℘[z.periodPair] (((a 0).val * (z : ℂ) + (a 1).val) / N) :=
  (rfl)

/-- The series is linear in the weight: the zero weight. -/
lemma weightedG2_zero : weightedG2 (0 : (Fin 2 → ZMod N) → ℂ) = 0 := by
  ext z
  simp [weightedG2]

/-- The series is linear in the weight: sums. -/
lemma weightedG2_add (W W' : (Fin 2 → ZMod N) → ℂ) :
    weightedG2 (W + W') = weightedG2 W + weightedG2 W' := by
  ext z
  simp [weightedG2, add_mul, Finset.sum_add_distrib, mul_add]

/-- The series is linear in the weight: scalar multiples. -/
lemma weightedG2_smul (c : ℂ) (W : (Fin 2 → ZMod N) → ℂ) :
    weightedG2 (c • W) = c • weightedG2 W := by
  ext z
  simp [weightedG2, Finset.mul_sum, mul_assoc, mul_left_comm]

variable (N) in
/-- The weighted series as a linear map to functions on `ℍ`. -/
def weightedG2ₗ : ((Fin 2 → ZMod N) → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun := weightedG2
  map_add' := weightedG2_add
  map_smul' := weightedG2_smul

@[simp]
lemma weightedG2ₗ_apply (W : (Fin 2 → ZMod N) → ℂ) : weightedG2ₗ N W = weightedG2 W :=
  (rfl)

/-! ### The division values of `℘` -/

/-- The least nonnegative representatives of a residue pair. -/
private def lift (a : Fin 2 → ZMod N) : Fin 2 → ℤ := fun i ↦ ((a i).val : ℤ)

omit [NeZero N] in
private lemma lift_eq (a : Fin 2 → ZMod N) : lift a = fun i ↦ ((a i).val : ℤ) := (rfl)

private lemma intCast_comp_lift (a : Fin 2 → ZMod N) : ((↑) : ℤ → ZMod N) ∘ lift a = a := by
  ext i
  simp [lift]

/-- The division point of `ℤ z + ℤ` attached to an integer pair `b`. -/
private def divisionPoint (N : ℕ) (b : Fin 2 → ℤ) (z : ℍ) : ℂ := ((b 0 : ℂ) * z + b 1) / N

private lemma divisionPoint_lift (a : Fin 2 → ZMod N) (z : ℍ) :
    divisionPoint N (lift a) z = ((a 0).val * (z : ℂ) + (a 1).val) / N := by
  simp [divisionPoint, lift]

/-- `℘` only sees the division point modulo the lattice: the value at the division point of `b`
depends only on `b` modulo `N`. -/
private lemma weierstrassP_divisionPoint_eq (b : Fin 2 → ℤ) (z : ℍ) :
    ℘[z.periodPair] (divisionPoint N b z) =
      ℘[z.periodPair] (divisionPoint N (lift (((↑) : ℤ → ZMod N) ∘ b)) z) := by
  have hdvd (i : Fin 2) : (N : ℤ) ∣ b i - lift (((↑) : ℤ → ZMod N) ∘ b) i := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [lift]
  obtain ⟨m, hm⟩ := hdvd 0
  obtain ⟨n, hn⟩ := hdvd 1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h : divisionPoint N b z =
      divisionPoint N (lift (((↑) : ℤ → ZMod N) ∘ b)) z + ((m : ℂ) * z + n) := by
    have hm' : (b 0 : ℂ) = lift (((↑) : ℤ → ZMod N) ∘ b) 0 + N * m := by
      rw [← sub_eq_iff_eq_add']
      exact_mod_cast hm
    have hn' : (b 1 : ℂ) = lift (((↑) : ℤ → ZMod N) ∘ b) 1 + N * n := by
      rw [← sub_eq_iff_eq_add']
      exact_mod_cast hn
    simp only [divisionPoint]
    rw [hm', hn']
    field_simp
    ring
  rw [h]
  exact z.periodPair.weierstrassP_add_coe _
    ⟨_, intCast_mul_add_intCast_mem_lattice_periodPair z m n⟩

/-- The summands of the lattice series at a division point, as Eisenstein summands. -/
private lemma one_div_divisionPoint_sub_sq (b y : Fin 2 → ℤ) (z : ℍ) :
    1 / (divisionPoint N b z - (y 0 * z + y 1)) ^ 2 =
      (N : ℂ) ^ 2 * eisSummand 2 (b - N • y) z := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h : ((b - N • y) 0 : ℂ) * z + (b - N • y) 1 =
      N * (divisionPoint N b z - (y 0 * z + y 1)) := by
    simp only [divisionPoint, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    field_simp
    ring
  rw [eisSummand, h, _root_.zpow_neg, zpow_ofNat, mul_pow, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero 2 hN), one_mul, one_div]

private lemma one_div_sq_eq_eisSummand (y : Fin 2 → ℤ) (z : ℍ) :
    1 / ((y 0 : ℂ) * z + y 1) ^ 2 = eisSummand 2 y z := by
  rw [eisSummand, _root_.zpow_neg, zpow_ofNat, one_div]

/-- The lattice series at a division point, in Eisenstein summands. -/
private lemma hasSum_weierstrassP_divisionPoint (b : Fin 2 → ℤ) (z : ℍ) :
    HasSum (fun y : Fin 2 → ℤ ↦ (N : ℂ) ^ 2 * eisSummand 2 (b - N • y) z - eisSummand 2 y z)
      (℘[z.periodPair] (divisionPoint N b z)) := by
  simpa only [one_div_divisionPoint_sub_sq, one_div_sq_eq_eisSummand] using
    hasSum_weierstrassP_periodPair z (divisionPoint N b z)

/-- **The weighted weight-two series over integer pairs.** For `ã` the least nonnegative
representatives of `a`,
`G₂^W(z) = ∑_y ∑_a W(a) (((ã - N y)₀ z + (ã - N y)₁)⁻² - N⁻² (y₀ z + y₁)⁻²)`, the series over `y`
converging absolutely. -/
theorem hasSum_weightedG2 (W : (Fin 2 → ZMod N) → ℂ) (z : ℍ) :
    HasSum (fun y : Fin 2 → ℤ ↦ ∑ a, W a *
        (eisSummand 2 ((fun i ↦ ((a i).val : ℤ)) - N • y) z - ((N : ℂ) ^ 2)⁻¹ * eisSummand 2 y z))
      (weightedG2 W z) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [weightedG2, Finset.mul_sum]
  refine hasSum_sum fun a _ ↦ ?_
  have h := ((hasSum_weierstrassP_divisionPoint (N := N) (lift a) z).mul_left (W a)).mul_left
    ((N : ℂ) ^ 2)⁻¹
  rw [divisionPoint_lift] at h
  refine h.congr_fun fun y ↦ ?_
  rw [lift_eq]
  field_simp

/-- **A weight of total mass zero needs no regularization**:
`G₂^W(z) = ∑_y ∑_a W(a) ((ã - N y)₀ z + (ã - N y)₁)⁻²`. -/
theorem hasSum_weightedG2_of_sum_eq_zero {W : (Fin 2 → ZMod N) → ℂ} (hW : ∑ a, W a = 0)
    (z : ℍ) :
    HasSum (fun y : Fin 2 → ℤ ↦ ∑ a, W a * eisSummand 2 ((fun i ↦ ((a i).val : ℤ)) - N • y) z)
      (weightedG2 W z) := by
  refine (hasSum_weightedG2 W z).congr_fun fun y ↦ ?_
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hW, zero_mul, sub_zero]

/-! ### The slash action -/

omit [NeZero N] in
/-- The division point of `b` at `γ z` is that of `b γ` at `z`, divided by `c z + d`. -/
private lemma divisionPoint_smul (γ : SL(2, ℤ)) (b : Fin 2 → ℤ) (z : ℍ) :
    divisionPoint N b (γ • z) =
      divisionPoint N (b ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) z / denom γ z := by
  rw [divisionPoint, intCast_mul_smul_add_intCast, divisionPoint, div_right_comm]

/-- The slash action on one division value. -/
private lemma weierstrassP_divisionPoint_smul (γ : SL(2, ℤ)) (a : Fin 2 → ZMod N) (z : ℍ) :
    ℘[(γ • z).periodPair] (divisionPoint N (lift a) (γ • z)) = denom γ z ^ 2 *
      ℘[z.periodPair] (divisionPoint N
        (lift (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) z) := by
  rw [divisionPoint_smul, weierstrassP_periodPair_smul, weierstrassP_divisionPoint_eq,
    intCast_comp_vecMul, intCast_comp_lift]

/-- **The slash action on a weighted weight-two series.** Slashing by `γ ∈ SL(2, ℤ)` replaces the
weight `W` by `a ↦ W (a γ⁻¹)`. -/
theorem weightedG2_slash_apply (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    weightedG2 W ∣[(2 : ℤ)] γ = weightedG2 (fun a ↦
      W (a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) := by
  ext z
  have hD := denom_ne_zero γ z
  simp_rw [SL_slash_apply, weightedG2, ← divisionPoint_lift, weierstrassP_divisionPoint_smul]
  have hsum : ∑ a, W a * (denom γ z ^ 2 * ℘[z.periodPair] (divisionPoint N
        (lift (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) z)) =
      denom γ z ^ 2 * ∑ a, W (a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) :
        Matrix (Fin 2) (Fin 2) (ZMod N))) * ℘[z.periodPair] (divisionPoint N (lift a) z) := by
    rw [Finset.mul_sum]
    -- reindex the residues by `a ↦ a γ`
    have h₂ : ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
        (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    refine Eq.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
      (Matrix.SpecialLinearGroup.sum_comp_vecMul _ (γ : SL(2, ZMod N)))
    simp only [Matrix.vecMul_vecMul, h₂, Matrix.vecMul_one]
    ring
  rw [hsum, _root_.zpow_neg, zpow_ofNat]
  field_simp

/-- **Weight two is even**: negating the residues does not change the weighted series, since
slashing by `-1` in weight two is the identity. -/
theorem weightedG2_comp_neg (W : (Fin 2 → ZMod N) → ℂ) :
    weightedG2 (fun a ↦ W (-a)) = weightedG2 W := by
  have h := weightedG2_slash_apply W (-1 : SL(2, ℤ))
  have hGL : Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (-1 : SL(2, ℤ))) = -1 :=
    Matrix.SpecialLinearGroup.mapGL_neg_one
  have hres (a : Fin 2 → ZMod N) :
      a ᵥ* (((-1 : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) = -a := by
    ext i
    fin_cases i <;> simp [vecMul, dotProduct]
  rw [SL_slash, hGL, _root_.ModularForm.slash_neg_one] at h
  simp only [hres] at h
  rw [← h]
  simp

/-! ### Holomorphy -/

/-- The lattice series at a division point converges locally uniformly in `z`. -/
private lemma tendstoLocallyUniformly_weierstrassP_divisionPoint (b : Fin 2 → ℤ) :
    TendstoLocallyUniformly
      (fun (s : Finset (Fin 2 → ℤ)) (z : ℍ) ↦
        ∑ y ∈ s, ((N : ℂ) ^ 2 * eisSummand 2 (b - N • y) z - eisSummand 2 y z))
      (fun z : ℍ ↦ ℘[z.periodPair] (divisionPoint N b z)) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨A, B, hB, HABK⟩ := subset_verticalStrip_of_isCompact hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun z : ℍ ↦ (z : ℂ))
    continuous_coe.continuousOn
  set r₀ := r ⟨⟨A, B⟩, hB⟩
  have hr₀ : 0 < r₀ := r_pos _
  set R : ℝ := |(b 0 : ℝ)| * |M| + |(b 1 : ℝ)| + 1
  have hR : 0 < R := by positivity
  have hlim : (fun z : ℍ ↦ ℘[z.periodPair] (divisionPoint N b z)) =
      fun z ↦ ∑' y, ((N : ℂ) ^ 2 * eisSummand 2 (b - N • y) z - eisSummand 2 y z) :=
    funext fun z ↦ (hasSum_weierstrassP_divisionPoint b z).tsum_eq.symm
  rw [hlim]
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually
    (u := fun y ↦ 10 * R * r₀ ^ (-3 : ℝ) * ‖y‖ ^ (-3 : ℝ))
    ((summable_one_div_norm_rpow (by norm_num)).mul_left _) ?_
  have hev : ∀ᶠ y : Fin 2 → ℤ in cofinite, 2 * R / r₀ ≤ ‖y‖ := by
    rw [← cocompact_eq_cofinite]
    exact tendsto_norm_cocompact_atTop.eventually_ge_atTop _
  filter_upwards [hev] with y hy z hz
  have hy' : 2 * R ≤ r₀ * ‖y‖ := by
    rwa [div_le_iff₀' hr₀] at hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [norm_zero, mul_zero] at hy'
    linarith
  -- the summand in the coordinates of the lattice
  rw [← one_div_divisionPoint_sub_sq, ← one_div_sq_eq_eisSummand]
  have hl : r₀ * ‖y‖ ≤ ‖(y 0 : ℂ) * z + y 1‖ :=
    (mul_le_mul_of_nonneg_right (r_lower_bound_on_verticalStrip z hB (HABK hz))
      (norm_nonneg _)).trans (r_mul_max_le z hy0)
  have hx : ‖divisionPoint N b z‖ < R := by
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
    have hz' : ‖(z : ℂ)‖ ≤ |M| := (hM z hz).trans (le_abs_self M)
    rw [divisionPoint, norm_div, Complex.norm_natCast]
    refine (div_le_self (norm_nonneg _) hN).trans_lt ?_
    refine (norm_add_le _ _).trans_lt ?_
    rw [norm_mul, Complex.norm_intCast, Complex.norm_intCast]
    have := mul_le_mul_of_nonneg_left hz' (abs_nonneg (b 0 : ℝ))
    linarith
  refine (weierstrassP_bound R hR _ hx _ (hy'.trans hl)).trans ?_
  rw [mul_assoc (10 * R), ← Real.mul_rpow hr₀.le (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)) (by positivity)

/-- Each division value of `℘` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_weierstrassP_divisionPoint (b : Fin 2 → ℤ) :
    MDiff (fun z : ℍ ↦ ℘[z.periodPair] (divisionPoint N b z)) :=
  TauCeti.UpperHalfPlane.mdifferentiable_of_tendstoLocallyUniformly
    (tendstoLocallyUniformly_weierstrassP_divisionPoint b) (Eventually.of_forall fun _ ↦
      UpperHalfPlane.mdifferentiable_iff.mpr (DifferentiableOn.fun_sum fun y _ ↦
        ((eisSummand_extension_differentiableOn 2 _).const_mul _).sub
          (eisSummand_extension_differentiableOn 2 y)))

/-- **The weighted weight-two series is holomorphic on `ℍ`.** -/
theorem weightedG2_mdifferentiable (W : (Fin 2 → ZMod N) → ℂ) : MDiff (weightedG2 W) := by
  have h (a : Fin 2 → ZMod N) := mdifferentiable_weierstrassP_divisionPoint (N := N) (lift a)
  simp only [divisionPoint_lift] at h
  have hsum : MDiff fun z : ℍ ↦ ∑ a, W a *
      ℘[z.periodPair] (((a 0).val * (z : ℂ) + (a 1).val) / N) := by
    convert MDifferentiable.sum (t := Finset.univ)
      (f := fun a (z : ℍ) ↦ W a * ℘[z.periodPair] (((a 0).val * (z : ℂ) + (a 1).val) / N))
      fun a _ ↦ mdifferentiable_const.mul (h a) using 1
    ext z
    simp [Finset.sum_apply]
  rw [show weightedG2 W = _ from funext (weightedG2_def W)]
  exact mdifferentiable_const.mul hsum

/-! ### Boundedness at infinity -/

/-- The decay constant of the rows with `|Im w| ≥ 1 / N`. -/
private def rowConst (N : ℕ) : ℝ := 4 * π ^ 2 / (1 - Real.exp (-2 * π * (1 / N))) ^ 2

private lemma rowConst_nonneg (N : ℕ) : 0 ≤ rowConst N := by
  unfold rowConst
  positivity

/-- The row bound in the form used along the lattice: `e^(-2π |Im w|) ≤ e^(-2π (|m| - 1))`. -/
private lemma norm_rowSum_le_of_le (w : ℂ) {m : ℤ} (hw : 1 / (N : ℝ) ≤ |w.im|)
    (hm : |(m : ℝ)| - 1 ≤ |w.im|) :
    ‖rowSum w‖ ≤ rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) := by
  have hN : (0 : ℝ) < 1 / N := one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N))
  have hK := rowConst_nonneg N
  rw [rowConst] at hK ⊢
  exact (norm_rowSum_le_of_le_abs_im hN hw).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) hK)

omit [NeZero N] in
/-- The imaginary part of `m z` is `|m| Im z` in absolute value. -/
private lemma abs_im_intCast_mul (m : ℤ) (z : ℍ) : |((m : ℂ) * z).im| = |(m : ℝ)| * z.im := by
  simp [abs_mul, abs_of_pos z.im_pos]

/-- The rows `P(m z)`, `m ≠ 0`, of the lattice series, on `1 ≤ Im z`. -/
private lemma norm_rowSum_intCast_mul_le {m : ℤ} (hm : m ≠ 0) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖rowSum (m * z)‖ ≤ rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) := by
  have hN1 : (1 : ℝ) / N ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast NeZero.one_le) (Nat.cast_nonneg N)
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
  have ht : |(m : ℝ)| ≤ |((m : ℂ) * z).im| := by
    rw [abs_im_intCast_mul]
    exact le_mul_of_one_le_right (abs_nonneg _) hz
  exact norm_rowSum_le_of_le _ (by linarith) (by linarith)

omit [NeZero N] in
/-- The imaginary part of `x - m z` at a division point `x = (a₀ z + a₁) / N` is
`(a₀ / N - m) Im z`. -/
private lemma im_divisionPoint_sub (a : Fin 2 → ZMod N) (m : ℤ) (z : ℍ) :
    (divisionPoint N (lift a) z - m * z).im = (((a 0).val : ℝ) / N - m) * z.im := by
  simp only [divisionPoint, lift, Complex.sub_im, Complex.div_natCast_im, Complex.add_im,
    Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Int.cast_natCast,
    Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im]
  ring

/-- For `(m, a₀) ≠ (0, 0)`, the coefficient `a₀ / N - m` of `Im z` in the imaginary part of
`x - m z` is at least `1 / N` in absolute value, as `a₀ - N m` is a nonzero integer. -/
private lemma one_div_le_abs_val_div_sub (a : Fin 2 → ZMod N) {m : ℤ}
    (h0 : ¬(m = 0 ∧ (a 0).val = 0)) : 1 / (N : ℝ) ≤ |((a 0).val : ℝ) / N - m| := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hk : (1 : ℝ) ≤ |((a 0).val : ℝ) - N * m| := by
    have hk' : ((a 0).val : ℤ) - N * m ≠ 0 := by
      intro h
      have hlt : ((a 0).val : ℤ) < N := by exact_mod_cast ZMod.val_lt (a 0)
      rcases lt_trichotomy m 0 with hm | hm | hm
      · nlinarith
      · exact h0 ⟨hm, by subst hm; omega⟩
      · nlinarith
    exact_mod_cast Int.one_le_abs hk'
  have hc : |((a 0).val : ℝ) / N - m| = |((a 0).val : ℝ) - N * m| / N := by
    have : ((a 0).val : ℝ) / N - m = (((a 0).val : ℝ) - N * m) / N := by
      field_simp
    rw [this, abs_div, abs_of_pos hN]
  rw [hc]
  gcongr

/-- The rows `P(x - m z)` at a division point `x = (a₀ z + a₁) / N`, for `(m, a₀) ≠ (0, 0)`, on
`1 ≤ Im z`: the imaginary part of `x - m z` is `(a₀ / N - m) Im z` with `a₀ - N m` a nonzero
integer. -/
private lemma norm_rowSum_divisionPoint_sub_le (a : Fin 2 → ZMod N) {m : ℤ}
    (h0 : ¬(m = 0 ∧ (a 0).val = 0)) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖rowSum (divisionPoint N (lift a) z - m * z)‖ ≤
      rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set c : ℝ := ((a 0).val : ℝ) / N
  have him : (divisionPoint N (lift a) z - m * z).im = (c - m) * z.im :=
    im_divisionPoint_sub a m z
  have hc1 : 1 / (N : ℝ) ≤ |c - m| := one_div_le_abs_val_div_sub a h0
  have hc2 : |(m : ℝ)| - 1 ≤ |c - m| := by
    have h0' : c < 1 := by
      rw [div_lt_one hN]
      exact_mod_cast ZMod.val_lt (a 0)
    have h0'' : 0 ≤ c := by positivity
    have := abs_sub_abs_le_abs_sub (m : ℝ) c
    rw [abs_of_nonneg h0'', abs_sub_comm] at this
    linarith
  have ht : |c - m| ≤ |(divisionPoint N (lift a) z - m * z).im| := by
    rw [him, abs_mul, abs_of_pos z.im_pos]
    exact le_mul_of_one_le_right (abs_nonneg _) hz
  exact norm_rowSum_le_of_le _ (hc1.trans ht) (hc2.trans ht)

/-- The bounds for the rows: a summable majorant independent of `z` on `1 ≤ Im z`. -/
private def rowBound (N : ℕ) (a : Fin 2 → ZMod N) (m : ℤ) : ℝ :=
  2 * rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) +
    if m = 0 then ‖rowSum ((a 1).val / N)‖ + ‖rowSum 0‖ else 0

omit [NeZero N] in
private lemma summable_rowBound (a : Fin 2 → ZMod N) : Summable (rowBound N a) := by
  refine Summable.add (Summable.mul_left _ summable_exp_neg_two_pi_mul_abs_sub_one)
    (summable_of_hasFiniteSupport ?_)
  refine (Set.finite_singleton 0).subset fun m hm ↦ ?_
  rw [Set.mem_singleton_iff]
  by_contra h
  exact hm (by simp [h])

/-- Each row of the lattice series at a division point is bounded by `rowBound` on
`1 ≤ Im z`. -/
private lemma norm_rowSum_sub_rowSum_le (a : Fin 2 → ZMod N) (m : ℤ) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖rowSum (divisionPoint N (lift a) z - m * z) - rowSum (m * z)‖ ≤ rowBound N a m := by
  refine (norm_sub_le _ _).trans ?_
  have hK := rowConst_nonneg N
  have h₂ : ‖rowSum (m * z)‖ ≤ rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) +
      if m = 0 then ‖rowSum 0‖ else 0 := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp only [↓reduceIte, Int.cast_zero, zero_mul]
      exact le_add_of_nonneg_left (by positivity)
    simpa only [hm, ↓reduceIte, add_zero] using norm_rowSum_intCast_mul_le hm hz
  have h₁ : ‖rowSum (divisionPoint N (lift a) z - m * z)‖ ≤
      rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) +
        if m = 0 then ‖rowSum ((a 1).val / N)‖ else 0 := by
    by_cases h0 : m = 0 ∧ (a 0).val = 0
    · obtain ⟨rfl, ha⟩ := h0
      have : divisionPoint N (lift a) z - ((0 : ℤ) : ℂ) * z = (a 1).val / N := by
        simp [divisionPoint, lift, ha]
      simp only [this, ↓reduceIte]
      exact le_add_of_nonneg_left (by positivity)
    refine le_add_of_le_of_nonneg (norm_rowSum_divisionPoint_sub_le a h0 hz) ?_
    split_ifs <;> positivity
  calc _ ≤ _ := add_le_add h₁ h₂
    _ = rowBound N a m := by
      simp only [rowBound]
      split_ifs <;> ring

/-- Each division value of `℘` is bounded on `1 ≤ Im z`, by summing the lattice series along its
rows. -/
private lemma norm_weierstrassP_divisionPoint_le (a : Fin 2 → ZMod N) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖℘[z.periodPair] (divisionPoint N (lift a) z)‖ ≤ ∑' m, rowBound N a m :=
  (hasSum_weierstrassP_periodPair_rows z _).norm_le_of_bounded (summable_rowBound a).hasSum
    fun m ↦ norm_rowSum_sub_rowSum_le a m hz

/-- **The weighted weight-two series is bounded at `i∞`.** -/
theorem isBoundedAtImInfty_weightedG2 (W : (Fin 2 → ZMod N) → ℂ) :
    IsBoundedAtImInfty (weightedG2 W) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨‖((N : ℂ) ^ 2)⁻¹‖ * ∑ a, ‖W a‖ * ∑' m, rowBound N a m, 1, fun z hz ↦ ?_⟩
  rw [weightedG2, norm_mul]
  gcongr
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  rw [norm_mul, ← divisionPoint_lift]
  gcongr
  exact norm_weierstrassP_divisionPoint_le a hz

/-- Every `SL(2, ℤ)`-translate of the weighted weight-two series is bounded at `i∞`. -/
theorem isBoundedAtImInfty_weightedG2_slash (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (weightedG2 W ∣[(2 : ℤ)] γ) := by
  rw [weightedG2_slash_apply]
  exact isBoundedAtImInfty_weightedG2 _

/-! ### The value at infinity -/

/-- The rows `P(x - m z)` at a division point `x = (a₀ z + a₁) / N`, for `(m, a₀) ≠ (0, 0)`, tend
to `0` at `i∞`. -/
private lemma tendsto_rowSum_divisionPoint_sub_atImInfty (a : Fin 2 → ZMod N) {m : ℤ}
    (h0 : ¬(m = 0 ∧ (a 0).val = 0)) :
    Tendsto (fun z : ℍ ↦ rowSum (divisionPoint N (lift a) z - m * z)) atImInfty (𝓝 0) := by
  refine tendsto_rowSum_atImInfty (c := 1 / N) (one_div_pos.mpr (Nat.cast_pos.mpr (NeZero.pos N)))
    fun z ↦ ?_
  rw [im_divisionPoint_sub, abs_mul, abs_of_pos z.im_pos]
  exact mul_le_mul_of_nonneg_right (one_div_le_abs_val_div_sub a h0) z.im_pos.le

/-- The limit at `i∞` of the row `m` of the lattice series at a division point
`x = (a₀ z + a₁) / N`: only the row `m = 0` survives, contributing `P(a₁ / N) - P(0)` if `a₀ = 0`
and `-P(0)` otherwise. -/
private lemma tendsto_rowSum_divisionPoint_sub_sub_atImInfty (a : Fin 2 → ZMod N) (m : ℤ) :
    Tendsto (fun z : ℍ ↦ rowSum (divisionPoint N (lift a) z - m * z) - rowSum (m * z))
      atImInfty (𝓝 (if m = 0 then
        (if (a 0).val = 0 then rowSum ((a 1).val / N) else 0) - rowSum 0 else 0)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [↓reduceIte, Int.cast_zero, zero_mul, sub_zero]
    refine Tendsto.sub_const ?_ _
    split_ifs with ha
    · refine tendsto_const_nhds.congr fun z ↦ ?_
      simp [divisionPoint, lift, ha]
    · simpa using tendsto_rowSum_divisionPoint_sub_atImInfty a (m := 0) (by simp [ha])
  · simp only [hm, ↓reduceIte]
    have h₂ : Tendsto (fun z : ℍ ↦ rowSum (m * z)) atImInfty (𝓝 0) := by
      refine tendsto_rowSum_atImInfty one_pos fun z ↦ ?_
      have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
      rw [abs_im_intCast_mul, one_mul]
      exact le_mul_of_one_le_left z.im_pos.le hm1
    simpa using (tendsto_rowSum_divisionPoint_sub_atImInfty a (by simp [hm])).sub h₂

/-- The limit at `i∞` of a division value of `℘`, by dominated convergence along the rows. -/
private lemma tendsto_weierstrassP_divisionPoint_atImInfty (a : Fin 2 → ZMod N) :
    Tendsto (fun z : ℍ ↦ ℘[z.periodPair] (divisionPoint N (lift a) z)) atImInfty
      (𝓝 ((if (a 0).val = 0 then rowSum ((a 1).val / N) else 0) - rowSum 0)) := by
  have hfun : (fun z : ℍ ↦ ℘[z.periodPair] (divisionPoint N (lift a) z)) = fun z ↦
      ∑' m : ℤ, (rowSum (divisionPoint N (lift a) z - m * z) - rowSum (m * z)) :=
    funext fun z ↦ (hasSum_weierstrassP_periodPair_rows z _).tsum_eq.symm
  rw [hfun]
  convert tendsto_tsum_of_dominated_convergence (summable_rowBound a)
    (tendsto_rowSum_divisionPoint_sub_sub_atImInfty a) ?_ using 2
  · rw [tsum_ite_eq]
  filter_upwards [(tendsto_comap : Tendsto (fun z : ℍ ↦ z.im) atImInfty atTop).eventually_ge_atTop
    1] with z hz m
  exact norm_rowSum_sub_rowSum_le a m hz

/-- The residue class of `r` modulo `N` contributes `N⁻² P(r / N)` to the series
`∑_{n ∈ ℤ} n⁻²`. -/
private lemma hasSum_zpow_val_sub (r : ZMod N) :
    HasSum (fun y : ℤ ↦ ((((r.val : ℤ) - N * y : ℤ) : ℂ)) ^ (-2 : ℤ))
      (((N : ℂ) ^ 2)⁻¹ * rowSum (r.val / N)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h := ((Equiv.neg ℤ).hasSum_iff.mpr (hasSum_rowSum ((r.val : ℂ) / N))).mul_left
    ((N : ℂ) ^ 2)⁻¹
  refine h.congr_fun fun y ↦ ?_
  simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast]
  rw [_root_.zpow_neg, zpow_ofNat]
  field_simp
  ring

/-- The sum of a weight along the row `x₀ = 0`, grouped by residue classes modulo `N`:
`∑_{n ∈ ℤ} W(0, n) n⁻² = N⁻² ∑_{r mod N} W(0, r) P(r / N)`. -/
private lemma tsum_row_zero_eq (W : (Fin 2 → ZMod N) → ℂ) :
    ∑' n : ℤ, W ((↑) ∘ ![0, n]) * (n : ℂ) ^ (-2 : ℤ) =
      ((N : ℂ) ^ 2)⁻¹ * ∑ r : ZMod N, W ![0, r] * rowSum (r.val / N) := by
  have hS : Summable fun n : ℤ ↦ W ((↑) ∘ ![0, n]) * (n : ℂ) ^ (-2 : ℤ) := by
    refine ((summable_one_div_add_intCast_sq 0).norm.mul_left (∑ b, ‖W b‖)).of_norm_bounded
      fun n ↦ ?_
    rw [norm_mul, zero_add, one_div, ← zpow_ofNat, ← _root_.zpow_neg]
    gcongr
    exact Finset.single_le_sum (f := fun b ↦ ‖W b‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ _)
  have hres (r : ZMod N) (y : ℤ) :
      (((↑) : ℤ → ZMod N) ∘ ![0, (r.val : ℤ) - N * y]) = ![0, r] := by
    ext i
    fin_cases i <;> simp
  refine (hS.hasSum.sum_zmod_val_sub N).unique ?_
  rw [Finset.mul_sum]
  refine hasSum_sum fun r _ ↦ ?_
  simpa only [hres, mul_left_comm (W _)] using (hasSum_zpow_val_sub r).mul_left (W ![0, r])

/-- **The limit at `i∞` of the weighted weight-two series**: `G₂^W` tends to
`∑_{n ∈ ℤ} W(0, n) n⁻² - N⁻² (∑_a W(a)) · 2 ζ(2)`, the sum of the row `x₀ = 0` of the formal
series minus the regularization by `N⁻² G₂`, whose value at `i∞` is `N⁻² · 2 ζ(2)`. -/
theorem tendsto_weightedG2_atImInfty (W : (Fin 2 → ZMod N) → ℂ) :
    Tendsto (weightedG2 W) atImInfty
      (𝓝 (∑' n : ℤ, W ((↑) ∘ ![0, n]) * (n : ℂ) ^ (-2 : ℤ) -
        ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * (2 * riemannZeta 2))) := by
  have h := (tendsto_finsetSum Finset.univ fun a _ ↦
    (tendsto_weierstrassP_divisionPoint_atImInfty (N := N) a).const_mul (W a)).const_mul
      ((N : ℂ) ^ 2)⁻¹
  simp only [divisionPoint_lift] at h
  convert h using 2 with z
  · exact weightedG2_def W z
  -- only the residues with `a₀ = 0` see the row `P(a₁ / N)`
  have hrow : ∑ a : Fin 2 → ZMod N, W a * (if (a 0).val = 0 then rowSum ((a 1).val / N) else 0) =
      ∑ r : ZMod N, W ![0, r] * rowSum (r.val / N) := by
    have he (r : ZMod N) : (piFinTwoEquiv fun _ ↦ ZMod N).symm (0, r) = ![0, r] := by
      ext i
      fin_cases i <;> simp
    rw [← (piFinTwoEquiv fun _ ↦ ZMod N).symm.sum_comp, Fintype.sum_prod_type,
      Fintype.sum_eq_single 0 fun x hx ↦ by simp [ZMod.val_eq_zero, hx]]
    simp only [he, Matrix.cons_val_zero, Matrix.cons_val_one, ZMod.val_zero, ↓reduceIte]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, rowSum_zero,
    tsum_row_zero_eq]
  ring

/-- The value at `i∞` of the weighted weight-two series:
`∑_{n ∈ ℤ} W(0, n) n⁻² - N⁻² (∑_a W(a)) · 2 ζ(2)`. -/
theorem valueAtInfty_weightedG2 (W : (Fin 2 → ZMod N) → ℂ) :
    valueAtInfty (weightedG2 W) = ∑' n : ℤ, W ((↑) ∘ ![0, n]) * (n : ℂ) ^ (-2 : ℤ) -
      ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * (2 * riemannZeta 2) :=
  (tendsto_weightedG2_atImInfty W).limUnder_eq

/-- **The value at `i∞` of a translated weighted weight-two series.** For
`γ = !![a, b; c, d] ∈ SL₂(ℤ)`, the value at `i∞` of `G₂^W ∣[2] γ` is
`∑_{n ∈ ℤ} W(-n c, n a) n⁻² - N⁻² (∑_a W(a)) · 2 ζ(2)`: the multiples of the row `(-c, a)` of
`γ⁻¹` contribute as in weight `k ≥ 3`, and the regularization does not depend on the cusp. -/
theorem valueAtInfty_weightedG2_slash (W : (Fin 2 → ZMod N) → ℂ) (γ : SL(2, ℤ)) :
    valueAtInfty (weightedG2 W ∣[(2 : ℤ)] γ) =
      ∑' n : ℤ, W ((↑) ∘ ![-(n * γ 1 0), n * γ 0 0]) * (n : ℂ) ^ (-2 : ℤ) -
        ((N : ℂ) ^ 2)⁻¹ * (∑ a, W a) * (2 * riemannZeta 2) := by
  rw [weightedG2_slash_apply, valueAtInfty_weightedG2, Matrix.SpecialLinearGroup.sum_comp_vecMul]
  congr 1
  refine tsum_congr fun n ↦ ?_
  congr 2
  ext i
  fin_cases i <;> simp [vecMul, dotProduct, Matrix.adjugate_fin_two]

/-! ### The modular form -/

/-- The weighted weight-two series as a slash invariant form of level `Γ(N)`: an element of
`Γ(N)` reduces to the identity modulo `N`, so it does not change the weight. -/
def weightedG2SIF (W : (Fin 2 → ZMod N) → ℂ) : SlashInvariantForm Γ(N) 2 where
  toFun := weightedG2 W
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, weightedG2_slash_apply,
      Gamma_mem'.mp (inv_mem hA)]

@[simp]
lemma coe_weightedG2SIF (W : (Fin 2 → ZMod N) → ℂ) : ⇑(weightedG2SIF W) = weightedG2 W := (rfl)

/-- **The weighted weight-two series is a modular form** of weight two and level `Γ(N)`. -/
def weightedG2MF (W : (Fin 2 → ZMod N) → ℂ) : ModularForm Γ(N) 2 where
  toSlashInvariantForm := weightedG2SIF W
  holo' := weightedG2_mdifferentiable W
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ ↦ isBoundedAtImInfty_weightedG2_slash W γ

@[simp]
lemma coe_weightedG2MF (W : (Fin 2 → ZMod N) → ℂ) : ⇑(weightedG2MF W) = weightedG2 W := (rfl)

@[simp]
lemma weightedG2MF_zero : weightedG2MF (0 : (Fin 2 → ZMod N) → ℂ) = 0 := by
  ext z
  exact congrFun weightedG2_zero z

@[simp]
lemma weightedG2MF_add (W W' : (Fin 2 → ZMod N) → ℂ) :
    weightedG2MF (W + W') = weightedG2MF W + weightedG2MF W' := by
  ext z
  exact congrFun (weightedG2_add W W') z

@[simp]
lemma weightedG2MF_smul (c : ℂ) (W : (Fin 2 → ZMod N) → ℂ) :
    weightedG2MF (c • W) = c • weightedG2MF W := by
  ext z
  exact congrFun (weightedG2_smul c W) z

/-- The weighted weight-two series as a linear map from weights to `M₂(Γ(N))`. -/
def weightedG2MFₗ : ((Fin 2 → ZMod N) → ℂ) →ₗ[ℂ] ModularForm Γ(N) 2 where
  toFun := weightedG2MF
  map_add' := weightedG2MF_add
  map_smul' := weightedG2MF_smul

@[simp]
lemma weightedG2MFₗ_apply (W : (Fin 2 → ZMod N) → ℂ) : weightedG2MFₗ W = weightedG2MF W := (rfl)

/-! ### Weights invariant under `SL(2, ℤ)` -/

/-- A weight invariant under right multiplication by `SL(2, ℤ)` has the zero series. -/
theorem weightedG2_eq_zero_of_forall_vecMul_eq {W : (Fin 2 → ZMod N) → ℂ}
    (hW : ∀ (γ : SL(2, ℤ)) (a : Fin 2 → ZMod N),
      W (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) = W a) :
    weightedG2 W = 0 := by
  have hslash (γ : SL(2, ℤ)) : weightedG2 W ∣[(2 : ℤ)] γ = weightedG2 W := by
    rw [weightedG2_slash_apply]
    simp only [hW]
  let f : ModularForm 𝒮ℒ 2 :=
    ModularForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp (weightedG2MF W) <| by
      rintro _ ⟨γ, rfl⟩
      rw [coe_weightedG2MF]
      exact hslash γ
  have hf := congrArg DFunLike.coe
    ((rank_zero_iff_forall_zero.mp _root_.ModularForm.levelOne_weight_two_rank_zero) f)
  rwa [ModularForm.coe_ofSlashInvariant, coe_weightedG2MF] at hf

/-! ### Changing the level -/

variable {M : ℕ} [NeZero M]

/-- The change of level for a weight of total mass zero: both series are
`∑_x W(x mod M) (x₀ z + x₁)⁻²`, summed over blocks of residues modulo `M` and modulo `N`. -/
private lemma weightedG2_comp_castHom_of_sum_eq_zero (h : M ∣ N) {W : (Fin 2 → ZMod M) → ℂ}
    (hW : ∑ a, W a = 0) :
    weightedG2 (fun c : Fin 2 → ZMod N ↦ W (ZMod.castHom h (ZMod M) ∘ c)) = weightedG2 W := by
  ext z
  -- a residue modulo `N` is its residue modulo `M` and the quotient of its representative by `M`
  let D : ZMod N → ZMod M × Fin (N / M) := fun c ↦
    (ZMod.castHom h (ZMod M) c, ⟨c.val / M, Nat.div_lt_div_of_lt_of_dvd h c.val_lt⟩)
  have hval (c : ZMod N) : c.val = (D c).1.val + M * ((D c).2 : ℕ) := by
    simp only [D, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    exact (Nat.mod_add_div _ _).symm
  have hD : Function.Bijective D := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun c c' hcc' ↦ ZMod.val_injective N (by rw [hval c, hval c', hcc']), by
      simp [ZMod.card, Nat.mul_div_cancel' h]⟩
  let E₂ : (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod M) × (Fin 2 → Fin (N / M)) :=
    (Equiv.piCongrRight fun _ ↦ Equiv.ofBijective D hD).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  have hn : NeZero (N / M) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) h) (NeZero.pos M)).ne'⟩
  have hNM : ((N : ℕ) : ℤ) = M * (N / M : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' h).symm
  -- the series of level `M`, over the blocks `e + M y` with `e` lifted to `ℤ`
  let F : (Fin 2 → ℤ) → ℂ := fun y ↦
    ∑ e, W e * eisSummand 2 ((fun i ↦ ((e i).val : ℤ)) + M • y) z
  have hF : HasSum F (weightedG2 W z) := by
    refine ((Equiv.neg (Fin 2 → ℤ)).hasSum_iff.mpr
      (hasSum_weightedG2_of_sum_eq_zero hW z)).congr_fun fun y ↦ ?_
    simp [F, sub_eq_add_neg]
  -- regroup the blocks along `y = (N / M) q + r`
  let E : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) × (Fin 2 → Fin (N / M)) :=
    (Equiv.piCongrRight fun _ ↦ Int.divModEquiv (N / M)).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)
  have hG : HasSum (fun q : Fin 2 → ℤ ↦ ∑ r : Fin 2 → Fin (N / M),
      F (fun i ↦ q i * (N / M : ℕ) + r i)) (weightedG2 W z) :=
    (E.symm.hasSum_iff.mpr hF).prod_fiberwise fun q ↦ hasSum_fintype _
  have hmass : ∑ c : Fin 2 → ZMod N, W (ZMod.castHom h (ZMod M) ∘ c) = 0 := by
    rw [Fintype.sum_equiv E₂ (fun c ↦ W (ZMod.castHom h (ZMod M) ∘ c))
      (fun p ↦ W p.1) fun _ ↦ rfl,
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, ← Finset.smul_sum, hW, smul_zero]
  have hN := (Equiv.neg (Fin 2 → ℤ)).hasSum_iff.mpr (hasSum_weightedG2_of_sum_eq_zero hmass z)
  refine hN.unique (hG.congr_fun fun q ↦ ?_)
  simp only [Function.comp_apply, Equiv.neg_apply, F]
  rw [Fintype.sum_equiv E₂ (fun c ↦ W (ZMod.castHom h (ZMod M) ∘ c) *
      eisSummand 2 ((fun i ↦ ((c i).val : ℤ)) - N • -q) z) (fun p ↦ W p.1 * eisSummand 2
      ((fun i ↦ ((p.1 i).val : ℤ)) + M • (fun i ↦ ((p.2 i : ℕ) : ℤ)) + N • q) z) fun c ↦ ?_,
    Fintype.sum_prod_type, Finset.sum_comm]
  · refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
    congr 2
    ext i
    simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, hNM]
    ring
  · congr 2
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, nsmul_eq_mul, smul_neg, sub_neg_eq_add]
    rw [hval (c i)]
    simp [E₂]

/-- **Changing the level of a weight-two series.** For `M ∣ N`, the series of a weight `W` modulo
`M` and of the weight `c ↦ W(c mod M)` modulo `N` agree. -/
theorem weightedG2_comp_castHom (h : M ∣ N) (W : (Fin 2 → ZMod M) → ℂ) :
    weightedG2 (fun c : Fin 2 → ZMod N ↦ W (ZMod.castHom h (ZMod M) ∘ c)) = weightedG2 W := by
  -- split off a constant weight, whose series vanishes at every level
  set m : ℂ := (∑ a, W a) / (M : ℂ) ^ 2
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hmass : ∑ a, (W a - m) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [show (M : ℂ) ^ 2 * m = ∑ a, W a from mul_div_cancel₀ _ (pow_ne_zero 2 hM), sub_self]
  have hconst {L : ℕ} [NeZero L] : weightedG2 (fun _ : Fin 2 → ZMod L ↦ m) = 0 :=
    weightedG2_eq_zero_of_forall_vecMul_eq fun _ _ ↦ rfl
  have hsplit {L : ℕ} [NeZero L] (V : (Fin 2 → ZMod L) → ℂ) :
      weightedG2 V = weightedG2 fun a ↦ V a - m := by
    conv_lhs => rw [show V = (fun a ↦ V a - m) + fun _ ↦ m by ext; simp]
    rw [weightedG2_add, hconst, add_zero]
  rw [hsplit, hsplit W]
  exact weightedG2_comp_castHom_of_sum_eq_zero h (W := fun a ↦ W a - m) hmass

/-! ### Common division points -/

/-- The single-residue series of level `N` at the residue `g e` agrees with `g⁻²` times that of
level `M` at `e`, when `N = g M`: both are values of `℘` at the same division point. -/
theorem weightedG2_single_eq_of_val_eq {g : ℕ} (hg : N = g * M) {c : Fin 2 → ZMod N}
    {e : Fin 2 → ZMod M} (hce : ∀ i, (c i).val = g * (e i).val) :
    weightedG2 (Pi.single c (1 : ℂ)) = ((g : ℂ) ^ 2)⁻¹ • weightedG2 (Pi.single e (1 : ℂ)) := by
  ext z
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr fun h0 ↦ NeZero.ne N (by simp [hg, h0])
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  simp only [weightedG2_def, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Pi.smul_apply, smul_eq_mul, hce, hg]
  push_cast
  rw [show ((g : ℂ) * (e 0).val * z + g * (e 1).val) / (g * M) = ((e 0).val * z + (e 1).val) / M by
    field_simp]
  field_simp

/-- The weighted series as a combination of single-residue series. -/
theorem weightedG2_eq_sum_single (W : (Fin 2 → ZMod N) → ℂ) :
    weightedG2 W = ∑ a, W a • weightedG2 (Pi.single a (1 : ℂ)) := by
  conv_lhs => rw [pi_eq_sum_univ' W, ← weightedG2ₗ_apply, map_sum]
  simp only [map_smul, weightedG2ₗ_apply]

end TauCeti.EisensteinSeries
