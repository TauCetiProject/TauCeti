/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
public import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Weighted
import Mathlib.Analysis.Complex.LocallyUniformLimit

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
is the series `∑_y ∑_a W(a) ((ã - N y)₀ z + (ã - N y)₁)⁻²` regularized by subtracting the mean of
`W` times `N⁻² G₂` (`TauCeti.EisensteinSeries.hasSum_weightedG2`); when `W` has total mass zero,
as for the weights of Eisenstein series with a nontrivial character, no regularization occurs
(`TauCeti.EisensteinSeries.hasSum_weightedG2_of_sum_eq_zero`).

As in weight `k ≥ 3`, slashing by `γ ∈ SL(2, ℤ)` replaces the weight by `a ↦ W (a γ⁻¹)`
(`TauCeti.EisensteinSeries.weightedG2_slash_apply`): the lattice of `γ z` is `(c z + d)⁻¹` times
that of `z`, and `℘` is periodic, so it only sees the division point modulo the lattice. Hence
`G₂^W` is a modular form of weight two and level `Γ(N)`
(`TauCeti.EisensteinSeries.weightedG2MF`). Holomorphy follows from the absolute convergence of the
lattice sum, locally uniformly in `z`. Boundedness at `i∞` sums the lattice series along its rows,
each of which decays like `e^(-2π |Im|)`.

## Main definitions

* `TauCeti.EisensteinSeries.weightedG2`: the weight-two series weighted by `W`.
* `TauCeti.EisensteinSeries.weightedG2MF`: it is a modular form of weight two and level `Γ(N)`.

## Main results

* `TauCeti.EisensteinSeries.hasSum_weightedG2`: the series over integer pairs.
* `TauCeti.EisensteinSeries.hasSum_weightedG2_of_sum_eq_zero`: for a weight of total mass zero,
  the weighted series itself.
* `TauCeti.EisensteinSeries.weightedG2_slash_apply`: the slash action.
* `TauCeti.EisensteinSeries.weightedG2_mdifferentiable`: holomorphy on `ℍ`.
* `TauCeti.EisensteinSeries.isBoundedAtImInfty_weightedG2_slash`: every `SL(2, ℤ)`-translate is
  bounded at `i∞`.

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

/-- Right multiplication by the reduction of `γ ∈ SL(2, ℤ)` permutes the residue pairs. -/
private def vecMulEquiv (γ : SL(2, ℤ)) : (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod N) where
  toFun a := a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))
  invFun a := a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))
  left_inv a := by
    simp only [Matrix.vecMul_vecMul]
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, mul_inv_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  right_inv a := by
    simp only [Matrix.vecMul_vecMul]
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul, inv_mul_cancel, map_one,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]

omit [NeZero N] in
private lemma vecMulEquiv_apply (γ : SL(2, ℤ)) (a : Fin 2 → ZMod N) :
    vecMulEquiv γ a = a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := (rfl)

omit [NeZero N] in
private lemma vecMulEquiv_symm_apply (γ : SL(2, ℤ)) (a : Fin 2 → ZMod N) :
    (vecMulEquiv γ).symm a =
      a ᵥ* (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := (rfl)

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
    refine Fintype.sum_equiv (vecMulEquiv γ) _ _ fun a ↦ ?_
    rw [← vecMulEquiv_symm_apply, Equiv.symm_apply_apply, vecMulEquiv_apply]
    ring
  rw [hsum, _root_.zpow_neg, zpow_ofNat]
  field_simp

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
    MDiff (fun z : ℍ ↦ ℘[z.periodPair] (divisionPoint N b z)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hloc : TendstoLocallyUniformlyOn (fun s : Finset (Fin 2 → ℤ) ↦
      ↑ₕ(fun z : ℍ ↦ ∑ y ∈ s, ((N : ℂ) ^ 2 * eisSummand 2 (b - N • y) z - eisSummand 2 y z)))
        (↑ₕ(fun z : ℍ ↦ ℘[z.periodPair] (divisionPoint N b z))) atTop {z : ℂ | 0 < z.im} := by
    rw [← upperHalfPlaneSet, ← range_coe, ← image_univ]
    apply TendstoLocallyUniformlyOn.comp (s := ⊤) _ _ _
      (OpenPartialHomeomorph.continuousOn_symm _)
    · simp only [Set.top_eq_univ, tendstoLocallyUniformlyOn_univ]
      exact tendstoLocallyUniformly_weierstrassP_divisionPoint b
    · simp only [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, Set.top_eq_univ,
        mapsTo_range_iff, Set.mem_univ, forall_const]
  exact hloc.differentiableOn (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun y _ ↦ ((eisSummand_extension_differentiableOn 2 _).const_mul _).sub
      (eisSummand_extension_differentiableOn 2 y)) isOpen_upperHalfPlaneSet

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

/-- A row `P(w) = ∑_n (w + n)⁻²` of the lattice series. -/
private def rowSum (w : ℂ) : ℂ := ∑' n : ℤ, 1 / (w + n) ^ 2

/-- The rows are even functions. -/
private lemma rowSum_neg (w : ℂ) : rowSum (-w) = rowSum w := by
  rw [rowSum, rowSum, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

/-- The decay constant of the rows with `|Im w| ≥ 1 / N`. -/
private def rowConst (N : ℕ) : ℝ := 4 * π ^ 2 / (1 - Real.exp (-2 * π / N)) ^ 2

private lemma rowConst_nonneg (N : ℕ) : 0 ≤ rowConst N := by
  unfold rowConst
  positivity

/-- The rows decay like `e^(-2π |Im w|)` once `|Im w| ≥ 1 / N`. -/
private lemma norm_rowSum_le (w : ℂ) (hw : 1 / (N : ℝ) ≤ |w.im|) :
    ‖rowSum w‖ ≤ rowConst N * Real.exp (-2 * π * |w.im|) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hθ : Real.exp (-2 * π / N) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith [Real.pi_pos]) hN)
  -- reduce to `0 < Im w` by evenness
  wlog hpos : 0 < w.im generalizing w
  · have hne : w.im ≠ 0 := by
      intro h
      rw [h, abs_zero] at hw
      exact absurd hw (not_le.mpr (by positivity))
    have := this (-w) (by simpa using hw) (by simpa using lt_of_le_of_ne (not_lt.mp hpos) hne)
    rwa [rowSum_neg, Complex.neg_im, abs_neg] at this
  rw [abs_of_pos hpos] at hw ⊢
  have hq : ‖cexp (2 * π * Complex.I * w)‖ = Real.exp (-2 * π * w.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h := norm_tsum_one_div_add_sq_le ⟨w, hpos⟩
  simp only [hq] at h
  have hle : Real.exp (-2 * π * w.im) ≤ Real.exp (-2 * π / N) := by
    rw [Real.exp_le_exp, div_eq_mul_inv, mul_le_mul_left_of_neg (by linarith [Real.pi_pos])]
    rwa [one_div] at hw
  refine h.trans ?_
  rw [rowConst, div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
  gcongr

/-- The row bound in the form used along the lattice: `e^(-2π |Im w|) ≤ e^(-2π (|m| - 1))`. -/
private lemma norm_rowSum_le_of_le (w : ℂ) {m : ℤ} (hw : 1 / (N : ℝ) ≤ |w.im|)
    (hm : |(m : ℝ)| - 1 ≤ |w.im|) :
    ‖rowSum w‖ ≤ rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) :=
  (norm_rowSum_le w hw).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) (rowConst_nonneg N))

/-- The rows `P(m z)`, `m ≠ 0`, of the lattice series, on `1 ≤ Im z`. -/
private lemma norm_rowSum_intCast_mul_le {m : ℤ} (hm : m ≠ 0) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖rowSum (m * z)‖ ≤ rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) := by
  have hN1 : (1 : ℝ) / N ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast NeZero.one_le) (Nat.cast_nonneg N)
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
  have ht : |(m : ℝ)| ≤ |((m : ℂ) * z).im| := by
    rw [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, abs_mul,
      UpperHalfPlane.coe_im, abs_of_pos z.im_pos]
    exact le_mul_of_one_le_right (abs_nonneg _) hz
  exact norm_rowSum_le_of_le _ (by linarith) (by linarith)

/-- The rows `P(x - m z)` at a division point `x = (a₀ z + a₁) / N`, for `(m, a₀) ≠ (0, 0)`, on
`1 ≤ Im z`: the imaginary part of `x - m z` is `(a₀ / N - m) Im z` with `a₀ - N m` a nonzero
integer. -/
private lemma norm_rowSum_divisionPoint_sub_le (a : Fin 2 → ZMod N) {m : ℤ}
    (h0 : ¬(m = 0 ∧ (a 0).val = 0)) {z : ℍ} (hz : 1 ≤ z.im) :
    ‖rowSum (divisionPoint N (lift a) z - m * z)‖ ≤
      rowConst N * Real.exp (-2 * π * (|(m : ℝ)| - 1)) := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  set c : ℝ := ((a 0).val : ℝ) / N
  have him : (divisionPoint N (lift a) z - m * z).im = (c - m) * z.im := by
    simp only [divisionPoint, lift, Complex.sub_im, Complex.div_natCast_im, Complex.add_im,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Int.cast_natCast,
      Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im, c]
    ring
  -- the integer `a₀ - N m` is nonzero
  have hk : (1 : ℝ) ≤ |((a 0).val : ℝ) - N * m| := by
    have hk' : ((a 0).val : ℤ) - N * m ≠ 0 := by
      intro h
      have hlt : ((a 0).val : ℤ) < N := by exact_mod_cast ZMod.val_lt (a 0)
      rcases lt_trichotomy m 0 with hm | hm | hm
      · nlinarith
      · exact h0 ⟨hm, by subst hm; omega⟩
      · nlinarith
    exact_mod_cast Int.one_le_abs hk'
  have hc1 : 1 / (N : ℝ) ≤ |c - m| := by
    have hc : |c - m| = |((a 0).val : ℝ) - N * m| / N := by
      have : c - m = (((a 0).val : ℝ) - N * m) / N := by
        simp only [c]
        field_simp
      rw [this, abs_div, abs_of_pos hN]
    rw [hc]
    gcongr
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
  refine Summable.add (Summable.mul_left _ ?_) (summable_of_hasFiniteSupport ?_)
  · have hg : Summable fun n : ℕ ↦ Real.exp (2 * π) * Real.exp (-2 * π) ^ n :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos]))).mul_left _
    have hexp (n : ℕ) : Real.exp (-2 * π * (|((n : ℤ) : ℝ)| - 1)) =
        Real.exp (2 * π) * Real.exp (-2 * π) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
      ring
    refine summable_int_iff_summable_nat_and_neg.mpr ⟨hg.congr fun n ↦ (hexp n).symm, ?_⟩
    refine hg.congr fun n ↦ ?_
    rw [← hexp]
    push_cast
    rw [abs_neg]
  · refine (Set.finite_singleton 0).subset fun m hm ↦ ?_
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
lemma weightedG2MF_add (W W' : (Fin 2 → ZMod N) → ℂ) :
    weightedG2MF (W + W') = weightedG2MF W + weightedG2MF W' := by
  ext z
  exact congrFun (weightedG2_add W W') z

@[simp]
lemma weightedG2MF_smul (c : ℂ) (W : (Fin 2 → ZMod N) → ℂ) :
    weightedG2MF (c • W) = c • weightedG2MF W := by
  ext z
  exact congrFun (weightedG2_smul c W) z

end TauCeti.EisensteinSeries
