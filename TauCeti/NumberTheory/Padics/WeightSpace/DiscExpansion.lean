/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.ExpLog
public import TauCeti.NumberTheory.Padics.WeightSpace.AnalyticLevel
public import TauCeti.NumberTheory.Padics.WeightSpace.ZeroExtend
import TauCeti.Analysis.Normed.Ring.CompactMonoid
import TauCeti.RingTheory.PowerSeries.Exp
import TauCeti.RingTheory.PowerSeries.Restricted.CompNullSeq

/-!
# Expansion of weights on the unit discs of `ℤ_p`

A continuous weight `κ : WeightSpace p R` (`ℤ_pˣ →ₜ* Rˣ`) extends continuously to `ℤ_p` by `0` on
`pℤ_p` (`TauCeti.WeightSpace.zeroExtend`). At level `h = 0`, where `ℤ_p` is a single disc, no
weight over a nontrivial `p`-torsion-free module admits a single power-series expansion
(`TauCeti.WeightSpace.not_exists_eval_zero_eq_zeroExtend`), because `κ.zeroExtend` vanishes on
`pℤ_p` while taking the value `1` at `1`.

Let `k = TauCeti.padicUnitsDepth p` (`k = 1` for odd `p` and `k = 2` for `p = 2`), `q = p ^ k`,
`γ = exp q`, and `h = k + j`. Every disc `a + pʰℤ_p` (`a ∈ ZMod (pʰ)`) lies either entirely inside
`pℤ_p` (when `¬IsUnit a`), where `κ.zeroExtend` vanishes, or entirely inside `ℤ_pˣ` (when
`IsUnit a`). On a unit disc, factoring out the centre `u_a = a.val ∈ ℤ_pˣ` writes every point as
`u_a (1 + pʰ (u_a⁻¹ w))` (`w ∈ ℤ_p`). Since `1 < (p - 1) h`, `1 + pʰ z` lies in the deep
convergence range of the `p`-adic logarithm, and its logarithmic coordinate in `1 + qℤ_p` is
`pʲ · g(z)`, where `g(X) = (pʰ)⁻¹ log(1 + pʰ X) ∈ ℤ_p⟦X⟧` is restricted at radius `1`
(`PadicInt.deepLogSeries`). Hence on the unit disc of `a`,

`κ.zeroExtend(a.val + pʰ w) = κ(u_a) · κ.principalChar(pʲ · g(u_a⁻¹ w))`.

Suppose `R` is a complete ultrametric Banach algebra over `ℤ_p` and `ℚ_p` (possibly noncommutative
and without assuming `‖1‖ = 1`), and suppose `‖κ(γ ^ (p ^ j)) - 1‖ < r_0`, where
`r_0 = TauCeti.amiceRadius p 0 = p ^ (-1 / (p - 1))`. Expanding the additive character
`s ↦ κ.principalChar(pʲ s)` at level `0` by Amice's theorem
(`TauCeti.AnalyticStage.addCharExpansion`), scaling on the left by `κ(u_a)`, and pulling back along
`g(u_a⁻¹ X)` via `PowerSeries.IsRestricted.compNullSeq` yields an explicit coefficient vector
`κ.discExpansion j ht : AnalyticStage p (k + j) R` whose evaluation is `κ.zeroExtend`
(`TauCeti.WeightSpace.eval_discExpansion`). Its constant term on each unit disc `a` is `κ(u_a)`,
its higher coefficients decay by the factor `‖κ(γ ^ (p ^ j)) - 1‖ / r_0 < 1`, its Gauss norm on
each unit disc is `‖κ(u_a)‖`, and its stage norm equals `‖κ.zeroExtend‖`.

Conversely, when the norm on `K` is multiplicative with `‖1‖ = 1`, any expansion in
`AnalyticStage p (k + j) K` agreeing with `κ.zeroExtend` on the principal disc `1 + pʰℤ_p` pulls
back along the normalized deep exponential series `(pʰ)⁻¹ (exp(pʰ X) - 1) ∈ ℤ_p⟦X⟧`
(`PadicInt.deepExpSeries`) to a level-`0` expansion of `s ↦ κ.principalChar(pʲ s)`, forcing
`‖T_κ‖ < r_j` by `TauCeti.AnalyticStage.exists_eval_eq_addChar_iff`. This characterizes the
analytic levels `h ≥ k` of `κ.zeroExtend` (`TauCeti.WeightSpace.exists_eval_eq_zeroExtend_iff`,
`TauCeti.WeightSpace.exists_eval_eq_zeroExtend_of_le_iff`), implies that every weight over such an
algebra is analytic at all large levels
(`TauCeti.WeightSpace.eventually_exists_eval_eq_zeroExtend`), gives conductor bounds for locally
algebraic weights over complete normed field extensions of `ℚ_p`
(`TauCeti.WeightSpace.exists_eval_eq_zeroExtend_inclusion_zpow_mul`), and recovers the binomial
polynomial coefficients of nonnegative algebraic weights `x ↦ x ^ n` on unit discs
(`TauCeti.WeightSpace.discExpansionOfCoord_inclusion_pow_apply`). At `p = 2` and `h = 1`, positive
algebraic weights already have polynomial expansions on `1 + 2ℤ_2`, whereas characters nontrivial
on `{±1}` require `h ≥ 2 = padicUnitsDepth 2`.

## Main definitions

* `TauCeti.WeightSpace.discExpansion`: expansion of `κ.zeroExtend` in
  `AnalyticStage p (padicUnitsDepth p + j) R` when `‖κ(γ ^ (p ^ j)) - 1‖ < amiceRadius p 0`.
* `TauCeti.WeightSpace.discExpansionOfCoord`: the same expansion constructed from
  `‖κ.coord‖ < amiceRadius p j`.

## Main results

* `TauCeti.WeightSpace.not_exists_eval_zero_eq_zeroExtend`: no weight is analytic at level `0` over
  a nontrivial `p`-torsion-free coefficient ring.
* `TauCeti.WeightSpace.discExpansion_apply_of_isUnit`,
  `TauCeti.WeightSpace.discExpansion_apply_of_not_isUnit`,
  `TauCeti.WeightSpace.eval_discExpansion`, `TauCeti.WeightSpace.norm_discExpansion`,
  `TauCeti.WeightSpace.isGreatest_norm_discExpansion_of_isUnit`: coefficient formulas, evaluation,
  global stage norm, and per-disc Gauss norm of `discExpansion` over any complete ultrametric
  Banach algebra.
* `TauCeti.WeightSpace.exists_eval_eq_zeroExtend_iff`,
  `TauCeti.WeightSpace.exists_eval_eq_zeroExtend_of_le_iff`: characterization of the analytic
  levels `h ≥ padicUnitsDepth p` of a weight for a multiplicative ultrametric norm.
* `TauCeti.WeightSpace.eventually_exists_eval_eq_zeroExtend`,
  `TauCeti.WeightSpace.exists_eval_eq_zeroExtend_inclusion_zpow_mul`,
  `TauCeti.WeightSpace.exists_eval_eq_zeroExtend_iff_lt_of_conductor`: eventual analyticity and
  conductor bounds for weights.
* `TauCeti.WeightSpace.discExpansionOfCoord_inclusion_pow_apply`: on unit discs, the expansion of
  `inclusion K ^ n` (`n : ℕ`) has the binomial polynomial coefficients of `(a.val + pʰ w) ^ n`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §§I.3–I.4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3–4.
-/

public section

open Filter Topology NormedSpace
open scoped PowerSeries ZeroAtInfty

namespace TauCeti.WeightSpace

/-- Every level `padicUnitsDepth p + j` is nonzero. -/
theorem padicUnitsDepth_add_ne_zero (p j : ℕ) : padicUnitsDepth p + j ≠ 0 :=
  (Nat.add_pos_left (padicUnitsDepth_pos p) j).ne'

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Level-`0` stage packaging and obstruction to analyticity at level `0` -/

section LevelZero

-- Package a single null sequence `c : C₀(ℕ, E)` into `AnalyticStage p 0 E` (`ZMod (p ^ 0) × ℕ`).
private noncomputable def stageZeroOfSeq {E : Type*} [NormedAddCommGroup E] (c : C₀(ℕ, E)) :
    AnalyticStage p 0 E :=
  haveI : Fintype (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
  (ZeroAtInftyContinuousMap.curryEquiv ℕ E).symm
    ((ZeroAtInftyContinuousMap.equivFunOnFintype ℕ C₀(ℕ, E)).symm fun _ ↦ c)

omit hp in
private theorem stageZeroOfSeq_apply {E : Type*} [NormedAddCommGroup E] (c : C₀(ℕ, E))
    (a : ZMod (p ^ 0)) (m : ℕ) : stageZeroOfSeq (p := p) c (a, m) = c m := by
  rw [stageZeroOfSeq, ZeroAtInftyContinuousMap.curryEquiv_symm_apply,
    ZeroAtInftyContinuousMap.coe_equivFunOnFintype_symm]

private theorem eval_stageZeroOfSeq_apply {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E]
    [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E] (c : C₀(ℕ, E)) (s : ℤ_[p]) :
    AnalyticStage.eval ℤ_[p] (stageZeroOfSeq (p := p) c) s = ∑' m, s ^ m • c m := by
  have hs0 : s = ((0 : ZMod (p ^ 0)).val : ℤ_[p]) + (p : ℤ_[p]) ^ 0 * s := by
    rw [pow_zero]
    simp
  conv_lhs => rw [hs0]
  rw [AnalyticStage.eval_natCast_val_add_mul]
  exact tsum_congr fun m ↦ by rw [stageZeroOfSeq_apply]

/-- **No weight is analytic on all of `ℤ_p` (level `0`).** Over a nontrivial complete ultrametric
ring `R` on which multiplication by `p` is injective, `κ.zeroExtend` vanishes on `pℤ_p` while
taking the value `1 ≠ 0` at `1`, so it is never the evaluation of an element of
`AnalyticStage p 0 R`. -/
theorem not_exists_eval_zero_eq_zeroExtend {R : Type*} [NormedRing R] [Nontrivial R]
    [Module ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    (S : Type*) [Semiring S] [Module S R] [ContinuousConstSMul S R] [SMulCommClass ℤ_[p] S R]
    (hpR : IsSMulRegular R (p : ℤ_[p])) (κ : WeightSpace p R) :
    ¬∃ f : AnalyticStage p 0 R, ⇑(AnalyticStage.eval S f) = κ.zeroExtend := by
  rintro ⟨f, hf⟩
  have hf_eq (x : ℤ_[p]) : AnalyticStage.eval ℤ_[p] f x = κ.zeroExtend x := by
    rw [AnalyticStage.eval_apply, ← AnalyticStage.eval_apply S, congr_fun hf x]
  let f₁ := AnalyticStage.transition ℤ_[p] f
  let row₀ := ZeroAtInftyContinuousMap.curryEquiv ℤ_[p] R f₁ 0
  let g : AnalyticStage p 0 R := stageZeroOfSeq row₀
  have hg_eval : AnalyticStage.eval ℤ_[p] g = 0 := by
    ext w
    have hw : ¬IsUnit ((p : ℤ_[p]) * w) := PadicInt.not_isUnit_iff_dvd.mpr ⟨w, rfl⟩
    rw [eval_stageZeroOfSeq_apply]
    have hsum : (∑' m, w ^ m • row₀ m) =
        AnalyticStage.eval ℤ_[p] f₁ (((0 : ZMod (p ^ 1)).val : ℤ_[p]) + (p : ℤ_[p]) ^ 1 * w) := by
      rw [AnalyticStage.eval_natCast_val_add_mul]
      exact tsum_congr fun m ↦ by rw [ZeroAtInftyContinuousMap.curryEquiv_apply_apply]
    rw [hsum, AnalyticStage.eval_transition, ZMod.val_zero, Nat.cast_zero, zero_add, pow_one,
      hf_eq, zeroExtend_apply_of_not_isUnit κ hw, ContinuousMap.zero_apply]
  have hg0 : g = 0 := AnalyticStage.eval_injective ℤ_[p] hpR (by rw [hg_eval, map_zero])
  have hf0 : f = 0 := by
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    ext ⟨a, m⟩
    have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    have hgm : g (0, m) = 0 := by rw [hg0]; rfl
    have hm : (p : ℤ_[p]) ^ m • f (0, m) = 0 := by
      have hg_app : g (0, m) = (p : ℤ_[p]) ^ m • f (0, m) := by
        have hcast : ((0 : ZMod (p ^ 0)).cast : ZMod (p ^ 1)) = 0 := by
          rw [ZMod.cast_eq_val, pow_zero]
          simp
        rw [stageZeroOfSeq_apply]
        dsimp only [row₀, f₁]
        rw [ZeroAtInftyContinuousMap.curryEquiv_apply_apply, ← hcast]
        exact AnalyticStage.transition_apply_cast ℤ_[p] f 0 m
      exact hg_app.symm.trans hgm
    exact hpR.pow m (hm.trans (smul_zero _).symm)
  have h1 : κ.zeroExtend 1 = 0 := by rw [← hf_eq 1, hf0, map_zero, ContinuousMap.zero_apply]
  exact one_ne_zero (κ.zeroExtend_one.symm.trans h1)

end LevelZero

/-! ### Logarithmic factorization and Banach-algebra expansion on unit discs -/

section DiscHelpers

/-- Every level `padicUnitsDepth p + j` lies in the deep convergence range `1 < (p - 1) * h`. -/
theorem one_lt_sub_one_mul_padicUnitsDepth_add (j : ℕ) :
    1 < (p - 1) * (padicUnitsDepth p + j) :=
  one_lt_sub_one_mul_padicUnitsDepth.trans_le (Nat.mul_le_mul_left _ (Nat.le_add_right _ j))

/-- On the principal disc `1 + p ^ (k + j) ℤ_p`, `1 + p ^ (k + j) z` is the principal unit whose
logarithmic coordinate is `p ^ j · (deepLogSeries hh).evalAt z`. -/
private theorem zeroExtend_one_add_pow_mul {R : Type*} [MonoidWithZero R] [TopologicalSpace R]
    (κ : WeightSpace p R) (j : ℕ) (z : ℤ_[p]) :
    κ.zeroExtend (1 + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * z) =
      κ.principalChar ((p : ℤ_[p]) ^ j *
        (PadicInt.deepLogSeries (one_lt_sub_one_mul_padicUnitsDepth_add (p := p) j)).evalAt z) := by
  let k := padicUnitsDepth p
  let h := k + j
  have hh := one_lt_sub_one_mul_padicUnitsDepth_add (p := p) j
  let u₁ : unitsPrincipal p h :=
    unitsPrincipalMk (padicUnitsDepth_add_ne_zero p j) ⟨z, add_sub_cancel_left _ _⟩
  let u₀ : unitsPrincipal p k := ⟨u₁, unitsPrincipal_antitone p (Nat.le_add_right k j) u₁.2⟩
  have hu₀_val : ((u₀ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ h * z :=
    coe_unitsPrincipalMk (padicUnitsDepth_add_ne_zero p j) _
  have hlog : (unitsPrincipalLogEquiv p u₀).toAdd =
      (p : ℤ_[p]) ^ j * (PadicInt.deepLogSeries hh).evalAt z := by
    apply PadicInt.ext
    have hpk : (p : ℚ_[p]) ^ padicUnitsDepth p ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    have hpj : (p : ℚ_[p]) ^ j ≠ 0 := pow_ne_zero j (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    rw [coe_unitsPrincipalLogEquiv_apply, hu₀_val, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast, PadicInt.coe_evalAt_deepLogSeries hh z]
    push_cast
    dsimp only [h, k]
    rw [pow_add (p : ℚ_[p]) (padicUnitsDepth p) j]
    field_simp [hpk, hpj]
  have hu₀_symm : (u₀ : ℤ_[p]ˣ) =
       ((unitsPrincipalLogEquiv p).symm
        (.ofAdd ((p : ℤ_[p]) ^ j * (PadicInt.deepLogSeries hh).evalAt z)) : ℤ_[p]ˣ) := by
    congr 1
    rw [← hlog, ofAdd_toAdd, ContinuousMulEquiv.symm_apply_apply]
  rw [← hu₀_val, zeroExtend_coe_unit, hu₀_symm, principalChar_apply]

/-- On any unit disc `a + p ^ (k + j) ℤ_p` (`IsUnit a`), `κ.zeroExtend (a.val + p ^ (k + j) w)`
factors as `κ(u_a)` times `κ.principalChar` at `p ^ j · (deepLogSeries hh).evalAt (u_a⁻¹ w)`. -/
private theorem zeroExtend_natCast_val_add_mul_of_isUnit {R : Type*} [MonoidWithZero R]
    [TopologicalSpace R] (κ : WeightSpace p R) (j : ℕ) {a : ZMod (p ^ (padicUnitsDepth p + j))}
    (ha : IsUnit a) (w : ℤ_[p]) :
    let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    κ.zeroExtend ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w) =
      (κ u : R) * κ.principalChar ((p : ℤ_[p]) ^ j *
        (PadicInt.deepLogSeries (one_lt_sub_one_mul_padicUnitsDepth_add (p := p) j)).evalAt
          ((↑u⁻¹ : ℤ_[p]) * w)) := by
  intro u
  have hfac : (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w =
      (u : ℤ_[p]) * (1 + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * ((↑u⁻¹ : ℤ_[p]) * w)) := by
    calc (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w
        = (u : ℤ_[p]) + ((u : ℤ_[p]) * ↑u⁻¹) *
            ((p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w) := by
          rw [u.mul_inv, one_mul, IsUnit.unit_spec]
      _ = (u : ℤ_[p]) * (1 + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * ((↑u⁻¹ : ℤ_[p]) * w)) := by
          ring
  rw [hfac, zeroExtend_mul_apply, zeroExtend_coe_unit, zeroExtend_one_add_pow_mul]

end DiscHelpers

section DiscExpansion

-- Left multiplication by `c : R` is `ℤ_p`-linear (since `ℤ_p` acts centrally through
-- `algebraMap ℤ_[p] R`) and bounded by `‖c‖`, even when `R` is noncommutative.
private noncomputable def mulLeftPadicIntCLM {R : Type*} [NormedRing R] [Algebra ℤ_[p] R]
    (c : R) : R →L[ℤ_[p]] R :=
  let L : R →ₗ[ℤ_[p]] R :=
    { toFun x := c * x
      map_add' := mul_add c
      map_smul' z x := by
        rw [RingHom.id_apply, mul_smul_comm] }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L ‖c‖ (norm_mul_le c) }

@[simp]
private theorem mulLeftPadicIntCLM_apply {R : Type*} [NormedRing R] [Algebra ℤ_[p] R]
    (c x : R) : mulLeftPadicIntCLM (p := p) c x = c * x :=
  (rfl)

-- The shifted additive character `s ↦ κ.principalChar (p ^ j * s)` of `ℤ_p`.
private noncomputable def shiftedPrincipalChar {M : Type*} [Monoid M] [TopologicalSpace M]
    (κ : WeightSpace p M) (j : ℕ) : AddChar ℤ_[p] M where
  toFun s := κ.principalChar ((p : ℤ_[p]) ^ j * s)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [mul_add, AddChar.map_add_eq_mul]

@[simp]
private theorem shiftedPrincipalChar_apply {M : Type*} [Monoid M] [TopologicalSpace M]
    (κ : WeightSpace p M) (j : ℕ) (s : ℤ_[p]) :
    shiftedPrincipalChar κ j s = κ.principalChar ((p : ℤ_[p]) ^ j * s) :=
  (rfl)

private theorem continuous_shiftedPrincipalChar {M : Type*} [Monoid M] [TopologicalSpace M]
    (κ : WeightSpace p M) (j : ℕ) : Continuous (shiftedPrincipalChar κ j) :=
  κ.continuous_principalChar.comp (continuous_const.mul continuous_id)

private theorem shiftedPrincipalChar_one {M : Type*} [Monoid M] [TopologicalSpace M]
    (κ : WeightSpace p M) (j : ℕ) :
    shiftedPrincipalChar κ j 1 = κ (padicUnitsGenerator p ^ p ^ j) := by
  rw [shiftedPrincipalChar_apply, mul_one, ← Nat.cast_pow, ← nsmul_one, AddChar.map_nsmul_eq_pow,
    principalChar_one, map_pow, Units.val_pow_eq_pow_val]

variable {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [Module ℚ_[p] R]
  [IsBoundedSMul ℚ_[p] R] [IsUltrametricDist R] [CompleteSpace R]

omit [Module ℚ_[p] R] [IsBoundedSMul ℚ_[p] R] [CompleteSpace R] in
private theorem tendsto_apply_padicUnitsGenerator_pow_sub_one_pow (κ : WeightSpace p R) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1) ^ n) atTop (𝓝 0) := by
  simpa only [shiftedPrincipalChar_one] using
    (shiftedPrincipalChar κ j).tendsto_eval_one_sub_pow (continuous_shiftedPrincipalChar κ j)

omit [Module ℚ_[p] R] [IsBoundedSMul ℚ_[p] R] in
private theorem principalChar_pow_mul_eq_addChar (κ : WeightSpace p R) (j : ℕ) (s : ℤ_[p]) :
    κ.principalChar ((p : ℤ_[p]) ^ j * s) =
      PadicInt.addChar_of_value_at_one ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1)
        (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j) s := by
  have heq : shiftedPrincipalChar κ j =
      PadicInt.addChar_of_value_at_one ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1)
        (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j) :=
    PadicInt.eq_addChar_of_value_at_one _ (continuous_shiftedPrincipalChar κ j)
      (by rw [shiftedPrincipalChar_one, add_sub_cancel])
  exact DFunLike.congr_fun heq s

-- Rescaling `deepLogSeries` by a unit of `ℤ_p` preserves restrictedness at radius `1`.
private theorem isRestricted_rescale_deepLogSeries (j : ℕ) (u : ℤ_[p]ˣ) :
    (PowerSeries.rescale (u : ℤ_[p])
      (PadicInt.deepLogSeries (one_lt_sub_one_mul_padicUnitsDepth_add (p := p) j))).IsRestricted
        1 := by
  refine PowerSeries.IsRestricted.rescale ?_
  rw [PadicInt.isUnit_iff.mp u.isUnit, one_mul]
  exact PadicInt.isRestricted_deepLogSeries _

/-- **Expansion of a weight on the discs of `ℤ_p` at level `padicUnitsDepth p + j`.** Given a
weight `κ : WeightSpace p R` into a complete ultrametric Banach algebra `R` over `ℤ_p` and `ℚ_p`
with `‖κ(γ ^ (p ^ j)) - 1‖ < amiceRadius p 0`, `κ.discExpansion j ht` vanishes on non-unit discs
and pulls back the level-`0` Amice expansion of `s ↦ κ.principalChar (p ^ j * s)` (scaled on the
left by `κ(u_a)`) along `w ↦ (p ^ h)⁻¹ log(1 + p ^ h u_a⁻¹ w)` on each unit disc `a + p ^ h ℤ_p`.
-/
noncomputable def discExpansion (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) :
    AnalyticStage p (padicUnitsDepth p + j) R :=
  let b₀ : C₀(ℕ, R) :=
    ZeroAtInftyContinuousMap.curryEquiv ℤ_[p] R
      (AnalyticStage.addCharExpansion p 0 ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1) ht) 0
  let row (a : ZMod (p ^ (padicUnitsDepth p + j))) : C₀(ℕ, R) :=
    if ha : IsUnit a then
      let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
      PowerSeries.IsRestricted.compNullSeq ℤ_[p]
        (isRestricted_rescale_deepLogSeries j u⁻¹)
        (fun _ ↦ PadicInt.norm_le_one _)
        (ZeroAtInftyContinuousMap.compLeft (mulLeftPadicIntCLM (p := p) (κ u : R))
          ⟨‖(κ u : R)‖, norm_mul_le _⟩ b₀)
    else 0
  (ZeroAtInftyContinuousMap.curryEquiv ℤ_[p] R).symm
    ((ZeroAtInftyContinuousMap.equivFunOnFintype ℤ_[p] C₀(ℕ, R)).symm row)

/-- **Expansion of a weight from its coordinate bound.** For `‖κ.coord‖ < amiceRadius p j`, the
expansion of `κ.zeroExtend` in `AnalyticStage p (padicUnitsDepth p + j) R` obtained from
`WeightSpace.discExpansion`. -/
noncomputable def discExpansionOfCoord (κ : WeightSpace p R) (j : ℕ)
    (hT : ‖κ.coord‖ < amiceRadius p j) :
    AnalyticStage p (padicUnitsDepth p + j) R :=
  κ.discExpansion j <| by
    rw [apply_padicUnitsGenerator_pow]
    exact norm_one_add_pow_sub_one_lt_of_norm_lt hT

theorem discExpansionOfCoord_eq_discExpansion (κ : WeightSpace p R) (j : ℕ)
    (hT : ‖κ.coord‖ < amiceRadius p j) :
    κ.discExpansionOfCoord j hT =
      κ.discExpansion j (by
        rw [apply_padicUnitsGenerator_pow]
        exact norm_one_add_pow_sub_one_lt_of_norm_lt hT) :=
  (rfl)

/-- On every unit residue class `a`, the `m`-th coefficient of `κ.discExpansion` is the pullback
along `rescale u_a⁻¹ (deepLogSeries hh)` of `n ↦ κ(u_a) * addCharExpansion p 0 t ht (0, n)`. -/
theorem discExpansion_apply_of_isUnit (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) (m : ℕ) :
    let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    κ.discExpansion j ht (a, m) =
      ∑' n, PowerSeries.coeff m
          (PowerSeries.rescale (↑u⁻¹ : ℤ_[p])
            (PadicInt.deepLogSeries (one_lt_sub_one_mul_padicUnitsDepth_add (p := p) j)) ^ n) •
        ((κ u : R) *
          AnalyticStage.addCharExpansion p 0
            ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1) ht (0, n)) := by
  intro u
  simp only [discExpansion, ZeroAtInftyContinuousMap.curryEquiv_symm_apply,
    ZeroAtInftyContinuousMap.coe_equivFunOnFintype_symm, ha, ↓reduceDIte,
    PowerSeries.IsRestricted.compNullSeq_apply, ZeroAtInftyContinuousMap.compLeft_apply,
    mulLeftPadicIntCLM_apply, ZeroAtInftyContinuousMap.curryEquiv_apply_apply, u]

/-- On every non-unit residue class `a`, all coefficients of `κ.discExpansion` vanish. -/
theorem discExpansion_apply_of_not_isUnit (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : ¬IsUnit a) (m : ℕ) :
    κ.discExpansion j ht (a, m) = 0 := by
  simp [discExpansion, ha]

/-- On every unit residue class `a`, the constant coefficient of `κ.discExpansion` is the value of
`κ` at the natural unit representative `a.val` of `a`. -/
theorem discExpansion_apply_zero_of_isUnit (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) :
    κ.discExpansion j ht (a, 0) =
      κ ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit := by
  have hg0 : PowerSeries.constantCoeff
      (PowerSeries.rescale
        (↑(((PadicInt.isUnit_natCast_val_iff
          (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit)⁻¹ : ℤ_[p])
        (PadicInt.deepLogSeries (one_lt_sub_one_mul_padicUnitsDepth_add (p := p) j))) = 0 := by
    rw [PowerSeries.constantCoeff_rescale, PadicInt.constantCoeff_deepLogSeries]
  have hval0 : (0 : ZMod (p ^ 0)).val = 0 := by
    rw [pow_zero]
    simp
  simp only [discExpansion, ZeroAtInftyContinuousMap.curryEquiv_symm_apply,
    ZeroAtInftyContinuousMap.coe_equivFunOnFintype_symm, ha, ↓reduceDIte]
  rw [PowerSeries.IsRestricted.compNullSeq_apply_zero_of_constantCoeff_eq_zero ℤ_[p] _ _ hg0,
    ZeroAtInftyContinuousMap.compLeft_apply, mulLeftPadicIntCLM_apply,
    ZeroAtInftyContinuousMap.curryEquiv_apply_apply, AnalyticStage.addCharExpansion_apply_zero,
    hval0, pow_zero, mul_one]

/-- **Evaluation of `discExpansion`.** Over any complete ultrametric Banach algebra `R` over `ℤ_p`
and `ℚ_p`, `κ.discExpansion j ht` evaluates to the continuous zero-extension `κ.zeroExtend` on
`ℤ_p`. -/
theorem eval_discExpansion (S : Type*) [Semiring S] [Module S R] [ContinuousConstSMul S R]
    [SMulCommClass ℤ_[p] S R] (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) :
    ⇑(AnalyticStage.eval S (κ.discExpansion j ht)) = κ.zeroExtend := by
  ext x
  let h := padicUnitsDepth p + j
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  rw [PadicInt.discHomeomorph_apply, AnalyticStage.eval_natCast_val_add_mul]
  by_cases ha : IsUnit a
  · let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    let t := (κ (padicUnitsGenerator p ^ p ^ j) : R) - 1
    let c₀ := AnalyticStage.addCharExpansion p 0 t ht
    let b₀ : C₀(ℕ, R) := ZeroAtInftyContinuousMap.curryEquiv ℤ_[p] R c₀ 0
    have hcoeff (m : ℕ) : κ.discExpansion j ht (a, m) =
        PowerSeries.IsRestricted.compNullSeq ℤ_[p]
          (isRestricted_rescale_deepLogSeries j u⁻¹) (fun _ ↦ PadicInt.norm_le_one _)
          (ZeroAtInftyContinuousMap.compLeft (mulLeftPadicIntCLM (p := p) (κ u : R))
            ⟨‖(κ u : R)‖, norm_mul_le _⟩ b₀) m := by
      simp [discExpansion, ha, u, b₀, c₀, t]
    simp_rw [hcoeff]
    rw [PowerSeries.IsRestricted.tsum_pow_smul_compNullSeq ℤ_[p] _ _ _ (PadicInt.norm_le_one w)]
    let z := (PowerSeries.rescale (↑u⁻¹ : ℤ_[p])
      (PadicInt.deepLogSeries (one_lt_sub_one_mul_padicUnitsDepth_add (p := p) j))).evalAt w
    have h0z : ((0 : ZMod (p ^ 0)).val : ℤ_[p]) + (p : ℤ_[p]) ^ 0 * z = z := by
      rw [pow_zero]
      simp
    have hsum_c₀ : HasSum (fun n ↦ z ^ n • c₀ (0, n)) (AnalyticStage.eval ℤ_[p] c₀ z) := by
      simpa only [h0z] using AnalyticStage.hasSum_eval_natCast_val_add_mul ℤ_[p] c₀ 0 z
    have hmul_sum : (∑' n, z ^ n • ((κ u : R) * c₀ (0, n))) =
        (κ u : R) * AnalyticStage.eval ℤ_[p] c₀ z := by
      refine ((hsum_c₀.mul_left (κ u : R)).congr_fun fun n ↦ ?_).tsum_eq
      rw [mul_smul_comm]
    have hcomp (n : ℕ) :
        ZeroAtInftyContinuousMap.compLeft (mulLeftPadicIntCLM (p := p) (κ u : R))
          ⟨‖(κ u : R)‖, norm_mul_le _⟩ b₀ n = (κ u : R) * c₀ (0, n) := by
      rw [ZeroAtInftyContinuousMap.compLeft_apply, mulLeftPadicIntCLM_apply,
        ZeroAtInftyContinuousMap.curryEquiv_apply_apply]
    simp_rw [hcomp]
    rw [hmul_sum, AnalyticStage.eval_addCharExpansion ℤ_[p] ht
      (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j),
      ← principalChar_pow_mul_eq_addChar,
      zeroExtend_natCast_val_add_mul_of_isUnit κ j ha w]
    simp only [z, PowerSeries.evalAt_rescale, smul_eq_mul, u]
  · have hnu : ¬IsUnit ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) := by
      rwa [PadicInt.isUnit_natCast_val_add_mul_iff (padicUnitsDepth_add_ne_zero p j)]
    simp only [discExpansion_apply_of_not_isUnit κ j ht ha, smul_zero, tsum_zero,
      zeroExtend_apply_of_not_isUnit κ hnu]

@[simp]
theorem eval_discExpansion_eq_zeroExtend (S : Type*) [Semiring S] [Module S R]
    [ContinuousConstSMul S R] [SMulCommClass ℤ_[p] S R] (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) :
    AnalyticStage.eval S (κ.discExpansion j ht) = κ.zeroExtend :=
  ContinuousMap.ext (congr_fun (eval_discExpansion S κ j ht))

/-- `discExpansionOfCoord` evaluates to `κ.zeroExtend`. -/
theorem eval_discExpansionOfCoord (S : Type*) [Semiring S] [Module S R] [ContinuousConstSMul S R]
    [SMulCommClass ℤ_[p] S R] (κ : WeightSpace p R) (j : ℕ) (hT : ‖κ.coord‖ < amiceRadius p j) :
    ⇑(AnalyticStage.eval S (κ.discExpansionOfCoord j hT)) = κ.zeroExtend :=
  eval_discExpansion S κ j _

@[simp]
theorem eval_discExpansionOfCoord_eq_zeroExtend (S : Type*) [Semiring S] [Module S R]
    [ContinuousConstSMul S R] [SMulCommClass ℤ_[p] S R] (κ : WeightSpace p R) (j : ℕ)
    (hT : ‖κ.coord‖ < amiceRadius p j) :
    AnalyticStage.eval S (κ.discExpansionOfCoord j hT) = κ.zeroExtend :=
  eval_discExpansion_eq_zeroExtend S κ j _

/-- At level `0`, every positive-degree coefficient of `addCharExpansion p 0 t ht` has norm at most
`‖t‖ / amiceRadius p 0` (without requiring `NormOneClass R`). -/
private theorem norm_addCharExpansion_zero_apply_le_of_ne_zero {t : R}
    (ht : ‖t‖ < amiceRadius p 0) {n : ℕ} (hn : n ≠ 0) :
    ‖AnalyticStage.addCharExpansion p 0 t ht (0, n)‖ ≤ ‖t‖ / amiceRadius p 0 := by
  have hr0 : 0 < amiceRadius p 0 := amiceRadius_pos 0
  have hB0 : 0 ≤ ‖t‖ / amiceRadius p 0 := div_nonneg (norm_nonneg t) hr0.le
  have hB1 : ‖t‖ / amiceRadius p 0 ≤ 1 := (div_le_one hr0).mpr ht.le
  have hval0 : ((0 : ZMod (p ^ 0)).val : ℤ_[p]) = 0 := by
    rw [pow_zero]
    simp
  rw [AnalyticStage.addCharExpansion_apply]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hB0 fun l ↦ ?_
  rcases eq_or_ne l 0 with rfl | hl
  · rw [hval0, coeff_amicePolynomial_eq_zero 0 (Nat.pos_of_ne_zero hn), zero_smul, norm_zero]
    exact hB0
  · refine (norm_smul_le _ _).trans ?_
    refine (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)).trans ?_
    refine (norm_amiceCharCoeff_le 0 t l).trans ?_
    have hpow : ‖t ^ l‖ / ‖((l / p ^ 0).factorial : ℚ_[p])‖ ≤ (‖t‖ / amiceRadius p 0) ^ l := by
      rw [div_pow]
      exact div_le_div₀ (by positivity) (norm_pow_le' t (Nat.pos_of_ne_zero hl))
        (pow_pos hr0 l) (amiceRadius_pow_le_norm_factorial 0 l)
    exact hpow.trans (pow_le_of_le_one hB0 hB1 hl)

/-- **Higher-degree coefficient decay on unit discs.** For `m ≠ 0` on a unit disc `a`,
`‖κ.discExpansion j ht (a, m)‖ ≤ ‖κ(u_a)‖ * (‖κ(γ ^ (p ^ j)) - 1‖ / r_0)`. -/
theorem norm_discExpansion_apply_le_of_ne_zero (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) {m : ℕ} (hm : m ≠ 0) :
    let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    ‖κ.discExpansion j ht (a, m)‖ ≤
      ‖(κ u : R)‖ * (‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ / amiceRadius p 0) := by
  intro u
  let t := (κ (padicUnitsGenerator p ^ p ^ j) : R) - 1
  have hr0 : 0 < amiceRadius p 0 := amiceRadius_pos 0
  have hB0 : 0 ≤ ‖(κ u : R)‖ * (‖t‖ / amiceRadius p 0) :=
    mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg t) hr0.le)
  simp only [discExpansion, ZeroAtInftyContinuousMap.curryEquiv_symm_apply,
    ZeroAtInftyContinuousMap.coe_equivFunOnFintype_symm, ha, ↓reduceDIte]
  refine PowerSeries.IsRestricted.norm_compNullSeq_apply_le_of_ne_zero ℤ_[p] _ _ hB0
    (fun n hn ↦ ?_) hm
  simp only [ZeroAtInftyContinuousMap.compLeft_apply, mulLeftPadicIntCLM_apply,
    ZeroAtInftyContinuousMap.curryEquiv_apply_apply]
  refine (norm_mul_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_addCharExpansion_zero_apply_le_of_ne_zero ht hn)
    (norm_nonneg _)

/-- **Gauss norm on unit discs.** Over any complete ultrametric Banach algebra `R`, on each unit
disc `a` the largest coefficient norm of `κ.discExpansion j ht` is `‖κ(u_a)‖`, attained at degree
`0`. -/
theorem isGreatest_norm_discExpansion_of_isUnit (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) :
    let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    IsGreatest (Set.range fun m ↦ ‖κ.discExpansion j ht (a, m)‖) ‖(κ u : R)‖ := by
  intro u
  refine ⟨⟨0, by dsimp only; rw [discExpansion_apply_zero_of_isUnit κ j ht ha]⟩, ?_⟩
  rintro _ ⟨m, rfl⟩
  dsimp only
  rcases eq_or_ne m 0 with rfl | hm
  · rw [discExpansion_apply_zero_of_isUnit κ j ht ha]
  · have h1 : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ / amiceRadius p 0 ≤ 1 :=
      (div_le_one (amiceRadius_pos 0)).mpr ht.le
    exact (norm_discExpansion_apply_le_of_ne_zero κ j ht ha hm).trans
      (mul_le_of_le_one_right (norm_nonneg _) h1)

/-- **Exact stage norm of `discExpansion`.** Over any complete ultrametric Banach algebra `R`, the
analytic-stage norm of `κ.discExpansion j ht` equals the supremum norm `‖κ.zeroExtend‖`. -/
@[simp]
theorem norm_discExpansion (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) :
    ‖κ.discExpansion j ht‖ = ‖κ.zeroExtend‖ := by
  refine le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg _)).mpr fun ⟨a, m⟩ ↦ ?_) ?_
  · by_cases ha : IsUnit a
    · let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
      have hle : ‖κ.discExpansion j ht (a, m)‖ ≤ ‖(κ u : R)‖ :=
        (isGreatest_norm_discExpansion_of_isUnit κ j ht ha).2 ⟨m, rfl⟩
      exact hle.trans (by
        simpa only [zeroExtend_coe_unit] using ContinuousMap.norm_coe_le_norm κ.zeroExtend u)
    · simp [discExpansion_apply_of_not_isUnit κ j ht ha]
  · rw [← eval_discExpansion_eq_zeroExtend ℤ_[p] κ j ht]
    exact AnalyticStage.norm_eval_le ℤ_[p] _

@[simp]
theorem norm_discExpansionOfCoord (κ : WeightSpace p R) (j : ℕ)
    (hT : ‖κ.coord‖ < amiceRadius p j) :
    ‖κ.discExpansionOfCoord j hT‖ = ‖κ.zeroExtend‖ :=
  norm_discExpansion κ j _

end DiscExpansion

/-! ### Converse and characterization of analytic levels for multiplicative norms -/

section NormMulClass

variable {K : Type*} [NormedRing K] [NormMulClass K] [NormOneClass K]
  [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [Module ℚ_[p] K] [NormSMulClass ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

/-- For a multiplicative norm with `‖1‖ = 1`, `κ.discExpansion j ht` has norm `1`. -/
theorem norm_discExpansion_eq_one (κ : WeightSpace p K) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : K) - 1‖ < amiceRadius p 0) :
    ‖κ.discExpansion j ht‖ = 1 := by
  rw [norm_discExpansion, norm_zeroExtend_eq_one]

/-- For a multiplicative norm with `‖1‖ = 1`, `κ.discExpansionOfCoord j hT` has norm `1`. -/
theorem norm_discExpansionOfCoord_eq_one (κ : WeightSpace p K) (j : ℕ)
    (hT : ‖κ.coord‖ < amiceRadius p j) :
    ‖κ.discExpansionOfCoord j hT‖ = 1 := by
  rw [norm_discExpansionOfCoord, norm_zeroExtend_eq_one]

/-- For a multiplicative norm with `‖1‖ = 1`, `κ.discExpansion j ht` has Gauss norm `1` on every
unit disc `a`. -/
theorem isGreatest_norm_discExpansion_eq_one_of_isUnit (κ : WeightSpace p K) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : K) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) :
    IsGreatest (Set.range fun m ↦ ‖κ.discExpansion j ht (a, m)‖) 1 := by
  simpa only [κ.norm_apply_eq_one_of_compactSpace] using
    isGreatest_norm_discExpansion_of_isUnit κ j ht ha

variable (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]

/-- **Converse on the principal disc `1 + p ^ (k + j) ℤ_p`.** If an element of
`AnalyticStage p (padicUnitsDepth p + j) K` agrees after evaluation with `κ.zeroExtend` on the
principal disc `1 + p ^ (padicUnitsDepth p + j) ℤ_p`, then `‖κ.coord‖ < amiceRadius p j`. -/
theorem norm_coord_lt_amiceRadius_of_eval_one_add_pow_mul (κ : WeightSpace p K) {j : ℕ}
    {f : AnalyticStage p (padicUnitsDepth p + j) K}
    (hf : ∀ w : ℤ_[p],
      AnalyticStage.eval S f (1 + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w) =
        κ.zeroExtend (1 + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w)) :
    ‖κ.coord‖ < amiceRadius p j := by
  -- Pull the `a = 1` power series back along `deepExpSeries` to obtain a level-`0` expansion of
  -- `s ↦ κ.principalChar (p ^ j * s)`.
  let h := padicUnitsDepth p + j
  have hh := one_lt_sub_one_mul_padicUnitsDepth_add (p := p) j
  have h1val : ((1 : ZMod (p ^ h)).val : ℤ_[p]) = 1 := by
    have hgt : 1 < p ^ h := Nat.one_lt_pow (padicUnitsDepth_add_ne_zero p j) hp.out.one_lt
    rw [ZMod.val_one'' hgt.ne', Nat.cast_one]
  let row₁ : C₀(ℕ, K) := ZeroAtInftyContinuousMap.curryEquiv ℤ_[p] K f 1
  let c₀ : C₀(ℕ, K) :=
    PowerSeries.IsRestricted.compNullSeq ℤ_[p]
      (PadicInt.isRestricted_deepExpSeries hh) (fun _ ↦ PadicInt.norm_le_one _) row₁
  let f₀ : AnalyticStage p 0 K := stageZeroOfSeq c₀
  have hf₀ : ⇑(AnalyticStage.eval ℤ_[p] f₀) =
      PadicInt.addChar_of_value_at_one ((κ (padicUnitsGenerator p ^ p ^ j) : K) - 1)
        (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j) := by
    ext s
    rw [eval_stageZeroOfSeq_apply,
      PowerSeries.IsRestricted.tsum_pow_smul_compNullSeq ℤ_[p] _ _ _ (PadicInt.norm_le_one s)]
    let w := (PadicInt.deepExpSeries hh).evalAt s
    have hev₁ : (∑' n, w ^ n • row₁ n) =
        AnalyticStage.eval S f (1 + (p : ℤ_[p]) ^ h * w) := by
      rw [← h1val, AnalyticStage.eval_natCast_val_add_mul]
      exact tsum_congr fun n ↦ by rw [ZeroAtInftyContinuousMap.curryEquiv_apply_apply]
    have hexp_unit : 1 + (p : ℤ_[p]) ^ h * w =
        (((unitsPrincipalLogEquiv p).symm (.ofAdd ((p : ℤ_[p]) ^ j * s)) : ℤ_[p]ˣ) : ℤ_[p]) := by
      apply PadicInt.ext
      rw [coe_unitsPrincipalLogEquiv_symm_apply, toAdd_ofAdd]
      push_cast
      rw [← mul_assoc, ← pow_add]
      exact PadicInt.one_add_pow_mul_coe_evalAt_deepExpSeries hh s
    rw [hev₁, hf w, hexp_unit, zeroExtend_coe_unit, ← principalChar_apply,
      principalChar_pow_mul_eq_addChar]
  rw [← norm_apply_padicUnitsGenerator_pow_sub_one_lt_iff]
  exact (AnalyticStage.exists_eval_eq_addChar_iff ℤ_[p]
    (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j)).mp ⟨f₀, hf₀⟩

/-- **Characterization of the analytic levels of a weight.** For complete coefficients with a
multiplicative ultrametric norm, `κ.zeroExtend` is the evaluation of a coefficient vector in
`AnalyticStage p (padicUnitsDepth p + j) K` if and only if `‖κ.coord‖ < amiceRadius p j`. -/
theorem exists_eval_eq_zeroExtend_iff (κ : WeightSpace p K) {j : ℕ} :
    (∃ f : AnalyticStage p (padicUnitsDepth p + j) K,
      ⇑(AnalyticStage.eval S f) = κ.zeroExtend) ↔ ‖κ.coord‖ < amiceRadius p j :=
  ⟨fun ⟨_, hf⟩ ↦ norm_coord_lt_amiceRadius_of_eval_one_add_pow_mul S κ
      (fun _ ↦ congr_fun hf _),
    fun hT ↦ ⟨κ.discExpansionOfCoord j hT, eval_discExpansionOfCoord S κ j hT⟩⟩

/-- **Characterization in terms of `κ(γ ^ (p ^ j)) - 1`.** For complete coefficients with a
multiplicative ultrametric norm, `κ.zeroExtend` lies in the image of
`AnalyticStage p (padicUnitsDepth p + j) K` if and only if
`‖κ(γ ^ (p ^ j)) - 1‖ < amiceRadius p 0`. -/
theorem exists_eval_eq_zeroExtend_iff_norm_sub_one_lt (κ : WeightSpace p K) {j : ℕ} :
    (∃ f : AnalyticStage p (padicUnitsDepth p + j) K,
      ⇑(AnalyticStage.eval S f) = κ.zeroExtend) ↔
      ‖(κ (padicUnitsGenerator p ^ p ^ j) : K) - 1‖ < amiceRadius p 0 := by
  rw [exists_eval_eq_zeroExtend_iff S, norm_apply_padicUnitsGenerator_pow_sub_one_lt_iff]

/-- **Characterization at any level `h ≥ padicUnitsDepth p`.** For `padicUnitsDepth p ≤ h`,
`κ.zeroExtend` lies in the image of `AnalyticStage p h K` if and only if
`‖κ.coord‖ < amiceRadius p (h - padicUnitsDepth p)`. -/
theorem exists_eval_eq_zeroExtend_of_le_iff (κ : WeightSpace p K) {h : ℕ}
    (hh : padicUnitsDepth p ≤ h) :
    (∃ f : AnalyticStage p h K, ⇑(AnalyticStage.eval S f) = κ.zeroExtend) ↔
      ‖κ.coord‖ < amiceRadius p (h - padicUnitsDepth p) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hh
  simpa only [Nat.add_sub_cancel_left] using exists_eval_eq_zeroExtend_iff S κ (j := j)

/-- Whenever `‖κ.coord‖ < amiceRadius p j` over a complete ultrametric `ℚ_p`-algebra with
multiplicative norm, `κ.zeroExtend` is the evaluation of a norm-`1` element of
`AnalyticStage p (padicUnitsDepth p + j) K`. -/
theorem exists_norm_eq_one_and_eval_eq_zeroExtend_of_norm_coord_lt (κ : WeightSpace p K) {j : ℕ}
    (hT : ‖κ.coord‖ < amiceRadius p j) :
    ∃ f : AnalyticStage p (padicUnitsDepth p + j) K,
      ‖f‖ = 1 ∧ ⇑(AnalyticStage.eval S f) = κ.zeroExtend :=
  ⟨κ.discExpansionOfCoord j hT, norm_discExpansionOfCoord_eq_one κ j hT,
    eval_discExpansionOfCoord S κ j hT⟩

/-- **Every weight into a complete ultrametric `ℚ_p`-algebra with multiplicative norm (such as a
complete normed field over `ℚ_p`) is analytic on the discs of `ℤ_p` at all large levels**, realized
by a coefficient vector of norm `1`. -/
theorem eventually_exists_eval_eq_zeroExtend (κ : WeightSpace p K) :
    ∀ᶠ h in atTop,
      ∃ f : AnalyticStage p h K, ‖f‖ = 1 ∧ ⇑(AnalyticStage.eval S f) = κ.zeroExtend := by
  have hlim := (tendsto_amiceRadius (p := p)).eventually (lt_mem_nhds (norm_coord_lt_one κ))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hlim
  refine eventually_atTop.mpr ⟨padicUnitsDepth p + J, fun h hh ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.le_add_right _ J).trans hh)
  exact exists_norm_eq_one_and_eval_eq_zeroExtend_of_norm_coord_lt S κ (hJ j (by omega))

/-- **Every weight into a complete ultrametric `ℚ_p`-algebra with multiplicative norm is analytic at
some level** with stage norm `1`. -/
theorem exists_eval_eq_zeroExtend (κ : WeightSpace p K) :
    ∃ h, ∃ f : AnalyticStage p h K, ‖f‖ = 1 ∧ ⇑(AnalyticStage.eval S f) = κ.zeroExtend :=
  (eventually_exists_eval_eq_zeroExtend S κ).exists

end NormMulClass

/-! ### Conductor bounds and algebraic weights over normed fields -/

section Field

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
  (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]

/-- **Conductor bound for locally algebraic weights on unit discs.** If `ψ` is trivial on
`1 + p ^ M ℤ_p` (`unitsPrincipal p M ≤ ψ.toMonoidHom.ker`), then for every `m ∈ ℤ` and every level
`h ≥ max M (padicUnitsDepth p)`, the zero-extension of `x ↦ x ^ m ψ(x)` is the evaluation of a
norm-`1` element of `AnalyticStage p h K`. This includes `ψ = 1` (`M = 0`) and
`h = padicUnitsDepth p`. -/
theorem exists_eval_eq_zeroExtend_inclusion_zpow_mul (m : ℤ) {ψ : WeightSpace p K} {M h : ℕ}
    (hψ : unitsPrincipal p M ≤ ψ.toMonoidHom.ker) (hh : max M (padicUnitsDepth p) ≤ h) :
    ∃ f : AnalyticStage p h K,
      ‖f‖ = 1 ∧ ⇑(AnalyticStage.eval S f) = (inclusion K ^ m * ψ).zeroExtend := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ((le_max_right M (padicUnitsDepth p)).trans hh)
  have hM : M ≤ padicUnitsDepth p + j := (le_max_left M (padicUnitsDepth p)).trans hh
  have hψ' : unitsPrincipal p (padicUnitsDepth p + j) ≤ ψ.toMonoidHom.ker :=
    (unitsPrincipal_antitone p hM).trans hψ
  exact exists_norm_eq_one_and_eval_eq_zeroExtend_of_norm_coord_lt S (inclusion K ^ m * ψ)
    (norm_coord_inclusion_zpow_mul_lt_amiceRadius m hψ')

/-- Every integer power `x ↦ x ^ m` (`m ∈ ℤ`), extended by zero off `ℤ_pˣ`, is analytic of stage
norm `1` at every level `h ≥ padicUnitsDepth p`. -/
theorem exists_eval_eq_zeroExtend_inclusion_zpow (m : ℤ) {h : ℕ}
    (hh : padicUnitsDepth p ≤ h) :
    ∃ f : AnalyticStage p h K,
      ‖f‖ = 1 ∧ ⇑(AnalyticStage.eval S f) = (inclusion K ^ m).zeroExtend := by
  have hker : unitsPrincipal p 0 ≤ (1 : WeightSpace p K).toMonoidHom.ker := by
    intro u _
    simp
  have hle : max 0 (padicUnitsDepth p) ≤ h := by simpa using hh
  rw [← mul_one (inclusion K ^ m)]
  exact exists_eval_eq_zeroExtend_inclusion_zpow_mul S m hker hle

/-- **Sharp analytic level of a weight of exact conductor `p ^ (k + j + 1)`.** Over a complete
normed field over `ℚ_p`, `κ.zeroExtend` is analytic at level `padicUnitsDepth p + i` if and only if
`j < i`. -/
theorem exists_eval_eq_zeroExtend_iff_lt_of_conductor (κ : WeightSpace p K) {i j : ℕ}
    (h : unitsPrincipal p (padicUnitsDepth p + j + 1) ≤ κ.toMonoidHom.ker)
    (h' : ¬unitsPrincipal p (padicUnitsDepth p + j) ≤ κ.toMonoidHom.ker) :
    (∃ f : AnalyticStage p (padicUnitsDepth p + i) K,
      ⇑(AnalyticStage.eval S f) = κ.zeroExtend) ↔ j < i := by
  rw [exists_eval_eq_zeroExtend_iff S, norm_coord_lt_amiceRadius_iff κ h h']

omit [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K] in
private theorem isSMulRegular_padicInt_prime [IsScalarTower ℤ_[p] ℚ_[p] K] :
    IsSMulRegular K (p : ℤ_[p]) := by
  intro x y hxy
  have hp0 : algebraMap ℤ_[p] K (p : ℤ_[p]) ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K]
    have hqp : algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) ≠ 0 := by
      rw [PadicInt.algebraMap_apply, PadicInt.coe_natCast]
      exact Nat.cast_ne_zero.mpr hp.out.ne_zero
    rw [← map_zero (algebraMap ℚ_[p] K)]
    exact (algebraMap ℚ_[p] K).injective.ne hqp
  dsimp only at hxy
  rw [Algebra.smul_def, Algebra.smul_def] at hxy
  exact mul_left_cancel₀ hp0 hxy

/-- **Binomial polynomial coefficients of nonnegative algebraic weights `x ↦ x ^ n` (`n : ℕ`).**
On every unit disc `a + p ^ (k + j) ℤ_p`, `discExpansionOfCoord` of `inclusion K ^ n` has the exact
binomial polynomial coefficients `(n choose m) a.val ^ (n - m) p ^ ((k + j) m)` (which vanish for
`n < m`). -/
theorem discExpansionOfCoord_inclusion_pow_apply [IsScalarTower ℤ_[p] ℚ_[p] K]
    (n j : ℕ) (hT : ‖(inclusion K ^ n).coord‖ < amiceRadius p j)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) (m : ℕ) :
    (inclusion K ^ n).discExpansionOfCoord j hT (a, m) =
      padicIntAlgebraMap p K
        ((n.choose m : ℤ_[p]) * (a.val : ℤ_[p]) ^ (n - m) *
          (p : ℤ_[p]) ^ ((padicUnitsDepth p + j) * m)) := by
  let h := padicUnitsDepth p + j
  let polyRow (b : ZMod (p ^ h)) : C₀(ℕ, K) :=
    if IsUnit b then
      ZeroAtInftyContinuousMap.mkOfDiscrete
        (fun l ↦ padicIntAlgebraMap p K
          ((n.choose l : ℤ_[p]) * (b.val : ℤ_[p]) ^ (n - l) * (p : ℤ_[p]) ^ (h * l)))
        (by
          rw [Nat.cofinite_eq_atTop]
          refine tendsto_atTop_of_eventually_const (i₀ := n + 1) fun l hl ↦ ?_
          simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_le hl)])
    else 0
  let P : AnalyticStage p h K :=
    (ZeroAtInftyContinuousMap.curryEquiv ℤ_[p] K).symm
      ((ZeroAtInftyContinuousMap.equivFunOnFintype ℤ_[p] C₀(ℕ, K)).symm polyRow)
  have heq : (inclusion K ^ n).discExpansionOfCoord j hT = P := by
    refine AnalyticStage.eval_injective ℤ_[p] isSMulRegular_padicInt_prime ?_
    ext x
    rw [eval_discExpansionOfCoord_eq_zeroExtend ℤ_[p]]
    obtain ⟨⟨b, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
    rw [PadicInt.discHomeomorph_apply, AnalyticStage.eval_natCast_val_add_mul]
    by_cases hb : IsUnit b
    · have hbu : IsUnit ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) :=
        (PadicInt.isUnit_natCast_val_add_mul_iff (padicUnitsDepth_add_ne_zero p j) b w).mpr hb
      rw [zeroExtend_apply_of_isUnit _ hbu, ContinuousMonoidHom.pow_apply, Units.val_pow_eq_pow_val,
        coe_inclusion_apply, IsUnit.unit_spec, ← map_pow]
      have hP (l : ℕ) : P (b, l) = padicIntAlgebraMap p K
          ((n.choose l : ℤ_[p]) * (b.val : ℤ_[p]) ^ (n - l) * (p : ℤ_[p]) ^ (h * l)) := by
        simp [P, polyRow, hb, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
      simp_rw [hP]
      rw [tsum_eq_sum (s := Finset.range (n + 1)) fun l hl ↦ by
        rw [Finset.mem_range, not_lt] at hl
        simp [Nat.choose_eq_zero_of_lt hl]]
      rw [add_comm (b.val : ℤ_[p]), add_pow, map_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      have hwl : algebraMap ℤ_[p] K (w ^ l) = padicIntAlgebraMap p K (w ^ l) := by
        rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, PadicInt.algebraMap_apply,
          padicIntAlgebraMap_apply]
      rw [Algebra.smul_def, hwl, ← map_mul]
      congr 1
      rw [mul_pow, ← pow_mul]
      ring
    · have hbnu : ¬IsUnit ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) := by
        rwa [PadicInt.isUnit_natCast_val_add_mul_iff (padicUnitsDepth_add_ne_zero p j)]
      have hP (l : ℕ) : P (b, l) = 0 := by simp [P, polyRow, hb]
      simp only [hP, smul_zero, tsum_zero, zeroExtend_apply_of_not_isUnit _ hbnu]
  rw [heq]
  simp only [P, polyRow, h, ZeroAtInftyContinuousMap.curryEquiv_symm_apply,
    ZeroAtInftyContinuousMap.coe_equivFunOnFintype_symm, ha, ↓reduceIte,
    ZeroAtInftyContinuousMap.coe_mkOfDiscrete]

end Field

end TauCeti.WeightSpace
