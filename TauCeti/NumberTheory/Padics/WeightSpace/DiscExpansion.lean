/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Exp.Log
public import TauCeti.NumberTheory.Padics.WeightSpace.AnalyticLevel
public import TauCeti.NumberTheory.Padics.WeightSpace.ZeroExtend
import TauCeti.Analysis.Normed.Ring.CompactMonoid
import TauCeti.NumberTheory.Padics.Distribution.Polynomial
import TauCeti.RingTheory.PowerSeries.Restricted
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
`u_a (1 + pʰ (u_a⁻¹ w))` (`w ∈ ℤ_p`). Since `h ≠ 0`, `1 + pʰ z` lies in the convergence range of
the `p`-adic logarithm, and its logarithmic coordinate in `1 + qℤ_p` is `pʲ · g(z)`, where
`g(X) = (pʰ)⁻¹ log(1 + pʰ X) ∈ ℤ_p⟦X⟧` is restricted at radius `1` (`TauCeti.deepLogSeries`). Hence
on the unit disc of `a`,

`κ.zeroExtend(a.val + pʰ w) = κ(u_a) · κ.principalChar(pʲ · g(u_a⁻¹ w))`.

Suppose `R` is a complete ultrametric Banach algebra over `ℤ_p` and `ℚ_p` (possibly noncommutative
and without assuming `‖1‖ = 1`), and suppose `‖κ(γ ^ (p ^ j)) - 1‖ < r_0`, where
`r_0 = TauCeti.amiceRadius p 0 = p ^ (-1 / (p - 1))`. Expanding the additive character
`s ↦ κ.principalChar(pʲ s)` at level `0` by Amice's theorem
(`TauCeti.AnalyticStage.addCharExpansion`), scaling on the left by `κ(u_a)`, and pulling back along
`g(u_a⁻¹ X)` via `PowerSeries.compNullSeq` yields an explicit coefficient vector
`κ.discExpansion j ht : AnalyticStage p (k + j) R` whose evaluation is `κ.zeroExtend`
(`TauCeti.WeightSpace.eval_discExpansion`). Its constant term on each unit disc `a` is `κ(u_a)`,
all its positive-degree (`m ≠ 0`) coefficients have norm at most
`‖κ(u_a)‖ * (‖κ(γ ^ (p ^ j)) - 1‖ / r_0)`, its Gauss norm on each unit disc is `‖κ(u_a)‖`, and its
stage norm equals `‖κ.zeroExtend‖`.

Conversely, when the norm on `K` is multiplicative with `‖1‖ = 1`, any expansion in
`AnalyticStage p (k + j) K` agreeing with `κ.zeroExtend` on the principal disc `1 + pʰℤ_p` pulls
back along the normalized deep exponential series `(pʰ)⁻¹ (exp(pʰ X) - 1) ∈ ℤ_p⟦X⟧`
(`TauCeti.deepExpSeries`) to a level-`0` expansion of `s ↦ κ.principalChar(pʲ s)`, forcing
`‖T_κ‖ < r_j` by `TauCeti.AnalyticStage.exists_eval_eq_addChar_iff`. This characterizes the
analytic levels `h ≥ k` of `κ.zeroExtend` (`TauCeti.WeightSpace.exists_eval_eq_zeroExtend_iff`,
`TauCeti.WeightSpace.exists_eval_eq_zeroExtend_iff_of_le`), implies that every weight over such an
algebra is analytic at all large levels
(`TauCeti.WeightSpace.eventually_exists_eval_eq_zeroExtend`), gives conductor bounds for locally
algebraic weights over commutative ultrametric Banach `ℚ_p`-algebras
(`TauCeti.WeightSpace.exists_eval_eq_zeroExtend_inclusion_zpow_mul`), and recovers the binomial
polynomial coefficients of nonnegative algebraic weights `x ↦ x ^ n` on unit discs
(`TauCeti.WeightSpace.discExpansion_inclusion_pow_apply`). At `p = 2` and `h = 1`, positive
algebraic weights already have polynomial expansions on `1 + 2ℤ_2`, whereas finite-order (locally
constant) characters nontrivial on `{±1}` require `h ≥ 2 = padicUnitsDepth 2`.

## Main definitions

* `TauCeti.WeightSpace.discExpansion`: expansion of `κ.zeroExtend` in
  `AnalyticStage p (padicUnitsDepth p + j) R` when `‖κ(γ ^ (p ^ j)) - 1‖ < amiceRadius p 0`.
* `TauCeti.WeightSpace.discExpansionOfCoord`: the same expansion constructed from
  `‖κ.coord‖ < amiceRadius p j`.

## Main results

* `TauCeti.WeightSpace.not_exists_eval_zero_eq_zeroExtend`: no weight is analytic at level `0` over
  a nontrivial `p`-torsion-free coefficient ring.
* `TauCeti.WeightSpace.tendsto_apply_padicUnitsGenerator_pow_sub_one_pow`,
  `TauCeti.WeightSpace.principalChar_pow_mul_eq_addChar`: the shifted principal character
  `s ↦ κ.principalChar (p ^ j * s)` as the binomial character of `κ(γ ^ (p ^ j)) - 1`.
* `TauCeti.WeightSpace.discExpansion_apply_of_isUnit`,
  `TauCeti.WeightSpace.discExpansion_apply_of_not_isUnit`,
  `TauCeti.WeightSpace.discExpansion_apply_zero`,
  `TauCeti.WeightSpace.eval_discExpansion`, `TauCeti.WeightSpace.norm_discExpansion`,
  `TauCeti.WeightSpace.isGreatest_norm_discExpansion_of_isUnit`: coefficient formulas, evaluation,
  global stage norm, and per-disc Gauss norm of `discExpansion` over any complete ultrametric
  Banach algebra.
* `TauCeti.WeightSpace.exists_eval_eq_zeroExtend_iff`,
  `TauCeti.WeightSpace.exists_eval_eq_zeroExtend_iff_of_le`: characterization of the analytic
  levels `h ≥ padicUnitsDepth p` of a weight for a multiplicative ultrametric norm.
* `TauCeti.WeightSpace.eventually_exists_eval_eq_zeroExtend`,
  `TauCeti.WeightSpace.exists_eval_eq_zeroExtend_inclusion_zpow_mul`,
  `TauCeti.WeightSpace.exists_eval_eq_zeroExtend_iff_lt`: eventual analyticity and conductor bounds
  for weights.
* `TauCeti.WeightSpace.discExpansion_inclusion_pow_apply`,
  `TauCeti.WeightSpace.discExpansionOfCoord_inclusion_pow_apply`: on unit discs, the expansion of
  `inclusion R ^ n` (`n : ℕ`) has the binomial polynomial coefficients of `(a.val + pʰ w) ^ n`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §§I.3–I.4.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3–4.
-/

public section

open Filter Topology NormedSpace
open scoped PowerSeries ZeroAtInfty

namespace TauCeti.WeightSpace

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Obstruction to analyticity at level `0` -/

section LevelZero

/-- **No weight is analytic on all of `ℤ_p` (level `0`).** Over a nontrivial complete ultrametric
ring `R` on which multiplication by `p` is injective, `κ.zeroExtend` vanishes on `pℤ_p` while
taking the value `1 ≠ 0` at `1`, so it is never the evaluation of an element of
`AnalyticStage p 0 R`. -/
theorem not_exists_eval_zero_eq_zeroExtend {R : Type*} [NormedRing R] [Nontrivial R]
    [Module ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [IsUltrametricDist R] [CompleteSpace R]
    (S : Type*) [Semiring S] [Module S R] [ContinuousConstSMul S R] [SMulCommClass ℤ_[p] S R]
    (hpR : IsSMulRegular R (p : ℤ_[p])) (κ : WeightSpace p R) :
    ¬∃ f : AnalyticStage p 0 R, AnalyticStage.eval S f = κ.zeroExtend := by
  rintro ⟨f, hf⟩
  have hf_eq (x : ℤ_[p]) : AnalyticStage.eval ℤ_[p] f x = κ.zeroExtend x := by
    rw [AnalyticStage.eval_apply, ← AnalyticStage.eval_apply S, hf]
  let f₁ := AnalyticStage.transition ℤ_[p] f
  let row₀ : C₀(ℕ, R) := AnalyticStage.rowsEquiv p ℤ_[p] 1 f₁ 0
  let g : AnalyticStage p 0 R := (AnalyticStage.levelZeroEquiv p ℤ_[p]).symm row₀
  have hg_eval : AnalyticStage.eval ℤ_[p] g = 0 := by
    ext w
    have hw : ¬IsUnit ((p : ℤ_[p]) * w) := PadicInt.not_isUnit_iff_dvd.mpr ⟨w, rfl⟩
    have hsum : (∑' m, w ^ m • row₀ m) =
        AnalyticStage.eval ℤ_[p] f₁ (((0 : ZMod (p ^ 1)).val : ℤ_[p]) + (p : ℤ_[p]) ^ 1 * w) := by
      rw [AnalyticStage.eval_natCast_val_add_mul]
      exact tsum_congr fun m ↦ by rw [AnalyticStage.rowsEquiv_apply]
    rw [AnalyticStage.eval_levelZeroEquiv_symm_apply, hsum, AnalyticStage.eval_transition,
      ZMod.val_zero, Nat.cast_zero, zero_add, pow_one, hf_eq, zeroExtend_apply_of_not_isUnit κ hw,
      ContinuousMap.zero_apply]
  have hg0 : g = 0 := AnalyticStage.eval_injective ℤ_[p] hpR (by rw [hg_eval, map_zero])
  have hf0 : f = 0 := by
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    ext ⟨a, m⟩
    rw [_root_.zero_apply]
    obtain rfl : a = 0 := Subsingleton.elim a 0
    have hcast : ((0 : ZMod (p ^ 0)).cast : ZMod (p ^ 1)) = 0 := by
      rw [ZMod.cast_eq_val, pow_zero]; simp
    have hm : (p : ℤ_[p]) ^ m • f (0, m) = 0 :=
      calc (p : ℤ_[p]) ^ m • f (0, m)
          = f₁ ((0 : ZMod (p ^ 0)).cast, m) :=
            (AnalyticStage.transition_apply_cast ℤ_[p] f 0 m).symm
        _ = g (0, m) := by
            dsimp only [g, row₀, f₁]
            rw [AnalyticStage.levelZeroEquiv_symm_apply, AnalyticStage.rowsEquiv_apply, hcast]
        _ = 0 := by rw [hg0, _root_.zero_apply]
    exact hpR.pow m (hm.trans (smul_zero _).symm)
  have h1 : κ.zeroExtend 1 = 0 := by rw [← hf_eq 1, hf0, map_zero, ContinuousMap.zero_apply]
  exact one_ne_zero (κ.zeroExtend_apply_one.symm.trans h1)

end LevelZero

/-! ### Logarithmic factorization and Banach-algebra expansion on unit discs -/

section DiscHelpers

/-- On the principal disc `1 + p ^ (k + j) ℤ_p`, `1 + p ^ (k + j) z` is the principal unit whose
logarithmic coordinate is `p ^ j · (deepLogSeries (padicUnitsDepth_add_ne_zero p j)).evalAt z`. -/
private theorem zeroExtend_one_add_pow_mul {R : Type*} [MonoidWithZero R] [TopologicalSpace R]
    (κ : WeightSpace p R) (j : ℕ) (z : ℤ_[p]) :
    κ.zeroExtend (1 + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * z) =
      κ.principalChar ((p : ℤ_[p]) ^ j *
        (deepLogSeries (p := p) (padicUnitsDepth_add_ne_zero p j)).evalAt z) := by
  let k := padicUnitsDepth p
  let h := k + j
  have hh := padicUnitsDepth_add_ne_zero p j
  let u₁ : unitsPrincipal p h := unitsPrincipalMk hh ⟨z, add_sub_cancel_left _ _⟩
  let u₀ : unitsPrincipal p k := ⟨u₁, unitsPrincipal_antitone p (Nat.le_add_right k j) u₁.property⟩
  have hu₀_val : ((u₀ : ℤ_[p]ˣ) : ℤ_[p]) = 1 + (p : ℤ_[p]) ^ h * z := coe_unitsPrincipalMk hh _
  have hlog : (unitsPrincipalLogEquiv p u₀).toAdd =
      (p : ℤ_[p]) ^ j * (deepLogSeries (p := p) hh).evalAt z := by
    apply PadicInt.ext
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
    rw [coe_unitsPrincipalLogEquiv_apply, hu₀_val, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast, coe_evalAt_deepLogSeries hh z]
    push_cast; dsimp only [h, k]
    rw [pow_add (p : ℚ_[p]) (padicUnitsDepth p) j]
    field_simp [pow_ne_zero (padicUnitsDepth p) hp0, pow_ne_zero j hp0]
  have hu₀_symm : (u₀ : ℤ_[p]ˣ) = ((unitsPrincipalLogEquiv p).symm
      (.ofAdd ((p : ℤ_[p]) ^ j * (deepLogSeries (p := p) hh).evalAt z)) : ℤ_[p]ˣ) := by
    congr 1; rw [← hlog, ofAdd_toAdd, ContinuousMulEquiv.symm_apply_apply]
  rw [← hu₀_val, zeroExtend_coe_unit, hu₀_symm, principalChar_apply]

/-- On any unit disc `a + p ^ (k + j) ℤ_p` (`IsUnit a`), `κ.zeroExtend (a.val + p ^ (k + j) w)`
factors as `κ(u_a)` times `κ.principalChar` at `p ^ j · (deepLogSeries hh).evalAt (u_a⁻¹ w)`. -/
private theorem zeroExtend_natCast_val_add_mul_of_isUnit {R : Type*} [MonoidWithZero R]
    [TopologicalSpace R] (κ : WeightSpace p R) (j : ℕ) {a : ZMod (p ^ (padicUnitsDepth p + j))}
    (ha : IsUnit a) (w : ℤ_[p]) :
    let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    κ.zeroExtend ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w) =
      (κ u : R) * κ.principalChar ((p : ℤ_[p]) ^ j *
        (deepLogSeries (p := p) (padicUnitsDepth_add_ne_zero p j)).evalAt
          ((↑u⁻¹ : ℤ_[p]) * w)) := by
  intro u
  have hfac : (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w =
      (u : ℤ_[p]) * (1 + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * ((↑u⁻¹ : ℤ_[p]) * w)) :=
    calc (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w
        = (u : ℤ_[p]) + ((u : ℤ_[p]) * ↑u⁻¹) * ((p : ℤ_[p]) ^ (padicUnitsDepth p + j) * w) := by
          rw [u.mul_inv, one_mul, IsUnit.unit_spec]
      _ = _ := by ring
  rw [hfac, zeroExtend_apply_mul, zeroExtend_coe_unit, zeroExtend_one_add_pow_mul]

end DiscHelpers

section DiscExpansion

section ShiftedPrincipalChar

variable {M : Type*} [Monoid M] [TopologicalSpace M] (κ : WeightSpace p M) (j : ℕ)

private noncomputable def shiftedPrincipalChar : AddChar ℤ_[p] M :=
  κ.principalChar.compAddMonoidHom (AddMonoidHom.mulLeft ((p : ℤ_[p]) ^ j))

private theorem continuous_shiftedPrincipalChar : Continuous (shiftedPrincipalChar κ j) :=
  (κ.continuous_principalChar.comp
    ((continuous_const (y := (p : ℤ_[p]) ^ j)).mul continuous_id)).congr fun _ ↦ by
      simp [shiftedPrincipalChar]

private theorem shiftedPrincipalChar_one :
    shiftedPrincipalChar κ j 1 = κ (padicUnitsGenerator p ^ p ^ j) := by
  rw [shiftedPrincipalChar, AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_mulLeft, mul_one,
    ← Nat.cast_pow, ← nsmul_one, AddChar.map_nsmul_eq_pow, principalChar_one, map_pow,
    Units.val_pow_eq_pow_val]

end ShiftedPrincipalChar

variable {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [Module ℚ_[p] R]
  [IsBoundedSMul ℚ_[p] R] [IsUltrametricDist R] [CompleteSpace R]

omit [Module ℚ_[p] R] [IsBoundedSMul ℚ_[p] R] [CompleteSpace R] in
/-- For any `j : ℕ`, `κ(γ ^ (p ^ j)) - 1` is topologically nilpotent. -/
theorem tendsto_apply_padicUnitsGenerator_pow_sub_one_pow (κ : WeightSpace p R) (j : ℕ) :
    Tendsto (fun n : ℕ ↦ ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1) ^ n) atTop (𝓝 0) := by
  simpa only [shiftedPrincipalChar_one] using
    (shiftedPrincipalChar κ j).tendsto_eval_one_sub_pow (continuous_shiftedPrincipalChar κ j)

omit [Module ℚ_[p] R] [IsBoundedSMul ℚ_[p] R] in
/-- Over a complete ultrametric `ℤ_p`-algebra, the shifted principal character
`s ↦ κ.principalChar (p ^ j * s)` is the Mahler binomial character with parameter
`κ(γ ^ (p ^ j)) - 1`. -/
theorem principalChar_pow_mul_eq_addChar (κ : WeightSpace p R) (j : ℕ) (s : ℤ_[p]) :
    κ.principalChar ((p : ℤ_[p]) ^ j * s) =
      PadicInt.addChar_of_value_at_one ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1)
        (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j) s := by
  have heq : shiftedPrincipalChar κ j =
      PadicInt.addChar_of_value_at_one ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1)
        (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j) :=
    PadicInt.eq_addChar_of_value_at_one _ (continuous_shiftedPrincipalChar κ j)
      (by rw [shiftedPrincipalChar_one, add_sub_cancel])
  simpa [shiftedPrincipalChar] using DFunLike.congr_fun heq s

private theorem isRestricted_rescale_deepLogSeries (j : ℕ) (u : ℤ_[p]ˣ) :
    (PowerSeries.rescale (u : ℤ_[p])
      (deepLogSeries (p := p) (padicUnitsDepth_add_ne_zero p j))).IsRestricted 1 := by
  refine PowerSeries.IsRestricted.rescale ?_
  rw [PadicInt.isUnit_iff.mp u.isUnit, one_mul]; exact isRestricted_deepLogSeries _

private noncomputable def discExpansionScaledRow (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) (u : ℤ_[p]ˣ) :
    C₀(ℕ, R) :=
  (κ u : R) • AnalyticStage.levelZeroEquiv p ℤ_[p]
    (AnalyticStage.addCharExpansion p 0 ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1) ht)

@[simp] private theorem discExpansionScaledRow_apply (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) (u : ℤ_[p]ˣ) (n : ℕ) :
    discExpansionScaledRow κ j ht u n = (κ u : R) *
      AnalyticStage.addCharExpansion p 0 ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1) ht (0, n) :=
  by simp [discExpansionScaledRow]

/-- **Expansion of a weight on the discs of `ℤ_p` at level `padicUnitsDepth p + j`.** Given a
weight `κ : WeightSpace p R` into a complete ultrametric Banach algebra `R` over `ℤ_p` and `ℚ_p`
with `‖κ(γ ^ (p ^ j)) - 1‖ < amiceRadius p 0`, `κ.discExpansion j ht` vanishes on non-unit discs
and pulls back the level-`0` Amice expansion of `s ↦ κ.principalChar (p ^ j * s)` (scaled on the
left by `κ(u_a)`) along `w ↦ (p ^ h)⁻¹ log(1 + p ^ h u_a⁻¹ w)` on each unit disc `a + p ^ h ℤ_p`. -/
noncomputable def discExpansion (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) :
    AnalyticStage p (padicUnitsDepth p + j) R :=
  (AnalyticStage.rowsEquiv p ℤ_[p] (padicUnitsDepth p + j)).symm fun a ↦
    if ha : IsUnit a then
      let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
      PowerSeries.compNullSeq ℤ_[p] (isRestricted_rescale_deepLogSeries j u⁻¹)
        (fun _ ↦ PadicInt.norm_le_one _) (discExpansionScaledRow κ j ht u)
    else 0

private theorem discExpansion_apply_of_isUnit_eq_compNullSeq (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) (m : ℕ) :
    let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    κ.discExpansion j ht (a, m) =
      PowerSeries.compNullSeq ℤ_[p] (isRestricted_rescale_deepLogSeries j u⁻¹)
        (fun _ ↦ PadicInt.norm_le_one _) (discExpansionScaledRow κ j ht u) m := by
  simp [discExpansion, ha]

/-- **Expansion of a weight from its coordinate bound.** For `‖κ.coord‖ < amiceRadius p j`, the
expansion of `κ.zeroExtend` in `AnalyticStage p (padicUnitsDepth p + j) R` obtained from
`WeightSpace.discExpansion`. -/
noncomputable def discExpansionOfCoord (κ : WeightSpace p R) (j : ℕ)
    (hT : ‖κ.coord‖ < amiceRadius p j) : AnalyticStage p (padicUnitsDepth p + j) R :=
  κ.discExpansion j (by
    rw [apply_padicUnitsGenerator_pow]; exact norm_one_add_pow_sub_one_lt_of_norm_lt hT)

@[simp] theorem discExpansionOfCoord_eq_discExpansion (κ : WeightSpace p R) (j : ℕ)
    (hT : ‖κ.coord‖ < amiceRadius p j) :
    κ.discExpansionOfCoord j hT = κ.discExpansion j (by
      rw [apply_padicUnitsGenerator_pow]; exact norm_one_add_pow_sub_one_lt_of_norm_lt hT) := by rfl

/-- On every unit residue class `a`, the `m`-th coefficient of `κ.discExpansion` is the pullback
along `rescale u_a⁻¹ (deepLogSeries (padicUnitsDepth_add_ne_zero p j))` of
`n ↦ κ(u_a) * addCharExpansion p 0 t ht (0, n)`. -/
theorem discExpansion_apply_of_isUnit (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) (m : ℕ) :
    let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    κ.discExpansion j ht (a, m) =
      ∑' n, PowerSeries.coeff m (PowerSeries.rescale (↑u⁻¹ : ℤ_[p])
          (deepLogSeries (p := p) (padicUnitsDepth_add_ne_zero p j)) ^ n) •
        ((κ u : R) * AnalyticStage.addCharExpansion p 0
          ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1) ht (0, n)) := by
  intro u
  rw [discExpansion_apply_of_isUnit_eq_compNullSeq κ j ht ha m,
    PowerSeries.compNullSeq_apply]
  simp [u]

/-- On every non-unit residue class `a`, all coefficients of `κ.discExpansion` vanish. -/
@[simp] theorem discExpansion_apply_of_not_isUnit (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : ¬IsUnit a) (m : ℕ) :
    κ.discExpansion j ht (a, m) = 0 := by simp [discExpansion, ha]

/-- On every unit residue class `a`, the constant coefficient of `κ.discExpansion` is the value of
`κ` at the natural unit representative `a.val` of `a`. -/
theorem discExpansion_apply_zero_of_isUnit (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) :
    κ.discExpansion j ht (a, 0) =
      κ ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit := by
  have hg0 : ∀ z : ℤ_[p], PowerSeries.constantCoeff
      (PowerSeries.rescale z (deepLogSeries (p := p) (padicUnitsDepth_add_ne_zero p j))) = 0 :=
    fun _ ↦ by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero,
        one_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_deepLogSeries]
  have hval0 : (0 : ZMod (p ^ 0)).val = 0 := by rw [pow_zero]; simp
  rw [discExpansion_apply_of_isUnit_eq_compNullSeq κ j ht ha 0,
    PowerSeries.compNullSeq_apply_zero_of_constantCoeff_eq_zero ℤ_[p] _ _ (hg0 _),
    discExpansionScaledRow_apply, AnalyticStage.addCharExpansion_apply_zero, hval0, pow_zero,
    mul_one]

/-- On every residue class `a`, the constant coefficient of `κ.discExpansion` is
`κ.zeroExtend a.val` (equal to `κ(u_a)` on unit discs and `0` on non-unit discs). -/
@[simp] theorem discExpansion_apply_zero (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    (a : ZMod (p ^ (padicUnitsDepth p + j))) :
    κ.discExpansion j ht (a, 0) = κ.zeroExtend (a.val : ℤ_[p]) := by
  by_cases ha : IsUnit a
  · rw [discExpansion_apply_zero_of_isUnit κ j ht ha, zeroExtend_apply_of_isUnit κ
      ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha)]
  · have hanu : ¬IsUnit (a.val : ℤ_[p]) := by
      rwa [PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j)]
    rw [discExpansion_apply_of_not_isUnit κ j ht ha 0, zeroExtend_apply_of_not_isUnit κ hanu]

/-- **Evaluation of `discExpansion`.** Over any complete ultrametric Banach algebra `R` over `ℤ_p`
and `ℚ_p`, `κ.discExpansion j ht` evaluates to `κ.zeroExtend` on `ℤ_p`. -/
@[simp] theorem eval_discExpansion (S : Type*) [Semiring S] [Module S R] [ContinuousConstSMul S R]
    [SMulCommClass ℤ_[p] S R] (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) :
    AnalyticStage.eval S (κ.discExpansion j ht) = κ.zeroExtend := by
  ext x
  let h := padicUnitsDepth p + j
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  rw [PadicInt.discHomeomorph_apply, AnalyticStage.eval_natCast_val_add_mul]
  by_cases ha : IsUnit a
  · let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    let c₀ := AnalyticStage.addCharExpansion p 0 ((κ (padicUnitsGenerator p ^ p ^ j) : R) - 1) ht
    simp_rw [discExpansion_apply_of_isUnit_eq_compNullSeq κ j ht ha]
    rw [PowerSeries.tsum_pow_smul_compNullSeq ℤ_[p] _ _ _ (PadicInt.norm_le_one w)]
    let z := (PowerSeries.rescale (↑u⁻¹ : ℤ_[p])
      (deepLogSeries (p := p) (padicUnitsDepth_add_ne_zero p j))).evalAt w
    have h0z : ((0 : ZMod (p ^ 0)).val : ℤ_[p]) + (p : ℤ_[p]) ^ 0 * z = z := by rw [pow_zero]; simp
    have hsum_c₀ : HasSum (fun n ↦ z ^ n • c₀ (0, n)) (AnalyticStage.eval ℤ_[p] c₀ z) := by
      simpa only [h0z] using AnalyticStage.hasSum_eval_natCast_val_add_mul ℤ_[p] c₀ 0 z
    have hmul_sum : (∑' n, z ^ n • discExpansionScaledRow κ j ht u n) =
        (κ u : R) * AnalyticStage.eval ℤ_[p] c₀ z :=
      ((hsum_c₀.mul_left (κ u : R)).congr_fun fun n ↦ by
        rw [discExpansionScaledRow_apply, mul_smul_comm]).tsum_eq
    rw [hmul_sum, AnalyticStage.eval_addCharExpansion ℤ_[p] ht
      (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j),
      ← principalChar_pow_mul_eq_addChar, zeroExtend_natCast_val_add_mul_of_isUnit κ j ha w]
    simp only [z, PowerSeries.evalAt_rescale, smul_eq_mul, u]
  · have hnu : ¬IsUnit ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) := by
      rwa [PadicInt.isUnit_natCast_val_add_mul_iff (padicUnitsDepth_add_ne_zero p j)]
    simp only [discExpansion_apply_of_not_isUnit κ j ht ha, smul_zero, tsum_zero]
    exact (zeroExtend_apply_of_not_isUnit κ hnu).symm

/-- **Higher-degree coefficient bound on unit discs.** For `m ≠ 0` on a unit disc `a`,
`‖κ.discExpansion j ht (a, m)‖ ≤ ‖κ(u_a)‖ * (‖κ(γ ^ (p ^ j)) - 1‖ / r_0)`. -/
theorem norm_discExpansion_apply_le_of_ne_zero (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) {m : ℕ} (hm : m ≠ 0) :
    let u := ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    ‖κ.discExpansion j ht (a, m)‖ ≤
      ‖(κ u : R)‖ * (‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ / amiceRadius p 0) := by
  intro u
  have hB0 : 0 ≤ ‖(κ u : R)‖ *
      (‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ / amiceRadius p 0) :=
    mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) (amiceRadius_pos 0).le)
  rw [discExpansion_apply_of_isUnit_eq_compNullSeq κ j ht ha m]
  refine PowerSeries.norm_compNullSeq_apply_le_of_ne_zero ℤ_[p] _ _ hB0 (fun n hn ↦ ?_) hm
  rw [discExpansionScaledRow_apply]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
    (AnalyticStage.norm_addCharExpansion_apply_le_of_ne_zero ht 0 hn) (norm_nonneg _))

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
  rintro _ ⟨m, rfl⟩; dsimp only
  rcases eq_or_ne m 0 with rfl | hm
  · rw [discExpansion_apply_zero_of_isUnit κ j ht ha]
  · exact (norm_discExpansion_apply_le_of_ne_zero κ j ht ha hm).trans
      (mul_le_of_le_one_right (norm_nonneg _) ((div_le_one (amiceRadius_pos 0)).mpr ht.le))

/-- **Exact stage norm of `discExpansion`.** Over any complete ultrametric Banach algebra `R`, the
analytic-stage norm of `κ.discExpansion j ht` equals the supremum norm `‖κ.zeroExtend‖`. -/
@[simp] theorem norm_discExpansion (κ : WeightSpace p R) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0) :
    ‖κ.discExpansion j ht‖ = ‖κ.zeroExtend‖ := by
  refine le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg _)).mpr fun ⟨a, m⟩ ↦ ?_) ?_
  · by_cases ha : IsUnit a
    · exact ((isGreatest_norm_discExpansion_of_isUnit κ j ht ha).2 ⟨m, rfl⟩).trans <| by
        simpa only [zeroExtend_coe_unit] using ContinuousMap.norm_coe_le_norm κ.zeroExtend
          ((PadicInt.isUnit_natCast_val_iff (padicUnitsDepth_add_ne_zero p j) a).mpr ha).unit
    · simp [ha]
  · rw [← eval_discExpansion ℤ_[p] κ j ht]; exact AnalyticStage.norm_eval_le ℤ_[p] _

end DiscExpansion

/-! ### Converse and characterization of analytic levels for multiplicative norms -/

section NormMulClass

variable {K : Type*} [NormedRing K] [NormMulClass K] [NormOneClass K]
  [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [Module ℚ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

section BoundedSMul

variable [IsBoundedSMul ℚ_[p] K]

/-- For a multiplicative norm with `‖1‖ = 1`, `κ.discExpansion j ht` has norm `1`. -/
theorem norm_discExpansion_eq_one (κ : WeightSpace p K) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : K) - 1‖ < amiceRadius p 0) :
    ‖κ.discExpansion j ht‖ = 1 := by
  rw [norm_discExpansion, norm_zeroExtend_eq_one]

/-- For a multiplicative norm with `‖1‖ = 1`, `κ.discExpansion j ht` has Gauss norm `1` on every
unit disc `a`. -/
theorem isGreatest_norm_discExpansion_one_of_isUnit (κ : WeightSpace p K) (j : ℕ)
    (ht : ‖(κ (padicUnitsGenerator p ^ p ^ j) : K) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) :
    IsGreatest (Set.range fun m ↦ ‖κ.discExpansion j ht (a, m)‖) 1 := by
  simpa only [κ.norm_apply_eq_one_of_compactSpace] using
    isGreatest_norm_discExpansion_of_isUnit κ j ht ha

variable (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]

/-- Whenever `‖κ.coord‖ < amiceRadius p j` over a complete ultrametric `ℚ_p`-algebra with
multiplicative norm, `κ.zeroExtend` is the evaluation of a norm-`1` element of
`AnalyticStage p (padicUnitsDepth p + j) K`. -/
theorem exists_norm_eq_one_and_eval_eq_zeroExtend_of_norm_coord_lt (κ : WeightSpace p K) {j : ℕ}
    (hT : ‖κ.coord‖ < amiceRadius p j) :
    ∃ f : AnalyticStage p (padicUnitsDepth p + j) K,
      ‖f‖ = 1 ∧ AnalyticStage.eval S f = κ.zeroExtend :=
  ⟨κ.discExpansionOfCoord j hT, by simp, by simp⟩

/-- **Every weight into a complete ultrametric `ℚ_p`-algebra with multiplicative norm (such as a
complete normed field over `ℚ_p`) is analytic on the discs of `ℤ_p` at all large levels**, realized
by a coefficient vector of norm `1`. -/
theorem eventually_exists_eval_eq_zeroExtend (κ : WeightSpace p K) :
    ∀ᶠ h in atTop, ∃ f : AnalyticStage p h K, ‖f‖ = 1 ∧ AnalyticStage.eval S f = κ.zeroExtend := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp <|
    (tendsto_amiceRadius (p := p)).eventually (lt_mem_nhds (norm_coord_lt_one κ))
  refine eventually_atTop.mpr ⟨padicUnitsDepth p + J, fun h hh ↦ ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ((Nat.le_add_right _ J).trans hh)
  exact exists_norm_eq_one_and_eval_eq_zeroExtend_of_norm_coord_lt S κ (hJ j (by omega))

/-- **Every weight into a complete ultrametric `ℚ_p`-algebra with multiplicative norm is analytic at
some level** with stage norm `1`. -/
theorem exists_eval_eq_zeroExtend (κ : WeightSpace p K) :
    ∃ h, ∃ f : AnalyticStage p h K, ‖f‖ = 1 ∧ AnalyticStage.eval S f = κ.zeroExtend :=
  (eventually_exists_eval_eq_zeroExtend S κ).exists

end BoundedSMul

section NormSMulClass

variable [NormSMulClass ℚ_[p] K]
  (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]

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
    rw [ZMod.val_one'' (Nat.one_lt_pow (padicUnitsDepth_add_ne_zero p j) hp.out.one_lt).ne',
      Nat.cast_one]
  let row₁ : C₀(ℕ, K) := AnalyticStage.rowsEquiv p ℤ_[p] h f 1
  let c₀ : C₀(ℕ, K) := PowerSeries.compNullSeq ℤ_[p]
    (isRestricted_deepExpSeries hh) (fun _ ↦ PadicInt.norm_le_one _) row₁
  let f₀ : AnalyticStage p 0 K := (AnalyticStage.levelZeroEquiv p ℤ_[p]).symm c₀
  have hf₀ : ⇑(AnalyticStage.eval ℤ_[p] f₀) =
      PadicInt.addChar_of_value_at_one ((κ (padicUnitsGenerator p ^ p ^ j) : K) - 1)
        (tendsto_apply_padicUnitsGenerator_pow_sub_one_pow κ j) := by
    ext s
    rw [AnalyticStage.eval_levelZeroEquiv_symm_apply,
      PowerSeries.tsum_pow_smul_compNullSeq ℤ_[p] _ _ _ (PadicInt.norm_le_one s)]
    let w := (deepExpSeries hh).evalAt s
    have hev₁ : (∑' n, w ^ n • row₁ n) = AnalyticStage.eval S f (1 + (p : ℤ_[p]) ^ h * w) := by
      rw [← h1val, AnalyticStage.eval_natCast_val_add_mul]
      exact tsum_congr fun n ↦ by rw [AnalyticStage.rowsEquiv_apply]
    have hexp_unit : 1 + (p : ℤ_[p]) ^ h * w =
        (((unitsPrincipalLogEquiv p).symm (.ofAdd ((p : ℤ_[p]) ^ j * s)) : ℤ_[p]ˣ) : ℤ_[p]) := by
      apply PadicInt.ext
      rw [coe_unitsPrincipalLogEquiv_symm_apply, toAdd_ofAdd]; push_cast
      rw [← mul_assoc, ← pow_add]; exact one_add_pow_mul_coe_evalAt_deepExpSeries hh s
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
      AnalyticStage.eval S f = κ.zeroExtend) ↔ ‖κ.coord‖ < amiceRadius p j :=
  ⟨fun ⟨_, hf⟩ ↦ norm_coord_lt_amiceRadius_of_eval_one_add_pow_mul S κ
      (fun _ ↦ DFunLike.congr_fun hf _),
    fun hT ↦ ⟨κ.discExpansionOfCoord j hT, by simp⟩⟩

/-- **Characterization in terms of `κ(γ ^ (p ^ j)) - 1`.** For complete coefficients with a
multiplicative ultrametric norm, `κ.zeroExtend` lies in the image of
`AnalyticStage p (padicUnitsDepth p + j) K` if and only if
`‖κ(γ ^ (p ^ j)) - 1‖ < amiceRadius p 0`. -/
theorem exists_eval_eq_zeroExtend_iff_norm_sub_one_lt (κ : WeightSpace p K) {j : ℕ} :
    (∃ f : AnalyticStage p (padicUnitsDepth p + j) K, AnalyticStage.eval S f = κ.zeroExtend) ↔
      ‖(κ (padicUnitsGenerator p ^ p ^ j) : K) - 1‖ < amiceRadius p 0 := by
  rw [exists_eval_eq_zeroExtend_iff S, norm_apply_padicUnitsGenerator_pow_sub_one_lt_iff]

/-- **Characterization at any level `h ≥ padicUnitsDepth p`.** For `padicUnitsDepth p ≤ h`,
`κ.zeroExtend` lies in the image of `AnalyticStage p h K` if and only if
`‖κ.coord‖ < amiceRadius p (h - padicUnitsDepth p)`. -/
theorem exists_eval_eq_zeroExtend_iff_of_le (κ : WeightSpace p K) {h : ℕ}
    (hh : padicUnitsDepth p ≤ h) :
    (∃ f : AnalyticStage p h K, AnalyticStage.eval S f = κ.zeroExtend) ↔
      ‖κ.coord‖ < amiceRadius p (h - padicUnitsDepth p) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hh
  simpa only [Nat.add_sub_cancel_left] using exists_eval_eq_zeroExtend_iff S κ (j := j)

end NormSMulClass

end NormMulClass

/-! ### Conductor bounds and algebraic weights over Banach `ℚ_p`-algebras -/

section LocallyAlgebraic

/-- Every integer power `x ↦ x ^ m` (`m ∈ ℤ`) into a complete ultrametric commutative Banach
`ℚ_p`-algebra with `‖1‖ = 1` (without requiring a multiplicative norm), extended by zero off
`ℤ_pˣ`, is analytic of stage norm `1` at every level `h ≥ padicUnitsDepth p`. -/
theorem exists_eval_eq_zeroExtend_inclusion_zpow {K : Type*} [NormedCommRing K] [NormOneClass K]
    [NormedAlgebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K]
    [CompleteSpace K] (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K]
    [SMulCommClass ℤ_[p] S K] (m : ℤ) {h : ℕ} (hh : padicUnitsDepth p ≤ h) :
    ∃ f : AnalyticStage p h K,
      ‖f‖ = 1 ∧ AnalyticStage.eval S f = (inclusion (p := p) K ^ m).zeroExtend := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hh
  have ht := norm_apply_inclusion_zpow_padicUnitsGenerator_pow_sub_one_lt (p := p) (K := K) m j
  exact ⟨(inclusion (p := p) K ^ m).discExpansion j ht, by simp, by simp⟩

/-- **Conductor bound for locally algebraic weights on unit discs.** Over any complete ultrametric
commutative Banach `ℚ_p`-algebra with multiplicative norm and `‖1‖ = 1`, if `ψ` is trivial on
`1 + p ^ M ℤ_p` (`unitsPrincipal p M ≤ ψ.toMonoidHom.ker`), then for every `m ∈ ℤ` and every level
`h ≥ max M (padicUnitsDepth p)`, the zero-extension of `x ↦ x ^ m ψ(x)` is the evaluation of a
norm-`1` element of `AnalyticStage p h K`. This includes `ψ = 1` (`M = 0`) and
`h = padicUnitsDepth p`. -/
theorem exists_eval_eq_zeroExtend_inclusion_zpow_mul {K : Type*} [NormedCommRing K]
    [NormMulClass K] [NormOneClass K] [NormedAlgebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]
    (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]
    (m : ℤ) {ψ : WeightSpace p K} {M h : ℕ}
    (hψ : unitsPrincipal p M ≤ ψ.toMonoidHom.ker) (hh : max M (padicUnitsDepth p) ≤ h) :
    ∃ f : AnalyticStage p h K,
      ‖f‖ = 1 ∧ AnalyticStage.eval S f = (inclusion (p := p) K ^ m * ψ).zeroExtend := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ((le_max_right M (padicUnitsDepth p)).trans hh)
  have hψ' : unitsPrincipal p (padicUnitsDepth p + j) ≤ ψ.toMonoidHom.ker :=
    (unitsPrincipal_antitone p ((le_max_left M (padicUnitsDepth p)).trans hh)).trans hψ
  have ht := norm_apply_inclusion_zpow_mul_padicUnitsGenerator_pow_sub_one_lt m hψ'
  exact ⟨(inclusion (p := p) K ^ m * ψ).discExpansion j ht,
    norm_discExpansion_eq_one _ j ht, by simp⟩

section BinomialPoly

variable {R : Type*} [NormedCommRing R] [NormedAlgebra ℚ_[p] R] [Algebra ℤ_[p] R]
  [IsBoundedSMul ℤ_[p] R]

private noncomputable def binomialPolyStage (n h : ℕ) :
    AnalyticStage.polynomialSubmodule (p := p) (h := h) (E := R) ℤ_[p] n :=
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  (AnalyticStage.polynomialEquiv (p := p) (h := h) (E := R) ℤ_[p] n).symm fun i ↦
    if IsUnit i.1 then padicIntAlgebraMap p R
      ((n.choose i.2 : ℤ_[p]) * (i.1.val : ℤ_[p]) ^ (n - i.2) * (p : ℤ_[p]) ^ (h * i.2))
    else 0

private theorem binomialPolyStage_apply_of_isUnit (n h : ℕ) {a : ZMod (p ^ h)} (ha : IsUnit a)
    (m : ℕ) :
    (binomialPolyStage (p := p) (R := R) n h).val (a, m) = padicIntAlgebraMap p R
      ((n.choose m : ℤ_[p]) * (a.val : ℤ_[p]) ^ (n - m) * (p : ℤ_[p]) ^ (h * m)) := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  rw [binomialPolyStage, AnalyticStage.polynomialEquiv_symm_apply]
  split_ifs with hm
  · simp
  · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hm)]

private theorem binomialPolyStage_apply_of_not_isUnit (n h : ℕ) {a : ZMod (p ^ h)} (ha : ¬IsUnit a)
    (m : ℕ) : (binomialPolyStage (p := p) (R := R) n h).val (a, m) = 0 := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  rw [binomialPolyStage, AnalyticStage.polynomialEquiv_symm_apply]; split_ifs <;> simp

variable [IsUltrametricDist R] [CompleteSpace R]

private theorem eval_binomialPolyStage (n : ℕ) {h : ℕ} (hh : h ≠ 0) :
    AnalyticStage.eval ℤ_[p] (binomialPolyStage (p := p) (R := R) n h).val =
      (inclusion (p := p) R ^ n).zeroExtend := by
  ext x
  obtain ⟨⟨b, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  rw [PadicInt.discHomeomorph_apply, AnalyticStage.eval_polynomial_natCast_val_add_mul]
  by_cases hb : IsUnit b
  · have hbu : IsUnit ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) :=
      (PadicInt.isUnit_natCast_val_add_mul_iff hh b w).mpr hb
    rw [zeroExtend_pow_apply_of_isUnit _ n hbu, zeroExtend_inclusion_apply_of_isUnit hbu,
      ← map_pow, add_comm (b.val : ℤ_[p]), add_pow, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [binomialPolyStage_apply_of_isUnit n h hb l, Algebra.smul_def,
      algebraMap_padicInt_eq_padicIntAlgebraMap, ← map_mul]
    congr 1; rw [mul_pow, ← pow_mul]; ring
  · have hbnu : ¬IsUnit ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) := by
      rwa [PadicInt.isUnit_natCast_val_add_mul_iff hh]
    simp only [binomialPolyStage_apply_of_not_isUnit n h hb, smul_zero, Finset.sum_const_zero]
    exact (zeroExtend_apply_of_not_isUnit _ hbnu).symm

/-- **Binomial polynomial coefficients of nonnegative algebraic weights `x ↦ x ^ n` (`n : ℕ`) over
Banach `ℚ_p`-algebras.** On every unit disc `a + p ^ (k + j) ℤ_p`, `discExpansion` of
`inclusion R ^ n` has the exact binomial polynomial coefficients
`(n choose m) a.val ^ (n - m) p ^ ((k + j) m)` (which vanish for `n < m`). -/
theorem discExpansion_inclusion_pow_apply (n j : ℕ)
    (ht :
      ‖((inclusion (p := p) R ^ n) (padicUnitsGenerator p ^ p ^ j) : R) - 1‖ < amiceRadius p 0)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) (m : ℕ) :
    (inclusion (p := p) R ^ n).discExpansion j ht (a, m) =
      padicIntAlgebraMap p R ((n.choose m : ℤ_[p]) * (a.val : ℤ_[p]) ^ (n - m) *
        (p : ℤ_[p]) ^ ((padicUnitsDepth p + j) * m)) := by
  have heq : (inclusion (p := p) R ^ n).discExpansion j ht =
      (binomialPolyStage (p := p) (R := R) n (padicUnitsDepth p + j)).val :=
    AnalyticStage.eval_injective ℤ_[p] isSMulRegular_padicInt_prime <| by
      rw [eval_discExpansion, eval_binomialPolyStage n (padicUnitsDepth_add_ne_zero p j)]
  rw [heq, binomialPolyStage_apply_of_isUnit n _ ha m]

end BinomialPoly

end LocallyAlgebraic

/-! ### Exact-conductor criterion and field specialization -/

section Field

variable {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Sharp analytic level of a weight of exact conductor `p ^ (k + j + 1)`.** Over a complete
normed field over `ℚ_p`, `κ.zeroExtend` is analytic at level `padicUnitsDepth p + i` if and only if
`j < i`. -/
theorem exists_eval_eq_zeroExtend_iff_lt
    (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]
    (κ : WeightSpace p K) {i j : ℕ}
    (h : unitsPrincipal p (padicUnitsDepth p + j + 1) ≤ κ.toMonoidHom.ker)
    (h' : ¬unitsPrincipal p (padicUnitsDepth p + j) ≤ κ.toMonoidHom.ker) :
    (∃ f : AnalyticStage p (padicUnitsDepth p + i) K,
      AnalyticStage.eval S f = κ.zeroExtend) ↔ j < i := by
  rw [exists_eval_eq_zeroExtend_iff S, norm_coord_lt_amiceRadius_iff κ h h']

/-- Specialization of `discExpansion_inclusion_pow_apply` to `discExpansionOfCoord` over a normed
field over `ℚ_p` (where `hT` holds automatically by `norm_coord_inclusion_pow_lt_amiceRadius`). -/
theorem discExpansionOfCoord_inclusion_pow_apply (n j : ℕ)
    (hT : ‖(inclusion (p := p) K ^ n).coord‖ < amiceRadius p j :=
      norm_coord_inclusion_pow_lt_amiceRadius n j)
    {a : ZMod (p ^ (padicUnitsDepth p + j))} (ha : IsUnit a) (m : ℕ) :
    (inclusion (p := p) K ^ n).discExpansionOfCoord j hT (a, m) =
      padicIntAlgebraMap p K ((n.choose m : ℤ_[p]) * (a.val : ℤ_[p]) ^ (n - m) *
        (p : ℤ_[p]) ^ ((padicUnitsDepth p + j) * m)) := by
  simp [discExpansion_inclusion_pow_apply, ha]

end Field

end TauCeti.WeightSpace
