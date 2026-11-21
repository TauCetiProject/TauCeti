/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps
public import TauCeti.Analysis.Normed.Module.InfiniteSum
public import TauCeti.NumberTheory.Padics.Disc
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import Mathlib.Algebra.GroupWithZero.Action.Regular

/-!
# Analytic stages on `ℤ_p` and their evaluation

For `h : ℕ`, the residue classes `a ∈ ZMod (p ^ h)` cut `ℤ_p` into the discs `a + pʰℤ_p`, where
`a` is represented by its natural representative `a.val < pʰ`. On the disc of `a` the coordinate
`w = (x - a) / pʰ` runs through `ℤ_p`, and a function analytic on each of these discs is a family
of power series `∑ₙ c(a, n) wⁿ` whose coefficients tend to zero. With coefficients in a complete
ultrametric normed `ℤ_p`-module `E`, these coefficient families make up the analytic stage

`LA_h(E) = C₀(ZMod (pʰ) × ℕ, E)`,

normed by the largest coefficient (the maximum of the Gauss norms on the discs). Its elements are
coefficient vectors, kept distinct from the functions they define: evaluation need not be
injective when `E` has `p`-torsion. If multiplication by `p` on `E` is injective, evaluation
is injective: values at powers of `p` in each normalized disc coordinate determine all
coefficients by cancellation and a vanishing tail estimate.

Evaluation `TauCeti.AnalyticStage.eval` sends a coefficient vector to the continuous function
`x ↦ ∑ₙ wⁿ • c(a, n)`. It is linear over every scalar ring acting on `E` compatibly with `ℤ_p`,
and does not increase norms.

Passing from level `h` to level `h + 1` subdivides each disc `a + pʰℤ_p` into the `p` discs of the
classes `a' = a + pʰ b`, `0 ≤ b < p`, in `ZMod (p ^ (h + 1))`. On the smaller disc
`w = b + p v`, so re-expanding in `v` gives the coefficients

`d(a', j) = ∑_{k ≥ j} (k choose j) b^(k - j) pʲ • c(a, k)`.

The transition `TauCeti.AnalyticStage.transition` is this re-expansion. It does not increase norms
and it is compatible with evaluation. Composing these adjacent transitions gives
`transitionLE S hhk : LA_h(E) →L[S] LA_k(E)` for every `h ≤ k`. These maps form a directed
system, do not increase norms, and preserve evaluation. No injectivity assumption is needed.
When multiplication by `p` on `E` is injective, every transition is injective: reading the
coefficients on the subdisc with the same centre recovers `p^j` times the original coefficient.

The disc decomposition itself is the homeomorphism `PadicInt.discHomeomorph` of
`TauCeti.NumberTheory.Padics.Disc`, which sends `(a, w)` to `a.val + pʰ w`.

## Main definitions

* `TauCeti.AnalyticStage p h E`: the analytic stage `C₀(ZMod (pʰ) × ℕ, E)`.
* `TauCeti.AnalyticStage.eval S`: evaluation `LA_h(E) →L[S] C(ℤ_p, E)`.
* `TauCeti.AnalyticStage.transitionScalar b j k`: the re-expansion scalar
  `(k choose j) b^(k - j) pʲ`, the coefficient of `vʲ` in `(b + p v)ᵏ`.
* `TauCeti.AnalyticStage.transition S`: the re-expansion `LA_h(E) →L[S] LA_{h+1}(E)`.
* `TauCeti.AnalyticStage.transitionLE S hhk`: re-expansion from level `h` to level `k` for `h ≤ k`.

## Main results

* `TauCeti.AnalyticStage.eval_natCast_val_add_mul`: on the disc of `a`, the evaluation of `c` is
  `∑ₙ wⁿ • c(a, n)`; `TauCeti.AnalyticStage.eval_apply_zero` specializes to `0`, and
  `TauCeti.AnalyticStage.eval_single` evaluates a single coordinate vector.
* `TauCeti.AnalyticStage.norm_eval_le`, `TauCeti.AnalyticStage.opNorm_eval_le_one`: evaluation
  does not increase norms.
* `TauCeti.AnalyticStage.eval_compLeft`: evaluation commutes with uniformly bounded coefficient maps
  compatible with `ℤ_p`.
* `TauCeti.AnalyticStage.eval_injective`: evaluation is injective when multiplication by `p`
  on the coefficient module is injective.
* `TauCeti.AnalyticStage.transition_apply`, `TauCeti.AnalyticStage.hasSum_transition_apply`: the
  re-expansion formula for the transition.
* `TauCeti.AnalyticStage.transitionScalar_def`: the value of the re-expansion scalars.
* `TauCeti.AnalyticStage.transitionScalar_succ_succ`: Pascal's rule for the re-expansion scalars.
* `TauCeti.AnalyticStage.norm_transition_apply_le`: the coefficient of `vʲ` after the transition
  has norm at most `‖p‖ʲ ‖c‖`.
* `TauCeti.AnalyticStage.transition_apply_cast`: the same-centre coefficients recover
  `p^j` times the original coefficients.
* `TauCeti.AnalyticStage.transition_injective`: the transition is injective when multiplication
  by `p` on the coefficients is injective.
* `TauCeti.AnalyticStage.norm_transition_le`: the transition does not increase norms.
* `TauCeti.AnalyticStage.exists_norm_transition_le`: uniform boundedness of `transition`.
* `TauCeti.AnalyticStage.transition_compLeft`: the transition commutes with uniformly bounded
  coefficient maps compatible with `ℤ_p`.
* `TauCeti.AnalyticStage.eval_transition`, `TauCeti.AnalyticStage.eval_comp_transition`: the
  transition is compatible with evaluation.
* `TauCeti.AnalyticStage.transitionLE_comp`: re-expansion through an intermediate level is
  re-expansion to the final level.
* `TauCeti.AnalyticStage.norm_transitionLE_le`,
  `TauCeti.AnalyticStage.opNorm_transitionLE_le_one`: every multi-level transition decreases norms.
* `TauCeti.AnalyticStage.eval_transitionLE`, `TauCeti.AnalyticStage.eval_comp_transitionLE`:
  every multi-level transition preserves evaluation.
* `TauCeti.AnalyticStage.transitionLE_injective`: multi-level transitions are injective under
  the same scalar-regularity hypothesis.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti

/-! ### Analytic stages -/

variable (p) in
/-- The analytic stage `LA_h(E) = C₀(ZMod (pʰ) × ℕ, E)` of level `h`: the coefficient vectors
`c(a, n)` of families of power series `∑ₙ c(a, n) wⁿ`, one on each disc `a + pʰℤ_p`, in the
coordinate `w = (x - a.val) / pʰ`. Its norm is the largest coefficient norm. -/
abbrev AnalyticStage (h : ℕ) (E : Type*) [NormedAddCommGroup E] : Type _ :=
  C₀(ZMod (p ^ h) × ℕ, E)

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E]

omit hp in
/-- The coefficients of a vector in `LA_h(E)` on a single disc tend to zero. -/
private theorem tendsto_apply_mk_atTop (c : AnalyticStage p h E) (a : ZMod (p ^ h)) :
    Tendsto (fun n ↦ c (a, n)) atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact c.tendsto_cofinite.comp
    (Function.Injective.tendsto_cofinite fun _ _ hn ↦ (Prod.ext_iff.1 hn).2)

variable [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]

/-- The monomial `wⁿ • e` on the disc of `a`, extended by zero, as a function of `(a, w)`. -/
private noncomputable def discTerm (i : ZMod (p ^ h) × ℕ) (e : E) :
    C(ZMod (p ^ h) × ℤ_[p], E) where
  toFun y := if y.1 = i.1 then y.2 ^ i.2 • e else 0
  continuous_toFun := continuous_prod_of_discrete_left.mpr fun b ↦ by
    by_cases hb : b = i.1
    · simp only [hb, ite_true]
      fun_prop
    · simp only [hb, ite_false]
      fun_prop

private theorem norm_discTerm_le (i : ZMod (p ^ h) × ℕ) (e : E) : ‖discTerm i e‖ ≤ ‖e‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg e)).mpr fun y ↦ by
    simp only [discTerm, ContinuousMap.coe_mk]
    split_ifs
    · exact PadicInt.norm_smul_le_norm _ e
    · simp

variable [IsUltrametricDist E] [CompleteSpace E]

private theorem summable_smul_apply (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (r : ℕ → ℤ_[p]) :
    Summable fun n ↦ r n • c (a, n) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
    rw [Nat.cofinite_eq_atTop]
    exact squeeze_zero_norm (fun n ↦ PadicInt.norm_smul_le_norm (r n) _)
      (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_apply_mk_atTop c a))

/-- The family of power series with coefficient vector `c`, as a continuous function of the
disc label and the disc coordinate. -/
private noncomputable def discSeries (c : AnalyticStage p h E) : C(ZMod (p ^ h) × ℤ_[p], E) :=
  ∑' i, discTerm i (c i)

private theorem summable_discTerm (c : AnalyticStage p h E) :
    Summable fun i ↦ discTerm i (c i) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
    squeeze_zero_norm (fun i ↦ norm_discTerm_le i (c i))
      (tendsto_zero_iff_norm_tendsto_zero.mp c.tendsto_cofinite)

private theorem hasSum_discSeries_apply (c : AnalyticStage p h E) (y : ZMod (p ^ h) × ℤ_[p]) :
    HasSum (fun n ↦ y.2 ^ n • c (y.1, n)) (discSeries c y) := by
  have hsum : HasSum (fun i ↦ discTerm i (c i) y) (discSeries c y) := by
    simpa [discSeries] using (summable_discTerm c).hasSum.mapL (ContinuousMap.evalCLM ℤ_[p] y)
  have hinj : Function.Injective fun n : ℕ ↦ (y.1, n) := fun _ _ hn ↦ (Prod.ext_iff.1 hn).2
  refine ((hinj.hasSum_iff fun i hi ↦ ?_).mpr hsum).congr_fun ?_
  · have hne : y.1 ≠ i.1 := fun he ↦ hi ⟨i.2, by simp [he]⟩
    simp [discTerm, hne]
  · intro n
    simp [discTerm]

omit [CompleteSpace E] in
private theorem norm_discSeries_le (c : AnalyticStage p h E) : ‖discSeries c‖ ≤ ‖c‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg c) fun i ↦
    (norm_discTerm_le i (c i)).trans (c.norm_coe_le_norm i)

omit [CompleteSpace E] in
private theorem norm_discSeries_comp_le (c : AnalyticStage p h E) :
    ‖(discSeries c).comp ((PadicInt.discHomeomorph p h).symm : C(ℤ_[p], ZMod (p ^ h) × ℤ_[p]))‖ ≤
      ‖c‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg c)).mpr fun _ ↦
    ((discSeries c).norm_coe_le_norm _).trans (norm_discSeries_le c)

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- Evaluation of the analytic stage `LA_h(E)`: the coefficient vector `c` defines the continuous
function equal to `∑ₙ wⁿ • c(a, n)` on the disc `a + pʰℤ_p`, where `w = (x - a.val) / pʰ`. It is
linear over every scalar ring `S` acting on `E` compatibly with `ℤ_p`. -/
noncomputable def eval : AnalyticStage p h E →L[S] C(ℤ_[p], E) :=
  let L : AnalyticStage p h E →ₗ[S] C(ℤ_[p], E) :=
    { toFun c := (discSeries c).comp (PadicInt.discHomeomorph p h).symm
      map_add' c d := by
        ext x
        simp only [ContinuousMap.comp_apply, ContinuousMap.add_apply,
          FunLike.coe_add, Pi.add_apply, smul_add,
          (hasSum_discSeries_apply _ _).tsum_eq.symm]
        exact (hasSum_discSeries_apply c _).summable.tsum_add
          (hasSum_discSeries_apply d _).summable
      map_smul' s c := by
        ext x
        simp only [ContinuousMap.comp_apply, ContinuousMap.smul_apply, RingHom.id_apply,
          FunLike.coe_smul, Pi.smul_apply,
          (hasSum_discSeries_apply _ _).tsum_eq.symm, smul_comm _ s]
        exact (hasSum_discSeries_apply c _).summable.tsum_const_smul s }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      exact norm_discSeries_comp_le c }

private theorem eval_apply_eq_discSeries (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval S c x = discSeries c ((PadicInt.discHomeomorph p h).symm x) :=
  (rfl)

/-- The value of the evaluation at `x` is the power series of the disc of `x` at the disc
coordinate of `x`. -/
theorem hasSum_eval_apply (c : AnalyticStage p h E) (x : ℤ_[p]) :
    HasSum (fun n ↦ ((PadicInt.discHomeomorph p h).symm x).2 ^ n •
      c (PadicInt.toZModPow h x, n)) (eval S c x) := by
  simpa only [eval_apply_eq_discSeries, PadicInt.fst_discHomeomorph_symm] using
    hasSum_discSeries_apply c ((PadicInt.discHomeomorph p h).symm x)

/-- The evaluation of `c` at `x` is the sum of the power series of the disc of `x` at the disc
coordinate of `x`. -/
theorem eval_apply (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval S c x = ∑' n, ((PadicInt.discHomeomorph p h).symm x).2 ^ n •
      c (PadicInt.toZModPow h x, n) :=
  (hasSum_eval_apply S c x).tsum_eq.symm

/-- On the disc `a + pʰℤ_p`, the evaluation of `c` is the power series `∑ₙ wⁿ • c(a, n)` in the
disc coordinate `w`. -/
theorem hasSum_eval_natCast_val_add_mul (c : AnalyticStage p h E) (a : ZMod (p ^ h))
    (w : ℤ_[p]) :
    HasSum (fun n ↦ w ^ n • c (a, n)) (eval S c ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w)) := by
  simpa only [eval_apply_eq_discSeries, PadicInt.discHomeomorph_symm_natCast_val_add_mul] using
    hasSum_discSeries_apply c (a, w)

/-- On the disc of `a`, the evaluation of `c` at `a.val + pʰ w` is `∑' n, wⁿ • c(a, n)`. -/
theorem eval_natCast_val_add_mul (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (w : ℤ_[p]) :
    eval S c ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * w) = ∑' n, w ^ n • c (a, n) :=
  (hasSum_eval_natCast_val_add_mul S c a w).tsum_eq.symm

/-- Evaluation does not increase norms. -/
theorem norm_eval_le (c : AnalyticStage p h E) : ‖eval S c‖ ≤ ‖c‖ :=
  norm_discSeries_comp_le c

/-- Evaluation has operator norm at most `1`. -/
theorem opNorm_eval_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℤ_[p] 𝕜 E] : ‖eval (p := p) (h := h) (E := E) 𝕜‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by
    simpa using norm_eval_le 𝕜 c

/-- Stage evaluation at `0` reads off the constant coefficient on the disc `pʰℤ_p` of `0`. -/
@[simp]
theorem eval_apply_zero (c : AnalyticStage p h E) :
    eval S c 0 = c (0, 0) := by
  have h0 : (0 : ℤ_[p]) = (((0 : ZMod (p ^ h)).val : ℕ) : ℤ_[p]) + (p : ℤ_[p]) ^ h * 0 := by
    simp
  conv_lhs => rw [h0]
  rw [eval_natCast_val_add_mul, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-- Stage evaluation of a coordinate vector `single (a, n) e` at `z`: it vanishes outside the disc
of `a` and equals `w ^ n • e` on that disc, where `w` is the local disc coordinate of `z`. -/
theorem eval_single (a : ZMod (p ^ h)) (n : ℕ) (e : E) (z : ℤ_[p]) :
    eval S (ZeroAtInftyContinuousMap.single (a, n) e) z =
      if PadicInt.toZModPow h z = a then ((PadicInt.discHomeomorph p h).symm z).2 ^ n • e
      else 0 := by
  conv_lhs => rw [← PadicInt.natCast_val_toZModPow_add_mul_snd_discHomeomorph_symm h z]
  rw [eval_natCast_val_add_mul, tsum_eq_single n]
  · by_cases ha : PadicInt.toZModPow h z = a <;>
      simp [ZeroAtInftyContinuousMap.single_apply, ha]
  · intro k hk
    simp [ZeroAtInftyContinuousMap.single_apply, hk]

/-- The underlying function of `eval S c` does not depend on the auxiliary scalar ring `S`. -/
theorem eval_eq_eval_padicInt (c : AnalyticStage p h E) :
    eval S c = eval ℤ_[p] c := by
  ext x
  rw [eval_apply, eval_apply]

/-- Stage evaluation commutes with any uniformly bounded coefficient map compatible with `ℤ_p`. -/
theorem eval_compLeft {F : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F] [IsBoundedSMul ℤ_[p] F]
    [IsUltrametricDist F] [CompleteSpace F] [Module S F] [ContinuousConstSMul S F]
    [SMulCommClass ℤ_[p] S F] [LinearMap.CompatibleSMul E F ℤ_[p] S]
    (φ : E →L[S] F) (hφ : ∃ C, ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval S (ZeroAtInftyContinuousMap.compLeft φ hφ c) x = φ (eval S c x) :=
  (hasSum_eval_apply S (ZeroAtInftyContinuousMap.compLeft φ hφ c) x).unique <| by
    simpa only [ZeroAtInftyContinuousMap.compLeft_apply,
      ContinuousLinearMap.map_smul_of_tower] using (hasSum_eval_apply S c x).mapL φ

private theorem summable_smul_apply_add (c : AnalyticStage p h E) (a : ZMod (p ^ h))
    (n : ℕ) (r : ℕ → ℤ_[p]) : Summable fun k ↦ r k • c (a, k + n) := by
  simpa using (summable_nat_add_iff n).mpr (summable_smul_apply c a fun k ↦ r (k - n))

private theorem tsum_pow_smul_apply_add_eq_zero (hpE : IsSMulRegular E (p : ℤ_[p]))
    (c : AnalyticStage p h E) (hc : eval S c = 0) (a : ZMod (p ^ h)) (n : ℕ)
    (hn : ∀ k < n, c (a, k) = 0) (m : ℕ) :
    ∑' k, ((p : ℤ_[p]) ^ m) ^ k • c (a, k + n) = 0 := by
  set x : ℤ_[p] := p ^ m with hx
  have hs := summable_smul_apply_add c a n fun k ↦ x ^ k
  refine ((hpE.pow m).pow n).right_eq_zero_of_smul ?_
  rw [← hx, ← hs.tsum_const_smul]
  have hzero : ∑' k, x ^ k • c (a, k) = 0 := by
    rw [← eval_natCast_val_add_mul S, hc, ContinuousMap.zero_apply]
  have hprefix : ∑ k ∈ Finset.range n, x ^ k • c (a, k) = 0 :=
    Finset.sum_eq_zero fun k hk ↦ by rw [hn k (Finset.mem_range.mp hk), smul_zero]
  have htail := (summable_smul_apply c a fun k ↦ x ^ k).sum_add_tsum_nat_add n
  rw [hprefix, zero_add, hzero] at htail
  simpa only [smul_smul, ← pow_add, Nat.add_comm n] using htail

private theorem norm_apply_le_of_eval_eq_zero (hpE : IsSMulRegular E (p : ℤ_[p]))
    (c : AnalyticStage p h E) (hc : eval S c = 0) (a : ZMod (p ^ h)) (n : ℕ)
    (hn : ∀ k < n, c (a, k) = 0) (m : ℕ) :
    ‖c (a, n)‖ ≤ ‖(p : ℤ_[p])‖ ^ m * ‖c‖ := by
  set x : ℤ_[p] := p ^ m with hx
  have hs := summable_smul_apply_add c a n fun k ↦ x ^ k
  have hzero := tsum_pow_smul_apply_add_eq_zero S hpE c hc a n hn m
  rw [← hx, hs.tsum_eq_zero_add, pow_zero, one_smul, zero_add] at hzero
  have heq : c (a, n) = -∑' k, x ^ (k + 1) • c (a, k + 1 + n) :=
    eq_neg_iff_add_eq_zero.mpr hzero
  rw [heq, norm_neg, ← norm_pow, ← hx]
  apply IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity)
  intro k
  calc
    ‖x ^ (k + 1) • c (a, k + 1 + n)‖ ≤ ‖x ^ (k + 1)‖ * ‖c (a, k + 1 + n)‖ :=
      norm_smul_le _ _
    _ ≤ ‖x‖ * ‖c‖ := mul_le_mul (by
      rw [norm_pow, pow_succ]
      exact mul_le_of_le_one_left (norm_nonneg x)
        (pow_le_one₀ (norm_nonneg x) (PadicInt.norm_le_one x)))
      (c.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)

/-- Analytic-stage evaluation is injective if multiplication by `p` on the coefficient module
is injective. The coefficient module need not carry a field structure or an isometric scalar
action. -/
theorem eval_injective (hpE : IsSMulRegular E (p : ℤ_[p])) :
    Function.Injective (eval (p := p) (h := h) (E := E) S) := by
  apply (injective_iff_map_eq_zero (eval S)).mpr
  intro c hc
  ext ⟨a, n⟩
  rw [_root_.zero_apply]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    apply norm_eq_zero.mp
    apply le_antisymm ?_ (norm_nonneg _)
    have hlim : Tendsto (fun m : ℕ ↦ ‖(p : ℤ_[p])‖ ^ m * ‖c‖) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg (p : ℤ_[p])) PadicInt.norm_p_lt_one).mul_const ‖c‖
    exact ge_of_tendsto hlim (.of_forall fun m ↦
      norm_apply_le_of_eval_eq_zero S hpE c hc a n ih m)

/-! ### Raising the level -/

/-- The re-expansion scalars `(k choose j) b^(k - j) pʲ`, the coefficient of `vʲ` in
`(b + p v)ᵏ`. -/
noncomputable def transitionScalar (b : ℤ_[p]) (j k : ℕ) : ℤ_[p] :=
  (k.choose j : ℤ_[p]) * b ^ (k - j) * (p : ℤ_[p]) ^ j

/-- The value of the re-expansion scalar `transitionScalar b j k`. -/
theorem transitionScalar_def (b : ℤ_[p]) (j k : ℕ) :
    transitionScalar b j k = (k.choose j : ℤ_[p]) * b ^ (k - j) * (p : ℤ_[p]) ^ j := by
  rw [transitionScalar]

private theorem norm_transitionScalar_le (b : ℤ_[p]) (j k : ℕ) :
    ‖transitionScalar b j k‖ ≤ ‖(p : ℤ_[p])‖ ^ j := by
  rw [transitionScalar, norm_mul, norm_mul, norm_pow (p : ℤ_[p])]
  calc _ ≤ 1 * 1 * ‖(p : ℤ_[p])‖ ^ j := by
        gcongr
        exacts [PadicInt.norm_le_one _, PadicInt.norm_le_one _]
    _ = _ := by ring

/-- The constant re-expansion scalars are the powers `bᵏ`. -/
@[simp]
theorem transitionScalar_zero_left (b : ℤ_[p]) (k : ℕ) : transitionScalar b 0 k = b ^ k := by
  simp [transitionScalar]

/-- Pascal's rule for the re-expansion scalars:
`T(j + 1, k + 1) = b T(j + 1, k) + p T(j, k)`. -/
theorem transitionScalar_succ_succ (b : ℤ_[p]) (j k : ℕ) :
    transitionScalar b (j + 1) (k + 1) =
      b * transitionScalar b (j + 1) k + (p : ℤ_[p]) * transitionScalar b j k := by
  simp only [transitionScalar, Nat.add_sub_add_right, Nat.choose_succ_succ', Nat.cast_add]
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hjk
    rw [show j + m + 1 - (j + 1) = m by omega, show j + m + 1 - j = m + 1 by omega]
    ring
  · simp [Nat.choose_succ_self, pow_succ]
    ring
  · simp [Nat.choose_eq_zero_of_lt hjk, Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_lt hjk)]

/-- `(b + p v)ᵏ` is the sum of the re-expansion terms `vʲ (k choose j) b^(k - j) pʲ`. -/
private theorem add_mul_pow_eq_sum_transitionScalar (b v : ℤ_[p]) (k : ℕ) :
    (b + p * v) ^ k = ∑ j ∈ Finset.range (k + 1), v ^ j * transitionScalar b j k := by
  rw [add_comm, add_pow]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [transitionScalar]; ring

/-- The coefficients of the re-expansion of `c` on the discs of level `h + 1`: on the disc of
`a' = a + pʰ b`, `0 ≤ b < p`, the coefficient of `vʲ` is
`∑ₖ (k choose j) b^(k - j) pʲ • c(a, k)`. -/
private noncomputable def transitionCoeff (c : AnalyticStage p h E)
    (i : ZMod (p ^ (h + 1)) × ℕ) : E :=
  ∑' k, transitionScalar ((i.1.val / p ^ h : ℕ) : ℤ_[p]) i.2 k • c ((i.1.val : ZMod (p ^ h)), k)

private theorem summable_transitionScalar_smul (c : AnalyticStage p h E) (a : ZMod (p ^ h))
    (b : ℤ_[p]) (j : ℕ) : Summable fun k ↦ transitionScalar b j k • c (a, k) :=
  summable_smul_apply c a _

omit [CompleteSpace E] in
private theorem norm_transitionCoeff_le (c : AnalyticStage p h E) (i : ZMod (p ^ (h + 1)) × ℕ) :
    ‖transitionCoeff c i‖ ≤ ‖(p : ℤ_[p])‖ ^ i.2 * ‖c‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k ↦
    (norm_smul_le _ _).trans <| mul_le_mul (norm_transitionScalar_le _ _ _)
      (c.norm_coe_le_norm _) (norm_nonneg _) (by positivity)

omit [CompleteSpace E] in
private theorem norm_transitionCoeff_le_norm (c : AnalyticStage p h E)
    (i : ZMod (p ^ (h + 1)) × ℕ) : ‖transitionCoeff c i‖ ≤ ‖c‖ :=
  (norm_transitionCoeff_le c i).trans <| mul_le_of_le_one_left (norm_nonneg c) <|
    pow_le_one₀ (norm_nonneg _) PadicInt.norm_p_lt_one.le

omit [CompleteSpace E] in
private theorem tendsto_transitionCoeff (c : AnalyticStage p h E) :
    Tendsto (transitionCoeff c) cofinite (𝓝 0) :=
  squeeze_zero_norm (norm_transitionCoeff_le c) (PadicInt.tendsto_norm_p_pow_mul_cofinite _)

/-- The transition `LA_h(E) → LA_{h+1}(E)`. The disc of `a ∈ ZMod (pʰ)` is the union of the discs
of the classes `a' = a + pʰ b`, `0 ≤ b < p`, in `ZMod (p ^ (h + 1))`, where `b = ⌊a'.val / pʰ⌋`.
On the disc of `a'` the coordinates are related by `w = b + p v`, and the transition re-expands
`∑ₖ c(a, k) wᵏ` in powers of `v`:

`d(a', j) = ∑ₖ (k choose j) b^(k - j) pʲ • c(a, k)`. -/
noncomputable def transition : AnalyticStage p h E →L[S] AnalyticStage p (h + 1) E :=
  let L : AnalyticStage p h E →ₗ[S] AnalyticStage p (h + 1) E :=
    { toFun c := ZeroAtInftyContinuousMap.mkOfDiscrete (transitionCoeff c)
        (tendsto_transitionCoeff c)
      map_add' c d := by
        ext i
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, transitionCoeff,
          FunLike.coe_add, Pi.add_apply, smul_add]
        exact (summable_transitionScalar_smul c _ _ _).tsum_add
          (summable_transitionScalar_smul d _ _ _)
      map_smul' s c := by
        ext i
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, transitionCoeff,
          FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_comm _ s]
        exact (summable_transitionScalar_smul c _ _ _).tsum_const_smul s }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦ ?_
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
      exact norm_transitionCoeff_le_norm c i }

private theorem coe_transition (c : AnalyticStage p h E) :
    ⇑(transition S c) = transitionCoeff c :=
  ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _

/-- The re-expansion formula for the transition. -/
theorem transition_apply (c : AnalyticStage p h E) (a' : ZMod (p ^ (h + 1))) (j : ℕ) :
    transition S c (a', j) = ∑' k, ((k.choose j : ℤ_[p]) *
      ((a'.val / p ^ h : ℕ) : ℤ_[p]) ^ (k - j) * (p : ℤ_[p]) ^ j) •
        c ((a'.val : ZMod (p ^ h)), k) := by
  rw [coe_transition]
  rfl

/-- The re-expansion formula for the transition, as a convergent series in the re-expansion
scalars `transitionScalar`. -/
theorem hasSum_transition_apply (c : AnalyticStage p h E) (a' : ZMod (p ^ (h + 1))) (j : ℕ) :
    HasSum (fun k ↦ transitionScalar ((a'.val / p ^ h : ℕ) : ℤ_[p]) j k •
      c ((a'.val : ZMod (p ^ h)), k)) (transition S c (a', j)) := by
  rw [coe_transition]
  exact (summable_transitionScalar_smul c _ _ _).hasSum

/-- On the subdisc with the same natural centre, re-expansion multiplies the degree-`j`
coefficient by `p^j`. -/
@[simp]
theorem transition_apply_cast (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (j : ℕ) :
    transition S c ((a.cast : ZMod (p ^ (h + 1))), j) = (p : ℤ_[p]) ^ j • c (a, j) := by
  have hval : (a.cast : ZMod (p ^ (h + 1))).val = a.val :=
    ZMod.val_cast_eq_val_of_lt <| (ZMod.val_lt a).trans_le
      (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ h))
  rw [transition_apply, hval, Nat.div_eq_of_lt (ZMod.val_lt a), tsum_eq_single j]
  · simp
  · intro k hkj
    by_cases hlt : k < j
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · have hsub : k - j ≠ 0 := by omega
      simp [hsub]

/-- Raising the level is injective if multiplication by `p` on the coefficient module is
injective. -/
theorem transition_injective (hpE : IsSMulRegular E (p : ℤ_[p])) :
    Function.Injective (transition (p := p) (h := h) (E := E) S) := by
  intro c d hcd
  ext ⟨a, j⟩
  apply IsSMulRegular.pow j hpE
  simpa only [transition_apply_cast] using
    DFunLike.congr_fun hcd ((a.cast : ZMod (p ^ (h + 1))), j)

/-- The coefficient of `vʲ` after the transition has norm at most `‖p‖ʲ ‖c‖`. -/
theorem norm_transition_apply_le (c : AnalyticStage p h E) (a' : ZMod (p ^ (h + 1))) (j : ℕ) :
    ‖transition S c (a', j)‖ ≤ ‖(p : ℤ_[p])‖ ^ j * ‖c‖ := by
  rw [coe_transition]
  exact norm_transitionCoeff_le c (a', j)

/-- The transition does not increase norms. -/
theorem norm_transition_le (c : AnalyticStage p h E) : ‖transition S c‖ ≤ ‖c‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦
    coe_transition S c ▸ norm_transitionCoeff_le_norm c i

/-- The transition is uniformly bounded, in the form required by
`ZeroAtInftyContinuousMap.compLeft`. -/
theorem exists_norm_transition_le :
    ∃ C, ∀ c : AnalyticStage p h E, ‖transition S c‖ ≤ C * ‖c‖ :=
  ⟨1, fun c ↦ by simpa only [one_mul] using norm_transition_le S c⟩

/-- The underlying vector of `transition S c` does not depend on the auxiliary scalar ring `S`. -/
theorem transition_eq_transition_padicInt (c : AnalyticStage p h E) :
    transition S c = transition ℤ_[p] c := by
  ext ⟨a', j⟩
  rw [transition_apply, transition_apply]

open ZeroAtInftyContinuousMap in
/-- Stage re-expansion commutes with any uniformly bounded coefficient map compatible with `ℤ_p`. -/
theorem transition_compLeft {F : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F]
    [IsBoundedSMul ℤ_[p] F] [IsUltrametricDist F] [CompleteSpace F]
    [Module S F] [ContinuousConstSMul S F] [SMulCommClass ℤ_[p] S F]
    [LinearMap.CompatibleSMul E F ℤ_[p] S]
    (φ : E →L[S] F) (hφ : ∃ C, ∀ e, ‖φ e‖ ≤ C * ‖e‖)
    (c : AnalyticStage p h E) :
    transition S (compLeft φ hφ c) = compLeft φ hφ (transition S c) := by
  have hcomp : (transition (p := p) (h := h) S).comp (compLeft φ hφ) =
      (compLeft φ hφ).comp (transition S) := by
    refine continuousLinearMap_ext fun ⟨a, k⟩ e ↦ ?_
    ext ⟨a', j⟩
    simp only [ContinuousLinearMap.comp_apply, compLeft_single, compLeft_apply, transition_apply]
    rw [tsum_eq_single k (fun m hm ↦ by simp [single_apply, hm]),
      tsum_eq_single k (fun m hm ↦ by simp [single_apply, hm])]
    by_cases ha : a'.cast = a <;> simp [single_apply, ha]
  exact DFunLike.congr_fun hcomp c

/-- The transition is compatible with evaluation: a coefficient vector and its re-expansion on
the smaller discs define the same function. -/
@[simp]
theorem eval_transition (c : AnalyticStage p h E) : eval S (transition S c) = eval S c := by
  ext x
  obtain ⟨⟨a', v⟩, rfl⟩ := (PadicInt.discHomeomorph p (h + 1)).surjective x
  set a : ZMod (p ^ h) := (a'.val : ZMod (p ^ h))
  set b : ℤ_[p] := ((a'.val / p ^ h : ℕ) : ℤ_[p])
  have hx : (a'.val : ℤ_[p]) + (p : ℤ_[p]) ^ (h + 1) * v =
      (a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (b + p * v) := by
    rw [PadicInt.natCast_val_eq_add a']
    ring
  rw [PadicInt.discHomeomorph_apply, eval_natCast_val_add_mul]
  conv_rhs => rw [hx, eval_natCast_val_add_mul]
  -- Expand each coefficient of the re-expansion and exchange the two summations.
  have hF :
      Summable (Function.uncurry fun j k ↦ (v ^ j * transitionScalar b j k) • c (a, k)) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <|
      squeeze_zero_norm (a := fun jk ↦ ‖(p : ℤ_[p])‖ ^ jk.1 • ‖c (a, jk.2)‖) (fun jk ↦ ?_) ?_
    · refine (norm_smul_le _ _).trans ?_
      rw [smul_eq_mul, norm_mul, norm_pow v]
      gcongr
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one _))).trans
          (norm_transitionScalar_le b _ _)
    · refine Filter.Tendsto.smul_cofinite_nhds_zero (f := fun j ↦ ‖(p : ℤ_[p])‖ ^ j)
        (g := fun k ↦ ‖c (a, k)‖) PadicInt.tendsto_norm_p_pow_cofinite ?_
      rw [Nat.cofinite_eq_atTop]
      simpa using (tendsto_apply_mk_atTop c a).norm
  calc ∑' j, v ^ j • transition S c (a', j)
      = ∑' j, ∑' k, (v ^ j * transitionScalar b j k) • c (a, k) := by
        refine tsum_congr fun j ↦ ?_
        simp_rw [transition_apply, mul_smul (v ^ j)]
        exact ((summable_transitionScalar_smul c a b j).tsum_const_smul _).symm
    _ = ∑' k, ∑' j, (v ^ j * transitionScalar b j k) • c (a, k) := hF.tsum_comm.symm
    _ = ∑' k, (b + p * v) ^ k • c (a, k) := by
        refine tsum_congr fun k ↦ ?_
        rw [add_mul_pow_eq_sum_transitionScalar, Finset.sum_smul]
        refine tsum_eq_sum fun j hj ↦ ?_
        rw [Finset.mem_range, not_lt] at hj
        simp [transitionScalar, Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_le hj)]

/-- Evaluation after the transition is evaluation, as an identity of continuous linear maps. -/
@[simp]
theorem eval_comp_transition :
    (eval (p := p) (h := h + 1) (E := E) S).comp (transition S) = eval S :=
  ContinuousLinearMap.ext (eval_transition S)

variable {k l : ℕ}

/-- Re-expansion from level `h` to level `k`, obtained by composing adjacent transitions. -/
noncomputable def transitionLE (hhk : h ≤ k) : AnalyticStage p h E →L[S] AnalyticStage p k E :=
  Nat.leRecOn hhk (fun {_} L ↦ (transition S).comp L) (ContinuousLinearMap.id S _)

/-- Re-expansion from a level to itself is the identity. -/
@[simp]
theorem transitionLE_self :
    transitionLE (p := p) (E := E) S (le_refl h) = ContinuousLinearMap.id S _ :=
  Nat.leRecOn_self _

/-- Re-expansion to the next target level appends one adjacent transition. -/
theorem transitionLE_succ (hhk : h ≤ k) :
    transitionLE (p := p) (E := E) S (Nat.le_succ_of_le hhk) =
      (transition S).comp (transitionLE S hhk) :=
  Nat.leRecOn_succ hhk _

/-- Re-expansion to the adjacent level is the original transition. -/
@[simp]
theorem transitionLE_succ_self :
    transitionLE (p := p) (E := E) S (Nat.le_succ h) = transition S := by
  rw [transitionLE_succ S (le_refl h), transitionLE_self, ContinuousLinearMap.comp_id]

/-- Appending an adjacent transition is re-expansion to the next target level. -/
@[simp]
theorem transition_comp_transitionLE (hhk : h ≤ k) :
    (transition (p := p) (E := E) S).comp (transitionLE S hhk) =
      transitionLE S (Nat.le_succ_of_le hhk) :=
  (transitionLE_succ S hhk).symm

/-- Applying an adjacent transition after re-expansion raises the target level by one. -/
@[simp]
theorem transition_transitionLE (hhk : h ≤ k) (c : AnalyticStage p h E) :
    transition S (transitionLE S hhk c) = transitionLE S (Nat.le_succ_of_le hhk) c := by
  simpa only [ContinuousLinearMap.comp_apply] using
    DFunLike.congr_fun (transition_comp_transitionLE S hhk) c

/-- Re-expansion through an intermediate level equals the transition to the final level. -/
@[simp]
theorem transitionLE_comp (hhk : h ≤ k) (hkl : k ≤ l) :
    (transitionLE (p := p) (E := E) S hkl).comp (transitionLE S hhk) =
      transitionLE S (hhk.trans hkl) := by
  induction l, hkl using Nat.le_induction with
  | base => simp
  | succ l hkl ih =>
    rw [transitionLE_succ S hkl, transitionLE_succ S (hhk.trans hkl),
      ContinuousLinearMap.comp_assoc, ih]

/-- Applying two successive transitions is the transition across the combined levels. -/
@[simp]
theorem transitionLE_transitionLE (hhk : h ≤ k) (hkl : k ≤ l) (c : AnalyticStage p h E) :
    transitionLE S hkl (transitionLE S hhk c) = transitionLE S (hhk.trans hkl) c := by
  simpa only [ContinuousLinearMap.comp_apply] using
    DFunLike.congr_fun (transitionLE_comp S hhk hkl) c

/-- Re-expansion after an adjacent transition starts one level earlier. -/
@[simp]
theorem transitionLE_comp_transition (hkl : h + 1 ≤ k) :
    (transitionLE (p := p) (E := E) S hkl).comp (transition S) =
      transitionLE S ((Nat.le_succ h).trans hkl) := by
  simpa only [transitionLE_succ_self] using
    transitionLE_comp (p := p) (E := E) S (Nat.le_succ h) hkl

/-- Applying re-expansion after an adjacent transition starts one level earlier. -/
@[simp]
theorem transitionLE_transition (hkl : h + 1 ≤ k) (c : AnalyticStage p h E) :
    transitionLE S hkl (transition S c) = transitionLE S ((Nat.le_succ h).trans hkl) c := by
  simpa only [ContinuousLinearMap.comp_apply] using
    DFunLike.congr_fun (transitionLE_comp_transition S hkl) c

/-- Two adjacent transitions compose to re-expansion across two levels. -/
@[simp]
theorem transition_comp_transition :
    (transition (p := p) (h := h + 1) (E := E) S).comp (transition S) =
      transitionLE S (Nat.le_add_right h 2) := by
  simpa only [transitionLE_succ_self] using
    transitionLE_comp_transition (p := p) (E := E) S (Nat.le_succ (h + 1))

/-- Two adjacent transitions re-expand a coefficient vector across two levels. -/
@[simp]
theorem transition_transition (c : AnalyticStage p h E) :
    transition S (transition S c) = transitionLE S (Nat.le_add_right h 2) c := by
  simpa only [ContinuousLinearMap.comp_apply] using
    DFunLike.congr_fun (transition_comp_transition S) c

/-- Analytic-stage transitions form a directed system of coefficient vectors. -/
instance instDirectedSystemTransitionLE :
    DirectedSystem (fun h ↦ AnalyticStage p h E)
      (fun {_ _} hhk ↦ transitionLE (p := p) (E := E) S hhk) where
  map_self := fun {_} c ↦ by simp
  map_map := fun {_ _ _} hhk hkl c ↦
    transitionLE_transitionLE S hhk hkl c

/-- Re-expansion between any two analytic levels does not increase the Gauss norm. -/
theorem norm_transitionLE_le (hhk : h ≤ k) (c : AnalyticStage p h E) :
    ‖transitionLE S hhk c‖ ≤ ‖c‖ := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply]
    exact (norm_transition_le S _).trans ih

/-- Re-expansion between any two analytic levels has operator norm at most `1`. -/
theorem opNorm_transitionLE_le_one {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℤ_[p] 𝕜 E] (hhk : h ≤ k) : ‖transitionLE (p := p) (E := E) 𝕜 hhk‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ by
    simpa using norm_transitionLE_le 𝕜 hhk c

/-- Re-expansion between any two analytic levels preserves the evaluated function. -/
@[simp]
theorem eval_transitionLE (hhk : h ≤ k) (c : AnalyticStage p h E) :
    eval S (transitionLE S hhk c) = eval S c := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, eval_transition, ih]

/-- Evaluation after re-expansion between two levels is evaluation, as an identity of continuous
linear maps. -/
@[simp]
theorem eval_comp_transitionLE (hhk : h ≤ k) :
    (eval (p := p) (h := k) (E := E) S).comp (transitionLE S hhk) = eval S :=
  ContinuousLinearMap.ext (eval_transitionLE S hhk)

/-- Re-expansion between any two levels is injective if multiplication by `p` on the
coefficient module is injective. -/
theorem transitionLE_injective (hpE : IsSMulRegular E (p : ℤ_[p])) (hhk : h ≤ k) :
    Function.Injective (transitionLE (p := p) (E := E) S hhk) := by
  induction k, hhk using Nat.le_induction with
  | base =>
    intro c d hcd
    simpa using hcd
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk]
    exact (transition_injective S hpE).comp ih

end AnalyticStage

end TauCeti
