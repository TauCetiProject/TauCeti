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
public import TauCeti.Algebra.Polynomial.Binomial
public import TauCeti.Analysis.Normed.Module.InfiniteSum
public import TauCeti.NumberTheory.Padics.Disc
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import TauCeti.Data.ZMod.Cast
import Mathlib.Algebra.GroupWithZero.Action.Regular
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

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

More generally, `TauCeti.AnalyticStage.reexpand s t c` is the coefficient sequence of
`∑ₙ (s + t v)ⁿ • cₙ` in powers of `v`, for any `s t ∈ ℤ_p`. Re-expanding twice along affine
substitutions is re-expanding once along their composite, so summing a re-expansion against the
powers of `v` evaluates the original series at `s + t v`.

The transition `TauCeti.AnalyticStage.transition` is the re-expansion along `b + p v`. It does
not increase norms and it is compatible with evaluation. Composing these adjacent transitions
gives `transitionLE S hhk : LA_h(E) →L[S] LA_k(E)` for every `h ≤ k`. These maps form a directed
system, do not increase norms, and preserve evaluation. No injectivity assumption is needed.
When multiplication by `p` on `E` is injective, every transition is injective: reading the
coefficients on the subdisc with the same centre recovers `p^j` times the original coefficient.

The coordinate projection `ZeroAtInftyContinuousMap.indicatorCLM` onto the discs of a set of
classes evaluates to the product with the indicator of their union, and re-expansion only reads
the coefficients on the disc containing a smaller disc, so it commutes with these projections.

The disc decomposition itself is the homeomorphism `PadicInt.discHomeomorph` of
`TauCeti.NumberTheory.Padics.Disc`, which sends `(a, w)` to `a.val + pʰ w`.

## Main definitions

* `TauCeti.AnalyticStage p h E`: the analytic stage `C₀(ZMod (pʰ) × ℕ, E)`.
* `TauCeti.AnalyticStage.rowsEquiv p h S`: the isometric identification
  `LA_h(E) ≃ₗᵢ[S] (ZMod (pʰ) → C₀(ℕ, E))` with families of disc coefficient sequences.
* `TauCeti.AnalyticStage.levelZeroEquiv p S`: the level-`0` isometric identification
  `LA_0(E) ≃ₗᵢ[S] C₀(ℕ, E)`.
* `TauCeti.AnalyticStage.eval S`: evaluation `LA_h(E) →L[S] C(ℤ_p, E)`.
* `TauCeti.AnalyticStage.reexpand s t c`: the coefficients of `∑ₙ (s + t v)ⁿ • cₙ` in powers
  of `v`.
* `TauCeti.AnalyticStage.reexpandMap S σ s t`: the pullback `LA_h(E) →L[S] LA_k(E)` along a map
  that is affine from each disc of level `k` into a disc of level `h`.
* `TauCeti.AnalyticStage.transition S`: the re-expansion `LA_h(E) →L[S] LA_{h+1}(E)`.
* `TauCeti.AnalyticStage.transitionLE S hhk`: re-expansion from level `h` to level `k` for `h ≤ k`.

## Main results

* `TauCeti.AnalyticStage.eval_natCast_val_add_mul`: on the disc of `a`, the evaluation of `c` is
  `∑ₙ wⁿ • c(a, n)`; at level `0` this is `∑ₙ xⁿ • cₙ`
  (`TauCeti.AnalyticStage.eval_levelZeroEquiv_symm_apply`), `TauCeti.AnalyticStage.eval_apply_zero`
  specializes to `0`, and `TauCeti.AnalyticStage.eval_single` evaluates a single coordinate vector.
* `TauCeti.AnalyticStage.norm_eval_le`, `TauCeti.AnalyticStage.opNorm_eval_le_one`: evaluation
  does not increase norms.
* `TauCeti.AnalyticStage.eval_compLeft`: evaluation commutes with uniformly bounded coefficient maps
  compatible with `ℤ_p`.
* `TauCeti.AnalyticStage.eval_injective`: evaluation is injective when multiplication by `p`
  on the coefficient module is injective.
* `TauCeti.AnalyticStage.reexpand_reexpand`: re-expansions compose along affine substitutions.
* `TauCeti.AnalyticStage.tsum_pow_smul_reexpand`: a re-expansion evaluates the original series
  at `s + t v`.
* `TauCeti.AnalyticStage.eval_reexpandMap_natCast_val_add_mul`: a re-expansion map evaluates to
  the pullback along the corresponding affine maps of discs.
* `TauCeti.AnalyticStage.transition_apply`, `TauCeti.AnalyticStage.hasSum_transition_apply`: the
  re-expansion formula for the transition.
* `TauCeti.AnalyticStage.reexpandScalar_succ_succ`: Pascal's rule for the re-expansion scalars.
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
* `TauCeti.AnalyticStage.eval_indicatorCLM`: projecting onto the discs of a set of classes
  evaluates to the product with the indicator of their union.
* `TauCeti.AnalyticStage.transitionLE_indicatorCLM`: re-expansion commutes with the projections
  onto the discs of a set of classes.

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
theorem tendsto_apply_mk (c : AnalyticStage p h E) (a : ZMod (p ^ h)) :
    Tendsto (fun n ↦ c (a, n)) cofinite (𝓝 0) :=
  c.tendsto_cofinite.comp (Prod.mk_right_injective a).tendsto_cofinite

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

/-- The power series of a vector in `LA_h(E)` on a single disc converges at every point of
`ℤ_p`, and more generally against any `ℤ_p`-valued weights. -/
theorem summable_smul_apply (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (r : ℕ → ℤ_[p]) :
    Summable fun n ↦ r n • c (a, n) :=
  summable_smul_of_tendsto_of_norm_le_one (tendsto_apply_mk c a) fun n ↦
    PadicInt.norm_le_one (r n)

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
    (n : ℕ) (r : ℕ → ℤ_[p]) :
    Summable fun k ↦ r k • c (a, k + n) := by
  simpa using (summable_nat_add_iff n).mpr
    (summable_smul_apply c a fun k ↦ r (k - n))

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

/-! ### Affine re-expansion of coefficient sequences -/

section Reexpansion

open Polynomial

/-- The coefficient `(n choose j) sⁿ⁻ʲ tʲ` of `vʲ` in `(s + t v)ⁿ`. -/
noncomputable def reexpandScalar (s t : ℤ_[p]) (n j : ℕ) : ℤ_[p] :=
  (n.choose j : ℤ_[p]) * s ^ (n - j) * t ^ j

/-- The closed form of the re-expansion scalar. -/
theorem reexpandScalar_def (s t : ℤ_[p]) (n j : ℕ) :
    reexpandScalar s t n j = (n.choose j : ℤ_[p]) * s ^ (n - j) * t ^ j := by
  rw [reexpandScalar]

/-- The re-expansion scalar vanishes above the degree: `(s + t v)ⁿ` has no `vʲ` term for `n < j`. -/
theorem reexpandScalar_of_lt (s t : ℤ_[p]) {n j : ℕ} (hnj : n < j) :
    reexpandScalar s t n j = 0 := by
  simp [reexpandScalar, Nat.choose_eq_zero_of_lt hnj]

/-- The re-expansion scalar of degree `j` has norm at most `‖t‖ʲ`. -/
theorem norm_reexpandScalar_le (s t : ℤ_[p]) (n j : ℕ) : ‖reexpandScalar s t n j‖ ≤ ‖t‖ ^ j := by
  rw [reexpandScalar, norm_mul, norm_mul, norm_pow t]
  calc _ ≤ 1 * 1 * ‖t‖ ^ j := by
        gcongr
        exacts [PadicInt.norm_le_one _, PadicInt.norm_le_one _]
    _ = _ := by ring

/-- Re-expanding twice is re-expanding once: `s₁ + t₁ (s₂ + t₂ u) = (s₁ + t₁ s₂) + t₁ t₂ u`. -/
theorem sum_reexpandScalar_mul (s₁ t₁ s₂ t₂ : ℤ_[p]) (n j : ℕ) :
    ∑ m ∈ Finset.range (n + 1), reexpandScalar s₂ t₂ m j * reexpandScalar s₁ t₁ n m =
      reexpandScalar (s₁ + t₁ * s₂) (t₁ * t₂) n j := by
  have hdeg : ((C s₁ + C t₁ * X) ^ n).natDegree < n + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_pow_le_of_le n ?_).trans (mul_one n).le)
    rw [add_comm]
    exact natDegree_linear_le
  have hcomp : ((C s₁ + C t₁ * X) ^ n).comp (C s₂ + C t₂ * X) =
      (C (s₁ + t₁ * s₂) + C (t₁ * t₂) * X) ^ n := by
    simp only [pow_comp, add_comp, mul_comp, C_comp, X_comp, map_add, map_mul]
    ring
  have h := coeff_comp_C_add_C_mul_X _ hdeg s₂ t₂ j
  rw [hcomp, coeff_C_add_C_mul_X_pow] at h
  rw [reexpandScalar_def, h]
  exact Finset.sum_congr rfl fun m _ ↦ by
    rw [coeff_C_add_C_mul_X_pow, reexpandScalar_def, reexpandScalar_def, mul_comm]

/-- The constant re-expansion scalars are the powers `sⁿ`. -/
@[simp]
theorem reexpandScalar_zero_right (s t : ℤ_[p]) (n : ℕ) : reexpandScalar s t n 0 = s ^ n := by
  simp [reexpandScalar]

/-- Pascal's rule for the re-expansion scalars:
`R(n + 1, j + 1) = s R(n, j + 1) + t R(n, j)`. -/
theorem reexpandScalar_succ_succ (s t : ℤ_[p]) (n j : ℕ) :
    reexpandScalar s t (n + 1) (j + 1) =
      s * reexpandScalar s t n (j + 1) + t * reexpandScalar s t n j := by
  simp only [reexpandScalar, Nat.add_sub_add_right, Nat.choose_succ_succ', Nat.cast_add]
  rcases lt_trichotomy j n with hjn | rfl | hjn
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hjn
    rw [show j + m + 1 - (j + 1) = m by omega, show j + m + 1 - j = m + 1 by omega]
    ring
  · simp [Nat.choose_succ_self, pow_succ]
    ring
  · simp [Nat.choose_eq_zero_of_lt hjn, Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_lt hjn)]

omit [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E] in
/-- The coefficients `∑ₙ (n choose j) sⁿ⁻ʲ tʲ • cₙ` of `∑ₙ (s + t v)ⁿ • cₙ` in powers of `v`. -/
noncomputable def reexpand (s t : ℤ_[p]) (c : ℕ → E) (j : ℕ) : E :=
  ∑' n, reexpandScalar s t n j • c n

omit [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E] in
/-- A re-expanded coefficient as a sum over the original coefficients. -/
theorem reexpand_def (s t : ℤ_[p]) (c : ℕ → E) (j : ℕ) :
    reexpand s t c j = ∑' n, reexpandScalar s t n j • c n := by
  rw [reexpand]

omit [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E] in
/-- Re-expanding along `0 + t v` scales the coefficient of `vʲ` by `tʲ`. -/
@[simp]
theorem reexpand_zero_left (t : ℤ_[p]) (c : ℕ → E) (j : ℕ) : reexpand 0 t c j = t ^ j • c j := by
  rw [reexpand, tsum_eq_single j fun n hn ↦ ?_]
  · simp [reexpandScalar]
  · rcases lt_or_gt_of_ne hn with hnj | hnj
    · simp [reexpandScalar_of_lt _ _ hnj]
    · simp [reexpandScalar, Nat.sub_ne_zero_of_lt hnj]

omit [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E] in
/-- Re-expanding the coefficients of a polynomial is substituting `s + t X` into it. -/
theorem reexpand_coeff_smul (P : ℤ_[p][X]) (s t : ℤ_[p]) (e : E) (j : ℕ) :
    reexpand s t (fun k ↦ P.coeff k • e) j = (P.comp (C s + C t * X)).coeff j • e := by
  rw [coeff_comp_C_add_C_mul_X P (Nat.lt_succ_self _) s t j, Finset.sum_smul, reexpand]
  refine (tsum_eq_sum fun k hk ↦ ?_).trans
    (Finset.sum_congr rfl fun k _ ↦ by rw [smul_smul, mul_comm, reexpandScalar])
  rw [Finset.mem_range, not_lt] at hk
  simp [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hk)]

omit [CompleteSpace E] in
/-- The coefficient of `vʲ` in a re-expansion along `s + t v` is bounded by `‖t‖ʲ` times the
coefficients of the same or higher degree. -/
theorem norm_reexpand_le (s t : ℤ_[p]) {c : ℕ → E} {C : ℝ} (hC : 0 ≤ C) {j : ℕ}
    (hc : ∀ n, j ≤ n → ‖c n‖ ≤ C) : ‖reexpand s t c j‖ ≤ ‖t‖ ^ j * C :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n ↦ by
    rcases lt_or_ge n j with hn | hn
    · simpa [reexpandScalar_of_lt s t hn] using mul_nonneg (pow_nonneg (norm_nonneg t) j) hC
    · exact (norm_smul_le _ _).trans <|
        mul_le_mul (norm_reexpandScalar_le s t n j) (hc n hn) (norm_nonneg _) (by positivity)

/-- **Composition of re-expansions.** Re-expanding `∑ₙ (s₁ + t₁ v)ⁿ • cₙ` along
`v = s₂ + t₂ u` is the re-expansion along `s₁ + t₁ (s₂ + t₂ u)`. -/
theorem reexpand_reexpand {c : ℕ → E} (hc : Tendsto c cofinite (𝓝 0))
    (s₁ t₁ s₂ t₂ : ℤ_[p]) (j : ℕ) :
    reexpand s₂ t₂ (reexpand s₁ t₁ c) j = reexpand (s₁ + t₁ * s₂) (t₁ * t₂) c j := by
  set f : ℕ → ℕ → E := fun m n ↦ (reexpandScalar s₂ t₂ m j * reexpandScalar s₁ t₁ n m) • c n
  -- The term `(m, n)` vanishes unless `m ≤ n`, so it is bounded by `‖c (max m n)‖`.
  have hmax : Tendsto (fun x : ℕ × ℕ ↦ max x.1 x.2) cofinite cofinite :=
    Tendsto.cofinite_of_finite_preimage_singleton fun k ↦
      ((Set.finite_Iic k).prod (Set.finite_Iic k)).subset fun x hx ↦ by
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨Set.mem_Iic.mpr (le_max_left _ _), Set.mem_Iic.mpr (le_max_right _ _)⟩
  have hf : Summable (Function.uncurry f) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| squeeze_zero_norm
      (a := fun x ↦ ‖c (max x.1 x.2)‖) (fun x ↦ ?_)
      ((tendsto_zero_iff_norm_tendsto_zero.mp hc).comp hmax)
    rcases le_or_gt x.1 x.2 with hx | hx
    · simpa [f, Function.uncurry, max_eq_right hx] using
        PadicInt.norm_smul_le_norm _ (c x.2)
    · simp [f, Function.uncurry, reexpandScalar_of_lt s₁ t₁ hx]
  calc reexpand s₂ t₂ (reexpand s₁ t₁ c) j = ∑' m, ∑' n, f m n := by
        refine tsum_congr fun m ↦ ?_
        simp only [reexpand, f, mul_smul]
        exact ((summable_smul_of_tendsto_of_norm_le_one hc fun n ↦
          PadicInt.norm_le_one _).tsum_const_smul _).symm
    _ = ∑' n, ∑' m, f m n := hf.tsum_comm.symm
    _ = reexpand (s₁ + t₁ * s₂) (t₁ * t₂) c j := by
        refine tsum_congr fun n ↦ ?_
        rw [← sum_reexpandScalar_mul, Finset.sum_smul]
        refine tsum_eq_sum fun m hm ↦ ?_
        rw [Finset.mem_range, not_lt] at hm
        simp [f, reexpandScalar_of_lt s₁ t₁ (Nat.lt_of_succ_le hm)]

/-- Summing a re-expansion against the powers of `w` evaluates the original series at
`s + t w`. -/
theorem tsum_pow_smul_reexpand {c : ℕ → E} (hc : Tendsto c cofinite (𝓝 0)) (s t w : ℤ_[p]) :
    ∑' j, w ^ j • reexpand s t c j = ∑' n, (s + t * w) ^ n • c n := by
  -- Re-expand once more along the constant substitution `w + 0 u` and read off the coefficient
  -- of `u⁰`: as `reexpandScalar w 0 n 0 = wⁿ`, the left side becomes `∑ⱼ wʲ • reexpand s t c j`
  -- and the right side, a re-expansion along `(s + t w) + 0 u`, becomes `∑ₙ (s + t w)ⁿ • cₙ`.
  simpa [reexpand, reexpandScalar] using reexpand_reexpand hc s t w 0 0

end Reexpansion

/-! ### Re-expansion maps between analytic stages -/

section ReexpandMap

variable {k : ℕ} (σ : ZMod (p ^ k) → ZMod (p ^ h)) (s t : ZMod (p ^ k) → ℤ_[p])

omit [CompleteSpace E] in
private theorem norm_reexpand_apply_le (c : AnalyticStage p h E) (i : ZMod (p ^ k) × ℕ) :
    ‖reexpand (s i.1) (t i.1) (fun n ↦ c (σ i.1, n)) i.2‖ ≤ ‖c‖ :=
  (norm_reexpand_le _ _ (norm_nonneg c) fun _ _ ↦ c.norm_coe_le_norm _).trans <|
    mul_le_of_le_one_left (norm_nonneg c) (pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one _))

omit [CompleteSpace E] in
private theorem tendsto_reexpand_apply (c : AnalyticStage p h E) :
    Tendsto (fun i : ZMod (p ^ k) × ℕ ↦ reexpand (s i.1) (t i.1) (fun n ↦ c (σ i.1, n)) i.2)
      cofinite (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε ↦ ?_
  have hc := NormedAddGroup.tendsto_nhds_zero.mp c.tendsto_cofinite (ε / 2) (half_pos hε)
  rw [eventually_cofinite] at hc ⊢
  -- Beyond the degrees of the finitely many large coefficients of `c`, every re-expanded
  -- coefficient is small, uniformly in the disc.
  obtain ⟨N, hN⟩ := (hc.image Prod.snd).bddAbove
  refine (Set.finite_univ.prod (Set.finite_Iic N)).subset fun i hi ↦ ⟨trivial, ?_⟩
  by_contra hiN
  rw [Set.mem_Iic, not_le] at hiN
  refine hi (((norm_reexpand_le _ _ (half_pos hε).le fun n hn ↦ ?_).trans
    (mul_le_of_le_one_left (half_pos hε).le (pow_le_one₀ (norm_nonneg _)
      (PadicInt.norm_le_one _)))).trans_lt (half_lt_self hε))
  by_contra hcn
  have hmem : (σ i.1, n) ∈ {x | ¬‖c x‖ < ε / 2} := not_lt.mpr (not_le.mp hcn).le
  have := hN ⟨_, hmem, rfl⟩
  omega

/-- The pullback `LA_h(E) →L[S] LA_k(E)` along a self-map of `ℤ_p` that sends the disc of each
class `b` of level `k` into the disc of `σ b` of level `h`, affinely in the disc coordinates as
`w ↦ s b + t b w`. The series `∑ₙ c(σ b, n) vⁿ` becomes `∑ₙ c(σ b, n) (s b + t b w)ⁿ`, whose
coefficient of `wʲ` is the re-expansion `∑ₙ (n choose j) (s b)ⁿ⁻ʲ (t b)ʲ • c(σ b, n)`. -/
noncomputable def reexpandMap : AnalyticStage p h E →L[S] AnalyticStage p k E :=
  let L : AnalyticStage p h E →ₗ[S] AnalyticStage p k E :=
    { toFun c := ZeroAtInftyContinuousMap.mkOfDiscrete _ (tendsto_reexpand_apply σ s t c)
      map_add' c d := by
        ext i
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, reexpand, FunLike.coe_add,
          Pi.add_apply, smul_add]
        exact (summable_smul_apply c _ _).tsum_add (summable_smul_apply d _ _)
      map_smul' r c := by
        ext i
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, reexpand, FunLike.coe_smul,
          Pi.smul_apply, RingHom.id_apply, smul_comm _ r]
        exact (summable_smul_apply c _ _).tsum_const_smul r }
  { L with
    cont := AddMonoidHomClass.continuous_of_bound L 1 fun c ↦ by
      rw [one_mul]
      refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦ ?_
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
      exact norm_reexpand_apply_le σ s t c i }

/-- The coefficients of `reexpandMap S σ s t c` on the disc of `b` re-expand those of `c` on the
disc of `σ b` along `s b + t b w`. -/
@[simp]
theorem reexpandMap_apply (c : AnalyticStage p h E) (b : ZMod (p ^ k)) (j : ℕ) :
    reexpandMap S σ s t c (b, j) = reexpand (s b) (t b) (fun n ↦ c (σ b, n)) j :=
  congrFun (ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _) (b, j)

/-- A re-expansion map does not increase norms. -/
theorem norm_reexpandMap_le (c : AnalyticStage p h E) : ‖reexpandMap S σ s t c‖ ≤ ‖c‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i ↦
    reexpandMap_apply S σ s t c i.1 i.2 ▸ norm_reexpand_apply_le σ s t c i

/-- A re-expansion map evaluates on the disc of `b` to `c` evaluated at the affine image
`(σ b).val + pʰ (s b + t b w)` of the point `b.val + pᵏ w`. -/
theorem eval_reexpandMap_natCast_val_add_mul (c : AnalyticStage p h E) (b : ZMod (p ^ k))
    (w : ℤ_[p]) :
    eval S (reexpandMap S σ s t c) ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ k * w) =
      eval S c (((σ b).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (s b + t b * w)) := by
  simp only [eval_natCast_val_add_mul, reexpandMap_apply]
  exact tsum_pow_smul_reexpand (tendsto_apply_mk c _) _ _ w

end ReexpandMap

/-! ### Raising the level -/

/-- The transition `LA_h(E) → LA_{h+1}(E)`. The disc of `a ∈ ZMod (pʰ)` is the union of the discs
of the classes `a' = a + pʰ b`, `0 ≤ b < p`, in `ZMod (p ^ (h + 1))`, where `b = ⌊a'.val / pʰ⌋`.
On the disc of `a'` the coordinates are related by `w = b + p v`, and the transition re-expands
`∑ₖ c(a, k) wᵏ` in powers of `v`:

`d(a', j) = ∑ₖ (k choose j) b^(k - j) pʲ • c(a, k)`. -/
noncomputable def transition : AnalyticStage p h E →L[S] AnalyticStage p (h + 1) E :=
  reexpandMap S (fun a' ↦ (a'.val : ZMod (p ^ h))) (fun a' ↦ ((a'.val / p ^ h : ℕ) : ℤ_[p]))
    fun _ ↦ (p : ℤ_[p])

/-- The re-expansion formula for the transition: on the disc of `a'`, the transition re-expands
the coefficients on the disc of level `h` containing it along `⌊a'.val / pʰ⌋ + p v`. -/
theorem transition_apply (c : AnalyticStage p h E) (a' : ZMod (p ^ (h + 1))) (j : ℕ) :
    transition S c (a', j) =
      reexpand ((a'.val / p ^ h : ℕ) : ℤ_[p]) p (fun k ↦ c ((a'.val : ZMod (p ^ h)), k)) j := by
  rw [transition, reexpandMap_apply]

/-- The re-expansion formula for the transition, as a convergent series in the re-expansion
scalars `reexpandScalar`. -/
theorem hasSum_transition_apply (c : AnalyticStage p h E) (a' : ZMod (p ^ (h + 1))) (j : ℕ) :
    HasSum (fun k ↦ reexpandScalar ((a'.val / p ^ h : ℕ) : ℤ_[p]) p k j •
      c ((a'.val : ZMod (p ^ h)), k)) (transition S c (a', j)) := by
  rw [transition_apply, reexpand_def]
  exact (summable_smul_apply c _ _).hasSum

/-- On the subdisc with the same natural centre, re-expansion multiplies the degree-`j`
coefficient by `p^j`. -/
@[simp]
theorem transition_apply_cast (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (j : ℕ) :
    transition S c ((a.cast : ZMod (p ^ (h + 1))), j) = (p : ℤ_[p]) ^ j • c (a, j) := by
  have hval : (a.cast : ZMod (p ^ (h + 1))).val = a.val :=
    ZMod.val_cast_eq_val_of_lt <| (ZMod.val_lt a).trans_le
      (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ h))
  rw [transition_apply, hval, Nat.div_eq_of_lt (ZMod.val_lt a), Nat.cast_zero, reexpand_zero_left,
    ZMod.natCast_zmod_val]

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
  rw [transition_apply]
  exact norm_reexpand_le _ _ (norm_nonneg c) fun _ _ ↦ c.norm_coe_le_norm _

/-- The transition does not increase norms. -/
theorem norm_transition_le (c : AnalyticStage p h E) : ‖transition S c‖ ≤ ‖c‖ :=
  norm_reexpandMap_le S _ _ _ c

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
    simp only [ContinuousLinearMap.comp_apply, compLeft_single, compLeft_apply, transition_apply,
      reexpand_def]
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
  rw [PadicInt.discHomeomorph_apply, transition, eval_reexpandMap_natCast_val_add_mul, hx]

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

/-! ### Projecting onto the discs of a set of classes -/

section IndicatorCLM

open ZeroAtInftyContinuousMap

/-- Projecting onto the discs of a set `U` of classes of level `h` evaluates to the product of the
function with the indicator of the union of these discs. -/
@[simp]
theorem eval_indicatorCLM (U : Set (ZMod (p ^ h))) (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval S (indicatorCLM S (Prod.fst ⁻¹' U) c) x =
      (PadicInt.toZModPow h ⁻¹' U).indicator (eval S c) x := by
  obtain ⟨⟨a, w⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  classical
  rw [PadicInt.discHomeomorph_apply, Set.indicator_apply, Set.mem_preimage,
    PadicInt.toZModPow_natCast_val_add_mul, eval_natCast_val_add_mul, eval_natCast_val_add_mul]
  by_cases ha : a ∈ U <;> simp [ha]

/-- Re-expanding a vector projected onto the discs of a set `U` of classes of level `h` projects
the re-expansion onto the discs of level `h + 1` lying in them. -/
theorem transition_indicatorCLM (U : Set (ZMod (p ^ h))) (c : AnalyticStage p h E) :
    transition S (indicatorCLM S (Prod.fst ⁻¹' U) c) =
      indicatorCLM S
        (Prod.fst ⁻¹' ((fun b : ZMod (p ^ (h + 1)) ↦ (ZMod.cast b : ZMod (p ^ h))) ⁻¹' U))
        (transition S c) := by
  ext ⟨a', j⟩
  by_cases ha : (ZMod.cast a' : ZMod (p ^ h)) ∈ U <;> simp [transition_apply, ha, reexpand_def]

/-- Re-expanding a vector projected onto the discs of a set `U` of classes of level `h` to a level
`k ≥ h` projects the re-expansion onto the discs of level `k` lying in them. -/
theorem transitionLE_indicatorCLM (hhk : h ≤ k) (U : Set (ZMod (p ^ h)))
    (c : AnalyticStage p h E) :
    transitionLE S hhk (indicatorCLM S (Prod.fst ⁻¹' U) c) =
      indicatorCLM S (Prod.fst ⁻¹' ((fun b : ZMod (p ^ k) ↦ (ZMod.cast b : ZMod (p ^ h))) ⁻¹' U))
        (transitionLE S hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, ih, transition_indicatorCLM,
      ContinuousLinearMap.comp_apply]
    congr 3
    ext b
    simp only [Set.mem_preimage,
      ZMod.cast_cast_of_dvd (pow_dvd_pow p hhk) (pow_dvd_pow p k.le_succ)]

end IndicatorCLM

end AnalyticStage

namespace AnalyticStage

/-! ### Row decomposition and level-`0` stages -/

section Coords

variable {E : Type*} [NormedAddCommGroup E] (S : Type*) [Semiring S] [Module S E]
  [ContinuousConstSMul S E]

variable (p) in
/-- **Disc-row decomposition of an analytic stage.** A coefficient vector in `LA_h(E)` is
isometrically a finite family `ZMod (p ^ h) → C₀(ℕ, E)` of null sequences, one per disc. -/
noncomputable def rowsEquiv (h : ℕ) : AnalyticStage p h E ≃ₗᵢ[S] (ZMod (p ^ h) → C₀(ℕ, E)) :=
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  (ZeroAtInftyContinuousMap.curryEquiv S E).trans
    (ZeroAtInftyContinuousMap.equivFunOnFintype S C₀(ℕ, E))

/-- Evaluating `rowsEquiv p S h c` at `(a, n)` reads the coefficient `c (a, n)`. -/
@[simp] theorem rowsEquiv_apply {h : ℕ} (c : AnalyticStage p h E) (a : ZMod (p ^ h)) (n : ℕ) :
    rowsEquiv p S h c a n = c (a, n) := by simp [rowsEquiv]

/-- Assembling rows via `(rowsEquiv p S h).symm` evaluates `f` at `(i.1, i.2)`. -/
@[simp] theorem rowsEquiv_symm_apply {h : ℕ} (f : ZMod (p ^ h) → C₀(ℕ, E)) (i : ZMod (p ^ h) × ℕ) :
    (rowsEquiv p S h).symm f i = f i.1 i.2 := by simp [rowsEquiv]

omit hp in
variable (p) in
/-- **At level `0` there is a single disc (`ZMod 1` is a singleton)**, so `LA_0(E)` is
isometrically `C₀(ℕ, E)`. -/
noncomputable def levelZeroEquiv : AnalyticStage p 0 E ≃ₗᵢ[S] C₀(ℕ, E) :=
  ZeroAtInftyContinuousMap.congrLeft S E
    { toFun := Prod.snd, invFun := fun n ↦ (0, n)
      left_inv := fun ⟨_, _⟩ ↦ by
        have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
        exact Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_snd
      continuous_invFun := Continuous.prodMk continuous_const continuous_id }

omit hp in
/-- At level `0`, `levelZeroEquiv` reads the coefficient on the unique disc `0`. -/
@[simp] theorem levelZeroEquiv_apply (c : AnalyticStage p 0 E) (n : ℕ) :
    levelZeroEquiv p S c n = c (0, n) := by
  rw [levelZeroEquiv, ZeroAtInftyContinuousMap.congrLeft_apply]; rfl

omit hp in
/-- Evaluating `(levelZeroEquiv p S).symm c` at `i` projects onto the degree `i.2`. -/
-- Apply before `simp` normalizes the dependent index `p ^ 0` in the function coercion.
@[simp↓] theorem levelZeroEquiv_symm_apply (c : C₀(ℕ, E)) (i : ZMod (p ^ 0) × ℕ) :
    (levelZeroEquiv p S).symm c i = c i.2 := by
  rw [levelZeroEquiv, ZeroAtInftyContinuousMap.congrLeft_symm,
    ZeroAtInftyContinuousMap.congrLeft_apply]; rfl

variable [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
  [SMulCommClass ℤ_[p] S E]

/-- At level `0`, `(levelZeroEquiv p S).symm c` evaluates at `x : ℤ_p` as `∑ₙ xⁿ • cₙ`. -/
theorem hasSum_eval_levelZeroEquiv_symm (c : C₀(ℕ, E)) (x : ℤ_[p]) :
    HasSum (fun n ↦ x ^ n • c n) (eval S ((levelZeroEquiv p S).symm c) x) := by
  have : NeZero (p ^ 0) := ⟨by simp⟩
  have hx : ((0 : ZMod (p ^ 0)).val : ℤ_[p]) + (p : ℤ_[p]) ^ 0 * x = x := by rw [pow_zero]; simp
  simpa only [levelZeroEquiv_symm_apply, hx] using
    hasSum_eval_natCast_val_add_mul S ((levelZeroEquiv p S).symm c) 0 x

/-- At level `0`, `eval S ((levelZeroEquiv p S).symm c) x = ∑' n, x ^ n • c n`. -/
theorem eval_levelZeroEquiv_symm_apply (c : C₀(ℕ, E)) (x : ℤ_[p]) :
    eval S ((levelZeroEquiv p S).symm c) x = ∑' n, x ^ n • c n :=
  (hasSum_eval_levelZeroEquiv_symm S c x).tsum_eq.symm

end Coords

end AnalyticStage

end TauCeti
