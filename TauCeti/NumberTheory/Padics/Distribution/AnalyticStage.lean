/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps
public import TauCeti.Analysis.Normed.Module.InfiniteSum
public import TauCeti.NumberTheory.Padics.Disc
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete

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
injective when `E` has `p`-torsion.

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
* `TauCeti.AnalyticStage.transition S`: the re-expansion `LA_h(E) →L[S] LA_{h+1}(E)`.
* `TauCeti.AnalyticStage.transitionLE S hhk`: re-expansion from level `h` to level `k` for `h ≤ k`.

## Main results

* `TauCeti.AnalyticStage.eval_natCast_val_add_mul`: on the disc of `a`, the evaluation of `c` is
  `∑ₙ wⁿ • c(a, n)`.
* `TauCeti.AnalyticStage.norm_eval_le`: evaluation does not increase norms.
* `TauCeti.AnalyticStage.transition_apply`: the re-expansion formula for the transition.
* `TauCeti.AnalyticStage.norm_transition_apply_le`: the coefficient of `vʲ` after the transition
  has norm at most `‖p‖ʲ ‖c‖`.
* `TauCeti.AnalyticStage.transition_apply_cast`: the same-centre coefficients recover
  `p^j` times the original coefficients.
* `TauCeti.AnalyticStage.transition_injective`: the transition is injective when multiplication
  by `p` on the coefficients is injective.
* `TauCeti.AnalyticStage.norm_transition_le`: the transition does not increase norms.
* `TauCeti.AnalyticStage.eval_transition`: the transition is compatible with evaluation.
* `TauCeti.AnalyticStage.transitionLE_comp`: re-expansion through an intermediate level is
  re-expansion to the final level.
* `TauCeti.AnalyticStage.norm_transitionLE_le`: every multi-level transition decreases norms.
* `TauCeti.AnalyticStage.eval_transitionLE`: every multi-level transition preserves evaluation.
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

private theorem norm_smul_le_of_norm_le_one {r : ℤ_[p]} (e : E) (hr : ‖r‖ ≤ 1) :
    ‖r • e‖ ≤ ‖e‖ :=
  (norm_smul_le r e).trans (mul_le_of_le_one_left (norm_nonneg e) hr)

private theorem norm_discTerm_le (i : ZMod (p ^ h) × ℕ) (e : E) : ‖discTerm i e‖ ≤ ‖e‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg e)).mpr fun y ↦ by
    simp only [discTerm, ContinuousMap.coe_mk]
    split_ifs
    · exact norm_smul_le_of_norm_le_one e (PadicInt.norm_le_one _)
    · simp

variable [IsUltrametricDist E] [CompleteSpace E]

private theorem summable_smul_apply (c : AnalyticStage p h E) (a : ZMod (p ^ h)) {r : ℕ → ℤ_[p]}
    (hr : ∀ n, ‖r n‖ ≤ 1) : Summable fun n ↦ r n • c (a, n) :=
  NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero <| by
    rw [Nat.cofinite_eq_atTop]
    exact squeeze_zero_norm (fun n ↦ norm_smul_le_of_norm_le_one _ (hr n))
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
          ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, smul_add,
          (hasSum_discSeries_apply _ _).tsum_eq.symm]
        exact (hasSum_discSeries_apply c _).summable.tsum_add
          (hasSum_discSeries_apply d _).summable
      map_smul' s c := by
        ext x
        simp only [ContinuousMap.comp_apply, ContinuousMap.smul_apply, RingHom.id_apply,
          ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply,
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

/-! ### Raising the level -/

/-- The re-expansion scalars `(k choose j) b^(k - j) pʲ`, the coefficient of `vʲ` in
`(b + p v)ᵏ`. -/
private noncomputable def transitionScalar (b : ℤ_[p]) (j k : ℕ) : ℤ_[p] :=
  (k.choose j : ℤ_[p]) * b ^ (k - j) * (p : ℤ_[p]) ^ j

private theorem norm_transitionScalar_le (b : ℤ_[p]) (j k : ℕ) :
    ‖transitionScalar b j k‖ ≤ ‖(p : ℤ_[p])‖ ^ j := by
  rw [transitionScalar, norm_mul, norm_mul, norm_pow (p : ℤ_[p])]
  calc _ ≤ 1 * 1 * ‖(p : ℤ_[p])‖ ^ j := by
        gcongr
        exacts [PadicInt.norm_le_one _, PadicInt.norm_le_one _]
    _ = _ := by ring

/-- `(b + p v)ᵏ` is the sum of the re-expansion terms `vʲ (k choose j) b^(k - j) pʲ`. -/
private theorem add_mul_pow_eq_sum_transitionScalar (b v : ℤ_[p]) (k : ℕ) :
    (b + p * v) ^ k = ∑ j ∈ Finset.range (k + 1), v ^ j * transitionScalar b j k := by
  rw [add_comm, add_pow]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [transitionScalar]; ring

private theorem tendsto_norm_p_pow_cofinite :
    Tendsto (fun n : ℕ ↦ ‖(p : ℤ_[p])‖ ^ n) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) PadicInt.norm_p_lt_one

private theorem tendsto_norm_pow_mul_cofinite {ι : Type*} [Finite ι] (C : ℝ) :
    Tendsto (fun i : ι × ℕ ↦ ‖(p : ℤ_[p])‖ ^ i.2 * C) cofinite (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ ‖(p : ℤ_[p])‖ ^ n * C) cofinite (𝓝 0) := by
    simpa using (tendsto_norm_p_pow_cofinite (p := p)).mul_const C
  refine hpow.comp <| Tendsto.cofinite_of_finite_preimage_singleton fun n ↦ ?_
  rw [Set.preimage_snd_singleton_eq_range]
  exact Set.finite_range _

/-- The coefficients of the re-expansion of `c` on the discs of level `h + 1`: on the disc of
`a' = a + pʰ b`, `0 ≤ b < p`, the coefficient of `vʲ` is
`∑ₖ (k choose j) b^(k - j) pʲ • c(a, k)`. -/
private noncomputable def transitionCoeff (c : AnalyticStage p h E)
    (i : ZMod (p ^ (h + 1)) × ℕ) : E :=
  ∑' k, transitionScalar ((i.1.val / p ^ h : ℕ) : ℤ_[p]) i.2 k • c ((i.1.val : ZMod (p ^ h)), k)

private theorem summable_transitionScalar_smul (c : AnalyticStage p h E) (a : ZMod (p ^ h))
    (b : ℤ_[p]) (j : ℕ) : Summable fun k ↦ transitionScalar b j k • c (a, k) :=
  summable_smul_apply c a fun _ ↦ PadicInt.norm_le_one _

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
  squeeze_zero_norm (norm_transitionCoeff_le c) (tendsto_norm_pow_mul_cofinite _)

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
          ZeroAtInftyContinuousMap.coe_add, Pi.add_apply, smul_add]
        exact (summable_transitionScalar_smul c _ _ _).tsum_add
          (summable_transitionScalar_smul d _ _ _)
      map_smul' s c := by
        ext i
        simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, transitionCoeff,
          ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_comm _ s]
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
    have hval : a'.val = a.val + p ^ h * (a'.val / p ^ h) := by
      rw [ZMod.val_natCast, Nat.mod_add_div]
    rw [hval, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    simp only [b]
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
        (g := fun k ↦ ‖c (a, k)‖) tendsto_norm_p_pow_cofinite ?_
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

/-- Re-expansion between any two analytic levels preserves the evaluated function. -/
@[simp]
theorem eval_transitionLE (hhk : h ≤ k) (c : AnalyticStage p h E) :
    eval S (transitionLE S hhk c) = eval S c := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, eval_transition, ih]

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
