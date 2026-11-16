/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transform
public import TauCeti.Topology.MetricSpace.Ultra.ContinuousMaps
import TauCeti.NumberTheory.Padics.Measure.Moments

/-!
# Additive convolution and Dirac distributions on `ℤ_p`

This file develops the additive-group operations on analytic stages and locally analytic functions
on `ℤ_p`, together with Dirac distributions and additive convolution on
`TauCeti.LocallyAnalyticDistribution p K`.

## Analytic-stage comultiplication and translation

On an analytic stage `LA_h(E) = C₀(ZMod (pʰ) × ℕ, E)`, adding two points `x = a.val + pʰ u` and
`y = b.val + pʰ v` lands in the disc of `a + b` with coordinate `q + u + v`, where
`q = ⌊(a.val + b.val) / pʰ⌋`. Expanding `(q + u + v)ᵏ` in powers of `u` and `v` defines a
linear isometry

`AnalyticStage.comul S : LA_h(E) →ₗᵢ[S] LA_h(LA_h(E))`

satisfying `eval (eval (comul c) x) y = eval c (x + y)`. Evaluating the outer stage at a fixed
`x : ℤ_p` gives the isometric translation `AnalyticStage.translate S x : LA_h(E) ≃ₗᵢ[S] LA_h(E)`,
which commutes with stage transitions and descends to `LocallyAnalytic.translate S x` on the
algebraic direct limit `LA(ℤ_p, E)`.

Structural identities for `comul` — compatibility with `transition`, coassociativity, the
translation group law, and the binomial comultiplication formula on Amice's vectors
`amiceTerm p n n e` — are proved first for `E = ℤ_p` using injectivity of stage evaluation, and
then transferred to arbitrary complete ultrametric `ℤ_p`-modules `E` (including torsion and
positive-characteristic coefficients) by naturality under `ZeroAtInftyContinuousMap.compLeft`.

## Dirac distributions and additive convolution

For a complete nontrivially normed field `K` with contractive `ℤ_p`-action:

* `LocallyAnalyticDistribution.dirac K x` is the evaluation distribution at `x : ℤ_p`, induced by
  the Dirac measure `AbstractMeasure.dirac K x`. Its Amice transform is the binomial series
  `(1 + T)ˣ` (`amiceTransform_dirac`), and every stage seminorm of `dirac K x` equals `1`
  (`stageSeminorm_dirac`).
* Given a continuous functional `φ : LA_h(K) →L[K] K`, postcomposing `comul K` coordinatewise
  with `φ` defines the bounded operator
  `convolveFunRightStage φ : LA_h(K) →L[K] LA_h(K)` of norm at most `‖φ‖`. For a distribution `ν`,
  these operators commute with stage transitions and descend to
  `convolveFunRight ν : LA(ℤ_p, K) →ₗ[K] LA(ℤ_p, K)`, sending `f` to `x ↦ ν(y ↦ f(x + y))`.
* Additive convolution `(μ * ν)(f) = μ (convolveFunRight ν f)` with identity `1 = dirac K 0`
  equips `LocallyAnalyticDistribution p K` with a `CommRing` and `Algebra K` structure extending
  its existing submodule addition and scalar multiplication without typeclass diamonds.
* The stage seminorms are submultiplicative at every fixed level `h`:
  `stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν` (`stageSeminorm_mul_le`).
* The Amice transform sends convolution to power-series multiplication (`amiceTransform_mul`,
  `amiceTransformAlgHom`), upgrading `amiceTransformEquiv` under `[NormedAlgebra ℚ_[p] K]` to a
  ring isomorphism
  `amiceTransformRingEquiv : LocallyAnalyticDistribution p K ≃+* OnOpenDisc.subring K 1`.
* `ofMulMeasure` embeds Mathlib's convolution algebra `D(Multiplicative ℤ_[p], K)` of continuous
  measures into `LocallyAnalyticDistribution p K` as an injective `K`-algebra homomorphism
  intertwining the Amice transforms (`amiceTransform_ofMulMeasure`).

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Naturality of analytic stages under bounded coefficient maps -/

namespace AnalyticStage

section CompLeft

variable {h : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [NormedAddCommGroup F] [Module ℤ_[p] F] [IsBoundedSMul ℤ_[p] F]

/-- Applying a bounded `ℤ_p`-linear map coordinatewise sends Amice's vector `e_{h,n} • e` to
`e_{h,n} • u e`. -/
@[simp]
theorem compLeft_amiceTerm (u : E →L[ℤ_[p]] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖) (n : ℕ) (e : E) :
    ZeroAtInftyContinuousMap.compLeft u hu (amiceTerm p h n e) = amiceTerm p h n (u e) := by
  ext i
  simp

variable [IsUltrametricDist E] [CompleteSpace E] [IsUltrametricDist F] [CompleteSpace F]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]
  (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass ℤ_[p] S' F]

/-- Evaluation commutes with the coordinatewise action of a bounded `ℤ_p`-linear map. -/
theorem eval_compLeft (u : E →L[ℤ_[p]] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖)
    (c : AnalyticStage p h E) (x : ℤ_[p]) :
    eval S' (ZeroAtInftyContinuousMap.compLeft u hu c) x = u (eval S c x) := by
  have h1 := hasSum_eval_apply S' (ZeroAtInftyContinuousMap.compLeft u hu c) x
  have h2 := (hasSum_eval_apply S c x).mapL u
  exact h1.unique (h2.congr_fun fun n ↦ by simp)

/-- The stage transition commutes with the coordinatewise action of a bounded `ℤ_p`-linear map. -/
theorem transition_compLeft (u : E →L[ℤ_[p]] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖)
    (c : AnalyticStage p h E) :
    transition S' (ZeroAtInftyContinuousMap.compLeft u hu c) =
      ZeroAtInftyContinuousMap.compLeft u hu (transition S c) := by
  ext ⟨a', j⟩
  rw [transition_apply, ZeroAtInftyContinuousMap.compLeft_apply, transition_apply]
  have hs : Summable fun k ↦ ((k.choose j : ℤ_[p]) *
      ((a'.val / p ^ h : ℕ) : ℤ_[p]) ^ (k - j) * (p : ℤ_[p]) ^ j) •
      c ((a'.val : ZMod (p ^ h)), k) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [Nat.cofinite_eq_atTop]
    refine squeeze_zero_norm (fun k ↦ (norm_smul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))) ?_
    rw [← tendsto_zero_iff_norm_tendsto_zero, ← Nat.cofinite_eq_atTop]
    exact c.tendsto_cofinite.comp
      (Function.Injective.tendsto_cofinite fun _ _ hn ↦ (Prod.ext_iff.mp hn).2)
  exact ((hs.hasSum.mapL u).congr_fun fun k ↦ by simp).tsum_eq

private theorem eval_eq_eval {S₁ S₂ : Type*} [Semiring S₁] [Module S₁ E] [ContinuousConstSMul S₁ E]
    [SMulCommClass ℤ_[p] S₁ E] [Semiring S₂] [Module S₂ E] [ContinuousConstSMul S₂ E]
    [SMulCommClass ℤ_[p] S₂ E] (c : AnalyticStage p h E) :
    eval S₁ c = eval S₂ c := by
  ext x
  rw [eval_apply, eval_apply]

private theorem transition_eq_transition {S₁ S₂ : Type*} [Semiring S₁] [Module S₁ E]
    [ContinuousConstSMul S₁ E] [SMulCommClass ℤ_[p] S₁ E] [Semiring S₂] [Module S₂ E]
    [ContinuousConstSMul S₂ E] [SMulCommClass ℤ_[p] S₂ E] (c : AnalyticStage p h E) :
    transition S₁ c = transition S₂ c := by
  ext ⟨a', j⟩
  rw [transition_apply, transition_apply]

end CompLeft

/-! ### Comultiplication on analytic stages -/

section Comul

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]

/-- The scalar `(k choose j) ((k - j) choose m) q^(k - j - m)`, which is the coefficient of
`uᵐ vʲ` in `(q + u + v)ᵏ`. -/
private noncomputable def shiftScalar (q : ℤ_[p]) (m j k : ℕ) : ℤ_[p] :=
  (k.choose j : ℤ_[p]) * ((k - j).choose m : ℤ_[p]) * q ^ (k - j - m)

private theorem shiftScalar_eq_zero_of_lt {q : ℤ_[p]} {m j k : ℕ} (h : k < m + j) :
    shiftScalar q m j k = 0 := by
  by_cases hkj : k < j
  · simp [shiftScalar, Nat.choose_eq_zero_of_lt hkj]
  · have hkm : k - j < m := by omega
    simp [shiftScalar, Nat.choose_eq_zero_of_lt hkm]

private theorem shiftScalar_zero_zero (j k : ℕ) :
    shiftScalar (0 : ℤ_[p]) 0 j k = if k = j then 1 else 0 := by
  by_cases hkj : k = j
  · subst hkj; simp [shiftScalar]
  · simp only [hkj, ↓reduceIte]
    by_cases hlt : k < j
    · simp [shiftScalar, Nat.choose_eq_zero_of_lt hlt]
    · have hsub : k - j ≠ 0 := by omega
      simp [shiftScalar, hsub]

private theorem add_add_pow_eq_sum_shiftScalar (q u v : ℤ_[p]) (k : ℕ) :
    (q + u + v) ^ k = ∑ m ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      u ^ m * v ^ j * shiftScalar q m j k := by
  rw [add_comm (q + u) v, add_pow, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [add_comm q u, add_pow, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_subset (Finset.range_mono (by omega : k - j + 1 ≤ k + 1))
    fun m _ hm ↦ ?_).trans (Finset.sum_congr rfl fun m _ ↦ ?_)
  · have hlt : k - j < m := by simp only [Finset.mem_range, not_lt] at hm; omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  · rw [shiftScalar]; ring

private theorem summable_shiftScalar_smul (c : AnalyticStage p h E) (d : ZMod (p ^ h))
    (q : ℤ_[p]) (m j : ℕ) :
    Summable fun k ↦ shiftScalar q m j k • c (d, k) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun k ↦ (norm_smul_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))) ?_
  rw [← tendsto_zero_iff_norm_tendsto_zero, ← Nat.cofinite_eq_atTop]
  exact c.tendsto_cofinite.comp
    (Function.Injective.tendsto_cofinite fun _ _ hn ↦ (Prod.ext_iff.mp hn).2)

/-- The `(b, j)`-th entry of the `(a, m)`-th slice of `comul c`. -/
private noncomputable def comulCoeff (c : AnalyticStage p h E)
    (i₁ i₂ : ZMod (p ^ h) × ℕ) : E :=
  ∑' k, shiftScalar (((i₁.1.val + i₂.1.val) / p ^ h : ℕ) : ℤ_[p]) i₁.2 i₂.2 k •
    c (i₁.1 + i₂.1, k)

omit hp [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E] in
private theorem exists_forall_norm_apply_le (c : AnalyticStage p h E) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (d : ZMod (p ^ h)) (k : ℕ), K ≤ k → ‖c (d, k)‖ ≤ ε := by
  have hfin : {i : ZMod (p ^ h) × ℕ | ¬‖c i‖ < ε}.Finite :=
    eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp c.tendsto_cofinite ε hε)
  refine ⟨hfin.toFinset.sup Prod.snd + 1, fun d k hk ↦ ?_⟩
  by_contra hlt
  have hmem : (d, k) ∈ hfin.toFinset := hfin.mem_toFinset.mpr (not_lt.mpr (lt_of_not_ge hlt).le)
  have hle : k ≤ hfin.toFinset.sup Prod.snd := Finset.le_sup (f := Prod.snd) hmem
  omega

omit [CompleteSpace E] in
private theorem norm_comulCoeff_le_of_le (c : AnalyticStage p h E) {K : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ (d : ZMod (p ^ h)) (k : ℕ), K ≤ k → ‖c (d, k)‖ ≤ ε)
    {i₁ i₂ : ZMod (p ^ h) × ℕ} (hK : K ≤ i₁.2 + i₂.2) :
    ‖comulCoeff c i₁ i₂‖ ≤ ε := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hε fun k ↦ ?_
  by_cases hk : k < i₁.2 + i₂.2
  · simp [shiftScalar_eq_zero_of_lt hk, hε]
  · exact (norm_smul_le _ _).trans <|
      (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _)).trans
        (hc (i₁.1 + i₂.1) k (by omega))

omit [CompleteSpace E] in
private theorem norm_comulCoeff_le (c : AnalyticStage p h E) (i₁ i₂ : ZMod (p ^ h) × ℕ) :
    ‖comulCoeff c i₁ i₂‖ ≤ ‖c‖ :=
  norm_comulCoeff_le_of_le c (norm_nonneg c) (fun d k _ ↦ c.norm_coe_le_norm (d, k)) (Nat.zero_le _)

omit [CompleteSpace E] in
private theorem tendsto_comulCoeff (c : AnalyticStage p h E) (i₁ : ZMod (p ^ h) × ℕ) :
    Tendsto (comulCoeff c i₁) cofinite (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε ↦ eventually_cofinite.mpr ?_
  obtain ⟨K, hK⟩ := exists_forall_norm_apply_le c (half_pos hε)
  have hfin : {i₂ : ZMod (p ^ h) × ℕ | i₂.2 < K}.Finite :=
    (Set.finite_univ.prod (Set.finite_lt_nat K)).subset fun i₂ hi₂ ↦ ⟨trivial, hi₂⟩
  refine hfin.subset fun i₂ hi₂ ↦ ?_
  by_contra hlt
  have hle : K ≤ i₁.2 + i₂.2 := by simp only [Set.mem_ofPred_eq, not_lt] at hlt; omega
  exact hi₂ ((norm_comulCoeff_le_of_le c (half_pos hε).le hK hle).trans_lt (half_lt_self hε))

/-- The `i₁`-th slice of `comul c`, an element of `LA_h(E)`. -/
private noncomputable def comulSlice (c : AnalyticStage p h E) (i₁ : ZMod (p ^ h) × ℕ) :
    AnalyticStage p h E :=
  ZeroAtInftyContinuousMap.mkOfDiscrete (comulCoeff c i₁) (tendsto_comulCoeff c i₁)

omit [CompleteSpace E] in
private theorem norm_comulSlice_le (c : AnalyticStage p h E) (i₁ : ZMod (p ^ h) × ℕ) :
    ‖comulSlice c i₁‖ ≤ ‖c‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i₂ ↦ by
    rw [comulSlice, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
    exact norm_comulCoeff_le c i₁ i₂

omit [CompleteSpace E] in
private theorem tendsto_comulSlice (c : AnalyticStage p h E) :
    Tendsto (comulSlice c) cofinite (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε ↦ eventually_cofinite.mpr ?_
  obtain ⟨K, hK⟩ := exists_forall_norm_apply_le c (half_pos hε)
  have hfin : {i₁ : ZMod (p ^ h) × ℕ | i₁.2 < K}.Finite :=
    (Set.finite_univ.prod (Set.finite_lt_nat K)).subset fun i₁ hi₁ ↦ ⟨trivial, hi₁⟩
  refine hfin.subset fun i₁ hi₁ ↦ ?_
  by_contra hlt
  have hle : K ≤ i₁.2 := by simpa only [Set.mem_ofPred_eq, not_lt] using hlt
  have hslice : ‖comulSlice c i₁‖ ≤ ε / 2 :=
    (ZeroAtInftyContinuousMap.norm_le (half_pos hε).le).mpr fun i₂ ↦ by
      rw [comulSlice, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
      exact norm_comulCoeff_le_of_le c (half_pos hε).le hK (by omega)
  exact hi₁ (hslice.trans_lt (half_lt_self hε))

omit [CompleteSpace E] in
private theorem comulSlice_zero_zero (c : AnalyticStage p h E) :
    comulSlice c (0, 0) = c := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  ext ⟨b, j⟩
  simp only [comulSlice, ZeroAtInftyContinuousMap.coe_mkOfDiscrete, comulCoeff,
    ZMod.val_zero, zero_add, Nat.div_eq_of_lt (ZMod.val_lt b), Nat.cast_zero,
    shiftScalar_zero_zero]
  rw [tsum_eq_single j]
  · simp
  · intro k hkj
    simp [hkj]

variable (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **Comultiplication on an analytic stage.** Expanding `f(x + y)` in the disc coordinates of `x`
and `y` gives a linear isometry `LA_h(E) →ₗᵢ[S] LA_h(LA_h(E))` satisfying
`eval (eval (comul S c) x) y = eval S c (x + y)` (`eval_eval_comul`). -/
noncomputable def comul : AnalyticStage p h E →ₗᵢ[S] AnalyticStage p h (AnalyticStage p h E) where
  toFun c := ZeroAtInftyContinuousMap.mkOfDiscrete (comulSlice c) (tendsto_comulSlice c)
  map_add' c d := by
    ext i₁ i₂
    simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, comulSlice, comulCoeff,
      FunLike.coe_add, Pi.add_apply, smul_add]
    exact (summable_shiftScalar_smul c _ _ _ _).tsum_add (summable_shiftScalar_smul d _ _ _ _)
  map_smul' s c := by
    ext i₁ i₂
    simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, comulSlice, comulCoeff,
      FunLike.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_comm _ s]
    exact (summable_shiftScalar_smul c _ _ _ _).tsum_const_smul s
  norm_map' c := by
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    refine le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg c)).mpr fun i₁ ↦ ?_) ?_
    · rw [ZeroAtInftyContinuousMap.coe_mkOfDiscrete]
      exact norm_comulSlice_le c i₁
    · have h0 := ZeroAtInftyContinuousMap.norm_coe_le_norm
        (ZeroAtInftyContinuousMap.mkOfDiscrete (comulSlice c) (tendsto_comulSlice c)) (0, 0)
      rw [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, comulSlice_zero_zero] at h0
      exact h0

private theorem coe_comul (c : AnalyticStage p h E) : ⇑(comul S c) = comulSlice c :=
  ZeroAtInftyContinuousMap.coe_mkOfDiscrete _ _

/-- The `(0, 0)`-entry of `comul S c` recovers `c`. -/
@[simp]
theorem comul_apply_zero_zero (c : AnalyticStage p h E) :
    comul S c (0, 0) = c := by
  rw [coe_comul, comulSlice_zero_zero]

/-- The explicit coefficient formula for `comul S c`. -/
theorem comul_apply_apply (c : AnalyticStage p h E) (a b : ZMod (p ^ h)) (m j : ℕ) :
    comul S c (a, m) (b, j) =
      ∑' k, ((k.choose j : ℤ_[p]) * ((k - j).choose m : ℤ_[p]) *
        (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) ^ (k - j - m)) • c (a + b, k) := by
  simp only [coe_comul, comulSlice, ZeroAtInftyContinuousMap.coe_mkOfDiscrete, comulCoeff,
    shiftScalar]

private theorem comul_eq_comul {S₁ S₂ : Type*} [Semiring S₁] [Module S₁ E]
    [ContinuousConstSMul S₁ E] [SMulCommClass ℤ_[p] S₁ E] [Semiring S₂] [Module S₂ E]
    [ContinuousConstSMul S₂ E] [SMulCommClass ℤ_[p] S₂ E] (c : AnalyticStage p h E) :
    comul S₁ c = comul S₂ c := by
  ext ⟨a, m⟩ ⟨b, j⟩
  rw [comul_apply_apply, comul_apply_apply]

private theorem comul_single_apply_apply (d : ZMod (p ^ h)) (N : ℕ) (e : E)
    (a b : ZMod (p ^ h)) (m j : ℕ) :
    comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m) (b, j) =
      if a + b = d then
        shiftScalar (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) m j N • e
      else 0 := by
  rw [coe_comul, comulSlice, ZeroAtInftyContinuousMap.coe_mkOfDiscrete, comulCoeff,
    tsum_eq_single N]
  · by_cases hab : a + b = d <;> simp [hab]
  · intro k hk
    have hne : (a + b, k) ≠ (d, N) := fun h ↦ hk (Prod.ext_iff.mp h).2
    simp [ZeroAtInftyContinuousMap.single_eq_of_ne hne]

omit [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E]
  [CompleteSpace E] [Semiring S] [Module S E] [ContinuousConstSMul S E]
  [SMulCommClass ℤ_[p] S E] in
private theorem discHomeomorph_add_eq (a b : ZMod (p ^ h)) (u v : ℤ_[p]) :
    ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u) + ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) =
      ((a + b).val : ℤ_[p]) +
        (p : ℤ_[p]) ^ h * ((((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) + u + v) := by
  have : NeZero (p ^ h) := ⟨pow_ne_zero h hp.out.ne_zero⟩
  have hval : a.val + b.val = (a + b).val + p ^ h * ((a.val + b.val) / p ^ h) := by
    rw [ZMod.val_add, Nat.mod_add_div]
  have hcast : (a.val : ℤ_[p]) + (b.val : ℤ_[p]) =
      ((a + b).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) := by
    have hc := congrArg (Nat.cast (R := ℤ_[p])) hval
    push_cast at hc
    exact hc
  calc
    ((a.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * u) + ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v)
        = ((a.val : ℤ_[p]) + (b.val : ℤ_[p])) + (p : ℤ_[p]) ^ h * (u + v) := by ring
    _ = ((a + b).val : ℤ_[p]) + (p : ℤ_[p]) ^ h * (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) +
          (p : ℤ_[p]) ^ h * (u + v) := by rw [hcast]
    _ = ((a + b).val : ℤ_[p]) +
          (p : ℤ_[p]) ^ h * ((((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) + u + v) := by ring

private theorem comul_single_eq_zero_of_lt (d : ZMod (p ^ h)) {N m : ℕ} (hNm : N < m) (e : E)
    (a : ZMod (p ^ h)) :
    comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m) = 0 := by
  ext ⟨b', j⟩
  rw [comul_single_apply_apply]
  split_ifs
  · simp [shiftScalar_eq_zero_of_lt (by omega : N < m + j)]
  · rfl

private theorem eval_comul_single_apply (d : ZMod (p ^ h)) (N m : ℕ) (e : E)
    (a b : ZMod (p ^ h)) (u v : ℤ_[p]) :
    u ^ m • eval S (comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m))
      ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) =
    if a + b = d then
      ∑ j ∈ Finset.range (N + 1),
        (u ^ m * v ^ j * shiftScalar (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p]) m j N) • e
    else 0 := by
  rw [eval_natCast_val_add_mul]
  rw [tsum_eq_sum (s := Finset.range (N + 1)) fun j hj ↦ by
    have hNj : N < j := by simp only [Finset.mem_range, not_lt] at hj; omega
    rw [comul_single_apply_apply]
    split_ifs
    · simp [shiftScalar_eq_zero_of_lt (by omega : N < m + j)]
    · simp]
  by_cases hab : a + b = d
  · simp only [hab, ↓reduceIte, comul_single_apply_apply, Finset.smul_sum, smul_smul, mul_assoc]
  · simp [hab, comul_single_apply_apply]

private theorem eval_eval_comul_single (d : ZMod (p ^ h)) (N : ℕ) (e : E) (x y : ℤ_[p]) :
    eval S (eval S (comul S (ZeroAtInftyContinuousMap.single (d, N) e)) x) y =
      eval S (ZeroAtInftyContinuousMap.single (d, N) e) (x + y) := by
  obtain ⟨⟨a, u⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective x
  obtain ⟨⟨b, v⟩, rfl⟩ := (PadicInt.discHomeomorph p h).surjective y
  set q : ℤ_[p] := (((a.val + b.val) / p ^ h : ℕ) : ℤ_[p])
  simp only [PadicInt.discHomeomorph_apply]
  rw [discHomeomorph_add_eq a b u v,
    eval_natCast_val_add_mul S (comul S (ZeroAtInftyContinuousMap.single (d, N) e)) a u,
    eval_natCast_val_add_mul S (ZeroAtInftyContinuousMap.single (d, N) e) (a + b) (q + u + v)]
  let evY : AnalyticStage p h E →L[ℤ_[p]] E :=
    (ContinuousMap.evalCLM ℤ_[p] ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v)).comp (eval ℤ_[p])
  have houter : eval S (∑' m, u ^ m • comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m))
      ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) =
      ∑' m, u ^ m • eval S (comul S (ZeroAtInftyContinuousMap.single (d, N) e) (a, m))
        ((b.val : ℤ_[p]) + (p : ℤ_[p]) ^ h * v) := by
    have hsum := (hasSum_eval_natCast_val_add_mul S
      (comul S (ZeroAtInftyContinuousMap.single (d, N) e)) a u).summable
    simpa only [evY, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
      map_smul, eval_eq_eval (S₁ := ℤ_[p]) (S₂ := S)] using ((hsum.hasSum.mapL evY).tsum_eq).symm
  rw [houter, tsum_eq_sum (s := Finset.range (N + 1)) fun m hm ↦ by
    have hNm : N < m := by simp only [Finset.mem_range, not_lt] at hm; omega
    simp [comul_single_eq_zero_of_lt S d hNm]]
  have hrhs : ∑' k, (q + u + v) ^ k • ZeroAtInftyContinuousMap.single (d, N) e (a + b, k) =
      if a + b = d then (q + u + v) ^ N • e else 0 := by
    rw [tsum_eq_single N]
    · by_cases hab : a + b = d <;> simp [hab]
    · intro k hk
      have hne : (a + b, k) ≠ (d, N) := fun h ↦ hk (Prod.ext_iff.mp h).2
      simp [ZeroAtInftyContinuousMap.single_eq_of_ne hne]
  rw [hrhs]
  simp_rw [eval_comul_single_apply S d N _ e a b u v]
  split_ifs with hab
  · simp_rw [← Finset.sum_smul, ← add_add_pow_eq_sum_shiftScalar, q]
  · simp

/-- Evaluating `comul S c` at `x` and then at `y` equals evaluating `c` at `x + y`. -/
@[simp]
theorem eval_eval_comul (c : AnalyticStage p h E) (x y : ℤ_[p]) :
    eval S (eval S (comul S c) x) y = eval S c (x + y) := by
  let L₁ : AnalyticStage p h E →L[ℤ_[p]] E :=
    ((ContinuousMap.evalCLM ℤ_[p] y).comp (eval ℤ_[p])).comp
      (((ContinuousMap.evalCLM ℤ_[p] x).comp (eval ℤ_[p])).comp
        (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap)
  let L₂ : AnalyticStage p h E →L[ℤ_[p]] E :=
    (ContinuousMap.evalCLM ℤ_[p] (x + y)).comp (eval ℤ_[p])
  have hEq : L₁ = L₂ := ZeroAtInftyContinuousMap.continuousLinearMap_ext fun ⟨d, N⟩ e ↦
    eval_eval_comul_single ℤ_[p] d N e x y
  simpa only [L₁, L₂, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
    LinearIsometry.coe_toContinuousLinearMap, comul_eq_comul (S₁ := ℤ_[p]) (S₂ := S),
    eval_eq_eval (S₁ := ℤ_[p]) (S₂ := S)] using DFunLike.congr_fun hEq c

/-- Comultiplication commutes with the coordinatewise action of a bounded `ℤ_p`-linear map. -/
theorem comul_compLeft {F : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F] [IsBoundedSMul ℤ_[p] F]
    [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass ℤ_[p] S' F]
    (u : E →L[ℤ_[p]] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖) (c : AnalyticStage p h E) :
    comul S' (ZeroAtInftyContinuousMap.compLeft u hu c) =
      ZeroAtInftyContinuousMap.compLeft
        (ZeroAtInftyContinuousMap.compLeft u hu)
        (ZeroAtInftyContinuousMap.exists_norm_compLeft_apply_le u hu)
        (comul S c) := by
  ext ⟨a, m⟩ ⟨b, j⟩
  rw [ZeroAtInftyContinuousMap.compLeft_apply, ZeroAtInftyContinuousMap.compLeft_apply,
    coe_comul, coe_comul, comulSlice, comulSlice, ZeroAtInftyContinuousMap.coe_mkOfDiscrete,
    ZeroAtInftyContinuousMap.coe_mkOfDiscrete, comulCoeff, comulCoeff]
  exact (((summable_shiftScalar_smul c (a + b) _ m j).hasSum.mapL u).congr_fun
    fun k ↦ by simp).tsum_eq

private theorem isSMulRegular_p_padicInt : IsSMulRegular ℤ_[p] (p : ℤ_[p]) :=
  fun _ _ hxy ↦ mul_left_cancel₀ (by exact_mod_cast hp.out.ne_zero : (p : ℤ_[p]) ≠ 0) hxy

private theorem isSMulRegular_p_stage {k : ℕ} {M : Type*} [NormedAddCommGroup M] [Module ℤ_[p] M]
    [IsBoundedSMul ℤ_[p] M] (hM : IsSMulRegular M (p : ℤ_[p])) :
    IsSMulRegular (AnalyticStage p k M) (p : ℤ_[p]) :=
  fun _ _ hcd ↦ ZeroAtInftyContinuousMap.ext fun i ↦ hM (DFunLike.congr_fun hcd i)

omit [IsUltrametricDist E] [CompleteSpace E] in
private theorem norm_toSpanSingleton_padicInt_le (e : E) (r : ℤ_[p]) :
    ‖ContinuousLinearMap.toSpanSingleton ℤ_[p] e r‖ ≤ ‖e‖ * ‖r‖ := by
  rw [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  exact norm_smul_le r e

private theorem comul_transition_padicInt (c : AnalyticStage p h ℤ_[p]) :
    comul ℤ_[p] (transition ℤ_[p] c) =
      ZeroAtInftyContinuousMap.compLeft (transition ℤ_[p]) ⟨1, fun d ↦ by
        simpa using norm_transition_le ℤ_[p] d⟩ (transition ℤ_[p] (comul ℤ_[p] c)) := by
  have hreg1 := isSMulRegular_p_stage (p := p) (k := h + 1) (isSMulRegular_p_padicInt (p := p))
  apply eval_injective ℤ_[p] hreg1
  ext x : 1
  apply eval_injective ℤ_[p] (isSMulRegular_p_padicInt (p := p))
  ext y
  rw [eval_eval_comul, eval_transition, eval_compLeft ℤ_[p] ℤ_[p], eval_transition,
    eval_transition, eval_eval_comul]

/-- Comultiplication commutes with stage transitions: refining before comultiplying equals
refining both the outer and inner analytic stages after comultiplying. -/
theorem comul_transition (c : AnalyticStage p h E) :
    comul S (transition S c) =
      ZeroAtInftyContinuousMap.compLeft (transition S) ⟨1, fun d ↦ by
        simpa using norm_transition_le S d⟩ (transition S (comul S c)) := by
  let L₁ : AnalyticStage p h E →L[ℤ_[p]] AnalyticStage p (h + 1) (AnalyticStage p (h + 1) E) :=
    (comul (p := p) (h := h + 1) (E := E) ℤ_[p]).toContinuousLinearMap.comp (transition ℤ_[p])
  let L₂ : AnalyticStage p h E →L[ℤ_[p]] AnalyticStage p (h + 1) (AnalyticStage p (h + 1) E) :=
    (ZeroAtInftyContinuousMap.compLeft (transition ℤ_[p]) ⟨1, fun d ↦ by
      simpa using norm_transition_le ℤ_[p] d⟩).comp
      ((transition ℤ_[p]).comp (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap)
  have hEq : L₁ = L₂ := ZeroAtInftyContinuousMap.continuousLinearMap_ext fun i e ↦ by
    let u := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
    have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ := ⟨‖e‖, norm_toSpanSingleton_padicInt_le e⟩
    have hsingle : ZeroAtInftyContinuousMap.single i e =
        ZeroAtInftyContinuousMap.compLeft u hu (ZeroAtInftyContinuousMap.single i (1 : ℤ_[p])) := by
      simp [u]
    simp only [L₁, L₂, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [hsingle, transition_compLeft ℤ_[p] ℤ_[p], comul_compLeft ℤ_[p] ℤ_[p],
      comul_transition_padicInt]
    rw [comul_compLeft ℤ_[p] ℤ_[p], transition_compLeft ℤ_[p] ℤ_[p]]
    ext i₁ i₂
    simp only [ZeroAtInftyContinuousMap.compLeft_apply]
    simpa only [ZeroAtInftyContinuousMap.compLeft_apply] using
      DFunLike.congr_fun (transition_compLeft ℤ_[p] ℤ_[p] u hu _).symm i₂
  have hc := DFunLike.congr_fun hEq c
  simp only [L₁, L₂, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    comul_eq_comul (S₁ := ℤ_[p]) (S₂ := S),
    transition_eq_transition (S₁ := ℤ_[p]) (S₂ := S)] at hc
  rw [hc]
  ext i₁ i₂
  simp only [ZeroAtInftyContinuousMap.compLeft_apply]
  exact DFunLike.congr_fun (transition_eq_transition (S₁ := ℤ_[p]) (S₂ := S) _) i₂

private theorem comul_comul_padicInt (c : AnalyticStage p h ℤ_[p]) :
    comul ℤ_[p] (comul ℤ_[p] c) =
      ZeroAtInftyContinuousMap.compLeft
        (comul (p := p) (h := h) (E := ℤ_[p]) ℤ_[p]).toContinuousLinearMap
        ⟨1, fun d ↦ by simp⟩ (comul ℤ_[p] c) := by
  have hreg1 := isSMulRegular_p_stage (p := p) (k := h) (isSMulRegular_p_padicInt (p := p))
  have hreg2 := isSMulRegular_p_stage (p := p) (k := h) hreg1
  apply eval_injective ℤ_[p] hreg2
  ext x : 1
  apply eval_injective ℤ_[p] hreg1
  ext y : 1
  apply eval_injective ℤ_[p] (isSMulRegular_p_padicInt (p := p))
  ext z
  rw [eval_eval_comul, eval_eval_comul, eval_compLeft ℤ_[p] ℤ_[p],
    LinearIsometry.coe_toContinuousLinearMap, eval_eval_comul, eval_eval_comul, add_assoc]

/-- Comultiplication on an analytic stage is coassociative. -/
theorem comul_comul (c : AnalyticStage p h E) :
    comul S (comul S c) =
      ZeroAtInftyContinuousMap.compLeft
        (comul (p := p) (h := h) (E := E) S).toContinuousLinearMap
        ⟨1, fun d ↦ by simp⟩ (comul S c) := by
  let L₁ : AnalyticStage p h E →L[ℤ_[p]]
      AnalyticStage p h (AnalyticStage p h (AnalyticStage p h E)) :=
    (comul (p := p) (h := h) (E := AnalyticStage p h E) ℤ_[p]).toContinuousLinearMap.comp
      (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap
  let L₂ : AnalyticStage p h E →L[ℤ_[p]]
      AnalyticStage p h (AnalyticStage p h (AnalyticStage p h E)) :=
    (ZeroAtInftyContinuousMap.compLeft
      (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap
      ⟨1, fun d ↦ by simp⟩).comp
      (comul (p := p) (h := h) (E := E) ℤ_[p]).toContinuousLinearMap
  have hEq : L₁ = L₂ := ZeroAtInftyContinuousMap.continuousLinearMap_ext fun i e ↦ by
    let u := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
    have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ := ⟨‖e‖, norm_toSpanSingleton_padicInt_le e⟩
    have hsingle : ZeroAtInftyContinuousMap.single i e =
        ZeroAtInftyContinuousMap.compLeft u hu (ZeroAtInftyContinuousMap.single i (1 : ℤ_[p])) := by
      simp [u]
    simp only [L₁, L₂, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [hsingle, comul_compLeft ℤ_[p] ℤ_[p], comul_compLeft ℤ_[p] ℤ_[p], comul_comul_padicInt]
    ext i₁ i₂ i₃
    simp only [ZeroAtInftyContinuousMap.compLeft_apply, LinearIsometry.coe_toContinuousLinearMap]
    simpa only [ZeroAtInftyContinuousMap.compLeft_apply] using DFunLike.congr_fun
      (DFunLike.congr_fun (comul_compLeft ℤ_[p] ℤ_[p] u hu _).symm i₂) i₃
  have hc := DFunLike.congr_fun hEq c
  simp only [L₁, L₂, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    comul_eq_comul (S₁ := ℤ_[p]) (S₂ := S)] at hc
  rw [hc]
  ext i₁ i₂ i₃
  simp only [ZeroAtInftyContinuousMap.compLeft_apply, LinearIsometry.coe_toContinuousLinearMap]
  exact DFunLike.congr_fun
    (DFunLike.congr_fun (comul_eq_comul (S₁ := ℤ_[p]) (S₂ := S) _) i₂) i₃

private theorem comul_amiceTerm_padicInt (n : ℕ) :
    comul ℤ_[p] (amiceTerm p n n (1 : ℤ_[p])) =
      ∑ ij ∈ Finset.antidiagonal n, amiceTerm p n ij.1 (amiceTerm p n ij.2 (1 : ℤ_[p])) := by
  have hreg1 := isSMulRegular_p_stage (p := p) (k := n) (isSMulRegular_p_padicInt (p := p))
  apply eval_injective ℤ_[p] hreg1
  ext x : 1
  apply eval_injective ℤ_[p] (isSMulRegular_p_padicInt (p := p))
  ext y : 1
  have hlt : n < p ^ n := Nat.lt_pow_self hp.out.one_lt
  rw [eval_eval_comul, eval_amiceTerm, map_sum, ContinuousMap.coe_sum, Finset.sum_apply,
    map_sum, ContinuousMap.coe_sum, Finset.sum_apply]
  simp only [Nat.div_eq_of_lt hlt, Nat.factorial_zero, one_nsmul, PadicInt.mahlerTerm_apply,
    mahler_apply, smul_eq_mul, mul_one, Ring.add_choose_eq n (Commute.all x y)]
  apply Finset.sum_congr rfl
  intro ij hij
  have hij' := Finset.mem_antidiagonal.mp hij
  have hi : ij.1 / p ^ n = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt (by omega) hlt)
  have hj : ij.2 / p ^ n = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt (by omega) hlt)
  rw [eval_amiceTerm, PadicInt.mahlerTerm_apply, hi, Nat.factorial_zero, one_nsmul, map_smul,
    ContinuousMap.smul_apply, eval_amiceTerm, PadicInt.mahlerTerm_apply, hj, Nat.factorial_zero,
    one_nsmul, mahler_apply, mahler_apply, smul_eq_mul, smul_eq_mul, mul_one]

/-- **Binomial comultiplication on Amice's vectors.** At level `n`, comultiplying Amice's vector
`e_{n,n} • e` splits it according to Vandermonde's identity into
`∑_{i + j = n} e_{n,i} • (e_{n,j} • e)`. No torsion-freeness of `E` is needed. -/
theorem comul_amiceTerm (n : ℕ) (e : E) :
    comul S (amiceTerm p n n e) =
      ∑ ij ∈ Finset.antidiagonal n, amiceTerm p n ij.1 (amiceTerm p n ij.2 e) := by
  let u := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
  have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ := ⟨‖e‖, norm_toSpanSingleton_padicInt_le e⟩
  have he : amiceTerm p n n e =
      ZeroAtInftyContinuousMap.compLeft u hu (amiceTerm p n n (1 : ℤ_[p])) := by
    simp [u]
  rw [he, comul_compLeft ℤ_[p] S, comul_amiceTerm_padicInt,
    map_sum (ZeroAtInftyContinuousMap.compLeft _ _)]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  simp [u]

/-! ### Translation on analytic stages -/

private noncomputable def translateCLM (x : ℤ_[p]) :
    AnalyticStage p h E →L[S] AnalyticStage p h E :=
  (ContinuousMap.evalCLM S x).comp
    ((eval S).comp (comul (p := p) (h := h) (E := E) S).toContinuousLinearMap)

private theorem translateCLM_eq {S₁ S₂ : Type*} [Semiring S₁] [Module S₁ E]
    [ContinuousConstSMul S₁ E] [SMulCommClass ℤ_[p] S₁ E] [Semiring S₂] [Module S₂ E]
    [ContinuousConstSMul S₂ E] [SMulCommClass ℤ_[p] S₂ E] (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S₁ x c = translateCLM S₂ x c := by
  simp only [translateCLM, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
    LinearIsometry.coe_toContinuousLinearMap, comul_eq_comul (S₁ := S₁) (S₂ := S₂),
    eval_eq_eval (S₁ := S₁) (S₂ := S₂)]

private theorem eval_translateCLM (x : ℤ_[p]) (c : AnalyticStage p h E) (y : ℤ_[p]) :
    eval S (translateCLM S x c) y = eval S c (x + y) :=
  eval_eval_comul S c x y

private theorem norm_translateCLM_le (x : ℤ_[p]) (c : AnalyticStage p h E) :
    ‖translateCLM S x c‖ ≤ ‖c‖ := by
  calc
    ‖translateCLM S x c‖ ≤ ‖eval S (comul S c)‖ := ContinuousMap.norm_coe_le_norm _ x
    _ ≤ ‖comul S c‖ := norm_eval_le S (comul S c)
    _ = ‖c‖ := (comul (p := p) (h := h) (E := E) S).norm_map c

private theorem translateCLM_compLeft {F : Type*} [NormedAddCommGroup F] [Module ℤ_[p] F]
    [IsBoundedSMul ℤ_[p] F] [IsUltrametricDist F] [CompleteSpace F]
    (S' : Type*) [Semiring S'] [Module S' F] [ContinuousConstSMul S' F] [SMulCommClass ℤ_[p] S' F]
    (u : E →L[ℤ_[p]] F) (hu : ∃ C, ∀ e, ‖u e‖ ≤ C * ‖e‖) (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S' x (ZeroAtInftyContinuousMap.compLeft u hu c) =
      ZeroAtInftyContinuousMap.compLeft u hu (translateCLM S x c) := by
  simp only [translateCLM, ContinuousLinearMap.comp_apply, ContinuousMap.evalCLM_apply,
    LinearIsometry.coe_toContinuousLinearMap]
  rw [comul_compLeft S S' u hu, eval_compLeft S S']

private theorem translateCLM_zero (c : AnalyticStage p h E) : translateCLM S 0 c = c := by
  have hpadic : ∀ d : AnalyticStage p h ℤ_[p], translateCLM ℤ_[p] 0 d = d := fun d ↦ by
    apply eval_injective ℤ_[p] (isSMulRegular_p_padicInt (p := p))
    ext y
    rw [eval_translateCLM, zero_add]
  let L : AnalyticStage p h E →L[ℤ_[p]] AnalyticStage p h E := translateCLM ℤ_[p] 0
  have hEq : L = ContinuousLinearMap.id ℤ_[p] _ :=
    ZeroAtInftyContinuousMap.continuousLinearMap_ext fun i e ↦ by
      let u := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
      have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ := ⟨‖e‖, norm_toSpanSingleton_padicInt_le e⟩
      have hsingle : ZeroAtInftyContinuousMap.single i e =
          ZeroAtInftyContinuousMap.compLeft u hu
            (ZeroAtInftyContinuousMap.single i (1 : ℤ_[p])) := by
        simp [u]
      simp only [L, ContinuousLinearMap.id_apply]
      rw [hsingle, translateCLM_compLeft ℤ_[p] ℤ_[p], hpadic]
  rw [← translateCLM_eq (S₁ := ℤ_[p]) (S₂ := S)]
  exact DFunLike.congr_fun hEq c

private theorem translateCLM_add (x y : ℤ_[p]) (c : AnalyticStage p h E) :
    translateCLM S (x + y) c = translateCLM S x (translateCLM S y c) := by
  have hpadic : ∀ d : AnalyticStage p h ℤ_[p],
      translateCLM ℤ_[p] (x + y) d = translateCLM ℤ_[p] x (translateCLM ℤ_[p] y d) := fun d ↦ by
    apply eval_injective ℤ_[p] (isSMulRegular_p_padicInt (p := p))
    ext z
    rw [eval_translateCLM, eval_translateCLM, eval_translateCLM, add_left_comm, add_assoc]
  let L₁ : AnalyticStage p h E →L[ℤ_[p]] AnalyticStage p h E := translateCLM ℤ_[p] (x + y)
  let L₂ : AnalyticStage p h E →L[ℤ_[p]] AnalyticStage p h E :=
    (translateCLM ℤ_[p] x).comp (translateCLM ℤ_[p] y)
  have hEq : L₁ = L₂ := ZeroAtInftyContinuousMap.continuousLinearMap_ext fun i e ↦ by
    let u := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
    have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ := ⟨‖e‖, norm_toSpanSingleton_padicInt_le e⟩
    have hsingle : ZeroAtInftyContinuousMap.single i e =
        ZeroAtInftyContinuousMap.compLeft u hu
          (ZeroAtInftyContinuousMap.single i (1 : ℤ_[p])) := by
      simp [u]
    simp only [L₁, L₂, ContinuousLinearMap.comp_apply]
    rw [hsingle, translateCLM_compLeft ℤ_[p] ℤ_[p], translateCLM_compLeft ℤ_[p] ℤ_[p],
      translateCLM_compLeft ℤ_[p] ℤ_[p], hpadic]
  rw [← translateCLM_eq (S₁ := ℤ_[p]) (S₂ := S), ← translateCLM_eq (S₁ := ℤ_[p]) (S₂ := S),
    ← translateCLM_eq (S₁ := ℤ_[p]) (S₂ := S)]
  exact DFunLike.congr_fun hEq c

/-- **Translation on an analytic stage.** Translating the argument by `x : ℤ_p` defines a linear
isometry equivalence `LA_h(E) ≃ₗᵢ[S] LA_h(E)` with `eval (translate S x c) y = eval c (x + y)`. -/
noncomputable def translate (x : ℤ_[p]) : AnalyticStage p h E ≃ₗᵢ[S] AnalyticStage p h E where
  toFun := translateCLM S x
  map_add' := map_add (translateCLM S x)
  map_smul' := map_smul (translateCLM S x)
  invFun := translateCLM S (-x)
  left_inv c := by rw [← translateCLM_add, neg_add_cancel, translateCLM_zero]
  right_inv c := by rw [← translateCLM_add, add_neg_cancel, translateCLM_zero]
  norm_map' c := le_antisymm (norm_translateCLM_le S x c) <| by
    have h := norm_translateCLM_le S (-x) (translateCLM S x c)
    rwa [← translateCLM_add, neg_add_cancel, translateCLM_zero] at h

/-- Translation of `c` by `x` is the evaluation of `comul S c` at `x`. -/
theorem translate_eq_eval_comul (x : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S x c = eval S (comul S c) x :=
  (rfl)

/-- Evaluating the translate of `c` by `x` at `y` gives `eval S c (x + y)`. -/
@[simp]
theorem eval_translate (x : ℤ_[p]) (c : AnalyticStage p h E) (y : ℤ_[p]) :
    eval S (translate S x c) y = eval S c (x + y) :=
  eval_translateCLM S x c y

/-- Translating by `0` is the identity. -/
@[simp]
theorem translate_zero (c : AnalyticStage p h E) : translate S 0 c = c :=
  translateCLM_zero S c

/-- Translations compose by addition. -/
theorem translate_add (x y : ℤ_[p]) (c : AnalyticStage p h E) :
    translate S (x + y) c = translate S x (translate S y c) :=
  translateCLM_add S x y c

/-- The inverse of translation by `x` is translation by `-x`. -/
@[simp]
theorem translate_symm (x : ℤ_[p]) :
    (translate (p := p) (h := h) (E := E) S x).symm = translate S (-x) := by
  ext c
  rfl

/-- Translation commutes with adjacent stage transitions. -/
theorem transition_translate (x : ℤ_[p]) (c : AnalyticStage p h E) :
    transition S (translate S x c) = translate S x (transition S c) := by
  rw [translate_eq_eval_comul, translate_eq_eval_comul, comul_transition]
  have htrans : ∃ C, ∀ d : AnalyticStage p h E, ‖transition ℤ_[p] d‖ ≤ C * ‖d‖ :=
    ⟨1, fun d ↦ by simpa using norm_transition_le ℤ_[p] d⟩
  have hcomp : ZeroAtInftyContinuousMap.compLeft (transition S)
      ⟨1, fun d ↦ by simpa using norm_transition_le S d⟩ (transition S (comul S c)) =
      ZeroAtInftyContinuousMap.compLeft (transition ℤ_[p]) htrans (transition S (comul S c)) := by
    ext i₁ i₂
    simp only [ZeroAtInftyContinuousMap.compLeft_apply]
    exact DFunLike.congr_fun (transition_eq_transition (S₁ := S) (S₂ := ℤ_[p]) _) i₂
  rw [hcomp, eval_compLeft S S, eval_transition, transition_eq_transition (S₁ := ℤ_[p]) (S₂ := S)]

/-- Translation commutes with multi-level stage transitions. -/
theorem transitionLE_translate {k : ℕ} (hhk : h ≤ k) (x : ℤ_[p]) (c : AnalyticStage p h E) :
    transitionLE S hhk (translate S x c) = translate S x (transitionLE S hhk c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ S hhk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ih, transition_translate]

end Comul

end AnalyticStage

/-! ### Translation on locally analytic functions -/

namespace LocallyAnalytic

open AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

private noncomputable def translateLM (x : ℤ_[p]) :
    LocallyAnalytic p S E →ₗ[S] LocallyAnalytic p S E :=
  Module.DirectLimit.lift S ℕ _ _
    (fun h ↦ (ofStage S h).comp (AnalyticStage.translate S x).toLinearMap)
    (fun h k hhk c ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        ContinuousLinearMap.coe_coe, ← transitionLE_translate S hhk x c, ofStage_transitionLE])

private theorem translateLM_ofStage (x : ℤ_[p]) (h : ℕ) (c : AnalyticStage p h E) :
    translateLM S x (ofStage S h c) = ofStage S h (AnalyticStage.translate S x c) :=
  lift_ofStage S _ _ h c

private theorem translateLM_zero (f : LocallyAnalytic p S E) : translateLM S 0 f = f := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translateLM_ofStage, AnalyticStage.translate_zero]

private theorem translateLM_add (x y : ℤ_[p]) (f : LocallyAnalytic p S E) :
    translateLM S (x + y) f = translateLM S x (translateLM S y f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translateLM_ofStage, translateLM_ofStage, translateLM_ofStage,
    AnalyticStage.translate_add]

/-- **Translation on locally analytic functions.** Translating the argument by `x : ℤ_p` defines a
linear equivalence `LA(ℤ_p, E) ≃ₗ[S] LA(ℤ_p, E)` agreeing with `AnalyticStage.translate S x` on
every stage. -/
noncomputable def translate (x : ℤ_[p]) : LocallyAnalytic p S E ≃ₗ[S] LocallyAnalytic p S E where
  toFun := translateLM S x
  map_add' := map_add (translateLM S x)
  map_smul' := map_smul (translateLM S x)
  invFun := translateLM S (-x)
  left_inv f := by rw [← translateLM_add, neg_add_cancel, translateLM_zero]
  right_inv f := by rw [← translateLM_add, add_neg_cancel, translateLM_zero]

/-- Translation restricts to `AnalyticStage.translate` on every analytic stage. -/
@[simp]
theorem translate_ofStage (x : ℤ_[p]) (h : ℕ) (c : AnalyticStage p h E) :
    translate S x (ofStage S h c) = ofStage S h (AnalyticStage.translate S x c) :=
  translateLM_ofStage S x h c

/-- Evaluating the translate of `f` by `x` at `y` gives `eval S f (x + y)`. -/
@[simp]
theorem eval_translate (x : ℤ_[p]) (f : LocallyAnalytic p S E) (y : ℤ_[p]) :
    eval S (translate S x f) y = eval S f (x + y) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, translate_ofStage, eval_ofStage, eval_ofStage, AnalyticStage.eval_translate]

/-- Translating by `0` is the identity. -/
@[simp]
theorem translate_zero (f : LocallyAnalytic p S E) : translate S 0 f = f :=
  translateLM_zero S f

/-- Translations compose by addition. -/
theorem translate_add (x y : ℤ_[p]) (f : LocallyAnalytic p S E) :
    translate S (x + y) f = translate S x (translate S y f) :=
  translateLM_add S x y f

/-- The inverse of translation by `x` is translation by `-x`. -/
@[simp]
theorem translate_symm (x : ℤ_[p]) :
    (translate (p := p) (E := E) S x).symm = translate S (-x) := by
  ext f
  rfl

end LocallyAnalytic

/-! ### Dirac distributions and additive convolution -/

namespace LocallyAnalyticDistribution

open AnalyticStage LocallyAnalytic

variable {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

/-! #### Dirac distributions -/

variable (K) in
/-- The **Dirac distribution** at `x : ℤ_p`, evaluating locally analytic functions at `x`. -/
noncomputable def dirac (x : ℤ_[p]) : LocallyAnalyticDistribution p K :=
  ofMeasure (AbstractMeasure.dirac K x)

/-- Applying the Dirac distribution at `x` evaluates the function at `x`. -/
@[simp]
theorem coe_dirac_apply (x : ℤ_[p]) (f : LocallyAnalytic p K K) :
    (dirac K x : Module.Dual K (LocallyAnalytic p K K)) f = LocallyAnalytic.eval K f x := by
  simp [dirac]

/-- Restricting the Dirac distribution at `x` to stage `h` evaluates coefficient vectors at `x`. -/
theorem stage_dirac_apply (x : ℤ_[p]) (h : ℕ) (c : AnalyticStage p h K) :
    stage h (dirac K x) c = AnalyticStage.eval K c x := by
  simp [dirac]

/-- The Amice transform of the Dirac distribution at `x` is the binomial series `(1 + T)ˣ`. -/
@[simp]
theorem amiceTransform_dirac (x : ℤ_[p]) :
    amiceTransform (dirac K x) = PowerSeries.binomialSeries K x := by
  rw [dirac, amiceTransform_ofMeasure, AbstractMeasure.amiceTransform_dirac]

private theorem eval_single_zero {h : ℕ} (a : ZMod (p ^ h)) (e : K) (x : ℤ_[p]) :
    AnalyticStage.eval K (ZeroAtInftyContinuousMap.single (a, 0) e) x =
      if PadicInt.toZModPow h x = a then e else 0 := by
  rw [AnalyticStage.eval_apply, tsum_eq_single 0]
  · by_cases hmod : PadicInt.toZModPow h x = a <;> simp [hmod]
  · intro n hn
    have hne : (PadicInt.toZModPow h x, n) ≠ (a, 0) := fun h ↦ hn (Prod.ext_iff.mp h).2
    simp [ZeroAtInftyContinuousMap.single_eq_of_ne hne]

/-- The operator norm of a Dirac distribution on stage `h` equals `1`. -/
@[simp]
theorem norm_stage_dirac (x : ℤ_[p]) (h : ℕ) :
    ‖stage h (dirac K x)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun c ↦ ?_
    rw [stage_dirac_apply, one_mul]
    exact (ContinuousMap.norm_coe_le_norm _ x).trans (AnalyticStage.norm_eval_le K c)
  · let c : AnalyticStage p h K := ZeroAtInftyContinuousMap.single (PadicInt.toZModPow h x, 0) 1
    have hle := ContinuousLinearMap.le_opNorm (stage h (dirac K x)) c
    simpa [c, eval_single_zero] using hle

/-- Every stage seminorm of a Dirac distribution equals `1`. -/
theorem stageSeminorm_dirac (x : ℤ_[p]) (h : ℕ) :
    stageSeminorm h (dirac K x) = 1 := by
  rw [stageSeminorm_apply]
  exact norm_stage_dirac x h

/-- Distinct points of `ℤ_p` define distinct Dirac distributions. -/
theorem dirac_injective : Function.Injective (dirac (p := p) K) := by
  intro x y hxy
  refine PadicInt.ext_of_toZModPow.mp fun h ↦ ?_
  let c : AnalyticStage p h K := ZeroAtInftyContinuousMap.single (PadicInt.toZModPow h x, 0) 1
  have h1 := DFunLike.congr_fun (congrArg (stage h) hxy) c
  simp only [stage_dirac_apply, c, eval_single_zero, ↓reduceIte] at h1
  by_contra hne
  simp [Ne.symm hne] at h1

/-! #### Bounded two-variable test-function pairing -/

/-- The stage-level right convolution operator of a continuous functional `φ : LA_h(K) →L[K] K`:
postcomposing `AnalyticStage.comul K` coordinatewise with `φ` sends `c` to the coefficient vector
of `x ↦ φ (y ↦ c(x + y))`. -/
noncomputable def convolveFunRightStage {h : ℕ} :
    (AnalyticStage p h K →L[K] K) →ₗ[K] (AnalyticStage p h K →L[K] AnalyticStage p h K) where
  toFun φ :=
    (ZeroAtInftyContinuousMap.compLeft φ ⟨‖φ‖, φ.le_opNorm⟩).comp
      (AnalyticStage.comul (p := p) (h := h) (E := K) K).toContinuousLinearMap
  map_add' φ ψ := by ext c i; simp
  map_smul' a φ := by ext c i; simp

/-- Coordinatewise formula for `convolveFunRightStage φ`. -/
@[simp]
theorem convolveFunRightStage_apply {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) (i : ZMod (p ^ h) × ℕ) :
    convolveFunRightStage φ c i = φ (AnalyticStage.comul K c i) := by
  simp [convolveFunRightStage]

/-- `convolveFunRightStage φ` is bounded by `‖φ‖`. -/
theorem norm_convolveFunRightStage_apply_le {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) :
    ‖convolveFunRightStage φ c‖ ≤ ‖φ‖ * ‖c‖ := by
  calc
    ‖convolveFunRightStage φ c‖ ≤ ‖φ‖ * ‖AnalyticStage.comul K c‖ :=
      ZeroAtInftyContinuousMap.norm_compLeft_apply_le φ φ.le_opNorm (AnalyticStage.comul K c)
    _ = ‖φ‖ * ‖c‖ := by rw [(AnalyticStage.comul (p := p) (h := h) (E := K) K).norm_map]

/-- The operator norm of `convolveFunRightStage φ` is at most `‖φ‖`. -/
theorem opNorm_convolveFunRightStage_le {h : ℕ} (φ : AnalyticStage p h K →L[K] K) :
    ‖convolveFunRightStage φ‖ ≤ ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ) (norm_convolveFunRightStage_apply_le φ)

/-- Evaluating `convolveFunRightStage φ c` at `x` applies `φ` to the translate of `c` by `x`. -/
@[simp]
theorem eval_convolveFunRightStage {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) (x : ℤ_[p]) :
    AnalyticStage.eval K (convolveFunRightStage φ c) x = φ (AnalyticStage.translate K x c) := by
  let φ' : AnalyticStage p h K →L[ℤ_[p]] K := φ.restrictScalars ℤ_[p]
  have hφ' : ∃ C, ∀ d, ‖φ' d‖ ≤ C * ‖d‖ := ⟨‖φ‖, φ.le_opNorm⟩
  have hcomp : convolveFunRightStage φ c =
      ZeroAtInftyContinuousMap.compLeft φ' hφ' (AnalyticStage.comul K c) := by
    ext i
    simp [φ']
  rw [hcomp, AnalyticStage.eval_compLeft K K, AnalyticStage.translate_eq_eval_comul,
    ContinuousLinearMap.coe_restrictScalars']

/-- For a distribution `ν`, the stage-level right convolution operators commute with adjacent
transitions. -/
theorem convolveFunRightStage_transition (ν : LocallyAnalyticDistribution p K) {h : ℕ}
    (c : AnalyticStage p h K) :
    convolveFunRightStage (stage (h + 1) ν) (transition K c) =
      transition K (convolveFunRightStage (stage h ν) c) := by
  let φ : AnalyticStage p h K →L[ℤ_[p]] K := (stage h ν).restrictScalars ℤ_[p]
  let ψ : AnalyticStage p (h + 1) K →L[ℤ_[p]] K := (stage (h + 1) ν).restrictScalars ℤ_[p]
  have hφ : ∃ C, ∀ d, ‖φ d‖ ≤ C * ‖d‖ := ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩
  have hψ : ∃ C, ∀ d, ‖ψ d‖ ≤ C * ‖d‖ := ⟨‖stage (h + 1) ν‖, (stage (h + 1) ν).le_opNorm⟩
  have hL : convolveFunRightStage (stage (h + 1) ν) (transition K c) =
      ZeroAtInftyContinuousMap.compLeft ψ hψ (comul K (transition K c)) := by
    ext i
    simp [ψ]
  have hR : transition K (convolveFunRightStage (stage h ν) c) =
      transition K (ZeroAtInftyContinuousMap.compLeft φ hφ (comul K c)) := by
    congr 1
    ext i
    simp [φ]
  rw [hL, hR, comul_transition, transition_compLeft K K]
  ext i
  simp only [ZeroAtInftyContinuousMap.compLeft_apply]
  exact DFunLike.congr_fun (stage_comp_transition ν h) _

/-- For a distribution `ν`, the stage-level right convolution operators commute with multi-level
transitions. -/
theorem convolveFunRightStage_transitionLE (ν : LocallyAnalyticDistribution p K) {h k : ℕ}
    (hhk : h ≤ k) (c : AnalyticStage p h K) :
    convolveFunRightStage (stage k ν) (transitionLE K hhk c) =
      transitionLE K hhk (convolveFunRightStage (stage h ν) c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ K hhk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      convolveFunRightStage_transition, ih]

/-- Right convolution of a locally analytic function with a distribution: sends `f` to the locally
analytic function `x ↦ ν (y ↦ f (x + y))`. -/
noncomputable def convolveFunRight :
    LocallyAnalyticDistribution p K →ₗ[K] LocallyAnalytic p K K →ₗ[K] LocallyAnalytic p K K where
  toFun ν := Module.DirectLimit.lift K ℕ _ _
    (fun h ↦ (ofStage K h).comp (convolveFunRightStage (stage h ν)).toLinearMap)
    (fun h k hhk c ↦ by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        convolveFunRightStage_transitionLE, ofStage_transitionLE])
  map_add' ν₁ ν₂ := Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by
    simp only [← ofStage_def, LinearMap.comp_apply, LinearMap.add_apply, lift_ofStage,
      ContinuousLinearMap.coe_coe, map_add, add_apply]
  map_smul' a ν := Module.DirectLimit.hom_ext fun h ↦ LinearMap.ext fun c ↦ by
    simp only [← ofStage_def, LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply,
      lift_ofStage, ContinuousLinearMap.coe_coe, map_smul, smul_apply]

/-- Right convolution restricts to `convolveFunRightStage (stage h ν)` on stage `h`. -/
@[simp]
theorem convolveFunRight_ofStage (ν : LocallyAnalyticDistribution p K) (h : ℕ)
    (c : AnalyticStage p h K) :
    convolveFunRight ν (ofStage K h c) =
      ofStage K h (convolveFunRightStage (stage h ν) c) := by
  simp [convolveFunRight]

/-- Evaluating `convolveFunRight ν f` at `x` applies `ν` to the translate of `f` by `x`. -/
@[simp]
theorem eval_convolveFunRight (ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K)
    (x : ℤ_[p]) :
    LocallyAnalytic.eval K (convolveFunRight ν f) x =
      (ν : Module.Dual K (LocallyAnalytic p K K)) (LocallyAnalytic.translate K x f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, eval_ofStage, eval_convolveFunRightStage,
    LocallyAnalytic.translate_ofStage, stage_apply]

private theorem compLeft_eval_comul_padicInt {h : ℕ} (x : ℤ_[p]) (d : AnalyticStage p h ℤ_[p]) :
    ZeroAtInftyContinuousMap.compLeft
      ((ContinuousMap.evalCLM ℤ_[p] x).comp (AnalyticStage.eval ℤ_[p]))
      ⟨1, fun d' ↦ by
        simpa using (ContinuousMap.norm_coe_le_norm _ x).trans
          (AnalyticStage.norm_eval_le ℤ_[p] d')⟩
      (comul ℤ_[p] d) = AnalyticStage.translate ℤ_[p] x d := by
  apply AnalyticStage.eval_injective ℤ_[p] (isSMulRegular_p_padicInt (p := p))
  ext y
  rw [AnalyticStage.eval_compLeft ℤ_[p] ℤ_[p], ContinuousLinearMap.comp_apply,
    ContinuousMap.evalCLM_apply, eval_eval_comul, AnalyticStage.eval_translate, add_comm]

/-- Stage-level right convolution with a Dirac distribution at `x` is translation by `x`. -/
@[simp]
theorem convolveFunRightStage_stage_dirac_apply (x : ℤ_[p]) {h : ℕ} (c : AnalyticStage p h K) :
    convolveFunRightStage (stage h (dirac K x)) c = AnalyticStage.translate K x c := by
  let L₁ : AnalyticStage p h K →L[ℤ_[p]] AnalyticStage p h K :=
    (convolveFunRightStage (stage h (dirac K x))).restrictScalars ℤ_[p]
  let L₂ : AnalyticStage p h K →L[ℤ_[p]] AnalyticStage p h K :=
    (AnalyticStage.translate ℤ_[p] x).toLinearIsometry.toContinuousLinearMap
  have hEq : L₁ = L₂ := ZeroAtInftyContinuousMap.continuousLinearMap_ext fun i e ↦ by
    let u := ContinuousLinearMap.toSpanSingleton ℤ_[p] e
    have hu : ∃ C, ∀ r : ℤ_[p], ‖u r‖ ≤ C * ‖r‖ := ⟨‖e‖, norm_toSpanSingleton_padicInt_le e⟩
    have hsingle : ZeroAtInftyContinuousMap.single i e =
        ZeroAtInftyContinuousMap.compLeft u hu
          (ZeroAtInftyContinuousMap.single i (1 : ℤ_[p])) := by
      simp [u]
    have hL1 : L₁ (ZeroAtInftyContinuousMap.single i e) =
        ZeroAtInftyContinuousMap.compLeft u hu
          (AnalyticStage.translate ℤ_[p] x (ZeroAtInftyContinuousMap.single i (1 : ℤ_[p]))) := by
      rw [← compLeft_eval_comul_padicInt x]
      ext j
      simp only [L₁, ContinuousLinearMap.coe_restrictScalars', convolveFunRightStage_apply,
        stage_dirac_apply, ZeroAtInftyContinuousMap.compLeft_apply, ContinuousLinearMap.comp_apply,
        ContinuousMap.evalCLM_apply]
      rw [hsingle, comul_compLeft ℤ_[p] K u hu, ZeroAtInftyContinuousMap.compLeft_apply]
      exact AnalyticStage.eval_compLeft ℤ_[p] K u hu _ x
    rw [hL1, hsingle]
    exact (translateCLM_compLeft ℤ_[p] ℤ_[p] u hu x _).symm
  have hc : convolveFunRightStage (stage h (dirac K x)) c = AnalyticStage.translate ℤ_[p] x c :=
    DFunLike.congr_fun hEq c
  rw [hc]
  exact translateCLM_eq (S₁ := ℤ_[p]) (S₂ := K) x c

/-- Right convolution with a Dirac distribution at `x` is translation by `x`. -/
@[simp]
theorem convolveFunRight_dirac (x : ℤ_[p]) (f : LocallyAnalytic p K K) :
    convolveFunRight (dirac K x) f = LocallyAnalytic.translate K x f := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, convolveFunRightStage_stage_dirac_apply,
    LocallyAnalytic.translate_ofStage]

/-- Right convolution acts on locally analytic Mahler terms via the Vandermonde formula with the
moments of `ν`. -/
theorem convolveFunRight_mahlerTerm (ν : LocallyAnalyticDistribution p K) (n : ℕ) :
    convolveFunRight ν (mahlerTerm p K 1 n) =
      ∑ ij ∈ Finset.antidiagonal n, (amiceTransform ν).coeff ij.2 • mahlerTerm p K 1 ij.1 := by
  have hlt : n < p ^ n := Nat.lt_pow_self hp.out.one_lt
  rw [mahlerTerm_def, convolveFunRight_ofStage]
  have hstage : convolveFunRightStage (stage n ν) (amiceTerm p n n (1 : K)) =
      ∑ ij ∈ Finset.antidiagonal n, amiceTerm p n ij.1 ((amiceTransform ν).coeff ij.2) := by
    rw [convolveFunRightStage, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, comul_amiceTerm, map_sum]
    refine Finset.sum_congr rfl fun ij hij ↦ ?_
    have hij' := Finset.mem_antidiagonal.mp hij
    have hj : ij.2 / p ^ n = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt (by omega) hlt)
    have hcoeff : stage n ν (amiceTerm p n ij.2 (1 : K)) = (amiceTransform ν).coeff ij.2 := by
      rw [stage_amiceTerm, hj, Nat.factorial_zero, Nat.cast_one, one_mul, one_mul]
    ext i
    simp [hcoeff]
  rw [hstage, map_sum]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  have hij' := Finset.mem_antidiagonal.mp hij
  have hi : ij.1 / p ^ n = 0 := Nat.div_eq_of_lt (lt_of_le_of_lt (by omega) hlt)
  rw [ofStage_amiceTerm, hi, Nat.factorial_zero, one_smul]
  simpa only [smul_eq_mul, mul_one] using
    mahlerTerm_smul K ((amiceTransform ν).coeff ij.2) (1 : K) ij.1

/-! #### Convolution ring and `K`-algebra structure -/

/-- The multiplicative identity for additive convolution is the Dirac distribution at `0`. -/
noncomputable instance : One (LocallyAnalyticDistribution p K) where
  one := dirac K 0

/-- The convolution identity is the Dirac distribution at `0`. -/
theorem one_def : (1 : LocallyAnalyticDistribution p K) = dirac K 0 :=
  (rfl)

/-- Applying the convolution identity evaluates the function at `0`. -/
@[simp]
theorem coe_one_apply (f : LocallyAnalytic p K K) :
    ((1 : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      LocallyAnalytic.eval K f 0 :=
  coe_dirac_apply 0 f

/-- **Additive convolution of locally analytic distributions**:
`(μ * ν)(f) = μ (x ↦ ν (y ↦ f (x + y)))`. -/
noncomputable instance : Mul (LocallyAnalyticDistribution p K) where
  mul μ ν :=
    ⟨(μ : Module.Dual K (LocallyAnalytic p K K)).comp (convolveFunRight ν), mem_iff.mpr fun h ↦ by
      convert ((stage h μ).comp (convolveFunRightStage (stage h ν))).continuous using 1
      ext c
      simp⟩

/-- Applying the convolution `μ * ν` to `f` applies `μ` to `convolveFunRight ν f`. -/
@[simp]
theorem coe_mul_apply (μ ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    ((μ * ν : LocallyAnalyticDistribution p K) : Module.Dual K (LocallyAnalytic p K K)) f =
      (μ : Module.Dual K (LocallyAnalytic p K K)) (convolveFunRight ν f) :=
  (rfl)

/-- Restricting the convolution `μ * ν` to stage `h` composes `stage h μ` with the stage-level
right convolution operator of `stage h ν`. -/
@[simp]
theorem stage_mul (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    stage h (μ * ν) = (stage h μ).comp (convolveFunRightStage (stage h ν)) := by
  ext c
  simp

/-- The operator norm of the convolution identity on stage `h` equals `1`. -/
@[simp]
theorem norm_stage_one (h : ℕ) :
    ‖stage h (1 : LocallyAnalyticDistribution p K)‖ = 1 :=
  norm_stage_dirac (K := K) 0 h

/-- Every stage seminorm of the convolution identity equals `1`. -/
theorem stageSeminorm_one (h : ℕ) :
    stageSeminorm h (1 : LocallyAnalyticDistribution p K) = 1 :=
  stageSeminorm_dirac (K := K) 0 h

/-- **Stage seminorm submultiplicativity for additive convolution.** At every fixed analytic level
`h`, the stage seminorm of `μ * ν` is at most the product of the stage seminorms of `μ` and `ν`,
with no loss of level or extra constant. -/
theorem stageSeminorm_mul_le (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    stageSeminorm h (μ * ν) ≤ stageSeminorm h μ * stageSeminorm h ν := by
  rw [stageSeminorm_apply, stageSeminorm_apply, stageSeminorm_apply, stage_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (opNorm_convolveFunRightStage_le _) (norm_nonneg _))

/-- The Amice transform sends the convolution identity to `1`. -/
@[simp]
theorem amiceTransform_one : amiceTransform (1 : LocallyAnalyticDistribution p K) = 1 := by
  rw [one_def, amiceTransform_dirac, PowerSeries.binomialSeries_zero]

/-- **The Amice transform is multiplicative for additive convolution.** -/
@[simp]
theorem amiceTransform_mul (μ ν : LocallyAnalyticDistribution p K) :
    amiceTransform (μ * ν) = amiceTransform μ * amiceTransform ν := by
  ext n
  rw [coeff_amiceTransform, coe_mul_apply, convolveFunRight_mahlerTerm, map_sum,
    PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [map_smul, coeff_amiceTransform, coeff_amiceTransform, smul_eq_mul, mul_comm]

/-- Locally analytic distributions form a commutative ring under additive convolution, extending
the existing submodule additive group structure. -/
noncomputable instance : CommRing (LocallyAnalyticDistribution p K) where
  left_distrib μ ν₁ ν₂ := amiceTransform_injective <| by simp [map_add, mul_add]
  right_distrib μ₁ μ₂ ν := amiceTransform_injective <| by simp [map_add, add_mul]
  zero_mul μ := amiceTransform_injective <| by simp
  mul_zero μ := amiceTransform_injective <| by simp
  mul_assoc μ ν ρ := amiceTransform_injective <| by simp [mul_assoc]
  one_mul μ := amiceTransform_injective <| by simp
  mul_one μ := amiceTransform_injective <| by simp
  mul_comm μ ν := amiceTransform_injective <| by simp [mul_comm]

/-- Locally analytic distributions form a `K`-algebra under additive convolution, extending the
existing submodule scalar multiplication. -/
noncomputable instance : Algebra K (LocallyAnalyticDistribution p K) :=
  Algebra.ofModule
    (fun r μ ν ↦ amiceTransform_injective <| by
      rw [amiceTransform_mul, map_smul, map_smul, amiceTransform_mul, smul_mul_assoc])
    (fun r μ ν ↦ amiceTransform_injective <| by
      rw [amiceTransform_mul, map_smul, map_smul, amiceTransform_mul, mul_smul_comm])

/-- Convolution of Dirac distributions corresponds to addition in `ℤ_p`. -/
@[simp]
theorem dirac_mul_dirac (x y : ℤ_[p]) :
    dirac K x * dirac K y = dirac K (x + y) :=
  amiceTransform_injective <| by simp [PowerSeries.binomialSeries_add]

/-- Right convolution with `1` is the identity on locally analytic functions. -/
@[simp]
theorem convolveFunRight_one (f : LocallyAnalytic p K K) :
    convolveFunRight (1 : LocallyAnalyticDistribution p K) f = f := by
  rw [one_def, convolveFunRight_dirac, LocallyAnalytic.translate_zero]

/-- Stage-level right convolution is associative with respect to distribution convolution. -/
theorem convolveFunRightStage_stage_mul (μ ν : LocallyAnalyticDistribution p K) (h : ℕ) :
    convolveFunRightStage (stage h (μ * ν)) =
      (convolveFunRightStage (stage h μ)).comp (convolveFunRightStage (stage h ν)) := by
  ext c i
  let ψ : AnalyticStage p h K →L[ℤ_[p]] K := (stage h ν).restrictScalars ℤ_[p]
  have hψ : ∃ C, ∀ d, ‖ψ d‖ ≤ C * ‖d‖ := ⟨‖stage h ν‖, (stage h ν).le_opNorm⟩
  have hcomp (d : AnalyticStage p h K) : convolveFunRightStage (stage h ν) d =
      ZeroAtInftyContinuousMap.compLeft ψ hψ (comul K d) := by
    ext j
    simp [ψ]
  simp only [convolveFunRightStage_apply, ContinuousLinearMap.comp_apply, stage_mul]
  rw [hcomp, hcomp, comul_compLeft K K ψ hψ, ZeroAtInftyContinuousMap.compLeft_apply]
  congr 2
  have hcoassoc := congrArg (fun d ↦ d i) (comul_comul K c)
  simpa only [ZeroAtInftyContinuousMap.compLeft_apply,
    LinearIsometry.coe_toContinuousLinearMap] using hcoassoc.symm

/-- Right convolution turns `LocallyAnalytic p K K` into a module action of the convolution
algebra: `convolveFunRight (μ * ν) = convolveFunRight μ ∘ convolveFunRight ν`. -/
theorem convolveFunRight_mul (μ ν : LocallyAnalyticDistribution p K) (f : LocallyAnalytic p K K) :
    convolveFunRight (μ * ν) f = convolveFunRight μ (convolveFunRight ν f) := by
  obtain ⟨h, c, rfl⟩ := Module.DirectLimit.exists_of f
  rw [← ofStage_def, convolveFunRight_ofStage, convolveFunRight_ofStage, convolveFunRight_ofStage,
    convolveFunRightStage_stage_mul, ContinuousLinearMap.comp_apply]

/-! #### Algebra and ring homomorphisms for the Amice transform -/

/-- The Amice transform bundled as a `K`-algebra homomorphism into formal power series. -/
noncomputable def amiceTransformAlgHom :
    LocallyAnalyticDistribution p K →ₐ[K] PowerSeries K :=
  AlgHom.ofLinearMap amiceTransform amiceTransform_one amiceTransform_mul

/-- The underlying map of `amiceTransformAlgHom` is `amiceTransform`. -/
@[simp]
theorem coe_amiceTransformAlgHom (μ : LocallyAnalyticDistribution p K) :
    amiceTransformAlgHom μ = amiceTransform μ :=
  (rfl)

/-- The linear map underlying `amiceTransformAlgHom` is `amiceTransform`. -/
@[simp]
theorem toLinearMap_amiceTransformAlgHom :
    (amiceTransformAlgHom (p := p) (K := K)).toLinearMap = amiceTransform :=
  (rfl)

section NormedAlgebra

variable [NormedAlgebra ℚ_[p] K]

/-- **Amice's theorem as a ring isomorphism.** When `K` is a normed `ℚ_p`-algebra, the Amice
transform is a ring isomorphism from the convolution ring `LocallyAnalyticDistribution p K` onto
the ring `PowerSeries.OnOpenDisc.subring K 1` of power series converging on the open unit disc. -/
noncomputable def amiceTransformRingEquiv :
    LocallyAnalyticDistribution p K ≃+* PowerSeries.OnOpenDisc.subring K 1 where
  toFun := amiceTransformEquiv
  invFun := amiceTransformEquiv.symm
  left_inv := amiceTransformEquiv.left_inv
  right_inv := amiceTransformEquiv.right_inv
  map_add' := map_add amiceTransformEquiv
  map_mul' μ ν := Subtype.ext <| by
    simp only [Subring.coe_mul, coe_amiceTransformEquiv, amiceTransform_mul]

/-- The underlying power series of `amiceTransformRingEquiv μ` is `amiceTransform μ`. -/
@[simp]
theorem coe_amiceTransformRingEquiv (μ : LocallyAnalyticDistribution p K) :
    (amiceTransformRingEquiv μ : PowerSeries K) = amiceTransform μ :=
  coe_amiceTransformEquiv μ

/-- The inverse of `amiceTransformRingEquiv` is `ofOnOpenDisc`. -/
@[simp]
theorem amiceTransformRingEquiv_symm_apply (F : PowerSeries.OnOpenDisc.subring K 1) :
    amiceTransformRingEquiv.symm F =
      ofOnOpenDisc p (PowerSeries.OnOpenDisc.mem_subring.mp F.2) :=
  amiceTransformEquiv_symm_apply F

end NormedAlgebra

/-! #### Compatibility with native measure convolution -/

private theorem amiceTransform_ofMeasure_arrowCongrLeft
    (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K) :
    amiceTransform (ofMeasure (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ)) =
      AbstractMeasure.amiceTransformₐ μ := by
  ext n
  rw [amiceTransform_ofMeasure, AbstractMeasure.coeff_amiceTransform,
    AbstractMeasure.coeff_amiceTransformₐ, AbstractMeasure.arrowCongrLeft_apply]
  congr 1

/-- The canonical embedding of Mathlib's convolution algebra `D(Multiplicative ℤ_p, K)` of
continuous measures into `LocallyAnalyticDistribution p K`, as an injective `K`-algebra
homomorphism. -/
noncomputable def ofMulMeasure :
    AbstractMeasure (Multiplicative ℤ_[p]) K K →ₐ[K] LocallyAnalyticDistribution p K :=
  AlgHom.ofLinearMap
    (ofMeasure.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).toLinearMap)
    (amiceTransform_injective <| by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        amiceTransform_ofMeasure_arrowCongrLeft, map_one, amiceTransform_one])
    (fun μ ν ↦ amiceTransform_injective <| by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        amiceTransform_ofMeasure_arrowCongrLeft, map_mul, amiceTransform_mul])

/-- `ofMulMeasure` transports a measure along `Homeomorph.ofAdd.symm` and applies `ofMeasure`. -/
theorem ofMulMeasure_apply (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K) :
    ofMulMeasure μ = ofMeasure (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm μ) :=
  (rfl)

/-- Applying `ofMulMeasure μ` to a locally analytic function integrates its evaluation transported
to `Multiplicative ℤ_p`. -/
@[simp]
theorem coe_ofMulMeasure_apply (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K)
    (f : LocallyAnalytic p K K) :
    (ofMulMeasure μ : Module.Dual K (LocallyAnalytic p K K)) f =
      μ ((LocallyAnalytic.eval K f).comp
        (Homeomorph.ofAdd.symm : Multiplicative ℤ_[p] ≃ₜ ℤ_[p])) := by
  simp [ofMulMeasure_apply]

/-- `ofMulMeasure` sends the Dirac measure at `Multiplicative.ofAdd x` to `dirac K x`. -/
@[simp]
theorem ofMulMeasure_dirac (x : ℤ_[p]) :
    ofMulMeasure (AbstractMeasure.dirac K (Multiplicative.ofAdd x)) = dirac K x := by
  ext f
  simp [coe_ofMulMeasure_apply, AbstractMeasure.dirac_apply]

/-- The Amice transform on distributions agrees with Mathlib's multiplicative-measure Amice
transform `AbstractMeasure.amiceTransformₐ` along `ofMulMeasure`. -/
@[simp]
theorem amiceTransform_ofMulMeasure (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K) :
    amiceTransform (ofMulMeasure μ) = AbstractMeasure.amiceTransformₐ μ :=
  amiceTransform_ofMeasure_arrowCongrLeft μ

/-- `ofMulMeasure` is injective. -/
theorem ofMulMeasure_injective : Function.Injective (ofMulMeasure (p := p) (K := K)) :=
  ofMeasure_injective.comp (AbstractMeasure.arrowCongrLeft Homeomorph.ofAdd.symm).injective

/-- The stage seminorms of `ofMulMeasure μ` are bounded by the operator norm of `μ`. -/
theorem stageSeminorm_ofMulMeasure_le (μ : AbstractMeasure (Multiplicative ℤ_[p]) K K) (h : ℕ) :
    stageSeminorm h (ofMulMeasure μ) ≤ ‖AbstractMeasure.toCLMEquiv μ‖ := by
  rw [ofMulMeasure_apply]
  refine (stageSeminorm_ofMeasure_le _ h).trans ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f ↦ ?_
  let φ : Multiplicative ℤ_[p] ≃ₜ ℤ_[p] := Homeomorph.ofAdd.symm
  have hnorm : ‖f.comp (φ : C(Multiplicative ℤ_[p], ℤ_[p]))‖ ≤ ‖f‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun x ↦ by
      simpa only [ContinuousMap.comp_apply] using f.norm_coe_le_norm _
  rw [AbstractMeasure.coe_toCLMEquiv, AbstractMeasure.arrowCongrLeft_apply,
    ← AbstractMeasure.coe_toCLMEquiv]
  exact (ContinuousLinearMap.le_opNorm (AbstractMeasure.toCLMEquiv μ) _).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))

end LocallyAnalyticDistribution

end TauCeti
