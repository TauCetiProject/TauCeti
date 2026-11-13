/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Bases
public import TauCeti.MeasureTheory.Constructions.UnitInterval.Dyadic
public import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# The Haar basis of `Lᵖ([0, 1])`

The Haar system on the unit interval `I` consists of the constant function `h₀ = 1` and, for
`n ≥ 1`, the function `hₙ` equal to `1` on the left half and `-1` on the right half of the dyadic
cell numbered `n` in breadth-first order, and to `0` elsewhere. Writing `n = 2 ^ k + i` with
`i < 2 ^ k`, this is the cell `[i / 2 ^ k, (i + 1) / 2 ^ k)` of level `k`, and its halves are the
cells numbered `2 * n` and `2 * n + 1` (see `TauCeti.unitInterval.dyadicCell`). So the functions
are ordered by increasing dyadic level, and from left to right within a level.

For `1 ≤ p < ∞` and `𝕜` equal to `ℝ` or `ℂ` (`[RCLike 𝕜]`), the Haar system is a Schauder basis
of `Lᵖ(I; 𝕜)`. Its initial projections are the dyadic averaging projections `dyadicProj 𝕜 p N`:
for `0 < N` this is conditional expectation with respect to `dyadicFiltration N`, the σ-algebra
whose atoms are the `N` dyadic cells numbered `N, …, 2 * N - 1`, so it replaces a function on each
atom by its average there. These projections are contractions, compose by
`dyadicProj 𝕜 p n ∘ dyadicProj 𝕜 p m = dyadicProj 𝕜 p (min n m)`, and converge strongly to the
identity by the martingale convergence theorem. The basis is assembled from them by Mathlib's
`SchauderBasis.RankOneDecomposition`: `dyadicProj 𝕜 p N` has rank `N`, and `hₙ` spans the range of
`dyadicProj 𝕜 p (n + 1) - dyadicProj 𝕜 p n`.

## Main definitions

* `TauCeti.unitInterval.haarFun n`: the `n`-th Haar function.
* `TauCeti.unitInterval.dyadicProj 𝕜 p N`: the rank-`N` dyadic averaging projection on `Lᵖ(I; 𝕜)`.
* `TauCeti.unitInterval.haarBasis 𝕜 p hp`: the Haar basis of `Lᵖ(I; 𝕜)`, `1 ≤ p < ∞`.

## Main results

* `TauCeti.unitInterval.haarFun_eq_of_mem_dyadicCell`: for `k < N`, `hₖ` is constant on the dyadic
  cell numbered `N`.
* `TauCeti.unitInterval.integral_haarFun_mul_of_ne`: distinct Haar functions are orthogonal on `I`.
* `TauCeti.unitInterval.condExp_haarFun`: `hₙ` has conditional expectation zero given
  `dyadicFiltration n`, for `0 < n`.
* `TauCeti.unitInterval.dyadicProj_eq_sum`: the projections average over the dyadic atoms.
* `TauCeti.unitInterval.dyadicProj_dyadicProj`: the composition law of the projections.
* `TauCeti.unitInterval.tendsto_dyadicProj`: the projections converge strongly to the identity.
* `TauCeti.unitInterval.finrank_range_dyadicProj`: `dyadicProj 𝕜 p N` has rank `N`.
* `TauCeti.unitInterval.haarBasis_proj`: the initial projections of the Haar basis are the dyadic
  averaging projections.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Graduate Texts in
  Mathematics 233, Springer (2016), §6.1.
-/

public section

noncomputable section

open MeasureTheory Filter TauCeti.MeasureTheory

open scoped ENNReal Topology unitInterval

namespace TauCeti.unitInterval

/-! ### The Haar functions -/

/-- The `n`-th Haar function on the unit interval: `1` for `n = 0`, and for `n ≥ 1` the function
equal to `1` on the dyadic cell numbered `2 * n` and to `-1` on the cell numbered `2 * n + 1`, the
two halves of the cell numbered `n`, and to `0` elsewhere. -/
def haarFun (n : ℕ) (x : I) : ℝ :=
  if n = 0 then 1 else (dyadicCell (2 * n)).indicator 1 x - (dyadicCell (2 * n + 1)).indicator 1 x

/-- The zeroth Haar function is the constant function `1`. -/
@[simp]
theorem haarFun_zero : haarFun 0 = 1 :=
  funext fun _ => ite_eq_left rfl

/-- For `n ≠ 0`, `haarFun n` is the difference of the indicators of the two halves of
`dyadicCell n`. -/
theorem haarFun_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    haarFun n = (dyadicCell (2 * n)).indicator 1 - (dyadicCell (2 * n + 1)).indicator 1 :=
  funext fun _ => ite_eq_right hn

/-- For `0 < n`, the Haar function `hₙ` vanishes outside the dyadic cell numbered `n`. -/
theorem haarFun_eq_zero {n : ℕ} (hn : 0 < n) {x : I} (hx : x ∉ dyadicCell n) : haarFun n x = 0 := by
  have h0 : x ∉ dyadicCell (2 * n) := fun h =>
    hx (by simpa using mem_dyadicCell_div_two (by omega) h)
  have h1 : x ∉ dyadicCell (2 * n + 1) := mt (mem_dyadicCell_of_mem_two_mul_add hn one_lt_two) hx
  simp [haarFun_of_ne_zero hn.ne', h0, h1]

/-- For `0 < n`, the Haar function `hₙ` is `1` on the dyadic cell numbered `2 * n`. -/
theorem haarFun_eq_one {n : ℕ} (hn : 0 < n) {x : I} (hx : x ∈ dyadicCell (2 * n)) :
    haarFun n x = 1 := by
  have h1 : x ∉ dyadicCell (2 * n + 1) := Set.disjoint_left.1 (disjoint_dyadicCell_two_mul hn) hx
  simp [haarFun_of_ne_zero hn.ne', hx, h1]

/-- For `0 < n`, the Haar function `hₙ` is `-1` on the dyadic cell numbered `2 * n + 1`. -/
theorem haarFun_eq_neg_one {n : ℕ} (hn : 0 < n) {x : I} (hx : x ∈ dyadicCell (2 * n + 1)) :
    haarFun n x = -1 := by
  have h0 : x ∉ dyadicCell (2 * n) := Set.disjoint_right.1 (disjoint_dyadicCell_two_mul hn) hx
  simp [haarFun_of_ne_zero hn.ne', hx, h0]

/-- The Haar functions take values in `{-1, 0, 1}`. -/
theorem norm_haarFun_le (n : ℕ) (x : I) : ‖haarFun n x‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [haarFun_of_ne_zero hn, Pi.sub_apply]
    simp only [Set.indicator, Pi.one_apply]
    split_ifs <;> norm_num

/-- For `k < N`, the Haar function `hₖ` is constant on the dyadic cell numbered `N`. -/
theorem haarFun_eq_of_mem_dyadicCell {k N : ℕ} (hk : k < N) {x y : I}
    (hx : x ∈ dyadicCell N) (hy : y ∈ dyadicCell N) :
    haarFun k x = haarFun k y := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hN : N ∈ Set.Ico N (2 * N) := ⟨le_rfl, by omega⟩
  have hxy : dyadicAtom N x = dyadicAtom N y :=
    ((dyadicAtom_eq_iff hN).2 hx).trans ((dyadicAtom_eq_iff hN).2 hy).symm
  have hmem (m : ℕ) (hm : m < 2 * N) : x ∈ dyadicCell m ↔ y ∈ dyadicCell m := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [mem_dyadicCell] at h ⊢
      rw [dyadicNum_eq_of_dyadicAtom_eq hxy.symm (h.trans_lt hm), h]
    · rw [mem_dyadicCell] at h ⊢
      rw [dyadicNum_eq_of_dyadicAtom_eq hxy (h.trans_lt hm), h]
  classical
  simp only [haarFun_of_ne_zero hk0, Pi.sub_apply, Set.indicator, Pi.one_apply]
  exact congrArg₂ _ (if_congr (hmem (2 * k) (by omega)) rfl rfl)
    (if_congr (hmem (2 * k + 1) (by omega)) rfl rfl)

/-- The Haar function `hₙ` is measurable for the dyadic filtration at step `n + 1`. -/
theorem measurable_haarFun_dyadicFiltration (n : ℕ) :
    Measurable[dyadicFiltration (n + 1)] (haarFun n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [haarFun_zero]
    exact measurable_const
  · rw [haarFun_of_ne_zero hn]
    exact (measurable_const.indicator (measurableSet_dyadicFiltration_dyadicCell (by omega))).sub
      (measurable_const.indicator (measurableSet_dyadicFiltration_dyadicCell (by omega)))

/-- Each Haar function is measurable on the unit interval. -/
@[fun_prop]
theorem measurable_haarFun (n : ℕ) : Measurable (haarFun n) :=
  (measurable_haarFun_dyadicFiltration n).mono (dyadicFiltration.le _) le_rfl

/-- The Haar functions lie in every `Lᵖ(I)`. -/
theorem memLp_haarFun (p : ℝ≥0∞) (n : ℕ) : MemLp (haarFun n) p :=
  MemLp.of_bound (measurable_haarFun n).aestronglyMeasurable 1
    (ae_of_all _ (norm_haarFun_le n))

/-- Viewed as a `𝕜`-valued function, each Haar function lies in every `Lᵖ(I; 𝕜)`. -/
theorem memLp_ofReal_haarFun (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) (n : ℕ) :
    MemLp (fun x => (haarFun n x : 𝕜)) p :=
  MemLp.of_bound
    (RCLike.continuous_ofReal.measurable.comp (measurable_haarFun n)).aestronglyMeasurable
    1 (ae_of_all _ fun x => by simpa using norm_haarFun_le n x)

/-- For `0 < n`, the Haar function `hₙ` has integral zero. -/
theorem integral_haarFun {n : ℕ} (hn : 0 < n) : ∫ x, haarFun n x = 0 := by
  have hint (m : ℕ) : Integrable ((dyadicCell m).indicator (1 : I → ℝ)) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_dyadicCell m)
  have h0 : volume (dyadicCell (2 * n)) = _ := volume_dyadicCell_two_mul_add (e := 0) hn two_pos
  have h1 := volume_dyadicCell_two_mul_add hn one_lt_two
  simp [haarFun_of_ne_zero hn.ne', integral_sub (hint _) (hint _),
    integral_indicator_one (measurableSet_dyadicCell _), measureReal_def, h0, h1]

/-- Distinct Haar functions are orthogonal on the unit interval. -/
theorem integral_haarFun_mul_of_ne {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, haarFun m x * haarFun n x = 0 := by
  have key {a b : ℕ} (hab : a < b) : ∫ x, haarFun a x * haarFun b x = 0 := by
    have hb : 0 < b := by omega
    obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero (μ := (volume : Measure I)) (s := dyadicCell b)
      (by rw [volume_dyadicCell hb]; exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
    calc ∫ x, haarFun a x * haarFun b x
        = ∫ x in dyadicCell b, haarFun a x * haarFun b x :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            simp [haarFun_eq_zero hb hx]).symm
      _ = ∫ x in dyadicCell b, haarFun a x₀ * haarFun b x :=
          setIntegral_congr_fun (measurableSet_dyadicCell b) fun x hx => by
            rw [haarFun_eq_of_mem_dyadicCell hab hx hx₀]
      _ = haarFun a x₀ * ∫ x in dyadicCell b, haarFun b x := integral_const_mul _ _
      _ = haarFun a x₀ * ∫ x, haarFun b x := by
          rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => haarFun_eq_zero hb hx]
      _ = 0 := by rw [integral_haarFun hb, mul_zero]
  rcases hmn.lt_or_gt with h | h
  · exact key h
  · simpa only [mul_comm (haarFun m _)] using key h

/-- **The Haar functions are martingale differences.** For `0 < n`, the Haar function `hₙ` has
conditional expectation zero given the dyadic filtration at step `n`: it is supported in the atom
numbered `n` of that σ-algebra, with integral zero there. -/
theorem condExp_haarFun {n : ℕ} (hn : 0 < n) :
    volume[haarFun n | dyadicFiltration n] =ᵐ[volume] 0 := by
  have hmem : n ∈ Set.Ico n (2 * n) := ⟨le_rfl, by omega⟩
  rw [dyadicFiltration_eq_comap_dyadicAtom hn]
  refine (ae_eq_condExp_of_forall_setIntegral_fiber_eq (measurable_dyadicAtom n)
    ((memLp_haarFun 1 n).integrable le_rfl) (integrable_zero _ _ _) aestronglyMeasurable_zero
    fun j => ?_).symm
  rw [Pi.zero_def, integral_zero]
  by_cases hj : j = n
  · subst hj
    rw [preimage_dyadicAtom_singleton_of_mem hmem, setIntegral_eq_integral_of_forall_compl_eq_zero
      fun x hx => haarFun_eq_zero hn hx, integral_haarFun hn]
  · exact (setIntegral_eq_zero_of_forall_eq_zero fun x (hx : dyadicAtom n x = j) =>
      haarFun_eq_zero hn fun hc => hj (hx.symm.trans ((dyadicAtom_eq_iff hmem).2 hc))).symm

/-- Viewed as a `𝕜`-valued function, `hₙ` (`0 < n`) has conditional expectation zero given
`dyadicFiltration n`. -/
theorem condExp_ofReal_haarFun (𝕜 : Type*) [RCLike 𝕜] {n : ℕ} (hn : 0 < n) :
    volume[fun x => (haarFun n x : 𝕜) | dyadicFiltration n] =ᵐ[volume] 0 := by
  refine ((RCLike.ofRealCLM (K := 𝕜)).comp_condExp_comm
    ((memLp_haarFun 1 n).integrable le_rfl)).symm.trans ?_
  filter_upwards [condExp_haarFun hn] with x hx
  simp [hx]

/-! ### The dyadic averaging projections -/

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The dyadic averaging projection of rank `N` on `Lᵖ(I; 𝕜)`: `0` for `N = 0`, and for `0 < N`
conditional expectation with respect to `dyadicFiltration N`, which averages a function over each
of the `N` dyadic cells numbered `N, …, 2 * N - 1`. These are the initial projections of the Haar
basis (`haarBasis_proj`). -/
def dyadicProj (N : ℕ) : Lp 𝕜 p (volume : Measure I) →L[𝕜] Lp 𝕜 p (volume : Measure I) :=
  if N = 0 then 0 else condExpLp 𝕜 (dyadicFiltration N) p volume

/-- The dyadic averaging projection of rank `0` is `0`. -/
@[simp]
theorem dyadicProj_zero : dyadicProj 𝕜 p 0 = 0 :=
  ite_eq_left rfl

/-- For `N ≠ 0`, `dyadicProj 𝕜 p N` is conditional expectation on `Lᵖ` given
`dyadicFiltration N`. -/
theorem dyadicProj_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    dyadicProj 𝕜 p N = condExpLp 𝕜 (dyadicFiltration N) p volume :=
  ite_eq_right hN

variable {𝕜 p}

/-- For `N ≠ 0`, `dyadicProj 𝕜 p N f` agrees a.e. with the conditional expectation of `f` given
`dyadicFiltration N`. -/
theorem dyadicProj_ae_eq {N : ℕ} (hN : N ≠ 0) (f : Lp 𝕜 p (volume : Measure I)) :
    dyadicProj 𝕜 p N f =ᵐ[volume] volume[f | dyadicFiltration N] := by
  rw [dyadicProj_of_ne_zero 𝕜 p hN]
  exact condExpLp_ae_eq f

/-- For `N ≠ 0`, the dyadic averaging projection of `f` is a.e. the conditional expectation of any
a.e. representative `g` of `f`. -/
theorem dyadicProj_ae_eq_of_ae_eq {N : ℕ} (hN : N ≠ 0) {f : Lp 𝕜 p (volume : Measure I)}
    {g : I → 𝕜} (hfg : f =ᵐ[volume] g) :
    dyadicProj 𝕜 p N f =ᵐ[volume] volume[g | dyadicFiltration N] :=
  (dyadicProj_ae_eq hN f).trans (condExp_congr_ae hfg)

variable (𝕜 p) in
/-- The dyadic averaging projections are contractions. -/
theorem norm_dyadicProj_le (N : ℕ) : ‖dyadicProj 𝕜 p N‖ ≤ 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · rw [dyadicProj_of_ne_zero 𝕜 p hN]
    exact norm_condExpLp_le 𝕜 _ p volume

variable (𝕜 p) in
/-- **The composition law of the dyadic averaging projections.** -/
@[simp]
theorem dyadicProj_dyadicProj (n m : ℕ) (f : Lp 𝕜 p (volume : Measure I)) :
    dyadicProj 𝕜 p n (dyadicProj 𝕜 p m f) = dyadicProj 𝕜 p (min n m) f := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hnm : min n m ≠ 0 := by omega
  -- The tower property when `n ≤ m`; otherwise the inner conditional expectation is already
  -- measurable for the outer σ-algebra.
  have key : volume[volume[f | dyadicFiltration m] | dyadicFiltration n] =ᵐ[volume]
      volume[f | dyadicFiltration (min n m)] := by
    rcases le_total n m with h | h
    · rw [min_eq_left h]
      exact condExp_condExp_of_le (dyadicFiltration.mono h) (dyadicFiltration.le m)
    · rw [min_eq_right h]
      exact (condExp_of_stronglyMeasurable (dyadicFiltration.le n)
        (stronglyMeasurable_condExp.mono (dyadicFiltration.mono h)) integrable_condExp).eventuallyEq
  exact Lp.ext ((dyadicProj_ae_eq_of_ae_eq hn (dyadicProj_ae_eq hm f)).trans
    (key.trans (dyadicProj_ae_eq hnm f).symm))

variable (𝕜 p) in
/-- The composition law of the dyadic averaging projections, as operators. -/
@[simp]
theorem dyadicProj_comp_dyadicProj (n m : ℕ) :
    dyadicProj 𝕜 p n ∘L dyadicProj 𝕜 p m = dyadicProj 𝕜 p (min n m) :=
  ContinuousLinearMap.ext (dyadicProj_dyadicProj 𝕜 p n m)

/-- **The dyadic averaging projections converge strongly to the identity** on `Lᵖ(I; 𝕜)`,
`1 ≤ p < ∞`. -/
theorem tendsto_dyadicProj (hp : p ≠ ∞) (f : Lp 𝕜 p (volume : Measure I)) :
    Tendsto (fun N => dyadicProj 𝕜 p N f) atTop (𝓝 f) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine (tendsto_eLpNorm_condExp_dyadicFiltration Fact.out hp (Lp.memLp f)).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  exact eLpNorm_congr_ae ((dyadicProj_ae_eq hN f).symm.sub EventuallyEq.rfl)

/-- The Haar function `hₙ` is fixed by the dyadic averaging projection of rank `n + 1`. -/
private theorem dyadicProj_succ_haarFun (n : ℕ) :
    dyadicProj 𝕜 p (n + 1) ((memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜))) =
      (memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜)) := by
  refine Lp.ext
    ((dyadicProj_ae_eq_of_ae_eq n.succ_ne_zero (memLp_ofReal_haarFun 𝕜 p n).coeFn_toLp).trans ?_)
  have hmeas : StronglyMeasurable[dyadicFiltration (n + 1)] (fun x => (haarFun n x : 𝕜)) :=
    RCLike.continuous_ofReal.comp_stronglyMeasurable
      (measurable_haarFun_dyadicFiltration n).stronglyMeasurable
  rw [condExp_of_stronglyMeasurable (dyadicFiltration.le _) hmeas
    ((memLp_ofReal_haarFun 𝕜 1 n).integrable le_rfl)]
  exact (memLp_ofReal_haarFun 𝕜 p n).coeFn_toLp.symm

/-- The Haar function `hₙ` is annihilated by the dyadic averaging projection of rank `n`. -/
private theorem dyadicProj_haarFun_self (n : ℕ) :
    dyadicProj 𝕜 p n ((memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜))) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  exact Lp.ext (((dyadicProj_ae_eq_of_ae_eq hn.ne' (memLp_ofReal_haarFun 𝕜 p n).coeFn_toLp).trans
    (condExp_ofReal_haarFun 𝕜 hn)).trans (Lp.coeFn_zero 𝕜 p (volume : Measure I)).symm)

/-- The Haar function `hₙ` is fixed by the dyadic averaging projections of rank above `n`, and
annihilated by the others. -/
private theorem dyadicProj_haarFun (N n : ℕ) :
    dyadicProj 𝕜 p N ((memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜))) =
      if n < N then (memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜)) else 0 := by
  split_ifs with h
  · rw [← dyadicProj_succ_haarFun n, dyadicProj_dyadicProj, min_eq_right (by omega)]
  · calc dyadicProj 𝕜 p N ((memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜)))
        = dyadicProj 𝕜 p (min N n)
            ((memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜))) := by
          rw [min_eq_left (by omega)]
      _ = 0 := by rw [← dyadicProj_dyadicProj, dyadicProj_haarFun_self, map_zero]

omit [Fact (1 ≤ p)] in
private theorem haarFun_toLp_ne_zero (n : ℕ) :
    (memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜)) ≠ 0 := by
  intro h
  have h0 : (fun x => (haarFun n x : 𝕜)) =ᵐ[volume] 0 :=
    (memLp_ofReal_haarFun 𝕜 p n).coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.1 h)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨x, hx⟩ := h0.exists
    simp at hx
  · -- `hₙ` is `1` on the dyadic cell numbered `2 * n`, which has positive volume.
    have hnull : volume (dyadicCell (2 * n)) = 0 :=
      measure_mono_null (fun x hx => by simp [haarFun_eq_one hn hx]) (ae_iff.1 h0)
    rw [volume_dyadicCell (by omega)] at hnull
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _) hnull

private theorem linearIndependent_haarFun_toLp (N : ℕ) :
    LinearIndependent 𝕜 fun i : Fin N =>
      (memLp_ofReal_haarFun 𝕜 p i).toLp (fun x => (haarFun i x : 𝕜)) := by
  refine linearIndependent_iff'.2 fun s g hg i hi => ?_
  -- Apply `dyadicProj 𝕜 p (i + 1) - dyadicProj 𝕜 p i`, which keeps exactly the `i`-th term.
  have h := congrArg (dyadicProj 𝕜 p (i + 1) - dyadicProj 𝕜 p i) hg
  simp only [map_sum, map_smul, map_zero, sub_apply, dyadicProj_haarFun]
    at h
  rw [Finset.sum_eq_single_of_mem i hi fun j _ hji => by
    have := Fin.val_ne_of_ne hji
    split_ifs <;> first | omega | simp] at h
  rw [ite_eq_left (by omega), ite_eq_right (by omega), sub_zero] at h
  exact (smul_eq_zero.1 h).resolve_right (haarFun_toLp_ne_zero i)

/-- **The dyadic averaging projections average over the atoms.** For `0 < N`, the projection
`dyadicProj 𝕜 p N f` is the step function equal on each dyadic cell numbered `N, …, 2 * N - 1` to
the average of `f` over that cell. -/
theorem dyadicProj_eq_sum {N : ℕ} (hN : 0 < N) (f : Lp 𝕜 p (volume : Measure I)) :
    dyadicProj 𝕜 p N f = ∑ n ∈ Finset.Ico N (2 * N), (⨍ y in dyadicCell n, f y) •
      indicatorConstLp p (measurableSet_dyadicCell n) (measure_ne_top _ _) (1 : 𝕜) := by
  refine Lp.ext ?_
  have hv (n : ℕ) : ⇑((⨍ y in dyadicCell n, f y) •
      indicatorConstLp p (measurableSet_dyadicCell n) (measure_ne_top _ _) (1 : 𝕜)) =ᵐ[volume]
      (⨍ y in dyadicCell n, f y) • (dyadicCell n).indicator fun _ => (1 : 𝕜) :=
    (Lp.coeFn_smul _ _).trans (indicatorConstLp_coeFn.const_smul _)
  filter_upwards [dyadicProj_ae_eq hN.ne' f,
    condExp_dyadicFiltration_ae_eq hN ((Lp.memLp f).integrable Fact.out),
    Lp.coeFn_finsetSum (Finset.Ico N (2 * N)) fun n => (⨍ y in dyadicCell n, f y) •
      indicatorConstLp p (measurableSet_dyadicCell n) (measure_ne_top _ _) (1 : 𝕜),
    ae_all_iff.2 hv] with x h1 h2 h3 h4
  have hx := dyadicAtom_mem_Ico hN x
  rw [h1, h2, h3, Finset.sum_apply, Finset.sum_eq_single_of_mem (dyadicAtom N x)
    (Finset.mem_Ico.2 hx), h4]
  · simp [Set.indicator_of_mem (mem_dyadicCell_dyadicAtom N x)]
  · intro n hn hnx
    rw [h4, Pi.smul_apply, Set.indicator_of_notMem fun hc =>
      hnx ((dyadicAtom_eq_iff (Finset.mem_Ico.1 hn)).2 hc).symm, smul_zero]

variable (𝕜 p) in
/-- The dyadic averaging projection of rank `N` has rank `N`: its range lies in the span of the
indicators of the `N` atoms of `dyadicFiltration N`, and contains the `N` linearly independent
Haar functions `h₀, …, h_{N-1}`. -/
theorem finrank_range_dyadicProj (N : ℕ) :
    Module.finrank 𝕜 (dyadicProj 𝕜 p N).toLinearMap.range = N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [dyadicProj_zero, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, finrank_bot]
  set R := (dyadicProj 𝕜 p N).toLinearMap.range
  let v (n : ℕ) : Lp 𝕜 p (volume : Measure I) :=
    indicatorConstLp p (measurableSet_dyadicCell n) (measure_ne_top _ _) (1 : 𝕜)
  have hle : R ≤ Submodule.span 𝕜 ((Finset.Ico N (2 * N)).image v : Set _) := by
    rintro _ ⟨f, rfl⟩
    rw [ContinuousLinearMap.coe_coe, dyadicProj_eq_sum hN]
    exact Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem v hn)))
  have : FiniteDimensional 𝕜 R := Submodule.finiteDimensional_of_le hle
  refine le_antisymm ((Submodule.finrank_mono hle).trans
    ((finrank_span_finset_le_card _).trans
      (Finset.card_image_le.trans (by rw [Nat.card_Ico]; omega)))) ?_
  have hli : LinearIndependent 𝕜 fun i : Fin N =>
      (⟨(memLp_ofReal_haarFun 𝕜 p i).toLp (fun x => (haarFun i x : 𝕜)), _, by
        rw [ContinuousLinearMap.coe_coe, dyadicProj_haarFun, ite_eq_left i.2]⟩ : R) :=
    LinearIndependent.of_comp R.subtype (linearIndependent_haarFun_toLp N)
  simpa using hli.fintype_card_le_finrank

/-! ### The Haar basis -/

variable (𝕜 p) in
/-- **The Haar basis of `Lᵖ([0, 1]; 𝕜)`**, `1 ≤ p < ∞`: the Haar functions `haarFun n`, in their
breadth-first order, form a Schauder basis of `Lᵖ(I; 𝕜)` whose initial projections are the dyadic
averaging projections (`haarBasis_proj`). -/
def haarBasis (hp : p ≠ ∞) : SchauderBasis 𝕜 (Lp 𝕜 p (volume : Measure I)) :=
  SchauderBasis.RankOneDecomposition.basis
    { P := dyadicProj 𝕜 p
      e n := (memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜))
      proj_zero := dyadicProj_zero 𝕜 p
      finrank_range := finrank_range_dyadicProj 𝕜 p
      proj_comp := dyadicProj_dyadicProj 𝕜 p
      proj_tendsto := tendsto_dyadicProj hp
      e_mem_range n := ⟨(memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜)), by
        rw [ContinuousLinearMap.coe_coe, SchauderBasis.succSub, sub_apply,
          dyadicProj_succ_haarFun, dyadicProj_haarFun_self, sub_zero]⟩
      e_ne_zero := haarFun_toLp_ne_zero }

/-- The `n`-th vector of `haarBasis` is the `Lᵖ` class of `haarFun n`. -/
@[simp]
theorem haarBasis_apply (hp : p ≠ ∞) (n : ℕ) :
    haarBasis 𝕜 p hp n = (memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜)) :=
  congrFun (SchauderBasis.RankOneDecomposition.basis_coe _) n

/-- The `n`-th vector of the Haar basis is a.e. the Haar function `hₙ`. -/
theorem coeFn_haarBasis (hp : p ≠ ∞) (n : ℕ) :
    haarBasis 𝕜 p hp n =ᵐ[volume] fun x => (haarFun n x : 𝕜) :=
  (memLp_ofReal_haarFun 𝕜 p n).coeFn_toLp

/-- The initial projections of the Haar basis are the dyadic averaging projections. -/
@[simp]
theorem haarBasis_proj (hp : p ≠ ∞) : (haarBasis 𝕜 p hp).proj = dyadicProj 𝕜 p :=
  SchauderBasis.RankOneDecomposition.basis_proj _

end TauCeti.unitInterval
