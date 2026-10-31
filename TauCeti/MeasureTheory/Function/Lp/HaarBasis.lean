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

For `1 ≤ p < ∞` the Haar system is a Schauder basis of `Lᵖ(I)`. Its initial projections are the
dyadic averaging projections `dyadicProj p N`: for `0 < N` this is conditional expectation with
respect to `dyadicFiltration N`, the σ-algebra whose atoms are the `N` dyadic cells numbered
`N, …, 2 * N - 1`, so it replaces a function on each atom by its average there. These projections
are contractions, compose by `dyadicProj p n ∘ dyadicProj p m = dyadicProj p (min n m)`, and
converge strongly to the identity by the martingale convergence theorem. The basis is assembled
from them by Mathlib's `SchauderBasis.RankOneDecomposition`: `dyadicProj p N` has rank `N`, and
`hₙ` spans the range of `dyadicProj p (n + 1) - dyadicProj p n`.

## Main definitions

* `TauCeti.unitInterval.haarFun n`: the `n`-th Haar function.
* `TauCeti.unitInterval.dyadicProj p N`: the dyadic averaging projection of rank `N` on `Lᵖ(I)`.
* `TauCeti.unitInterval.haarBasis p hp`: the Haar basis of `Lᵖ(I)`, `1 ≤ p < ∞`.

## Main results

* `TauCeti.unitInterval.condExp_haarFun`: `hₙ` has conditional expectation zero given
  `dyadicFiltration n`, for `0 < n`.
* `TauCeti.unitInterval.dyadicProj_eq_sum`: the projections average over the dyadic atoms.
* `TauCeti.unitInterval.dyadicProj_dyadicProj`: the composition law of the projections.
* `TauCeti.unitInterval.tendsto_dyadicProj`: the projections converge strongly to the identity.
* `TauCeti.unitInterval.finrank_range_dyadicProj`: `dyadicProj p N` has rank `N`.
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

@[simp]
theorem haarFun_zero : haarFun 0 = 1 :=
  funext fun _ => ite_eq_left rfl

theorem haarFun_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    haarFun n = (dyadicCell (2 * n)).indicator 1 - (dyadicCell (2 * n + 1)).indicator 1 :=
  funext fun _ => ite_eq_right hn

/-- The halves of a positively numbered dyadic cell lie one level below it. -/
private theorem log_two_mul_add {n e : ℕ} (hn : 0 < n) (he : e < 2) :
    Nat.log 2 (2 * n + e) = Nat.log 2 n + 1 := by
  rw [Nat.log_of_one_lt_of_le one_lt_two (by omega)]
  congr 2
  omega

/-- A point of either half of the dyadic cell numbered `n` lies in that cell. -/
private theorem mem_dyadicCell_of_mem_two_mul_add {n e : ℕ} (hn : 0 < n) (he : e < 2) {x : I}
    (hx : x ∈ dyadicCell (2 * n + e)) : x ∈ dyadicCell n := by
  have h := mem_dyadicCell_div_two (by omega) hx
  rwa [show (2 * n + e) / 2 = n by omega] at h

/-- For `0 < n`, the Haar function `hₙ` vanishes outside the dyadic cell numbered `n`. -/
theorem haarFun_eq_zero {n : ℕ} (hn : 0 < n) {x : I} (hx : x ∉ dyadicCell n) : haarFun n x = 0 := by
  have h0 : x ∉ dyadicCell (2 * n + 0) := mt (mem_dyadicCell_of_mem_two_mul_add hn two_pos) hx
  have h1 : x ∉ dyadicCell (2 * n + 1) := mt (mem_dyadicCell_of_mem_two_mul_add hn one_lt_two) hx
  rw [add_zero] at h0
  simp [haarFun_of_ne_zero hn.ne', h0, h1]

/-- For `0 < n`, the Haar function `hₙ` is `1` on the dyadic cell numbered `2 * n`. -/
theorem haarFun_eq_one {n : ℕ} (hn : 0 < n) {x : I} (hx : x ∈ dyadicCell (2 * n)) :
    haarFun n x = 1 := by
  have hlog : Nat.log 2 (2 * n) = Nat.log 2 (2 * n + 1) := by
    rw [← add_zero (2 * n), log_two_mul_add hn two_pos, add_zero, log_two_mul_add hn one_lt_two]
  have h1 : x ∉ dyadicCell (2 * n + 1) :=
    Set.disjoint_left.1 (disjoint_dyadicCell hlog (by omega)) hx
  simp [haarFun_of_ne_zero hn.ne', hx, h1]

/-- The Haar functions take values in `{-1, 0, 1}`. -/
theorem norm_haarFun_le (n : ℕ) (x : I) : ‖haarFun n x‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [haarFun_of_ne_zero hn, Pi.sub_apply]
    simp only [Set.indicator, Pi.one_apply]
    split_ifs <;> norm_num

@[fun_prop]
theorem measurable_haarFun (n : ℕ) : Measurable (haarFun n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [haarFun_zero]
    exact measurable_const
  · rw [haarFun_of_ne_zero hn]
    exact (measurable_const.indicator (measurableSet_dyadicCell _)).sub
      (measurable_const.indicator (measurableSet_dyadicCell _))

/-- The Haar functions lie in every `Lᵖ(I)`. -/
theorem memLp_haarFun (p : ℝ≥0∞) (n : ℕ) : MemLp (haarFun n) p :=
  MemLp.of_bound (measurable_haarFun n).aestronglyMeasurable 1
    (ae_of_all _ (norm_haarFun_le n))

/-- The Haar function `hₙ` is measurable for the dyadic filtration at step `n + 1`. -/
theorem measurable_haarFun_dyadicFiltration (n : ℕ) :
    Measurable[dyadicFiltration (n + 1)] (haarFun n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [haarFun_zero]
    exact measurable_const
  · rw [haarFun_of_ne_zero hn]
    exact (measurable_const.indicator (measurableSet_dyadicFiltration_dyadicCell (by omega))).sub
      (measurable_const.indicator (measurableSet_dyadicFiltration_dyadicCell (by omega)))

/-- For `0 < n`, the Haar function `hₙ` has integral zero. -/
theorem integral_haarFun {n : ℕ} (hn : 0 < n) : ∫ x, haarFun n x = 0 := by
  have hint (m : ℕ) : Integrable ((dyadicCell m).indicator (1 : I → ℝ)) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_dyadicCell m)
  simp only [haarFun_of_ne_zero hn.ne', Pi.sub_apply]
  rw [integral_sub (hint _) (hint _),
    integral_indicator_one (measurableSet_dyadicCell _),
    integral_indicator_one (measurableSet_dyadicCell _), Measure.real, Measure.real,
    volume_dyadicCell (by omega), volume_dyadicCell (by omega), ← add_zero (2 * n),
    log_two_mul_add hn two_pos, add_zero, log_two_mul_add hn one_lt_two, sub_self]

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
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      haarFun_eq_zero hn fun hc => hx ((dyadicAtom_eq_iff hmem).2 hc), integral_haarFun hn]
  · exact (setIntegral_eq_zero_of_forall_eq_zero fun x (hx : dyadicAtom n x = j) =>
      haarFun_eq_zero hn fun hc => hj (hx.symm.trans ((dyadicAtom_eq_iff hmem).2 hc))).symm

/-! ### The dyadic averaging projections -/

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The dyadic averaging projection of rank `N` on `Lᵖ(I)`: `0` for `N = 0`, and for `0 < N`
conditional expectation with respect to `dyadicFiltration N`, which averages a function over each
of the `N` dyadic cells numbered `N, …, 2 * N - 1`. These are the initial projections of the Haar
basis (`haarBasis_proj`). -/
def dyadicProj (N : ℕ) : Lp ℝ p (volume : Measure I) →L[ℝ] Lp ℝ p (volume : Measure I) :=
  if N = 0 then 0 else condExpLp ℝ (dyadicFiltration N) p volume

@[simp]
theorem dyadicProj_zero : dyadicProj p 0 = 0 :=
  ite_eq_left rfl

theorem dyadicProj_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    dyadicProj p N = condExpLp ℝ (dyadicFiltration N) p volume :=
  ite_eq_right hN

variable {p}

theorem dyadicProj_ae_eq {N : ℕ} (hN : N ≠ 0) (f : Lp ℝ p (volume : Measure I)) :
    dyadicProj p N f =ᵐ[volume] volume[f | dyadicFiltration N] := by
  rw [dyadicProj_of_ne_zero p hN]
  exact condExpLp_ae_eq f

variable (p) in
/-- The dyadic averaging projections are contractions. -/
theorem norm_dyadicProj_le (N : ℕ) : ‖dyadicProj p N‖ ≤ 1 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · rw [dyadicProj_of_ne_zero p hN]
    exact norm_condExpLp_le ℝ _ p volume

variable (p) in
/-- **The composition law of the dyadic averaging projections.** -/
theorem dyadicProj_dyadicProj (n m : ℕ) (f : Lp ℝ p (volume : Measure I)) :
    dyadicProj p n (dyadicProj p m f) = dyadicProj p (min n m) f := by
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
  refine Lp.ext ?_
  filter_upwards [dyadicProj_ae_eq hn (dyadicProj p m f),
    condExp_congr_ae (m := dyadicFiltration n) (dyadicProj_ae_eq hm f), key,
    dyadicProj_ae_eq hnm f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- **The dyadic averaging projections converge strongly to the identity** on `Lᵖ(I)`,
`1 ≤ p < ∞`. -/
theorem tendsto_dyadicProj (hp : p ≠ ∞) (f : Lp ℝ p (volume : Measure I)) :
    Tendsto (fun N => dyadicProj p N f) atTop (𝓝 f) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  refine (tendsto_eLpNorm_condExp_dyadicFiltration Fact.out hp (Lp.memLp f)).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  exact eLpNorm_congr_ae ((dyadicProj_ae_eq hN f).symm.sub EventuallyEq.rfl)

/-- The Haar function `hₙ` is fixed by the dyadic averaging projection of rank `n + 1`. -/
private theorem dyadicProj_succ_haarFun (n : ℕ) :
    dyadicProj p (n + 1) ((memLp_haarFun p n).toLp (haarFun n)) =
      (memLp_haarFun p n).toLp (haarFun n) := by
  refine Lp.ext ?_
  filter_upwards [dyadicProj_ae_eq n.succ_ne_zero ((memLp_haarFun p n).toLp (haarFun n)),
    condExp_congr_ae (m := dyadicFiltration (n + 1)) (memLp_haarFun p n).coeFn_toLp,
    (memLp_haarFun p n).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, h3, condExp_of_stronglyMeasurable (dyadicFiltration.le _)
    (measurable_haarFun_dyadicFiltration n).stronglyMeasurable
    ((memLp_haarFun 1 n).integrable le_rfl)]

/-- The Haar function `hₙ` is annihilated by the dyadic averaging projection of rank `n`. -/
private theorem dyadicProj_haarFun_self (n : ℕ) :
    dyadicProj p n ((memLp_haarFun p n).toLp (haarFun n)) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine Lp.ext ?_
  filter_upwards [dyadicProj_ae_eq hn.ne' ((memLp_haarFun p n).toLp (haarFun n)),
    condExp_congr_ae (m := dyadicFiltration n) (memLp_haarFun p n).coeFn_toLp,
    condExp_haarFun hn, Lp.coeFn_zero ℝ p (volume : Measure I)] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- The Haar function `hₙ` is fixed by the dyadic averaging projections of rank above `n`, and
annihilated by the others. -/
private theorem dyadicProj_haarFun (N n : ℕ) :
    dyadicProj p N ((memLp_haarFun p n).toLp (haarFun n)) =
      if n < N then (memLp_haarFun p n).toLp (haarFun n) else 0 := by
  split_ifs with h
  · rw [← dyadicProj_succ_haarFun n, dyadicProj_dyadicProj, min_eq_right (by omega)]
  · calc dyadicProj p N ((memLp_haarFun p n).toLp (haarFun n))
        = dyadicProj p (min N n) ((memLp_haarFun p n).toLp (haarFun n)) := by
          rw [min_eq_left (by omega)]
      _ = 0 := by rw [← dyadicProj_dyadicProj, dyadicProj_haarFun_self, map_zero]

omit [Fact (1 ≤ p)] in
private theorem haarFun_toLp_ne_zero (n : ℕ) : (memLp_haarFun p n).toLp (haarFun n) ≠ 0 := by
  intro h
  have h0 : haarFun n =ᵐ[volume] 0 :=
    (memLp_haarFun p n).coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.1 h)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨x, hx⟩ := h0.exists
    simp at hx
  · -- `hₙ` is `1` on the dyadic cell numbered `2 * n`, which has positive volume.
    have hnull : volume (dyadicCell (2 * n)) = 0 :=
      measure_mono_null (fun x hx => by simp [haarFun_eq_one hn hx]) (ae_iff.1 h0)
    rw [volume_dyadicCell (by omega)] at hnull
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _) hnull

private theorem linearIndependent_haarFun_toLp (N : ℕ) :
    LinearIndependent ℝ fun i : Fin N => (memLp_haarFun p i).toLp (haarFun i) := by
  refine linearIndependent_iff'.2 fun s g hg i hi => ?_
  -- Apply `dyadicProj p (i + 1) - dyadicProj p i`, which keeps exactly the `i`-th term.
  have h := congrArg (dyadicProj p (i + 1) - dyadicProj p i) hg
  simp only [map_sum, map_smul, map_zero, sub_apply, dyadicProj_haarFun]
    at h
  rw [Finset.sum_eq_single_of_mem i hi fun j _ hji => by
    have := Fin.val_ne_of_ne hji
    split_ifs <;> first | omega | simp] at h
  rw [ite_eq_left (by omega), ite_eq_right (by omega), sub_zero] at h
  exact (smul_eq_zero.1 h).resolve_right (haarFun_toLp_ne_zero i)

/-- **The dyadic averaging projections average over the atoms.** For `0 < N`, the projection
`dyadicProj p N f` is the step function equal on each dyadic cell numbered `N, …, 2 * N - 1` to the
average of `f` over that cell. -/
theorem dyadicProj_eq_sum {N : ℕ} (hN : 0 < N) (f : Lp ℝ p (volume : Measure I)) :
    dyadicProj p N f = ∑ n ∈ Finset.Ico N (2 * N), (⨍ y in dyadicCell n, f y) •
      indicatorConstLp p (measurableSet_dyadicCell n) (measure_ne_top _ _) (1 : ℝ) := by
  refine Lp.ext ?_
  have hv (n : ℕ) : ⇑((⨍ y in dyadicCell n, f y) •
      indicatorConstLp p (measurableSet_dyadicCell n) (measure_ne_top _ _) (1 : ℝ)) =ᵐ[volume]
      (⨍ y in dyadicCell n, f y) • (dyadicCell n).indicator fun _ => (1 : ℝ) :=
    (Lp.coeFn_smul _ _).trans (indicatorConstLp_coeFn.const_smul _)
  filter_upwards [dyadicProj_ae_eq hN.ne' f,
    condExp_dyadicFiltration_ae_eq hN ((Lp.memLp f).integrable Fact.out),
    Lp.coeFn_finsetSum (Finset.Ico N (2 * N)) fun n => (⨍ y in dyadicCell n, f y) •
      indicatorConstLp p (measurableSet_dyadicCell n) (measure_ne_top _ _) (1 : ℝ),
    ae_all_iff.2 hv] with x h1 h2 h3 h4
  have hx := dyadicAtom_mem_Ico hN x
  rw [h1, h2, h3, Finset.sum_apply, Finset.sum_eq_single_of_mem (dyadicAtom N x)
    (Finset.mem_Ico.2 hx), h4]
  · simp [Set.indicator_of_mem (mem_dyadicCell_dyadicAtom N x)]
  · intro n hn hnx
    rw [h4, Pi.smul_apply, Set.indicator_of_notMem fun hc =>
      hnx ((dyadicAtom_eq_iff (Finset.mem_Ico.1 hn)).2 hc).symm, smul_zero]

variable (p) in
/-- The dyadic averaging projection of rank `N` has rank `N`: its range lies in the span of the
indicators of the `N` atoms of `dyadicFiltration N`, and contains the `N` linearly independent
Haar functions `h₀, …, h_{N-1}`. -/
theorem finrank_range_dyadicProj (N : ℕ) :
    Module.finrank ℝ (dyadicProj p N).toLinearMap.range = N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [dyadicProj_zero, ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, finrank_bot]
  set R := (dyadicProj p N).toLinearMap.range
  let v (n : ℕ) : Lp ℝ p (volume : Measure I) :=
    indicatorConstLp p (measurableSet_dyadicCell n) (measure_ne_top _ _) (1 : ℝ)
  have hle : R ≤ Submodule.span ℝ ((Finset.Ico N (2 * N)).image v : Set _) := by
    rintro _ ⟨f, rfl⟩
    rw [ContinuousLinearMap.coe_coe, dyadicProj_eq_sum hN]
    exact Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem v hn)))
  have : FiniteDimensional ℝ R := Submodule.finiteDimensional_of_le hle
  refine le_antisymm ((Submodule.finrank_mono hle).trans
    ((finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by simp; omega)))) ?_
  have hli : LinearIndependent ℝ fun i : Fin N =>
      (⟨(memLp_haarFun p i).toLp (haarFun i), _, by
        rw [ContinuousLinearMap.coe_coe, dyadicProj_haarFun, ite_eq_left i.2]⟩ : R) :=
    LinearIndependent.of_comp R.subtype (linearIndependent_haarFun_toLp N)
  simpa using hli.fintype_card_le_finrank

/-! ### The Haar basis -/

variable (p) in
/-- **The Haar basis of `Lᵖ([0, 1])`**, `1 ≤ p < ∞`: the Haar functions `haarFun n`, in their
breadth-first order, form a Schauder basis of `Lᵖ(I)` whose initial projections are the dyadic
averaging projections (`haarBasis_proj`). -/
def haarBasis (hp : p ≠ ∞) : SchauderBasis ℝ (Lp ℝ p (volume : Measure I)) :=
  SchauderBasis.RankOneDecomposition.basis
    { P := dyadicProj p
      e n := (memLp_haarFun p n).toLp (haarFun n)
      proj_zero := dyadicProj_zero p
      finrank_range := finrank_range_dyadicProj p
      proj_comp := dyadicProj_dyadicProj p
      proj_tendsto := tendsto_dyadicProj hp
      e_mem_range n := ⟨(memLp_haarFun p n).toLp (haarFun n), by
        rw [ContinuousLinearMap.coe_coe, SchauderBasis.succSub, sub_apply,
          dyadicProj_succ_haarFun, dyadicProj_haarFun_self, sub_zero]⟩
      e_ne_zero := haarFun_toLp_ne_zero }

theorem haarBasis_apply (hp : p ≠ ∞) (n : ℕ) :
    haarBasis p hp n = (memLp_haarFun p n).toLp (haarFun n) :=
  (rfl)

/-- The `n`-th vector of the Haar basis is a.e. the Haar function `hₙ`. -/
theorem coeFn_haarBasis (hp : p ≠ ∞) (n : ℕ) : haarBasis p hp n =ᵐ[volume] haarFun n :=
  (memLp_haarFun p n).coeFn_toLp

/-- The initial projections of the Haar basis are the dyadic averaging projections. -/
@[simp]
theorem haarBasis_proj (hp : p ≠ ∞) : (haarBasis p hp).proj = dyadicProj p :=
  SchauderBasis.RankOneDecomposition.basis_proj _

end TauCeti.unitInterval
