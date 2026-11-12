/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Topology.Bases
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Norming mixed `L^p_t L^q_x` norms

Let `F : T → L²(X, E)` be a family of square-integrable functions indexed by a σ-finite measure
space `T`, for instance a solution `t ↦ u(t)` of an evolution equation. Its mixed norm

`‖F‖_{L^p_t L^q_x} = ‖t ↦ ‖F t‖_{L^q(X)}‖_{L^p(T)}`

is written `eLpNorm (fun t ↦ eLpNorm (F t) q μ) p ν`. This file proves the duality bound for
mixed norms: if

`|∫ ⟪F t, G t⟫ dt| ≤ C ‖G‖_{L^{p'}_t L^{q'}_x}`

for every bounded `G : T → L²(X, E)` vanishing off a set of finite measure, then
`‖F‖_{L^p_t L^q_x} ≤ C`, for Hölder conjugate pairs `(p, p')`, `(q, q')` with `p < ∞`
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`).
Bounds proved by duality, such as the Strichartz estimates obtained from the `TT*` argument, come
in this tested form, and this theorem turns them into bounds on the mixed norm itself. The
finiteness of `‖F t‖_q` is not assumed: it follows for almost every `t` when `C < ∞`. The function
`t ↦ ‖F t‖_q` is almost everywhere measurable
(`MeasureTheory.AEStronglyMeasurable.aemeasurable_eLpNorm_Lp`).

## The argument

The difficulty is to choose, measurably in `t`, a test function `G t` that nearly norms `F t` in
`L^q`. Each single `h ∈ L²` is normed by test functions `g ∈ L²` in the unit ball of `L^{q'}`
(`MeasureTheory.Lp.exists_eLpNorm_le_one_and_lt_re_inner`). Almost every `F t` lies in a
separable set `S`, and on `S` countably many test functions suffice
(`TopologicalSpace.IsSeparable.exists_seq_eLpNorm_eq_iSup_ofReal_re_inner`): for each rational
level `c`, the sets `{h | c < re ⟪h, g⟫}` are open and cover `{h ∈ S | c < ‖h‖_q}`, and `S` is
Lindelöf. With such a sequence `gₘ`,

`‖F t‖_q = supₘ re ⟪F t, gₘ⟫`

for almost every `t`. For the bound, let `φ_N(t) = max_{m < N} (re ⟪F t, gₘ⟫)⁺`, choose
for each `t` the first index `m < N` attaining the maximum, and test against
`G t = φ_N(t) ^ (p - 1) gₘ` on a set of finite measure where `‖F t‖₂ ≤ N`. Then
`re ⟪F t, G t⟫ = φ_N(t) ^ p` and `‖G t‖_{q'} ≤ φ_N(t) ^ (p - 1)`, so the hypothesis gives
`‖φ_N‖_p ^ p ≤ C ‖φ_N‖_p ^ (p - 1)`, that is `‖φ_N‖_p ≤ C`. Fatou's lemma passes to the limit
`N → ∞`.

## Main declarations

* `TopologicalSpace.IsSeparable.exists_seq_eLpNorm_eq_iSup_ofReal_re_inner`: a countable family
  of test functions norming every element of a separable subset of `L²` in `L^q`.
* `MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`: the
  duality bound for mixed norms.

## References

* A. Benedek and R. Panzone, *The space `Lᵖ`, with mixed norm*, Duke Math. J. 28 (1961), 301–324,
  Section 2 (duality of mixed-norm spaces).
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3 (Strichartz estimates by duality).
-/

public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

variable {𝕜 X E : Type*} [RCLike 𝕜] {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace TopologicalSpace.IsSeparable

/-- **Countable norming families.** On a σ-finite measure space, let `q` and `q'` be Hölder
conjugate. For every separable set `S` of square-integrable functions there is a sequence `gₙ` of
square-integrable functions in the unit ball of `L^{q'}` which norms every element of `S` in
`L^q`:

`‖h‖_q = supₙ re ⟪h, gₙ⟫` for every `h ∈ S`,

whether `‖h‖_q` is finite or not. -/
theorem exists_seq_eLpNorm_eq_iSup_ofReal_re_inner [SigmaFinite μ] {q q' : ℝ≥0∞}
    [hqq : q.HolderConjugate q'] {S : Set (Lp E 2 μ)} (hS : IsSeparable S) :
    ∃ g : ℕ → Lp E 2 μ, (∀ n, eLpNorm (g n) q' μ ≤ 1) ∧
      ∀ h ∈ S, eLpNorm h q μ = ⨆ n, ENNReal.ofReal (RCLike.re ⟪h, g n⟫_𝕜) := by
  have := hS.separableSpace
  set Γ := {g : Lp E 2 μ // eLpNorm g q' μ ≤ 1}
  -- For each rational level `c`, countably many test functions cover `{h ∈ S | c < ‖h‖_q}`.
  have hcount : ∀ c : ℚ, ∃ D : Set Γ, D.Countable ∧
      ⋃ g ∈ D, {h : S | (c : ℝ) < RCLike.re ⟪(h : Lp E 2 μ), (g : Lp E 2 μ)⟫_𝕜} =
        ⋃ g : Γ, {h : S | (c : ℝ) < RCLike.re ⟪(h : Lp E 2 μ), (g : Lp E 2 μ)⟫_𝕜} := by
    intro c
    refine isOpen_iUnion_countable _ fun g ↦ isOpen_lt continuous_const ?_
    exact RCLike.continuous_re.comp ((continuous_subtype_val).inner continuous_const)
  choose D hDc hD using hcount
  set D' : Set (Lp E 2 μ) := insert 0 (⋃ c : ℚ, Subtype.val '' D c)
  have hD'c : D'.Countable :=
    (Set.countable_iUnion fun c ↦ (hDc c).image _).insert 0
  obtain ⟨g, hg⟩ := hD'c.exists_eq_range (Set.insert_nonempty _ _)
  have hgΓ : ∀ n, eLpNorm (g n) q' μ ≤ 1 := by
    intro n
    have hn : g n ∈ D' := hg ▸ Set.mem_range_self n
    rcases hn with hn | hn
    · rw [hn, eLpNorm_congr_ae (Lp.coeFn_zero E 2 μ)]
      simp
    · obtain ⟨c, hc⟩ := Set.mem_iUnion.1 hn
      obtain ⟨γ, -, hγ⟩ := hc
      exact hγ ▸ γ.2
  refine ⟨g, hgΓ, fun h hh ↦ le_antisymm ?_ (iSup_le fun n ↦ ?_)⟩
  · -- Below `‖h‖_q`, a rational level is exceeded by the pairing with some `gₙ`.
    refine le_of_forall_lt fun b hb ↦ ?_
    obtain ⟨c, hc0, hbc, hch⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hb
    obtain ⟨γ, hγ, hcγ⟩ := Lp.exists_eLpNorm_le_one_and_lt_re_inner (𝕜 := 𝕜) (q' := q') h
      (c := c) hch
    have hmem : (⟨h, hh⟩ : S) ∈ ⋃ γ : Γ,
        {h : S | (c : ℝ) < RCLike.re ⟪(h : Lp E 2 μ), (γ : Lp E 2 μ)⟫_𝕜} :=
      Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, hcγ⟩
    rw [← hD c] at hmem
    obtain ⟨γ', hγ'D, hγ'⟩ := Set.mem_iUnion₂.1 hmem
    have hγ'mem : (γ' : Lp E 2 μ) ∈ Set.range g :=
      hg ▸ Set.mem_insert_of_mem _ (Set.mem_iUnion.2 ⟨c, γ', hγ'D, rfl⟩)
    obtain ⟨n, hn⟩ := hγ'mem
    refine lt_iSup_iff.2 ⟨n, hbc.trans ?_⟩
    rw [hn]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by exact_mod_cast hc0)).2 hγ'
  · -- Hölder's inequality bounds each pairing.
    calc ENNReal.ofReal (RCLike.re ⟪h, g n⟫_𝕜) ≤ ‖⟪h, g n⟫_𝕜‖ₑ := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)
      _ ≤ eLpNorm h q μ * eLpNorm (g n) q' μ := by
          rw [L2.inner_def]
          exact TauCeti.enorm_integral_inner_le
      _ ≤ eLpNorm h q μ := mul_le_of_le_one_right' (hgΓ n)

end TopologicalSpace.IsSeparable

namespace MeasureTheory.AEStronglyMeasurable

variable {T : Type*} {mT : MeasurableSpace T} {ν : Measure T}

/-- The running maximum `max_{m < N} (aₘ t)⁺` of a sequence of real functions. -/
private noncomputable def runMax (a : ℕ → T → ℝ) : ℕ → T → ℝ≥0
  | 0 => fun _ ↦ 0
  | N + 1 => fun t ↦ runMax a N t ⊔ (a N t).toNNReal

/-- An index `m < N` at which the running maximum is attained, when it is positive: the last index
at which the running maximum strictly increased. -/
private noncomputable def runArgmax (a : ℕ → T → ℝ) : ℕ → T → ℕ
  | 0 => fun _ ↦ 0
  | N + 1 => fun t ↦ if runMax a N t < (a N t).toNNReal then N else runArgmax a N t

private theorem measurable_runMax {a : ℕ → T → ℝ} (ha : ∀ m, Measurable (a m)) (N : ℕ) :
    Measurable (runMax a N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih => exact ih.sup (ha N).real_toNNReal

private theorem measurable_runArgmax {a : ℕ → T → ℝ} (ha : ∀ m, Measurable (a m)) (N : ℕ) :
    Measurable (runArgmax a N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    exact Measurable.ite (measurableSet_lt (measurable_runMax ha N) (ha N).real_toNNReal)
      measurable_const ih

private theorem le_runMax {a : ℕ → T → ℝ} {m N : ℕ} (hm : m < N) (t : T) :
    (a m t).toNNReal ≤ runMax a N t := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact (ih hm).trans le_sup_left
    · exact le_sup_right

private theorem runMax_le {a : ℕ → T → ℝ} {N : ℕ} {t : T} {b : ℝ≥0}
    (h : ∀ m < N, (a m t).toNNReal ≤ b) : runMax a N t ≤ b := by
  induction N with
  | zero => exact bot_le
  | succ N ih => exact sup_le (ih fun m hm ↦ h m (hm.trans N.lt_succ_self)) (h N N.lt_succ_self)

private theorem monotone_runMax (a : ℕ → T → ℝ) (t : T) : Monotone fun N ↦ runMax a N t :=
  monotone_nat_of_le_succ fun _ ↦ le_sup_left

private theorem runArgmax_spec {a : ℕ → T → ℝ} {N : ℕ} {t : T} (h : runMax a N t ≠ 0) :
    runArgmax a N t < N ∧ (a (runArgmax a N t) t).toNNReal = runMax a N t := by
  induction N with
  | zero => exact absurd rfl h
  | succ N ih =>
    simp only [runArgmax, runMax] at h ⊢
    split_ifs with hlt
    · exact ⟨N.lt_succ_self, (sup_eq_right.2 hlt.le).symm⟩
    · have hle : (a N t).toNNReal ≤ runMax a N t := not_lt.1 hlt
      rw [sup_eq_left.2 hle] at h ⊢
      exact ⟨(ih h).1.trans N.lt_succ_self, (ih h).2⟩

private theorem iSup_runMax (a : ℕ → T → ℝ) (t : T) :
    ⨆ N, (runMax a N t : ℝ≥0∞) = ⨆ m, ENNReal.ofReal (a m t) := by
  refine le_antisymm (iSup_le fun N ↦ ?_) (iSup_le fun m ↦ ?_)
  · induction N with
    | zero => simp [runMax]
    | succ N ih =>
      exact (ENNReal.coe_max _ _).trans_le <| max_le ih (le_iSup (fun m ↦ ENNReal.ofReal (a m t)) N)
  · exact (ENNReal.coe_le_coe.2 (le_runMax m.lt_succ_self t)).trans (le_iSup_of_le (m + 1) le_rfl)

/-- **The testing step.** If a nonnegative `u ∈ L^p` and a test function `G` satisfy
`re ⟪F t, G t⟫ = u(t) ^ p` and `‖G t‖_{q'} ≤ u(t) ^ (p - 1)`, then the duality bound
`|∫ ⟪F t, G t⟫| ≤ C ‖G‖_{L^{p'}_t L^{q'}_x}` gives `‖u‖_p ≤ C`: the left side is `‖u‖_p ^ p` and
the right side is at most `C ‖u‖_p ^ (p - 1)`. -/
private theorem eLpNorm_le_of_re_inner_eq_rpow {p p' q' : ℝ≥0∞} [hpp : p.HolderConjugate p']
    (hp : p ≠ ∞) {C : ℝ≥0∞} {F G : T → Lp E 2 μ} {u : T → ℝ} (hu : MemLp u p ν)
    (hum : Measurable u) (hu0 : ∀ t, 0 ≤ u t) (hG : AEStronglyMeasurable G ν)
    (hint : Integrable (fun t ↦ ⟪F t, G t⟫_𝕜) ν)
    (hre : ∀ᵐ t ∂ν, RCLike.re ⟪F t, G t⟫_𝕜 = u t ^ p.toReal)
    (hGq : ∀ t, eLpNorm (G t) q' μ ≤ ENNReal.ofReal (u t ^ (p.toReal - 1)))
    (hC : ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν) :
    eLpNorm u p ν ≤ C := by
  have hp0 : p ≠ 0 := hpp.ne_zero
  set X := eLpNorm u p ν
  have hXr : X ^ p.toReal = ENNReal.ofReal (∫ t, u t ^ p.toReal ∂ν) := by
    rw [hu.eLpNorm_rpow_toReal_eq_enorm_integral (𝕜 := ℝ) hp0 hp,
      ← Real.enorm_eq_ofReal (integral_nonneg fun t ↦ Real.rpow_nonneg (hu0 t) _)]
    congr 2 with t
    rw [Real.norm_of_nonneg (hu0 t), RCLike.ofReal_real_eq_id, id]
  refine ENNReal.le_of_rpow_le_mul_rpow_sub_one (r := p.toReal) hu.eLpNorm_ne_top ?_
  calc X ^ p.toReal = ENNReal.ofReal (∫ t, u t ^ p.toReal ∂ν) := hXr
    _ = ENNReal.ofReal (RCLike.re (∫ t, ⟪F t, G t⟫_𝕜 ∂ν)) := by
        rw [← integral_re hint, integral_congr_ae (hre.mono fun t ht ↦ ht.symm)]
    _ ≤ ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)
    _ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν := hC
    _ ≤ C * eLpNorm (fun t ↦ u t ^ (p.toReal - 1)) p' ν := by
        gcongr
        refine eLpNorm_mono_enorm (hG.aemeasurable_eLpNorm_Lp
          Measure.AbsolutelyContinuous.rfl q').aestronglyMeasurable fun t ↦ ?_
        rw [enorm_eq_self, Real.enorm_eq_ofReal (Real.rpow_nonneg (hu0 t) _)]
        exact hGq t
    _ ≤ C * X ^ (p.toReal - 1) := by
        gcongr
        refine TauCeti.eLpNorm_le_eLpNorm_rpow_toReal_sub_one (q' := p') hp
          (hum.pow_const _).aestronglyMeasurable (ae_of_all _ fun t ↦ ?_)
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (hu0 t) _), Real.norm_of_nonneg (hu0 t)]

/-- **Fatou's lemma for `eLpNorm`**, for a limit with values in `ℝ≥0∞`: if `‖f_N‖ₑ → Φ` almost
everywhere and `‖f_N‖_p ≤ C` for every `N`, then `‖Φ‖_p ≤ C`. -/
private theorem eLpNorm_le_of_ae_tendsto_enorm {p : ℝ≥0∞} {C : ℝ≥0∞} {f : ℕ → T → ℝ}
    (hf : ∀ N, Measurable (f N)) {Φ : T → ℝ≥0∞} (hΦ : AEMeasurable Φ ν) (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hlim : ∀ᵐ t ∂ν, Tendsto (fun N ↦ ‖f N t‖ₑ) atTop (𝓝 (Φ t)))
    (hC : ∀ N, eLpNorm (f N) p ν ≤ C) : eLpNorm Φ p ν ≤ C := by
  have hr0 : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hΦ.aestronglyMeasurable]
  simp only [enorm_eq_self]
  have hint : ∫⁻ t, Φ t ^ p.toReal ∂ν ≤ C ^ p.toReal := by
    calc ∫⁻ t, Φ t ^ p.toReal ∂ν = ∫⁻ t, liminf (fun N ↦ ‖f N t‖ₑ ^ p.toReal) atTop ∂ν :=
          lintegral_congr_ae (hlim.mono fun t ht ↦
            (((ENNReal.continuous_rpow_const).tendsto _).comp ht).liminf_eq.symm)
      _ ≤ liminf (fun N ↦ ∫⁻ t, ‖f N t‖ₑ ^ p.toReal ∂ν) atTop :=
          lintegral_liminf_le' fun N ↦ ((hf N).enorm.pow_const _).aemeasurable
      _ ≤ C ^ p.toReal := liminf_le_of_frequently_le' (Frequently.of_forall fun N ↦ ?_)
    have hCN := hC N
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hf N).aestronglyMeasurable] at hCN
    calc ∫⁻ t, ‖f N t‖ₑ ^ p.toReal ∂ν
        = ((∫⁻ t, ‖f N t‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal)) ^ p.toReal := by
          rw [one_div, ENNReal.rpow_inv_rpow hr0]
      _ ≤ C ^ p.toReal := ENNReal.rpow_le_rpow hCN (by positivity)
  calc (∫⁻ t, Φ t ^ p.toReal ∂ν) ^ (1 / p.toReal) ≤ (C ^ p.toReal) ^ (1 / p.toReal) :=
        ENNReal.rpow_le_rpow hint (by positivity)
    _ = C := by rw [one_div, ENNReal.rpow_rpow_inv hr0]

/-- **Duality for mixed norms.** On σ-finite measure spaces `T` and `X`, let `(p, p')` and
`(q, q')` be Hölder conjugate pairs with `p < ∞`, and let `F : T → L²(X, E)` be almost everywhere
strongly measurable. If

`|∫ ⟪F t, G t⟫ dt| ≤ C ‖G‖_{L^{p'}_t L^{q'}_x}`

for every bounded `G : T → L²(X, E)` vanishing off a set of finite measure, then

`‖F‖_{L^p_t L^q_x} = ‖t ↦ ‖F t‖_{L^q(X)}‖_{L^p(T)} ≤ C`.

In particular `F t ∈ L^q` for almost every `t` as soon as `C < ∞`. -/
theorem eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le [SigmaFinite μ] [SigmaFinite ν]
    {p p' q q' : ℝ≥0∞} [hpp : p.HolderConjugate p'] [hqq : q.HolderConjugate q'] (hp : p ≠ ∞)
    {F : T → Lp E 2 μ} (hF : AEStronglyMeasurable F ν) {C : ℝ≥0∞}
    (hC : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν) :
    eLpNorm (fun t ↦ eLpNorm (F t) q μ) p ν ≤ C := by
  -- Structure: norm almost every `F t` by a countable sequence `gₘ`; for each `N` build the test
  -- function `G_N` from the running maximum `φ_N` of the first `N` pairings, truncated to a set
  -- `D_N` of finite measure; the testing step bounds `‖1_{D_N} φ_N‖_p` by `C`; Fatou's lemma
  -- passes to the limit, since `φ_N(t)` increases to `‖F t‖_q`.
  have hp0 : p ≠ 0 := hpp.ne_zero
  set r := p.toReal
  have hr1 : 1 ≤ r := by simpa using ENNReal.toReal_mono hp hpp.one_le
  have hr0 : r ≠ 0 := by positivity
  obtain ⟨S, hS, hFS⟩ := hF.isSeparable_ae_range
  obtain ⟨g, hg1, hgS⟩ :=
    hS.exists_seq_eLpNorm_eq_iSup_ofReal_re_inner (𝕜 := 𝕜) (q := q) (q' := q')
  set F' := hF.mk F
  have hF' : StronglyMeasurable F' := hF.stronglyMeasurable_mk
  have hFF' : F =ᵐ[ν] F' := hF.ae_eq_mk
  -- The pairings `aₘ(t) = re ⟪F t, gₘ⟫` with the norming sequence, and their running maxima.
  set a : ℕ → T → ℝ := fun m t ↦ RCLike.re ⟪F' t, g m⟫_𝕜
  have ha : ∀ m, Measurable (a m) := fun m ↦
    ((RCLike.continuous_re.comp (continuous_id.inner continuous_const)).comp_stronglyMeasurable
      hF').measurable
  set K : ℕ → ℝ := fun N ↦ ∑ m ∈ Finset.range N, ‖g m‖
  have hgK : ∀ {m N}, m < N → ‖g m‖ ≤ K N := fun hm ↦
    Finset.single_le_sum (fun m _ ↦ norm_nonneg (g m)) (Finset.mem_range.2 hm)
  have hrunMax_le : ∀ N t, (runMax a N t : ℝ) ≤ ‖F' t‖ * K N := fun N t ↦ by
    have hK : 0 ≤ ‖F' t‖ * K N :=
      mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun m _ ↦ norm_nonneg (g m))
    have := runMax_le (a := a) (N := N) (t := t) (b := ⟨_, hK⟩) fun m hm ↦ by
      rw [← Real.toNNReal_coe (r := ⟨_, hK⟩)]
      exact Real.toNNReal_le_toNNReal ((RCLike.re_le_norm _).trans
        ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hgK hm) (norm_nonneg _))))
    exact_mod_cast this
  -- The truncation sets: a set of finite measure on which `‖F t‖₂ ≤ N` and `φ_N(t) > 0`.
  set D : ℕ → Set T := fun N ↦
    spanningSets ν N ∩ {t | ‖F' t‖ ≤ N} ∩ {t | runMax a N t ≠ 0}
  have hDm : ∀ N, MeasurableSet (D N) := fun N ↦
    ((measurableSet_spanningSets ν N).inter (measurableSet_le hF'.norm.measurable
      measurable_const)).inter ((measurable_runMax ha N) (measurableSet_singleton 0)).compl
  set u : ℕ → T → ℝ := fun N ↦ (D N).indicator fun t ↦ (runMax a N t : ℝ)
  set G : ℕ → T → Lp E 2 μ := fun N ↦ (D N).indicator fun t ↦
    (((runMax a N t : ℝ) ^ (r - 1) : ℝ) : 𝕜) • g (runArgmax a N t)
  have hu_mem : ∀ N t, t ∈ D N → u N t = runMax a N t := fun N t ht ↦
    Set.indicator_of_mem ht _
  have hu_notMem : ∀ N t, t ∉ D N → u N t = 0 := fun N t ht ↦ Set.indicator_of_notMem ht _
  have hu_nonneg : ∀ N t, 0 ≤ u N t := fun N t ↦
    Set.indicator_nonneg (fun t _ ↦ NNReal.coe_nonneg _) t
  have hu_le : ∀ N t, u N t ≤ N * K N := fun N t ↦ by
    by_cases ht : t ∈ D N
    · rw [hu_mem N t ht]
      exact (hrunMax_le N t).trans (mul_le_mul_of_nonneg_right ht.1.2
        (Finset.sum_nonneg fun m _ ↦ norm_nonneg (g m)))
    · rw [hu_notMem N t ht]
      exact mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun m _ ↦ norm_nonneg (g m))
  have hum : ∀ N, Measurable (u N) := fun N ↦
    (NNReal.continuous_coe.measurable.comp (measurable_runMax ha N)).indicator (hDm N)
  -- The test function `G_N` and its three properties.
  have hG_eq : ∀ N t, t ∈ D N → G N t =
      (((runMax a N t : ℝ) ^ (r - 1) : ℝ) : 𝕜) • g (runArgmax a N t) := fun N t ht ↦
    Set.indicator_of_mem ht _
  have hG_zero : ∀ N t, t ∉ D N → G N t = 0 := fun N t ht ↦ Set.indicator_of_notMem ht _
  have hGm : ∀ N, StronglyMeasurable (G N) := fun N ↦ by
    have h₁ : StronglyMeasurable fun t ↦ (((runMax a N t : ℝ) ^ (r - 1) : ℝ) : 𝕜) :=
      RCLike.continuous_ofReal.comp_stronglyMeasurable ((NNReal.continuous_coe.measurable.comp
        (measurable_runMax ha N)).pow_const _).stronglyMeasurable
    have h₂ : StronglyMeasurable fun t ↦ g (runArgmax a N t) :=
      StronglyMeasurable.of_discrete.comp_measurable (measurable_runArgmax ha N)
    exact (h₁.smul h₂).indicator (hDm N)
  have hG_re : ∀ N t, RCLike.re ⟪F' t, G N t⟫_𝕜 = u N t ^ r := fun N t ↦ by
    by_cases ht : t ∈ D N
    · obtain ⟨-, hmax⟩ := runArgmax_spec ht.2
      have hpos : 0 < (runMax a N t : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht.2)
      have ha_eq : a (runArgmax a N t) t = runMax a N t := by
        have h0 : 0 < (a (runArgmax a N t) t).toNNReal := hmax ▸ pos_iff_ne_zero.2 ht.2
        rw [← hmax, Real.coe_toNNReal _ (Real.toNNReal_pos.1 h0).le]
      rw [hG_eq N t ht, inner_smul_right, RCLike.re_ofReal_mul, hu_mem N t ht]
      -- Fold the pairing back into the local abbreviation `a`, so that `ha_eq` applies.
      change (runMax a N t : ℝ) ^ (r - 1) * a (runArgmax a N t) t = _
      rw [ha_eq, Real.rpow_sub_one hpos.ne', div_mul_cancel₀ _ hpos.ne']
    · rw [hG_zero N t ht, inner_zero_right, map_zero, hu_notMem N t ht, Real.zero_rpow hr0]
  have hDsub : ∀ N, D N ⊆ spanningSets ν N := fun N t ht ↦ ht.1.1
  have hKnn : ∀ N, 0 ≤ K N := fun N ↦ Finset.sum_nonneg fun m _ ↦ norm_nonneg (g m)
  have hG_norm : ∀ N t, ‖G N t‖ ≤ (N * K N) ^ (r - 1) * K N := fun N t ↦ by
    by_cases ht : t ∈ D N
    · rw [hG_eq N t ht, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
      refine mul_le_mul ?_ (hgK (runArgmax_spec ht.2).1) (norm_nonneg _)
        (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) (hKnn N)) _)
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (hu_mem N t ht ▸ hu_le N t)
        (by linarith)
    · rw [hG_zero N t ht, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) (hKnn N)) _) (hKnn N)
  have hG_eLpNorm : ∀ N t, eLpNorm (G N t) q' μ ≤ ENNReal.ofReal (u N t ^ (r - 1)) :=
    fun N t ↦ by
    by_cases ht : t ∈ D N
    · rw [hG_eq N t ht, eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul, hu_mem N t ht,
        ← ofReal_norm, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
      exact mul_le_of_le_one_right' (hg1 _)
    · rw [hG_zero N t ht, eLpNorm_congr_ae (Lp.coeFn_zero E 2 μ)]
      simp
  have hint : ∀ N, Integrable (fun t ↦ ⟪F' t, G N t⟫_𝕜) ν := fun N ↦ by
    refine memLp_one_iff_integrable.1 ((memLp_top_of_bound
      (hF'.inner (hGm N)).aestronglyMeasurable (N * ((N * K N) ^ (r - 1) * K N))
      (ae_of_all _ fun t ↦ ?_)).mono_exponent_of_measure_support_ne_top
      (fun t ht ↦ by rw [hG_zero N t fun h ↦ ht (hDsub N h), inner_zero_right])
      (measure_spanningSets_lt_top ν N).ne le_top)
    by_cases ht : t ∈ D N
    · exact (norm_inner_le_norm _ _).trans (mul_le_mul ht.1.2 (hG_norm N t) (norm_nonneg _)
        (Nat.cast_nonneg N))
    · rw [hG_zero N t ht, inner_zero_right, norm_zero]
      exact mul_nonneg (Nat.cast_nonneg N)
        (mul_nonneg (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg N) (hKnn N)) _) (hKnn N))
  -- Testing against `G_N` bounds the `L^p` norm of `u_N = 1_{D_N} φ_N` by `C`.
  have hX : ∀ N, eLpNorm (u N) p ν ≤ C := fun N ↦ by
    have huLp : MemLp (u N) p ν := (memLp_top_of_bound (hum N).aestronglyMeasurable (N * K N)
      (ae_of_all _ fun t ↦ by rw [Real.norm_of_nonneg (hu_nonneg N t)]; exact hu_le N t)
      ).mono_exponent_of_measure_support_ne_top
      (fun t ht ↦ hu_notMem N t fun h ↦ ht (hDsub N h)) (measure_spanningSets_lt_top ν N).ne
      le_top
    have hFG : ∀ᵐ t ∂ν, ⟪F' t, G N t⟫_𝕜 = ⟪F t, G N t⟫_𝕜 :=
      hFF'.mono fun t ht ↦ by rw [ht]
    refine eLpNorm_le_of_re_inner_eq_rpow (p' := p') (q' := q') hp huLp (hum N) (hu_nonneg N)
      (hGm N).aestronglyMeasurable ((hint N).congr hFG) (hFG.mono fun t ht ↦ ht ▸ hG_re N t)
      (hG_eLpNorm N) ?_
    exact hC (G N) (spanningSets ν N) (measure_spanningSets_lt_top ν N).ne
      (fun t ht ↦ hG_zero N t fun h ↦ ht (hDsub N h))
      (memLp_top_of_bound (hGm N).aestronglyMeasurable _ (ae_of_all _ (hG_norm N)))
  -- Passage to the limit `N → ∞`: `u_N(t)` increases to `‖F t‖_q` for almost every `t`.
  have hΦ : ∀ᵐ t ∂ν, Tendsto (fun N ↦ ‖u N t‖ₑ) atTop (𝓝 (eLpNorm (F t) q μ)) := by
    filter_upwards [hFS, hFF'] with t htS ht
    rw [ht, hgS _ (ht ▸ htS)]
    -- Fold the pairings back into the local abbreviation `a`, so that `iSup_runMax` applies.
    change Tendsto _ _ (𝓝 (⨆ m, ENNReal.ofReal (a m t)))
    rw [← iSup_runMax]
    have hev : ∀ᶠ N in atTop, (runMax a N t : ℝ≥0∞) = ‖u N t‖ₑ := by
      obtain ⟨N₁, hN₁⟩ := exists_nat_ge ‖F' t‖
      filter_upwards [eventually_ge_atTop (max (spanningSetsIndex ν t) N₁)] with N hN
      by_cases h0 : runMax a N t = 0
      · have hu0 : u N t = 0 := by
          by_cases htD : t ∈ D N
          · rw [hu_mem N t htD, h0, NNReal.coe_zero]
          · exact hu_notMem N t htD
        rw [h0, hu0]
        simp
      · have htD : t ∈ D N := ⟨⟨mem_spanningSets_of_index_le ν t (le_of_max_le_left hN),
          hN₁.trans (by exact_mod_cast le_of_max_le_right hN)⟩, h0⟩
        rw [hu_mem N t htD, Real.enorm_eq_ofReal (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    exact (tendsto_atTop_iSup fun N M hNM ↦ ENNReal.coe_le_coe.2 (monotone_runMax a t hNM)).congr'
      hev
  exact eLpNorm_le_of_ae_tendsto_enorm hum
    (hF.aemeasurable_eLpNorm_Lp Measure.AbsolutelyContinuous.rfl q) hp0 hp hΦ hX

end MeasureTheory.AEStronglyMeasurable
