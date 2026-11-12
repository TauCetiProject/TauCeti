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
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
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
for each `t` the last index `m < N` attaining the maximum, and test against
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
    · exact hn ▸ Lp.eLpNorm_coeFn_zero.trans_le zero_le_one
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

/-- The running maximum `max_{m < N} (re ⟪F t, gₘ⟫)⁺` of the pairings with a sequence `gₘ` is
measurable in `t`. -/
private theorem measurable_finsetSup_re_inner {F : T → Lp E 2 μ} (hF : StronglyMeasurable F)
    (g : ℕ → Lp E 2 μ) (N : ℕ) :
    Measurable fun t ↦ (Finset.range N).sup fun m ↦ (RCLike.re ⟪F t, g m⟫_𝕜).toNNReal := by
  convert Finset.sup_induction (p := Measurable) (s := Finset.range N)
    (f := fun m t ↦ (RCLike.re ⟪F t, g m⟫_𝕜).toNNReal) measurable_const
    (fun _ h₁ _ h₂ ↦ h₁.sup h₂) fun m _ ↦ ((RCLike.continuous_re.comp
      (continuous_id.inner continuous_const)).comp_stronglyMeasurable hF).measurable.real_toNNReal
    using 1
  ext t
  simp

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


/-- **The truncated testing step.** Let `gₘ` be test functions in the unit ball of `L^{q'}`, let
`φ_N(t) = max_{m < N} (re ⟪F t, gₘ⟫)⁺`, and let `s` be a measurable set of finite measure on which
`‖F t‖₂ ≤ R`. Testing against `G t = φ_N(t) ^ (p - 1) gₘ`, where `m < N` is the last index
attaining the maximum, bounds `‖1_s φ_N‖_p` by `C`. -/
private theorem eLpNorm_indicator_finsetSup_le {p p' q' : ℝ≥0∞} [hpp : p.HolderConjugate p']
    (hp : p ≠ ∞) {F : T → Lp E 2 μ} (hF : StronglyMeasurable F) {g : ℕ → Lp E 2 μ}
    (hg1 : ∀ m, eLpNorm (g m) q' μ ≤ 1) {C : ℝ≥0∞}
    (hC : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν)
    (N : ℕ) {s : Set T} (hs : MeasurableSet s) (hsν : ν s ≠ ∞) {R : ℝ≥0}
    (hR : ∀ t ∈ s, ‖F t‖ ≤ R) :
    eLpNorm (s.indicator fun t ↦
      (((Finset.range N).sup fun m ↦ (RCLike.re ⟪F t, g m⟫_𝕜).toNNReal : ℝ≥0) : ℝ)) p ν ≤ C := by
  set r := p.toReal
  have hr1 : 1 ≤ r := by simpa using ENNReal.toReal_mono hp hpp.one_le
  have hr0 : r ≠ 0 := by positivity
  set a : ℕ → T → ℝ := fun m t ↦ RCLike.re ⟪F t, g m⟫_𝕜
  set φ : T → ℝ≥0 := fun t ↦ (Finset.range N).sup fun m ↦ (a m t).toNNReal
  have hφm : Measurable φ := measurable_finsetSup_re_inner hF g N
  -- The last index `ψ(t) < N` attaining the maximum `φ(t)`, when it is positive.
  set ψ : T → ℕ := fun t ↦ Nat.findGreatest (fun m ↦ m < N ∧ (a m t).toNNReal = φ t) N
  have hψm : Measurable ψ := measurable_findGreatest fun m _ ↦ (MeasurableSet.const _).inter
    (measurableSet_eq_fun ((RCLike.continuous_re.comp (continuous_id.inner
      continuous_const)).comp_stronglyMeasurable hF).measurable.real_toNNReal hφm)
  have hψ : ∀ t, φ t ≠ 0 → ψ t < N ∧ (a (ψ t) t).toNNReal = φ t := fun t ht ↦ by
    have hN : (Finset.range N).Nonempty :=
      Finset.nonempty_range_iff.2 fun hN ↦ ht (by simp [φ, hN])
    obtain ⟨m, hm, hmφ⟩ := Finset.exists_mem_eq_sup _ hN fun m ↦ (a m t).toNNReal
    exact Nat.findGreatest_spec (P := fun m ↦ m < N ∧ (a m t).toNNReal = φ t)
      (Finset.mem_range.1 hm).le ⟨Finset.mem_range.1 hm, hmφ.symm⟩
  set K : ℝ := ∑ m ∈ Finset.range N, ‖g m‖
  have hKnn : 0 ≤ K := Finset.sum_nonneg fun m _ ↦ norm_nonneg (g m)
  have hgK : ∀ {m}, m < N → ‖g m‖ ≤ K := fun hm ↦
    Finset.single_le_sum (fun m _ ↦ norm_nonneg (g m)) (Finset.mem_range.2 hm)
  have hφ_le : ∀ t ∈ s, (φ t : ℝ) ≤ R * K := fun t ht ↦ by
    have hK : 0 ≤ ‖F t‖ * K := mul_nonneg (norm_nonneg _) hKnn
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (hR t ht) hKnn)
    rw [← Real.coe_toNNReal _ hK]
    refine NNReal.coe_le_coe.2 (Finset.sup_le fun m hm ↦ Real.toNNReal_le_toNNReal ?_)
    exact (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hgK (Finset.mem_range.1 hm)) (norm_nonneg _)))
  -- Test on the part `D` of `s` where `φ` is positive, so that `ψ` attains the maximum there.
  set D : Set T := s ∩ {t | φ t ≠ 0}
  have hDm : MeasurableSet D := hs.inter (hφm (measurableSet_singleton 0)).compl
  set u : T → ℝ := D.indicator fun t ↦ (φ t : ℝ)
  have hsu : s.indicator (fun t ↦ (φ t : ℝ)) = u := by
    ext t
    by_cases hs : t ∈ s <;> by_cases h0 : φ t = 0 <;> simp [u, D, Set.indicator, hs, h0]
  rw [hsu]
  set G : T → Lp E 2 μ := D.indicator fun t ↦ (((φ t : ℝ) ^ (r - 1) : ℝ) : 𝕜) • g (ψ t)
  have hu_mem : ∀ t ∈ D, u t = φ t := fun t ht ↦ Set.indicator_of_mem ht _
  have hu_notMem : ∀ t, t ∉ D → u t = 0 := fun t ht ↦ Set.indicator_of_notMem ht _
  have hu_nonneg : ∀ t, 0 ≤ u t := Set.indicator_nonneg fun t _ ↦ NNReal.coe_nonneg _
  have hu_le : ∀ t, u t ≤ R * K := fun t ↦ by
    by_cases ht : t ∈ D
    · rw [hu_mem t ht]
      exact hφ_le t ht.1
    · rw [hu_notMem t ht]
      exact mul_nonneg R.coe_nonneg hKnn
  have hum : Measurable u := (NNReal.continuous_coe.measurable.comp hφm).indicator hDm
  -- The test function `G` and its three properties.
  have hG_eq : ∀ t ∈ D, G t = (((φ t : ℝ) ^ (r - 1) : ℝ) : 𝕜) • g (ψ t) := fun t ht ↦
    Set.indicator_of_mem ht _
  have hG_zero : ∀ t, t ∉ D → G t = 0 := fun t ht ↦ Set.indicator_of_notMem ht _
  have hGm : StronglyMeasurable G := by
    have h₁ : StronglyMeasurable fun t ↦ (((φ t : ℝ) ^ (r - 1) : ℝ) : 𝕜) :=
      RCLike.continuous_ofReal.comp_stronglyMeasurable
        ((NNReal.continuous_coe.measurable.comp hφm).pow_const _).stronglyMeasurable
    have h₂ : StronglyMeasurable fun t ↦ g (ψ t) :=
      StronglyMeasurable.of_discrete.comp_measurable hψm
    exact (h₁.smul h₂).indicator hDm
  have hG_re : ∀ t, RCLike.re ⟪F t, G t⟫_𝕜 = u t ^ r := fun t ↦ by
    by_cases ht : t ∈ D
    · obtain ⟨-, hmax⟩ := hψ t ht.2
      have hpos : 0 < (φ t : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht.2)
      have ha_eq : a (ψ t) t = φ t := by
        have h0 : 0 < (a (ψ t) t).toNNReal := hmax ▸ pos_iff_ne_zero.2 ht.2
        rw [← hmax, Real.coe_toNNReal _ (Real.toNNReal_pos.1 h0).le]
      rw [hG_eq t ht, inner_smul_right, RCLike.re_ofReal_mul, hu_mem t ht]
      -- Fold the pairing back into the local abbreviation `a`, so that `ha_eq` applies.
      change (φ t : ℝ) ^ (r - 1) * a (ψ t) t = _
      rw [ha_eq, Real.rpow_sub_one hpos.ne', div_mul_cancel₀ _ hpos.ne']
    · rw [hG_zero t ht, inner_zero_right, map_zero, hu_notMem t ht, Real.zero_rpow hr0]
  have hG_norm : ∀ t, ‖G t‖ ≤ (R * K) ^ (r - 1) * K := fun t ↦ by
    have hRK : 0 ≤ (R : ℝ) * K := mul_nonneg R.coe_nonneg hKnn
    by_cases ht : t ∈ D
    · rw [hG_eq t ht, norm_smul, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
      refine mul_le_mul ?_ (hgK (hψ t ht.2).1) (norm_nonneg _) (Real.rpow_nonneg hRK _)
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (hu_mem t ht ▸ hu_le t) (by linarith)
    · rw [hG_zero t ht, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg hRK _) hKnn
  have hG_eLpNorm : ∀ t, eLpNorm (G t) q' μ ≤ ENNReal.ofReal (u t ^ (r - 1)) := fun t ↦ by
    by_cases ht : t ∈ D
    · rw [hG_eq t ht, eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul, hu_mem t ht,
        ← ofReal_norm, RCLike.norm_ofReal,
        abs_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
      exact mul_le_of_le_one_right' (hg1 _)
    · rw [hG_zero t ht, Lp.eLpNorm_coeFn_zero]
      exact zero_le
  have hGs : ∀ t, t ∉ s → G t = 0 := fun t ht ↦ hG_zero t fun h ↦ ht h.1
  have hint : Integrable (fun t ↦ ⟪F t, G t⟫_𝕜) ν := by
    refine memLp_one_iff_integrable.1 ((memLp_top_of_bound (hF.inner hGm).aestronglyMeasurable
      (R * ((R * K) ^ (r - 1) * K)) (ae_of_all _ fun t ↦ ?_))
      |>.mono_exponent_of_measure_support_ne_top
        (fun t ht ↦ by rw [hGs t ht, inner_zero_right]) hsν le_top)
    by_cases ht : t ∈ s
    · exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hR t ht) (hG_norm t) (norm_nonneg _) R.coe_nonneg)
    · rw [hGs t ht, inner_zero_right, norm_zero]
      exact mul_nonneg R.coe_nonneg ((norm_nonneg _).trans (hG_norm t))
  -- Testing against `G` bounds the `L^p` norm of `u = 1_D φ` by `C`.
  have huLp : MemLp u p ν := (memLp_top_of_bound hum.aestronglyMeasurable (R * K)
    (ae_of_all _ fun t ↦ by rw [Real.norm_of_nonneg (hu_nonneg t)]; exact hu_le t)
    ).mono_exponent_of_measure_support_ne_top (fun t ht ↦ hu_notMem t fun h ↦ ht h.1) hsν le_top
  exact eLpNorm_le_of_re_inner_eq_rpow (p' := p') (q' := q') hp huLp hum hu_nonneg
    hGm.aestronglyMeasurable hint (ae_of_all _ hG_re) hG_eLpNorm
    (hC G s hsν hGs (memLp_top_of_bound hGm.aestronglyMeasurable _ (ae_of_all _ hG_norm)))

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
  -- Structure: norm almost every `F t` by a countable sequence `gₘ`; for each `N` the truncated
  -- testing step bounds `‖1_{s_N} φ_N‖_p` by `C`, where `φ_N` is the running maximum of the first
  -- `N` pairings; Fatou's lemma passes to the limit, since `φ_N(t)` increases to `‖F t‖_q`.
  obtain ⟨S, hS, hFS⟩ := hF.isSeparable_ae_range
  obtain ⟨g, hg1, hgS⟩ :=
    hS.exists_seq_eLpNorm_eq_iSup_ofReal_re_inner (𝕜 := 𝕜) (q := q) (q' := q')
  set F' := hF.mk F
  have hF' : StronglyMeasurable F' := hF.stronglyMeasurable_mk
  have hFF' : F =ᵐ[ν] F' := hF.ae_eq_mk
  have hC' : ∀ (G : T → Lp E 2 μ) (s : Set T), ν s ≠ ∞ → (∀ t, t ∉ s → G t = 0) →
      MemLp G ∞ ν → ‖∫ t, ⟪F' t, G t⟫_𝕜 ∂ν‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (G t) q' μ) p' ν :=
    fun G s hs hGs hG ↦ by
      have hFG : (fun t ↦ ⟪F t, G t⟫_𝕜) =ᵐ[ν] fun t ↦ ⟪F' t, G t⟫_𝕜 :=
        hFF'.mono fun t ht ↦ by simp only [ht]
      rw [← integral_congr_ae hFG]
      exact hC G s hs hGs hG
  -- The running maxima `φ_N`, truncated to sets `s_N` of finite measure where `‖F t‖₂ ≤ N`.
  set φ : ℕ → T → ℝ≥0 := fun N t ↦
    (Finset.range N).sup fun m ↦ (RCLike.re ⟪F' t, g m⟫_𝕜).toNNReal
  set s : ℕ → Set T := fun N ↦ spanningSets ν N ∩ {t | ‖F' t‖ ≤ N}
  have hsm : ∀ N, MeasurableSet (s N) := fun N ↦
    (measurableSet_spanningSets ν N).inter (measurableSet_le hF'.norm.measurable measurable_const)
  set u : ℕ → T → ℝ := fun N ↦ (s N).indicator fun t ↦ (φ N t : ℝ)
  have hum : ∀ N, Measurable (u N) := fun N ↦
    (NNReal.continuous_coe.measurable.comp (measurable_finsetSup_re_inner hF' g N)).indicator
      (hsm N)
  have hX : ∀ N, eLpNorm (u N) p ν ≤ C := fun N ↦
    eLpNorm_indicator_finsetSup_le hp hF' hg1 hC' N (hsm N)
      (measure_mono_top Set.inter_subset_left |>.mt (measure_spanningSets_lt_top ν N).ne)
      (R := N) fun t ht ↦ by exact_mod_cast ht.2
  -- Passage to the limit `N → ∞`: `u_N(t)` increases to `‖F t‖_q` for almost every `t`.
  have hΦ : ∀ᵐ t ∂ν, Tendsto (fun N ↦ ‖u N t‖ₑ) atTop (𝓝 (eLpNorm (F t) q μ)) := by
    filter_upwards [hFS, hFF'] with t htS ht
    rw [ht, hgS _ (ht ▸ htS)]
    have hiSup : ⨆ N, (φ N t : ℝ≥0∞) = ⨆ m, ENNReal.ofReal (RCLike.re ⟪F' t, g m⟫_𝕜) := by
      refine le_antisymm (iSup_le fun N ↦ ?_) (iSup_le fun m ↦ le_iSup_of_le (m + 1) ?_)
      · rw [ENNReal.coe_finset_sup]
        exact Finset.sup_le fun m _ ↦ le_iSup (fun m ↦ ENNReal.ofReal (RCLike.re ⟪F' t, g m⟫_𝕜)) m
      · exact ENNReal.coe_le_coe.2 (Finset.le_sup (f := fun m ↦ (RCLike.re ⟪F' t, g m⟫_𝕜).toNNReal)
          (Finset.self_mem_range_succ m))
    have hev : ∀ᶠ N in atTop, (φ N t : ℝ≥0∞) = ‖u N t‖ₑ := by
      obtain ⟨N₁, hN₁⟩ := exists_nat_ge ‖F' t‖
      filter_upwards [eventually_ge_atTop (max (spanningSetsIndex ν t) N₁)] with N hN
      have htN : t ∈ s N := ⟨mem_spanningSets_of_index_le ν t (le_of_max_le_left hN),
        hN₁.trans (by exact_mod_cast le_of_max_le_right hN)⟩
      rw [show u N t = φ N t from Set.indicator_of_mem htN _,
        Real.enorm_eq_ofReal (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    rw [← hiSup]
    exact (tendsto_atTop_iSup fun N M hNM ↦ ENNReal.coe_le_coe.2
      (Finset.sup_mono (Finset.range_mono hNM))).congr' hev
  exact TauCeti.eLpNorm_ennreal_le_of_ae_tendsto (fun N ↦ (hum N).enorm.aemeasurable) hΦ
    (Frequently.of_forall fun N ↦ (eLpNorm_enorm _ (hum N).aestronglyMeasurable).trans_le (hX N))

end MeasureTheory.AEStronglyMeasurable
