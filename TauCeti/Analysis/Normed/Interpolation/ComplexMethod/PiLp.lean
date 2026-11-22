/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.PiLp
import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Density
import TauCeti.Data.ENNReal.InterpolatedExponent

/-!
# Complex interpolation of finite `ℓ^q` sums: `ℓ^q([X₀, X₁]_θ) ⊆ [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`

Let `(X₀, X₁)` be a compatible couple of complex normed spaces, `ι` a finite index type,
`1 ≤ q₀, q₁ ≤ ∞`, `0 ≤ θ ≤ 1` and `1 / q = (1 - θ) / q₀ + θ / q₁`. Every finite family `u` of
elements of `[X₀, X₁]_θ` is an element of the complex interpolation space of the couple
`(ℓ^{q₀}(ι; X₀), ℓ^{q₁}(ι; X₁))` (`TauCeti.CompatibleCouple.piLp`), with

`‖u‖_{[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ} ≤ ‖(‖u k‖_θ)_k‖_{ℓ^q}`.

This is one of the two inclusions of the identity `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ = ℓ^q([X₀, X₁]_θ)`
with equal norms (Bergh–Löfström, Theorem 5.1.2, for finite sequences). Conversely, every element
of `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` has its coordinates in `[X₀, X₁]_θ`, each of norm at most its own
norm (`TauCeti.CompatibleCouple.ComplexMethodSpace.piLpProj`); the reverse norm inequality for the
whole family is not proved here.

## Main declarations

* `TauCeti.CompatibleCouple.ComplexMethodSpace.ofPiLp`: the inclusion
  `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`, a continuous linear map of norm at most one
  (`norm_ofPiLp_le`) lying over the identity of `ι → V`
  (`sumSpaceEmbed_toSum_ofPiLp`).
* `TauCeti.CompatibleCouple.ComplexMethodSpace.piLpProj`: the coordinate projections
  `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ → [X₀, X₁]_θ`, of norm at most one, which are left inverse to
  `ofPiLp` (`piLpProj_ofPiLp`).

## The argument

Normalize so that `N = ‖(c k)_k‖_{ℓ^q}` with `c k > ‖u k‖_θ`, and pick bounded-boundary strip
functions `F k` with `F k θ = u k` and boundary traces of norm less than `c k`. Put `b k = c k / N`
and `r_j = q / q_j` (with `q / ∞ = 0`; `r_j = 1` when `q = ∞`), so that `(1 - θ) r₀ + θ r₁ = 1`.
The family

`z ↦ (b k ^ ((z - θ) (r₁ - r₀)) F k z)_k`

is a bounded-boundary strip function for the couple of `ℓ^q` sums with value `u` at `θ`. On the
line `re z = j` its `k`-th coordinate has norm at most `b k ^ ((j - θ) (r₁ - r₀)) c k =
N b k ^ r_j`, and `‖(N b k ^ r_j)_k‖_{ℓ^{q_j}} = N (∑ₖ b k ^ q) ^ (1 / q_j) = N`. Letting
`c k ↓ ‖u k‖_θ` gives the bound.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.1 (Theorem 5.1.2).
-/

public noncomputable section

open Complex Complex.HadamardThreeLines Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  {C : CompatibleCouple ℂ X₀ X₁ V} {ι : Type*} [Fintype ι]
  {q₀ q₁ q : ℝ≥0∞} [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] {θ : ℝ}

/-! ### The scalar multipliers `b ^ ((z - θ) s)` -/

section Coefficient

/-- The multiplier `b ^ ((z - θ) s)` is bounded on the closed strip by `exp |s log b|`. -/
private theorem norm_cpow_le {b : ℝ} (hb : 0 < b) (hθ : θ ∈ Icc 0 1) (s : ℝ) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) :
    ‖(b : ℂ) ^ ((z - θ) * s)‖ ≤ Real.exp |s * Real.log b| := by
  rw [norm_cpow_eq_rpow_re_of_pos hb, Real.rpow_def_of_pos hb]
  refine Real.exp_le_exp.2 ?_
  have hre : |z.re - θ| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith [hz.2, hθ.1], by linarith [hz.1, hθ.2]⟩
  calc Real.log b * ((z - θ) * s).re = (z.re - θ) * (s * Real.log b) := by simp; ring
    _ ≤ |z.re - θ| * |s * Real.log b| := (le_abs_self _).trans (abs_mul _ _).le
    _ ≤ |s * Real.log b| := mul_le_of_le_one_left (abs_nonneg _) hre

/-- On a boundary line, the multiplier turns a bound `c` with `c = N b` into `N b ^ r` for the
exponent `r = a + 1`. -/
private theorem rpow_mul_le_mul_rpow {b N c : ℝ} (hb : 0 < b) (hc : c = N * b) {a r : ℝ}
    (har : a + 1 = r) {x : ℝ} (hx : x ≤ c) : b ^ a * x ≤ N * b ^ r := by
  calc b ^ a * x ≤ b ^ a * c := by gcongr
    _ = N * b ^ r := by rw [← har, Real.rpow_add_one hb.ne', hc]; ring

end Coefficient

/-! ### The norm of the boundary bounds -/

/-- For `N = ‖c‖_{ℓ^q}` with `q < ∞` and `c > 0`, the family `(N (c k / N) ^ (q / p))_k` has
`ℓ^p` norm at most `N`. -/
private theorem norm_toLp_mul_div_rpow_le [Fact (1 ≤ q)] [Nonempty ι] (hq : q ≠ ∞) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] {c : ι → ℝ} (hc : ∀ k, 0 < c k) :
    ‖WithLp.toLp p fun k => ‖WithLp.toLp q c‖ * (c k / ‖WithLp.toLp q c‖) ^ (q.toReal / p.toReal)‖
      ≤ ‖WithLp.toLp q c‖ := by
  set N := ‖WithLp.toLp q c‖
  have hN : 0 < N := (hc (Classical.arbitrary ι)).trans_le
    ((Real.le_norm_self _).trans (PiLp.norm_apply_le (WithLp.toLp q c) _))
  have hq₀ : 0 < q.toReal :=
    ENNReal.toReal_pos (one_pos.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hq
  rcases eq_or_ne p ∞ with rfl | hp
  · simp [abs_of_pos hN]
  have hp₀ : 0 < p.toReal :=
    ENNReal.toReal_pos (one_pos.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hp
  -- `∑ₖ (c k / N) ^ q = 1`
  have hsum : ∑ k, (c k / N) ^ q.toReal = 1 := by
    have h := PiLp.norm_rpow_eq_sum hq₀ (WithLp.toLp q c)
    simp only [Real.norm_eq_abs, abs_of_pos (hc _)] at h
    simp_rw [Real.div_rpow (hc _).le hN.le, ← Finset.sum_div, ← h]
    exact div_self (by positivity)
  refine (Real.rpow_le_rpow_iff (PiLp.norm_nonneg' _) hN.le hp₀).1 (le_of_eq ?_)
  rw [PiLp.norm_rpow_eq_sum hp₀]
  have hterm (k : ι) : ‖(WithLp.toLp p fun k => N * (c k / N) ^ (q.toReal / p.toReal)) k‖ ^
      p.toReal = N ^ p.toReal * (c k / N) ^ q.toReal := by
    have hb : 0 ≤ c k / N := (div_pos (hc k) hN).le
    rw [PiLp.toLp_apply, Real.norm_of_nonneg (by positivity), Real.mul_rpow hN.le (by positivity),
      ← Real.rpow_mul hb, div_mul_cancel₀ _ hp₀.ne']
  simp_rw [hterm, ← Finset.mul_sum, hsum, mul_one]

/-! ### The inclusion `ℓ^q([X₀, X₁]_θ) ⊆ [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` -/

section Inclusion

/-- Coordinatewise bounded-boundary strip functions `F k`, multiplied by entire scalars `m k`
bounded on the strip, assemble into a bounded-boundary strip function `z ↦ (m k z • F k z)_k` of
the couple `(ℓ^{q₀}(X₀), ℓ^{q₁}(X₁))`. -/
private theorem isBoundedStripFunction_sum_sumSingle_smul [DecidableEq ι]
    {F : ι → ℂ → C.SumSpace}
    {g : ι → BoundedContinuousFunction ℝ X₀ × BoundedContinuousFunction ℝ X₁}
    (hF : ∀ k, C.IsBoundedStripFunction (F k) (g k)) {m : ι → ℂ → ℂ}
    (hm : ∀ k, Differentiable ℂ (m k)) {K : ι → ℝ}
    (hK : ∀ k, ∀ z ∈ verticalClosedStrip 0 1, ‖m k z‖ ≤ K k)
    {G : BoundedContinuousFunction ℝ (PiLp q₀ fun _ : ι => X₀) ×
      BoundedContinuousFunction ℝ (PiLp q₁ fun _ : ι => X₁)}
    (hG₀ : ∀ t, G.1 t = WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t)
    (hG₁ : ∀ t, G.2 t = WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t) :
    (C.piLp ι q₀ q₁).IsBoundedStripFunction
      (∑ k, fun z => C.sumSingle q₀ q₁ k (m k z • F k z)) G := by
  choose M hM using fun k => (hF k).exists_norm_le
  refine ⟨Finset.sum_induction _ (fun f => DiffContOnCl ℂ f (verticalStrip 0 1))
      (fun _ _ => DiffContOnCl.add) diffContOnCl_const fun k _ =>
        (C.sumSingle q₀ q₁ k).differentiable.comp_diffContOnCl
          ((hm k).diffContOnCl.smul (hF k).diffContOnCl),
    isBounded_iff_forall_norm_le.2 ⟨∑ k : ι, ‖C.sumSingle q₀ q₁ k‖ * (K k * M k), ?_⟩,
    fun t => ?_, fun t => ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [Finset.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine ((C.sumSingle q₀ q₁ k).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [norm_smul]
    exact mul_le_mul (hK k z hz) (hM k z hz) (norm_nonneg _) ((norm_nonneg _).trans (hK k z hz))
  · conv_rhs => rw [← PiLp.univ_sum_single (G.1 t)]
    simp [hG₀, map_sum, (hF _).apply_mul_I]
  · conv_rhs => rw [← PiLp.univ_sum_single (G.2 t)]
    simp [hG₁, map_sum, (hF _).apply_one_add_mul_I]

/-- The core estimate: if `c k > ‖u k‖_θ` and the families `(N (c k / N) ^ r_j)_k` have
`ℓ^{q_j}` norm at most `N`, for exponents with `(1 - θ) r₀ + θ r₁ = 1`, then `u` is an element of
`[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at most `N`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt (hθ : θ ∈ Icc 0 1) {r₀ r₁ : ℝ}
    (hr : (1 - θ) * r₀ + θ * r₁ = 1) (u : ι → C.ComplexMethodSpace θ) {c : ι → ℝ}
    (hc : ∀ k, ‖u k‖ < c k) {N : ℝ} (hN : 0 < N)
    (h₀ : ‖WithLp.toLp q₀ fun k => N * (c k / N) ^ r₀‖ ≤ N)
    (h₁ : ‖WithLp.toLp q₁ fun k => N * (c k / N) ^ r₁‖ ≤ N) :
    ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧ ‖v‖ ≤ N := by
  classical
  choose F g hF hFθ hg using fun k =>
    (ComplexMethodSpace.norm_lt_iff_exists_isBoundedStripFunction hθ).1 (hc k)
  have hb (k : ι) : 0 < c k / N := div_pos ((norm_nonneg _).trans_lt (hc k)) hN
  have hcN (k : ι) : c k = N * (c k / N) := by field_simp
  -- the multiplier `(c k / N) ^ ((z - θ) (r₁ - r₀))` of the `k`-th coordinate
  set m : ι → ℂ → ℂ := fun k z => ((c k / N : ℝ) : ℂ) ^ ((z - θ) * ((r₁ - r₀ : ℝ) : ℂ))
  have hm (k : ι) : Differentiable ℂ (m k) :=
    ((differentiable_id.sub_const _).mul_const _).const_cpow (.inl (by exact_mod_cast (hb k).ne'))
  -- on the line `re z = j`, the `k`-th coordinate has norm at most `N (c k / N) ^ r_j`
  have hb₀ (k : ι) (t : ℝ) : ‖m k (t * I) • (g k).1 t‖ ≤ ‖N * (c k / N) ^ r₀‖ := by
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos (hb k),
      Real.norm_of_nonneg (by have := hb k; positivity)]
    refine rpow_mul_le_mul_rpow (hb k) (hcN k) (by simp; linear_combination -hr) ?_
    exact ((g k).1.norm_coe_le_norm t).trans ((norm_fst_le _).trans (hg k).le)
  have hb₁ (k : ι) (t : ℝ) : ‖m k (1 + t * I) • (g k).2 t‖ ≤ ‖N * (c k / N) ^ r₁‖ := by
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos (hb k),
      Real.norm_of_nonneg (by have := hb k; positivity)]
    refine rpow_mul_le_mul_rpow (hb k) (hcN k) (by simp; linear_combination -hr) ?_
    exact ((g k).2.norm_coe_le_norm t).trans ((norm_snd_le _).trans (hg k).le)
  -- the boundary traces of the family, of norm at most `N`
  have hG₀ (t : ℝ) : ‖WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t‖ ≤ N :=
    (PiLp.norm_mono fun k => hb₀ k t).trans h₀
  have hG₁ (t : ℝ) : ‖WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t‖ ≤ N :=
    (PiLp.norm_mono fun k => hb₁ k t).trans h₁
  let G₀ : BoundedContinuousFunction ℝ (PiLp q₀ fun _ : ι => X₀) :=
    .ofNormedAddCommGroup (fun t => WithLp.toLp q₀ fun k => m k (t * I) • (g k).1 t)
      ((PiLp.continuous_toLp _ _).comp <| continuous_pi fun k =>
        (((hm k).continuous).comp (by fun_prop)).smul (g k).1.continuous)
      N hG₀
  let G₁ : BoundedContinuousFunction ℝ (PiLp q₁ fun _ : ι => X₁) :=
    .ofNormedAddCommGroup (fun t => WithLp.toLp q₁ fun k => m k (1 + t * I) • (g k).2 t)
      ((PiLp.continuous_toLp _ _).comp <| continuous_pi fun k =>
        (((hm k).continuous).comp (by fun_prop)).smul (g k).2.continuous)
      N hG₁
  have hΦ := isBoundedStripFunction_sum_sumSingle_smul (G := (G₀, G₁)) hF hm
    (fun k _ hz => norm_cpow_le (hb k) hθ (r₁ - r₀) hz)
    (fun _ => rfl) (fun _ => rfl)
  obtain ⟨v, hv⟩ :=
    (ComplexMethodSpace.exists_toSum_eq_iff_isBoundedStripFunction hθ).2 ⟨_, _, hΦ, rfl⟩
  refine ⟨v, ?_, (ComplexMethodSpace.norm_le_of_isBoundedStripFunction hθ hΦ hv).trans ?_⟩
  · rw [hv]
    simp [m, ← hFθ, map_sum, Finset.univ_sum_single]
  · exact norm_prod_le_iff.2 ⟨BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hN.le hG₀,
      BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hN.le hG₁⟩

variable [Fact (1 ≤ q)]

/-- For every family `c` strictly dominating the coordinate norms of `u ∈ ℓ^q([X₀, X₁]_θ)`, `u` is
an element of `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at most `‖c‖_{ℓ^q}`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp [Nonempty ι]
    (hθ : θ ∈ Icc 0 1) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ)
    {c : ι → ℝ} (hc : ∀ k, ‖u k‖ < c k) : ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧
        ‖v‖ ≤ ‖WithLp.toLp q c‖ := by
  have hc₀ (k : ι) : 0 < c k := (norm_nonneg _).trans_lt (hc k)
  have hN : 0 < ‖WithLp.toLp q c‖ := (hc₀ (Classical.arbitrary ι)).trans_le
    ((Real.le_norm_self _).trans (PiLp.norm_apply_le (WithLp.toLp q c) _))
  by_cases hqt : q = ∞
  · -- all exponents are infinite: take `r₀ = r₁ = 1`
    obtain ⟨rfl, rfl⟩ := hq_top hqt
    subst hqt
    have hcN : (fun k => ‖WithLp.toLp ∞ c‖ * (c k / ‖WithLp.toLp ∞ c‖) ^ (1 : ℝ)) = c := by
      ext k
      rw [Real.rpow_one]
      field_simp
    exact exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt hθ (r₀ := 1) (r₁ := 1) (by ring) u hc
      hN (by rw [hcN]) (by rw [hcN])
  -- `q < ∞`: take `r_j = q / q_j`
  have hq₀ : q.toReal ≠ 0 :=
    (ENNReal.toReal_pos (one_pos.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne' hqt).ne'
  have hθq := inv_toReal_eq_of_inv_eq (one_pos.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q₀)).ne'
    (one_pos.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ q₁)).ne' hθ hq
  refine exists_sumSpaceEmbed_toSum_eq_and_norm_le_of_lt hθ ?_ u hc hN
    (norm_toLp_mul_div_rpow_le hqt q₀ hc₀) (norm_toLp_mul_div_rpow_le hqt q₁ hc₀)
  calc (1 - θ) * (q.toReal / q₀.toReal) + θ * (q.toReal / q₁.toReal)
      = q.toReal * ((1 - θ) * q₀.toReal⁻¹ + θ * q₁.toReal⁻¹) := by ring
    _ = 1 := by rw [← hθq, mul_inv_cancel₀ hq₀]

/-- Every family `u ∈ ℓ^q([X₀, X₁]_θ)` is an element of `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` of norm at
most `‖u‖`. -/
private theorem exists_sumSpaceEmbed_toSum_eq_and_norm_le (hθ : θ ∈ Icc 0 1)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    ∃ v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ,
      (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum v) =
        (fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k))) ∧ ‖v‖ ≤ ‖u‖ := by
  cases isEmpty_or_nonempty ι
  · exact ⟨0, funext isEmptyElim, by simp⟩
  obtain ⟨v, hv, -⟩ := exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp hθ hq hq_top u
    (c := fun k => ‖u k‖ + 1) fun k => by linarith
  refine ⟨v, hv, le_of_forall_pos_lt_add fun δ hδ => ?_⟩
  -- `v` is determined by `u`, so it obeys the bound for `c k = ‖u k‖ + ε` with `ε > 0` small
  set K := ‖WithLp.toLp q fun _ : ι => (1 : ℝ)‖
  have hε : 0 < δ / (K + 1) := div_pos hδ (by positivity)
  obtain ⟨v', hv', hnorm⟩ := exists_sumSpaceEmbed_toSum_eq_and_norm_le_norm_toLp hθ hq hq_top u
    (c := fun k => ‖u k‖ + δ / (K + 1)) fun k => by linarith
  obtain rfl : v' = v := ComplexMethodSpace.ext (sumSpace_ext _ (hv'.trans hv.symm))
  have hsplit : (WithLp.toLp q fun k => ‖u k‖ + δ / (K + 1)) =
      WithLp.toLp q (fun k => ‖u k‖) + (δ / (K + 1)) • WithLp.toLp q fun _ : ι => (1 : ℝ) :=
    WithLp.ofLp_injective q <| funext fun k => by simp
  calc ‖v'‖ ≤ ‖WithLp.toLp q fun k => ‖u k‖ + δ / (K + 1)‖ := hnorm
    _ ≤ ‖u‖ + δ / (K + 1) * K := by
        rw [hsplit]
        refine (norm_add_le _ _).trans_eq ?_
        rw [PiLp.norm_norm, norm_smul, Real.norm_of_nonneg hε.le]
    _ < ‖u‖ + δ := by
        have : δ * K / (K + 1) < δ := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        rw [div_mul_eq_mul_div]
        linarith

variable (hθ : θ ∈ Icc 0 1) (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
  (hq_top : q = ∞ → q₀ = ∞ ∧ q₁ = ∞)

private theorem sumSpaceEmbed_toSum_choose (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    (C.piLp ι q₀ q₁).sumSpaceEmbed (ComplexMethodSpace.toSum
        (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose) =
      fun k => C.sumSpaceEmbed (ComplexMethodSpace.toSum (u k)) :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.1

namespace ComplexMethodSpace

/-- **Complex interpolation of finite `ℓ^q` sums, `ℓ^q([X₀, X₁]_θ) ⊆ [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`.**
For `0 ≤ θ ≤ 1` and `1 / q = (1 - θ) / q₀ + θ / q₁` (with `q < ∞` unless `q₀ = q₁ = ∞`), the
inclusion of the finite families of elements of `[X₀, X₁]_θ`, normed in `ℓ^q`, into the complex
interpolation space of the couple `(ℓ^{q₀}(ι; X₀), ℓ^{q₁}(ι; X₁))`. It lies over the identity of
`ι → V` (`sumSpaceEmbed_toSum_ofPiLp`) and has norm at most one (`norm_ofPiLp_le`). -/
def ofPiLp : (PiLp q fun _ : ι => C.ComplexMethodSpace θ) →L[ℂ]
    (C.piLp ι q₀ q₁).ComplexMethodSpace θ :=
  LinearMap.mkContinuous
    { toFun u := (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose
      map_add' u w := ext <| sumSpace_ext _ <| by
        simp only [map_add, sumSpaceEmbed_toSum_choose hθ hq hq_top]
        ext k
        simp
      map_smul' a u := ext <| sumSpace_ext _ <| by
        simp only [map_smul, sumSpaceEmbed_toSum_choose hθ hq hq_top]
        ext k
        simp }
    1 fun u => by
      simpa using (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.2

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` lies over the identity of
`ι → V`: the element it produces has coordinates `u k`. -/
@[simp]
theorem sumSpaceEmbed_toSum_ofPiLp (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    (C.piLp ι q₀ q₁).sumSpaceEmbed (toSum (ofPiLp hθ hq hq_top u)) =
      fun k => C.sumSpaceEmbed (toSum (u k)) :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.1

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` does not increase norms:
`‖u‖_{[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ} ≤ ‖(‖u k‖_θ)_k‖_{ℓ^q}`. -/
theorem norm_ofPiLp_le (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    ‖ofPiLp hθ hq hq_top u‖ ≤ ‖u‖ :=
  (exists_sumSpaceEmbed_toSum_eq_and_norm_le hθ hq hq_top u).choose_spec.2

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` has operator norm at most one. -/
theorem opNorm_ofPiLp_le :
    ‖(ofPiLp hθ hq hq_top : (PiLp q fun _ : ι => C.ComplexMethodSpace θ) →L[ℂ]
      (C.piLp ι q₀ q₁).ComplexMethodSpace θ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa using norm_ofPiLp_le hθ hq hq_top u

variable (q₀ q₁) in
/-- The projection `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ → [X₀, X₁]_θ` onto the `k`-th coordinate, induced
by the coordinate projections of `ℓ^{q₀}(X₀)` and `ℓ^{q₁}(X₁)`. It lies over the coordinate
projection of the sum spaces (`toSum_piLpProj`) and does not increase norms
(`norm_piLpProj_le`). -/
def piLpProj (k : ι) : (C.piLp ι q₀ q₁).ComplexMethodSpace θ →L[ℂ] C.ComplexMethodSpace θ :=
  map θ (PiLp.proj q₀ (fun _ : ι => X₀) k) (PiLp.proj q₁ (fun _ : ι => X₁) k) fun x =>
    sumSpace_ext _ <| by simpa using congrFun ((C.piLp ι q₀ q₁).embed₀_interFst x) k

/-- The coordinate projection of the complex interpolation spaces lies over the coordinate
projection of the sum spaces. -/
@[simp]
theorem toSum_piLpProj (k : ι) (v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :
    toSum (piLpProj q₀ q₁ k v) = C.sumProj q₀ q₁ k (toSum v) := by
  rw [piLpProj, toSum_map]
  exact DFunLike.congr_fun ((C.piLp ι q₀ q₁).sumLift_unique _ _ _
    (by ext; simp) (by ext; simp)).symm (toSum v)

/-- The coordinate projection `[ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ → [X₀, X₁]_θ` does not increase norms. -/
theorem norm_piLpProj_le (k : ι) (v : (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :
    ‖piLpProj q₀ q₁ k v‖ ≤ ‖v‖ :=
  norm_map_le_of_norm_le _ _ _ (fun x => PiLp.norm_apply_le x k) (fun x => PiLp.norm_apply_le x k) v

/-- The coordinate projections are left inverse to the inclusion
`ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ`. -/
@[simp]
theorem piLpProj_ofPiLp (k : ι) (u : PiLp q fun _ : ι => C.ComplexMethodSpace θ) :
    piLpProj q₀ q₁ k (ofPiLp hθ hq hq_top u) = u k :=
  ext <| sumSpace_ext _ <| by simp

/-- The inclusion `ℓ^q([X₀, X₁]_θ) → [ℓ^{q₀}(X₀), ℓ^{q₁}(X₁)]_θ` is injective. -/
theorem ofPiLp_injective :
    Function.Injective (ofPiLp hθ hq hq_top :
      (PiLp q fun _ : ι => C.ComplexMethodSpace θ) → (C.piLp ι q₀ q₁).ComplexMethodSpace θ) :=
  fun u w h => WithLp.ofLp_injective q <| funext fun k => by
    simpa using congrArg (piLpProj q₀ q₁ k) h

end ComplexMethodSpace

end Inclusion

end TauCeti.CompatibleCouple
