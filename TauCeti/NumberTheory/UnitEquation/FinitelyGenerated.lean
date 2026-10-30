/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.House
public import TauCeti.NumberTheory.NumberField.Global.Places.Height
import TauCeti.Analysis.AbsoluteValue.FiniteOrder

/-!
# An explicit exponent bound for unit equations in finitely generated groups

Let `K` be a number field, `S` a finite set of finite places of `K`, and `γ j` nonzero elements
of `K` with absolute value `1` at every finite place outside `S`. Let `a, b ≠ 0`. We bound the
exponents of the solutions `x = ζₓ ∏ j, γ j ^ z j`, `y = ζ_y ∏ j, γ j ^ w j` (`ζₓ, ζ_y` roots of
unity) of the unit equation `a x + b y = 1`, assuming:

* an exponent–height bound `|z j| ≤ κ * logHeight₁ (ζ * ∏ i, γ i ^ z i)` for every root of unity
  `ζ`, as supplied for multiplicatively independent `γ j` by
  `TauCeti.NumberField.SUnit.exists_abs_le_mul_logHeight₁`;
* lower bounds for linear forms in logarithms in their multiplicative form, at every complex
  embedding `σ` and at every place `v ∈ S`: for some `C ≥ 0`, every `c ∈ {a, b}`, every root of
  unity `ζ` and every `z` with `c ζ ∏ j, γ j ^ z j ≠ 1`,
  `|σ (c ζ ∏ j, γ j ^ z j) - 1| ≥ (exp 1 * max(1, maxⱼ |z j|)) ^ (-C)`, and likewise for
  `|c ζ ∏ j, γ j ^ z j - 1|_v`. Baker's theorem and Yu's theorem supply such a `C`.

With `s = #S + #{infinite places}`, `M` an upper bound for `house a`, `house b` and the
`|a|_v, |b|_v` for `v ∈ S`, `A = 2 κ s (log M + C)` and `B₀ = 2 κ s C`, every solution satisfies
`max(|z j|, |w j|) ≤ max(1, 2 A + 2 B₀ (log (2 B₀) - 1))`.

The proof follows Győry. By the product formula some place `v` among the places of `S` and the
infinite places has `log ‖x‖_v ≤ -logHeight₁ x / s`, so `b y - 1 = -a x` is small at `v`, and the
lower bound gives `logHeight₁ x ≤ 2 s (log M + C (1 + log N))`, where
`N = max(1, maxⱼ max(|z j|, |w j|))`. The exponent–height bound turns this into
`N ≤ A + B₀ log N`, which is solved for `N`.

## Main results

* `TauCeti.NumberField.SUnit.max_abs_le_of_mul_add_mul_eq_one`: the exponent bound above.

## References

* K. Győry, *On the number of solutions of linear equations in units of an algebraic number
  field*, Comment. Math. Helv. **54** (1979), 583–600.
* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §§2–3.
* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Theorem 5.18 and its proof, pp. 102–103.
-/

public section

open Finset Height IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.NumberField.SUnit

variable {K : Type*} [Field K] [NumberField K]

/-- Let `q + δ x = 1`, where `x ≠ 0` has absolute value `1` at every finite place outside `S`
and `δ ≠ 0` has house and absolute values at the places of `S` at most `M`. If
`|σ q - 1|` and `|q - 1|_v` are at least `(exp 1 * N) ^ (-C)` for every complex embedding `σ`
and every `v ∈ S` whenever `q ≠ 1`, then
`logHeight₁ x ≤ 2 s (log M + C (1 + log N))`, where `s = #S + #{infinite places}`. -/
private theorem logHeight₁_le_of_add_mul_eq_one {S : Finset (HeightOneSpectrum (𝓞 K))}
    {x δ q : K} (hx0 : x ≠ 0) (hx : ∀ v ∉ S, HeightOneSpectrum.adicAbv K v x = 1)
    (hδ : δ ≠ 0) {M : ℝ} (hδM : house δ ≤ M)
    (hδS : ∀ v ∈ S, HeightOneSpectrum.adicAbv K v δ ≤ M) (h : q + δ * x = 1) {C N : ℝ}
    (hN : 0 < N) (hinf : ∀ σ : K →+* ℂ, q ≠ 1 → (Real.exp 1 * N) ^ (-C) ≤ ‖σ q - 1‖)
    (hfin : ∀ v ∈ S, q ≠ 1 →
      (Real.exp 1 * N) ^ (-C) ≤ HeightOneSpectrum.adicAbv K v (q - 1)) :
    logHeight₁ x ≤
      2 * (#S + Fintype.card (InfinitePlace K)) * (Real.log M + C * (1 + Real.log N)) := by
  have hq1 : q - 1 = -(δ * x) := by linear_combination h
  have hq : q ≠ 1 := by
    rintro rfl
    exact mul_ne_zero hδ hx0 (by linear_combination h)
  set s : ℝ := #S + Fintype.card (InfinitePlace K)
  have hs : 0 < s := by
    have := Fintype.card_pos (α := InfinitePlace K)
    positivity
  have hh : 0 ≤ logHeight₁ x := zero_le_logHeight₁ x
  have hlogE : Real.log ((Real.exp 1 * N) ^ (-C)) = -(C * (1 + Real.log N)) := by
    rw [Real.log_rpow (by positivity), Real.log_mul (Real.exp_pos 1).ne' hN.ne', Real.log_exp]
    ring
  -- Some place among those of `S` and the infinite places has `log ‖x‖_v ≤ -logHeight₁ x / s`.
  obtain ⟨v, hvT, hv⟩ :=
    GlobalNumberFields.exists_mem_log_normalizedAbsValue_le_neg_logHeight₁_div
      (T := S.disjSum univ) ⟨Sum.inr (Classical.arbitrary _), by simp⟩ (x := x) <| by
        rintro (v | w) hv
        · rw [GlobalNumberFields.normalizedAbsValue_inl]
          exact hx v (by simpa using hv)
        · simp at hv
  have hcard : ((S.disjSum (univ : Finset (InfinitePlace K))).card : ℝ) = s := by
    rw [card_disjSum, card_univ, Nat.cast_add]
  rw [hcard, neg_div] at hv
  suffices hL : logHeight₁ x / s ≤ 2 * (Real.log M + C * (1 + Real.log N)) by
    rw [div_le_iff₀ hs] at hL
    linarith
  rcases v with v | w
  · -- At a place `v ∈ S`: `|q - 1|_v = |δ|_v |x|_v ≤ M |x|_v`.
    have hvS : v ∈ S := by simpa using hvT
    rw [GlobalNumberFields.normalizedAbsValue_inl] at hv
    have hxv : 0 < HeightOneSpectrum.adicAbv K v x := (AbsoluteValue.pos_iff _).mpr hx0
    have hδv : 0 < HeightOneSpectrum.adicAbv K v δ := (AbsoluteValue.pos_iff _).mpr hδ
    have hM : 0 < M := hδv.trans_le (hδS v hvS)
    have key : (Real.exp 1 * N) ^ (-C) ≤ M * HeightOneSpectrum.adicAbv K v x := by
      refine (hfin v hvS hq).trans ?_
      rw [hq1, AbsoluteValue.map_neg, AbsoluteValue.map_mul]
      exact mul_le_mul_of_nonneg_right (hδS v hvS) hxv.le
    have hlog := Real.log_le_log (by positivity) key
    rw [hlogE, Real.log_mul hM.ne' hxv.ne'] at hlog
    have : 0 ≤ logHeight₁ x / s := by positivity
    linarith
  · -- At an infinite place `w`: `|σ q - 1| = |σ δ| w(x) ≤ M w(x)` for `σ` an embedding of `w`.
    rw [GlobalNumberFields.normalizedAbsValue_inr, Real.log_pow] at hv
    set σ := w.embedding
    have hxw : 0 < w x := (InfinitePlace.pos_iff).mpr hx0
    have hδσ : 0 < ‖σ δ‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hδ)
    have hM : 0 < M := hδσ.trans_le ((norm_embedding_le_house δ σ).trans hδM)
    have key : (Real.exp 1 * N) ^ (-C) ≤ M * w x := by
      refine (hinf σ hq).trans ?_
      rw [← map_one σ, ← map_sub, hq1, map_neg, norm_neg, map_mul, norm_mul,
        InfinitePlace.norm_embedding_eq w x]
      exact mul_le_mul_of_nonneg_right ((norm_embedding_le_house δ σ).trans hδM) hxw.le
    have hlog := Real.log_le_log (by positivity) key
    rw [hlogE, Real.log_mul hM.ne' hxw.ne'] at hlog
    -- The multiplicity of `w` is `1` or `2`, so `2 log w(x) ≤ -logHeight₁ x / s`.
    have hm1 : (1 : ℝ) ≤ w.mult := one_le_mult
    have hm2 : (w.mult : ℝ) ≤ 2 := by
      rw [mult]
      split_ifs <;> norm_num
    have : 0 ≤ logHeight₁ x / s := by positivity
    nlinarith

/-- **Exponent bound for unit equations in finitely generated groups** (Győry). Let `γ j` be
nonzero elements of a number field `K` with absolute value `1` at every finite place outside a
finite set `S`, and let `κ` bound exponents by heights:
`|z j| ≤ κ * logHeight₁ (ζ * ∏ i, γ i ^ z i)` for every root of unity `ζ` and every `z`. Let
`a, b ≠ 0`, let `M` bound `house a`, `house b` and `|a|_v`, `|b|_v` for `v ∈ S`, and let `C ≥ 0`
be such that for every `c ∈ {a, b}`, every root of unity `ζ` and every `z` with
`c ζ ∏ j, γ j ^ z j ≠ 1`, both `|σ (c ζ ∏ j, γ j ^ z j) - 1|` (for every complex embedding `σ`)
and `|c ζ ∏ j, γ j ^ z j - 1|_v` (for every `v ∈ S`) are at least
`(exp 1 * max(1, maxⱼ |z j|)) ^ (-C)`. If `a x + b y = 1` with `x = ζₓ ∏ j, γ j ^ zₓ j` and
`y = ζ_y ∏ j, γ j ^ z_y j` for roots of unity `ζₓ, ζ_y`, then
`max(|zₓ j|, |z_y j|) ≤ max(1, 2 A + 2 B₀ (log (2 B₀) - 1))` for every `j`, where
`s = #S + #{infinite places}`, `A = 2 κ s (log M + C)` and `B₀ = 2 κ s C`. -/
theorem max_abs_le_of_mul_add_mul_eq_one {ι : Type*} [Fintype ι]
    {S : Finset (HeightOneSpectrum (𝓞 K))} {γ : ι → K} (hγ0 : ∀ j, γ j ≠ 0)
    (hγS : ∀ j, ∀ v ∉ S, HeightOneSpectrum.adicAbv K v (γ j) = 1) {κ : ℝ}
    (hκ : ∀ ζ : K, IsOfFinOrder ζ → ∀ (z : ι → ℤ) (j : ι),
      |(z j : ℝ)| ≤ κ * logHeight₁ (ζ * ∏ i, γ i ^ z i))
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {M : ℝ} (haM : house a ≤ M) (hbM : house b ≤ M)
    (hSM : ∀ v ∈ S, HeightOneSpectrum.adicAbv K v a ≤ M ∧ HeightOneSpectrum.adicAbv K v b ≤ M)
    {C : ℝ} (hC : 0 ≤ C)
    (hinf : ∀ σ : K →+* ℂ, ∀ c ∈ ({a, b} : Set K), ∀ ζ : K, IsOfFinOrder ζ → ∀ z : ι → ℤ,
      c * ζ * ∏ j, γ j ^ z j ≠ 1 →
        (Real.exp 1 * max 1 ((Finset.univ.sup fun j ↦ (z j).natAbs : ℕ) : ℝ)) ^ (-C) ≤
          ‖σ (c * ζ * ∏ j, γ j ^ z j) - 1‖)
    (hfin : ∀ v ∈ S, ∀ c ∈ ({a, b} : Set K), ∀ ζ : K, IsOfFinOrder ζ → ∀ z : ι → ℤ,
      c * ζ * ∏ j, γ j ^ z j ≠ 1 →
        (Real.exp 1 * max 1 ((Finset.univ.sup fun j ↦ (z j).natAbs : ℕ) : ℝ)) ^ (-C) ≤
          HeightOneSpectrum.adicAbv K v (c * ζ * ∏ j, γ j ^ z j - 1))
    {ζx ζy : K} (hζx : IsOfFinOrder ζx) (hζy : IsOfFinOrder ζy) {zx zy : ι → ℤ}
    (hxy : a * (ζx * ∏ j, γ j ^ zx j) + b * (ζy * ∏ j, γ j ^ zy j) = 1) (j : ι) :
    let s : ℝ := #S + Fintype.card (InfinitePlace K)
    let A : ℝ := 2 * κ * s * (Real.log M + C)
    let B₀ : ℝ := 2 * κ * s * C
    max |(zx j : ℝ)| |(zy j : ℝ)| ≤ max 1 (2 * A + 2 * B₀ * (Real.log (2 * B₀) - 1)) := by
  classical
  intro s A B₀
  -- The largest exponent `Bn` is attained at some `j₀`.
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨j, Finset.mem_univ j⟩
    fun j ↦ max (zx j).natAbs (zy j).natAbs
  set Bn : ℕ := Finset.univ.sup fun j ↦ max (zx j).natAbs (zy j).natAbs
  set N : ℝ := max 1 (Bn : ℝ)
  have hN : 0 < N := zero_lt_one.trans_le (le_max_left _ _)
  have hs : 0 ≤ s := by positivity
  -- `κ ≥ 0`, by the exponent–height bound for `z = Pi.single j 1`.
  have hκ0 : 0 ≤ κ := by
    have h1 := hκ 1 IsOfFinOrder.one (Pi.single j 1) j
    simp only [Pi.single_eq_same, Int.cast_one, abs_one] at h1
    have := zero_le_logHeight₁ (1 * ∏ i, γ i ^ (Pi.single j 1 : ι → ℤ) i)
    nlinarith
  have hB₀ : 0 ≤ B₀ := by positivity
  have hprod (ζ : K) (hζ : IsOfFinOrder ζ) (z : ι → ℤ) :
      ζ * ∏ i, γ i ^ z i ≠ 0 ∧ ∀ v ∉ S, HeightOneSpectrum.adicAbv K v (ζ * ∏ i, γ i ^ z i) = 1 := by
    refine ⟨mul_ne_zero hζ.isUnit.ne_zero
      (prod_ne_zero_iff.mpr fun i _ ↦ zpow_ne_zero _ (hγ0 i)), fun v hv ↦ ?_⟩
    simp [map_zpow₀, hγS _ v hv, AbsoluteValue.map_eq_one_of_isOfFinOrder _ hζ]
  -- The lower bounds, with `max 1 (maxⱼ |z j|)` enlarged to `N`.
  have hLB {c : K} (hc : c ∈ ({a, b} : Set K)) {ζ : K} (hζ : IsOfFinOrder ζ) {z : ι → ℤ}
      (hz : (Finset.univ.sup fun j ↦ (z j).natAbs) ≤ Bn) :
      (∀ σ : K →+* ℂ, c * (ζ * ∏ i, γ i ^ z i) ≠ 1 →
        (Real.exp 1 * N) ^ (-C) ≤ ‖σ (c * (ζ * ∏ i, γ i ^ z i)) - 1‖) ∧
      ∀ v ∈ S, c * (ζ * ∏ i, γ i ^ z i) ≠ 1 →
        (Real.exp 1 * N) ^ (-C) ≤ HeightOneSpectrum.adicAbv K v (c * (ζ * ∏ i, γ i ^ z i) - 1) := by
    have hle : (Real.exp 1 * N) ^ (-C) ≤
        (Real.exp 1 * max 1 ((Finset.univ.sup fun j ↦ (z j).natAbs : ℕ) : ℝ)) ^ (-C) := by
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (neg_nonpos.mpr hC)
      gcongr
      exact max_le_max le_rfl (by exact_mod_cast hz)
    refine ⟨fun σ h ↦ ?_, fun v hv h ↦ ?_⟩
    · rw [← mul_assoc] at h ⊢
      exact hle.trans (hinf σ c hc ζ hζ z h)
    · rw [← mul_assoc] at h ⊢
      exact hle.trans (hfin v hv c hc ζ hζ z h)
  -- Hence every exponent is at most `A + B₀ log N`.
  have hexp (j : ι) : max |(zx j : ℝ)| |(zy j : ℝ)| ≤ A + B₀ * Real.log N := by
    have hAB : κ * (2 * s * (Real.log M + C * (1 + Real.log N))) = A + B₀ * Real.log N := by
      simp only [A, B₀]
      ring
    rw [← hAB]
    have hzx : (Finset.univ.sup fun j ↦ (zx j).natAbs) ≤ Bn :=
      Finset.sup_mono_fun fun j _ ↦ le_max_left _ _
    have hzy : (Finset.univ.sup fun j ↦ (zy j).natAbs) ≤ Bn :=
      Finset.sup_mono_fun fun j _ ↦ le_max_right _ _
    refine max_le ((hκ ζx hζx zx j).trans (mul_le_mul_of_nonneg_left ?_ hκ0))
      ((hκ ζy hζy zy j).trans (mul_le_mul_of_nonneg_left ?_ hκ0))
    · exact logHeight₁_le_of_add_mul_eq_one (hprod ζx hζx zx).1 (hprod ζx hζx zx).2 ha haM
        (fun v hv ↦ (hSM v hv).1) (by linear_combination hxy) hN
        (hLB (c := b) (by simp) hζy hzy).1 (hLB (c := b) (by simp) hζy hzy).2
    · exact logHeight₁_le_of_add_mul_eq_one (hprod ζy hζy zy).1 (hprod ζy hζy zy).2 hb hbM
        (fun v hv ↦ (hSM v hv).2) (by linear_combination hxy) hN
        (hLB (c := a) (by simp) hζx hzx).1 (hLB (c := a) (by simp) hζx hzx).2
  -- The largest exponent `Bn` satisfies `Bn ≤ A + B₀ log (max 1 Bn)`.
  have hcast (j : ι) :
      ((max (zx j).natAbs (zy j).natAbs : ℕ) : ℝ) = max |(zx j : ℝ)| |(zy j : ℝ)| := by
    rw [Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  have hBn : (Bn : ℝ) ≤ A + B₀ * Real.log N := by
    rw [hj₀, hcast]
    exact hexp j₀
  have hj : max |(zx j : ℝ)| |(zy j : ℝ)| ≤ Bn := by
    rw [← hcast]
    exact_mod_cast Finset.le_sup (f := fun j ↦ max (zx j).natAbs (zy j).natAbs)
      (Finset.mem_univ j)
  rcases le_or_gt (Bn : ℝ) 1 with h1 | h1
  · exact hj.trans (h1.trans (le_max_left _ _))
  refine hj.trans (le_trans ?_ (le_max_right _ _))
  simp only [N, max_eq_right h1.le] at hBn
  -- Solve `Bn ≤ A + B₀ log Bn`: as `log (Bn / (2 B₀)) ≤ Bn / (2 B₀) - 1`,
  -- `B₀ log Bn ≤ Bn / 2 + B₀ (log (2 B₀) - 1)`.
  rcases hB₀.eq_or_lt with h0 | h0
  · rw [← h0] at hBn ⊢
    simp only [zero_mul, add_zero, mul_zero] at hBn ⊢
    linarith
  have hBn0 : (0 : ℝ) < Bn := zero_lt_one.trans h1
  have hlog := Real.log_le_sub_one_of_pos (div_pos hBn0 (by positivity : (0 : ℝ) < 2 * B₀))
  rw [Real.log_div hBn0.ne' (by positivity)] at hlog
  have hmul : B₀ * ((Bn : ℝ) / (2 * B₀)) = Bn / 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog h0.le]

end TauCeti.NumberField.SUnit
