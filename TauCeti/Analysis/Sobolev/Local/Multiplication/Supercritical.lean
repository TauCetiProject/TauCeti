/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.Local.Norm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# Products of local Sobolev maps for `kp > 2`, including `p ≤ 2`

Let `Ω ⊆ ℂ` be open and let `B : F × G → H` be continuous bilinear with `F` and `G`
finite-dimensional. This file proves that `W^{k,p}_loc(Ω)` is an algebra under `B` whenever
`1 < p < ∞` and `kp > 2`. For `p > 2` this is `TauCeti.MemWkpLoc.bilin_succ`; the point here is the
range `p ≤ 2`. There `f` and `g` are still locally bounded, but their weak derivatives of order
`j` with `(k - j) p ≤ 2` need not be. Terms of the Leibniz rule in which neither factor is locally
bounded are controlled by the Sobolev embedding at every order and Hölder's inequality with
finite exponents; terms with a locally bounded factor may still use `L^∞_loc` bounds.

The algebra property is the diagonal case of a statement with three orders. If
`f ∈ W^{a,p}_loc`, `g ∈ W^{b,p}_loc`, `c ≤ a`, `c ≤ b` and `(a + b - c) p > 2`, then
`B(f, g) ∈ W^{c,p}_loc`. The proof is by induction on `c`.

* At `c = 0`, the Sobolev embedding `W^{a,p}_loc ⊂ L^s_loc` for `1/p - 1/s ≤ a/2` and its
  analogue for `g` give exponents `s_f` and `s_g` with `1/s_f + 1/s_g = 1/p`, and Hölder's
  inequality puts `B(f, g)` in `L^p_loc`. When `ap > 2` the factor `f` is locally bounded instead,
  and similarly for `g`.
* For `c + 1`, the weak Leibniz rule `D B(f, g) = B(Df, g) + B(f, Dg)` holds with finite Hölder
  exponents chosen from the same embedding, and both terms are products with the same value of
  `a + b - c` and one order less, for the bilinear maps `B.precompL ℂ` and `B.precompR ℂ`.

The Leibniz step needs `p > 1`: at `p = 1` a factor of order one has an integrable derivative
only, which pairs with no finite exponent of the other factor.

Each membership statement comes with a local bound, stated with the `W^{k,p}` size
`TauCeti.eLpNormWkp`: on a set `U` whose closure is compact and contained in `Ω`,
`‖B(f, g)‖_{W^{c,p}(U)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω)} ‖g‖_{W^{b,p}(Ω)}`, with `C` uniform in `B`, `f`
and `g`. The proof follows the same induction, with the estimates of the Sobolev embedding
(`TauCeti.exists_eLpNorm_le_mul_eLpNormWkp_of_inv_sub_inv_le_div_two` and
`TauCeti.exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul`) in place of the embeddings. These
bounds feed the higher-order elliptic estimates with Sobolev coefficients.

## Main declarations

* `TauCeti.MemWkpLoc.memLpLoc_bilin_of_two_lt_add_mul`: `B(f, g) ∈ L^p_loc` for
  `(a + b) p > 2`.
* `TauCeti.HasWeakFDerivOn.bilin_of_two_lt_add_mul` and
  `TauCeti.HasWeakFDerivOn.bilin_of_two_lt_mul`: the weak Leibniz rule
  `D B(f, g) = B(Df, g) + B(f, Dg)` for `f ∈ W^{a+1,p}_loc` and `g ∈ W^{b+1,p}_loc` with
  `(a + b + 1) p > 2`.
* `TauCeti.MemWkpLoc.bilin_of_two_lt_add_sub_mul`: `B(f, g) ∈ W^{c,p}_loc` for
  `(a + b - c) p > 2`.
* `TauCeti.MemWkpLoc.bilin_of_two_lt_mul`, `TauCeti.MemWkpLoc.clm_apply_of_two_lt_mul` and
  `TauCeti.MemWkpLoc.compL_of_two_lt_mul`: the algebra property of `W^{k,p}_loc` for `kp > 2`.
* `TauCeti.exists_eLpNorm_bilin_le_of_two_lt_add_mul` and
  `TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul`: the local bounds for products with
  `(a + b) p > 2` and `(a + b - c) p > 2`.
* `TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_mul`,
  `TauCeti.exists_eLpNormWkp_clm_apply_le_of_two_lt_mul` and
  `TauCeti.exists_eLpNormWkp_compL_le_of_two_lt_mul`: the local bounds for the algebra property
  for `kp > 2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, second edition, Theorem 4.39.
-/

public noncomputable section

open MeasureTheory TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ}

/-- The Sobolev embedding `W^{m,p}_loc ⊂ L^s_loc` in terms of the reciprocal `t = 1/s`, which is
how the exponents of products are chosen below. -/
private theorem MemWkpLoc.memLpLoc_inv_ofReal {p : ℝ≥0} {m : ℕ} {u : ℂ → F}
    (hu : MemWkpLoc p Ω m u) (hp : 1 ≤ p) {t : ℝ} (ht : 0 < t) (htp : t ≤ (p : ℝ)⁻¹)
    (hpt : (p : ℝ)⁻¹ ≤ t + m / 2) : MemLpLoc (ENNReal.ofReal t)⁻¹ Ω u := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  lift t to ℝ≥0 using ht.le
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  rw [ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_inv ht0]
  refine hu.memLpLoc_of_inv_sub_inv_le_div_two hp ?_ ?_
  · rw [← NNReal.coe_le_coe, NNReal.coe_inv, ← inv_le_inv₀ (inv_pos.2 ht) hp0, inv_inv]
    exact htp
  · rw [NNReal.coe_inv, inv_inv]
    linarith

/-- The exponent `(ofReal t)⁻¹` is at least one when `t ≤ 1`. -/
private theorem one_le_inv_ofReal {t : ℝ} (ht : t ≤ 1) : 1 ≤ (ENNReal.ofReal t)⁻¹ :=
  ENNReal.one_le_inv.2 (ENNReal.ofReal_le_one.2 ht)

/-- The exponent `(ofReal t)⁻¹` is finite when `0 < t`. -/
private theorem inv_ofReal_ne_top {t : ℝ} (ht : 0 < t) : (ENNReal.ofReal t)⁻¹ ≠ ∞ :=
  ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 ht).ne'

/-- The Hölder condition for the exponents `(ofReal t)⁻¹` and `(ofReal t')⁻¹`. -/
private theorem inv_inv_ofReal_add_le {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (h : t + t' ≤ 1) :
    (ENNReal.ofReal t)⁻¹⁻¹ + (ENNReal.ofReal t')⁻¹⁻¹ ≤ 1 := by
  rw [inv_inv, inv_inv, ← ENNReal.ofReal_add ht ht']
  exact ENNReal.ofReal_le_one.2 h

/-- Without local boundedness of a factor of order `m`, that is for `m p ≤ 2`, the reciprocal
exponent satisfies `m/2 ≤ 1/p`. -/
private theorem div_two_le_inv_of_not_two_lt_mul {p : ℝ≥0} (hp0 : (0 : ℝ) < p) {m : ℕ}
    (h : ¬ 2 < (m : ℝ≥0∞) * p) : (m : ℝ) / 2 ≤ (p : ℝ)⁻¹ := by
  have : (m : ℝ) * p ≤ 2 := by
    rw [not_lt] at h
    exact_mod_cast h
  rw [div_le_iff₀ two_pos, inv_mul_eq_div, le_div_iff₀ hp0]
  linarith

/-- The reciprocal exponents for the Leibniz step. For `0 < x < 1` there is `T : ℕ → ℝ` with
`0 < T m ≤ x ≤ T m + m/2` for every `m`, and `T m + T n ≤ 1` whenever `2x < m + n`. With
`x = 1/p`, a factor of order `m` then lies in `L^{1/T m}_loc`, and Hölder's inequality applies
to the pairs of orders in the Leibniz rule. -/
private theorem exists_leibniz_inv_exponents {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ T : ℕ → ℝ, (∀ m, 0 < T m) ∧ (∀ m, T m ≤ x) ∧ (∀ m : ℕ, x ≤ T m + m / 2) ∧
      ∀ m n : ℕ, 2 * x < m + n → T m + T n ≤ 1 := by
  -- Take `T m = max (x - m/2) δ`, where the floor `δ > 0` keeps every exponent finite.
  set δ : ℝ := x * (1 - x) / 2 with hδ_def
  have hδ : 0 < δ := by
    rw [hδ_def]
    nlinarith
  have hδx : δ ≤ x := by
    rw [hδ_def]
    nlinarith
  have hxδ : x + δ ≤ 1 := by
    rw [hδ_def]
    nlinarith
  refine ⟨fun m => max (x - m / 2) δ, fun m => lt_max_of_lt_right hδ,
    fun m => max_le (by linarith [m.cast_nonneg (α := ℝ)]) hδx,
    fun m => by linarith [le_max_left (x - m / 2) δ], fun m n hmn => ?_⟩
  simp only [max_def]
  split_ifs <;> linarith

/-- **Products of local Sobolev maps in `Lᵖ`.** Let `1 ≤ p` and let `f ∈ W^{a,p}_loc(Ω, F)` and
`g ∈ W^{b,p}_loc(Ω, G)` with `(a + b) p > 2`. Then `B(f, g)` is in `L^p_loc(Ω, H)`. -/
theorem MemWkpLoc.memLpLoc_bilin_of_two_lt_add_mul (B : F →L[ℝ] G →L[ℝ] H) {p : ℝ≥0}
    (hp : 1 ≤ p) {a b : ℕ} {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω a f)
    (hg : MemWkpLoc p Ω b g) (hab : 2 < ((a + b : ℕ) : ℝ≥0) * p) :
    MemLpLoc p Ω (fun z => B (f z) (g z)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  -- Hölder's inequality on each compact set, for any exponents `s`, `t` with `1/s + 1/t = 1/p`.
  have holder {s t : ℝ≥0∞} [ENNReal.HolderTriple s t p] (hfs : MemLpLoc s Ω f)
      (hgt : MemLpLoc t Ω g) : MemLpLoc p Ω (fun z => B (f z) (g z)) :=
    memLpLoc_iff.2 fun K hKΩ hK => B.memLp_of_bilin (p : ℝ≥0∞)
      (memLpLoc_iff.1 hfs K hKΩ hK) (memLpLoc_iff.1 hgt K hKΩ hK)
  -- If one factor is locally bounded, Hölder's inequality with `L^∞` suffices.
  by_cases ha : 2 < (a : ℝ≥0∞) * p
  · exact holder (hf.memLpLoc_top_of_two_lt_mul hp1 ha) hg.memLpLoc
  by_cases hb : 2 < (b : ℝ≥0∞) * p
  · exact holder hf.memLpLoc (hg.memLpLoc_top_of_two_lt_mul hp1 hb)
  -- Otherwise `1/p - a/2` and `1/p - b/2` are nonnegative with sum below `1/p`, and raising both
  -- by half the defect gives reciprocal exponents summing to `1/p`.
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  have hxa := div_two_le_inv_of_not_two_lt_mul hp0 ha
  have hxb := div_two_le_inv_of_not_two_lt_mul hp0 hb
  set x : ℝ := (p : ℝ)⁻¹ with hx
  have hxab : 2 * x < a + b := by
    have : (2 : ℝ) < (a + b) * p := by exact_mod_cast hab
    rw [hx, ← div_eq_mul_inv, div_lt_iff₀ hp0]
    exact this
  set ε : ℝ := ((a + b) / 2 - x) / 2 with hε_def
  have hε : 0 < ε := by linarith
  set tf : ℝ := x - a / 2 + ε with htf_def
  set tg : ℝ := x - b / 2 + ε with htg_def
  have htf : 0 < tf := by linarith
  have htg : 0 < tg := by linarith
  have hfs := hf.memLpLoc_inv_ofReal hp htf (by linarith) (by linarith)
  have hgs := hg.memLpLoc_inv_ofReal hp htg (by linarith) (by linarith)
  have : ENNReal.HolderTriple (ENNReal.ofReal tf)⁻¹ (ENNReal.ofReal tg)⁻¹ p := by
    refine ⟨?_⟩
    rw [inv_inv, inv_inv, ← ENNReal.ofReal_add htf.le htg.le,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_inv_of_pos hp0]
    congr 1
    rw [htf_def, htg_def, hε_def]
    ring
  exact holder hfs hgs

/-- **The weak Leibniz rule for `kp > 2`, with two orders.** Let `1 < p`, let
`f ∈ W^{a+1,p}_loc(Ω, F)` and `g ∈ W^{b+1,p}_loc(Ω, G)` have weak derivatives `Df` and `Dg` on
`Ω`, and let `(a + b + 1) p > 2`. Then `B(Df, g) + B(f, Dg)` is a weak derivative of `B(f, g)` on
`Ω`. For `p ≤ 2` the factors and their derivatives need not be locally bounded, and the products
are integrable by the Sobolev embedding of each factor and Hölder's inequality. -/
theorem HasWeakFDerivOn.bilin_of_two_lt_add_mul [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    {p : ℝ≥0} (hp : 1 < p) {a b : ℕ} {f : ℂ → F} {g : ℂ → G} {Df : ℂ → ℂ →L[ℝ] F}
    {Dg : ℂ → ℂ →L[ℝ] G}
    (hDf : HasWeakFDerivOn volume Ω f Df) (hDg : HasWeakFDerivOn volume Ω g Dg)
    (hf : MemWkpLoc p Ω (a + 1) f) (hg : MemWkpLoc p Ω (b + 1) g)
    (hab : 2 < ((a + b + 1 : ℕ) : ℝ≥0) * p) :
    HasWeakFDerivOn volume Ω (fun z => B (f z) (g z))
      (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) := by
  have hDfa := hf.memWkpLoc_of_hasWeakFDerivOn hDf
  have hDgb := hg.memWkpLoc_of_hasWeakFDerivOn hDg
  -- A factor of order `m` is placed in `L^{1/T m}_loc`, for the exponents `T` of
  -- `exists_leibniz_inv_exponents` at `x = 1/p`.
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans (by exact_mod_cast hp)
  set x : ℝ := (p : ℝ)⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hp0
  have hx1 : x < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)
  have hxab : 2 * x < a + b + 1 := by
    have : (2 : ℝ) < ((a + b + 1 : ℕ) : ℝ) * p := by exact_mod_cast hab
    push_cast at this
    rw [hx, ← div_eq_mul_inv, div_lt_iff₀ hp0]
    exact this
  obtain ⟨T, hT0, hTx, hxT, hsum⟩ := exists_leibniz_inv_exponents hx0 hx1
  -- These local `Fact` instances supply the `[Fact (1 ≤ _)]` arguments of
  -- `HasWeakFDerivOn.bilin_of_memLp` below.
  have hP (m : ℕ) : Fact (1 ≤ (ENNReal.ofReal (T m))⁻¹) :=
    ⟨one_le_inv_ofReal ((hTx m).trans hx1.le)⟩
  have hfP := hf.memLpLoc_inv_ofReal hp.le (hT0 _) (hTx _) (hxT _)
  have hDfP := hDfa.memLpLoc_inv_ofReal hp.le (hT0 _) (hTx _) (hxT _)
  have hgP := hg.memLpLoc_inv_ofReal hp.le (hT0 _) (hTx _) (hxT _)
  have hDgP := hDgb.memLpLoc_inv_ofReal hp.le (hT0 _) (hTx _) (hxT _)
  exact hDf.bilin_of_memLp B (inv_ofReal_ne_top (hT0 _)) (inv_ofReal_ne_top (hT0 _))
    (inv_ofReal_ne_top (hT0 _)) (inv_ofReal_ne_top (hT0 _))
    (inv_inv_ofReal_add_le (hT0 _).le (hT0 _).le (hsum (a + 1) (b + 1) (by push_cast; linarith)))
    (inv_inv_ofReal_add_le (hT0 _).le (hT0 _).le (hsum a (b + 1) (by push_cast; linarith)))
    (inv_inv_ofReal_add_le (hT0 _).le (hT0 _).le (hsum (a + 1) b (by push_cast; linarith)))
    hDg (fun K hK hKΩ => memLpLoc_iff.1 hfP K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hDfP K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hgP K hKΩ hK)
    (fun K hK hKΩ => memLpLoc_iff.1 hDgP K hKΩ hK)

/-- **The weak Leibniz rule for `kp > 2`.** Let `1 < p` and `(k + 1) p > 2`, and let
`f ∈ W^{k+1,p}_loc(Ω, F)` and `g ∈ W^{k+1,p}_loc(Ω, G)` have weak derivatives `Df` and `Dg` on
`Ω`. Then `B(Df, g) + B(f, Dg)` is a weak derivative of `B(f, g)` on `Ω`. -/
theorem HasWeakFDerivOn.bilin_of_two_lt_mul [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    {p : ℝ≥0} (hp : 1 < p) {k : ℕ} {f : ℂ → F} {g : ℂ → G} {Df : ℂ → ℂ →L[ℝ] F} {Dg : ℂ → ℂ →L[ℝ] G}
    (hDf : HasWeakFDerivOn volume Ω f Df) (hDg : HasWeakFDerivOn volume Ω g Dg)
    (hf : MemWkpLoc p Ω (k + 1) f) (hg : MemWkpLoc p Ω (k + 1) g)
    (hkp : 2 < ((k + 1 : ℕ) : ℝ≥0) * p) :
    HasWeakFDerivOn volume Ω (fun z => B (f z) (g z))
      (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) :=
  hDf.bilin_of_two_lt_add_mul B hp hDg hf hg
    (hkp.trans_le (mul_le_mul_left (Nat.cast_le.2 (by omega)) _))

/-- **Products of local Sobolev maps with three orders.** Let `1 < p`, let
`f ∈ W^{a,p}_loc(Ω, F)` and `g ∈ W^{b,p}_loc(Ω, G)`, and let `c ≤ a`, `c ≤ b` with
`(a + b - c) p > 2`. Then `B(f, g)` is in `W^{c,p}_loc(Ω, H)`. -/
theorem MemWkpLoc.bilin_of_two_lt_add_sub_mul [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    {p : ℝ≥0} (hp : 1 < p) {a b c : ℕ} {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω a f)
    (hg : MemWkpLoc p Ω b g) (hca : c ≤ a) (hcb : c ≤ b)
    (habc : 2 < ((a + b - c : ℕ) : ℝ≥0) * p) :
    MemWkpLoc p Ω c (fun z => B (f z) (g z)) := by
  induction c generalizing F G H a b with
  | zero => exact memWkpLoc_zero_iff.2 (hf.memLpLoc_bilin_of_two_lt_add_mul B hp.le hg habc)
  | succ c ih =>
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨Df, hDf, hDfa⟩ := hf.exists_weakFDeriv_of_isOpen
    obtain ⟨Dg, hDg, hDgb⟩ := hg.exists_weakFDeriv_of_isOpen
    have hD := hDf.bilin_of_two_lt_add_mul B hp hDg hf hg
      (habc.trans_le (mul_le_mul_left (Nat.cast_le.2 (by omega)) _))
    -- Both terms of the Leibniz rule keep the value of `a + b - c` and lose one order.
    have habc' : a + (b + 1) - c = a + 1 + (b + 1) - (c + 1) := by omega
    have habc'' : a + 1 + b - c = a + 1 + (b + 1) - (c + 1) := by omega
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨(hf.memLpLoc_bilin_of_two_lt_add_mul B hp.le hg
      (habc.trans_le (mul_le_mul_left (Nat.cast_le.2 (Nat.sub_le _ _)) _))), _, hD, ?_⟩
    exact (ih (B.precompL ℂ) hDfa hg (by omega) (by omega) (by rwa [habc'])).add
      (ih (B.precompR ℂ) hf hDgb (by omega) (by omega) (by rwa [habc'']))

/-- **The algebra property for `kp > 2`.** Let `1 < p` and `k p > 2`. For `f ∈ W^{k,p}_loc(Ω, F)`
and `g ∈ W^{k,p}_loc(Ω, G)`, the product `B(f, g)` is in `W^{k,p}_loc(Ω, H)`. This includes
`p ≤ 2` for `k ≥ 2`. -/
theorem MemWkpLoc.bilin_of_two_lt_mul [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) {p : ℝ≥0}
    (hp : 1 < p) {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc p Ω k f) (hg : MemWkpLoc p Ω k g) :
    MemWkpLoc p Ω k (fun z => B (f z) (g z)) :=
  hf.bilin_of_two_lt_add_sub_mul B hp hg le_rfl le_rfl (by rwa [Nat.add_sub_cancel])

/-- **Coefficient fields acting on local Sobolev maps for `kp > 2`.** Let `1 < p` and `k p > 2`.
A coefficient field `A ∈ W^{k,p}_loc(Ω; F →L[ℝ] G)` applied to `u ∈ W^{k,p}_loc(Ω; F)` gives
`z ↦ A z (u z) ∈ W^{k,p}_loc(Ω; G)`. -/
theorem MemWkpLoc.clm_apply_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {A : ℂ → F →L[ℝ] G} {u : ℂ → F} (hA : MemWkpLoc p Ω k A)
    (hu : MemWkpLoc p Ω k u) : MemWkpLoc p Ω k (fun z => A z (u z)) :=
  hA.bilin_of_two_lt_mul (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) hp hkp hu

/-- **Composition of local Sobolev fields of linear maps for `kp > 2`.** Let `1 < p` and
`k p > 2`. If `A ∈ W^{k,p}_loc(Ω; G →L[ℝ] H)` and `C ∈ W^{k,p}_loc(Ω; F →L[ℝ] G)`, then
`z ↦ A z ∘L C z ∈ W^{k,p}_loc(Ω; F →L[ℝ] H)`. -/
theorem MemWkpLoc.compL_of_two_lt_mul [FiniteDimensional ℝ H] {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {A : ℂ → G →L[ℝ] H} {C : ℂ → F →L[ℝ] G}
    (hA : MemWkpLoc p Ω k A) (hC : MemWkpLoc p Ω k C) :
    MemWkpLoc p Ω k (fun z => (A z).comp (C z)) :=
  hA.bilin_of_two_lt_mul (ContinuousLinearMap.compL ℝ F G H) hp hkp hC

/-! ### Local bounds -/

/-- The local Sobolev bound `‖u‖_{L^{1/t}(U)} ≤ C ‖u‖_{W^{m,p}(Ω)}` in terms of the reciprocal
exponent `t`, for `0 < t ≤ 1/p ≤ t + m/2` and a set `U` whose closure is compact and contained in
`Ω`. -/
private theorem exists_eLpNorm_inv_ofReal_le {p : ℝ≥0} (hp : 1 ≤ p) {m : ℕ} {t : ℝ} (ht : 0 < t)
    (htp : t ≤ (p : ℝ)⁻¹) (hpt : (p : ℝ)⁻¹ ≤ t + m / 2) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F,
      eLpNorm u (ENNReal.ofReal t)⁻¹ (volume.restrict U) ≤ C * eLpNormWkp p Ω m u := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  lift t to ℝ≥0 using ht.le
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  rw [ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_inv ht0]
  refine exists_eLpNorm_le_mul_eLpNormWkp_of_inv_sub_inv_le_div_two hp ?_ ?_ hU hUΩ
  · rw [← NNReal.coe_le_coe, NNReal.coe_inv, ← inv_le_inv₀ (inv_pos.2 ht) hp0, inv_inv]
    exact htp
  · rw [NNReal.coe_inv, inv_inv]
    linarith

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ G] in
/-- Hölder's inequality on `U` turns bounds for the factors in `Lˢ(U)` and `Lᵗ(U)`, with
`1/s + 1/t = 1/p`, by their Sobolev norms on `Ω` into a bound for their product in `Lᵖ(U)`. -/
private theorem exists_eLpNorm_bilin_le_of_holderTriple {p : ℝ≥0} (hp : 1 ≤ p) {a b : ℕ}
    {s t : ℝ≥0∞} [ENNReal.HolderTriple s t p] {U : Set ℂ} (hUΩ : U ⊆ Ω) {Cf Cg : ℝ≥0}
    (hCf : ∀ f : ℂ → F, eLpNorm f s (volume.restrict U) ≤ Cf * eLpNormWkp p Ω a f)
    (hCg : ∀ g : ℂ → G, eLpNorm g t (volume.restrict U) ≤ Cg * eLpNormWkp p Ω b g) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNorm (fun z => B (f z) (g z)) p (volume.restrict U) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω a f * eLpNormWkp p Ω b g := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le (by exact_mod_cast hp : (1 : ℝ≥0∞) ≤ p)).ne'
  have hUm : volume.restrict U ≤ volume.restrict Ω := Measure.restrict_mono hUΩ le_rfl
  refine ⟨Cf * Cg + 1, fun B f g => ?_⟩
  refine le_mul_eNorm_mul_eLpNormWkp_mul_eLpNormWkp_of_ne_top_imp_le hp0 hp0 hUΩ hUΩ
    (by positivity) (fun h => by rw [eLpNorm_congr_ae h, eLpNorm_zero]) fun hf hg => ?_
  calc
    _ ≤ ‖B‖ₑ * eLpNorm f s (volume.restrict U) * eLpNorm g t (volume.restrict U) :=
      eLpNorm_le_eNorm_mul_eLpNorm_mul_eLpNorm B
        ((memLp_of_eLpNormWkp_ne_top hf).aestronglyMeasurable.mono_measure hUm)
        ((memLp_of_eLpNormWkp_ne_top hg).aestronglyMeasurable.mono_measure hUm)
    _ ≤ ‖B‖ₑ * (Cf * eLpNormWkp p Ω a f) * (Cg * eLpNormWkp p Ω b g) := by
      gcongr
      exacts [hCf f, hCg g]
    _ = ↑(Cf * Cg) * ‖B‖ₑ * eLpNormWkp p Ω a f * eLpNormWkp p Ω b g := by
      push_cast
      ring
    _ ≤ _ := by
      gcongr
      exact_mod_cast le_self_add

omit [FiniteDimensional ℝ F] in
/-- The `Lᵖ(U)` norm is at most the `W^{m,p}(Ω)` norm, for `U ⊆ Ω`. -/
private theorem eLpNorm_le_one_mul_eLpNormWkp {p : ℝ≥0} {m : ℕ} {U : Set ℂ} (hUΩ : U ⊆ Ω)
    (u : ℂ → F) : eLpNorm u p (volume.restrict U) ≤ (1 : ℝ≥0) * eLpNormWkp p Ω m u := by
  rw [ENNReal.coe_one, one_mul]
  exact (eLpNorm_mono_measure u (Measure.restrict_mono hUΩ le_rfl)).trans eLpNorm_le_eLpNormWkp

/-- **Local bound for products in `Lᵖ`.** Let `1 ≤ p` and `(a + b) p > 2`, and let `U` have
compact closure contained in `Ω`. There is a constant `C` such that
`‖B(f, g)‖_{Lᵖ(U)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω)} ‖g‖_{W^{b,p}(Ω)}` for every continuous bilinear map
`B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This is the bound that accompanies
`TauCeti.MemWkpLoc.memLpLoc_bilin_of_two_lt_add_mul`. -/
theorem exists_eLpNorm_bilin_le_of_two_lt_add_mul {p : ℝ≥0} (hp : 1 ≤ p) {a b : ℕ}
    (hab : 2 < ((a + b : ℕ) : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNorm (fun z => B (f z) (g z)) p (volume.restrict U) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω a f * eLpNormWkp p Ω b g := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
  -- If one factor is locally bounded, Hölder's inequality with `L^∞` suffices.
  by_cases ha : 2 < (a : ℝ≥0∞) * p
  · obtain ⟨Cf, hCf⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul (F := F) hp1 ha hU hUΩ
    exact exists_eLpNorm_bilin_le_of_holderTriple hp hUΩ' hCf (eLpNorm_le_one_mul_eLpNormWkp hUΩ')
  by_cases hb : 2 < (b : ℝ≥0∞) * p
  · obtain ⟨Cg, hCg⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul (F := G) hp1 hb hU hUΩ
    exact exists_eLpNorm_bilin_le_of_holderTriple hp hUΩ' (eLpNorm_le_one_mul_eLpNormWkp hUΩ') hCg
  -- Otherwise the exponents are those of `TauCeti.MemWkpLoc.memLpLoc_bilin_of_two_lt_add_mul`.
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  have hxa := div_two_le_inv_of_not_two_lt_mul hp0 ha
  have hxb := div_two_le_inv_of_not_two_lt_mul hp0 hb
  set x : ℝ := (p : ℝ)⁻¹ with hx
  have hxab : 2 * x < a + b := by
    have : (2 : ℝ) < (a + b) * p := by exact_mod_cast hab
    rw [hx, ← div_eq_mul_inv, div_lt_iff₀ hp0]
    exact this
  set ε : ℝ := ((a + b) / 2 - x) / 2 with hε_def
  have hε : 0 < ε := by linarith
  set tf : ℝ := x - a / 2 + ε with htf_def
  set tg : ℝ := x - b / 2 + ε with htg_def
  have htf : 0 < tf := by linarith
  have htg : 0 < tg := by linarith
  obtain ⟨Cf, hCf⟩ := exists_eLpNorm_inv_ofReal_le (F := F) (m := a) hp htf (by linarith)
    (by linarith) hU hUΩ
  obtain ⟨Cg, hCg⟩ := exists_eLpNorm_inv_ofReal_le (F := G) (m := b) hp htg (by linarith)
    (by linarith) hU hUΩ
  have : ENNReal.HolderTriple (ENNReal.ofReal tf)⁻¹ (ENNReal.ofReal tg)⁻¹ p := by
    refine ⟨?_⟩
    rw [inv_inv, inv_inv, ← ENNReal.ofReal_add htf.le htg.le,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_inv_of_pos hp0]
    congr 1
    rw [htf_def, htg_def, hε_def]
    ring
  exact exists_eLpNorm_bilin_le_of_holderTriple hp hUΩ' hCf hCg

/-- **Local bound for products with three orders.** Let `1 < p`, let `c ≤ a`, `c ≤ b` with
`(a + b - c) p > 2`, and let `U` have compact closure contained in `Ω`. There is a constant `C`
such that `‖B(f, g)‖_{W^{c,p}(U)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω)} ‖g‖_{W^{b,p}(Ω)}` for every
continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This is the
bound that accompanies `TauCeti.MemWkpLoc.bilin_of_two_lt_add_sub_mul`. -/
theorem exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul [CompleteSpace H] {p : ℝ≥0}
    (hp : 1 < p) {a b c : ℕ} (hca : c ≤ a) (hcb : c ≤ b)
    (habc : 2 < ((a + b - c : ℕ) : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp p U c (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω a f * eLpNormWkp p Ω b g := by
  induction c generalizing F G H a b with
  | zero =>
    obtain ⟨C, hC⟩ := exists_eLpNorm_bilin_le_of_two_lt_add_mul (F := F) (G := G) (H := H)
      hp.le (by simpa using habc) hU hUΩ
    exact ⟨C, fun B f g => by simpa only [eLpNormWkp_zero] using hC B f g⟩
  | succ c ih =>
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hle {n : ℕ} (hn : a + 1 + (b + 1) - (c + 1) ≤ n) : 2 < (n : ℝ≥0) * p :=
      habc.trans_le (mul_le_mul_left (Nat.cast_le.2 hn) _)
    -- The order-zero bound controls the `Lᵖ` part. Both terms of the Leibniz rule keep the value
    -- of `a + b - c` and lose one order, for the bilinear maps `B.precompL ℂ` and
    -- `B.precompR ℂ`.
    obtain ⟨C₀, hC₀⟩ := exists_eLpNorm_bilin_le_of_two_lt_add_mul (F := F) (G := G) (H := H)
      hp.le (a := a + 1) (b := b + 1) (hle (by omega)) hU hUΩ
    have habc' : a + (b + 1) - c = a + 1 + (b + 1) - (c + 1) := by omega
    have habc'' : a + 1 + b - c = a + 1 + (b + 1) - (c + 1) := by omega
    obtain ⟨Cl, hCl⟩ := ih (F := ℂ →L[ℝ] F) (G := G) (H := ℂ →L[ℝ] H) (a := a) (b := b + 1)
      (by omega) (by omega) (by rwa [habc'])
    obtain ⟨Cr, hCr⟩ := ih (F := F) (G := ℂ →L[ℝ] G) (H := ℂ →L[ℝ] H) (a := a + 1) (b := b)
      (by omega) (by omega) (by rwa [habc''])
    refine ⟨C₀ + Cl + Cr + 1, fun B f g => ?_⟩
    have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
    have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hp1).ne'
    have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
    refine le_mul_eNorm_mul_eLpNormWkp_mul_eLpNormWkp_of_ne_top_imp_le hp0 hp0 hUΩ' hUΩ'
      (by positivity) (fun h => by rw [eLpNormWkp_congr_ae h, eLpNormWkp_zero_fun]) fun hf hg => ?_
    -- Weak derivatives of the factors realizing their norms on `Ω`.
    obtain ⟨Df, hDf, -, hfΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hf
    obtain ⟨Dg, hDg, -, hgΩ⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hg
    set X := eLpNormWkp p Ω (a + 1) f
    set Y := eLpNormWkp p Ω (b + 1) g
    have hDfX : eLpNormWkp p Ω a Df ≤ X := hfΩ ▸ le_add_self
    have hDgY : eLpNormWkp p Ω b Dg ≤ Y := hgΩ ▸ le_add_self
    have hLeib := hDf.bilin_of_two_lt_add_mul B hp hDg (memWkpLoc_of_eLpNormWkp_ne_top hf)
      (memWkpLoc_of_eLpNormWkp_ne_top hg) (hle (by omega))
    calc
      _ ≤ eLpNorm (fun z => B (f z) (g z)) p (volume.restrict U) +
          eLpNormWkp p U c
            (fun z => B.precompL ℂ (Df z) (g z) + B.precompR ℂ (f z) (Dg z)) :=
        eLpNormWkp_succ_le (hLeib.mono fun z hz => hUΩ' (interior_subset hz))
      _ ≤ eLpNorm (fun z => B (f z) (g z)) p (volume.restrict U) +
          (eLpNormWkp p U c (fun z => B.precompL ℂ (Df z) (g z)) +
            eLpNormWkp p U c (fun z => B.precompR ℂ (f z) (Dg z))) :=
        add_le_add le_rfl (eLpNormWkp_add_le hp1)
      _ ≤ C₀ * ‖B‖ₑ * X * Y + (Cl * ‖B‖ₑ * X * Y + Cr * ‖B‖ₑ * X * Y) := by
        gcongr
        · exact hC₀ B f g
        · exact (hCl (B.precompL ℂ) Df g).trans
            (by gcongr; exact eNorm_le_iff_norm_le.2 (B.norm_precompL_le ℂ))
        · exact (hCr (B.precompR ℂ) f Dg).trans
            (by gcongr; exact eNorm_le_iff_norm_le.2 (B.norm_precompR_le ℂ))
      _ = ↑(C₀ + Cl + Cr) * ‖B‖ₑ * X * Y := by push_cast; ring
      _ ≤ _ := by gcongr ?_ * _ * _ * _; exact_mod_cast le_self_add

/-- **Local bound for the algebra property for `kp > 2`.** Let `1 < p` and `k p > 2`, and let
`U` have compact closure contained in `Ω`. There is a constant `C` such that
`‖B(f, g)‖_{W^{k,p}(U)} ≤ C ‖B‖ ‖f‖_{W^{k,p}(Ω)} ‖g‖_{W^{k,p}(Ω)}` for every continuous bilinear
map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This includes `p ≤ 2` for
`k ≥ 2`, and is the bound that accompanies `TauCeti.MemWkpLoc.bilin_of_two_lt_mul`. -/
theorem exists_eLpNormWkp_bilin_le_of_two_lt_mul [CompleteSpace H] {p : ℝ≥0} (hp : 1 < p)
    {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp p U k (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω k f * eLpNormWkp p Ω k g :=
  exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul hp le_rfl le_rfl
    (by rwa [Nat.add_sub_cancel]) hU hUΩ

/-- **Local bound for coefficient fields for `kp > 2`.** Let `1 < p` and `k p > 2`, and let `U`
have compact closure contained in `Ω`. There is a constant `C` such that
`‖z ↦ A z (u z)‖_{W^{k,p}(U)} ≤ C ‖A‖_{W^{k,p}(Ω)} ‖u‖_{W^{k,p}(Ω)}` for every coefficient field
`A : ℂ → F →L[ℝ] G` and every `u : ℂ → F`. This is the bound that accompanies
`TauCeti.MemWkpLoc.clm_apply_of_two_lt_mul`. -/
theorem exists_eLpNormWkp_clm_apply_le_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → F →L[ℝ] G) (u : ℂ → F),
      eLpNormWkp p U k (fun z => A z (u z)) ≤
        C * eLpNormWkp p Ω k A * eLpNormWkp p Ω k u := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_mul (F := F →L[ℝ] G) (G := F) (H := G)
    hp hkp hU hUΩ
  refine ⟨C, fun A u => (hC (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) A u).trans ?_⟩
  calc
    _ ≤ C * 1 * eLpNormWkp p Ω k A * eLpNormWkp p Ω k u := by
      gcongr
      exact (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_one.2 ContinuousLinearMap.norm_id_le)
    _ = _ := by rw [mul_one]

/-- **Local bound for compositions of fields of linear maps for `kp > 2`.** Let `1 < p` and
`k p > 2`, and let `U` have compact closure contained in `Ω`. There is a constant `C` such that
`‖z ↦ A z ∘L T z‖_{W^{k,p}(U)} ≤ C ‖A‖_{W^{k,p}(Ω)} ‖T‖_{W^{k,p}(Ω)}` for all fields
`A : ℂ → G →L[ℝ] H` and `T : ℂ → F →L[ℝ] G`. This is the bound that accompanies
`TauCeti.MemWkpLoc.compL_of_two_lt_mul`. -/
theorem exists_eLpNormWkp_compL_le_of_two_lt_mul [FiniteDimensional ℝ H] {p : ℝ≥0} (hp : 1 < p)
    {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → G →L[ℝ] H) (T : ℂ → F →L[ℝ] G),
      eLpNormWkp p U k (fun z => (A z).comp (T z)) ≤
        C * eLpNormWkp p Ω k A * eLpNormWkp p Ω k T := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_mul (F := G →L[ℝ] H) (G := F →L[ℝ] G)
    (H := F →L[ℝ] H) hp hkp hU hUΩ
  refine ⟨C, fun A T => (hC (ContinuousLinearMap.compL ℝ F G H) A T).trans ?_⟩
  calc
    _ ≤ C * 1 * eLpNormWkp p Ω k A * eLpNormWkp p Ω k T := by
      gcongr
      exact (ofReal_norm _).symm.trans_le
        (ENNReal.ofReal_le_one.2 (ContinuousLinearMap.norm_compL_le ℝ F G H))
    _ = _ := by rw [mul_one]

/-- The check at `p = 4/3` and `k = 2`: here `kp = 8/3 > 2` while `p < 2`, outside the range
`p > 2` of `TauCeti.MemWkpLoc.bilin_succ`, and `W^{2,4/3}_loc` is an algebra. -/
example [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 f) (hg : MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 g) :
    MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 (fun z => B (f z) (g z)) :=
  hf.bilin_of_two_lt_mul B (by norm_num) (by norm_num) hg

/-- The bound at `p = 4/3` and `k = 2`, where `kp = 8/3 > 2` while `p < 2`: on the disc of radius
`1/2`, the `W^{2,4/3}` norm of a product is controlled by the norms of the factors on the unit
disc. -/
example [CompleteSpace H] :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) (1 / 2)) 2 (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) 1) 2 f *
          eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) 1) 2 g :=
  exists_eLpNormWkp_bilin_le_of_two_lt_mul (Ω := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩)
    (by norm_num) (by norm_num)
    ((isCompact_closedBall 0 (1 / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall)
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num)))

end TauCeti
