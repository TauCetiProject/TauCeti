/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# Products of local Sobolev maps for `kp > 2`, including `p ≤ 2`

Let `Ω ⊆ ℂ` be open and let `B : F × G → H` be continuous bilinear with `F` and `G`
finite-dimensional. This file proves that `W^{k,p}_loc(Ω)` is an algebra under `B` whenever
`1 < p < ∞` and `kp > 2`. For `p > 2` this is `TauCeti.MemWkpLoc.bilin_succ`; the point here is the
range `p ≤ 2`, where the factors need not be locally bounded and the weak derivatives of the
product are controlled by the Sobolev embedding at every order rather than by `L^∞` bounds.

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

## Main declarations

* `TauCeti.MemWkpLoc.of_add_of_inv_sub_inv_le`: the Sobolev embedding lowering the order by `k`,
  `W^{k+m,q}_loc ⊂ W^{m,s}_loc` for `1/q - 1/s ≤ k/2`.
* `TauCeti.MemWkpLoc.memLpLoc_top_of_two_lt_mul`: local boundedness of `W^{k,p}_loc` for `kp > 2`.
* `TauCeti.MemWkpLoc.memLpLoc_bilin_of_two_lt_add_mul`: `B(f, g) ∈ L^p_loc` for
  `(a + b) p > 2`.
* `TauCeti.MemWkpLoc.bilin_of_two_lt_add_mul`: `B(f, g) ∈ W^{c,p}_loc` for
  `(a + b - c) p > 2`.
* `TauCeti.MemWkpLoc.bilin_of_two_lt_mul`, `TauCeti.MemWkpLoc.clm_apply_of_two_lt_mul` and
  `TauCeti.MemWkpLoc.compL_of_two_lt_mul`: the algebra property of `W^{k,p}_loc` for `kp > 2`.

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

/-- **The Sobolev embedding at every order.** If `1 ≤ q ≤ s < ∞` and `1/q - 1/s ≤ k/2`, then
`W^{k+m,q}_loc(Ω, F) ⊂ W^{m,s}_loc(Ω, F)`. At `m = 0` this is `W^{k,q}_loc ⊂ L^s_loc`. -/
theorem MemWkpLoc.of_add_of_inv_sub_inv_le {q s : ℝ≥0} {k m : ℕ} {u : ℂ → F}
    (hu : MemWkpLoc q Ω (k + m) u) (hq : 1 ≤ q) (hqs : q ≤ s)
    (hgap : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ k / 2) : MemWkpLoc s Ω m u := by
  -- Each step lowers the order by one and replaces `1/q` by `max (1/q - 1/2) (1/s)`.
  induction k generalizing q with
  | zero =>
    have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le (by exact_mod_cast hq)
    have hsq : (q : ℝ)⁻¹ ≤ (s : ℝ)⁻¹ := by
      have : (q : ℝ)⁻¹ - (s : ℝ)⁻¹ ≤ 0 := by simpa using hgap
      linarith
    have hs0 : (0 : ℝ) < s := hq0.trans_le (by exact_mod_cast hqs)
    have hsq' : (s : ℝ) ≤ q := (inv_le_inv₀ hq0 hs0).1 hsq
    have hs : s = q := le_antisymm (by exact_mod_cast hsq') hqs
    subst hs
    simpa using hu
  | succ k ih =>
    have hq0 : (0 : ℝ) < q := zero_lt_one.trans_le (by exact_mod_cast hq)
    have hs0 : (0 : ℝ) < s := hq0.trans_le (by exact_mod_cast hqs)
    set r : ℝ := max ((q : ℝ)⁻¹ - 2⁻¹) (s : ℝ)⁻¹ with hr
    have hr0 : 0 < r := lt_max_of_lt_right (inv_pos.2 hs0)
    let q₁ : ℝ≥0 := ⟨r⁻¹, (inv_pos.2 hr0).le⟩
    have hq₁ : (q₁ : ℝ)⁻¹ = r := inv_inv r
    have hq₁0 : (0 : ℝ) < q₁ := inv_pos.2 hr0
    have hrq : r ≤ (q : ℝ)⁻¹ :=
      max_le (by linarith) ((inv_le_inv₀ hs0 hq0).2 (by exact_mod_cast hqs))
    have hqq₁ : q ≤ q₁ := by
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hq₁0 hq0, hq₁]
      exact hrq
    have hq₁s : q₁ ≤ s := by
      rw [← NNReal.coe_le_coe, ← inv_le_inv₀ hs0 hq₁0, hq₁]
      exact le_max_right _ _
    have hu' : MemWkpLoc q Ω (k + m + 1) u := by rwa [show k + m + 1 = k + 1 + m by omega]
    refine ih (hu'.of_succ_of_inv_sub_inv_le hq hqq₁ ?_) (hq.trans hqq₁) hq₁s ?_
    · rw [hq₁]
      linarith [le_max_left ((q : ℝ)⁻¹ - 2⁻¹) (s : ℝ)⁻¹]
    · rw [hq₁]
      push_cast at hgap
      rcases max_cases ((q : ℝ)⁻¹ - 2⁻¹) (s : ℝ)⁻¹ with ⟨h, -⟩ | ⟨h, -⟩
      · rw [hr, h]
        linarith
      · rw [hr, h, sub_self]
        positivity

/-- **Local boundedness for `kp > 2`.** If `1 ≤ p ≤ ∞` and `2 < k p`, every
`u ∈ W^{k,p}_loc(Ω, F)` is locally essentially bounded on `Ω`. -/
theorem MemWkpLoc.memLpLoc_top_of_two_lt_mul {p : ℝ≥0∞} {k : ℕ} {u : ℂ → F} (hp : 1 ≤ p)
    (hkp : 2 < (k : ℝ≥0∞) * p) (hu : MemWkpLoc p Ω k u) : MemLpLoc ∞ Ω u := by
  refine memLpLoc_iff.2 fun K hKΩ hK => ?_
  obtain ⟨W, hKW, hWΩ, hWc⟩ := Opens.exists_between_and_isCompact_closure hK hKΩ
  have hKc : closure K = K := hK.isClosed.closure_eq
  obtain ⟨C, hC⟩ := exists_eLpNorm_top_le_mul_eLpNormWkp_of_two_lt_mul (F := F) (W := W) hp hkp
    (by rwa [hKc]) (by rwa [hKc])
  exact memLp_iff.2 ((hC u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_top_iff_ne_top.2 (hu.eLpNormWkp_ne_top_of_closure_subset hWc hWΩ))))

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
  refine memWkpLoc_zero_iff.1 (MemWkpLoc.of_add_of_inv_sub_inv_le (k := m) (m := 0) hu hp ?_ ?_)
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

/-- **Products of local Sobolev maps in `Lᵖ`.** Let `1 ≤ p` and let `f ∈ W^{a,p}_loc(Ω, F)` and
`g ∈ W^{b,p}_loc(Ω, G)` with `(a + b) p > 2`. Then `B(f, g)` is in `L^p_loc(Ω, H)`. -/
theorem MemWkpLoc.memLpLoc_bilin_of_two_lt_add_mul (B : F →L[ℝ] G →L[ℝ] H) {p : ℝ≥0}
    (hp : 1 ≤ p) {a b : ℕ} {f : ℂ → F} {g : ℂ → G} (hf : MemWkpLoc p Ω a f)
    (hg : MemWkpLoc p Ω b g) (hab : 2 < ((a + b : ℕ) : ℝ≥0) * p) :
    MemLpLoc p Ω (fun z => B (f z) (g z)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  -- If one factor is locally bounded, Hölder's inequality with `L^∞` suffices.
  by_cases ha : 2 < (a : ℝ≥0∞) * p
  · have hfi := hf.memLpLoc_top_of_two_lt_mul hp1 ha
    exact memLpLoc_iff.2 fun K hKΩ hK => B.memLp_of_bilin (p : ℝ≥0∞)
      (memLpLoc_iff.1 hfi K hKΩ hK) (memLpLoc_iff.1 hg.memLpLoc K hKΩ hK)
  by_cases hb : 2 < (b : ℝ≥0∞) * p
  · have hgi := hg.memLpLoc_top_of_two_lt_mul hp1 hb
    exact memLpLoc_iff.2 fun K hKΩ hK => B.memLp_of_bilin (p : ℝ≥0∞)
      (memLpLoc_iff.1 hf.memLpLoc K hKΩ hK) (memLpLoc_iff.1 hgi K hKΩ hK)
  -- Otherwise `1/p - a/2` and `1/p - b/2` are nonnegative with sum below `1/p`, and raising both
  -- by half the defect gives reciprocal exponents summing to `1/p`.
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le (by exact_mod_cast hp)
  set x : ℝ := (p : ℝ)⁻¹ with hx
  have hx0 : 0 < x := inv_pos.2 hp0
  have hxa : (a : ℝ) / 2 ≤ x := by
    have : (a : ℝ) * p ≤ 2 := by
      rw [not_lt] at ha
      exact_mod_cast ha
    rw [hx, div_le_iff₀ two_pos, inv_mul_eq_div, le_div_iff₀ hp0]
    linarith
  have hxb : (b : ℝ) / 2 ≤ x := by
    have : (b : ℝ) * p ≤ 2 := by
      rw [not_lt] at hb
      exact_mod_cast hb
    rw [hx, div_le_iff₀ two_pos, inv_mul_eq_div, le_div_iff₀ hp0]
    linarith
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
  exact memLpLoc_iff.2 fun K hKΩ hK => B.memLp_of_bilin (p : ℝ≥0∞)
    (memLpLoc_iff.1 hfs K hKΩ hK) (memLpLoc_iff.1 hgs K hKΩ hK)

/-- **Products of local Sobolev maps with three orders.** Let `1 < p`, let
`f ∈ W^{a,p}_loc(Ω, F)` and `g ∈ W^{b,p}_loc(Ω, G)`, and let `c ≤ a`, `c ≤ b` with
`(a + b - c) p > 2`. Then `B(f, g)` is in `W^{c,p}_loc(Ω, H)`. -/
theorem MemWkpLoc.bilin_of_two_lt_add_mul [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
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
    -- The reciprocal exponent for a factor of order `m` is `T m = max (1/p - m/2) δ`, where the
    -- floor `δ > 0` keeps every exponent finite.
    have hp0 : (0 : ℝ) < p := zero_lt_one.trans (by exact_mod_cast hp)
    set x : ℝ := (p : ℝ)⁻¹ with hx
    have hx0 : 0 < x := inv_pos.2 hp0
    have hx1 : x < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)
    have hxab : 2 * x < a + b + 1 := by
      have h : ((a + 1 + (b + 1) - (c + 1) : ℕ) : ℝ) ≤ a + b + 1 := by
        have := Nat.cast_le (α := ℝ).2 (show a + 1 + (b + 1) - (c + 1) ≤ a + b + 1 by omega)
        push_cast at this
        exact this
      have : (2 : ℝ) < ((a + 1 + (b + 1) - (c + 1) : ℕ) : ℝ) * p := by exact_mod_cast habc
      rw [hx, ← div_eq_mul_inv, div_lt_iff₀ hp0]
      nlinarith
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
    let T : ℕ → ℝ := fun m => max (x - m / 2) δ
    have hT0 (m : ℕ) : 0 < T m := lt_max_of_lt_right hδ
    have hTx (m : ℕ) : T m ≤ x := max_le (by linarith [m.cast_nonneg (α := ℝ)]) hδx
    have hxT (m : ℕ) : x ≤ T m + m / 2 := by
      linarith [le_max_left (x - m / 2) δ]
    have hsum (m n : ℕ) (hmn : 2 * x < m + n) : T m + T n ≤ 1 := by
      simp only [T, max_def]
      split_ifs <;> linarith
    have hP (m : ℕ) : Fact (1 ≤ (ENNReal.ofReal (T m))⁻¹) :=
      ⟨one_le_inv_ofReal ((hTx m).trans hx1.le)⟩
    have hfP := hf.memLpLoc_inv_ofReal hp.le (hT0 _) (hTx _) (hxT _)
    have hDfP := hDfa.memLpLoc_inv_ofReal hp.le (hT0 _) (hTx _) (hxT _)
    have hgP := hg.memLpLoc_inv_ofReal hp.le (hT0 _) (hTx _) (hxT _)
    have hDgP := hDgb.memLpLoc_inv_ofReal hp.le (hT0 _) (hTx _) (hxT _)
    have hD := hDf.bilin_of_memLp B (inv_ofReal_ne_top (hT0 _)) (inv_ofReal_ne_top (hT0 _))
      (inv_ofReal_ne_top (hT0 _)) (inv_ofReal_ne_top (hT0 _))
      (inv_inv_ofReal_add_le (hT0 _).le (hT0 _).le (hsum (a + 1) (b + 1) (by push_cast; linarith)))
      (inv_inv_ofReal_add_le (hT0 _).le (hT0 _).le (hsum a (b + 1) (by push_cast; linarith)))
      (inv_inv_ofReal_add_le (hT0 _).le (hT0 _).le (hsum (a + 1) b (by push_cast; linarith)))
      hDg (fun K hK hKΩ => memLpLoc_iff.1 hfP K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDfP K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hgP K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDgP K hKΩ hK)
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
  hf.bilin_of_two_lt_add_mul B hp hg le_rfl le_rfl (by rwa [Nat.add_sub_cancel])

/-- **Coefficient fields acting on local Sobolev maps for `kp > 2`.** Let `1 < p` and `k p > 2`.
A coefficient field `A ∈ W^{k,p}_loc(Ω; F →L[ℝ] G)` applied to `u ∈ W^{k,p}_loc(Ω; F)` gives
`z ↦ A z (u z) ∈ W^{k,p}_loc(Ω; G)`. -/
theorem MemWkpLoc.clm_apply_of_two_lt_mul [CompleteSpace G] {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
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

/-- The check at `p = 4/3` and `k = 2`: here `kp = 8/3 > 2` while `p < 2`, outside the range
`p > 2` of `TauCeti.MemWkpLoc.bilin_succ`, and `W^{2,4/3}_loc` is an algebra. -/
example [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 f) (hg : MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 g) :
    MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 (fun z => B (f z) (g z)) :=
  hf.bilin_of_two_lt_mul B (by norm_num) (by norm_num) hg

end TauCeti
