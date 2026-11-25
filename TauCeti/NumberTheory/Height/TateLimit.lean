/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Tate's limit

Let `φ : S → S` be a self-map of an arbitrary type, let `d > 1`, and let `f : S → ℝ` scale by `d`
along `φ` up to a uniformly bounded error: `|f (φ s) - d * f s| ≤ C` for every `s`. Tate's limit
replaces `f` by the unique function `f̂` that scales by `d` along `φ` *exactly* and stays at
bounded distance from `f`:

`f̂ s = f s + ∑_{m ≥ 0} (f (φ^[m+1] s) - d * f (φ^[m] s)) / d ^ (m + 1)`,

and `f̂ s = lim_{n → ∞} f (φ^[n] s) / dⁿ`.

This is the engine behind every canonical height. For the multiplication-by-two map on an abelian
variety and a Weil height of a symmetric line bundle (`d = 4`) it gives the Néron–Tate height; for
an endomorphism of projective space of degree `d ≥ 2` and the Weil height it gives the canonical
height of the dynamical system. Nothing here depends on the arithmetic: `S` is an arbitrary type
and `f` an arbitrary real function.

## Main definitions

* `TauCeti.tateLimit φ d f`: the series above.

## Main results

* `TauCeti.summable_tateLimit`: under the bounded-error hypothesis the defining series converges
  absolutely, so the definition is not the junk value `0` of a divergent `tsum`.
* `TauCeti.abs_tateLimit_sub_le`: `|f̂ s - f s| ≤ C / (d - 1)`.
* `TauCeti.tateLimit_comp` and `TauCeti.tateLimit_iterate`: `f̂ (φ s) = d * f̂ s`, and hence
  `f̂ (φ^[n] s) = dⁿ * f̂ s`.
* `TauCeti.abs_div_pow_sub_tateLimit_le` and `TauCeti.tendstoUniformly_tateLimit`: the normalized
  iterates `f (φ^[n] s) / dⁿ` converge to `f̂ s`, uniformly in `s`, with error at most
  `C / ((d - 1) dⁿ)`; `TauCeti.tendsto_tateLimit` is the pointwise limit.
* `TauCeti.tateLimit_unique` and `TauCeti.tateLimit_eq_iff`: `f̂` is the only function that scales
  by `d` along `φ` and lies at bounded distance from `f`. Uniqueness needs no hypothesis on `f`:
  the existence of such a function already bounds the error of `f`.
* `TauCeti.eq_zero_of_comp_eq_mul_of_abs_le`: the rigidity behind uniqueness, a bounded function
  that scales by `d > 1` along `φ` vanishes.
* `TauCeti.tateLimit_eq_of_abs_sub_le`: functions at bounded distance from each other have the same
  Tate limit, so the Tate limit only depends on the class of `f` modulo bounded functions.
* `TauCeti.tateLimit_add` and `TauCeti.tateLimit_smul`: additivity and homogeneity in `f`.

## Implementation notes

The definition is the series rather than `limUnder` of the normalized iterates: the series makes
`tateLimit_comp` an index shift and `abs_tateLimit_sub_le` a comparison with a geometric series,
and `tateLimit_smul` holds with no hypothesis at all. The limit description is then recovered from
the scaling law and the distance bound.

## References

* G. S. Call and J. H. Silverman, *Canonical heights on varieties with morphisms*, Compositio
  Math. 89 (1993), Theorem 1.1 and Proposition 1.2.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9.
-/

public section

open Filter Topology

namespace TauCeti

variable {S : Type*}

/-- **Tate's limit** of `f : S → ℝ` along `φ : S → S` with scaling factor `d`:
`f s + ∑_{m ≥ 0} (f (φ^[m+1] s) - d * f (φ^[m] s)) / d ^ (m + 1)`.

When `1 < d` and `f ∘ φ - d • f` is bounded this is the limit of `f (φ^[n] s) / dⁿ`
(`tendsto_tateLimit`), and it is the unique function scaling by `d` along `φ` at bounded distance
from `f` (`tateLimit_unique`). -/
noncomputable def tateLimit (φ : S → S) (d : ℝ) (f : S → ℝ) (s : S) : ℝ :=
  f s + ∑' m : ℕ, (f (φ^[m + 1] s) - d * f (φ^[m] s)) / d ^ (m + 1)

theorem tateLimit_def (φ : S → S) (d : ℝ) (f : S → ℝ) (s : S) :
    tateLimit φ d f s = f s + ∑' m : ℕ, (f (φ^[m + 1] s) - d * f (φ^[m] s)) / d ^ (m + 1) :=
  (rfl)

variable {φ : S → S} {d C : ℝ} {f : S → ℝ}

/-- The `m`-th term of the series defining `tateLimit` is at most `C / d ^ (m + 1)`. -/
private theorem norm_tateTerm_le (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) (s : S)
    (m : ℕ) :
    ‖(f (φ^[m + 1] s) - d * f (φ^[m] s)) / d ^ (m + 1)‖ ≤ C * d⁻¹ ^ (m + 1) := by
  have hpos : (0 : ℝ) < d ^ (m + 1) := pow_pos (by linarith) _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, inv_pow, ← div_eq_mul_inv,
    Function.iterate_succ_apply']
  exact div_le_div_of_nonneg_right (hf _) hpos.le

/-- The series `∑ C * d⁻¹ ^ (m + 1)` dominating the series of `tateLimit` sums to `C / (d - 1)`. -/
private theorem hasSum_mul_inv_pow_succ (hd : 1 < d) :
    HasSum (fun m : ℕ ↦ C * d⁻¹ ^ (m + 1)) (C / (d - 1)) := by
  have h := (hasSum_geometric_of_lt_one (inv_nonneg.mpr (by linarith))
    (inv_lt_one_of_one_lt₀ hd)).mul_left (C * d⁻¹)
  convert h using 1
  · funext m
    ring
  · field_simp [show d - 1 ≠ 0 by linarith, show d ≠ 0 by linarith]

/-- Under the bounded-error hypothesis the series defining `tateLimit` converges absolutely. -/
theorem summable_tateLimit (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) (s : S) :
    Summable fun m : ℕ ↦ (f (φ^[m + 1] s) - d * f (φ^[m] s)) / d ^ (m + 1) :=
  (hasSum_mul_inv_pow_succ hd).summable.of_norm_bounded (norm_tateTerm_le hd hf s)

/-- **Tate's limit is at bounded distance from `f`**: `|tateLimit φ d f s - f s| ≤ C / (d - 1)`
when `|f (φ s) - d * f s| ≤ C` for every `s`. -/
theorem abs_tateLimit_sub_le (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) (s : S) :
    |tateLimit φ d f s - f s| ≤ C / (d - 1) := by
  rw [tateLimit_def, add_sub_cancel_left]
  exact tsum_of_norm_bounded (hasSum_mul_inv_pow_succ hd) (norm_tateTerm_le hd hf s)

/-- **Tate's limit scales by `d` along `φ`**: `tateLimit φ d f (φ s) = d * tateLimit φ d f s`.
The series at `φ s` is `d` times the tail of the series at `s`. -/
theorem tateLimit_comp (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) (s : S) :
    tateLimit φ d f (φ s) = d * tateLimit φ d f s := by
  have hd0 : d ≠ 0 := by linarith
  have hshift : ∀ m : ℕ, (f (φ^[m + 1] (φ s)) - d * f (φ^[m] (φ s))) / d ^ (m + 1)
      = d * ((f (φ^[m + 1 + 1] s) - d * f (φ^[m + 1] s)) / d ^ (m + 1 + 1)) := by
    intro m
    rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply, pow_succ _ (m + 1)]
    field_simp
  rw [tateLimit_def, tateLimit_def, tsum_congr hshift, tsum_mul_left,
    (summable_tateLimit hd hf s).tsum_eq_zero_add]
  simp only [Function.iterate_one, Function.iterate_zero, id_eq, zero_add, pow_one]
  field_simp
  ring

/-- A function that scales by `a` along `φ` scales by `a ^ n` along `φ^[n]`. -/
theorem apply_iterate_eq_pow_mul {M : Type*} [Monoid M] {a : M} {h : S → M}
    (hh : ∀ s, h (φ s) = a * h s) (n : ℕ) (s : S) : h (φ^[n] s) = a ^ n * h s :=
  (Function.Semiconj.iterate_right (gb := (a * ·)) hh n s).trans (mul_left_iterate_apply a _)

/-- Iterating `tateLimit_comp`: `tateLimit φ d f (φ^[n] s) = d ^ n * tateLimit φ d f s`. -/
theorem tateLimit_iterate (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) (n : ℕ) (s : S) :
    tateLimit φ d f (φ^[n] s) = d ^ n * tateLimit φ d f s :=
  apply_iterate_eq_pow_mul (tateLimit_comp hd hf) n s

/-- **The normalized iterates approximate Tate's limit geometrically**:
`|f (φ^[n] s) / dⁿ - tateLimit φ d f s| ≤ C / ((d - 1) * dⁿ)`. -/
theorem abs_div_pow_sub_tateLimit_le (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) (n : ℕ)
    (s : S) :
    |f (φ^[n] s) / d ^ n - tateLimit φ d f s| ≤ C / ((d - 1) * d ^ n) := by
  have hpos : (0 : ℝ) < d ^ n := pow_pos (by linarith) _
  have h := abs_tateLimit_sub_le hd hf (φ^[n] s)
  rw [tateLimit_iterate hd hf, abs_sub_comm] at h
  have e : f (φ^[n] s) / d ^ n - tateLimit φ d f s
      = (f (φ^[n] s) - d ^ n * tateLimit φ d f s) / d ^ n := by
    field_simp
  rw [e, abs_div, abs_of_pos hpos, ← div_div]
  exact div_le_div_of_nonneg_right h hpos.le

/-- **Tate's limit is the uniform limit of the normalized iterates** `f (φ^[n] s) / dⁿ`. -/
theorem tendstoUniformly_tateLimit (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) :
    TendstoUniformly (fun (n : ℕ) (s : S) ↦ f (φ^[n] s) / d ^ n) (tateLimit φ d f) atTop := by
  have hlim : Tendsto (fun n : ℕ ↦ C / (d - 1) / d ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hd)
  refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn s
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_div_pow_sub_tateLimit_le hd hf n s).trans_lt (by rwa [← div_div])

/-- **Tate's limit is the limit of the normalized iterates** `f (φ^[n] s) / dⁿ`. -/
theorem tendsto_tateLimit (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) (s : S) :
    Tendsto (fun n : ℕ ↦ f (φ^[n] s) / d ^ n) atTop (𝓝 (tateLimit φ d f s)) :=
  (tendstoUniformly_tateLimit hd hf).tendsto_at s

/-- A function at distance at most `C'` from a function with scaling error at most `C` has scaling
error at most `C + (1 + |d|) * C'`. -/
theorem abs_comp_sub_mul_le_of_abs_sub_le {g : S → ℝ} {C' : ℝ}
    (hf : ∀ s, |f (φ s) - d * f s| ≤ C) (hfg : ∀ s, |g s - f s| ≤ C') (s : S) :
    |g (φ s) - d * g s| ≤ C + (1 + |d|) * C' := by
  have h1 := hfg (φ s)
  have h2 : |d * (g s - f s)| ≤ |d| * C' := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hfg s) (abs_nonneg d)
  calc |g (φ s) - d * g s| = |(f (φ s) - d * f s) + (g (φ s) - f (φ s)) - d * (g s - f s)| := by
        congr 1; ring
    _ ≤ |f (φ s) - d * f s| + |g (φ s) - f (φ s)| + |d * (g s - f s)| := by
        have := abs_add_le (f (φ s) - d * f s) (g (φ s) - f (φ s))
        have := abs_sub (f (φ s) - d * f s + (g (φ s) - f (φ s))) (d * (g s - f s))
        linarith
    _ ≤ C + C' + |d| * C' := by gcongr; exact hf s
    _ = C + (1 + |d|) * C' := by ring

/-- **Rigidity**: a bounded function that scales by `d > 1` along `φ` vanishes. -/
theorem eq_zero_of_comp_eq_mul_of_abs_le {h : S → ℝ} {B : ℝ} (hd : 1 < d)
    (hh : ∀ s, h (φ s) = d * h s) (hB : ∀ s, |h s| ≤ B) (s : S) : h s = 0 := by
  by_contra hne
  have hpos : 0 < |h s| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hd).atTop_mul_const hpos).eventually
    (eventually_gt_atTop B) |>.exists
  have := hB (φ^[n] s)
  rw [apply_iterate_eq_pow_mul hh, abs_mul, abs_of_pos (pow_pos (by linarith) n)] at this
  linarith

/-- A function at distance at most `C'` from `f` is at distance at most `C / (d - 1) + C'` from
`tateLimit φ d f`. -/
theorem abs_tateLimit_sub_le_of_abs_sub_le (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C)
    {g : S → ℝ} {C' : ℝ} (hgf : ∀ s, |g s - f s| ≤ C') (s : S) :
    |tateLimit φ d f s - g s| ≤ C / (d - 1) + C' :=
  (abs_sub_le _ (f s) _).trans <|
    add_le_add (abs_tateLimit_sub_le hd hf s) ((abs_sub_comm _ _).trans_le (hgf s))

/-- **Uniqueness of Tate's limit**: a function `g` that scales by `d > 1` along `φ` and lies at
bounded distance from `f` is `tateLimit φ d f`. No hypothesis on `f` is needed: such a `g` already
bounds the scaling error of `f`. -/
theorem tateLimit_unique (hd : 1 < d) {g : S → ℝ} (hg : ∀ s, g (φ s) = d * g s) {C' : ℝ}
    (hgf : ∀ s, |g s - f s| ≤ C') : tateLimit φ d f = g := by
  have hf : ∀ s, |f (φ s) - d * f s| ≤ 0 + (1 + |d|) * C' :=
    abs_comp_sub_mul_le_of_abs_sub_le (C := 0) (g := f) (f := g)
      (fun s ↦ by rw [hg, sub_self, abs_zero])
      (fun s ↦ by rw [abs_sub_comm]; exact hgf s)
  have hscale : ∀ s, tateLimit φ d f (φ s) - g (φ s) = d * (tateLimit φ d f s - g s) := by
    intro s
    rw [tateLimit_comp hd hf, hg]
    ring
  funext s
  exact sub_eq_zero.mp <| eq_zero_of_comp_eq_mul_of_abs_le (h := fun s ↦ tateLimit φ d f s - g s)
    hd hscale (abs_tateLimit_sub_le_of_abs_sub_le hd hf hgf) s

/-- **Characterization of Tate's limit**: when `f` scales by `d > 1` along `φ` up to a bounded
error, `tateLimit φ d f` is exactly the function that scales by `d` along `φ` and lies at bounded
distance from `f`. -/
theorem tateLimit_eq_iff (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) {g : S → ℝ} :
    tateLimit φ d f = g ↔ (∀ s, g (φ s) = d * g s) ∧ ∃ C' : ℝ, ∀ s, |g s - f s| ≤ C' := by
  refine ⟨?_, fun ⟨hg, C', hgf⟩ ↦ tateLimit_unique hd hg hgf⟩
  rintro rfl
  exact ⟨tateLimit_comp hd hf, C / (d - 1), abs_tateLimit_sub_le hd hf⟩

/-- A function that already scales by `d` along `φ` is its own Tate limit: every term of the
defining series vanishes. -/
theorem tateLimit_eq_self (hf : ∀ s, f (φ s) = d * f s) : tateLimit φ d f = f := by
  funext s
  simp [tateLimit_def, Function.iterate_succ_apply', hf]

/-- **Tate's limit only depends on `f` up to bounded functions**: if `f` has bounded scaling error
and `g` is at bounded distance from `f`, then `f` and `g` have the same Tate limit. -/
theorem tateLimit_eq_of_abs_sub_le (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C)
    {g : S → ℝ} {C' : ℝ} (hfg : ∀ s, |g s - f s| ≤ C') : tateLimit φ d g = tateLimit φ d f :=
  tateLimit_unique hd (tateLimit_comp hd hf) (abs_tateLimit_sub_le_of_abs_sub_le hd hf hfg)

/-- **Tate's limit is additive** in functions with bounded scaling error. -/
theorem tateLimit_add (hd : 1 < d) (hf : ∀ s, |f (φ s) - d * f s| ≤ C) {g : S → ℝ} {C' : ℝ}
    (hg : ∀ s, |g (φ s) - d * g s| ≤ C') :
    tateLimit φ d (f + g) = tateLimit φ d f + tateLimit φ d g := by
  funext s
  simp only [tateLimit_def, Pi.add_apply]
  rw [add_add_add_comm, ← (summable_tateLimit hd hf s).tsum_add (summable_tateLimit hd hg s)]
  congr 1
  exact tsum_congr fun m ↦ by ring

/-- **Tate's limit is homogeneous** in `f`. This needs no hypothesis: scalars pass through every
`tsum` in `ℝ`, summable or not. -/
@[simp]
theorem tateLimit_smul (φ : S → S) (d c : ℝ) (f : S → ℝ) :
    tateLimit φ d (c • f) = c • tateLimit φ d f := by
  funext s
  simp only [tateLimit_def, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun m ↦ by ring

end TauCeti
