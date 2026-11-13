/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Taubes's gradient bound for large-parameter Seiberg–Witten solutions

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `ψ = α u₀ + β`, where `α` is a section of the
twisting line and `β` the component orthogonal to the canonical spinor `u₀`. Write
`w₊ = max (1 - |α|²) 0` for the vacuum defect. Among Taubes's coarse a priori estimates is the
pointwise gradient bound

`|∇_a α|² + r |∇β|² ≤ C' r w₊ + C'`,

with `C'` independent of `r` and of the solution. Thus `|∇_a α| = O(r^(1/2))` everywhere, and
where `|α| ≥ 1` the gradients are small: `|∇_a α|² ≤ C'` and `|∇β|² ≤ C' / r`. The
coarse bounds of `TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds` and
`TauCeti.Analysis.PDE.SeibergWitten.ConeDefect` take it as a hypothesis.

This file derives it on a closed Riemannian manifold, writing `Δ = div ∘ grad`
(`TauCeti.Manifold.laplaceBeltrami`), from two pairs of scalar differential inequalities with a
constant `c`. The first pair are the projected Weitzenböck inequalities, obtained by pairing the
projected equations `∇*∇α = (r / 4) (1 - |α|² - |β|²) α + 𝔞` and
`∇*∇β + (r / 4) (1 + |α|² + |β|²) β = 𝔟` with `α` and `β`:

`-Δ|α|² / 2 + |∇_a α|² + (r / 4) (|α|² + |β|² - 1) |α|² ≤ c |α| (|∇β| + |α| + |β|)`,
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)`.

The second pair come from differentiating the projected equations once and pairing with `∇_a α`
and `∇β`:

`-Δ|∇_a α|² / 2 + |∇²α|² ≤ c (r (|∇_a α|² + |∇_a α| |∇β| + |∇_a α|) +`
`  (|∇²β| + |∇_a α| + |∇β| + 1) |∇_a α|)`,
`-Δ|∇β|² / 2 + |∇²β|² ≤ c (r (|∇β|² + |β| (|∇_a α| + |∇β| + 1) |∇β|) +`
`  (|∇²α| + |∇_a α| + |∇β| + 1) |∇β|)`.

Here the factor `r` collects the derivative of the potential `(r / 4) (|α|² + |β|² ∓ 1)` and the
commutator of `∇` with `∇*∇`, which involves the curvature `F_a` and its divergence; the constant
`c` absorbs a bound `|F_a| ≤ c r`, the curvature equation for `d*F_a`, the bounds on `|α|` and
`|β|`, and the derivatives of the coefficients of `𝔞` and `𝔟`. The second derivatives of the other
component enter through the derivatives of the cross terms of `𝔞` and `𝔟`. The remaining inputs are
Taubes's first two coarse bounds, `|α|² + |β|² ≤ 1 + C / r` and `|β|² ≤ (C / r) w₊ + C / r²`.

The proof is a comparison argument by the maximum principle. With `m = 1 + 2 C`, the function
`G = m |∇_a α|² + r |∇β|²` is a subsolution, `-Δ G / 2 ≤ A r G + B r`, once the second
derivatives are absorbed by Young's inequality. The function `V = m (1 - |α|²) - r |β|²` is a
supersolution with source `G`, `(3 / 4) G ≤ -Δ V / 2 + K₁ r w₊ + O(1)`, because the Weitzenböck
inequality for `|α|²` contains `|∇_a α|²` with a good sign. At a maximum of `G - K r V` with
`K ≥ max (4 A) (2 K₁)`, the two inequalities give `G ≤ 2 K₁ r w₊ + O(1)`. Since
`r (1 - |α|²) ≥ r w₊ - C` and `r² |β|² ≤ C r w₊ + C`, the potential satisfies
`r V ≥ (m - C) r w₊ - O(1) = (1 + C) r w₊ - O(1)`; the coefficient `K (1 + C)` dominates the
defect coefficient `2 K₁`, so the maximum of `G - K r V` is `O(1)`. Hence `G ≤ K r V + O(1)`
everywhere, which is the bound. The constant is `C' = 150 (1 + c + C)⁵`
(`TauCeti.SeibergWitten.norm_sq_add_mul_norm_sq_le`).

The sections, their covariant derivatives and second covariant derivatives are arbitrary families
of elements of normed groups over the manifold satisfying the displayed inequalities; only the
squared norms `|α|²`, `|β|²`, `|∇_a α|²` and `|∇β|²` need to be `C²`. Deriving the scalar
inequalities from the Seiberg–Witten equations is not done here.

## Main results

* `TauCeti.SeibergWitten.norm_sq_add_mul_norm_sq_le`: the gradient bound
  `|∇_a α|² + r |∇β|² ≤ C' r w₊ + C'` with `C' = 150 (1 + c + C)⁵`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti.SeibergWitten

/-! ### The comparison inequality for the defect -/

section Defect

variable {a b p q c C r : ℝ}

/-- The bound `|β|² ≤ (C / r) w₊ + C / r²` in the form `r² |β|² ≤ C r w₊ + C`. -/
private theorem sq_mul_sq_le (hr : 1 ≤ r)
    (ht : b ^ 2 ≤ C / r * max (1 - a ^ 2) 0 + C / r ^ 2) :
    r ^ 2 * b ^ 2 ≤ C * r * max (1 - a ^ 2) 0 + C := by
  have := mul_le_mul_of_nonneg_left ht (sq_nonneg r)
  have e : r ^ 2 * (C / r * max (1 - a ^ 2) 0 + C / r ^ 2) = C * r * max (1 - a ^ 2) 0 + C := by
    have : r ≠ 0 := by linarith
    field_simp
  linarith

/-- The potential term of the `α` inequality is controlled by the defect `w₊ = max (1 - |α|²) 0`:
where `1 - |α|² - |β|² > 0` the factor `|α|²` is below one. -/
private theorem potential_le (hr : 0 ≤ r) :
    r / 4 * (1 - a ^ 2 - b ^ 2) * a ^ 2 ≤ r / 4 * max (1 - a ^ 2) 0 := by
  have hw0 : 0 ≤ max (1 - a ^ 2) 0 := le_max_right _ _
  have hr4 : 0 ≤ r / 4 := by positivity
  rcases le_or_gt (1 - a ^ 2 - b ^ 2) 0 with h | h
  · have : (1 - a ^ 2 - b ^ 2) * a ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg a)
    have : r / 4 * ((1 - a ^ 2 - b ^ 2) * a ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr4 this
    have : 0 ≤ r / 4 * max (1 - a ^ 2) 0 := by positivity
    linarith [mul_assoc (r / 4) (1 - a ^ 2 - b ^ 2) (a ^ 2)]
  · have h1 : 1 - a ^ 2 - b ^ 2 ≤ max (1 - a ^ 2) 0 :=
      (by nlinarith [sq_nonneg b] : 1 - a ^ 2 - b ^ 2 ≤ 1 - a ^ 2).trans (le_max_left _ _)
    have h2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
    have := mul_le_mul h1 h2 (sq_nonneg a) hw0
    calc r / 4 * (1 - a ^ 2 - b ^ 2) * a ^ 2 = r / 4 * ((1 - a ^ 2 - b ^ 2) * a ^ 2) := by ring
      _ ≤ r / 4 * (max (1 - a ^ 2) 0 * 1) := by gcongr
      _ = r / 4 * max (1 - a ^ 2) 0 := by ring

/-- **The supersolution inequality for the defect.** Write `m = 1 + 2 C`, `w₊ = max (1 - |α|²) 0`
and `V = m (1 - |α|²) - r |β|²`. Adding `m` times the `α` inequality to `r` times the `β`
inequality bounds `(3 / 4) (m |∇_a α|² + r |∇β|²)` by `-Δ V / 2 = (m Δ|α|² + r Δ|β|²) / 2` up to
`O(r w₊ + 1)`; the cross terms are absorbed using the bounds `|α|² + |β|² ≤ 1 + C / r` and
`|β|² ≤ (C / r) w₊ + C / r²`. Here `a, b, p, q` stand for `|α|, |β|, |∇_a α|, |∇β|` and
`ga, gb` for `Δ|α|², Δ|β|²`. -/
private theorem defect_le_of_weitzenbock {ga gb : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hWα : -ga / 2 + p ^ 2 + r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 ≤ c * a * (q + a + b))
    (hWβ : -gb / 2 + q ^ 2 + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 ≤ c * b * (p + a + b))
    (hs : a ^ 2 + b ^ 2 ≤ 1 + C / r)
    (ht : b ^ 2 ≤ C / r * max (1 - a ^ 2) 0 + C / r ^ 2) :
    3 / 4 * ((1 + 2 * C) * p ^ 2 + r * q ^ 2) ≤ ((1 + 2 * C) * ga + r * gb) / 2 +
      ((1 + 2 * C) / 4 + c ^ 2 * C + 3 / 2 * c * C) * r * max (1 - a ^ 2) 0 +
      ((1 + 2 * C) ^ 2 * c ^ 2 * (1 + C) + 3 / 2 * (1 + 2 * C) * c * (1 + C) + c ^ 2 * C +
        c * (1 + 5 * C) / 2) := by
  set w := max (1 - a ^ 2) 0
  set m := 1 + 2 * C
  have hr0 : 0 < r := by linarith
  have hw0 : 0 ≤ w := le_max_right _ _
  have hm1 : 1 ≤ m := by linarith
  have hs' : a ^ 2 + b ^ 2 ≤ 1 + C := hs.trans (by linarith [div_le_self hC hr])
  have ha2 : a ^ 2 ≤ 1 + C := by nlinarith [sq_nonneg b]
  have hR2 := sq_mul_sq_le hr ht
  -- The potential term of the `α` inequality.
  have T1 := mul_le_mul_of_nonneg_left (potential_le (a := a) (b := b) hr0.le) (by linarith : 0 ≤ m)
  -- The cross terms `m c |α| |∇β|` and `r c |β| |∇_a α|`.
  have T2 : m * c * a * q ≤ r * q ^ 2 / 4 + m ^ 2 * c ^ 2 * (1 + C) := by
    -- Young's inequality `2 (r q / 2) (m c a) ≤ (r q / 2)² + (m c a)²`, divided by `r`.
    have h1 := two_mul_le_add_sq (r * q / 2) (m * c * a)
    have h2 : m ^ 2 * c ^ 2 * a ^ 2 ≤ r * (m ^ 2 * c ^ 2 * (1 + C)) :=
      calc m ^ 2 * c ^ 2 * a ^ 2 ≤ m ^ 2 * c ^ 2 * (1 + C) := by gcongr
        _ ≤ r * (m ^ 2 * c ^ 2 * (1 + C)) := le_mul_of_one_le_left (by positivity) hr
    refine le_of_mul_le_mul_left ?_ hr0
    linarith
  have T4 : r * c * b * p ≤ m * p ^ 2 / 4 + c ^ 2 * (C * r * w + C) := by
    -- Young's inequality `2 (m p / 2) (r c b) ≤ (m p / 2)² + (r c b)²`, divided by `m`.
    have h1 := two_mul_le_add_sq (m * p / 2) (r * c * b)
    have h2 : (r * c * b) ^ 2 ≤ m * (c ^ 2 * (C * r * w + C)) :=
      calc (r * c * b) ^ 2 = c ^ 2 * (r ^ 2 * b ^ 2) := by ring
        _ ≤ c ^ 2 * (C * r * w + C) := by gcongr
        _ ≤ m * (c ^ 2 * (C * r * w + C)) := le_mul_of_one_le_left (by positivity) hm1
    refine le_of_mul_le_mul_left ?_ (by linarith : 0 < m)
    linarith
  -- The zeroth-order terms.
  have T3 : m * c * (a * (a + b)) ≤ m * c * (3 / 2 * (1 + C)) := by
    have : a * (a + b) ≤ 3 / 2 * (1 + C) := by nlinarith [sq_nonneg (a - b)]
    have hmc : 0 ≤ m * c := by positivity
    exact mul_le_mul_of_nonneg_left this hmc
  have T5 : c * (r * b * (a + b)) ≤ c * (3 / 2 * C * r * w + (1 + 5 * C) / 2) := by
    have h1 : r * b * a ≤ (C * r * w + C + (1 + C)) / 2 := by nlinarith [sq_nonneg (r * b - a)]
    have h2 : r * b ^ 2 ≤ C * w + C := by
      have := mul_le_mul_of_nonneg_left ht hr0.le
      have e : r * (C / r * w + C / r ^ 2) = C * w + C / r := by field_simp
      linarith [div_le_self hC hr]
    have h3 : C * w ≤ C * r * w := by
      have := mul_le_mul_of_nonneg_left hr (mul_nonneg hC hw0)
      linarith
    have : r * b * (a + b) ≤ 3 / 2 * C * r * w + (1 + 5 * C) / 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hc
  -- Combine `m` times the `α` inequality with `r` times the `β` inequality.
  have hα := mul_le_mul_of_nonneg_left hWα (by linarith : (0 : ℝ) ≤ m)
  have hβ := mul_le_mul_of_nonneg_left hWβ hr0.le
  have hβpot : 0 ≤ r * (r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2) := by positivity
  linarith

end Defect

/-! ### The subsolution inequality for the gradient -/

section Gradient

variable {b p q P Q c C r : ℝ}

/-- The `α`-side terms of the differentiated inequalities, with `G = m |∇_a α|² + r |∇β|²`. -/
private theorem alpha_terms_le {m : ℝ} (hc : 0 ≤ c) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    m * (c * (r * (p ^ 2 + p * q + p) + (Q + p + q + 1) * p)) ≤
      r * Q ^ 2 / 2 + (c * (6 + m) + m * c ^ 2 / 2) * r * (m * p ^ 2 + r * q ^ 2) +
        m * c * r := by
  set G := m * p ^ 2 + r * q ^ 2
  have hr0 : 0 < r := by linarith
  have hmp : m * p ^ 2 ≤ G := by have := mul_nonneg hr0.le (sq_nonneg q); linarith
  have hrq : r * q ^ 2 ≤ G := by have := mul_nonneg (by linarith : 0 ≤ m) (sq_nonneg p); linarith
  have hG : 0 ≤ G := by positivity
  have hGr : G ≤ r * G := le_mul_of_one_le_left hG hr
  have hq2 : q ^ 2 ≤ r * q ^ 2 := le_mul_of_one_le_left (sq_nonneg q) hr
  have hpq := two_mul_le_add_sq p q
  have hp1 := two_mul_le_add_sq p 1
  -- `m c Q |∇_a α| ≤ r Q² / 2 + m² c² |∇_a α|² / (2 r)`.
  have hQ : m * c * (Q * p) ≤ r * Q ^ 2 / 2 + m * c ^ 2 / 2 * r * G := by
    -- Young's inequality `2 (r Q) (m c p) ≤ (r Q)² + (m c p)²`, divided by `2 r`.
    have h1 := two_mul_le_add_sq (r * Q) (m * c * p)
    have h2 : (m * c * p) ^ 2 ≤ m * c ^ 2 * (r * r * G) := by
      have hmc : 0 ≤ m * c ^ 2 := by positivity
      have hr2 : 1 ≤ r * r := one_le_mul_of_one_le_of_one_le hr hr
      calc (m * c * p) ^ 2 = m * c ^ 2 * (m * p ^ 2) := by ring
        _ ≤ m * c ^ 2 * G := mul_le_mul_of_nonneg_left hmp hmc
        _ ≤ m * c ^ 2 * (r * r * G) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hG hr2) hmc
    refine le_of_mul_le_mul_left ?_ hr0
    linarith
  -- The remaining terms are bounded by `G`, `r G` and `r`.
  have hrest : m * (r * (p ^ 2 + p * q + p) + (p + q + 1) * p) ≤
      (6 + m) * r * G + m * r := by
    have hm0 : 0 ≤ m := by linarith
    have t1 : m * (p * q) ≤ G / 2 + m / 2 * G := by
      have := mul_le_mul_of_nonneg_left hpq hm0
      have := mul_le_mul_of_nonneg_left hq2 hm0
      have := mul_le_mul_of_nonneg_left hrq hm0
      nlinarith
    have t2 : m * p ≤ m / 2 + G / 2 := by
      have := mul_le_mul_of_nonneg_left hp1 hm0
      nlinarith
    have t1r := mul_le_mul_of_nonneg_left t1 hr0.le
    have t2r := mul_le_mul_of_nonneg_left t2 hr0.le
    have hmr := mul_le_mul_of_nonneg_left hmp hr0.le
    have hmG : m * G ≤ m * (r * G) := mul_le_mul_of_nonneg_left hGr hm0
    have hm1r : m ≤ m * r := le_mul_of_one_le_right hm0 hr
    nlinarith
  have hcr := mul_le_mul_of_nonneg_left hrest hc
  nlinarith

/-- The `β`-side terms of the differentiated inequalities, with `G = m |∇_a α|² + r |∇β|²`, given
`r² |β|² ≤ 2 C r`. -/
private theorem beta_terms_le {m : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hb : r ^ 2 * b ^ 2 ≤ 2 * C * r) :
    r * (c * (r * (q ^ 2 + b * (p + q + 1) * q) + (P + p + q + 1) * q)) ≤
      m * P ^ 2 / 2 + (c * (3 * C + 5) + c ^ 2 / 2) * r * (m * p ^ 2 + r * q ^ 2) + c * r := by
  set G := m * p ^ 2 + r * q ^ 2
  have hr0 : 0 < r := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hmp : m * p ^ 2 ≤ G := by have := mul_nonneg hr0.le (sq_nonneg q); linarith
  have hrq : r * q ^ 2 ≤ G := by have := mul_nonneg hm0 (sq_nonneg p); linarith
  have hG : 0 ≤ G := by positivity
  have hGr : G ≤ r * G := le_mul_of_one_le_left hG hr
  have hp2 : r * p ^ 2 ≤ r * G :=
    mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left (sq_nonneg p) hm).trans hmp) hr0.le
  -- `r³ |β|² |∇β|² ≤ 2 C r G`.
  have hb3 : r ^ 3 * b ^ 2 * q ^ 2 ≤ 2 * C * r * G := by
    have e : r ^ 3 * b ^ 2 * q ^ 2 = (r ^ 2 * b ^ 2) * (r * q ^ 2) := by ring
    rw [e]
    calc (r ^ 2 * b ^ 2) * (r * q ^ 2) ≤ (2 * C * r) * (r * q ^ 2) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ 2 * C * r * G := mul_le_mul_of_nonneg_left hrq (by positivity)
  -- The three terms carrying `|β|`, by Young's inequality.
  have t1 : r ^ 2 * b * p * q ≤ (C + 1 / 2) * r * G := by
    have := two_mul_le_add_sq (r * b * q) p
    have := mul_le_mul_of_nonneg_left this hr0.le
    nlinarith
  have t2 : r ^ 2 * b * q ^ 2 ≤ (C + 1 / 2) * r * G := by
    have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (r * b) 1)
      (mul_nonneg hr0.le (sq_nonneg q))
    nlinarith
  have t3 : r ^ 2 * b * q ≤ C * r * G + r / 2 := by
    have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq (r * b * q) 1) hr0.le
    nlinarith
  -- `r c P |∇β| ≤ m P² / 2 + r² c² |∇β|² / (2 m)`.
  have t4 : r * c * (P * q) ≤ m * P ^ 2 / 2 + c ^ 2 / 2 * r * G := by
    -- Young's inequality `2 (m P) (r c q) ≤ (m P)² + (r c q)²`, divided by `2 m`.
    have h1 := two_mul_le_add_sq (m * P) (r * c * q)
    have h2 : (r * c * q) ^ 2 ≤ m * (c ^ 2 * r * G) := by
      have hcr : 0 ≤ c ^ 2 * r := by positivity
      calc (r * c * q) ^ 2 = c ^ 2 * r * (r * q ^ 2) := by ring
        _ ≤ c ^ 2 * r * G := mul_le_mul_of_nonneg_left hrq hcr
        _ ≤ m * (c ^ 2 * r * G) := le_mul_of_one_le_left (by positivity) hm
    refine le_of_mul_le_mul_left ?_ (by linarith : 0 < m)
    linarith
  -- The remaining terms.
  have t5 : r * (p * q + q ^ 2 + q) ≤ 5 / 2 * r * G + r / 2 := by
    have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq p q) hr0.le
    have := mul_le_mul_of_nonneg_left (two_mul_le_add_sq q 1) hr0.le
    nlinarith
  have hcr := mul_le_mul_of_nonneg_left hrq (mul_nonneg hc hr0.le)
  have e : r * (c * (r * (q ^ 2 + b * (p + q + 1) * q) + (P + p + q + 1) * q)) =
      c * r * (r * q ^ 2) + c * (r ^ 2 * b * p * q) + c * (r ^ 2 * b * q ^ 2) +
        c * (r ^ 2 * b * q) + r * c * (P * q) + c * (r * (p * q + q ^ 2 + q)) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left t1 hc
  have := mul_le_mul_of_nonneg_left t2 hc
  have := mul_le_mul_of_nonneg_left t3 hc
  have := mul_le_mul_of_nonneg_left t5 hc
  nlinarith

/-- **The subsolution inequality for the gradient.** Adding `m = 1 + 2 C` times the differentiated
`α` inequality to `r` times the differentiated `β` inequality bounds `-Δ G / 2` by `O(r G + r)`
for `G = m |∇_a α|² + r |∇β|²`, after the second derivatives are absorbed. Here `p, q, P, Q`
stand for `|∇_a α|, |∇β|, |∇²α|, |∇²β|` and `gp, gq` for `Δ|∇_a α|², Δ|∇β|²`. -/
private theorem gradient_le_of_weitzenbock {gp gq : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C) (hr : 1 ≤ r)
    (hDα : -gp / 2 + P ^ 2 ≤ c * (r * (p ^ 2 + p * q + p) + (Q + p + q + 1) * p))
    (hDβ : -gq / 2 + Q ^ 2 ≤ c * (r * (q ^ 2 + b * (p + q + 1) * q) + (P + p + q + 1) * q))
    (hb : r ^ 2 * b ^ 2 ≤ 2 * C * r) :
    -((1 + 2 * C) * gp + r * gq) / 2 ≤
      (c * (12 + 5 * C) + (1 + C) * c ^ 2) * r * ((1 + 2 * C) * p ^ 2 + r * q ^ 2) +
        c * (2 + 2 * C) * r := by
  have hm : 1 ≤ 1 + 2 * C := by linarith
  have h1 := alpha_terms_le (p := p) (q := q) (Q := Q) hc hr hm
  have h2 := beta_terms_le (p := p) (q := q) (P := P) hc hC hr hm hb
  have hα := mul_le_mul_of_nonneg_left hDα (by linarith : (0 : ℝ) ≤ 1 + 2 * C)
  have hβ := mul_le_mul_of_nonneg_left hDβ (by linarith : (0 : ℝ) ≤ r)
  have hP : 0 ≤ (1 + 2 * C) * P ^ 2 := by positivity
  have hQ : 0 ≤ r * Q ^ 2 := mul_nonneg (by linarith) (sq_nonneg Q)
  linarith

end Gradient

/-! ### The maximum principle argument -/

section Comparison

variable {a b G w gG gV c C r K A B K₁ K₂ : ℝ}

/-- At a maximum of `G - K r V`, the subsolution inequality `-Δ G / 2 ≤ A r G + B r` and the
supersolution inequality `(3 / 4) G ≤ -Δ V / 2 + K₁ r w + K₂` give `G ≤ 2 K₁ r w + 2 B + 2 K₂`
once `K ≥ max 1 (4 A)`. Here `gG` and `gV` stand for `Δ G` and `Δ V`. -/
private theorem le_of_laplacian_sub_nonpos (hr : 1 ≤ r) (hG : 0 ≤ G) (hK : 1 ≤ K)
    (hKA : 4 * A ≤ K) (hB : 0 ≤ B) (hsub : -gG / 2 ≤ A * r * G + B * r)
    (hsup : 3 / 4 * G ≤ -gV / 2 + K₁ * r * w + K₂) (hmax : gG - K * r * gV ≤ 0) :
    G ≤ 2 * K₁ * r * w + 2 * B + 2 * K₂ := by
  have hr0 : 0 < r := by linarith
  -- Multiplying the supersolution inequality by `K r` and using `Δ (G - K r V) ≤ 0`.
  have h1 := mul_le_mul_of_nonneg_left hsup (by positivity : 0 ≤ K * r)
  have h2 : r * (K / 2 * G) ≤ r * (B + K * K₁ * r * w + K * K₂) := by
    have : K / 2 * G ≤ (3 / 4 * K - A) * G := mul_le_mul_of_nonneg_right (by linarith) hG
    nlinarith
  have h3 : K / 2 * G ≤ B + K * K₁ * r * w + K * K₂ := le_of_mul_le_mul_left h2 hr0
  have h4 : B ≤ K * B := le_mul_of_one_le_left hB hK
  have h5 : K * G ≤ K * (2 * K₁ * r * w + 2 * B + 2 * K₂) := by nlinarith
  exact le_of_mul_le_mul_left h5 (by linarith)

/-- The defect side of the comparison function: with `m = 1 + 2 C`,
`-K r (m (1 - |α|²) - r |β|²) ≤ -K (1 + C) r w₊ + K C (m + 1)`, from `|α|² ≤ 1 + C / r` and
`r² |β|² ≤ C r w₊ + C`. -/
private theorem neg_mul_defect_le (hr : 1 ≤ r) (hK : 0 ≤ K)
    (hs : a ^ 2 + b ^ 2 ≤ 1 + C / r) (hR2 : r ^ 2 * b ^ 2 ≤ C * r * max (1 - a ^ 2) 0 + C) :
    -(K * r * ((1 + 2 * C) * (1 - a ^ 2) - r * b ^ 2)) ≤
      -(K * (1 + C) * r * max (1 - a ^ 2) 0) + K * C * (2 + 2 * C) := by
  have hr0 : 0 < r := by linarith
  -- `-r (1 - |α|²) ≤ -r w₊ + C`.
  have hw : -(r * (1 - a ^ 2)) ≤ -(r * max (1 - a ^ 2) 0) + C := by
    rcases le_total 0 (1 - a ^ 2) with h | h
    · rw [max_eq_left h]; linarith [show (0 : ℝ) ≤ C by
        have := mul_nonneg (sq_nonneg r) (sq_nonneg b)
        nlinarith [mul_nonneg hr0.le (le_max_right (1 - a ^ 2) 0)]]
    · rw [max_eq_right h]
      have : r * (a ^ 2 - 1) ≤ C := by
        have := mul_le_mul_of_nonneg_left (show a ^ 2 - 1 ≤ C / r by nlinarith [sq_nonneg b])
          hr0.le
        rwa [mul_div_cancel₀ _ hr0.ne'] at this
      linarith
  have hC : 0 ≤ C := by
    have := mul_nonneg (sq_nonneg r) (sq_nonneg b)
    nlinarith [mul_nonneg hr0.le (le_max_right (1 - a ^ 2) 0)]
  have h1 := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ K * (1 + 2 * C))
  have h2 := mul_le_mul_of_nonneg_left hR2 hK
  nlinarith

end Comparison

/-! ### The constants -/

section Constants

variable {c C : ℝ}

/-- The comparison constant `K = 60 (1 + c + C)³` dominates `4 A` for the subsolution constant
`A = c (12 + 5 C) + (1 + C) c²`. -/
private theorem four_mul_le_comparisonConst (hc : 0 ≤ c) (hC : 0 ≤ C) :
    4 * (c * (12 + 5 * C) + (1 + C) * c ^ 2) ≤ 60 * (1 + c + C) ^ 3 := by
  have : 0 ≤ 60 * (1 + c + C) ^ 3 - 4 * (c * (12 + 5 * C) + (1 + C) * c ^ 2) := by
    ring_nf; positivity
  linarith

/-- The comparison constant `K = 60 (1 + c + C)³` dominates twice the defect coefficient of the
supersolution inequality. -/
private theorem two_mul_le_comparisonConst (hc : 0 ≤ c) (hC : 0 ≤ C) :
    2 * ((1 + 2 * C) / 4 + c ^ 2 * C + 3 / 2 * c * C) ≤ 60 * (1 + c + C) ^ 3 := by
  have : 0 ≤ 60 * (1 + c + C) ^ 3 - 2 * ((1 + 2 * C) / 4 + c ^ 2 * C + 3 / 2 * c * C) := by
    ring_nf; positivity
  linarith

/-- The final defect coefficient `K (1 + 2 C)` is at most `150 (1 + c + C)⁵`. -/
private theorem comparisonConst_mul_le (hc : 0 ≤ c) (hC : 0 ≤ C) :
    60 * (1 + c + C) ^ 3 * (1 + 2 * C) ≤ 150 * (1 + c + C) ^ 5 := by
  have : 0 ≤ 150 * (1 + c + C) ^ 5 - 60 * (1 + c + C) ^ 3 * (1 + 2 * C) := by
    ring_nf; positivity
  linarith

/-- The final additive constant is at most `150 (1 + c + C)⁵`. -/
private theorem additiveConst_le (hc : 0 ≤ c) (hC : 0 ≤ C) :
    2 * (c * (2 + 2 * C)) + 2 * ((1 + 2 * C) ^ 2 * c ^ 2 * (1 + C) +
      3 / 2 * (1 + 2 * C) * c * (1 + C) + c ^ 2 * C + c * (1 + 5 * C) / 2) +
        60 * (1 + c + C) ^ 3 * C * (2 + 2 * C) ≤ 150 * (1 + c + C) ^ 5 := by
  have : 0 ≤ 150 * (1 + c + C) ^ 5 - (2 * (c * (2 + 2 * C)) + 2 * ((1 + 2 * C) ^ 2 * c ^ 2 *
      (1 + C) + 3 / 2 * (1 + 2 * C) * c * (1 + C) + c ^ 2 * C + c * (1 + 5 * C) / 2) +
        60 * (1 + c + C) ^ 3 * C * (2 + 2 * C)) := by
    ring_nf; positivity
  linarith

end Constants

/-! ### The gradient bound on a closed manifold -/

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] [CompactSpace M]
  {A B F₁ F₂ S₁ S₂ : M → Type*} [∀ x, NormedAddCommGroup (A x)] [∀ x, NormedAddCommGroup (B x)]
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedAddCommGroup (F₂ x)]
  [∀ x, NormedAddCommGroup (S₁ x)] [∀ x, NormedAddCommGroup (S₂ x)]
  {α : (x : M) → A x} {β : (x : M) → B x} {Dα : (x : M) → F₁ x} {Dβ : (x : M) → F₂ x}
  {D2α : (x : M) → S₁ x} {D2β : (x : M) → S₂ x} {c C r : ℝ}

/-- **Taubes's gradient bound `|∇_a α|² + r |∇β|² ≤ C' r w₊ + C'`.** On a closed Riemannian
manifold, suppose that for `r ≥ 1` the projected Weitzenböck inequalities for `|α|²` and `|β|²`
and their once differentiated versions for `|∇_a α|²` and `|∇β|²` hold everywhere with constant
`c ≥ 0`, and that `|α|² + |β|² ≤ 1 + C / r` and `|β|² ≤ (C / r) w₊ + C / r²`, where
`w₊ = max (1 - |α|²) 0`. Then everywhere

`|∇_a α|² + r |∇β|² ≤ C' r w₊ + C'`,  `C' = 150 (1 + c + C)⁵`.

The constant depends only on `c` and `C`, not on `r`, the manifold or the solution. -/
theorem norm_sq_add_mul_norm_sq_le (hc : 0 ≤ c) (hr : 1 ≤ r)
    (hα₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖α x‖ ^ 2) (hβ₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖β x‖ ^ 2)
    (hDα₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖Dα x‖ ^ 2)
    (hDβ₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖Dβ x‖ ^ 2)
    (hWα : ∀ x, -laplaceBeltrami I (fun x ↦ ‖α x‖ ^ 2) x / 2 + ‖Dα x‖ ^ 2 +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖α x‖ ^ 2 ≤ c * ‖α x‖ * (‖Dβ x‖ + ‖α x‖ + ‖β x‖))
    (hWβ : ∀ x, -laplaceBeltrami I (fun x ↦ ‖β x‖ ^ 2) x / 2 + ‖Dβ x‖ ^ 2 +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤ c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖))
    (hDα : ∀ x, -laplaceBeltrami I (fun x ↦ ‖Dα x‖ ^ 2) x / 2 + ‖D2α x‖ ^ 2 ≤
      c * (r * (‖Dα x‖ ^ 2 + ‖Dα x‖ * ‖Dβ x‖ + ‖Dα x‖) +
        (‖D2β x‖ + ‖Dα x‖ + ‖Dβ x‖ + 1) * ‖Dα x‖))
    (hDβ : ∀ x, -laplaceBeltrami I (fun x ↦ ‖Dβ x‖ ^ 2) x / 2 + ‖D2β x‖ ^ 2 ≤
      c * (r * (‖Dβ x‖ ^ 2 + ‖β x‖ * (‖Dα x‖ + ‖Dβ x‖ + 1) * ‖Dβ x‖) +
        (‖D2α x‖ + ‖Dα x‖ + ‖Dβ x‖ + 1) * ‖Dβ x‖))
    (hs : ∀ x, ‖α x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + C / r)
    (ht : ∀ x, ‖β x‖ ^ 2 ≤ C / r * max (1 - ‖α x‖ ^ 2) 0 + C / r ^ 2) (x : M) :
    ‖Dα x‖ ^ 2 + r * ‖Dβ x‖ ^ 2 ≤
      150 * (1 + c + C) ^ 5 * r * max (1 - ‖α x‖ ^ 2) 0 + 150 * (1 + c + C) ^ 5 := by
  have hr0 : 0 < r := by linarith
  -- The bound on `|β|²` forces `C ≥ 0`.
  have hC : 0 ≤ C := by
    by_contra h
    have h1 : C / r * max (1 - ‖α x‖ ^ 2) 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (by linarith) hr0.le)
        (le_max_right _ _)
    have h2 : C / r ^ 2 < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
    linarith [ht x, sq_nonneg ‖β x‖]
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 1 + 2 * C := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 60 * (1 + c + C) ^ 3 := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by linarith
  have hK1 : 1 ≤ K := by
    have : 1 ≤ (1 + c + C) ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hKA := four_mul_le_comparisonConst hc hC
  have hKK := two_mul_le_comparisonConst hc hC
  have hKm := comparisonConst_mul_le hc hC
  have hK₃ := additiveConst_le hc hC
  rw [← hK] at hKA hKK hKm hK₃
  rw [← hm] at hKm hKK hK₃
  -- The comparison function `f = G - K r V + K r m`, with `G = m |∇_a α|² + r |∇β|²` and
  -- `V = m (1 - |α|²) - r |β|²`; the constant `K r m` does not affect its Laplacian.
  have h₁ : ContMDiff I 𝓘(ℝ) 2 (m • fun x ↦ ‖Dα x‖ ^ 2) := contMDiff_const.mul hDα₂
  have h₂ : ContMDiff I 𝓘(ℝ) 2 (r • fun x ↦ ‖Dβ x‖ ^ 2) := contMDiff_const.mul hDβ₂
  have h₃ : ContMDiff I 𝓘(ℝ) 2 ((K * r * m) • fun x ↦ ‖α x‖ ^ 2) := contMDiff_const.mul hα₂
  have h₄ : ContMDiff I 𝓘(ℝ) 2 ((K * r * r) • fun x ↦ ‖β x‖ ^ 2) := contMDiff_const.mul hβ₂
  set f : M → ℝ := m • (fun x ↦ ‖Dα x‖ ^ 2) + r • (fun x ↦ ‖Dβ x‖ ^ 2) +
    (K * r * m) • (fun x ↦ ‖α x‖ ^ 2) + (K * r * r) • (fun x ↦ ‖β x‖ ^ 2) with hf
  have hf₂ : ContMDiff I 𝓘(ℝ) 2 f := ((h₁.add h₂).add h₃).add h₄
  have hfx (y : M) : f y = m * ‖Dα y‖ ^ 2 + r * ‖Dβ y‖ ^ 2 + K * r * m * ‖α y‖ ^ 2 +
      K * r * r * ‖β y‖ ^ 2 := by
    simp [hf]
  obtain ⟨x₀, -, hx₀⟩ :=
    isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩ hf₂.continuous.continuousOn
  -- At the maximum `x₀` the Laplacian of `f` is nonpositive.
  have hlap : laplaceBeltrami I f x₀ ≤ 0 :=
    laplaceBeltrami_nonpos_of_isLocalMax hf₂.contMDiffAt (hx₀.isLocalMax Filter.univ_mem)
  rw [hf, laplaceBeltrami_add I ((h₁.add h₂).add h₃) h₄, laplaceBeltrami_add I (h₁.add h₂) h₃,
    laplaceBeltrami_add I h₁ h₂, laplaceBeltrami_smul I _ hDα₂, laplaceBeltrami_smul I _ hDβ₂,
    laplaceBeltrami_smul I _ hα₂, laplaceBeltrami_smul I _ hβ₂] at hlap
  -- The sub- and supersolution inequalities at `x₀`.
  have hR2 := sq_mul_sq_le hr (ht x₀)
  have hb : r ^ 2 * ‖β x₀‖ ^ 2 ≤ 2 * C * r := by
    have hw1 : max (1 - ‖α x₀‖ ^ 2) 0 ≤ 1 :=
      max_le (by linarith [sq_nonneg ‖α x₀‖]) zero_le_one
    have : C * r * max (1 - ‖α x₀‖ ^ 2) 0 ≤ C * r :=
      mul_le_of_le_one_right (by positivity) hw1
    have : C * 1 ≤ C * r := mul_le_mul_of_nonneg_left hr hC
    linarith
  have hsub := gradient_le_of_weitzenbock hc hC hr (hDα x₀) (hDβ x₀) hb
  have hsup := defect_le_of_weitzenbock hc hC hr (hWα x₀) (hWβ x₀) (hs x₀) (ht x₀)
  have hdef := neg_mul_defect_le hr (by linarith) (hs x₀) hR2 (K := K)
  rw [← hm] at hsub hsup hdef
  have hG : 0 ≤ m * ‖Dα x₀‖ ^ 2 + r * ‖Dβ x₀‖ ^ 2 := by positivity
  have hmax := le_of_laplacian_sub_nonpos (gV := -(m * laplaceBeltrami I (fun x ↦ ‖α x‖ ^ 2) x₀ +
      r * laplaceBeltrami I (fun x ↦ ‖β x‖ ^ 2) x₀)) (w := max (1 - ‖α x₀‖ ^ 2) 0)
    (K₁ := m / 4 + c ^ 2 * C + 3 / 2 * c * C)
    (K₂ := m ^ 2 * c ^ 2 * (1 + C) + 3 / 2 * m * c * (1 + C) + c ^ 2 * C + c * (1 + 5 * C) / 2)
    hr hG hK1 hKA (by positivity) hsub (by linarith) (by linarith)
  -- Hence `f - K r m ≤ K₃` at `x₀`, and so everywhere.
  have hrw : 0 ≤ r * max (1 - ‖α x₀‖ ^ 2) 0 := mul_nonneg hr0.le (le_max_right _ _)
  have hKK' := mul_le_mul_of_nonneg_right (hKK.trans (le_mul_of_one_le_right (by linarith)
    (by linarith : (1 : ℝ) ≤ 1 + C))) hrw
  have hfx' : f x ≤ f x₀ := hx₀ (Set.mem_univ x)
  rw [hfx, hfx] at hfx'
  -- At `x`, `V ≤ m w₊`.
  have hV : m * (1 - ‖α x‖ ^ 2) ≤ m * max (1 - ‖α x‖ ^ 2) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  have hKV := mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ K * r)
  have hrw' : 0 ≤ r * max (1 - ‖α x‖ ^ 2) 0 := mul_nonneg hr0.le (le_max_right _ _)
  have hKmw := mul_le_mul_of_nonneg_right hKm hrw'
  have hDα1 : ‖Dα x‖ ^ 2 ≤ m * ‖Dα x‖ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hm1
  have hβ0 : 0 ≤ K * r * r * ‖β x‖ ^ 2 := by positivity
  linarith

end TauCeti.SeibergWitten
