/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Pointwise bounds on large-parameter Seiberg–Witten solutions from the maximum principle

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `ψ = α u₀ + β`, where `α` is a section of the
twisting line and `β` the component orthogonal to the canonical spinor `u₀`. The two components
satisfy projected Weitzenböck equations

`∇*∇α = (r / 4) (1 - |α|² - |β|²) α + 𝔞`,  `∇*∇β + (r / 4) (1 + |α|² + |β|²) β = 𝔟`,

whose errors are bounded by `|𝔞| ≤ c (|∇β| + |α| + |β|)` and `|𝔟| ≤ c (|∇_a α| + |α| + |β|)`,
with a constant `c` independent of `r` that absorbs the torsion of `J`, the curvature of the
canonical connection and the forcing. Pairing with `α` and `β` and writing
`Δ = div ∘ grad` (`TauCeti.Manifold.laplaceBeltrami`), so that `⟪∇*∇α, α⟫ = |∇_a α|² - Δ|α|² / 2`,
gives the scalar inequalities

`-Δ|α|² / 2 + |∇_a α|² + (r / 4) (|α|² + |β|² - 1) |α|² ≤ c |α| (|∇β| + |α| + |β|)`,
`-Δ|β|² / 2 + |∇β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)`.

This file derives from them, by the maximum principle on a closed manifold, two of Taubes's
coarse pointwise bounds, with constants depending only on `c`:

* `|α|² + |β|² ≤ 1 + (c² + 8 c) / r` everywhere
  (`TauCeti.SeibergWitten.norm_sq_add_norm_sq_le_one_add_div`). At a maximum of `|α|² + |β|²` the
  Laplacian is nonpositive, and the sum of the two inequalities becomes
  `(r / 4) (|ψ|² - 1) |ψ|² ≤ (c² / 4 + 2 c) |ψ|²` once the derivative terms of the right-hand
  side are absorbed into `|∇_a α|² + |∇β|²`.
* `|β|² ≤ (4 c² / r) (1 - |α|²) + K / r²` everywhere, for `r ≥ max 1 (max (32 c) (c² + 8 c))`
  and `K = 128 c² + 128 c³ + 4 c⁴ + 64 c⁶`
  (`TauCeti.SeibergWitten.norm_sq_le_div_mul_one_sub_add_div_sq`). This is Taubes's comparison
  argument: one evaluates the inequalities at a maximum of `|β|² + (κ / r) |α|²` with
  `κ = 4 c²`. The cross term `c |β| |∇_a α|` of the `β` inequality is
  absorbed by the term `(κ / r) |∇_a α|²` that the `α` inequality contributes, which is what
  forces `κ ≥ 4 c²`. The defect `1 - |α|²` appears with the same coefficient on both sides and
  cancels, so the bound holds with the error `O(r⁻²)` rather than `O(r⁻¹)`. In particular
  `|β|² ≤ (K / r) w₊ + K / r²` with `w₊ = max (1 - |α|²) 0`
  (`TauCeti.SeibergWitten.norm_sq_le_div_mul_max_add_div_sq`), the form in which the coarse
  bounds of `TauCeti.Analysis.PDE.SeibergWitten.CoarseBounds`, such as
  `TauCeti.SeibergWitten.integral_norm_sq_le_div_sq`, take it as a hypothesis.

The same statements hold at a local maximum on any boundaryless Riemannian manifold
(`TauCeti.SeibergWitten.norm_sq_add_norm_sq_le_one_add_div_of_isLocalMax`,
`TauCeti.SeibergWitten.norm_sq_le_div_mul_one_sub_add_div_sq_of_isLocalMax`). The sections `α`,
`β` and their covariant derivatives `∇_a α`, `∇β` are arbitrary families of elements of normed
groups over the manifold satisfying the displayed inequalities; only the squared norms `|α|²` and
`|β|²` need to be `C²`, and for the local statements only at the maximum. Deriving the scalar
inequalities from the Seiberg–Witten equations is not done here.

## Main results

* `TauCeti.SeibergWitten.norm_sq_add_norm_sq_le_one_add_div`: `|α|² + |β|² ≤ 1 + (c² + 8 c) / r`.
* `TauCeti.SeibergWitten.norm_sq_le_div_mul_one_sub_add_div_sq`:
  `|β|² ≤ (4 c² / r) (1 - |α|²) + K / r²`.
* `TauCeti.SeibergWitten.norm_sq_le_div_mul_max_add_div_sq`:
  `|β|² ≤ (C / r) max (1 - |α|²) 0 + C / r²`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
-/

public section

open scoped Manifold

namespace TauCeti.SeibergWitten

/-! ### The pointwise algebra at a maximum -/

/-- At a point where the Laplacian of `|α|² + |β|²` is nonpositive, the sum of the projected
Weitzenböck inequalities gives `|α|² + |β|² ≤ 1 + (c² + 8 c) / r`. Here `a`, `b`, `da`, `db`
stand for `|α|`, `|β|`, `|∇_a α|`, `|∇β|`, and `ga`, `gb` for `Δ|α|²`, `Δ|β|²`. -/
private theorem sq_add_sq_le_of_weitzenbock {a b da db ga gb c r : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (hα : -ga / 2 + da ^ 2 + r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 ≤ c * a * (db + a + b))
    (hβ : -gb / 2 + db ^ 2 + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 ≤ c * b * (da + a + b))
    (hg : ga + gb ≤ 0) :
    a ^ 2 + b ^ 2 ≤ 1 + (c ^ 2 + 8 * c) / r := by
  set s := a ^ 2 + b ^ 2
  -- Absorb the derivative cross terms and bound the remaining ones by `2 c s`.
  have hda : c * b * da ≤ da ^ 2 + c ^ 2 * b ^ 2 / 4 := by nlinarith [sq_nonneg (da - c * b / 2)]
  have hdb : c * a * db ≤ db ^ 2 + c ^ 2 * a ^ 2 / 4 := by nlinarith [sq_nonneg (db - c * a / 2)]
  have hab : c * (a * (a + b) + b * (a + b)) ≤ 2 * c * s := by
    nlinarith [mul_nonneg hc (sq_nonneg (a - b))]
  -- Hence `(r / 4) (s - 1) s ≤ (c² / 4 + 2 c) s`.
  have hkey : r * (s - 1) * s ≤ (c ^ 2 + 8 * c) * s := by
    have hpot : r / 4 * (s - 1) * s ≤ r / 4 * (s - 1) * a ^ 2 + r / 4 * (s + 1) * b ^ 2 := by
      nlinarith [mul_nonneg hr.le (sq_nonneg b)]
    nlinarith
  rcases (show 0 ≤ s by positivity).eq_or_lt with hs0 | hs0
  · rw [← hs0]
    linarith [show 0 ≤ (c ^ 2 + 8 * c) / r by positivity]
  · -- If `s > 0`, divide by `s`.
    have hrs : r * (s - 1) ≤ c ^ 2 + 8 * c := le_of_mul_le_mul_right (by linarith) hs0
    have : s - 1 ≤ (c ^ 2 + 8 * c) / r := by rw [le_div_iff₀ hr]; linarith
    linarith

/-- The comparison step of the `β` bound. With `k = 4 c² / r`, add `k` times the `α` inequality
to the `β` inequality at a point where `Δ|β|² + k Δ|α|² ≤ 0`, absorb the derivative cross terms,
and rewrite the potential through `v = |β|² - k (1 - |α|²)`: the defect `1 - |α|²` enters on both
sides with the same coefficient and cancels. -/
private theorem comparison_of_weitzenbock {a b da db ga gb c r k : ℝ} (hr : 0 < r)
    (hr32 : 32 * c ≤ r) (hk_def : k = 4 * c ^ 2 / r)
    (hα : -ga / 2 + da ^ 2 + r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 ≤ c * a * (db + a + b))
    (hβ : -gb / 2 + db ^ 2 + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 ≤ c * b * (da + a + b))
    (hg : gb + k * ga ≤ 0) :
    r / 8 * (b ^ 2 - k * (1 - a ^ 2)) + r / 4 * a ^ 2 * (b ^ 2 - k * (1 - a ^ 2)) ≤
      8 * c ^ 2 / r * a ^ 2 + (k * c) ^ 2 * a ^ 2 / 4 + k * c * (a ^ 2 + a * b) -
        c ^ 2 / 2 * (1 - a ^ 2) := by
  have hk : 0 ≤ k := by rw [hk_def]; positivity
  have hkr : k * r = 4 * c ^ 2 := by rw [hk_def]; field_simp
  -- Add `k` times the `α` inequality to the `β` inequality; the Laplacian terms are `≥ 0`.
  have h1 : db ^ 2 + k * da ^ 2 + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 +
      c ^ 2 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 ≤
        c * b * da + c * b * a + c * b * b + k * c * a * db + k * c * (a ^ 2 + a * b) := by
    have hkα := mul_le_mul_of_nonneg_left hα hk
    have e : k * (-ga / 2 + da ^ 2 + r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2) =
        k * (-ga / 2) + k * da ^ 2 + c ^ 2 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 := by
      linear_combination (a ^ 2 + b ^ 2 - 1) * a ^ 2 / 4 * hkr
    linarith
  -- Absorb the cross terms.
  have h2 : c * b * da ≤ k * da ^ 2 + r / 16 * b ^ 2 := by
    have e : k * da ^ 2 + r / 16 * b ^ 2 - c * b * da = (8 * c * da - r * b) ^ 2 / (16 * r) := by
      rw [hk_def]; field_simp; ring
    have : 0 ≤ (8 * c * da - r * b) ^ 2 / (16 * r) := by positivity
    linarith
  have h3 : c * b * a ≤ r / 32 * b ^ 2 + 8 * c ^ 2 / r * a ^ 2 := by
    have e : r / 32 * b ^ 2 + 8 * c ^ 2 / r * a ^ 2 - c * b * a =
        (r * b - 16 * c * a) ^ 2 / (32 * r) := by
      field_simp; ring
    have : 0 ≤ (r * b - 16 * c * a) ^ 2 / (32 * r) := by positivity
    linarith
  have h4 : c * b * b ≤ r / 32 * b ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hr32 (sq_nonneg b)]
  have h5 : k * c * a * db ≤ db ^ 2 + (k * c) ^ 2 * a ^ 2 / 4 := by
    nlinarith [sq_nonneg (db - k * c * a / 2)]
  -- Rewrite the potential terms through `v = |β|² - k (1 - |α|²)`.
  have e : r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 + c ^ 2 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 -
      r / 8 * b ^ 2 = r / 8 * (b ^ 2 - k * (1 - a ^ 2)) + c ^ 2 / 2 * (1 - a ^ 2) +
        r / 4 * a ^ 2 * (b ^ 2 - k * (1 - a ^ 2)) + r / 4 * b ^ 4 + c ^ 2 * a ^ 2 * b ^ 2 := by
    linear_combination ((1 - a ^ 2) * (1 / 8 + a ^ 2 / 4)) * hkr
  have : 0 ≤ r / 4 * b ^ 4 := by positivity
  have : 0 ≤ c ^ 2 * a ^ 2 * b ^ 2 := by positivity
  linarith

/-- The right-hand side of `comparison_of_weitzenbock` is `O(1 / r)` once `|α|² + |β|² ≤ 2` and
`|α|² ≤ 1 + (c² + 8 c) / r`. -/
private theorem comparison_rhs_le {a b c r k : ℝ} (hc : 0 ≤ c) (hr1 : 1 ≤ r)
    (hk_def : k = 4 * c ^ 2 / r) (ha2 : a ^ 2 ≤ 2) (hab1 : a * b ≤ 1)
    (hw : -(1 - a ^ 2) ≤ (c ^ 2 + 8 * c) / r) :
    8 * c ^ 2 / r * a ^ 2 + (k * c) ^ 2 * a ^ 2 / 4 + k * c * (a ^ 2 + a * b) -
      c ^ 2 / 2 * (1 - a ^ 2) ≤ (16 * c ^ 2 + 16 * c ^ 3 + c ^ 4 / 2 + 8 * c ^ 6) / r := by
  have hr : 0 < r := by linarith
  have hkc : k * c = 4 * c ^ 3 / r := by rw [hk_def]; ring
  have t1 : 8 * c ^ 2 / r * a ^ 2 ≤ 16 * c ^ 2 / r := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr]
    linarith [mul_le_mul_of_nonneg_left ha2 (sq_nonneg c)]
  have t2 : (k * c) ^ 2 * a ^ 2 / 4 ≤ 8 * c ^ 6 / r := by
    have h6 : 0 ≤ c ^ 6 := by positivity
    rw [hkc]
    calc (4 * c ^ 3 / r) ^ 2 * a ^ 2 / 4 = 4 * c ^ 6 * a ^ 2 / r ^ 2 := by ring
      _ ≤ 4 * c ^ 6 * 2 / r ^ 2 := by gcongr
      _ ≤ 8 * c ^ 6 / r := by
        rw [div_le_div_iff₀ (by positivity) hr]
        linarith [mul_le_mul_of_nonneg_left (le_self_pow₀ hr1 two_ne_zero) h6]
  have t3 : k * c * (a ^ 2 + a * b) ≤ 12 * c ^ 3 / r := by
    rw [hkc, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr]
    linarith [mul_le_mul_of_nonneg_left (show a ^ 2 + a * b ≤ 3 by linarith) (pow_nonneg hc 3)]
  have t4 : -(c ^ 2 / 2 * (1 - a ^ 2)) ≤ c ^ 2 * (c ^ 2 + 8 * c) / (2 * r) := by
    calc -(c ^ 2 / 2 * (1 - a ^ 2)) = c ^ 2 / 2 * -(1 - a ^ 2) := by ring
      _ ≤ c ^ 2 / 2 * ((c ^ 2 + 8 * c) / r) := by gcongr
      _ = c ^ 2 * (c ^ 2 + 8 * c) / (2 * r) := by field_simp
  have e : (16 * c ^ 2 + 16 * c ^ 3 + c ^ 4 / 2 + 8 * c ^ 6) / r =
      16 * c ^ 2 / r + 8 * c ^ 6 / r + 12 * c ^ 3 / r + c ^ 2 * (c ^ 2 + 8 * c) / (2 * r) := by
    field_simp; ring
  linarith

/-- At a point where the Laplacian of `|β|² + (4 c² / r) |α|²` is nonpositive, the projected
Weitzenböck inequalities and the bound `|α|² + |β|² ≤ 1 + (c² + 8 c) / r` give
`|β|² ≤ (4 c² / r) (1 - |α|²) + K / r²`. The notation is that of
`sq_add_sq_le_of_weitzenbock`. -/
private theorem sq_le_of_weitzenbock {a b da db ga gb c r : ℝ} (hc : 0 ≤ c) (hr1 : 1 ≤ r)
    (hr32 : 32 * c ≤ r) (hrK : c ^ 2 + 8 * c ≤ r)
    (hs : a ^ 2 + b ^ 2 ≤ 1 + (c ^ 2 + 8 * c) / r)
    (hα : -ga / 2 + da ^ 2 + r / 4 * (a ^ 2 + b ^ 2 - 1) * a ^ 2 ≤ c * a * (db + a + b))
    (hβ : -gb / 2 + db ^ 2 + r / 4 * (a ^ 2 + b ^ 2 + 1) * b ^ 2 ≤ c * b * (da + a + b))
    (hg : gb + 4 * c ^ 2 / r * ga ≤ 0) :
    b ^ 2 ≤ 4 * c ^ 2 / r * (1 - a ^ 2) +
      (128 * c ^ 2 + 128 * c ^ 3 + 4 * c ^ 4 + 64 * c ^ 6) / r ^ 2 := by
  have hr : 0 < r := by linarith
  -- `|α|²` and `|β|²` are at most `2`, so `|α| |β| ≤ 1`.
  have hK1 : (c ^ 2 + 8 * c) / r ≤ 1 := by rw [div_le_one hr]; exact hrK
  have ha2 : a ^ 2 ≤ 2 := by linarith [sq_nonneg b]
  have hab1 : a * b ≤ 1 := by nlinarith [sq_nonneg (a - b)]
  have hw : -(1 - a ^ 2) ≤ (c ^ 2 + 8 * c) / r := by linarith [sq_nonneg b]
  have hmain := (comparison_of_weitzenbock hr hr32 rfl hα hβ hg).trans
    (comparison_rhs_le hc hr1 rfl ha2 hab1 hw)
  set v := b ^ 2 - 4 * c ^ 2 / r * (1 - a ^ 2)
  suffices v ≤ (128 * c ^ 2 + 128 * c ^ 3 + 4 * c ^ 4 + 64 * c ^ 6) / r ^ 2 by
    simp only [v] at this; linarith
  rcases le_or_gt v 0 with hv0 | hv0
  · exact hv0.trans (by positivity)
  · -- For `v > 0` the term `(r / 4) |α|² v` is nonnegative and may be dropped.
    have hv8 : r / 8 * v ≤ (16 * c ^ 2 + 16 * c ^ 3 + c ^ 4 / 2 + 8 * c ^ 6) / r := by
      have : 0 ≤ r / 4 * a ^ 2 * v := by positivity
      linarith
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ hr] at hv8
    linarith

/-! ### The maximum principle on a Riemannian manifold -/

open Bundle TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {A B F₁ F₂ : M → Type*} [∀ x, NormedAddCommGroup (A x)] [∀ x, NormedAddCommGroup (B x)]
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedAddCommGroup (F₂ x)]
  {α : (x : M) → A x} {β : (x : M) → B x} {Dα : (x : M) → F₁ x} {Dβ : (x : M) → F₂ x}
  {c r : ℝ}

/-- **The bound `|ψ|² ≤ 1 + O(1 / r)` at a local maximum.** At a local maximum `x₀` of
`|α|² + |β|²`, the projected Weitzenböck inequalities at `x₀` give
`|α(x₀)|² + |β(x₀)|² ≤ 1 + (c² + 8 c) / r`. Here `Dα` and `Dβ` stand for `∇_a α` and `∇β`. -/
theorem norm_sq_add_norm_sq_le_one_add_div_of_isLocalMax {x₀ : M} (hc : 0 ≤ c) (hr : 0 < r)
    (hα₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun x ↦ ‖α x‖ ^ 2) x₀)
    (hβ₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun x ↦ ‖β x‖ ^ 2) x₀)
    (hmax : IsLocalMax (fun x ↦ ‖α x‖ ^ 2 + ‖β x‖ ^ 2) x₀)
    (hWα : -laplaceBeltrami I (fun x ↦ ‖α x‖ ^ 2) x₀ / 2 + ‖Dα x₀‖ ^ 2 +
      r / 4 * (‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 - 1) * ‖α x₀‖ ^ 2 ≤
        c * ‖α x₀‖ * (‖Dβ x₀‖ + ‖α x₀‖ + ‖β x₀‖))
    (hWβ : -laplaceBeltrami I (fun x ↦ ‖β x‖ ^ 2) x₀ / 2 + ‖Dβ x₀‖ ^ 2 +
      r / 4 * (‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 + 1) * ‖β x₀‖ ^ 2 ≤
        c * ‖β x₀‖ * (‖Dα x₀‖ + ‖α x₀‖ + ‖β x₀‖)) :
    ‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 ≤ 1 + (c ^ 2 + 8 * c) / r := by
  -- The function `fun x ↦ ‖α x‖ ^ 2 + ‖β x‖ ^ 2` is the pointwise sum of the two squared norms.
  have hlap : laplaceBeltrami I ((fun x ↦ ‖α x‖ ^ 2) + fun x ↦ ‖β x‖ ^ 2) x₀ ≤ 0 :=
    laplaceBeltrami_nonpos_of_isLocalMax (hα₂.add hβ₂) hmax
  rw [laplaceBeltrami_add_of_contMDiffAt I hα₂ hβ₂] at hlap
  exact sq_add_sq_le_of_weitzenbock hc hr hWα hWβ hlap

/-- **Taubes's bound `|β|² ≤ (4 c² / r) (1 - |α|²) + O(r⁻²)` at a local maximum.** At a local
maximum `x₀` of `|β|² + (4 c² / r) |α|²` where `|α|² + |β|² ≤ 1 + (c² + 8 c) / r`, the projected
Weitzenböck inequalities at `x₀` give
`|β(x₀)|² ≤ (4 c² / r) (1 - |α(x₀)|²) + (128 c² + 128 c³ + 4 c⁴ + 64 c⁶) / r²`, provided
`r ≥ 1`, `r ≥ 32 c` and `r ≥ c² + 8 c`. -/
theorem norm_sq_le_div_mul_one_sub_add_div_sq_of_isLocalMax {x₀ : M} (hc : 0 ≤ c) (hr1 : 1 ≤ r)
    (hr32 : 32 * c ≤ r) (hrK : c ^ 2 + 8 * c ≤ r)
    (hα₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun x ↦ ‖α x‖ ^ 2) x₀)
    (hβ₂ : ContMDiffAt I 𝓘(ℝ) 2 (fun x ↦ ‖β x‖ ^ 2) x₀)
    (hmax : IsLocalMax (fun x ↦ ‖β x‖ ^ 2 + 4 * c ^ 2 / r * ‖α x‖ ^ 2) x₀)
    (hs : ‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 ≤ 1 + (c ^ 2 + 8 * c) / r)
    (hWα : -laplaceBeltrami I (fun x ↦ ‖α x‖ ^ 2) x₀ / 2 + ‖Dα x₀‖ ^ 2 +
      r / 4 * (‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 - 1) * ‖α x₀‖ ^ 2 ≤
        c * ‖α x₀‖ * (‖Dβ x₀‖ + ‖α x₀‖ + ‖β x₀‖))
    (hWβ : -laplaceBeltrami I (fun x ↦ ‖β x‖ ^ 2) x₀ / 2 + ‖Dβ x₀‖ ^ 2 +
      r / 4 * (‖α x₀‖ ^ 2 + ‖β x₀‖ ^ 2 + 1) * ‖β x₀‖ ^ 2 ≤
        c * ‖β x₀‖ * (‖Dα x₀‖ + ‖α x₀‖ + ‖β x₀‖)) :
    ‖β x₀‖ ^ 2 ≤ 4 * c ^ 2 / r * (1 - ‖α x₀‖ ^ 2) +
      (128 * c ^ 2 + 128 * c ^ 3 + 4 * c ^ 4 + 64 * c ^ 6) / r ^ 2 := by
  -- The comparison function is `fun x ↦ ‖β x‖ ^ 2 + k * ‖α x‖ ^ 2`, that is `g + k • f`.
  have hkα : ContMDiffAt I 𝓘(ℝ) 2 ((4 * c ^ 2 / r) • fun x ↦ ‖α x‖ ^ 2) x₀ :=
    contMDiffAt_const.mul hα₂
  have hlap : laplaceBeltrami I
      ((fun x ↦ ‖β x‖ ^ 2) + (4 * c ^ 2 / r) • fun x ↦ ‖α x‖ ^ 2) x₀ ≤ 0 :=
    laplaceBeltrami_nonpos_of_isLocalMax (hβ₂.add hkα) hmax
  rw [laplaceBeltrami_add_of_contMDiffAt I hβ₂ hkα,
    laplaceBeltrami_smul_of_contMDiffAt I _ hα₂] at hlap
  exact sq_le_of_weitzenbock hc hr1 hr32 hrK hs hWα hWβ hlap

/-! ### The global bounds on a closed manifold -/

variable [CompactSpace M]

/-- **Taubes's bound `|α|² + |β|² ≤ 1 + O(1 / r)`.** On a closed Riemannian manifold, if the
projected Weitzenböck inequalities hold everywhere, then
`|α|² + |β|² ≤ 1 + (c² + 8 c) / r` everywhere. -/
theorem norm_sq_add_norm_sq_le_one_add_div (hc : 0 ≤ c) (hr : 0 < r)
    (hα₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖α x‖ ^ 2) (hβ₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖β x‖ ^ 2)
    (hWα : ∀ x, -laplaceBeltrami I (fun x ↦ ‖α x‖ ^ 2) x / 2 + ‖Dα x‖ ^ 2 +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖α x‖ ^ 2 ≤ c * ‖α x‖ * (‖Dβ x‖ + ‖α x‖ + ‖β x‖))
    (hWβ : ∀ x, -laplaceBeltrami I (fun x ↦ ‖β x‖ ^ 2) x / 2 + ‖Dβ x‖ ^ 2 +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤ c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖))
    (x : M) : ‖α x‖ ^ 2 + ‖β x‖ ^ 2 ≤ 1 + (c ^ 2 + 8 * c) / r := by
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩
    (hα₂.continuous.add hβ₂.continuous).continuousOn
  exact (hx₀ (Set.mem_univ x)).trans <| norm_sq_add_norm_sq_le_one_add_div_of_isLocalMax hc hr
    (hα₂ x₀) (hβ₂ x₀) (hx₀.isLocalMax Filter.univ_mem) (hWα x₀) (hWβ x₀)

/-- **Taubes's bound `|β|² ≤ (4 c² / r) (1 - |α|²) + O(r⁻²)`.** On a closed Riemannian manifold,
if the projected Weitzenböck inequalities hold everywhere, then
`|β|² ≤ (4 c² / r) (1 - |α|²) + (128 c² + 128 c³ + 4 c⁴ + 64 c⁶) / r²` everywhere, provided
`r ≥ 1`, `r ≥ 32 c` and `r ≥ c² + 8 c`. -/
theorem norm_sq_le_div_mul_one_sub_add_div_sq (hc : 0 ≤ c) (hr1 : 1 ≤ r) (hr32 : 32 * c ≤ r)
    (hrK : c ^ 2 + 8 * c ≤ r)
    (hα₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖α x‖ ^ 2) (hβ₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖β x‖ ^ 2)
    (hWα : ∀ x, -laplaceBeltrami I (fun x ↦ ‖α x‖ ^ 2) x / 2 + ‖Dα x‖ ^ 2 +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖α x‖ ^ 2 ≤ c * ‖α x‖ * (‖Dβ x‖ + ‖α x‖ + ‖β x‖))
    (hWβ : ∀ x, -laplaceBeltrami I (fun x ↦ ‖β x‖ ^ 2) x / 2 + ‖Dβ x‖ ^ 2 +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤ c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖))
    (x : M) : ‖β x‖ ^ 2 ≤ 4 * c ^ 2 / r * (1 - ‖α x‖ ^ 2) +
      (128 * c ^ 2 + 128 * c ^ 3 + 4 * c ^ 4 + 64 * c ^ 6) / r ^ 2 := by
  have hr : 0 < r := by linarith
  obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn ⟨x, Set.mem_univ x⟩
    (hβ₂.continuous.add (continuous_const.mul hα₂.continuous)).continuousOn
  have h₀ := norm_sq_le_div_mul_one_sub_add_div_sq_of_isLocalMax hc hr1 hr32 hrK (hα₂ x₀) (hβ₂ x₀)
    (hx₀.isLocalMax Filter.univ_mem) (norm_sq_add_norm_sq_le_one_add_div hc hr hα₂ hβ₂ hWα hWβ x₀)
    (hWα x₀) (hWβ x₀)
  have hx : ‖β x‖ ^ 2 + 4 * c ^ 2 / r * ‖α x‖ ^ 2 ≤ ‖β x₀‖ ^ 2 + 4 * c ^ 2 / r * ‖α x₀‖ ^ 2 :=
    hx₀ (Set.mem_univ x)
  linarith

/-- **Taubes's bound `|β|² ≤ (C / r) w₊ + C / r²`.** Under the hypotheses of
`TauCeti.SeibergWitten.norm_sq_le_div_mul_one_sub_add_div_sq`, with `w₊ = max (1 - |α|²) 0` the
vacuum defect and `C = 128 c² + 128 c³ + 4 c⁴ + 64 c⁶`, `|β|² ≤ (C / r) w₊ + C / r²` everywhere. -/
theorem norm_sq_le_div_mul_max_add_div_sq (hc : 0 ≤ c) (hr1 : 1 ≤ r) (hr32 : 32 * c ≤ r)
    (hrK : c ^ 2 + 8 * c ≤ r)
    (hα₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖α x‖ ^ 2) (hβ₂ : ContMDiff I 𝓘(ℝ) 2 fun x ↦ ‖β x‖ ^ 2)
    (hWα : ∀ x, -laplaceBeltrami I (fun x ↦ ‖α x‖ ^ 2) x / 2 + ‖Dα x‖ ^ 2 +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 - 1) * ‖α x‖ ^ 2 ≤ c * ‖α x‖ * (‖Dβ x‖ + ‖α x‖ + ‖β x‖))
    (hWβ : ∀ x, -laplaceBeltrami I (fun x ↦ ‖β x‖ ^ 2) x / 2 + ‖Dβ x‖ ^ 2 +
      r / 4 * (‖α x‖ ^ 2 + ‖β x‖ ^ 2 + 1) * ‖β x‖ ^ 2 ≤ c * ‖β x‖ * (‖Dα x‖ + ‖α x‖ + ‖β x‖))
    (x : M) :
    ‖β x‖ ^ 2 ≤ (128 * c ^ 2 + 128 * c ^ 3 + 4 * c ^ 4 + 64 * c ^ 6) / r *
        max (1 - ‖α x‖ ^ 2) 0 + (128 * c ^ 2 + 128 * c ^ 3 + 4 * c ^ 4 + 64 * c ^ 6) / r ^ 2 := by
  refine (norm_sq_le_div_mul_one_sub_add_div_sq hc hr1 hr32 hrK hα₂ hβ₂ hWα hWβ x).trans
    (add_le_add_left ?_ _)
  calc 4 * c ^ 2 / r * (1 - ‖α x‖ ^ 2) ≤ 4 * c ^ 2 / r * max (1 - ‖α x‖ ^ 2) 0 := by
        gcongr; exact le_max_left _ _
    _ ≤ (128 * c ^ 2 + 128 * c ^ 3 + 4 * c ^ 4 + 64 * c ^ 6) / r * max (1 - ‖α x‖ ^ 2) 0 := by
        gcongr
        nlinarith [pow_nonneg hc 3, pow_nonneg hc 4, pow_nonneg hc 6, sq_nonneg c]

end TauCeti.SeibergWitten
