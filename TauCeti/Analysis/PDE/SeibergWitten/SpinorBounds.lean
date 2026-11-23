/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Pointwise bounds on the spinor components at large parameter

On a closed symplectic four-manifold Taubes writes a solution of the large-parameter
Seiberg–Witten equations as `Ψ = √r (α u₀ + β)`, where `u₀` spans the canonical line of the
positive spinors, `α` is a section of the line `E` and `β` of `K⁻¹ E`. Projecting the
Weitzenböck formula for `D_A Ψ = 0` onto the two summands, and using the curvature equation
`F_A⁺ = q(Ψ) + F_{A₀}⁺ - i r ω / 4 + ρ`, gives

`∇*∇ α + (r / 4) (|α|² + |β|² - 1) α = 𝔞`,  `∇*∇ β + (r / 4) (|α|² + |β|² + 1) β = 𝔟`,

where the errors, which collect the derivatives of `u₀`, the curvature of `A₀` and the forcing
`ρ`, satisfy `|𝔞| ≤ c (|∇_a β| + |α| + |β|)` and `|𝔟| ≤ c (|∇_a α| + |α| + |β|)` with a constant
`c` independent of `r`. Taking the real inner product with `α` and using the identity
`(1 / 2) d*d |α|² + |∇_a α|² = Re ⟪α, ∇*∇ α⟫`, and likewise for `β`, gives the two differential
inequalities

`-Δ|α|² / 2 + |∇_a α|² + (r / 4) (|α|² + |β|² - 1) |α|² ≤ c |α| (|∇_a β| + |α| + |β|)`,
`-Δ|β|² / 2 + |∇_a β|² + (r / 4) (|α|² + |β|² + 1) |β|² ≤ c |β| (|∇_a α| + |α| + |β|)`,

where `Δ = div ∘ grad = -d*d` is the Laplace–Beltrami operator
(`TauCeti.Manifold.laplaceBeltrami`). This file draws Taubes's first two pointwise bounds from
these inequalities by the maximum principle on a compact boundaryless Riemannian manifold:

* `|α|² + |β|² ≤ 1 + (8 c + c²) / r` (`TauCeti.SeibergWitten.sq_add_sq_le_one_add_div`);
* `|β|² ≤ (κ / r) max (1 - |α|²) 0 + C / r²` for every `κ ≥ 4 c²` and `r ≥ max 1 (16 c)`, with
  `C` an explicit polynomial in `c` and `κ`
  (`TauCeti.SeibergWitten.sq_le_div_mul_max_add_div_sq`).

The constants depend only on `c` and `κ`, not on `r`, the manifold or the solution. The first bound
comes from the sum of the two inequalities, which bounds the full spinor: a function `u`
with `a u² - b u ≤ Δu` and `a > 0` is at most `max (b / a) 0`
(`TauCeti.Manifold.le_max_div_zero_of_mul_sq_sub_mul_le_laplaceBeltrami`), because `Δu ≤ 0` at a
maximum of `u`. The second applies the maximum principle to `|β|² - (κ / r) (1 - |α|²)`: at its
maximum, if it is nonnegative, the damping `(r / 4) |α|² |β|²` of the `β` inequality cancels the
term `(κ / 4) (1 - |α|²) |α|²` from the `α` inequality, and what is left forces `|β|² = O(r⁻²)`
there.

The functions `A`, `B`, `Dα`, `Dβ` in the statements stand for `|α|`, `|β|`, `|∇_a α|` and
`|∇_a β|`. Only the squares `|α|²` and `|β|²` need to be `C²`, as they are for smooth `α` and `β`.
The differential inequalities themselves are hypotheses: deriving them from the Dirac equation
needs the Weitzenböck formula for the `Spinᶜ` Dirac operator, which is not part of this file.

## Main results

* `TauCeti.SeibergWitten.sq_add_sq_le_one_add_div`: `|α|² + |β|² ≤ 1 + (8 c + c²) / r`.
* `TauCeti.SeibergWitten.sq_le_div_mul_max_add_div_sq`:
  `|β|² ≤ (κ / r) max (1 - |α|²) 0 + C / r²`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210, Section 2.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.SeibergWitten

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] [CompactSpace M]

/-- **Taubes's bound on the full spinor.** On a compact boundaryless Riemannian manifold, let
`A`, `B`, `Dα`, `Dβ` stand for `|α|`, `|β|`, `|∇_a α|` and `|∇_a β|`, with `A²` and `B²` of class
`C²`, and suppose they satisfy the projected Weitzenböck inequalities with constant `c ≥ 0`.
Then `|α|² + |β|² ≤ 1 + (8 c + c²) / r`. -/
theorem sq_add_sq_le_one_add_div {A B Dα Dβ : M → ℝ} {r c : ℝ} (hr : 0 < r) (hc : 0 ≤ c)
    (hA : ContMDiff I 𝓘(ℝ) 2 fun x ↦ A x ^ 2) (hB : ContMDiff I 𝓘(ℝ) 2 fun x ↦ B x ^ 2)
    (hα : ∀ x, -laplaceBeltrami I (fun y ↦ A y ^ 2) x / 2 + Dα x ^ 2 +
      r / 4 * (A x ^ 2 + B x ^ 2 - 1) * A x ^ 2 ≤ c * A x * (Dβ x + A x + B x))
    (hβ : ∀ x, -laplaceBeltrami I (fun y ↦ B y ^ 2) x / 2 + Dβ x ^ 2 +
      r / 4 * (A x ^ 2 + B x ^ 2 + 1) * B x ^ 2 ≤ c * B x * (Dα x + A x + B x)) (x : M) :
    A x ^ 2 + B x ^ 2 ≤ 1 + (8 * c + c ^ 2) / r := by
  have hu : ContMDiff I 𝓘(ℝ) 2 fun x ↦ A x ^ 2 + B x ^ 2 := hA.add hB
  have key : (r / 2 + 4 * c + c ^ 2 / 2) / (r / 2) = 1 + (8 * c + c ^ 2) / r := by
    field_simp
    ring
  refine (le_max_div_zero_of_mul_sq_sub_mul_le_laplaceBeltrami (by positivity : 0 < r / 2) hu
    (fun y ↦ ?_) x).trans (max_le key.le (by positivity))
  -- Sum the two inequalities; the gradient cross terms are absorbed by `|∇_a α|² + |∇_a β|²`.
  have hΔ : laplaceBeltrami I (fun x ↦ A x ^ 2 + B x ^ 2) y =
      laplaceBeltrami I (fun x ↦ A x ^ 2) y + laplaceBeltrami I (fun x ↦ B x ^ 2) y :=
    laplaceBeltrami_add I hA hB y
  rw [hΔ]
  nlinarith [hα y, hβ y, sq_nonneg (Dβ y - c * A y / 2), sq_nonneg (Dα y - c * B y / 2),
    mul_nonneg hc (sq_nonneg (A y - B y)), mul_nonneg hr.le (sq_nonneg (B y))]

/-- The pointwise step of Taubes's bound on `β`, at a point where
`f = |β|² - (κ / r) (1 - |α|²)` is nonnegative and `Δf ≤ 0`: there `(r / 16) |β|² ≤ K₁ |α|²`, with
`K₁ = κ c / r + κ² c² / (4 r²) + 8 c² / r + 8 κ² c² / r³`. The real numbers `A`, `B`, `Dα`, `Dβ`
are the values of `|α|`, `|β|`, `|∇_a α|`, `|∇_a β|`, and `LA`, `LB` those of `Δ|α|²`, `Δ|β|²`. -/
private theorem div_mul_sq_le_of_add_div_mul_nonpos {A B Dα Dβ LA LB r c κ : ℝ} (hr : 0 < r)
    (hκc : 4 * c ^ 2 ≤ κ) (hrc : 16 * c ≤ r)
    (hα : -LA / 2 + Dα ^ 2 + r / 4 * (A ^ 2 + B ^ 2 - 1) * A ^ 2 ≤ c * A * (Dβ + A + B))
    (hβ : -LB / 2 + Dβ ^ 2 + r / 4 * (A ^ 2 + B ^ 2 + 1) * B ^ 2 ≤ c * B * (Dα + A + B))
    (hΔ : LB + κ / r * LA ≤ 0) (hf : 0 ≤ B ^ 2 - κ / r * (1 - A ^ 2)) :
    r / 16 * B ^ 2 ≤
      (κ * c / r + κ ^ 2 * c ^ 2 / (4 * r ^ 2) + 8 * c ^ 2 / r + 8 * κ ^ 2 * c ^ 2 / r ^ 3) *
        A ^ 2 := by
  have hκ : 0 ≤ κ := (by positivity : 0 ≤ 4 * c ^ 2).trans hκc
  have hκr : 0 ≤ κ / r := by positivity
  -- The four cross terms are split by the weighted arithmetic–geometric mean inequality
  -- `2 a b ≤ ε a² + ε⁻¹ b²`; for the first, `4 c² ≤ κ` absorbs the coefficient of `|∇_a α|²`.
  have h₁ : c * Dα * B ≤ κ / r * Dα ^ 2 + r / 16 * B ^ 2 := by
    have hc : 4 * c ^ 2 / r * Dα ^ 2 ≤ κ / r * Dα ^ 2 := by gcongr
    linear_combination two_mul_le_add_mul_sq (a := B) (b := c * Dα / 2)
      (by positivity : 0 < r / 16) + hc
  have h₂ : κ * c / r * Dβ * A ≤ Dβ ^ 2 + κ ^ 2 * c ^ 2 / (4 * r ^ 2) * A ^ 2 := by
    linear_combination two_mul_le_add_mul_sq (a := Dβ) (b := κ * c / r * A / 2) one_pos
  have h₃ : c * B * A ≤ r / 32 * B ^ 2 + 8 * c ^ 2 / r * A ^ 2 := by
    linear_combination two_mul_le_add_mul_sq (a := B) (b := c * A / 2)
      (by positivity : 0 < r / 32)
  have h₄ : κ * c / r * B * A ≤ r / 32 * B ^ 2 + 8 * κ ^ 2 * c ^ 2 / r ^ 3 * A ^ 2 := by
    linear_combination two_mul_le_add_mul_sq (a := B) (b := κ * c / r * A / 2)
      (by positivity : 0 < r / 32)
  -- The `α` inequality, weighted by `κ / r`.
  have hα' : κ / r * (-LA / 2 + Dα ^ 2) + κ / 4 * (A ^ 2 + B ^ 2 - 1) * A ^ 2 ≤
      κ * c / r * A * Dβ + κ * c / r * A ^ 2 + κ * c / r * A * B := by
    have := mul_le_mul_of_nonneg_left hα hκr
    have e₁ : κ / r * (r / 4 * (A ^ 2 + B ^ 2 - 1) * A ^ 2) =
        κ / 4 * (A ^ 2 + B ^ 2 - 1) * A ^ 2 := by field_simp
    have e₂ : κ / r * (c * A * (Dβ + A + B)) =
        κ * c / r * A * Dβ + κ * c / r * A ^ 2 + κ * c / r * A * B := by ring
    linarith [e₁, e₂]
  -- The lower bound `|β|² ≥ (κ / r) (1 - |α|²)` turns `(r / 4) |α|² |β|²` into the term that
  -- cancels `(κ / 4) (1 - |α|²) |α|²`.
  have hsb : κ / 4 * (1 - A ^ 2) * A ^ 2 ≤ r / 4 * A ^ 2 * B ^ 2 := by
    have := mul_le_mul_of_nonneg_left (sub_nonneg.1 hf) (by positivity : 0 ≤ r / 4 * A ^ 2)
    have e : r / 4 * A ^ 2 * (κ / r * (1 - A ^ 2)) = κ / 4 * (1 - A ^ 2) * A ^ 2 := by
      field_simp
    linarith
  have hcB : c * B ^ 2 ≤ r / 16 * B ^ 2 := by
    have : c ≤ r / 16 := by linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg B)
  nlinarith [mul_nonneg hκ (mul_nonneg (sq_nonneg A) (sq_nonneg B)), sq_nonneg (B ^ 2),
    mul_nonneg hr.le (sq_nonneg (B ^ 2))]

/-- The arithmetic closing Taubes's bound on `β` at the maximum of
`f = |β|² - (κ / r) (1 - |α|²)`: the pointwise step `(r / 16) |β|² ≤ K₁ |α|²` and the full-spinor
bound `|α|² ≤ 1 + (8 c + c²) / r` give `f ≤ C / r²` for `r ≥ 1`. -/
private theorem sq_sub_div_mul_le_div_sq {A B r c κ : ℝ} (hr₁ : 1 ≤ r) (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hb : r / 16 * B ^ 2 ≤
      (κ * c / r + κ ^ 2 * c ^ 2 / (4 * r ^ 2) + 8 * c ^ 2 / r + 8 * κ ^ 2 * c ^ 2 / r ^ 3) *
        A ^ 2)
    (hs : A ^ 2 ≤ 1 + (8 * c + c ^ 2) / r) :
    B ^ 2 - κ / r * (1 - A ^ 2) ≤
      ((16 * κ * c + 128 * c ^ 2 + 132 * κ ^ 2 * c ^ 2) * (1 + 8 * c + c ^ 2) +
        κ * (8 * c + c ^ 2)) / r ^ 2 := by
  have hr : 0 < r := by linarith
  set s := A ^ 2
  set C₀ := 8 * c + c ^ 2
  have hC₀ : 0 ≤ C₀ := by positivity
  set K₁ := κ * c / r + κ ^ 2 * c ^ 2 / (4 * r ^ 2) + 8 * c ^ 2 / r + 8 * κ ^ 2 * c ^ 2 / r ^ 3
    with hK₁_def
  -- Since `r ≥ 1`, `r K₁ ≤ κ c + 33 κ² c² / 4 + 8 c²`, and `s ≤ 1 + C₀`.
  have hK : K₁ * r ≤ κ * c + 33 / 4 * κ ^ 2 * c ^ 2 + 8 * c ^ 2 := by
    have e : K₁ * r =
        κ * c + κ ^ 2 * c ^ 2 / 4 * r⁻¹ + 8 * c ^ 2 + 8 * κ ^ 2 * c ^ 2 * (r ^ 2)⁻¹ := by
      rw [hK₁_def]
      field_simp
    have hr₁' : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr₁
    have hr₂' : (r ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hr₁)
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hr₁' (by positivity : 0 ≤ κ ^ 2 * c ^ 2 / 4),
      mul_le_mul_of_nonneg_left hr₂' (by positivity : 0 ≤ 8 * κ ^ 2 * c ^ 2)]
  have hs' : s ≤ 1 + C₀ := hs.trans (by
    have : C₀ / r ≤ C₀ := div_le_self hC₀ hr₁
    linarith)
  -- `|β|² ≤ (16 / r²) (r K₁) s`, and `-(κ / r) (1 - s) ≤ κ C₀ / r²`.
  have hb' : B ^ 2 * r ^ 2 ≤ 16 * (κ * c + 33 / 4 * κ ^ 2 * c ^ 2 + 8 * c ^ 2) * (1 + C₀) := by
    calc B ^ 2 * r ^ 2 = 16 * (r / 16 * B ^ 2) * r := by ring
      _ ≤ 16 * (K₁ * s) * r := by gcongr
      _ = 16 * (K₁ * r) * s := by ring
      _ ≤ 16 * (κ * c + 33 / 4 * κ ^ 2 * c ^ 2 + 8 * c ^ 2) * (1 + C₀) := by gcongr
  have hκs : -(κ / r * (1 - s)) * r ^ 2 ≤ κ * C₀ := by
    have e : -(κ / r * (1 - s)) * r ^ 2 = κ * ((s - 1) * r) := by field_simp; ring
    rw [e]
    have : (s - 1) * r ≤ C₀ := by
      have := (le_div_iff₀ hr).1 (sub_le_iff_le_add'.2 hs)
      linarith
    exact mul_le_mul_of_nonneg_left this hκ
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hb', hκs]

/-- **Taubes's bound on `β`.** On a compact boundaryless Riemannian manifold, let `A`, `B`, `Dα`,
`Dβ` stand for `|α|`, `|β|`, `|∇_a α|` and `|∇_a β|`, with `A²` and `B²` of class `C²`, and
suppose they satisfy the projected Weitzenböck inequalities with constant `c ≥ 0`. Then for every
`κ ≥ 4 c²` and every `r ≥ max 1 (16 c)`,

`|β|² ≤ (κ / r) max (1 - |α|²) 0 + C / r²`,

with `C = (16 κ c + 128 c² + 132 κ² c²) (1 + 8 c + c²) + κ (8 c + c²)`. In terms of the vacuum
defect `w₊ = max (1 - |α|²) 0` this is `|β|² ≤ (κ / r) w₊ + C / r²`. -/
theorem sq_le_div_mul_max_add_div_sq {A B Dα Dβ : M → ℝ} {r c κ : ℝ} (hc : 0 ≤ c)
    (hκc : 4 * c ^ 2 ≤ κ) (hr₁ : 1 ≤ r) (hrc : 16 * c ≤ r)
    (hA : ContMDiff I 𝓘(ℝ) 2 fun x ↦ A x ^ 2) (hB : ContMDiff I 𝓘(ℝ) 2 fun x ↦ B x ^ 2)
    (hα : ∀ x, -laplaceBeltrami I (fun y ↦ A y ^ 2) x / 2 + Dα x ^ 2 +
      r / 4 * (A x ^ 2 + B x ^ 2 - 1) * A x ^ 2 ≤ c * A x * (Dβ x + A x + B x))
    (hβ : ∀ x, -laplaceBeltrami I (fun y ↦ B y ^ 2) x / 2 + Dβ x ^ 2 +
      r / 4 * (A x ^ 2 + B x ^ 2 + 1) * B x ^ 2 ≤ c * B x * (Dα x + A x + B x)) (x : M) :
    B x ^ 2 ≤ κ / r * max (1 - A x ^ 2) 0 +
      ((16 * κ * c + 128 * c ^ 2 + 132 * κ ^ 2 * c ^ 2) * (1 + 8 * c + c ^ 2) +
        κ * (8 * c + c ^ 2)) / r ^ 2 := by
  have hr : 0 < r := by linarith
  have hκ : 0 ≤ κ := (by positivity : 0 ≤ 4 * c ^ 2).trans hκc
  have : Nonempty M := ⟨x⟩
  set C := (16 * κ * c + 128 * c ^ 2 + 132 * κ ^ 2 * c ^ 2) * (1 + 8 * c + c ^ 2) +
    κ * (8 * c + c ^ 2)
  -- Apply the maximum principle to `f = |β|² - (κ / r) (1 - |α|²)`.
  have hAs : ContMDiff I 𝓘(ℝ) 2 ((κ / r) • fun y ↦ A y ^ 2) :=
    (contMDiff_const : ContMDiff I 𝓘(ℝ) 2 fun _ : M ↦ κ / r).smul hA
  set f : M → ℝ := fun y ↦ B y ^ 2 - κ / r * (1 - A y ^ 2) with hf_def
  have hf_eq : f = (fun y ↦ B y ^ 2) + (κ / r) • (fun y ↦ A y ^ 2) - fun _ ↦ κ / r := by
    funext y
    simp only [hf_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hfC : ContMDiff I 𝓘(ℝ) 2 f := by
    rw [hf_eq]
    exact (hB.add hAs).sub contMDiff_const
  obtain ⟨x₀, hx₀, hΔ⟩ := exists_forall_ge_and_laplaceBeltrami_nonpos hfC
  rw [hf_eq, laplaceBeltrami_sub I (hB.add hAs) contMDiff_const,
    laplaceBeltrami_add I hB hAs, laplaceBeltrami_smul I _ hA,
    laplaceBeltrami_const, sub_zero] at hΔ
  -- It suffices to bound the maximum `f x₀` by `C / r²`.
  suffices hmax : f x₀ ≤ C / r ^ 2 by
    have hx := (hx₀ x).trans hmax
    simp only [hf_def] at hx
    have : κ / r * (1 - A x ^ 2) ≤ κ / r * max (1 - A x ^ 2) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    linarith
  rcases lt_or_ge (f x₀) 0 with hneg | hnonneg
  · exact hneg.le.trans (by positivity)
  -- At the maximum, `(r / 16) |β|² ≤ K₁ |α|²`.
  have hb := div_mul_sq_le_of_add_div_mul_nonpos hr hκc hrc (hα x₀) (hβ x₀) hΔ hnonneg
  -- The full-spinor bound controls `|α|²` at the maximum.
  have hs : A x₀ ^ 2 ≤ 1 + (8 * c + c ^ 2) / r := by
    have := sq_add_sq_le_one_add_div hr hc hA hB hα hβ x₀
    nlinarith [sq_nonneg (B x₀)]
  exact sq_sub_div_mul_le_div_sq hr₁ hc hκ hb hs

end TauCeti.SeibergWitten
