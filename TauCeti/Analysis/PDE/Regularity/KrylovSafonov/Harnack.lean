/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.WeakHarnack
import TauCeti.Analysis.Convex.HarnackChain
import TauCeti.Analysis.PDE.Regularity.KrylovSafonov.LocalMaximumPrinciple

/-!
# The Harnack inequality of Krylov and Safonov

Let `a` be uniformly elliptic on a ball `B(x₀, 2 r) ⊆ ℝⁿ` with constants `λ ≤ Λ ≤ κ λ`, and let
`u ≥ 0` be a `C²` solution of the non-divergence-form equation

`∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` in `B(x₀, 2 r)`

with `f ∈ Lⁿ(B(x₀, 2 r))`. The **Harnack inequality** of Krylov and Safonov compares the values of
`u` at any two points of the concentric ball of half the radius:

`u(x) ≤ C (u(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)` for all `x, y ∈ B(x₀, r)`,

with `C` depending only on the dimension and on `κ`
(`TauCeti.PDE.exists_le_mul_add_of_sum_mul_fderiv_fderiv_eq`). In particular
`sup_{B(x₀, r)} u ≤ C (inf_{B(x₀, r)} u + r ‖f‖ / λ)`. The coefficients need no regularity, not
even measurability, and need not be symmetric. More generally, the same bound holds when only
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` (`TauCeti.PDE.exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le`;
Caffarelli–Cabré, Theorem 4.3).

## The argument

* **At the centre of a ball.** Let `u ≥ 0` solve the equation in `B(c, R)` and put
  `δ = R / (16 √n)`. The local maximum principle on `B(c, δ)`, at the exponent `p` of the weak
  Harnack inequality, bounds `u(c)` by `δ^(-n/p) ‖u‖_{Lᵖ(B(c, δ))}` and `δ ‖f‖ₙ / λ`. The weak
  Harnack inequality on `B(c, R)` bounds `‖u‖_{Lᵖ(B(c, δ))}` by `R^(n/p) (u(y) + R ‖f‖ₙ / λ)` for
  every `y ∈ B(c, R / 4)`. Since `δ^(-n/p) R^(n/p) = (16 √n)^(n/p)`, this gives
  `u(c) ≤ C₀ (u(y) + R ‖f‖ₙ / λ)` whenever `‖y - c‖ < R / 4`.
* **Chaining.** For `z ∈ B(x₀, r)`, the closed ball `closedBall z r` lies in `B(x₀, 2 r)`, so the
  previous step applies with `R = r` and gives `u(z) ≤ C₀ (u(w) + r ‖f‖ₙ / λ)` for points `z, w`
  of `B(x₀, r)` at distance at most `r / 5`. Two points of `B(x₀, r)` are at distance less than
  `2 r = 10 (r / 5)`, and the Harnack chain along the segment joining them
  (`Convex.le_pow_mul_add_mul_of_dist_le_mul`) gives the estimate with `C = 10 C₀¹⁰`.

## Main declarations

* `TauCeti.PDE.exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le`: **the Harnack inequality of
  Krylov and Safonov** for nonnegative `C²` functions with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f`.
* `TauCeti.PDE.exists_le_mul_add_of_sum_mul_fderiv_fderiv_eq`: the same for nonnegative `C²`
  solutions of `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f`.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Corollary 9.25.
* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), Theorem 4.3.
-/

public section

noncomputable section

open Metric MeasureTheory Set

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weak Harnack inequality, in real form, for nonnegative `C²` functions with
`|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` in `B(c, R)`. -/
private theorem exists_toReal_eLpNorm_le_mul_rpow_mul_add {κ : ℝ} (hκ : 0 < κ) :
    ∃ p C : ℝ, 0 < p ∧ 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, UniformlyEllipticOn (ball c R) a lam Lam →
        Lam ≤ κ * lam → ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ closedBall c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball c R)) →
        ∀ y ∈ ball c (R / 4),
          (eLpNorm u (ENNReal.ofReal p)
              (volume.restrict (ball c (R / (16 * √(Fintype.card ι)))))).toReal ≤
            C * R ^ ((Fintype.card ι : ℝ) / p) * (u y + R / lam *
              (eLpNorm f (Fintype.card ι) (volume.restrict (ball c R))).toReal) := by
  obtain ⟨p, C, hp, hC, H⟩ := exists_eLpNorm_le_mul_rpow_mul_add_eLpNorm_posPart (ι := ι) hκ
  refine ⟨p, C, hp, hC, fun lam Lam R c a u f ha hLam hcont hu hnonneg habs hf y hy ↦ ?_⟩
  have hR : 0 < R := by linarith [pos_of_mem_ball hy]
  have hlam : 0 < lam := ha.pos
  have huy : 0 ≤ u y := hnonneg y (ball_subset_closedBall (ball_subset_ball (by linarith) hy))
  have hweak := H ha hLam hcont hu hnonneg (fun x hx ↦ le_of_abs_le (habs x hx)) y hy
  -- `f ≥ |∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≥ 0` on the ball, so `f⁺ = f` there.
  have hfpos : eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball c R)) =
      ENNReal.ofReal (eLpNorm f (Fintype.card ι) (volume.restrict (ball c R))).toReal := by
    rw [ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
    exact eLpNorm_congr_ae <| ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦
      posPart_eq_self.2 ((abs_nonneg _).trans (habs x hx))
  rw [hfpos, ← ENNReal.ofReal_mul (div_pos hR hlam).le, ← ENNReal.ofReal_add huy (by positivity),
    ← ENNReal.ofReal_mul (by positivity)] at hweak
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hweak

/-- The local maximum principle at the centre of `B(c, R)`, in real form, for nonnegative `C²`
functions with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` in `B(c, R)`. -/
private theorem exists_le_mul_rpow_mul_toReal_eLpNorm_add [Nonempty ι] {κ p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam R : ℝ⦄ ⦃c : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, 0 < R → UniformlyEllipticOn (ball c R) a lam Lam →
        Lam ≤ κ * lam → ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
        (∀ x ∈ ball c R, 0 ≤ u x) →
        (∀ x ∈ ball c R, |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball c R)) →
        u c ≤ C * (R ^ (-(Fintype.card ι : ℝ) / p) *
          (eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c R))).toReal +
          R / lam * (eLpNorm f (Fintype.card ι) (volume.restrict (ball c R))).toReal) := by
  obtain ⟨C, hC, H⟩ := exists_le_mul_rpow_mul_eLpNorm_posPart_add (ι := ι) (κ := κ) hp
  refine ⟨C, hC, fun lam Lam R c a u f hR ha hLam hcont hu hnonneg habs hf ↦ ?_⟩
  -- `f ≥ |∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≥ 0` on the ball, so `(-f)⁻ = f` there; and `u⁺ = u` there.
  have hfneg : (fun x ↦ (-f x)⁻) =ᵐ[volume.restrict (ball c R)] f :=
    ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦ by
      simp only [negPart_neg, posPart_eq_self.2 ((abs_nonneg _).trans (habs x hx))]
  have hupos : eLpNorm (fun x ↦ (u x)⁺) (ENNReal.ofReal p) (volume.restrict (ball c R)) =
      eLpNorm u (ENNReal.ofReal p) (volume.restrict (ball c R)) :=
    eLpNorm_congr_ae <| ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦
      posPart_eq_self.2 (hnonneg x hx)
  have h := H ha hLam hcont hu (f := fun x ↦ -f x) (fun x hx ↦ neg_le_of_abs_le (habs x hx))
    (hf.ae_eq hfneg.symm) c (mem_ball_self (half_pos hR))
  rwa [hupos, eLpNorm_congr_ae hfneg] at h

/-- **The Harnack inequality at a fixed scale.** There is `C ≥ 1`, depending only on the
dimension and on `κ`, such that a nonnegative `C²` function `u` with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` in
`B(x₀, 2 r)` satisfies `u(z) ≤ C (u(w) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)` for all `z, w ∈ B(x₀, r)` at
distance at most `r / 5`. -/
private theorem exists_le_mul_add_of_dist_le_div_five [Nonempty ι] {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
        Lam ≤ κ * lam → ContDiffOn ℝ 2 u (ball x₀ (2 * r)) →
        (∀ x ∈ ball x₀ (2 * r), 0 ≤ u x) →
        (∀ x ∈ ball x₀ (2 * r), |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        ∀ z ∈ ball x₀ r, ∀ w ∈ ball x₀ r, dist z w ≤ r / 5 → u z ≤ C * (u w + r *
          (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨p, Cw, hp, hCw, HW⟩ := exists_toReal_eLpNorm_le_mul_rpow_mul_add (ι := ι) hκ
  obtain ⟨Cl, hCl, HL⟩ := exists_le_mul_rpow_mul_toReal_eLpNorm_add (ι := ι) (κ := κ) hp
  set n : ℝ := (Fintype.card ι : ℝ)
  set s : ℝ := 16 * √n
  have hs : 16 ≤ s := by linarith [Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos : 1 ≤ n)]
  refine ⟨max 1 (Cl * (s ^ (n / p) * Cw + 1)), le_max_left _ _, ?_⟩
  intro lam Lam r x₀ a u f ha hLam hu hnonneg habs hf z hz w hw hzw
  have hr : 0 < r := pos_of_mem_ball hz
  have hlam : 0 < lam := ha.pos
  have huw : 0 ≤ u w := hnonneg w (ball_subset_ball (by linarith) hw)
  set F := (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal
  have hF : ∀ {t}, t ⊆ ball x₀ (2 * r) →
      (eLpNorm f (Fintype.card ι) (volume.restrict t)).toReal ≤ F := fun ht ↦
    ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ (Measure.restrict_mono ht le_rfl))
  -- The balls about `z`: `B(z, r / s) ⊆ closedBall z r ⊆ B(x₀, 2 r)`.
  have hsub : closedBall z r ⊆ ball x₀ (2 * r) := fun v hv ↦ by
    rw [mem_closedBall] at hv
    rw [mem_ball] at hz ⊢
    linarith [dist_triangle v z x₀]
  have hb : ball z r ⊆ ball x₀ (2 * r) := ball_subset_closedBall.trans hsub
  have hδ : 0 < r / s := div_pos hr (by linarith)
  have hδr : r / s < r := div_lt_self hr (by linarith)
  have hbδ : ball z (r / s) ⊆ ball x₀ (2 * r) := (ball_subset_ball hδr.le).trans hb
  have hloc := HL hδ (ha.mono_set hbδ) hLam
    (hu.continuousOn.mono ((closedBall_subset_ball hδr).trans hb)) (hu.mono hbδ)
    (fun x hx ↦ hnonneg x (hbδ hx)) (fun x hx ↦ habs x (hbδ hx))
    (hf.mono_measure (Measure.restrict_mono hbδ le_rfl))
  have hweak := HW (ha.mono_set hb) hLam (hu.continuousOn.mono hsub) (hu.mono hb)
    (fun x hx ↦ hnonneg x (hsub hx)) (fun x hx ↦ habs x (hb hx))
    (hf.mono_measure (Measure.restrict_mono hb le_rfl)) w (by rw [mem_ball, dist_comm]; linarith)
  -- Combine, using `(r / s)^(-n/p) r^(n/p) = s^(n/p)`.
  have hscale : (r / s) ^ (-n / p) * r ^ (n / p) = s ^ (n / p) := by
    rw [neg_div, Real.rpow_neg hδ.le, Real.div_rpow hr.le (by linarith), inv_div,
      div_mul_cancel₀ _ (Real.rpow_pos_of_pos hr _).ne']
  calc u z ≤ Cl * ((r / s) ^ (-n / p) * (Cw * r ^ (n / p) * (u w + r / lam * F)) +
        r / lam * F) := by
        refine hloc.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hCl.le)
        · refine mul_le_mul_of_nonneg_left (hweak.trans ?_) (by positivity)
          gcongr
          exact hF hb
        · exact mul_le_mul (div_le_div_of_nonneg_right hδr.le hlam.le) (hF hbδ)
            ENNReal.toReal_nonneg (by positivity)
    _ = Cl * (s ^ (n / p) * Cw * (u w + r * F / lam) + r * F / lam) := by
        rw [← hscale]
        ring
    _ ≤ Cl * (s ^ (n / p) * Cw + 1) * (u w + r * F / lam) := by
        have : 0 ≤ r * F / lam := by positivity
        nlinarith [mul_nonneg hCl.le huw]
    _ ≤ max 1 (Cl * (s ^ (n / p) * Cw + 1)) * (u w + r * F / lam) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **The Harnack inequality of Krylov and Safonov** (Caffarelli–Cabré, Theorem 4.3, for
classical functions). For every `κ` there is `C > 0`, depending only on the dimension and on `κ`,
with the following property. Let `a` be uniformly elliptic on `B(x₀, 2 r)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be `C²` in `B(x₀, 2 r)` with `|∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu| ≤ f` there, where
`f ∈ Lⁿ(B(x₀, 2 r))`. Then for all `x, y ∈ B(x₀, r)`,

`u(x) ≤ C (u(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le (κ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
        Lam ≤ κ * lam → ContDiffOn ℝ 2 u (ball x₀ (2 * r)) →
        (∀ x ∈ ball x₀ (2 * r), 0 ≤ u x) →
        (∀ x ∈ ball x₀ (2 * r), |∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r, u x ≤ C * (u y + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  -- For `κ ≤ 0` no coefficients satisfy `0 < λ ≤ Λ ≤ κ λ`.
  rcases le_or_gt κ 0 with hκ | hκ
  · refine ⟨1, one_pos, fun lam Lam r x₀ a u f ha hLam _ _ _ _ ↦ absurd hLam ?_⟩
    have := ha.pos
    nlinarith [ha.le]
  -- In dimension `0` all points coincide.
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, one_pos, fun lam Lam r x₀ a u f ha _ _ _ _ _ x _ y hy ↦ ?_⟩
    rw [Subsingleton.elim x y, one_mul]
    have : 0 ≤ r * (eLpNorm f (Fintype.card ι)
        (volume.restrict (ball x₀ (2 * r)))).toReal / lam := by
      have := ha.pos
      have : 0 < r := pos_of_mem_ball hy
      positivity
    linarith
  obtain ⟨C₀, hC₀, H⟩ := exists_le_mul_add_of_dist_le_div_five (ι := ι) hκ
  refine ⟨10 * C₀ ^ 10, by positivity, ?_⟩
  intro lam Lam r x₀ a u f ha hLam hu hnonneg habs hf x hx y hy
  have hr : 0 < r := pos_of_mem_ball hx
  have hlam : 0 < lam := ha.pos
  set F := (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal
  -- Chain the fixed-scale estimate along the segment from `x` to `y`, cut into ten pieces.
  have hxy : dist x y ≤ (10 : ℕ) * (r / 5) := by
    have := dist_triangle_right x y x₀
    rw [mem_ball] at hx hy
    push_cast
    linarith
  have hchain := (convex_ball x₀ r).le_pow_mul_add_mul_of_dist_le_mul hC₀ (by positivity)
    (H ha hLam hu hnonneg habs hf) 10 hx hy hxy
  have huy : 0 ≤ u y := hnonneg y (ball_subset_ball (by linarith) hy)
  have hC10 : 0 ≤ C₀ ^ 10 := by positivity
  calc u x ≤ C₀ ^ 10 * (u y + (10 : ℕ) * (r * F / lam)) := hchain
    _ ≤ 10 * C₀ ^ 10 * (u y + r * F / lam) := by
      push_cast
      nlinarith [mul_nonneg hC10 huy]

/-- **The Harnack inequality of Krylov and Safonov** (Gilbarg–Trudinger, Corollary 9.25, for
classical solutions). For every `κ` there is `C > 0`, depending only on the dimension and on `κ`,
with the following property. Let `a` be uniformly elliptic on `B(x₀, 2 r)` with constants
`λ ≤ Λ ≤ κ λ`, and let `u ≥ 0` be `C²` in `B(x₀, 2 r)` with `∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu = f` there, where
`f ∈ Lⁿ(B(x₀, 2 r))`. Then for all `x, y ∈ B(x₀, r)`,

`u(x) ≤ C (u(y) + r ‖f‖_{Lⁿ(B(x₀, 2 r))} / λ)`.

The coefficients need no regularity, not even measurability, and need not be symmetric. -/
theorem exists_le_mul_add_of_sum_mul_fderiv_fderiv_eq (κ : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃lam Lam r : ℝ⦄ ⦃x₀ : EuclideanSpace ℝ ι⦄ ⦃a : EuclideanSpace ℝ ι → Matrix ι ι ℝ⦄
        ⦃u f : EuclideanSpace ℝ ι → ℝ⦄, UniformlyEllipticOn (ball x₀ (2 * r)) a lam Lam →
        Lam ≤ κ * lam → ContDiffOn ℝ 2 u (ball x₀ (2 * r)) →
        (∀ x ∈ ball x₀ (2 * r), 0 ≤ u x) →
        (∀ x ∈ ball x₀ (2 * r), ∑ i, ∑ j, a x i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = f x) →
        MemLp f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r))) →
        ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r, u x ≤ C * (u y + r * (eLpNorm f (Fintype.card ι)
          (volume.restrict (ball x₀ (2 * r)))).toReal / lam) := by
  obtain ⟨C, hC, H⟩ := exists_le_mul_add_of_abs_sum_mul_fderiv_fderiv_le (ι := ι) κ
  refine ⟨C, hC, fun lam Lam r x₀ a u f ha hLam hu hnonneg heq hf ↦ ?_⟩
  rw [← eLpNorm_norm f hf.aestronglyMeasurable]
  exact H ha hLam hu hnonneg (fun x hx ↦ (heq x hx).symm ▸ (Real.norm_eq_abs _).ge) hf.norm

end PDE

end TauCeti
