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

* **At the centre of a ball.** Let `u ≥ 0` solve the equation in `B(c, R)` and put `δ = R / 4`.
  The local maximum principle on `B(c, δ)`, at the exponent `p` of the weak Harnack inequality,
  bounds `u(c)` by `δ^(-n/p) ‖u‖_{Lᵖ(B(c, δ))}` and `δ ‖f‖ₙ / λ`. The weak Harnack inequality on
  `B(c, R)` at `θ = 1 / 4` bounds `δ^(-n/p) ‖u‖_{Lᵖ(B(c, δ))}` by `C₀ (u(y) + R ‖f‖ₙ / λ)` for
  every `y ∈ B(c, R / 4)`. Thus `u(c) ≤ C (u(y) + R ‖f‖ₙ / λ)` whenever `‖y - c‖ < R / 4`.
* **Chaining.** For `z ∈ B(x₀, r)`, the ball `B(z, r)` lies in `B(x₀, 2 r)`, so the previous step
  applies with `R = r` and gives `u(z) ≤ C₀ (u(w) + r ‖f‖ₙ / λ)` for points `z, w` of `B(x₀, r)`
  at distance at most `r / 5`. Two points of `B(x₀, r)` are at distance less than
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
private theorem exists_le_mul_add_of_dist_le_div_five [Nonempty ι] {κ : ℝ} :
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
  obtain ⟨p, hp, HW'⟩ :=
    exists_rpow_neg_mul_eLpNorm_le_mul_add_of_sum_mul_fderiv_fderiv_le (ι := ι) (κ := κ)
  obtain ⟨Cw, hCw, HW⟩ := HW' (θ := 1 / 4) (by norm_num) (by norm_num)
  obtain ⟨Cl, hCl, HL⟩ := exists_le_mul_rpow_mul_toReal_eLpNorm_add (ι := ι) (κ := κ) hp
  refine ⟨max 1 (Cl * (Cw + 1)), le_max_left _ _, ?_⟩
  intro lam Lam r x₀ a u f ha hLam hu hnonneg habs hf z hz w hw hzw
  have hr : 0 < r := pos_of_mem_ball hz
  have hlam : 0 < lam := ha.pos
  have huw : 0 ≤ u w := hnonneg w (ball_subset_ball (by linarith) hw)
  set F := (eLpNorm f (Fintype.card ι) (volume.restrict (ball x₀ (2 * r)))).toReal
  have hF : ∀ {t}, t ⊆ ball x₀ (2 * r) →
      (eLpNorm f (Fintype.card ι) (volume.restrict t)).toReal ≤ F := fun ht ↦
    ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure _ (Measure.restrict_mono ht le_rfl))
  -- The balls about `z`: `B(z, r / 4) ⊆ B(z, r) ⊆ B(x₀, 2 r)`.
  have hb : ball z r ⊆ ball x₀ (2 * r) := fun v hv ↦ by
    rw [mem_ball] at hz hv ⊢
    linarith [dist_triangle v z x₀]
  have h4r : 1 / 4 * r < r := by linarith
  have hb4 : ball z (1 / 4 * r) ⊆ ball x₀ (2 * r) := (ball_subset_ball h4r.le).trans hb
  have hcb4 : closedBall z (1 / 4 * r) ⊆ ball x₀ (2 * r) := (closedBall_subset_ball h4r).trans hb
  have hloc := HL (by positivity) (ha.mono_set hb4) hLam
    (hu.continuousOn.mono hcb4) (hu.mono hb4)
    (fun x hx ↦ hnonneg x (hb4 hx)) (fun x hx ↦ habs x (hb4 hx))
    (hf.mono_measure (Measure.restrict_mono hb4 le_rfl))
  have hf_ae : f =ᵐ[volume.restrict (ball z r)] fun x ↦ (f x)⁺ :=
    ae_restrict_of_forall_mem measurableSet_ball fun x hx ↦
      (posPart_eq_self.2 ((abs_nonneg _).trans (habs x (hb hx)))).symm
  have hfpos : eLpNorm (fun x ↦ (f x)⁺) (Fintype.card ι) (volume.restrict (ball z r)) =
      eLpNorm f (Fintype.card ι) (volume.restrict (ball z r)) :=
    eLpNorm_congr_ae hf_ae.symm
  have hweak := HW (ha.mono_set hb) hLam (hu.mono hb)
    (fun x hx ↦ hnonneg x (hb hx)) (fun x hx ↦ le_of_abs_le (habs x (hb hx)))
    ((hf.mono_measure (Measure.restrict_mono hb le_rfl)).ae_eq hf_ae)
    w (by rw [mem_ball, dist_comm]; linarith)
  rw [hfpos] at hweak
  calc u z ≤ Cl * (Cw * (u w + r * F / lam) + r * F / lam) := by
        refine hloc.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hCl.le)
        · refine hweak.trans (mul_le_mul_of_nonneg_left ?_ hCw.le)
          have := hF hb
          gcongr
        · rw [div_mul_eq_mul_div]
          have := hF hb4
          gcongr
    _ ≤ Cl * (Cw + 1) * (u w + r * F / lam) := by
        have : 0 ≤ r * F / lam := by positivity
        nlinarith [mul_nonneg hCl.le huw]
    _ ≤ max 1 (Cl * (Cw + 1)) * (u w + r * F / lam) :=
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
  obtain ⟨C₀, hC₀, H⟩ := exists_le_mul_add_of_dist_le_div_five (ι := ι) (κ := κ)
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
