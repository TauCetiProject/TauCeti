/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.InverseCoercive
public import TauCeti.Analysis.PDE.Regularity.Harnack
public import TauCeti.Analysis.PDE.Regularity.HolderContinuity
import TauCeti.MeasureTheory.Measure.Restrict.Chain

/-!
# De Giorgi–Nash–Moser on balls under inverse-coercive ellipticity

Let `a` be a measurable coefficient field on a ball of `ℝⁿ` which is uniformly elliptic in the
almost-everywhere inverse-coercive sense (`TauCeti.PDE.IsUniformlyEllipticAE`): for almost every
`x` and every `ξ`, `ξ · a(x)ξ ≥ λ‖ξ‖²` and `ξ · a(x)⁻¹ξ ≥ Λ⁻¹‖ξ‖²`, with no symmetry. This file
proves the two interior regularity theorems for weak solutions of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0` in the
form in which they are used: on a ball, quantitative in the `L²` norm of the solution, and with
constants depending only on the ellipticity ratio `Λ / λ`, the dimension and the normalization
of the Haar measure, in every dimension.

* **De Giorgi's theorem.** A weak solution `u ∈ H¹(B(x₀, 2r))` has a precise representative
  which is `α`-Hölder on `B(x₀, r)` with constant `C r^(-α) r^(-n/2) ‖u‖_{L²(B(x₀, 2r))}`
  (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isUniformlyEllipticAE`).
* **Moser's Harnack inequality.** A nonnegative weak solution `u ∈ H¹(B(x₀, 4r))` satisfies
  `u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`
  (`TauCeti.PDE.exists_ae_ae_value_le_mul_value_of_isUniformlyEllipticAE`).

Both reduce to the theorems for the pointwise operator-bound predicate
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative` and
`TauCeti.PDE.exists_ae_ae_value_le_mul_value`). Dividing `a` by `λ` does not change the weak
solutions and normalizes the constants to `(1, Λ / λ)`, and changing `a` on a null set gives a
field satisfying the operator bound with the same constants everywhere
(`TauCeti.PDE.IsUniformlyEllipticAE.exists_uniformlyEllipticOn_energyFormH1_eq_zero`).
The Hölder estimate is then applied with the thickening radius `r / 2`. The Harnack inequality on
`B(x₀, r)` is assembled from the inequality on balls of radius `ρ = r / (8 √n)` centred in
`closedBall x₀ r`: finitely many such balls cover `closedBall x₀ r`, and each is joined to
`B(x₀, ρ)` by a chain of `⌈8 √n⌉ + 2` balls centred on a segment, consecutive balls overlapping
(`TauCeti.ae_ae_le_pow_mul_of_forall_mem_closedBall`). The number of balls in a chain depends
only on the dimension, so the constant does too.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.20, 8.22 and 8.24.
-/

public section

open MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped NNReal

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- **De Giorgi's theorem on a ball.** Fix a bound `ratio` for the ellipticity ratio. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `ratio`, the dimension `n` and the normalization of
the additive Haar measure `mu`, such that the following holds. Let `a` be measurable and
uniformly elliptic on `B(x₀, 2r)` in the inverse-coercive sense with constants `λ, Λ`,
`Λ ≤ ratio · λ`, not necessarily symmetric, and let `u ∈ H¹(B(x₀, 2r))` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, that is `a(u, v) = 0` for every `v ∈ H¹₀(B(x₀, 2r))`. Then the precise
representative of `u` is `α`-Hölder on `B(x₀, r)` with constant
`C r^(-α) r^(-n/2) ‖u‖_{L²(B(x₀, 2r))}`.

The precise representative agrees with `u` almost everywhere
(`TauCeti.W1p.ae_eq_preciseRepresentative`). The estimate is invariant under `u ↦ M u`, under
`a ↦ t a` for `t > 0`, and under translations and dilations of the ball. -/
theorem exists_holderOnWith_preciseRepresentative_of_isUniformlyEllipticAE (ratio : ℝ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧
      ∀ {lam Lam : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {u : W1p mu ⟨ball x₀ (2 * r), isOpen_ball⟩ 2},
        IsUniformlyEllipticAE mu (ball x₀ (2 * r)) a lam Lam → Lam ≤ ratio * lam →
        AEStronglyMeasurable a (mu.restrict (ball x₀ (2 * r))) →
        (∀ v : W1p0 mu ⟨ball x₀ (2 * r), isOpen_ball⟩ 2,
          energyFormH1 a 0 0 u (v : W1p mu ⟨ball x₀ (2 * r), isOpen_ball⟩ 2) = 0) →
        HolderOnWith (C * r ^ (-(α : ℝ)) * (r ^ (-(Fintype.card ι : ℝ) / 2) *
            √(∫ y in ball x₀ (2 * r), W1p.value u y ^ 2 ∂mu))).toNNReal α
          (preciseRepresentative mu (W1p.value u)) (ball x₀ r) := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative (mu := mu) (lam := 1) (Lam := ratio)
  refine ⟨α, C * 2 ^ ((α : ℝ) + Fintype.card ι / 2), hα, hα1, by positivity, ?_⟩
  intro lam Lam x₀ r a u h hratio ha hu
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  obtain ⟨a', h', ha', hu'⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq_zero
    (Omega := ⟨ball x₀ (2 * r), isOpen_ball⟩) hratio ha hu
  -- The closed `r / 2`-thickening of `B(x₀, r)` lies in `B(x₀, 2r)`.
  have hthick : cthickening (r / 2) (ball x₀ r) ⊆ ball x₀ (2 * r) :=
    (cthickening_subset_of_subset _ ball_subset_closedBall).trans
      ((cthickening_closedBall (by positivity) hr.le x₀).trans_subset
        (closedBall_subset_ball (by linarith)))
  have key := hhol (Omega := ⟨ball x₀ (2 * r), isOpen_ball⟩) (K := ball x₀ r) h' ha' hu'
    (half_pos hr) hthick
  -- Rescale the constant from the radius `r / 2` to the radius `r`.
  have hconst : ∀ S : ℝ, C * 2 ^ ((α : ℝ) + Fintype.card ι / 2) * r ^ (-(α : ℝ)) *
      (r ^ (-(Fintype.card ι : ℝ) / 2) * S) =
      C * (r / 2) ^ (-(α : ℝ)) * ((r / 2) ^ (-(Fintype.card ι : ℝ) / 2) * S) := fun S => by
    simp only [Real.div_rpow hr.le zero_le_two, Real.rpow_add two_pos, neg_div,
      Real.rpow_neg zero_le_two]
    field_simp
  rw [hconst]
  exact key

/-- **Moser's Harnack inequality on a ball.** Fix a bound `ratio` for the ellipticity ratio.
There is `C > 0`, depending only on `ratio`, the dimension `n` and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `a` be measurable and uniformly
elliptic on `B(x₀, 4r)` in the inverse-coercive sense with constants `λ, Λ`, `Λ ≤ ratio · λ`, not
necessarily symmetric, and let `u ∈ H¹(B(x₀, 4r))` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`
with `u ≥ 0` almost everywhere. Then

`u(y) ≤ C u(x)` for almost every `x, y ∈ B(x₀, r)`,

that is, `ess sup_{B(x₀, r)} u ≤ C ess inf_{B(x₀, r)} u`. -/
theorem exists_ae_ae_value_le_mul_value_of_isUniformlyEllipticAE (ratio : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {lam Lam : ℝ} {x₀ : EuclideanSpace ℝ ι} {r : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
        {u : W1p mu ⟨ball x₀ (4 * r), isOpen_ball⟩ 2},
        IsUniformlyEllipticAE mu (ball x₀ (4 * r)) a lam Lam → Lam ≤ ratio * lam →
        AEStronglyMeasurable a (mu.restrict (ball x₀ (4 * r))) →
        (∀ v : W1p0 mu ⟨ball x₀ (4 * r), isOpen_ball⟩ 2,
          energyFormH1 a 0 0 u (v : W1p mu ⟨ball x₀ (4 * r), isOpen_ball⟩ 2) = 0) →
        (∀ᵐ x ∂mu.restrict (ball x₀ (4 * r)), 0 ≤ W1p.value u x) →
        ∀ᵐ x ∂mu.restrict (ball x₀ r), ∀ᵐ y ∂mu.restrict (ball x₀ r),
          W1p.value u y ≤ C * W1p.value u x := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In dimension zero the space is a single point.
    refine ⟨1, one_pos, fun {lam Lam x₀ r a u} _ _ _ _ hu0 => ?_⟩
    rcases le_or_gt r 0 with hr | hr
    · simp [ball_eq_empty.2 hr]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hu0]
      with x _
    filter_upwards with y
    rw [Subsingleton.elim y x, one_mul]
  obtain ⟨C₀, hC₀, hH⟩ := exists_ae_ae_value_le_mul_value (mu := mu) (lam := 1) (Lam := ratio)
  -- Chains of `m + 1` balls of radius `ρ = r / (8 √n)` join `x₀` to every point of
  -- `closedBall x₀ r`.
  set m : ℕ := ⌈8 * √(Fintype.card ι : ℝ)⌉₊ + 1
  refine ⟨C₀ ^ (2 * m + 2), by positivity, ?_⟩
  intro lam Lam x₀ r a u h hratio ha hu hu0
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  obtain ⟨a', h', ha', hu'⟩ := h.exists_uniformlyEllipticOn_energyFormH1_eq_zero
    (Omega := ⟨ball x₀ (4 * r), isOpen_ball⟩) hratio ha hu
  have : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)
  have hρ : 0 < r / (8 * √(Fintype.card ι : ℝ)) := by positivity
  refine ae_ae_le_pow_mul_of_forall_mem_closedBall hC₀.le hρ ?_ fun z hz => ?_
  · -- `r < m ρ` since `m > 8 √n`.
    have h8 : 8 * √(Fintype.card ι : ℝ) < m :=
      (Nat.le_ceil _).trans_lt (by simp only [m]; push_cast; linarith)
    rw [mul_div_assoc', lt_div_iff₀ (by positivity)]
    nlinarith
  -- Moser's Harnack inequality on `B(z, ρ)`, since `B(z, 16 √n ρ) = B(z, 2r) ⊆ B(x₀, 4r)`.
  refine hH (Omega := ⟨ball x₀ (4 * r), isOpen_ball⟩) h' ha' hu' hu0 (ball_subset_ball' ?_)
  rw [mem_closedBall] at hz
  have : 16 * √(Fintype.card ι : ℝ) * (r / (8 * √(Fintype.card ι : ℝ))) = 2 * r := by
    field_simp; ring
  linarith

end TauCeti.PDE
