/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.WittenLaplacian.Gap
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The gap of the Witten Laplacian at nondegenerate critical points

`TauCeti.Analysis.Calculus.WittenLaplacian.Gap` proves Witten's linear-in-`t` gap for a function
`f` on `ℝ^ι` that is *exactly* a diagonal quadratic model near each of its critical points. This
file removes that assumption: it is enough that each critical point `p` is nondegenerate with
Hessian `∑ᵢ aᵢ vᵢ wᵢ`, diagonal in the coordinates of `ℝ^ι`. The quadratic model is then only the
second-order Taylor approximation of `f` at `p`, and the remainder is controlled on a small ball.

**Comparing two functions.** By Witten's frame formula, the Witten Laplacians `Δ_t` of two
functions `f` and `g` (`TauCeti.euclideanWittenLaplacian`) differ by the fibre endomorphism
`t² (|df|² - |dg|²) + t ∑_{i,j} (∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg) ⁅εᵢ, ιⱼ⁆`. So wherever `|dg|² ≤ |df|²` and
`∑_{i,j} |∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg| ≤ e` on the support of a form `φ`,

`∫ ⟨Δ_t^g φ, φ⟩ - |t| e ‖φ‖² ≤ ∫ ⟨Δ_t^f φ, φ⟩`

(`integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul`).

**Near a critical point.** Taking for `g` the translated quadratic model
`y ↦ ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` and its harmonic-oscillator gap, a form supported where
`|df(x)|² ≥ ∑ᵢ aᵢ² (xᵢ - pᵢ)²` and the Hessian of `f` is within `e` of `diag(a)` satisfies

`2 t c ‖φ_{≠ s₀}‖² - t e ‖φ‖² ≤ ∫ ⟨Δ_t φ, φ⟩`

(`TauCeti.two_mul_mul_integral_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`),
where `c ≤ |aᵢ|` for all `i` and `φ_{≠ s₀}` omits the component in the degree `s₀ = {i | aᵢ < 0}`
of the Morse index. At a nondegenerate critical point with Hessian `diag(a)`, Taylor's theorem
gives both hypotheses on a small ball for the slightly weakened model `θ a`, `θ < 1`, with `e`
small plus `(1 - θ) ∑ᵢ |aᵢ|`: the gradient of `f` is `diag(a) (x - p)` up to `o(|x - p|)` and the
Hessian is continuous.

**The gap.** Combining these local bounds with the bound away from the critical points by IMS
localization (`TauCeti.sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`) gives the
gap: if `f` is `C²`, its critical points in a finite set `P` have diagonal Hessians with every
`|aᵢ| ≥ c > 0`, and away from every neighbourhood of `P` the gradient is bounded below and the
Hessian bounded above, then in every degree `m` that is no Morse index the quadratic form of `Δ_t`
is at least `t c ‖φ‖²` for all large `t`
(`exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_fderiv_eq_zero`).
This is the same conclusion as
`TauCeti.exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`, without the
assumption that `f` is exactly quadratic near `P`. As there, the statements concern the quadratic
form on compactly supported forms, not the spectrum of a self-adjoint realization of `Δ_t`.

## Main results

* `TauCeti.sum_euclideanWittenLaplacian_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul`
  and
  `integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul`:
  comparison of the Witten Laplacians of two functions, pointwise and integrated.
* `TauCeti.two_mul_mul_integral_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`:
  the harmonic-oscillator gap for forms supported where `f` is close to a quadratic model.
* `exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_fderiv_eq_zero`:
  the gap `t c ‖φ‖²` for large `t` in a degree that is no Morse index.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Texts and
  Monographs in Physics, Springer (1987), Chapter 11 (Witten's proof of the Morse inequalities,
  where the quadratic model is the Taylor approximation of the function at its critical points).
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-! ### Comparing the Witten Laplacians of two functions -/

/-- **Comparison of the Witten Laplacians of two functions, pointwise.** For functions `f`, `g` and
a form `φ` that are `C²` at `x`,

`⟨Δ_t^g φ, φ⟩ + (t² (|df|² - |dg|²) - |t| ∑_{i,j} |∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg|) |φ|² ≤ ⟨Δ_t^f φ, φ⟩`

at `x`: by Witten's frame formula the two pairings differ by `t² (|df|² - |dg|²) |φ|²` and `t`
times the pairing of `φ` with `∑_{i,j} (∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg) ⁅εᵢ, ιⱼ⁆ φ`. -/
theorem sum_euclideanWittenLaplacian_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul
    {f g : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {x : ι → ℝ} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (hφ : ContDiffAt ℝ 2 φ x) (t : ℝ) :
    ∑ s, euclideanWittenLaplacian g t φ x s * φ x s +
        (t ^ 2 * (∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 - ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2) -
          |t| * ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
            fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1)|) * ∑ s, φ x s ^ 2 ≤
      ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  rw [sum_euclideanWittenLaplacian_apply_mul hf hφ, sum_euclideanWittenLaplacian_apply_mul hg hφ]
  -- The Hessian terms differ by the commutators weighted by the difference of the Hessians.
  have hD : ∀ H₁ H₂ : ι → ι → ℝ,
      ∑ s, (∑ i, ∑ j, H₁ i j • ⁅(Pi.basisFun ℝ ι).exteriorCreation i,
        (Pi.basisFun ℝ ι).exteriorContraction j⁆ (φ x)) s * φ x s -
      ∑ s, (∑ i, ∑ j, H₂ i j • ⁅(Pi.basisFun ℝ ι).exteriorCreation i,
        (Pi.basisFun ℝ ι).exteriorContraction j⁆ (φ x)) s * φ x s =
      ∑ s, (∑ i, ∑ j, (H₁ i j - H₂ i j) • ⁅(Pi.basisFun ℝ ι).exteriorCreation i,
        (Pi.basisFun ℝ ι).exteriorContraction j⁆ (φ x)) s * φ x s := by
    intro H₁ H₂
    simp only [sub_smul, Finset.sum_sub_distrib, Pi.sub_apply, sub_mul]
  have h := hD (fun i j ↦ fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1))
    (fun i j ↦ fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1))
  have hb :=
    (Pi.basisFun ℝ ι).abs_sum_sum_sum_smul_lie_exteriorCreation_exteriorContraction_apply_mul_le
      (fun i j ↦ fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1)) (φ x)
  rw [← h] at hb
  generalize ∑ s, (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) •
    ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆ (φ x)) s *
      φ x s = Hf at hb ⊢
  generalize ∑ s, (∑ i, ∑ j, fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1) •
    ⁅(Pi.basisFun ℝ ι).exteriorCreation i, (Pi.basisFun ℝ ι).exteriorContraction j⁆ (φ x)) s *
      φ x s = Hg at hb ⊢
  have ht : -(t * (Hf - Hg)) ≤ |t| * ((∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1)|) * ∑ s, φ x s ^ 2) :=
    calc -(t * (Hf - Hg)) ≤ |t * (Hf - Hg)| := neg_le_abs _
      _ = |t| * |Hf - Hg| := abs_mul t _
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (abs_nonneg t)
  linarith

/-- **Comparison of the Witten Laplacians of two functions.** Let `φ` be a compactly supported
`C²` form and `f`, `g` functions that are `C²` at every point of the support of `φ`. If, wherever
`φ` does not vanish, `|dg|² ≤ |df|²` and `∑_{i,j} |∂ᵢ∂ⱼf - ∂ᵢ∂ⱼg| ≤ e`, then

`∫ ⟨Δ_t^g φ, φ⟩ - |t| e ∫ |φ|² ≤ ∫ ⟨Δ_t^f φ, φ⟩`. -/
theorem integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul
    {f g : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x)
    (hg : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 g x) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hdf : ∀ x, φ x ≠ 0 →
      ∑ i, fderiv ℝ g x (Pi.single i 1) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    {e : ℝ} (he : ∀ x, φ x ≠ 0 → ∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        fderiv ℝ (fderiv ℝ g) x (Pi.single i 1) (Pi.single j 1)| ≤ e) (t : ℝ) :
    (∫ x, ∑ s, euclideanWittenLaplacian g t φ x s * φ x s) - |t| * e * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have hint : ∀ u : (ι → ℝ) → ℝ, (∀ x ∈ tsupport φ, ContDiffAt ℝ 2 u x) →
      Integrable fun x ↦ ∑ s, euclideanWittenLaplacian u t φ x s * φ x s := fun u hu ↦
    hφ.continuous.integrable_sum_mul_of_continuousOn hφc subset_rfl fun x hx ↦
      (continuousAt_euclideanWittenLaplacian (hu x hx) hφ.contDiffAt t).continuousWithinAt
  have hN : Integrable fun x ↦ |t| * e * ∑ s, φ x s ^ 2 :=
    hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl continuousOn_const
  calc _ = ∫ x, (∑ s, euclideanWittenLaplacian g t φ x s * φ x s -
        |t| * e * ∑ s, φ x s ^ 2) := by
          rw [integral_sub (hint g hg) hN, integral_const_mul]
    _ ≤ _ := integral_mono ((hint g hg).sub hN) (hint f hf) fun x ↦ ?_
  by_cases hx : φ x = 0
  · simp [hx]
  have hxs := subset_tsupport φ hx
  have h := sum_euclideanWittenLaplacian_mul_add_mul_sum_sq_le_sum_euclideanWittenLaplacian_mul
    (hf x hxs) (hg x hxs) hφ.contDiffAt t
  have h₁ := mul_nonneg (sq_nonneg t) (sub_nonneg.2 (hdf x hx))
  have h₂ := mul_le_mul_of_nonneg_left (he x hx) (abs_nonneg t)
  have h₃ : 0 ≤ ∑ s, φ x s ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  simp only
  nlinarith

/-! ### The gap near a quadratic model -/

/-- The partial derivatives of the translated quadratic model `y ↦ ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` are
`aᵢ (xᵢ - pᵢ)`. -/
private theorem fderiv_diagonalQuadratic_comp_sub_apply_single (a p x : ι → ℝ) (i : ι) :
    fderiv ℝ (fun y ↦ diagonalQuadratic a (y - p)) x (Pi.single i 1) = a i * (x i - p i) := by
  rw [fderiv_comp_sub, fderiv_diagonalQuadratic_apply_single, Pi.sub_apply]

/-- The Hessian of the translated quadratic model `y ↦ ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` is `diag(a)`. -/
private theorem fderiv_fderiv_diagonalQuadratic_comp_sub_apply_single (a p x : ι → ℝ) (i j : ι) :
    fderiv ℝ (fderiv ℝ fun y ↦ diagonalQuadratic a (y - p)) x (Pi.single i 1) (Pi.single j 1) =
      if i = j then a i else 0 := by
  have h : fderiv ℝ (fun y ↦ diagonalQuadratic a (y - p)) =
      fun y ↦ fderiv ℝ (diagonalQuadratic a) (y - p) := funext fun y ↦ fderiv_comp_sub p
  rw [h, fderiv_comp_sub, fderiv_fderiv_diagonalQuadratic_apply_single_single]

/-- **The harmonic-oscillator gap near a quadratic model.** Let `φ` be a compactly supported `C²`
form and `f` a function that is `C²` at every point of the support of `φ`. Suppose that wherever `φ`
does not vanish, the gradient of `f` is at least that of the quadratic model
`y ↦ ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2`, that is `∑ᵢ aᵢ² (xᵢ - pᵢ)² ≤ |df(x)|²`, and the Hessian of `f` is within
`e` of `diag(a)`, that is `∑_{i,j} |∂ᵢ∂ⱼf(x) - aᵢ δᵢⱼ| ≤ e`. If `c ≤ |aᵢ|` for every `i` and
`t ≥ 0`, then

`2 t c ‖φ_{≠ s₀}‖² - t e ‖φ‖² ≤ ∫ ⟨Δ_t φ, φ⟩`,

where `φ_{≠ s₀}` omits the component at the multi-index `s₀ = {i | aᵢ < 0}`, whose cardinality is
the Morse index of the model. -/
theorem two_mul_mul_integral_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {a p : ι → ℝ} {t c e : ℝ} (ht : 0 ≤ t)
    (hc : ∀ i, c ≤ |a i|) (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ)
    (hdf : ∀ x, φ x ≠ 0 →
      ∑ i, (a i * (x i - p i)) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (he : ∀ x, φ x ≠ 0 → ∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) - if i = j then a i else 0| ≤ e) :
    2 * t * c * (∫ x, ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a i < 0), φ x s ^ 2) -
        t * e * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have hg : ContDiff ℝ 2 fun y ↦ diagonalQuadratic a (y - p) :=
    (contDiff_diagonalQuadratic a).comp (contDiff_id.sub contDiff_const)
  -- Compare `f` with the translated quadratic model, then use the gap of the model.
  have hcmp :=
    integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul hf
      (fun x _ ↦ hg.contDiffAt) hφ hφc
      (fun x hx ↦ by simpa only [fderiv_diagonalQuadratic_comp_sub_apply_single] using hdf x hx)
      (fun x hx ↦ by
        simpa only [fderiv_fderiv_diagonalQuadratic_comp_sub_apply_single] using he x hx) t
  have hmodel := two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq
    (f := fun y ↦ diagonalQuadratic a (y - p)) (p := p) (b := 0) ht hc hφ hφc
    fun x _ ↦ Eventually.of_forall fun y ↦ (zero_add _).symm
  rw [abs_of_nonneg ht] at hcmp
  linarith

/-! ### Taylor approximation at a critical point -/

section Taylor

variable {f : (ι → ℝ) → ℝ} {a p : ι → ℝ}

/-- At a `C²` critical point `p` with Hessian `∑ᵢ aᵢ vᵢ wᵢ`, the gradient of `f` is
`(aᵢ (xᵢ - pᵢ))ᵢ` up to `o(|x - p|)`: for every `ε > 0`, near `p`,
`∑ᵢ (∂ᵢf(x) - aᵢ (xᵢ - pᵢ))² ≤ ε ∑ᵢ (xᵢ - pᵢ)²`. -/
private theorem eventually_sum_sq_fderiv_apply_single_sub_le (hf : ContDiffAt ℝ 2 f p)
    (hp : fderiv ℝ f p = 0) (ha : ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a i * v i * w i)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 p, ∑ i, (fderiv ℝ f x (Pi.single i 1) - a i * (x i - p i)) ^ 2 ≤
      ε * ∑ i, (x i - p i) ^ 2 := by
  have hd : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) p) p :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  set n : ℝ := (Fintype.card ι : ℝ)
  set δ := min 1 (ε / (n + 1))
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hδ : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  have hnδ : n * δ ^ 2 ≤ ε := by
    have h₁ : δ ^ 2 ≤ δ := by nlinarith [min_le_left 1 (ε / (n + 1))]
    have h₂ : (n + 1) * δ ≤ ε := (le_div_iff₀' (by positivity)).1 (min_le_right _ _)
    nlinarith
  filter_upwards [hd.isLittleO.def hδ] with x hx
  rw [hp, sub_zero] at hx
  -- Each coordinate of the remainder is bounded by its norm.
  have hi : ∀ i, (fderiv ℝ f x (Pi.single i 1) - a i * (x i - p i)) ^ 2 ≤
      δ ^ 2 * ‖x - p‖ ^ 2 := by
    intro i
    have hcomp : fderiv ℝ f x (Pi.single i 1) - a i * (x i - p i) =
        (fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) p (x - p)) (Pi.single i 1) := by
      rw [sub_apply, ha]
      simp [Pi.single_apply]
    have h₁ := ((fderiv ℝ f x - fderiv ℝ (fderiv ℝ f) p (x - p)).le_opNorm (Pi.single i 1)).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
    rw [Pi.norm_single, norm_one, mul_one, ← hcomp, Real.norm_eq_abs] at h₁
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h₁ 2
  calc ∑ i, (fderiv ℝ f x (Pi.single i 1) - a i * (x i - p i)) ^ 2
      ≤ ∑ _i : ι, δ ^ 2 * ‖x - p‖ ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = n * δ ^ 2 * ‖x - p‖ ^ 2 := by simp [n, mul_assoc]
    _ ≤ ε * ∑ i, (x i - p i) ^ 2 := by
      -- The sup norm is at most the Euclidean norm.
      have hs : 0 ≤ ∑ i, (x i - p i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
      have h : ‖x - p‖ ≤ √(∑ i, (x i - p i) ^ 2) :=
        (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i ↦ by
          rw [Real.norm_eq_abs, Pi.sub_apply]
          exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j ↦ (x j - p j) ^ 2)
            (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i))
      have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
      rw [Real.sq_sqrt hs] at h'
      exact mul_le_mul hnδ h' (sq_nonneg _) hε.le

/-- At a `C²` critical point `p` with Hessian `∑ᵢ aᵢ vᵢ wᵢ`, where every `|aᵢ| ≥ c > 0`, the
gradient of `f` is at least `θ` times that of the quadratic model near `p` for every `θ² < 1`:
`∑ᵢ (θ aᵢ (xᵢ - pᵢ))² ≤ |df(x)|²`. -/
private theorem eventually_sum_mul_sq_le_sum_fderiv_apply_single_sq (hf : ContDiffAt ℝ 2 f p)
    (hp : fderiv ℝ f p = 0) (ha : ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a i * v i * w i)
    {c : ℝ} (hc : 0 < c) (hca : ∀ i, c ≤ |a i|) {θ : ℝ} (hθ : θ ^ 2 < 1) :
    ∀ᶠ x in 𝓝 p, ∑ i, (θ * a i * (x i - p i)) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 := by
  set η := (1 - θ ^ 2) / 2
  have hη : 0 < η := by simp only [η]; linarith
  filter_upwards [eventually_sum_sq_fderiv_apply_single_sub_le hf hp ha
    (ε := c ^ 2 * η ^ 2) (by positivity)] with x hx
  -- Write `∂ᵢf(x) = Aᵢ + Eᵢ` with `Aᵢ = aᵢ (xᵢ - pᵢ)` the gradient of the model.
  set A : ι → ℝ := fun i ↦ a i * (x i - p i)
  set E : ι → ℝ := fun i ↦ fderiv ℝ f x (Pi.single i 1) - A i
  have hpt : ∀ i, η * (1 - η) * A i ^ 2 - E i ^ 2 ≤ η * fderiv ℝ f x (Pi.single i 1) ^ 2 := by
    intro i
    have h : fderiv ℝ f x (Pi.single i 1) = A i + E i := by simp only [E]; ring
    rw [h]
    nlinarith [sq_nonneg (η * A i + E i), sq_nonneg (E i)]
  -- The remainder is small compared with the gradient of the model.
  have hE : ∑ i, E i ^ 2 ≤ η ^ 2 * ∑ i, A i ^ 2 := by
    refine hx.trans ?_
    rw [mul_comm (c ^ 2), mul_assoc, Finset.mul_sum (s := Finset.univ) (a := c ^ 2)]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ ?_) (sq_nonneg η)
    simp only [A, mul_pow]
    have : c ^ 2 ≤ a i ^ 2 := by
      rw [← sq_abs (a i)]
      exact pow_le_pow_left₀ hc.le (hca i) 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hpt i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hθA : ∑ i, (θ * a i * (x i - p i)) ^ 2 = θ ^ 2 * ∑ i, A i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by simp only [A]; ring
  rw [hθA]
  have hθη : θ ^ 2 = 1 - 2 * η := by simp only [η]; ring
  rw [hθη]
  nlinarith

/-- Near a `C²` critical point `p` with Hessian `∑ᵢ aᵢ vᵢ wᵢ`, where every `|aᵢ| ≥ c > 0`, the
function `f` satisfies the hypotheses of the gap near the weakened quadratic model with
coefficients `θ aᵢ`, `0 ≤ θ < 1`: its gradient is at least that of the model, and its Hessian is
within `η + (1 - θ) ∑ᵢ |aᵢ|` of `diag(θ a)`, for any `η > 0`. -/
private theorem eventually_sum_mul_sq_le_and_sum_sum_abs_sub_le (hf : ContDiffAt ℝ 2 f p)
    (hp : fderiv ℝ f p = 0) (ha : ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a i * v i * w i)
    {c : ℝ} (hc : 0 < c) (hca : ∀ i, c ≤ |a i|) {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ x in 𝓝 p, ∑ i, (θ * a i * (x i - p i)) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 ∧
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        if i = j then θ * a i else 0| ≤ η + (1 - θ) * ∑ i, |a i| := by
  -- The Hessian is continuous at `p`.
  have hcont : ContinuousAt (fun x ↦ ∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1)|) p := by
    have hf₂ := hf.continuousAt_fderiv_fderiv le_rfl
    exact tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
      (((hf₂.clm_apply continuousAt_const).clm_apply continuousAt_const).sub
        continuousAt_const).abs
  filter_upwards [eventually_sum_mul_sq_le_sum_fderiv_apply_single_sq hf hp ha hc hca
    (θ := θ) (by nlinarith), hcont.eventually_lt continuousAt_const (by simpa using hη)]
    with x h₁ h₂
  refine ⟨h₁, ?_⟩
  have hp' : ∀ i j, fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1) =
      if i = j then a i else 0 := fun i j ↦ by
    rw [ha, ← fderiv_fderiv_diagonalQuadratic_apply a 0,
      fderiv_fderiv_diagonalQuadratic_apply_single_single]
  -- The Hessian at `p` is `diag(a)`, at distance `(1 - θ) ∑ᵢ |aᵢ|` from `diag(θ a)`.
  have h₃ : ∀ i, ∑ j, |fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1) -
      if i = j then θ * a i else 0| = (1 - θ) * |a i| := fun i ↦ by
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hp', Ne.symm hj]) (by simp), hp']
    simp only [ite_true]
    rw [← one_sub_mul, abs_mul, abs_of_nonneg (by linarith)]
  calc ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          if i = j then θ * a i else 0|
      ≤ ∑ i, ∑ j, (|fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1)| +
          |fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1) -
            if i = j then θ * a i else 0|) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ abs_sub_le _ _ _
    _ = (∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          fderiv ℝ (fderiv ℝ f) p (Pi.single i 1) (Pi.single j 1)|) +
          (1 - θ) * ∑ i, |a i| := by
        simp only [Finset.sum_add_distrib, h₃, Finset.mul_sum]
    _ ≤ η + (1 - θ) * ∑ i, |a i| := by linarith [h₂]

end Taylor

/-! ### The gap at nondegenerate critical points -/

/-- A factor `θ ∈ [7/8, 1)` so close to `1` that `(1 - θ) S ≤ c / 8`. -/
private theorem exists_le_lt_one_mul_le {S c : ℝ} (hS : 0 ≤ S) (hc : 0 < c) :
    ∃ θ : ℝ, 7 / 8 ≤ θ ∧ θ < 1 ∧ (1 - θ) * S ≤ c / 8 := by
  have hδ : 0 < c / (8 * (S + c)) := by positivity
  refine ⟨1 - c / (8 * (S + c)), ?_, by linarith, ?_⟩
  · have : c / (8 * (S + c)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  · rw [sub_sub_cancel, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- Under the hypotheses of the gap at nondegenerate critical points, there is a radius `r > 0`
that separates the points of `P` and on which the hypotheses of the gap near the weakened model
`θ a p` hold around every `p ∈ P`, with error at most `c / 4` when `(1 - θ) ∑ₚ ∑ᵢ |a p i| ≤ c / 8`.
-/
private theorem exists_pos_forall_mem_ball_and_two_mul_le_dist {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)} (hP : ∀ p ∈ P, fderiv ℝ f p = 0)
    {a : (ι → ℝ) → ι → ℝ}
    (ha : ∀ p ∈ P, ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a p i * v i * w i)
    {c : ℝ} (hc : 0 < c) (hca : ∀ p ∈ P, ∀ i, c ≤ |a p i|) {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ < 1) (hθS : (1 - θ) * ∑ p ∈ P, ∑ i, |a p i| ≤ c / 8) :
    ∃ r > 0, ∀ p ∈ P,
      (∀ x ∈ ball p r, ∑ i, (θ * a p i * (x i - p i)) ^ 2 ≤
        ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 ∧
        ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          if i = j then θ * a p i else 0| ≤ c / 4) ∧
      ∀ q ∈ P, p ≠ q → 2 * r ≤ dist p q := by
  have hr : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ p ∈ P,
      (∀ x ∈ ball p r, ∑ i, (θ * a p i * (x i - p i)) ^ 2 ≤
        ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 ∧
        ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          if i = j then θ * a p i else 0| ≤ c / 4) ∧
      ∀ q ∈ P, p ≠ q → 2 * r ≤ dist p q := by
    rw [eventually_all_finset]
    intro p hp
    refine Eventually.and ?_ ?_
    · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
        (eventually_sum_mul_sq_le_and_sum_sum_abs_sub_le hf.contDiffAt (hP p hp) (ha p hp) hc
          (hca p hp) hθ₀ hθ₁ (η := c / 8) (by positivity))
      -- The cost of the weakening at `p` is at most that over all of `P`.
      have he : (1 - θ) * ∑ i, |a p i| ≤ c / 8 :=
        (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun p ↦ ∑ i, |a p i|)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hp) (by linarith)).trans hθS
      filter_upwards [Ioo_mem_nhdsGT hε] with r hr x hx
      have hx := hball x (ball_subset_ball hr.2.le hx)
      exact ⟨hx.1, by linarith [hx.2]⟩
    · rw [eventually_all_finset]
      intro q _
      by_cases hpq : p = q
      · exact Eventually.of_forall fun _ h ↦ absurd hpq h
      · filter_upwards [Ioo_mem_nhdsGT (half_pos (dist_pos.2 hpq))] with r hr _
        linarith [hr.2]
  obtain ⟨r, hrQ, hr0 : 0 < r⟩ := (hr.and self_mem_nhdsWithin).exists
  exact ⟨r, hr0, hrQ⟩

/-- The gap at one critical point in a degree `m` that is not its Morse index: if the form `ψ`
of degree `m` is supported where `f` satisfies the hypotheses of the gap near the weakened model
`θ a`, with `7/8 ≤ θ ≤ 1` and error at most `c / 4`, then its energy is at least
`3 t c / 2` times its squared norm. -/
private theorem three_div_two_mul_mul_integral_le_of_card_ne
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {ψ : (ι → ℝ) → Finset ι → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) {m : ℕ} (hψm : ∀ x s, ψ x s ≠ 0 → s.card = m) {a p : ι → ℝ}
    (hm : (Finset.univ.filter fun i ↦ a i < 0).card ≠ m) {c θ e t : ℝ}
    (hca : ∀ i, c ≤ |a i|) (hc : 0 < c) (hθ₀ : 7 / 8 ≤ θ) (he : e ≤ c / 4) (ht : 0 ≤ t)
    (hdf : ∀ x, ψ x ≠ 0 →
      ∑ i, (θ * a i * (x i - p i)) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hH : ∀ x, ψ x ≠ 0 → ∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        if i = j then θ * a i else 0| ≤ e) :
    3 / 2 * t * c * ∫ x, ∑ s, ψ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t ψ x s * ψ x s := by
  have hθ : 0 < θ := by linarith
  have hloc := two_mul_mul_integral_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul
    (a := fun i ↦ θ * a i) (p := p) (c := θ * c) ht
    (fun i ↦ by
      rw [abs_mul, abs_of_pos hθ]
      exact mul_le_mul_of_nonneg_left (hca i) hθ.le)
    (fun x _ ↦ hf.contDiffAt) hψ hψc hdf hH
  -- In degree `m`, the component at `{i | θ aᵢ < 0} = {i | aᵢ < 0}` vanishes.
  have hfilt : (Finset.univ.filter fun i ↦ θ * a i < 0) = Finset.univ.filter fun i ↦ a i < 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h' <;> nlinarith
  have herase : ∀ x, ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a i < 0), ψ x s ^ 2 =
      ∑ s, ψ x s ^ 2 := by
    intro x
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (Finset.univ.filter fun i ↦ a i < 0))]
    have : ψ x (Finset.univ.filter fun i ↦ a i < 0) = 0 := by
      by_contra h'
      exact hm (hψm x _ h')
    simp [this]
  simp only [hfilt, herase] at hloc
  have hN : 0 ≤ ∫ x, ∑ s, ψ x s ^ 2 :=
    integral_nonneg fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  -- The gap `2 t θ c ≥ 7 t c / 4` of the model minus the error `t e ≤ t c / 4`.
  have hcoef : 3 / 2 * t * c ≤ 2 * t * (θ * c) - t * e := by
    nlinarith [mul_nonneg (mul_nonneg ht (sub_nonneg.2 hθ₀)) hc.le, mul_nonneg ht (sub_nonneg.2 he)]
  nlinarith [mul_le_mul_of_nonneg_right hcoef hN]

/-- The bound away from the critical points: if `|df|² ≥ c₀` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h` wherever
the form `ψ` does not vanish, and `3 c / 2 + h ≤ t c₀` with `t ≥ 0`, then the energy of `ψ` is at
least `3 t c / 2` times its squared norm. -/
private theorem three_div_two_mul_mul_integral_le_of_le
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {ψ : (ι → ℝ) → Finset ι → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) {c c₀ h t : ℝ} (ht : 0 ≤ t) (htc : 3 / 2 * c + h ≤ t * c₀)
    (hdf : ∀ x, ψ x ≠ 0 → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, ψ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h) :
    3 / 2 * t * c * ∫ x, ∑ s, ψ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t ψ x s * ψ x s := by
  have h₀ := mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul
    (fun x _ ↦ hf.contDiffAt) hψ hψc hdf hh t
  rw [abs_of_nonneg ht] at h₀
  have hcoef : 3 / 2 * t * c ≤ t ^ 2 * c₀ - t * h := by nlinarith
  exact (mul_le_mul_of_nonneg_right hcoef
    (integral_nonneg fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).trans h₀

/-- **The gap of the Witten Laplacian in a degree that is no Morse index, for nondegenerate
critical points.** Let `f` be a `C²` function on `ℝ^ι` and `P` a finite set of critical points of
`f` at which the Hessian is diagonal, `∑ᵢ a p i vᵢ wᵢ`, with every `|a p i| ≥ c > 0`, so that the
Morse index of `p` is the number of negative `a p i`. Suppose that away from every neighbourhood
of `P` the gradient of `f` is bounded below and its Hessian bounded above: for every `ρ > 0` there
are `c₀ > 0` and `h` with `|df|² ≥ c₀` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h` at distance more than `ρ` from
`P`; in particular `P` contains every critical point of `f`. If `m` is not the Morse index of any
`p ∈ P`, then for all large `t` the quadratic form of the Witten Laplacian is at least `t c ‖φ‖²` on
compactly supported `C²` forms `φ` of degree `m`. -/
theorem exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_fderiv_eq_zero
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)}
    (hP : ∀ p ∈ P, fderiv ℝ f p = 0) {a : (ι → ℝ) → ι → ℝ}
    (ha : ∀ p ∈ P, ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a p i * v i * w i)
    {c : ℝ} (hc : 0 < c) (hca : ∀ p ∈ P, ∀ i, c ≤ |a p i|)
    (hdf : ∀ ρ > 0, ∃ c₀ > 0, ∀ x, (∀ p ∈ P, ρ < dist x p) →
      c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ ρ > 0, ∃ h, ∀ x, (∀ p ∈ P, ρ < dist x p) →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    {m : ℕ} (hm : ∀ p ∈ P, (Finset.univ.filter fun i ↦ a p i < 0).card ≠ m) :
    ∃ T, ∀ t, T ≤ t → ∀ φ : (ι → ℝ) → Finset ι → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∀ x s, φ x s ≠ 0 → s.card = m) →
      t * c * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  -- Weaken the models to `θ a p`, at the cost `(1 - θ) ∑ᵢ |a p i| ≤ c / 8` in the Hessian, and
  -- localize at a scale `r` on which the Taylor estimates hold.
  obtain ⟨θ, hθ₀, hθ₁, hθS⟩ := exists_le_lt_one_mul_le (S := ∑ p ∈ P, ∑ i, |a p i|)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hc
  obtain ⟨r, hr0, hrQ⟩ :=
    exists_pos_forall_mem_ball_and_two_mul_le_dist hf hP ha hc hca (by linarith) hθ₁ hθS
  obtain ⟨J₀, J, hJ₀, hJ, hJ1, hJr, hJ₀ρ, hJ₀c, hJc⟩ := exists_sq_add_sum_sq_eq_one
    (half_pos hr0) (half_lt_self hr0) fun p hp q hq hpq ↦ (hrQ p hp).2 q hq hpq
  replace hJ₀ : ContDiff ℝ 2 J₀ := hJ₀.of_le (by simp)
  replace hJ : ∀ p, ContDiff ℝ 2 (J p) := fun p ↦ (hJ p).of_le (by simp)
  obtain ⟨c₀, hc₀, hdf₀⟩ := hdf (r / 2) (half_pos hr0)
  obtain ⟨h, hh₀⟩ := hh (r / 2) (half_pos hr0)
  obtain ⟨K₀, hK₀⟩ :=
    (hJ₀.of_le one_le_two).exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv hJ₀c
  choose K hK using fun p ↦
    ((hJ p).of_le one_le_two).exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv
      ((hJc p).fderiv (𝕜 := ℝ))
  refine ⟨max (max ((3 / 2 * c + h) / c₀) (2 * (K₀ + ∑ p ∈ P, K p) / c)) 0,
    fun t ht φ hφ hφc hφm ↦ ?_⟩
  have ht₀ : 0 ≤ t := (le_max_right _ _).trans ht
  have ht₁ : 3 / 2 * c + h ≤ t * c₀ :=
    (div_le_iff₀ hc₀).1 ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  have ht₂ : 2 * (K₀ + ∑ p ∈ P, K p) ≤ t * c :=
    (div_le_iff₀ hc).1 ((le_max_right _ _).trans ((le_max_left _ _).trans ht))
  have hsupp : ∀ (u : (ι → ℝ) → ℝ) x, (u • φ) x ≠ 0 → u x ≠ 0 ∧ φ x ≠ 0 := fun u x hx ↦
    smul_ne_zero_iff.1 (by simpa only [Pi.smul_apply'] using hx)
  -- IMS localization, with the bound `3 t c / 2` at every piece.
  have key := sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul
    (A := P.insertNone) (J := fun o ↦ o.elim J₀ J) (fun x _ ↦ hf.contDiffAt)
    (by rintro (_ | p) _ x _; exacts [hJ₀.contDiffAt, (hJ p).contDiffAt]) hφ hφc
    (fun x _ ↦ by simpa [Finset.sum_insertNone] using hJ1 x)
    (fun x _ ↦ by
      simpa [Finset.sum_insertNone] using
        add_le_add (hK₀ x) (Finset.sum_le_sum fun p (_ : p ∈ P) ↦ hK p x))
    (t := t) (κ := 3 / 2 * t * c) ?_
  · have hN : 0 ≤ ∫ x, ∑ s, φ x s ^ 2 :=
      integral_nonneg fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    nlinarith
  rintro (_ | p) hp
  · -- Away from `P`, the potential `t² c₀ - t h` is at least `3 t c / 2`.
    exact three_div_two_mul_mul_integral_le_of_le hf (hJ₀.smul hφ) hφc.smul_left ht₀ ht₁
      (fun x hx ↦ hdf₀ x (hJ₀ρ x (hsupp J₀ x hx).1)) (fun x hx ↦ hh₀ x (hJ₀ρ x (hsupp J₀ x hx).1))
  · -- Near `p`, the gap of the weakened model.
    have hp' := Finset.some_mem_insertNone.1 hp
    exact three_div_two_mul_mul_integral_le_of_card_ne hf ((hJ p).smul hφ) hφc.smul_left
      (fun x s hx ↦ hφm x s (right_ne_zero_of_mul hx)) (hm p hp') (hca p hp') hc hθ₀ le_rfl ht₀
      (fun x hx ↦ ((hrQ p hp').1 x (mem_ball.2 (hJr p x (hsupp _ x hx).1))).1)
      (fun x hx ↦ ((hrQ p hp').1 x (mem_ball.2 (hJr p x (hsupp _ x hx).1))).2)

end TauCeti
