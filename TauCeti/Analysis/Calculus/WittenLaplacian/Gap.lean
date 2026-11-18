/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.SquarePartition
public import TauCeti.Analysis.Calculus.WittenLaplacian.Energy
public import TauCeti.Analysis.Calculus.WittenLaplacian.Localization
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The gap of the Witten Laplacian in degrees without critical points

Let `f` be a function on `ℝ^ι` whose critical points `p ∈ P` are nondegenerate and, as for a
metric that is Euclidean in Morse charts, have exact quadratic models: near `p`,
`f = f(p) + ∑ᵢ aᵢ (xᵢ - pᵢ)² / 2` with every `|aᵢ| ≥ c > 0`. The number of negative `aᵢ` is the
Morse index of `p` (`TauCeti.morseIndex_diagonalQuadratic`). Suppose also that away from these
points `|df|²` is bounded below by `c₀ > 0` and the Hessian is bounded. This file proves Witten's
localization estimate: for every degree `m` that is not the Morse index of a critical point, the
quadratic form of the Witten Laplacian `Δ_t` (`TauCeti.euclideanWittenLaplacian`) on compactly
supported `C²` forms of degree `m` is at least `t c ‖φ‖²` for all large `t`
(`TauCeti.exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`). This is the
linear-in-`t` gap estimate of Witten's proof of the weak Morse inequalities: in such a degree no
form has energy below a multiple of `t`. The other analytic half, that in a degree `k` the
low-energy forms span a space of dimension at most the number of critical points of index `k`, is
not proved here.

The proof splits the quadratic form along a partition of unity by squares
`J₀² + ∑ₚ (J p)² = 1` (`TauCeti.exists_sq_add_sum_sq_eq_one`), with `J p` supported where `f` is
the quadratic model at `p` and `J₀` supported where `|df|² ≥ c₀`, by the IMS localization formula
`TauCeti.integral_sum_euclideanWittenLaplacian_mul_eq`. The commutator terms cost a constant `K`
independent of `t`.

* **Near a critical point** the Witten Laplacian of `f` agrees with that of the translated
  quadratic model, since it is a local operator
  (`Filter.EventuallyEq.euclideanWittenLaplacian`) commuting with translations
  (`TauCeti.euclideanWittenLaplacian_comp_add_right`). The harmonic-oscillator gap
  `TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`
  then bounds the part of `J p φ` other than its component at the multi-index
  `s₀(p) = {i | a p i < 0}`, whose cardinality is the Morse index of `p`, by `2 t c`
  (`TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq`).
* **Away from the critical points** the quadratic form of `J₀ φ` is at least `t² c₀ - t h`
  times its squared norm, by
  `TauCeti.mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul`.

Together these give, for every compactly supported `C²` form `φ` and `t ≥ 0`, a lower bound for
`∫ ⟨Δ_t φ, φ⟩` by `2 t c ∑ₚ ‖(J p φ)_{≠ s₀(p)}‖² + (t² c₀ - t h) ‖J₀ φ‖² - K ‖φ‖²`
(`TauCeti.le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`), where
`(J p φ)_{≠ s₀(p)}` omits the single component indexed by the multi-index `s₀(p)`. For a form of
degree `m` that is no Morse index this component vanishes, and once `t c₀ ≥ 2 c + h` the bound
becomes `(2 t c - K) ‖φ‖²`
(`TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`).

The exact quadratic models are the Euclidean form of the standard metrics near critical points.
For a general function, the Taylor remainder of the Hessian approximation has to be estimated
instead; that is not done here. The statements concern the quadratic form on compactly supported
forms, not the spectrum of a self-adjoint realization of `Δ_t`.

## Main results

* `TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq`:
  the harmonic-oscillator gap for forms supported where `f` is a translated quadratic model.
* `TauCeti.le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`: the localized
  lower bound for the quadratic form of `Δ_t`.
* `TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`:
  the lower bound `(2 t c - K) ‖φ‖²` in a degree that is no Morse index.
* `TauCeti.exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`: the gap
  `t c ‖φ‖²` for large `t` in a degree that is no Morse index.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Texts and
  Monographs in Physics, Springer (1987), Chapter 11 (Witten's proof of the Morse inequalities,
  by IMS localization around the critical points).
* B. Helffer and J. Sjöstrand, *Puits multiples en mécanique semi-classique IV: étude du
  complexe de Witten*, Comm. Partial Differential Equations **10** (1985), 245–340.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-! ### The quadratic model near one point -/

/-- **The harmonic-oscillator gap near a critical point.** Let `φ` be a compactly supported `C²`
form such that, near every point where `φ` does not vanish, `f` is the translated quadratic model
`y ↦ b + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2`. If `c ≤ |aᵢ|` for every `i` and `t ≥ 0`, the part of `φ` other than
its component at the multi-index `s₀ = {i | aᵢ < 0}`, whose cardinality is the Morse index,
contributes at least `2 t c` times its squared norm to the quadratic form of the Witten Laplacian
of `f`. -/
theorem two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {a p : ι → ℝ} {b t c : ℝ} (ht : 0 ≤ t)
    (hc : ∀ i, c ≤ |a i|) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hf : ∀ x, φ x ≠ 0 → f =ᶠ[𝓝 x] fun y ↦ b + diagonalQuadratic a (y - p)) :
    2 * t * c *
        ∫ x, ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a i < 0), φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  set g : (ι → ℝ) → ℝ := fun y ↦ b + diagonalQuadratic a (y - p)
  set ψ : (ι → ℝ) → Finset ι → ℝ := fun x ↦ φ (x + p)
  -- Near every point where `φ` does not vanish, `f` is the translated quadratic model `g`.
  have hfg : ∀ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s =
      ∑ s, euclideanWittenLaplacian g t φ x s * φ x s := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    rw [((hf x hx).euclideanWittenLaplacian (EventuallyEq.refl _ φ) t).eq_of_nhds]
  -- Translating by `p` turns `g` into the model `b + ∑ᵢ aᵢ xᵢ² / 2` and `φ` into `ψ`.
  have hg : euclideanWittenLaplacian (fun x ↦ g (x + p)) t ψ =
      euclideanWittenLaplacian (diagonalQuadratic a) t ψ := by
    simp only [g, add_sub_cancel_right]
    exact congrFun (euclideanWittenLaplacian_const_add b (diagonalQuadratic a) t) ψ
  have hψ : ContDiff ℝ 2 ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.addRight p)
  have key := two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul
    (μ := volume) ht hc hψ hψc
  rw [← hg, euclideanWittenLaplacian_comp_add_right] at key
  rw [integral_congr_ae (Eventually.of_forall hfg),
    ← integral_add_right_eq_self (fun x ↦ ∑ s, euclideanWittenLaplacian g t φ x s * φ x s) p,
    ← integral_add_right_eq_self
      (fun x ↦ ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a i < 0), φ x s ^ 2) p]
  exact key

/-! ### Localization -/

/-- **Witten's localization estimate.** Let `φ` be a compactly supported `C²` form, `f` a function
that is `C²` on the support of `φ`, and `J₀`, `J p` (`p ∈ P`) `C²` functions with
`J₀² + ∑ₚ (J p)² = 1` and `∑ᵢ (∂ᵢJ₀)² + ∑ₚ ∑ᵢ (∂ᵢ J p)² ≤ K` wherever `φ` does not vanish.
Suppose that near every point where `J p` does not vanish, `f` is the translated quadratic model
`y ↦ b p + ∑ᵢ a p i (yᵢ - pᵢ)² / 2` with every `|a p i| ≥ c`, and that `|df|² ≥ c₀` and
`∑_{i,j} |∂ᵢ∂ⱼf| ≤ h` wherever `J₀ φ` does not vanish. Then for `t ≥ 0`

`2 t c ∑ₚ ‖(J p φ)_{≠ s₀(p)}‖² + (t² c₀ - t h) ‖J₀ φ‖² - K ‖φ‖² ≤ ∫ ⟨Δ_t φ, φ⟩`,

where `(J p φ)_{≠ s₀(p)}` omits the component at the multi-index `s₀(p) = {i | a p i < 0}`, whose
cardinality is the Morse index of `p`, and `‖ψ‖² = ∫ ∑ s, ψ_s²`. -/
theorem le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one {f : (ι → ℝ) → ℝ}
    {φ : (ι → ℝ) → Finset ι → ℝ} {P : Finset (ι → ℝ)} {J₀ : (ι → ℝ) → ℝ} {J : (ι → ℝ) → (ι → ℝ) → ℝ}
    {a : (ι → ℝ) → ι → ℝ} {b : (ι → ℝ) → ℝ} {t c c₀ h K : ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hJ₀ : ContDiff ℝ 2 J₀) (hJ : ∀ p ∈ P, ContDiff ℝ 2 (J p))
    (hJ1 : ∀ x, φ x ≠ 0 → J₀ x ^ 2 + ∑ p ∈ P, J p x ^ 2 = 1)
    (hK : ∀ x, φ x ≠ 0 → ∑ i, fderiv ℝ J₀ x (Pi.single i 1) ^ 2 +
      ∑ p ∈ P, ∑ i, fderiv ℝ (J p) x (Pi.single i 1) ^ 2 ≤ K)
    (hmodel : ∀ p ∈ P, ∀ x, J p x ≠ 0 →
      f =ᶠ[𝓝 x] fun y ↦ b p + diagonalQuadratic (a p) (y - p))
    (hc : ∀ p ∈ P, ∀ i, c ≤ |a p i|)
    (hc₀ : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    (ht : 0 ≤ t) :
    2 * t * c * (∑ p ∈ P, ∫ x, ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a p i < 0),
        (J p • φ) x s ^ 2) +
      (t ^ 2 * c₀ - t * h) * (∫ x, ∑ s, (J₀ • φ) x s ^ 2) - K * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  -- The partition of unity `J₀, (J p)_{p ∈ P}`, indexed by `Option (ι → ℝ)`.
  set J' : Option (ι → ℝ) → (ι → ℝ) → ℝ := fun o ↦ o.elim J₀ J
  have hJ' : ∀ o ∈ P.insertNone, ContDiff ℝ 2 (J' o) := by
    rintro (_ | p) hp
    · exact hJ₀
    · exact hJ p (Finset.some_mem_insertNone.1 hp)
  have hims := integral_sum_euclideanWittenLaplacian_mul_eq (A := P.insertNone) (J := J') hf
    (fun o ho x _ ↦ (hJ' o ho).contDiffAt) hφ hφc
    (fun x hx ↦ by simpa [J', Finset.sum_insertNone] using hJ1 x hx) t
  simp only [J', Finset.sum_insertNone, Option.elim_none, Option.elim_some] at hims
  rw [hims]
  -- Each piece of the partition is bounded below.
  have hsmul_ne : ∀ (u : (ι → ℝ) → ℝ) x, (u • φ) x ≠ 0 → u x ≠ 0 ∧ φ x ≠ 0 := fun u x hx ↦
    smul_ne_zero_iff.1 (by simpa only [Pi.smul_apply'] using hx)
  have h₀ := mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul
    (φ := J₀ • φ) (fun x hx ↦ hf x (tsupport_smul_subset_right J₀ φ hx)) (hJ₀.smul hφ)
    hφc.smul_left (fun x hx ↦ hc₀ x (hsmul_ne J₀ x hx).1 (hsmul_ne J₀ x hx).2)
    (fun x hx ↦ hh x (hsmul_ne J₀ x hx).1 (hsmul_ne J₀ x hx).2) t
  rw [abs_of_nonneg ht] at h₀
  have hP : ∀ p ∈ P, 2 * t * c *
      ∫ x, ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a p i < 0), (J p • φ) x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t (J p • φ) x s * (J p • φ) x s := fun p hp ↦
    two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq ht
      (hc p hp) ((hJ p hp).smul hφ) hφc.smul_left
      fun x hx ↦ hmodel p hp x (hsmul_ne (J p) x hx).1
  -- The localization error is at most `K ∫ |φ|²`.
  have herr : ∫ x, (∑ i, fderiv ℝ J₀ x (Pi.single i 1) ^ 2 +
      ∑ p ∈ P, ∑ i, fderiv ℝ (J p) x (Pi.single i 1) ^ 2) * ∑ s, φ x s ^ 2 ≤
      K * ∫ x, ∑ s, φ x s ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x ↦ ?_)
      (hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl continuousOn_const)
      (Eventually.of_forall fun x ↦ ?_)
    · exact mul_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
        (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    · by_cases hx : φ x = 0
      · simp [hx]
      exact mul_le_mul_of_nonneg_right (hK x hx) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have := Finset.sum_le_sum hP
  rw [← Finset.mul_sum] at this
  linarith

/-! ### The gap in degrees with no critical point -/

/-- **The Witten Laplacian in a degree that is no Morse index.** Under the hypotheses of
`TauCeti.le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`, let `φ` have
degree `m`, where `m` is not the number of negative coefficients `a p i`, the Morse index, of any
`p ∈ P`. If `t ≥ 0` and `t c₀ ≥ 2 c + h`, then `(2 t c - K) ‖φ‖² ≤ ∫ ⟨Δ_t φ, φ⟩`. -/
theorem mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {P : Finset (ι → ℝ)} {J₀ : (ι → ℝ) → ℝ}
    {J : (ι → ℝ) → (ι → ℝ) → ℝ} {a : (ι → ℝ) → ι → ℝ} {b : (ι → ℝ) → ℝ} {t c c₀ h K : ℝ}
    {m : ℕ} (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφm : ∀ x s, φ x s ≠ 0 → s.card = m) (hJ₀ : ContDiff ℝ 2 J₀)
    (hJ : ∀ p ∈ P, ContDiff ℝ 2 (J p))
    (hJ1 : ∀ x, φ x ≠ 0 → J₀ x ^ 2 + ∑ p ∈ P, J p x ^ 2 = 1)
    (hK : ∀ x, φ x ≠ 0 → ∑ i, fderiv ℝ J₀ x (Pi.single i 1) ^ 2 +
      ∑ p ∈ P, ∑ i, fderiv ℝ (J p) x (Pi.single i 1) ^ 2 ≤ K)
    (hmodel : ∀ p ∈ P, ∀ x, J p x ≠ 0 →
      f =ᶠ[𝓝 x] fun y ↦ b p + diagonalQuadratic (a p) (y - p))
    (hc : ∀ p ∈ P, ∀ i, c ≤ |a p i|)
    (hm : ∀ p ∈ P, (Finset.univ.filter fun i ↦ a p i < 0).card ≠ m)
    (hc₀ : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    (ht : 0 ≤ t) (htc : 2 * c + h ≤ t * c₀) :
    (2 * t * c - K) * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have hloc := le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one hf hφ hφc
    hJ₀ hJ hJ1 hK hmodel hc hc₀ hh ht
  have hsq : ∀ (u : (ι → ℝ) → ℝ) x, ∑ s, (u • φ) x s ^ 2 = u x ^ 2 * ∑ s, φ x s ^ 2 := by
    intro u x
    simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  -- In degree `m`, the omitted component at the multi-index `{i | a p i < 0}` vanishes.
  have herase : ∀ p ∈ P, ∀ x,
      ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a p i < 0), (J p • φ) x s ^ 2 =
        J p x ^ 2 * ∑ s, φ x s ^ 2 := by
    intro p hp x
    rw [Finset.sum_erase _ ?_, hsq]
    have : φ x (Finset.univ.filter fun i ↦ a p i < 0) = 0 := by
      by_contra h'
      exact hm p hp (hφm x _ h')
    simp [this]
  rw [Finset.sum_congr rfl fun p hp ↦ integral_congr_ae (Eventually.of_forall (herase p hp))]
    at hloc
  simp only [hsq] at hloc
  -- The pieces `‖J₀ φ‖²` and `‖J p φ‖²` add up to `‖φ‖²`.
  have hint : ∀ u : (ι → ℝ) → ℝ, Continuous u →
      Integrable fun x ↦ u x ^ 2 * ∑ s, φ x s ^ 2 := fun u hu ↦
    hφ.continuous.integrable_mul_sum_sq_of_continuousOn hφc subset_rfl (hu.pow 2).continuousOn
  have hN : (∫ x, J₀ x ^ 2 * ∑ s, φ x s ^ 2) + ∑ p ∈ P, ∫ x, J p x ^ 2 * ∑ s, φ x s ^ 2 =
      ∫ x, ∑ s, φ x s ^ 2 := by
    rw [← integral_finsetSum _ fun p hp ↦ hint _ (hJ p hp).continuous,
      ← integral_add (hint _ hJ₀.continuous) (integrable_finsetSum _ fun p hp ↦
        hint _ (hJ p hp).continuous)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    beta_reduce
    by_cases hx : φ x = 0
    · simp [hx]
    rw [← Finset.sum_mul, ← add_mul, hJ1 x hx, one_mul]
  have h₁ : 0 ≤ (t ^ 2 * c₀ - t * h - 2 * t * c) * ∫ x, J₀ x ^ 2 * ∑ s, φ x s ^ 2 :=
    mul_nonneg (by nlinarith) (integral_nonneg fun x ↦
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
  have h₂ := congrArg (2 * t * c * ·) hN
  simp only [mul_add] at h₂
  linarith

/-- **The gap of the Witten Laplacian in a degree that is no Morse index.** Let `f` be a `C²`
function on `ℝ^ι` and `P` a finite set of points at mutual distance at least `2 r`. Suppose that
on the ball of radius `r` around each `p ∈ P`, `f` is the quadratic model
`y ↦ f p + ∑ᵢ a p i (yᵢ - pᵢ)² / 2` with every `|a p i| ≥ c > 0`, so that `p` is a nondegenerate
critical point whose Morse index is the number of negative `a p i`, and that outside the balls of
radius `ρ < r` around the points of `P`, `|df|² ≥ c₀ > 0` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h`. If `m` is not
the Morse index of any `p ∈ P`, then for all large `t` the quadratic form of the Witten Laplacian
is at least `t c ‖φ‖²` on compactly supported `C²` forms `φ` of degree `m`. -/
theorem exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)} {ρ r : ℝ} (hρ : 0 < ρ)
    (hρr : ρ < r) (hP : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → 2 * r ≤ dist p q) {a : (ι → ℝ) → ι → ℝ}
    (hfa : ∀ p ∈ P, EqOn f (fun y ↦ f p + diagonalQuadratic (a p) (y - p)) (ball p r))
    {c : ℝ} (hc : 0 < c) (hca : ∀ p ∈ P, ∀ i, c ≤ |a p i|) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdf : ∀ x, (∀ p ∈ P, ρ < dist x p) → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    {h : ℝ} (hh : ∀ x, (∀ p ∈ P, ρ < dist x p) →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    {m : ℕ} (hm : ∀ p ∈ P, (Finset.univ.filter fun i ↦ a p i < 0).card ≠ m) :
    ∃ T, ∀ t, T ≤ t → ∀ φ : (ι → ℝ) → Finset ι → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∀ x s, φ x s ≠ 0 → s.card = m) →
      t * c * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  obtain ⟨J₀, J, hJ₀, hJ, hJ1, hJr, hJ₀ρ, hJ₀c, hJc⟩ := exists_sq_add_sum_sq_eq_one hρ hρr hP
  obtain ⟨K₀, hK₀⟩ :=
    (hJ₀.of_le (by simp)).exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv hJ₀c
  choose K hK using fun p ↦
    ((hJ p).of_le (by simp)).exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv
      ((hJc p).fderiv (𝕜 := ℝ))
  refine ⟨max ((2 * c + h) / c₀) ((K₀ + ∑ p ∈ P, K p) / c), fun t ht φ hφ hφc hφm ↦ ?_⟩
  have ht₁ : 2 * c + h ≤ t * c₀ := (div_le_iff₀ hc₀).1 ((le_max_left _ _).trans ht)
  have ht₂ : K₀ + ∑ p ∈ P, K p ≤ t * c := (div_le_iff₀ hc).1 ((le_max_right _ _).trans ht)
  have ht₀ : 0 ≤ t := by
    have : 0 ≤ K₀ := ((hK₀ 0).trans' (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    have : 0 ≤ ∑ p ∈ P, K p := Finset.sum_nonneg fun p _ ↦
      (hK p 0).trans' (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    nlinarith
  have key := mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one
    (fun x _ ↦ hf.contDiffAt) hφ hφc hφm (hJ₀.of_le (by simp)) (fun p _ ↦ (hJ p).of_le (by simp))
    (fun x _ ↦ hJ1 x) (fun x _ ↦ add_le_add (hK₀ x) (Finset.sum_le_sum fun p _ ↦ hK p x))
    (fun p hp x hx ↦ eventuallyEq_of_mem (isOpen_ball.mem_nhds (hJr p x hx)) (hfa p hp)) hca hm
    (fun x hx _ ↦ hdf x (hJ₀ρ x hx)) (fun x hx _ ↦ hh x (hJ₀ρ x hx)) ht₀ ht₁
  have hN : 0 ≤ ∫ x, ∑ s, φ x s ^ 2 :=
    integral_nonneg fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith

end TauCeti
