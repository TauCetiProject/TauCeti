/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.SquarePartition
public import TauCeti.Analysis.Calculus.WittenLaplacian.Energy
public import TauCeti.Analysis.Calculus.WittenLaplacian.Localization

/-!
# The gap of the Witten Laplacian away from the ground states

Let `f` be a function on `ℝ^ι` whose critical points `p ∈ P` are nondegenerate and, as for a
metric that is Euclidean in Morse charts, have exact quadratic models: near `p`,
`f = f(p) + ∑ᵢ aᵢ (xᵢ - pᵢ)² / 2` with every `|aᵢ| ≥ c > 0`. The number of negative `aᵢ` is the
Morse index of `p` (`TauCeti.morseIndex_diagonalQuadratic`). Suppose also that away from these
points `|df|²` is bounded below by `c₀ > 0` and the Hessian is bounded. This file proves Witten's
localization estimate: for every degree `m` that is not the Morse index of a critical point, the
quadratic form of the Witten Laplacian `Δ_t` (`TauCeti.euclideanWittenLaplacian`) on compactly
supported `C²` forms of degree `m` is at least `(2 t c - K) ‖φ‖²` for large `t`, where `K` depends
only on a partition of unity adapted to `P`
(`TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`).
This gives the linear-in-`t` gap estimate of Witten's proof of the weak Morse inequalities: in such
a degree no form has energy below a multiple of `t`
(`TauCeti.exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`, in
`TauCeti.Analysis.Calculus.WittenLaplacian.Taylor`). In every degree `m` the same bound
`(2 t c - K) ‖φ‖²` holds
for the forms `φ` whose localized pieces `J p φ` at the points `p` of Morse index `m` are
orthogonal to the translated Gaussian ground states of the quadratic models
(`TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_orthogonal`). This is the
gap above the ground states, from which
`TauCeti.Analysis.Calculus.WittenLaplacian.LowEnergy` bounds the dimension of the low-energy forms
of degree `m` by the number of critical points of index `m`.

The proof splits the quadratic form along a partition of unity by squares
`J₀² + ∑ₚ (J p)² = 1` (`TauCeti.exists_sq_add_sum_sq_eq_one`), with `J p` supported where `f` is
the quadratic model at `p` and `J₀` supported where `|df|² ≥ c₀`, by the IMS localization formula
`TauCeti.integral_sum_euclideanWittenLaplacian_mul_eq`, in the form of the lower bound
`TauCeti.sum_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`. The commutator terms
cost a constant `K` independent of `t`.

* **Near a critical point** the Witten Laplacian of `f` agrees with that of the translated
  quadratic model, since it is a local operator
  (`Filter.EventuallyEq.euclideanWittenLaplacian`) commuting with translations
  (`TauCeti.euclideanWittenLaplacian_comp_add_right`). The harmonic-oscillator gap
  `TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul`
  then bounds the part of `J p φ` other than its component at the multi-index
  `s₀(p) = {i | a p i < 0}`, whose cardinality is the Morse index of `p`, by `2 t c`
  (`TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq`).
  If `J p φ` is orthogonal to the translated ground state, the gap of the model above its ground
  state bounds all of `J p φ` by `2 t c`
  (`two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_of_eventuallyEq_of_orthogonal`).
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
instead; `TauCeti.Analysis.Calculus.WittenLaplacian.Taylor` does this in the degrees that are no
Morse index, and recovers the gap for exact quadratic models as a special case. The statements
concern the quadratic form on compactly supported forms, not the spectrum of a self-adjoint
realization of `Δ_t`.

## Main results

* `TauCeti.two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq`:
  the harmonic-oscillator gap for forms supported where `f` is a translated quadratic model.
* `two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_of_eventuallyEq_of_orthogonal`:
  the gap above the ground state for forms supported where `f` is a translated quadratic model.
* `TauCeti.le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`: the localized
  lower bound for the quadratic form of `Δ_t`.
* `TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_orthogonal`: the lower
  bound `(2 t c - K) ‖φ‖²` for forms whose pieces at the critical points of their degree are
  orthogonal to the ground states.
* `TauCeti.mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`:
  the lower bound `(2 t c - K) ‖φ‖²` in a degree that is no Morse index.

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

/-- Let `f` be the translated quadratic model `y ↦ b + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` near every point where
the form `φ` does not vanish. Then the quadratic form of the Witten Laplacian of `f` at `φ` is that
of the model `∑ᵢ aᵢ xᵢ² / 2` at the translated form `φ (· + p)`. -/
private theorem integral_sum_euclideanWittenLaplacian_mul_eq_diagonalQuadratic
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {a p : ι → ℝ} {b : ℝ} (t : ℝ)
    (hf : ∀ x, φ x ≠ 0 → f =ᶠ[𝓝 x] fun y ↦ b + diagonalQuadratic a (y - p)) :
    ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s =
      ∫ x, ∑ s, euclideanWittenLaplacian (diagonalQuadratic a) t (fun y ↦ φ (y + p)) x s *
        φ (x + p) s := by
  set g : (ι → ℝ) → ℝ := fun y ↦ b + diagonalQuadratic a (y - p)
  -- Near every point where `φ` does not vanish, `f` is the translated quadratic model `g`.
  have hfg : ∀ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s =
      ∑ s, euclideanWittenLaplacian g t φ x s * φ x s := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    rw [((hf x hx).euclideanWittenLaplacian (EventuallyEq.refl _ φ) t).eq_of_nhds]
  -- Translating by `p` turns `g` into the model `b + ∑ᵢ aᵢ xᵢ² / 2`.
  have hg : euclideanWittenLaplacian (fun x ↦ g (x + p)) t (fun y ↦ φ (y + p)) =
      euclideanWittenLaplacian (diagonalQuadratic a) t (fun y ↦ φ (y + p)) := by
    simp only [g, add_sub_cancel_right]
    exact congrFun (euclideanWittenLaplacian_const_add b (diagonalQuadratic a) t) _
  rw [integral_congr_ae (Eventually.of_forall hfg), ← hg, euclideanWittenLaplacian_comp_add_right,
    ← integral_add_right_eq_self (fun x ↦ ∑ s, euclideanWittenLaplacian g t φ x s * φ x s) p]

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
  rw [integral_sum_euclideanWittenLaplacian_mul_eq_diagonalQuadratic t hf,
    ← integral_add_right_eq_self
      (fun x ↦ ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a i < 0), φ x s ^ 2) p]
  exact two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_mul
    (μ := volume) ht hc (hφ.comp (contDiff_id.add contDiff_const))
    (hφc.comp_homeomorph (Homeomorph.addRight p))

/-- **The gap above the ground state near a critical point.** Let `φ` be a compactly supported
`C²` form such that, near every point where `φ` does not vanish, `f` is the translated quadratic
model `y ↦ b + ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2`. If `c ≤ |aᵢ|` for every `i`, `t ≥ 0`, and `φ` is orthogonal
to the translated Gaussian ground state `Ψ_{0,s₀}(· - p)` in the degree `s₀ = {i | aᵢ < 0}` of the
Morse index, then the quadratic form of the Witten Laplacian of `f` at `φ` is at least
`2 t c ∫ |φ|²`. -/
theorem
    two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_of_eventuallyEq_of_orthogonal
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {a p : ι → ℝ} {b t c : ℝ} (ht : 0 ≤ t)
    (hc : ∀ i, c ≤ |a i|) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hf : ∀ x, φ x ≠ 0 → f =ᶠ[𝓝 x] fun y ↦ b + diagonalQuadratic a (y - p))
    (horth : ∫ x, ∑ s, diagonalQuadraticWittenEigenform a t 0
      (Finset.univ.filter fun i ↦ a i < 0) (x - p) s * φ x s = 0) :
    2 * t * c * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  rw [← integral_add_right_eq_self _ p] at horth
  simp only [add_sub_cancel_right] at horth
  rw [integral_sum_euclideanWittenLaplacian_mul_eq_diagonalQuadratic t hf,
    ← integral_add_right_eq_self (fun x ↦ ∑ s, φ x s ^ 2) p]
  exact
    two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_diagonalQuadratic_of_orthogonal
    (μ := volume) ht hc (hφ.comp (contDiff_id.add contDiff_const))
    (hφc.comp_homeomorph (Homeomorph.addRight p)) horth

/-! ### Localization -/

/-- The lower bound of IMS localization for the partition of unity `J₀, (J p)_{p ∈ P}`: lower
bounds `B₀` and `B p` for the quadratic forms at the pieces `J₀ φ` and `J p φ` give the lower
bound `B₀ + ∑ₚ B p - K ‖φ‖²` at `φ`. -/
private theorem add_sum_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {P : Finset (ι → ℝ)} {J₀ : (ι → ℝ) → ℝ}
    {J : (ι → ℝ) → (ι → ℝ) → ℝ} {t K B₀ : ℝ} {B : (ι → ℝ) → ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hJ₀ : ContDiff ℝ 2 J₀) (hJ : ∀ p ∈ P, ContDiff ℝ 2 (J p))
    (hJ1 : ∀ x, φ x ≠ 0 → J₀ x ^ 2 + ∑ p ∈ P, J p x ^ 2 = 1)
    (hK : ∀ x, φ x ≠ 0 → ∑ i, fderiv ℝ J₀ x (Pi.single i 1) ^ 2 +
      ∑ p ∈ P, ∑ i, fderiv ℝ (J p) x (Pi.single i 1) ^ 2 ≤ K)
    (h₀ : B₀ ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t (J₀ • φ) x s * (J₀ • φ) x s)
    (hB : ∀ p ∈ P, B p ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t (J p • φ) x s * (J p • φ) x s) :
    B₀ + ∑ p ∈ P, B p - K * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  -- Index the partition of unity by `Option (ι → ℝ)`, with `none` for `J₀`.
  simpa [Finset.sum_insertNone] using
    sum_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul (A := P.insertNone)
      (J := fun o ↦ o.elim J₀ J) (B := fun o ↦ o.elim B₀ B) hf (by
        rintro (_ | p) hp x -
        · exact hJ₀.contDiffAt
        · exact (hJ p (Finset.some_mem_insertNone.1 hp)).contDiffAt) hφ hφc
      (fun x hx ↦ by simpa [Finset.sum_insertNone] using hJ1 x hx)
      (fun x hx ↦ by simpa [Finset.sum_insertNone] using hK x hx) (by
        rintro (_ | p) hp
        · exact h₀
        · exact hB p (Finset.some_mem_insertNone.1 hp))

/-- Away from the critical points, where `|df|² ≥ c₀` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h`, the potential
`t² |df|² - t |Hess f|` bounds the quadratic form at the piece `J₀ φ` below by `t κ ‖J₀ φ‖²` for
`t ≥ 0` and `κ + h ≤ t c₀`. -/
private theorem mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_smul_mul
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {J₀ : (ι → ℝ) → ℝ} {t c₀ h κ : ℝ}
    (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hJ₀ : ContDiff ℝ 2 J₀)
    (hc₀ : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    (ht : 0 ≤ t) (htc : κ + h ≤ t * c₀) :
    t * κ * ∫ x, ∑ s, (J₀ • φ) x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t (J₀ • φ) x s * (J₀ • φ) x s :=
  mul_mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul_of_add_le_mul
    (φ := J₀ • φ) (fun x hx ↦ hf x (tsupport_smul_subset_right J₀ φ hx)) (hJ₀.smul hφ)
    hφc.smul_left
    (fun x hx ↦ hc₀ x (Function.support_smul_subset_left J₀ φ hx)
      (Function.support_smul_subset_right J₀ φ hx))
    (fun x hx ↦ hh x (Function.support_smul_subset_left J₀ φ hx)
      (Function.support_smul_subset_right J₀ φ hx)) ht htc

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
  -- Away from the critical points, the coefficient `t (t c₀ - h) = t² c₀ - t h`.
  have h₀ := mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_smul_mul (κ := t * c₀ - h)
    hf hφ hφc hJ₀ hc₀ hh ht (sub_add_cancel _ _).le
  have key := add_sum_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul hf hφ hφc hJ₀
    hJ hJ1 hK h₀ fun p hp ↦
      two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq ht
        (hc p hp) ((hJ p hp).smul hφ) hφc.smul_left fun x hx ↦
        hmodel p hp x (Function.support_smul_subset_left (J p) φ hx)
  rw [← Finset.mul_sum] at key
  linarith

/-! ### The gap above the ground states -/

/-- The harmonic-oscillator gap at one critical point, for a form of degree `m`: if `φ` is
supported where `f` is the translated quadratic model at `p`, then the quadratic form of the
Witten Laplacian at `φ` is at least `2 t c ‖φ‖²` when either `m` is not the Morse index of `p`, or
`φ` is orthogonal to the translated ground state. -/
private theorem two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_of_degree
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {a p : ι → ℝ} {b t c : ℝ} {m : ℕ}
    (ht : 0 ≤ t) (hc : ∀ i, c ≤ |a i|) (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφm : ∀ x s, φ x s ≠ 0 → s.card = m)
    (hf : ∀ x, φ x ≠ 0 → f =ᶠ[𝓝 x] fun y ↦ b + diagonalQuadratic a (y - p))
    (horth : (Finset.univ.filter fun i ↦ a i < 0).card = m →
      ∫ x, ∑ s, diagonalQuadraticWittenEigenform a t 0
        (Finset.univ.filter fun i ↦ a i < 0) (x - p) s * φ x s = 0) :
    2 * t * c * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  by_cases hm : (Finset.univ.filter fun i ↦ a i < 0).card = m
  · exact
      two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_of_eventuallyEq_of_orthogonal
      ht hc hφ hφc hf (horth hm)
  -- In a degree other than the Morse index, the component at `{i | a i < 0}` vanishes.
  simpa only [sum_erase_sq_eq_sum_sq_of_card_ne hφm hm] using
    two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq ht hc hφ
      hφc hf

/-- **The gap of the Witten Laplacian above the ground states.** Under the hypotheses of
`TauCeti.le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`, let `φ` have
degree `m`, and suppose that for every `p ∈ P` of Morse index `m`, the number of negative
coefficients `a p i`, the localized piece `J p φ` is orthogonal to the translated Gaussian ground
state `Ψ_{0,s₀(p)}(· - p)` of the quadratic model at `p`. If `t ≥ 0` and `t c₀ ≥ 2 c + h`, then
`(2 t c - K) ‖φ‖² ≤ ∫ ⟨Δ_t φ, φ⟩`. -/
theorem mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_orthogonal
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
    (horth : ∀ p ∈ P, (Finset.univ.filter fun i ↦ a p i < 0).card = m →
      ∫ x, ∑ s, diagonalQuadraticWittenEigenform (a p) t 0
        (Finset.univ.filter fun i ↦ a p i < 0) (x - p) s * (J p • φ) x s = 0)
    (hc₀ : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hh : ∀ x, J₀ x ≠ 0 → φ x ≠ 0 →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    (ht : 0 ≤ t) (htc : 2 * c + h ≤ t * c₀) :
    (2 * t * c - K) * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  -- IMS localization: away from the critical points `t² c₀ - t h ≥ 2 t c` bounds `J₀ φ` below,
  -- and at each critical point the harmonic-oscillator gap bounds `J p φ` below.
  refine sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one
    (κ := 2 * t * c) hf (fun x _ ↦ hJ₀.contDiffAt) (fun p hp x _ ↦ (hJ p hp).contDiffAt) hφ hφc
    hJ1 hK ?_ fun p hp ↦
      two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_of_degree ht (hc p hp)
        ((hJ p hp).smul hφ) hφc.smul_left (fun x s hx ↦ hφm x s (right_ne_zero_of_mul hx))
        (fun x hx ↦ hmodel p hp x (Function.support_smul_subset_left (J p) φ hx)) (horth p hp)
  rw [show 2 * t * c = t * (2 * c) by ring]
  exact mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_smul_mul hf hφ hφc hJ₀ hc₀ hh ht
    htc

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
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s :=
  mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_orthogonal hf hφ hφc hφm hJ₀ hJ
    hJ1 hK hmodel hc (fun p hp hpm ↦ absurd hpm (hm p hp)) hc₀ hh ht htc

end TauCeti
