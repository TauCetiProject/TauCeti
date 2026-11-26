/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Liouville.Green
import TauCeti.Analysis.ODE.Liouville.Transformation
import TauCeti.Order.Monotone.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Liouville–Green theorem on an arbitrary open interval

Let `I = (a₁, a₂)` be an open interval of `ℝ`, with `-∞ ≤ a₁ < a₂ ≤ ∞`, let `f` be positive and
`C²` and `g` continuous on `I`, let `ξ` be a primitive of `f^{1/2}` there, and let

  `Φ = f^{-1/4} (f^{-1/4})'' - g f^{-1/2}`

be the error-control function. The equation `w'' = (f + g) w` has two Liouville–Green
solutions, each controlled at one end of `I`:

* if `Φ` is integrable on `(x, a₂)` for every `x ∈ I`, there is a solution
  `w₂ = f^{-1/4} e^{-ξ} (1 + ε₂)` with, for `V₂(x) = ∫ₓ^{a₂} |Φ|`,
  `|ε₂(x)| ≤ exp(V₂(x) / 2) - 1` and `f^{-1/2}(x) |ε₂'(x)| / 2 ≤ exp(V₂(x) / 2) - 1`
  (`TauCeti.exists_liouvilleGreen_right`);
* if `Φ` is integrable on `(a₁, x)` for every `x ∈ I`, there is a solution
  `w₁ = f^{-1/4} e^{ξ} (1 + ε₁)` with the same bounds for `V₁(x) = ∫_{a₁}^x |Φ|`
  (`TauCeti.exists_liouvilleGreen_left`).

This is DLMF 2.7.20–2.7.25 (Olver, Chapter 6, Theorem 2.1) in full generality. The interval is
given as an open, order-connected set `I`, and the integrals over `(x, a₂)` and `(a₁, x)` are
written as integrals over `Ioi x ∩ I` and `Iio x ∩ I`. The case `I = (a, ∞)` of the first
statement is `TauCeti.exists_liouvilleGreen_atTop`.

## Proof

Every case is reduced to `TauCeti.exists_liouvilleGreen_atTop` by a change of the independent
variable. If `x = φ(t)` is an increasing `C³` bijection from `J` onto `I` and `u = φ'^{-1/2}`,
then `w` solves `w'' = (f + g) w` on `I` exactly when `W = u · w ∘ φ` solves
`W'' = (F + G) W` on `J`, with `F = φ'² f ∘ φ` and `G = φ'² g ∘ φ + u''/u`, because
`(u · h ∘ φ)'' = u'' · h ∘ φ + u φ'² · h'' ∘ φ` for every `C²` function `h`. The same identity,
applied to `h = f^{-1/4}`, shows that the error-control function of the new equation is
`φ' · Φ ∘ φ`: the differential `Φ(x) dx` is invariant, so the variations `V` agree, and so do the
relative errors `ε`. The reductions use `x = b - 1/t` from `(c, ∞)` when `I` is bounded above by
`b`, and `x = log t` from `(0, ∞)` when `I = ℝ`; the left end is the right end of the reflected
interval `-I`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §2.
* NIST Digital Library of Mathematical Functions, §2.7(iii), equations (2.7.20)–(2.7.25),
  <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Set MeasureTheory
open scoped Topology

namespace TauCeti

/-- The right-end Liouville–Green theorem on `I`, for all admissible data. -/
private def LiouvilleGreenRight (I : Set ℝ) : Prop :=
  ∀ ⦃f ξ : ℝ → ℝ⦄ ⦃g Φ : ℝ → ℂ⦄, ContDiffOn ℝ 2 f I → (∀ x ∈ I, 0 < f x) → ContinuousOn g I →
    (∀ x ∈ I, HasDerivAt ξ (√(f x)) x) →
    (∀ x ∈ I, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x)) →
    (∀ x ∈ I, IntegrableOn Φ (Ioi x ∩ I)) →
    ∃ w ε : ℝ → ℂ, ContDiffOn ℝ 2 w I ∧ DifferentiableOn ℝ ε I ∧
      ∀ x ∈ I, iteratedDeriv 2 w x = (f x + g x) * w x ∧
        w x = ↑(f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x)) * (1 + ε x) ∧
        ‖ε x‖ ≤ Real.exp ((∫ v in Ioi x ∩ I, ‖Φ v‖) / 2) - 1 ∧
        ‖deriv ε x‖ / (2 * √(f x)) ≤ Real.exp ((∫ v in Ioi x ∩ I, ‖Φ v‖) / 2) - 1

/-- The half-line `(a, ∞)` is `TauCeti.exists_liouvilleGreen_atTop`. -/
private lemma liouvilleGreenRight_Ioi (a : ℝ) : LiouvilleGreenRight (Ioi a) := by
  intro f ξ g Φ hf hf0 hg hξ hΦ hΦi
  have hI (x : ℝ) (hx : x ∈ Ioi a) : Ioi x ∩ Ioi a = Ioi x :=
    inter_eq_left.2 (Ioi_subset_Ioi (le_of_lt hx))
  obtain ⟨w, ε, hw, hε, h⟩ := exists_liouvilleGreen_atTop hf hf0 hg hξ hΦ
    fun x hx ↦ hI x hx ▸ hΦi x hx
  exact ⟨w, ε, hw, hε, fun x hx ↦ by rw [hI x hx]; exact h x hx⟩

/-- `(D² a)^{-1/4} = D^{-1/2} a^{-1/4}` for positive `D` and `a`. -/
private lemma rpow_sq_mul_rpow {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    (D ^ 2 * a) ^ (-(1 / 4) : ℝ) = D ^ (-(1 / 2) : ℝ) * a ^ (-(1 / 4) : ℝ) := by
  rw [Real.mul_rpow (by positivity) ha.le, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
  norm_num

private lemma rpow_sq_mul_self {D : ℝ} (hD : 0 < D) : (D ^ (-(1 / 2) : ℝ)) ^ 2 * D = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le, ← Real.rpow_add_one hD.ne']
  norm_num

private lemma rpow_sq_mul_sqrt {a : ℝ} (ha : 0 < a) : (a ^ (-(1 / 4) : ℝ)) ^ 2 * √a = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
  norm_num

/-- The error-control function of the transformed equation is `φ' · Φ ∘ φ`. -/
private lemma liouvilleGreen_control_comp {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 3 φ J) (hd : ∀ t ∈ J, 0 < deriv φ t) (hφJ : MapsTo φ J I)
    {f : ℝ → ℝ} {g Φ : ℝ → ℂ} (hf : ContDiffOn ℝ 2 f I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hΦ : ∀ x ∈ I, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x)) {t : ℝ}
    (ht : t ∈ J) :
    ((deriv φ t : ℝ) : ℂ) * Φ (φ t) =
      ↑((deriv φ t ^ 2 * f (φ t)) ^ (-(1 / 4) : ℝ) *
        iteratedDeriv 2 (fun s ↦ (deriv φ s ^ 2 * f (φ s)) ^ (-(1 / 4) : ℝ)) t) -
      (((deriv φ t ^ 2 : ℝ) : ℂ) * g (φ t) +
        ((iteratedDeriv 2 (fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ)) t /
          deriv φ t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) / ↑√(deriv φ t ^ 2 * f (φ t)) := by
  have heq : (fun s ↦ (deriv φ s ^ 2 * f (φ s)) ^ (-(1 / 4) : ℝ)) =ᶠ[𝓝 t]
      fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ) • (fun y ↦ f y ^ (-(1 / 4) : ℝ)) (φ s) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact rpow_sq_mul_rpow (hd s hs) (hf0 _ (hφJ hs))
  have hD := hd t ht
  have hfx := hf0 _ (hφJ ht)
  rw [(heq.iteratedDeriv 2).eq_of_nhds, iteratedDeriv_two_deriv_rpow_smul_comp hJ hI hφ hd
    (hf.rpow_const_of_ne fun x hx ↦ (hf0 x hx).ne') hφJ ht, hΦ _ (hφJ ht),
    rpow_sq_mul_rpow hD hfx, Real.sqrt_mul (by positivity), Real.sqrt_sq hD.le]
  have h1 := rpow_sq_mul_self hD
  have h2 := rpow_sq_mul_sqrt hfx
  have hU : 0 < deriv φ t ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hD _
  have hq : 0 < f (φ t) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hfx _
  simp only [smul_eq_mul]
  generalize deriv φ t ^ (-(1 / 2) : ℝ) = U at *
  generalize f (φ t) ^ (-(1 / 4) : ℝ) = q at *
  generalize √(f (φ t)) = S at *
  generalize deriv φ t = D at *
  have hDU : (D : ℂ) = ((U : ℂ) ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact_mod_cast h1)
  have hSq : (S : ℂ) = ((q : ℂ) ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact_mod_cast h2)
  have hU0 : (U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hU.ne'
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
  push_cast
  rw [hDU, hSq]
  field_simp
  ring

/-- If `W = φ'^{-1/2} · (w ∘ φ)` solves the transformed equation at `t`, then `w` solves
`w'' = (f + g) w` at `φ t`. -/
private lemma iteratedDeriv_two_eq_of_comp {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)
    {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 3 φ J) (hd : ∀ t ∈ J, 0 < deriv φ t) (hφJ : MapsTo φ J I)
    {f : ℝ → ℝ} {g W w : ℝ → ℂ} (hw : ContDiffOn ℝ 2 w I)
    (hWw : ∀ s ∈ J, W s = ((deriv φ s ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * w (φ s)) {t : ℝ}
    (ht : t ∈ J)
    (hW : iteratedDeriv 2 W t = (((deriv φ t ^ 2 * f (φ t) : ℝ) : ℂ) +
      (((deriv φ t ^ 2 : ℝ) : ℂ) * g (φ t) +
        ((iteratedDeriv 2 (fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ)) t /
          deriv φ t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) * W t) :
    iteratedDeriv 2 w (φ t) = (f (φ t) + g (φ t)) * w (φ t) := by
  have heq : W =ᶠ[𝓝 t] fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ) • w (φ s) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    rw [hWw s hs, Complex.real_smul]
  rw [(heq.iteratedDeriv 2).eq_of_nhds,
    iteratedDeriv_two_deriv_rpow_smul_comp hJ hI hφ hd hw hφJ ht, hWw t ht] at hW
  have hD := hd t ht
  have hU : 0 < deriv φ t ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hD _
  simp only [Complex.real_smul] at hW
  generalize deriv φ t ^ (-(1 / 2) : ℝ) = U at *
  generalize iteratedDeriv 2 (fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ)) t = U₂ at *
  generalize deriv φ t = D at *
  have hc : ((U₂ : ℂ) / U) * U = U₂ := div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 hU.ne')
  have hUD : (U : ℂ) * D ^ 2 ≠ 0 := by
    have : U * D ^ 2 ≠ 0 := by positivity
    exact_mod_cast this
  apply mul_left_cancel₀ hUD
  push_cast at hW
  linear_combination hW + w (φ t) * hc

/-- The Liouville–Green solution on `J` of the equation transformed by `x = φ(t)`. With
`u = φ'^{-1/2}`, the transformed coefficients are `φ'² f ∘ φ` and `φ'² g ∘ φ + u''/u`, and the
transformed error-control function is `φ' Φ ∘ φ`. -/
private lemma LiouvilleGreenRight.exists_comp {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)
    {φ ψ : ℝ → ℝ} (hφ : ContDiffOn ℝ 3 φ J) (hd : ∀ t ∈ J, 0 < deriv φ t)
    (hφm : StrictMonoOn φ J) (hφJ : MapsTo φ J I) (hψI : MapsTo ψ I J)
    (hφψ : ∀ x ∈ I, φ (ψ x) = x) (H : LiouvilleGreenRight J)
    {f ξ : ℝ → ℝ} {g Φ : ℝ → ℂ} (hf : ContDiffOn ℝ 2 f I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hg : ContinuousOn g I) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hΦ : ∀ x ∈ I, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x))
    (hΦi : ∀ x ∈ I, IntegrableOn Φ (Ioi x ∩ I)) :
    ∃ W E : ℝ → ℂ, ContDiffOn ℝ 2 W J ∧ DifferentiableOn ℝ E J ∧ ∀ t ∈ J,
      iteratedDeriv 2 W t = (((deriv φ t ^ 2 * f (φ t) : ℝ) : ℂ) +
        (((deriv φ t ^ 2 : ℝ) : ℂ) * g (φ t) +
          ((iteratedDeriv 2 (fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ)) t /
            deriv φ t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) * W t ∧
      W t = ↑(deriv φ t ^ (-(1 / 2) : ℝ) * (f (φ t) ^ (-(1 / 4) : ℝ) * Real.exp (-ξ (φ t)))) *
        (1 + E t) ∧
      ‖E t‖ ≤ Real.exp ((∫ v in Ioi (φ t) ∩ I, ‖Φ v‖) / 2) - 1 ∧
      ‖deriv E t‖ / (2 * (deriv φ t * √(f (φ t)))) ≤
        Real.exp ((∫ v in Ioi (φ t) ∩ I, ‖Φ v‖) / 2) - 1 := by
  set d := deriv φ
  set u : ℝ → ℝ := fun s ↦ d s ^ (-(1 / 2) : ℝ)
  have hd2 : ContDiffOn ℝ 2 d J := hφ.deriv_of_isOpen hJ (by norm_num)
  have hu : ContDiffOn ℝ 2 u J := hd2.rpow_const_of_ne fun s hs ↦ (hd s hs).ne'
  have hφ1 (s : ℝ) (hs : s ∈ J) : HasDerivAt φ (d s) s :=
    ((hφ.contDiffAt (hJ.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  have hu2c : ContinuousOn (iteratedDeriv 2 u) J := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hu.deriv_of_isOpen hJ (m := 1) (by norm_num)).deriv_of_isOpen hJ (m := 0)
      (by norm_num)).continuousOn
  have hGc : ContinuousOn
      (fun s ↦ ((d s ^ 2 : ℝ) : ℂ) * g (φ s) + ((iteratedDeriv 2 u s / u s : ℝ) : ℂ)) J :=
    ((Complex.continuous_ofReal.comp_continuousOn (hd2.continuousOn.pow 2)).mul
      (hg.comp hφ.continuousOn hφJ)).add (Complex.continuous_ofReal.comp_continuousOn
        (hu2c.div hu.continuousOn fun s hs ↦ (Real.rpow_pos_of_pos (hd s hs) _).ne'))
  have hΞ (s : ℝ) (hs : s ∈ J) : HasDerivAt (fun s ↦ ξ (φ s)) (√(d s ^ 2 * f (φ s))) s := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (hd s hs).le, mul_comm]
    exact (hξ _ (hφJ hs)).comp s (hφ1 s hs)
  -- change of variables `v = φ(r)` in the tail integrals of `Φ`
  have hint (s : ℝ) (hs : s ∈ J) :
      (IntegrableOn Φ (Ioi (φ s) ∩ I) ↔
        IntegrableOn (fun r ↦ ((deriv φ r : ℝ) : ℂ) * Φ (φ r)) (Ioi s ∩ J)) ∧
      ∫ v in Ioi (φ s) ∩ I, ‖Φ v‖ = ∫ r in Ioi s ∩ J, ‖((deriv φ r : ℝ) : ℂ) * Φ (φ r)‖ := by
    have hm : MeasurableSet (Ioi s ∩ J) := measurableSet_Ioi.inter hJ.measurableSet
    have hφ' (r : ℝ) (hr : r ∈ Ioi s ∩ J) : HasDerivWithinAt φ (deriv φ r) (Ioi s ∩ J) r :=
      (hφ1 r hr.2).hasDerivWithinAt
    have hmono : MonotoneOn φ (Ioi s ∩ J) := hφm.monotoneOn.mono inter_subset_right
    rw [← hφJ.image_subset.antisymm fun x hx ↦ ⟨ψ x, hψI hx, hφψ x hx⟩,
      ← hφm.image_Ioi_inter hs,
      integral_image_eq_integral_deriv_smul_of_monotoneOn hm hφ' hmono]
    refine ⟨(integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn hm hφ' hmono Φ).trans
      (by simp only [Complex.real_smul]), setIntegral_congr_fun hm fun r hr ↦ ?_⟩
    have hr0 : 0 < deriv φ r := hd r hr.2
    simp [abs_of_pos hr0]
  obtain ⟨W, E, hW, hE, hWE⟩ := H ((hd2.pow 2).mul (hf.comp (hφ.of_le (by norm_num)) hφJ))
    (fun s hs ↦ mul_pos (pow_pos (hd s hs) 2) (hf0 _ (hφJ hs))) hGc hΞ
    (fun s hs ↦ liouvilleGreen_control_comp hI hJ hφ hd hφJ hf hf0 hΦ hs)
    (fun s hs ↦ (hint s hs).1.1 (hΦi _ (hφJ hs)))
  refine ⟨W, E, hW, hE, fun t ht ↦ ?_⟩
  obtain ⟨hW2, hWf, hEb, hEd⟩ := hWE t ht
  simp only [Function.comp_apply, ← (hint t ht).2] at hW2 hWf hEb hEd
  rw [rpow_sq_mul_rpow (hd t ht) (hf0 _ (hφJ ht)), mul_assoc] at hWf
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (hd t ht).le] at hEd
  exact ⟨hW2, hWf, hEb, hEd⟩

/-- The right-end Liouville–Green theorem is invariant under an increasing `C³` change of
variable `x = φ(t)` from `J` onto `I`, with inverse `ψ`: a solution `W` for the transformed data
on `J` gives the solution `w = φ'^{1/2} ∘ ψ · W ∘ ψ` on `I`, with the same relative error. -/
private lemma LiouvilleGreenRight.of_comp {I J : Set ℝ} (hI : IsOpen I) (hJ : IsOpen J)
    {φ ψ : ℝ → ℝ} (hφ : ContDiffOn ℝ 3 φ J) (hd : ∀ t ∈ J, 0 < deriv φ t)
    (hφm : StrictMonoOn φ J) (hψ : ContDiffOn ℝ 2 ψ I) (hφJ : MapsTo φ J I)
    (hψI : MapsTo ψ I J) (hφψ : ∀ x ∈ I, φ (ψ x) = x) (hψφ : ∀ t ∈ J, ψ (φ t) = t)
    (H : LiouvilleGreenRight J) : LiouvilleGreenRight I := by
  intro f ξ g Φ hf hf0 hg hξ hΦ hΦi
  obtain ⟨W, E, hW, hE, hWE⟩ :=
    H.exists_comp hI hJ hφ hd hφm hφJ hψI hφψ hf hf0 hg hξ hΦ hΦi
  set u : ℝ → ℝ := fun s ↦ deriv φ s ^ (-(1 / 2) : ℝ)
  have hu : ContDiffOn ℝ 2 u J := (hφ.deriv_of_isOpen hJ (by norm_num)).rpow_const_of_ne
    fun s hs ↦ (hd s hs).ne'
  have hu0 (s : ℝ) (hs : s ∈ J) : 0 < u s := Real.rpow_pos_of_pos (hd s hs) _
  set w : ℝ → ℂ := fun x ↦ (((u (ψ x))⁻¹ : ℝ) : ℂ) * W (ψ x)
  have hw : ContDiffOn ℝ 2 w I :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn ((hu.comp hψ hψI).inv
      fun x hx ↦ (hu0 _ (hψI hx)).ne')).mul (hW.comp hψ hψI)
  have hWw (s : ℝ) (hs : s ∈ J) : W s = ((u s : ℝ) : ℂ) * w (φ s) := by
    simp only [w, hψφ s hs]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hu0 s hs).ne', Complex.ofReal_one,
      one_mul]
  refine ⟨w, fun x ↦ E (ψ x), hw, hE.comp (hψ.differentiableOn (by norm_num)) hψI,
    fun x hx ↦ ?_⟩
  set t := ψ x with htx
  have ht : t ∈ J := hψI hx
  have hxt : φ t = x := hφψ x hx
  obtain ⟨hW2, hWf, hEb, hEd⟩ := hWE t ht
  rw [hxt] at hWf hEb hEd
  refine ⟨?_, ?_, hEb, ?_⟩
  · have := iteratedDeriv_two_eq_of_comp hI hJ hφ hd hφJ hw hWw ht hW2
    rwa [hxt] at this
  · simp only [w]
    rw [← htx, hWf, ← mul_assoc, Complex.ofReal_mul, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (hu0 t ht).ne', Complex.ofReal_one, one_mul]
  · have hψ1 : HasDerivAt ψ (deriv φ t)⁻¹ x := by
      refine HasDerivAt.of_local_left_inverse (hψ.continuousOn.continuousAt (hI.mem_nhds hx))
        ((hφ.contDiffAt (hJ.mem_nhds ht)).differentiableAt (by norm_num)).hasDerivAt
        (hd t ht).ne' ?_
      filter_upwards [hI.mem_nhds hx] with y hy using hφψ y hy
    have h3 : HasDerivAt (fun x ↦ E (ψ x)) ((deriv φ t)⁻¹ • deriv E t) x :=
      (hE.differentiableAt (hJ.mem_nhds ht)).hasDerivAt.scomp x hψ1
    rw [h3.deriv, norm_smul, norm_inv, Real.norm_of_nonneg (hd t ht).le]
    convert hEd using 1
    have := (hd t ht).ne'
    field_simp

/-- The whole line, through `x = log t` from `(0, ∞)`. -/
private lemma liouvilleGreenRight_univ : LiouvilleGreenRight univ :=
  LiouvilleGreenRight.of_comp isOpen_univ isOpen_Ioi
    (Real.contDiffOn_log.mono fun _ ht ↦ (mem_Ioi.1 ht).ne')
    (fun t ht ↦ by rw [Real.deriv_log]; exact inv_pos.2 ht) Real.strictMonoOn_log
    Real.contDiff_exp.contDiffOn (mapsTo_univ _ _) (fun x _ ↦ Real.exp_pos x)
    (fun x _ ↦ Real.log_exp x) (fun _ ht ↦ Real.exp_log ht) (liouvilleGreenRight_Ioi 0)

/-- An open interval that is unbounded above is `(a, ∞)` or the whole line. -/
private lemma liouvilleGreenRight_of_not_bddAbove {I : Set ℝ} (hI : IsOpen I)
    (hIc : I.OrdConnected) (hb : ¬BddAbove I) : LiouvilleGreenRight I := by
  by_cases hbb : BddBelow I
  · have : I = Ioi (sInf I) := by
      refine subset_antisymm (fun x hx ↦ ?_) (hIc.isPreconnected.Ioi_csInf_subset hbb hb)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI x hx
      have hm : x - ε / 2 ∈ I := by
        refine hball ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
      exact (csInf_le hbb hm).trans_lt (by linarith)
    rw [this]
    exact liouvilleGreenRight_Ioi _
  · rw [hIc.isPreconnected.eq_univ_of_unbounded hbb hb]
    exact liouvilleGreenRight_univ

/-- A nonempty open interval bounded above by `b = sup I`, through `x = b - 1 / t`. -/
private lemma liouvilleGreenRight_of_bddAbove {I : Set ℝ} (hI : IsOpen I) (hIc : I.OrdConnected)
    (hne : I.Nonempty) (hb : BddAbove I) : LiouvilleGreenRight I := by
  set b := sSup I
  have hIb (x : ℝ) (hx : x ∈ I) : x < b := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hI x hx
    have hm : x + ε / 2 ∈ I := by
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact lt_of_lt_of_le (by linarith) (le_csSup hb hm)
  set φ : ℝ → ℝ := fun t ↦ b - t⁻¹
  set ψ : ℝ → ℝ := fun x ↦ (b - x)⁻¹
  set J := Ioi 0 ∩ φ ⁻¹' I
  have hφd (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt φ (-(-(t ^ 2)⁻¹)) t :=
    (hasDerivAt_inv (ne_of_gt ht)).const_sub b
  have hφm : StrictMonoOn φ (Ioi 0) := fun s hs t ht hst ↦
    sub_lt_sub_left ((inv_lt_inv₀ ht hs).2 hst) b
  have hJ : IsOpen J := ContinuousOn.isOpen_inter_preimage
    (fun t ht ↦ (hφd t ht).continuousAt.continuousWithinAt) isOpen_Ioi hI
  have hJc : J.OrdConnected := ⟨fun s hs t ht r hr ↦ by
    have hr0 : r ∈ Ioi (0 : ℝ) := mem_Ioi.2 (lt_of_lt_of_le hs.1 hr.1)
    exact ⟨hr0, hIc.out hs.2 ht.2
      ⟨hφm.monotoneOn hs.1 hr0 hr.1, hφm.monotoneOn hr0 ht.1 hr.2⟩⟩⟩
  have hψφ (t : ℝ) (_ : t ∈ J) : ψ (φ t) = t := by simp [φ, ψ]
  have hφψ (x : ℝ) (_ : x ∈ I) : φ (ψ x) = x := by simp [φ, ψ]
  have hψI : MapsTo ψ I J := fun x hx ↦
    ⟨inv_pos.2 (sub_pos.2 (hIb x hx)), by simpa [Set.mem_preimage, hφψ x hx] using hx⟩
  have hJb : ¬BddAbove J := by
    rintro ⟨M, hM⟩
    obtain ⟨x, hx, hbx⟩ := exists_lt_of_lt_csSup hne
      (sub_lt_self b (inv_pos.2 (lt_max_of_lt_right one_pos) : 0 < (max M 1)⁻¹))
    have hpos : 0 < b - x := sub_pos.2 (hIb x hx)
    have : max M 1 < ψ x := (lt_inv_comm₀ (lt_max_of_lt_right one_pos) hpos).2 (by linarith)
    exact absurd (hM (hψI hx)) (not_le.2 ((le_max_left M 1).trans_lt this))
  refine LiouvilleGreenRight.of_comp hI hJ (φ := φ) (ψ := ψ) ?_ (fun t ht ↦ ?_)
    (hφm.mono inter_subset_left) ?_ (fun t ht ↦ ht.2) hψI hφψ hψφ
    (liouvilleGreenRight_of_not_bddAbove hJ hJc hJb)
  · exact (contDiffOn_const.sub (contDiffOn_inv ℝ)).mono fun t ht ↦ ne_of_gt ht.1
  · rw [(hφd t ht.1).deriv, neg_neg]
    exact inv_pos.2 (pow_pos ht.1 2)
  · exact (contDiffOn_const.sub contDiffOn_id).inv fun x hx ↦ (sub_pos.2 (hIb x hx)).ne'

/-- **The Liouville–Green theorem, solution controlled at the right end.** Let `I` be an open
interval `(a₁, a₂)`, let `f` be positive and `C²` and `g` continuous on `I`, let `ξ` be a
primitive of `f^{1/2}` there, and let `Φ = f^{-1/4} (f^{-1/4})'' - g f^{-1/2}` be integrable on
`(x, a₂)` for every `x ∈ I`. Then `w'' = (f + g) w` has a solution `w`, `C²` on `I`, of the form
`w = f^{-1/4} e^{-ξ} (1 + ε)` with `ε` differentiable and, for `V(x) = ∫ₓ^{a₂} |Φ|`,
`|ε(x)| ≤ exp(V(x) / 2) - 1` and `|ε'(x)| / (2 f(x)^{1/2}) ≤ exp(V(x) / 2) - 1`
(DLMF 2.7.20–2.7.25; Olver, Chapter 6, Theorem 2.1). -/
theorem exists_liouvilleGreen_right {I : Set ℝ} (hI : IsOpen I) (hIc : I.OrdConnected)
    {f ξ : ℝ → ℝ} {g Φ : ℝ → ℂ} (hf : ContDiffOn ℝ 2 f I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hg : ContinuousOn g I) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hΦ : ∀ x ∈ I, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x))
    (hΦi : ∀ x ∈ I, IntegrableOn Φ (Ioi x ∩ I)) :
    ∃ w ε : ℝ → ℂ, ContDiffOn ℝ 2 w I ∧ DifferentiableOn ℝ ε I ∧
      ∀ x ∈ I, iteratedDeriv 2 w x = (f x + g x) * w x ∧
        w x = ↑(f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x)) * (1 + ε x) ∧
        ‖ε x‖ ≤ Real.exp ((∫ v in Ioi x ∩ I, ‖Φ v‖) / 2) - 1 ∧
        ‖deriv ε x‖ / (2 * √(f x)) ≤ Real.exp ((∫ v in Ioi x ∩ I, ‖Φ v‖) / 2) - 1 := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 0, contDiffOn_empty, differentiableOn_empty, fun x hx ↦ hx.elim⟩
  by_cases hb : BddAbove I
  · exact liouvilleGreenRight_of_bddAbove hI hIc hne hb hf hf0 hg hξ hΦ hΦi
  · exact liouvilleGreenRight_of_not_bddAbove hI hIc hb hf hf0 hg hξ hΦ hΦi

/-- **The Liouville–Green theorem, solution controlled at the left end.** Let `I` be an open
interval `(a₁, a₂)`, let `f` be positive and `C²` and `g` continuous on `I`, let `ξ` be a
primitive of `f^{1/2}` there, and let `Φ = f^{-1/4} (f^{-1/4})'' - g f^{-1/2}` be integrable on
`(a₁, x)` for every `x ∈ I`. Then `w'' = (f + g) w` has a solution `w`, `C²` on `I`, of the form
`w = f^{-1/4} e^{ξ} (1 + ε)` with `ε` differentiable and, for `V(x) = ∫_{a₁}^x |Φ|`,
`|ε(x)| ≤ exp(V(x) / 2) - 1` and `|ε'(x)| / (2 f(x)^{1/2}) ≤ exp(V(x) / 2) - 1`
(DLMF 2.7.20–2.7.25; Olver, Chapter 6, Theorem 2.1). -/
theorem exists_liouvilleGreen_left {I : Set ℝ} (hI : IsOpen I) (hIc : I.OrdConnected)
    {f ξ : ℝ → ℝ} {g Φ : ℝ → ℂ} (hf : ContDiffOn ℝ 2 f I) (hf0 : ∀ x ∈ I, 0 < f x)
    (hg : ContinuousOn g I) (hξ : ∀ x ∈ I, HasDerivAt ξ (√(f x)) x)
    (hΦ : ∀ x ∈ I, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x))
    (hΦi : ∀ x ∈ I, IntegrableOn Φ (Iio x ∩ I)) :
    ∃ w ε : ℝ → ℂ, ContDiffOn ℝ 2 w I ∧ DifferentiableOn ℝ ε I ∧
      ∀ x ∈ I, iteratedDeriv 2 w x = (f x + g x) * w x ∧
        w x = ↑(f x ^ (-(1 / 4) : ℝ) * Real.exp (ξ x)) * (1 + ε x) ∧
        ‖ε x‖ ≤ Real.exp ((∫ v in Iio x ∩ I, ‖Φ v‖) / 2) - 1 ∧
        ‖deriv ε x‖ / (2 * √(f x)) ≤ Real.exp ((∫ v in Iio x ∩ I, ‖Φ v‖) / 2) - 1 := by
  have hneg : MapsTo Neg.neg (Neg.neg ⁻¹' I) I := fun _ ht ↦ ht
  have hneg' : MapsTo Neg.neg I (Neg.neg ⁻¹' I) := fun x hx ↦ by simpa using hx
  -- reflection `v = -s` in the tail integrals of `Φ`
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hpre (t : ℝ) : Neg.neg ⁻¹' (Iio (-t) ∩ I) = Ioi t ∩ Neg.neg ⁻¹' I := by
    ext s
    simp
  have hint (t : ℝ) :
      (IntegrableOn Φ (Iio (-t) ∩ I) ↔ IntegrableOn (fun s ↦ Φ (-s)) (Ioi t ∩ Neg.neg ⁻¹' I)) ∧
      ∫ v in Iio (-t) ∩ I, ‖Φ v‖ = ∫ s in Ioi t ∩ Neg.neg ⁻¹' I, ‖Φ (-s)‖ := by
    rw [← hpre]
    exact ⟨(hmp.integrableOn_comp_preimage measurableEmbedding_neg).symm,
      (hmp.setIntegral_preimage_emb measurableEmbedding_neg (fun v ↦ ‖Φ v‖) _).symm⟩
  obtain ⟨w, ε, hw, hε, h⟩ := exists_liouvilleGreen_right (hI.preimage continuous_neg)
    ⟨fun a ha b hb c hc ↦ hIc.out hb ha ⟨neg_le_neg hc.2, neg_le_neg hc.1⟩⟩
    (f := fun t ↦ f (-t)) (ξ := fun t ↦ -ξ (-t)) (g := fun t ↦ g (-t)) (Φ := fun t ↦ Φ (-t))
    (hf.comp contDiff_neg.contDiffOn hneg) (fun t ht ↦ hf0 _ ht)
    (hg.comp continuous_neg.continuousOn hneg)
    (fun t ht ↦ by
      convert ((hξ _ ht).comp t (hasDerivAt_neg t)).neg using 1
      · ext; simp
      · simp)
    (fun t ht ↦ by
      have := iteratedDeriv_comp_neg 2 (fun s ↦ f s ^ (-(1 / 4) : ℝ)) t
      simp only [neg_one_sq, one_smul] at this
      rw [this]
      exact hΦ _ ht)
    (fun t ht ↦ (hint t).1.1 (by simpa using hΦi _ ht))
  refine ⟨fun x ↦ w (-x), fun x ↦ ε (-x), hw.comp contDiff_neg.contDiffOn hneg',
    hε.comp differentiable_neg.differentiableOn hneg', fun x hx ↦ ?_⟩
  obtain ⟨h2, hform, hb, hd⟩ := h (-x) (by simpa using hx)
  have hV : ∫ v in Ioi (-x) ∩ Neg.neg ⁻¹' I, ‖Φ (-v)‖ = ∫ v in Iio x ∩ I, ‖Φ v‖ := by
    rw [← (hint (-x)).2, neg_neg]
  simp only [neg_neg, hV] at h2 hform hb hd
  refine ⟨?_, hform, hb, ?_⟩
  · rw [iteratedDeriv_comp_neg, neg_one_sq, one_smul, h2]
  · rwa [deriv_comp_neg, norm_neg]

end TauCeti
