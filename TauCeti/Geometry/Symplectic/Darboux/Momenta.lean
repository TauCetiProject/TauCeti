/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Poincare

/-!
# Closed two-forms with prescribed contractions along coordinate directions

On `(ι → ℝ) × (ι → ℝ)`, with coordinates `(t, c)`, let `μ` be a smooth closed two-form near a point
`p₀ = (t₀, c₀)` whose contraction with each coordinate vector `∂_{tᵢ}` is `dcᵢ`:

`μ_p(∂_{tᵢ}, v) = (v.2)ᵢ`.

This file shows that such a form is a standard symplectic form after a shear of the
`t`-coordinates: there is a smooth `a : (ι → ℝ) → (ι → ℝ)` with `a c₀ = 0` and

`μ = ∑ᵢ d(tᵢ + aᵢ(c)) ∧ dcᵢ`

near `p₀` (`TauCeti.exists_apply_eq_sum_of_apply_inl_single_eq_snd`). In the coordinates
`(t + a(c), c)` the form is `∑ᵢ dqᵢ ∧ dpᵢ` with momenta `p = c`.

This is the local model behind the Carathéodory–Jacobi–Lie theorem: for Poisson-commuting
functions `F₁, …, Fₙ` with independent differentials on a `2n`-dimensional symplectic manifold,
the Hamiltonian vector fields `X_{Fᵢ}` can be straightened to the coordinate fields `∂_{tᵢ}`, and
then `ι_{X_{Fᵢ}} σ = dFᵢ` is the hypothesis above with `c = F`.

The proof has three steps.

* The contraction `ι_{∂_{tᵢ}} μ = dcᵢ` is constant, so Cartan's formula `L_{∂_{tᵢ}} μ =
  d ι_{∂_{tᵢ}} μ + ι_{∂_{tᵢ}} dμ = 0` shows that `μ` does not depend on `t`
  (`TauCeti.fderiv_apply_inl_eq_zero_of_apply_inl_single_eq_snd`).
* Hence `μ(t, c)` is determined by the contractions and by the closed two-form
  `β(c) = μ(t₀, c)|_{0 × (ι → ℝ)}` on the `c`-space, which by the Poincaré lemma is `dα` for a
  one-form `α` vanishing at `c₀`.
* Writing `α_c = ∑ᵢ aᵢ(c) dcᵢ`, the form `dα = ∑ᵢ daᵢ ∧ dcᵢ` is exactly the correction.

## References

* P. Libermann and C.-M. Marle, *Symplectic Geometry and Analytical Mechanics*, Reidel, 1987,
  Chapter III (the Carathéodory–Jacobi–Lie theorem).
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49 (Liouville's theorem on integrable systems).
-/

public section

open Set Metric
open scoped ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section TwoForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- A two-form changes sign when its arguments are swapped. -/
private theorem apply_vecCons_swap (f : E [⋀^Fin 2]→L[ℝ] ℝ) (a b : E) :
    f ![a, b] = -f ![b, a] := by
  have h := f.toAlternatingMap.map_swap ![b, a] (i := 0) (j := 1) (by decide)
  have hv : (![b, a] ∘ Equiv.swap (0 : Fin 2) 1) = ![a, b] := by
    funext k
    fin_cases k <;> rfl
  rw [hv] at h
  exact h

/-- An alternating map is homogeneous in its first argument. -/
private theorem apply_vecCons_smul (f : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) (m : Fin n → E) (c : ℝ)
    (a : E) : f (Matrix.vecCons (c • a) m) = c * f (Matrix.vecCons a m) :=
  f.toAlternatingMap.map_vecCons_smul m c a

omit [DecidableEq ι] in
/-- An alternating map is additive over finite sums in its first argument. -/
private theorem apply_vecCons_sum (f : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) (m : Fin n → E) (g : ι → E) :
    f (Matrix.vecCons (∑ i, g i) m) = ∑ i, f (Matrix.vecCons (g i) m) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using apply_vecCons_smul f m 0 0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, f.vecCons_add, ih]

/-- An alternating map on `ι → ℝ` evaluated with first argument `γ` is the combination of its
values on the standard basis vectors with coefficients `γ i`. -/
private theorem apply_vecCons_eq_sum (f : (ι → ℝ) [⋀^Fin (n + 1)]→L[ℝ] ℝ) (m : Fin n → ι → ℝ)
    (γ : ι → ℝ) :
    f (Matrix.vecCons γ m) = ∑ i, γ i * f (Matrix.vecCons (Pi.single i 1) m) := by
  conv_lhs => rw [← Finset.univ_sum_single γ]
  rw [apply_vecCons_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← apply_vecCons_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

end TwoForm

/-- The coordinate vector `∂_{tᵢ} = (eᵢ, 0)` of `(ι → ℝ) × (ι → ℝ)`. -/
private theorem prod_mk_zero_eq_sum (τ : ι → ℝ) :
    ((τ, 0) : (ι → ℝ) × (ι → ℝ)) = ∑ i, τ i • ((Pi.single i 1, 0) : (ι → ℝ) × (ι → ℝ)) := by
  ext j
  · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · simp [Prod.snd_sum]

variable {μ : (ι → ℝ) × (ι → ℝ) → ((ι → ℝ) × (ι → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ}
  {O : Set ((ι → ℝ) × (ι → ℝ))}

/-- Contracting with `∂_{tᵢ}` is evaluation of the `c`-component of a vector. -/
private theorem apply_inl_eq (hham : ∀ p ∈ O, ∀ i v, μ p ![(Pi.single i 1, 0), v] = v.2 i)
    {p : (ι → ℝ) × (ι → ℝ)} (hp : p ∈ O) (τ : ι → ℝ) (v : (ι → ℝ) × (ι → ℝ)) :
    μ p ![(τ, 0), v] = ∑ i, τ i * v.2 i := by
  rw [prod_mk_zero_eq_sum, apply_vecCons_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [apply_vecCons_smul, hham p hp]

/-- **A two-form with constant contractions along the `t`-directions is independent of `t`.** If
`μ` is closed and differentiable on an open set `O` and `μ_p(∂_{tᵢ}, v) = (v.2)ᵢ` there, then the
derivative of `μ` along every vector `(τ, 0)` vanishes on `O`: by Cartan's formula, the Lie
derivative `L_{∂_{tᵢ}} μ = d ι_{∂_{tᵢ}} μ + ι_{∂_{tᵢ}} dμ` vanishes, since the contraction
`ι_{∂_{tᵢ}} μ = dcᵢ` is constant. -/
theorem fderiv_apply_inl_eq_zero_of_apply_inl_single_eq_snd (hO : IsOpen O)
    (hμ : DifferentiableOn ℝ μ O) (hcl : ∀ p ∈ O, extDeriv μ p = 0)
    (hham : ∀ p ∈ O, ∀ i v, μ p ![(Pi.single i 1, 0), v] = v.2 i)
    {p : (ι → ℝ) × (ι → ℝ)} (hp : p ∈ O) (τ : ι → ℝ) :
    fderiv ℝ μ p (τ, 0) = 0 := by
  have hdp : DifferentiableAt ℝ μ p := hμ.differentiableAt (hO.mem_nhds hp)
  -- The contraction of `μ` with `(τ, 0)` is the same at every point of `O`.
  have hconst (w : (ι → ℝ) × (ι → ℝ)) (a : (ι → ℝ) × (ι → ℝ)) :
      fderiv ℝ μ p a ![(τ, 0), w] = 0 := by
    have heq : (fun y ↦ μ y ![(τ, 0), w]) =ᶠ[nhds p] fun _ ↦ ∑ i, τ i * w.2 i := by
      filter_upwards [hO.mem_nhds hp] with y hy
      exact apply_inl_eq hham hy τ w
    rw [← fderiv_continuousAlternatingMap_apply_const_apply hdp, heq.fderiv_eq]
    simp
  ext v
  have hv : v = ![v 0, v 1] := by
    funext k
    fin_cases k <;> rfl
  have hr0 : (0 : Fin 3).removeNth ![((τ, 0) : (ι → ℝ) × (ι → ℝ)), v 0, v 1] = ![v 0, v 1] := by
    funext k
    fin_cases k <;> rfl
  have hr1 : (1 : Fin 3).removeNth ![((τ, 0) : (ι → ℝ) × (ι → ℝ)), v 0, v 1] = ![(τ, 0), v 1] := by
    funext k
    fin_cases k <;> rfl
  have hr2 : (2 : Fin 3).removeNth ![((τ, 0) : (ι → ℝ) × (ι → ℝ)), v 0, v 1] = ![(τ, 0), v 0] := by
    funext k
    fin_cases k <;> rfl
  -- Expand `dμ_p((τ, 0), v₀, v₁) = 0`: only the derivative of `μ` along `(τ, 0)` survives.
  have h3 := congrArg (fun A ↦ A ![(τ, 0), v 0, v 1]) (hcl p hp)
  simp only [extDeriv_apply hdp] at h3
  rw [Fin.sum_univ_three, hr0, hr1, hr2] at h3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    fderiv_continuousAlternatingMap_apply_const_apply hdp, hconst] at h3
  rw [hv]
  simpa using h3

omit [DecidableEq ι] in
/-- A point of a ball in `(ι → ℝ) × (ι → ℝ)` has both coordinates in balls of the same radius. -/
private theorem mem_ball_iff {p₀ p : (ι → ℝ) × (ι → ℝ)} {r : ℝ} :
    p ∈ ball p₀ r ↔ p.1 ∈ ball p₀.1 r ∧ p.2 ∈ ball p₀.2 r := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff, mem_ball, mem_ball]

/-- Under the hypotheses of `fderiv_apply_inl_eq_zero_of_apply_inl_single_eq_snd`, the form `μ` is
constant along the `t`-directions on a ball inside `O`. -/
private theorem apply_eq_apply_fst_of_mem_ball (hO : IsOpen O) (hμ : DifferentiableOn ℝ μ O)
    (hcl : ∀ p ∈ O, extDeriv μ p = 0)
    (hham : ∀ p ∈ O, ∀ i v, μ p ![(Pi.single i 1, 0), v] = v.2 i)
    {p₀ : (ι → ℝ) × (ι → ℝ)} {r : ℝ} (hrO : ball p₀ r ⊆ O) {p : (ι → ℝ) × (ι → ℝ)}
    (hp : p ∈ ball p₀ r) : μ p = μ (p₀.1, p.2) := by
  have hmem {t : ι → ℝ} (ht : t ∈ ball p₀.1 r) : (t, p.2) ∈ O :=
    hrO (mem_ball_iff.2 ⟨ht, (mem_ball_iff.1 hp).2⟩)
  have hd : DifferentiableOn ℝ (fun t ↦ μ (t, p.2)) (ball p₀.1 r) := fun t ht ↦
    ((hμ _ (hmem ht)).differentiableAt (hO.mem_nhds (hmem ht))).comp_differentiableWithinAt t
      (differentiableAt_id.prodMk (differentiableAt_const _)).differentiableWithinAt
  refine (convex_ball p₀.1 r).is_const_of_fderivWithin_eq_zero hd (fun t ht ↦ ?_)
    (mem_ball_iff.1 hp).1 (mem_ball_self (pos_of_mem_ball (mem_ball_iff.1 hp).1))
  have hD : HasFDerivAt (fun t ↦ μ (t, p.2))
      ((fderiv ℝ μ (t, p.2)).comp (ContinuousLinearMap.inl ℝ (ι → ℝ) (ι → ℝ))) t :=
    ((hμ _ (hmem ht)).differentiableAt (hO.mem_nhds (hmem ht))).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_left t p.2)
  rw [fderivWithin_of_isOpen isOpen_ball ht, hD.fderiv]
  ext τ : 1
  exact fderiv_apply_inl_eq_zero_of_apply_inl_single_eq_snd hO hμ hcl hham (hmem ht) τ

/-- Splitting a vector of `(ι → ℝ) × (ι → ℝ)` into its `t`- and `c`-parts, a two-form with
`μ_p(∂_{tᵢ}, v) = (v.2)ᵢ` is `∑ᵢ dtᵢ ∧ dcᵢ` plus its restriction to the `c`-directions. -/
private theorem apply_eq_sum_add_apply_inr
    (hham : ∀ p ∈ O, ∀ i v, μ p ![(Pi.single i 1, 0), v] = v.2 i)
    {p : (ι → ℝ) × (ι → ℝ)} (hp : p ∈ O) (v w : (ι → ℝ) × (ι → ℝ)) :
    μ p ![v, w] = ∑ i, (v.1 i * w.2 i - w.1 i * v.2 i) + μ p ![(0, v.2), (0, w.2)] := by
  have hsplit (u : (ι → ℝ) × (ι → ℝ)) : u = (u.1, 0) + (0, u.2) := by simp
  have h1 : μ p ![v, w] = μ p ![(v.1, 0), w] - μ p ![w, (0, v.2)] := by
    conv_lhs => rw [hsplit v]
    rw [μ p |>.vecCons_add, apply_vecCons_swap (μ p) (0, v.2) w, sub_eq_add_neg]
  have h2 : μ p ![w, (0, v.2)] = μ p ![(w.1, 0), (0, v.2)] - μ p ![(0, v.2), (0, w.2)] := by
    conv_lhs => rw [hsplit w]
    rw [μ p |>.vecCons_add, apply_vecCons_swap (μ p) (0, w.2), sub_eq_add_neg]
  rw [h1, h2, apply_inl_eq hham hp, apply_inl_eq hham hp, Finset.sum_sub_distrib]
  ring

/-- The exterior derivative of a one-form `α` on `ι → ℝ` in coordinates:
`dα(γ, γ') = ∑ᵢ (daᵢ(γ) γ'ᵢ - daᵢ(γ') γᵢ)`, where `aᵢ = α(eᵢ)` are the coefficients of `α`. -/
private theorem extDeriv_apply_eq_sum {α : (ι → ℝ) → (ι → ℝ) [⋀^Fin 1]→L[ℝ] ℝ} {c : ι → ℝ}
    (hα : DifferentiableAt ℝ α c) (γ γ' : ι → ℝ) :
    extDeriv α c ![γ, γ'] = ∑ i, (fderiv ℝ α c γ ![Pi.single i 1] * γ' i -
      fderiv ℝ α c γ' ![Pi.single i 1] * γ i) := by
  rw [extDeriv_apply hα, Fin.sum_univ_two]
  have hr0 : (0 : Fin 2).removeNth ![γ, γ'] = ![γ'] := by
    funext k
    fin_cases k
    rfl
  have hr1 : (1 : Fin 2).removeNth ![γ, γ'] = ![γ] := by
    funext k
    fin_cases k
    rfl
  simp only [hr0, hr1, Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_continuousAlternatingMap_apply_const_apply hα, Fin.val_zero, Fin.val_one, pow_zero,
    pow_one, one_smul, neg_smul]
  rw [apply_vecCons_eq_sum (fderiv ℝ α c γ), apply_vecCons_eq_sum (fderiv ℝ α c γ'),
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **Closed two-forms with `ι_{∂_{tᵢ}} μ = dcᵢ` are standard after a shear.** Let `μ` be a smooth
closed two-form on an open set `O` of `(ι → ℝ) × (ι → ℝ)`, with coordinates `(t, c)`, such that
`μ_p(∂_{tᵢ}, v) = (v.2)ᵢ` on `O`. Then near any `p₀ ∈ O` there is a smooth
`a : (ι → ℝ) → (ι → ℝ)` with `a p₀.2 = 0` such that `μ = ∑ᵢ d(tᵢ + aᵢ(c)) ∧ dcᵢ`: on a ball
around `p₀`,

`μ_p(v, w) = ∑ᵢ ((v.1 + da_{p.2}(v.2))ᵢ (w.2)ᵢ - (w.1 + da_{p.2}(w.2))ᵢ (v.2)ᵢ)`. -/
theorem exists_apply_eq_sum_of_apply_inl_single_eq_snd (hO : IsOpen O)
    {p₀ : (ι → ℝ) × (ι → ℝ)} (hp₀ : p₀ ∈ O) (hμ : ContDiffOn ℝ ∞ μ O)
    (hcl : ∀ p ∈ O, extDeriv μ p = 0)
    (hham : ∀ p ∈ O, ∀ i v, μ p ![(Pi.single i 1, 0), v] = v.2 i) :
    ∃ r > 0, ball p₀ r ⊆ O ∧ ∃ a : (ι → ℝ) → ι → ℝ, a p₀.2 = 0 ∧
      ContDiffOn ℝ ∞ a (ball p₀.2 r) ∧ ∀ p ∈ ball p₀ r, ∀ v w : (ι → ℝ) × (ι → ℝ),
        μ p ![v, w] = ∑ i, ((v.1 i + fderiv ℝ a p.2 v.2 i) * w.2 i -
          (w.1 i + fderiv ℝ a p.2 w.2 i) * v.2 i) := by
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO p₀ hp₀
  refine ⟨r, hr, hrO, ?_⟩
  have hμd : DifferentiableOn ℝ μ O := hμ.differentiableOn (by simp)
  have hslO {c : ι → ℝ} (hc : c ∈ ball p₀.2 r) : (p₀.1, c) ∈ O :=
    hrO (mem_ball_iff.2 ⟨mem_ball_self hr, hc⟩)
  -- The restriction `β` of `μ` to the slice `t = t₀` is a closed two-form on the `c`-space.
  set β : (ι → ℝ) → (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ := fun c ↦
    (μ (p₀.1, c)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ (ι → ℝ) (ι → ℝ)) with hβ
  have hslice : ContDiff ℝ ∞ fun c : ι → ℝ ↦ (p₀.1, c) := contDiff_const.prodMk contDiff_id
  have hβs : ContDiffOn ℝ ∞ β (ball p₀.2 r) :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (ι := Fin 2) (F := ℝ)
      (ContinuousLinearMap.inr ℝ (ι → ℝ) (ι → ℝ))).contDiff.comp_contDiffOn
        (hμ.comp hslice.contDiffOn fun _ hc ↦ hslO hc)
  have hβc : ∀ c ∈ ball p₀.2 r, extDeriv β c = 0 := by
    intro c hc
    have hβ' : β = fun c ↦ (μ (p₀.1, c)).compContinuousLinearMap
        (fderiv ℝ (fun c : ι → ℝ ↦ (p₀.1, c)) c) := by
      funext c
      rw [(hasFDerivAt_prodMk_right p₀.1 c).fderiv]
    rw [hβ', extDeriv_pullback ((hμd _ (hslO hc)).differentiableAt (hO.mem_nhds (hslO hc)))
      hslice.contDiffAt (by simp), hcl _ (hslO hc)]
    ext
    simp
  -- By the Poincaré lemma, `β = dα` with `α` vanishing at `c₀`; `aᵢ(c) = α_c(eᵢ)`.
  obtain ⟨α, hα, hα0, hdα⟩ := StarConvex.exists_contDiffOn_forall_extDeriv_eq
    ((convex_ball p₀.2 r).starConvex (mem_ball_self hr)) isOpen_ball (r := ⊤) le_top hβs hβc
  set L : ((ι → ℝ) [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ι → ℝ :=
    ContinuousLinearMap.pi fun i ↦ ContinuousAlternatingMap.apply ℝ (ι → ℝ) ℝ ![Pi.single i 1]
  refine ⟨fun c ↦ L (α c), by simp [hα0], L.contDiff.comp_contDiffOn hα, fun p hp v w ↦ ?_⟩
  have hp2 := (mem_ball_iff.1 hp).2
  have hdα' : DifferentiableAt ℝ α p.2 :=
    (hα.differentiableOn (by simp) _ hp2).differentiableAt (isOpen_ball.mem_nhds hp2)
  have hda (γ : ι → ℝ) (i : ι) :
      fderiv ℝ (fun c ↦ L (α c)) p.2 γ i = fderiv ℝ α p.2 γ ![Pi.single i 1] := by
    have hD : HasFDerivAt (fun c ↦ L (α c)) (L.comp (fderiv ℝ α p.2)) p.2 :=
      L.hasFDerivAt.comp p.2 hdα'.hasFDerivAt
    rw [hD.fderiv]
    simp [L]
  -- The `c`-part of `μ_p` is `β_{p.2} = dα_{p.2}`, by `t`-invariance of `μ`.
  have hvv : μ p ![(0, v.2), (0, w.2)] = extDeriv α p.2 ![v.2, w.2] := by
    rw [apply_eq_apply_fst_of_mem_ball hO hμd hcl hham hrO hp, hdα _ hp2, hβ,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [apply_eq_sum_add_apply_inr hham (hrO hp), hvv, extDeriv_apply_eq_sum hdα',
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hda, hda]
  ring

end TauCeti
