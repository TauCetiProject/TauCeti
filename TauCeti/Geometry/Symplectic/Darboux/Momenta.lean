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
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import TauCeti.Analysis.Normed.Module.Alternating.Bilinear

/-!
# Closed two-forms with prescribed contractions along coordinate directions

On `(ι → ℝ) × (ι → ℝ)`, with coordinates `(t, c)`, let `μ` be a smooth closed two-form near a point
`p₀ = (t₀, c₀)` whose contraction with each coordinate vector `∂_{tᵢ}` is `dcᵢ`:

`μ_p(∂_{tᵢ}, v) = (v.2)ᵢ`.

This file shows that such a form is a standard symplectic form after a shear of the
`t`-coordinates: there is a smooth `a : (ι → ℝ) → (ι → ℝ)` with `a c₀ = 0` and

`μ = ∑ᵢ d(tᵢ + aᵢ(c)) ∧ dcᵢ`

near `p₀` (`TauCeti.exists_apply_eq_sum_of_apply_inl_single_eq_snd`). In the coordinates
`(t + a(c), c)` the form is `∑ᵢ dqᵢ ∧ dpᵢ` with momenta `p = c`. This standard form is
nondegenerate (`TauCeti.eq_of_forall_sum_mul_sub_mul_eq`).

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

/-- A vector `(τ, 0)` is the combination `∑ᵢ τᵢ ∂_{tᵢ}` of the coordinate vectors
`∂_{tᵢ} = (eᵢ, 0)` of `(ι → ℝ) × (ι → ℝ)`. -/
private theorem prod_mk_zero_eq_sum (τ : ι → ℝ) :
    ((τ, 0) : (ι → ℝ) × (ι → ℝ)) = ∑ i, τ i • ((Pi.single i 1, 0) : (ι → ℝ) × (ι → ℝ)) := by
  ext j
  · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · simp [Prod.snd_sum]

omit [DecidableEq ι] in
/-- The standard form `∑ᵢ dqᵢ ∧ dpᵢ` on `(ι → ℝ) × (ι → ℝ)` is nondegenerate: two vectors with
the same pairing against every vector are equal. -/
theorem eq_of_forall_sum_mul_sub_mul_eq {a c : (ι → ℝ) × (ι → ℝ)}
    (h : ∀ b : (ι → ℝ) × (ι → ℝ), ∑ i, (a.1 i * b.2 i - b.1 i * a.2 i) =
      ∑ i, (c.1 i * b.2 i - b.1 i * c.2 i)) : a = c := by
  classical
  refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
  · simpa [Pi.single_apply] using h (0, Pi.single i 1)
  · simpa [Pi.single_apply] using h (Pi.single i 1, 0)

variable {μ : (ι → ℝ) × (ι → ℝ) → ((ι → ℝ) × (ι → ℝ)) [⋀^Fin 2]→L[ℝ] ℝ}
  {O : Set ((ι → ℝ) × (ι → ℝ))}

/-- Contracting with `∂_{tᵢ}` is evaluation of the `c`-component of a vector. -/
private theorem apply_inl_eq (hham : ∀ p ∈ O, ∀ i v, μ p ![(Pi.single i 1, 0), v] = v.2 i)
    {p : (ι → ℝ) × (ι → ℝ)} (hp : p ∈ O) (τ : ι → ℝ) (v : (ι → ℝ) × (ι → ℝ)) :
    μ p ![(τ, 0), v] = ∑ i, τ i * v.2 i := by
  rw [prod_mk_zero_eq_sum, ← (μ p).curryLeft_apply_apply, map_sum,
    ContinuousAlternatingMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, ContinuousAlternatingMap.smul_apply, (μ p).curryLeft_apply_apply, hham p hp,
    smul_eq_mul]

/-- **A two-form with constant contractions along the `t`-directions is independent of `t`.** If
`μ` is closed and differentiable on an open set `O` and `μ_p(∂_{tᵢ}, v) = (v.2)ᵢ` there, then the
derivative of `μ` along every vector `(τ, 0)` vanishes on `O`, i.e. `μ` is independent of `t`. -/
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
  -- Expand `dμ_p((τ, 0), v₀, v₁) = 0`: only the derivative of `μ` along `(τ, 0)` survives.
  have h3 := congrArg (fun A ↦ A ![(τ, 0), v 0, v 1]) (hcl p hp)
  simp only [extDeriv_apply_triple, hconst] at h3
  have hv : ![v 0, v 1] = v := by simp [funext_iff, Fin.forall_fin_two]
  simpa [hv] using h3

/-- Under the hypotheses of `fderiv_apply_inl_eq_zero_of_apply_inl_single_eq_snd`, the form `μ` is
constant along the `t`-directions on a ball inside `O`. -/
private theorem apply_eq_apply_fst_of_mem_ball (hO : IsOpen O) (hμ : DifferentiableOn ℝ μ O)
    (hcl : ∀ p ∈ O, extDeriv μ p = 0)
    (hham : ∀ p ∈ O, ∀ i v, μ p ![(Pi.single i 1, 0), v] = v.2 i)
    {p₀ : (ι → ℝ) × (ι → ℝ)} {r : ℝ} (hrO : ball p₀ r ⊆ O) {p : (ι → ℝ) × (ι → ℝ)}
    (hp : p ∈ ball p₀ r) : μ p = μ (p₀.1, p.2) := by
  rw [← ball_prod_same] at hrO hp
  have hmem {t : ι → ℝ} (ht : t ∈ ball p₀.1 r) : (t, p.2) ∈ O := hrO ⟨ht, hp.2⟩
  have hd : DifferentiableOn ℝ (fun t ↦ μ (t, p.2)) (ball p₀.1 r) := fun t ht ↦
    ((hμ _ (hmem ht)).differentiableAt (hO.mem_nhds (hmem ht))).comp_differentiableWithinAt t
      (differentiableAt_id.prodMk (differentiableAt_const _)).differentiableWithinAt
  refine (convex_ball p₀.1 r).is_const_of_fderivWithin_eq_zero hd (fun t ht ↦ ?_)
    hp.1 (mem_ball_self (pos_of_mem_ball hp.1))
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
  have hswap (a b : (ι → ℝ) × (ι → ℝ)) : μ p ![a, b] = -μ p ![b, a] := by
    simpa using (μ p).map_swap ![b, a] (i := 0) (j := 1) Fin.zero_ne_one
  have h1 : μ p ![v, w] = μ p ![(v.1, 0), w] - μ p ![w, (0, v.2)] := by
    conv_lhs => rw [hsplit v]
    rw [μ p |>.vecCons_add, hswap (0, v.2) w, sub_eq_add_neg]
  have h2 : μ p ![w, (0, v.2)] = μ p ![(w.1, 0), (0, v.2)] - μ p ![(0, v.2), (0, w.2)] := by
    conv_lhs => rw [hsplit w]
    rw [μ p |>.vecCons_add, hswap (0, w.2), sub_eq_add_neg]
  rw [h1, h2, apply_inl_eq hham hp, apply_inl_eq hham hp, Finset.sum_sub_distrib]
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
    hrO (ball_prod_same p₀.1 p₀.2 r ▸ ⟨mem_ball_self hr, hc⟩)
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
    ContinuousLinearMap.pi fun i ↦ ContinuousAlternatingMap.apply ℝ (ι → ℝ) ℝ fun _ ↦ Pi.single i 1
  refine ⟨fun c ↦ L (α c), by simp [hα0], L.contDiff.comp_contDiffOn hα, fun p hp v w ↦ ?_⟩
  have hp2 := (ball_prod_same p₀.1 p₀.2 r ▸ hp).2
  have hdα' : DifferentiableAt ℝ α p.2 :=
    (hα.differentiableOn (by simp) _ hp2).differentiableAt (isOpen_ball.mem_nhds hp2)
  have hda (γ : ι → ℝ) (i : ι) :
      fderiv ℝ (fun c ↦ L (α c)) p.2 γ i = fderiv ℝ (fun c ↦ α c fun _ ↦ Pi.single i 1) p.2 γ := by
    have hD : HasFDerivAt (fun c ↦ L (α c)) (L.comp (fderiv ℝ α p.2)) p.2 :=
      L.hasFDerivAt.comp p.2 hdα'.hasFDerivAt
    rw [hD.fderiv, fderiv_continuousAlternatingMap_apply_const_apply hdα']
    simp [L]
  -- The `c`-part of `μ_p` is `β_{p.2} = dα_{p.2}`, by `t`-invariance of `μ`.
  have hvv : μ p ![(0, v.2), (0, w.2)] = extDeriv α p.2 ![v.2, w.2] := by
    rw [apply_eq_apply_fst_of_mem_ball hO hμd hcl hham hrO hp, hdα _ hp2, hβ,
      ContinuousAlternatingMap.compContinuousLinearMap_apply_vecCons_two,
      ContinuousLinearMap.inr_apply, ContinuousLinearMap.inr_apply]
  rw [apply_eq_sum_add_apply_inr hham (hrO hp), hvv, extDeriv_apply_pair_eq_sum hdα',
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hda, hda, smul_eq_mul, smul_eq_mul]
  ring

end TauCeti
