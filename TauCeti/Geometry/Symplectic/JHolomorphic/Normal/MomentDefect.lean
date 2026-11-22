/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.SliceMoment
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Rescaling

/-!
# The normal Cauchy–Riemann operator of a complex normal line and its moment defects

Let `C` be a pseudoholomorphic curve with complex normal line, read in coordinates
`(z, w) ∈ V × ℂ` in which `C` is the zero section, the curve has the complex structure of `V` and
the normal fibre that of `ℂ`: the almost complex structure `J` satisfies
`J(z, 0) (v, 0) = (i v, 0)` and `J(z, 0) (0, n) = (0, i n)`. The normal linearization
`J_N = TauCeti.normalLinearization J` is the limit of the normally dilated structures, and its
block `V → ℂ` is real linear in `w`. It is complex antilinear in `v`, because `J_N² = -1`, so it
has the form

`J_N(z, w) (v, 0) = (i v, 2 i (ν(v) w + μ(v) \bar w))`,  `J_N(z, w) (0, n) = (0, i n)`

for two `(0,1)`-forms `ν` and `μ` (`TauCeti.exists_normalLinearization_apply_eq`), determined by
`J` (`TauCeti.eq_and_eq_of_normalLinearization_apply_eq`). These are the
coefficients of the normal Cauchy–Riemann operator `D_C = \bar∂ + ν W + μ \bar W`: the graph of a
section `s` has complex-linear tangent spaces for `J_N` at `z` exactly when
`\bar∂ s + s ν + \bar s μ = 0` at `z`
(`TauCeti.normalLinearization_prod_eq_iff_conjWirtingerDeriv_add_add`).

In Taubes's analysis of Seiberg–Witten solutions concentrating along `C`, the rescaled cutoff
curvature form `T` on `V × ℂ` has normal slices `μ_z`, moments `M_k = ∫ wᵏ dμ_z` and mixed moments
`Q_ℓ = ∫ w^ℓ \bar w dμ_z` (`TauCeti.sliceMoment`), and the Newton coefficients of the moments
nearly solve the equation of the elementary symmetric functions of `m` solutions of `D_C` with
the remainders driven by the defects

`E_k = \bar∂ M_k + k M_k ν + k Q_{k-1} μ`

(`TauCeti.conjWirtingerDeriv_add_eq_sum_of_newton`). For a closed form `T` with compact support in
the fibre, `E_k` is the fibre integral of `k w^(k-1) dw ∧ T⁻`, where `T⁻` is the part of `T`
anti-invariant under `J_N`
(`TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_apply_normalLinearization`): the coefficients
`ν` and `μ` are absorbed exactly, and the defects measure only the failure of `T` to have type
`(1,1)` for `J_N`.

## Main results

* `TauCeti.exists_normalLinearization_apply_eq`: the normal linearization in the coordinates of
  a complex normal line, through the `(0,1)`-forms `ν` and `μ`, which are unique
  (`TauCeti.eq_and_eq_of_normalLinearization_apply_eq`).
* `TauCeti.normalLinearization_prod_eq_iff_conjWirtingerDeriv_add_add`: the `J_N`-holomorphic
  graphs are the solutions of `\bar∂ s + s ν + \bar s μ = 0`.
* `TauCeti.conjWirtingerDeriv_sliceMoment_pow_add_add_apply_normalLinearization`: the moment
  defects `E_k` as fibre integrals of the part of `T` anti-invariant under `J_N`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818–893.
-/

public section

noncomputable section

open Complex Filter Topology
open scoped ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {J : V × ℂ → V × ℂ →L[ℝ] V × ℂ} {z : V}

/-- **The normal linearization along a curve with a complex normal line.** Suppose that at the
point `(z, 0)` of the zero section of `V × ℂ` the almost complex structure `J` is multiplication by
`i` on both factors, and that `J² = -1` near `(z, 0)`. Then there are `(0,1)`-forms `ν` and `μ` on
`V` with

`J_N(z, w) (v, 0) = (i v, 2 i (ν(v) w + μ(v) \bar w))`

for the normal linearization `J_N`, at every point `w` of the normal fibre. -/
theorem exists_normalLinearization_apply_eq (hJ₀ : ∀ v, J (z, 0) (v, 0) = (I • v, 0))
    (hJ₁ : ∀ n, J (z, 0) (0, n) = (0, I * n)) (hJ₂ : ∀ᶠ q in 𝓝 (z, 0), ∀ u, J q (J q u) = -u) :
    ∃ ν μ : V →L⋆[ℂ] ℂ, ∀ w v,
      normalLinearization J (z, w) (v, 0) = (I • v, 2 * I * (ν v * w + μ v * conj w)) := by
  -- The block `V → ℂ` of `J_N(z, w)`.
  set A : ℂ → V →L[ℝ] ℂ := fun w ↦
    ContinuousLinearMap.snd ℝ V ℂ ∘L fderiv ℝ J (z, 0) (0, w) ∘L ContinuousLinearMap.inl ℝ V ℂ
  have hA (w : ℂ) (v : V) : normalLinearization J (z, w) (v, 0) = (I • v, A w v) := by
    simp [A, hJ₀]
  -- `J_N² = -1` makes the block complex antilinear in `v`.
  have hanti (w : ℂ) (v : V) : A w (I • v) = -(I * A w v) := by
    have h := normalLinearization_apply_normalLinearization_apply (p := (z, w))
      (fun v ↦ by simp [hJ₀]) hJ₂ (v, 0)
    rw [hA, normalLinearization_apply_mk, hA, hJ₁] at h
    have h₂ := congrArg Prod.snd h
    simp only [Prod.snd_add, Prod.snd_neg, neg_zero] at h₂
    linear_combination h₂
  -- The block is real linear in the normal coordinate `w = re w + i im w`.
  have hlin (w : ℂ) (v : V) : A w v = w.re * A 1 v + w.im * A I v := by
    have hw : ((0 : V), w) = w.re • ((0 : V), (1 : ℂ)) + w.im • ((0 : V), I) := by
      refine Prod.ext (by simp) ?_
      simpa [mul_comm] using (re_add_im w).symm
    simp only [A, ContinuousLinearMap.comp_apply, hw, map_add, map_smul, add_apply, smul_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply, real_smul]
  set νR : V →L[ℝ] ℂ := (4 : ℝ)⁻¹ • (-(I • A 1) - A I)
  set μR : V →L[ℝ] ℂ := (4 : ℝ)⁻¹ • (-(I • A 1) + A I)
  have hν (v : V) : νR.complexAntilinearPart v = (-(I * A 1 v) - A I v) / 4 := by
    simp only [ContinuousLinearMap.complexAntilinearPart_apply, νR, smul_apply, sub_apply,
      neg_apply, hanti, real_smul, smul_eq_mul]
    push_cast
    linear_combination ((I * A 1 v + A I v) / 8) * I_sq
  have hμ (v : V) : μR.complexAntilinearPart v = (-(I * A 1 v) + A I v) / 4 := by
    simp only [ContinuousLinearMap.complexAntilinearPart_apply, μR, smul_apply, add_apply,
      neg_apply, hanti, real_smul, smul_eq_mul]
    push_cast
    linear_combination ((I * A 1 v - A I v) / 8) * I_sq
  refine ⟨νR.complexAntilinearPart, μR.complexAntilinearPart, fun w v ↦ ?_⟩
  rw [hA, hν, hμ, hlin w v, RCLike.conj_eq_re_sub_im w]
  refine Prod.ext rfl ?_
  linear_combination (A 1 v * w.re + A I v * w.im) * I_sq -
    (I * (I * A 1 v + A I v) / 2) * re_add_im w

/-- **The `(0,1)`-forms of the normal linearization are unique**: two pairs `(ν, μ)` and
`(ν', μ')` describing `J_N(z, w) (v, 0)` as in `TauCeti.exists_normalLinearization_apply_eq` are
equal. -/
theorem eq_and_eq_of_normalLinearization_apply_eq {ν μ ν' μ' : V →L⋆[ℂ] ℂ}
    (h : ∀ w v,
      normalLinearization J (z, w) (v, 0) = (I • v, 2 * I * (ν v * w + μ v * conj w)))
    (h' : ∀ w v,
      normalLinearization J (z, w) (v, 0) = (I • v, 2 * I * (ν' v * w + μ' v * conj w))) :
    ν = ν' ∧ μ = μ' := by
  have hw (w : ℂ) (v : V) : ν v * w + μ v * conj w = ν' v * w + μ' v * conj w := by
    have h₂ := congrArg Prod.snd ((h w v).symm.trans (h' w v))
    exact mul_left_cancel₀ (mul_ne_zero two_ne_zero I_ne_zero) h₂
  -- Evaluate at `w = 1` and `w = i`.
  have h₁ (v : V) := hw 1 v
  have hI (v : V) := hw I v
  simp only [map_one, mul_one, conj_I] at h₁ hI
  refine ⟨ContinuousLinearMap.ext fun v ↦ ?_, ContinuousLinearMap.ext fun v ↦ ?_⟩
  · linear_combination (h₁ v - I * hI v) / 2 + ((ν v - ν' v - (μ v - μ' v)) / 2) * I_sq
  · linear_combination (h₁ v + I * hI v) / 2 + ((μ v - μ' v - (ν v - ν' v)) / 2) * I_sq

/-- **The holomorphic graphs of the normal linearization solve the normal Cauchy–Riemann
equation.** Suppose that `J(z, 0)` acts on the normal fibre by multiplication by `i` and that `ν`
and `μ` are the `(0,1)`-forms of the normal linearization `J_N` at `z`
(`TauCeti.exists_normalLinearization_apply_eq`). For a section `s : V → ℂ`, the derivative
`v ↦ (v, ds(z) v)` of its graph is complex linear from `V` to `J_N(z, s(z))` exactly when
`\bar∂ s + s ν + \bar s μ = 0` at `z`. So `ν` and `μ` are the coefficients of the normal
Cauchy–Riemann operator `D_C = \bar∂ + ν W + μ \bar W`. -/
theorem normalLinearization_prod_eq_iff_conjWirtingerDeriv_add_add {ν μ : V →L⋆[ℂ] ℂ}
    (hJ₁ : ∀ n, J (z, 0) (0, n) = (0, I * n))
    (hνμ : ∀ w v,
      normalLinearization J (z, w) (v, 0) = (I • v, 2 * I * (ν v * w + μ v * conj w)))
    (s : V → ℂ) :
    (∀ v, normalLinearization J (z, s z) (v, fderiv ℝ s z v) = (I • v, fderiv ℝ s z (I • v))) ↔
      conjWirtingerDeriv s z + s z • ν + conj (s z) • μ = 0 := by
  have hsplit (v : V) : normalLinearization J (z, s z) (v, fderiv ℝ s z v) =
      (I • v, 2 * I * (ν v * s z + μ v * conj (s z)) + I * fderiv ℝ s z v) := by
    rw [normalLinearization_apply_mk, hνμ, hJ₁]
    simp
  simp only [hsplit, Prod.mk.injEq, true_and]
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun v ↦ ?_
    simp only [add_apply, smul_apply, smul_eq_mul, zero_apply, conjWirtingerDeriv_apply]
    linear_combination (-(I / 2)) * h v +
      (ν v * s z + μ v * conj (s z) + fderiv ℝ s z v / 2) * I_sq
  · intro h v
    have hv := congrArg (fun L : V →L⋆[ℂ] ℂ ↦ L v) h
    simp only [add_apply, smul_apply, smul_eq_mul, zero_apply, conjWirtingerDeriv_apply] at hv
    linear_combination (2 * I) * hv - fderiv ℝ s z (I • v) * I_sq

/-- **The moment defects for the normal linearization.** Let `T` be a `C¹` two-form on `V × ℂ`
vanishing over the complement of a compact set `K` and closed at every point of the fibre over
`z`, with normal slices `μ_z`, moments `M_k = ∫ wᵏ dμ_z` and mixed moments
`Q_ℓ = ∫ w^ℓ \bar w dμ_z`. Suppose that `J(z, 0)` acts on the normal fibre by multiplication by
`i`, and that `ν` and `μ` are the `(0,1)`-forms of the normal linearization `J_N` at `z`
(`TauCeti.exists_normalLinearization_apply_eq`), the coefficients of the normal Cauchy–Riemann
operator `D_C = \bar∂ + ν W + μ \bar W`. Then the defects of the moment equations of `D_C`,

`E_k = \bar∂ M_k + k M_k ν + k Q_{k-1} μ`,

are the fibre integrals of `k w^(k-1) dw ∧ T⁻`, where
`T⁻(u, u') = (T(u, u') - T(J_N u, J_N u')) / 2` is the part of `T` anti-invariant under `J_N`:

`E_k(v) = ∫ k w^(k-1) (i T⁻(z, w)((v, 0), ∂_x) - T⁻(z, w)((v, 0), ∂_y)) dw`. -/
theorem conjWirtingerDeriv_sliceMoment_pow_add_add_apply_normalLinearization {K : Set ℂ}
    {T : V × ℂ → (V × ℂ) [⋀^Fin 2]→L[ℝ] ℝ} (hK : IsCompact K) (hTc : ContDiff ℝ 1 T)
    (hT : ∀ z, ∀ w ∉ K, T (z, w) = 0) (hdT : ∀ w, extDeriv T (z, w) = 0) {ν μ : V →L⋆[ℂ] ℂ}
    (hJ₁ : ∀ n, J (z, 0) (0, n) = (0, I * n))
    (hνμ : ∀ w v,
      normalLinearization J (z, w) (v, 0) = (I • v, 2 * I * (ν v * w + μ v * conj w)))
    (k : ℕ) (v : V) :
    (conjWirtingerDeriv (sliceMoment T (· ^ k)) z + (k * sliceMoment T (· ^ k) z) • ν +
        (k * sliceMoment T (fun w ↦ w ^ (k - 1) * conj w) z) • μ) v =
      ∫ w, (k : ℂ) * w ^ (k - 1) *
        (I * ((T (z, w) ![(v, 0), (0, 1)] - T (z, w) ![normalLinearization J (z, w) (v, 0),
            normalLinearization J (z, w) (0, 1)]) / 2 : ℝ) -
          ((T (z, w) ![(v, 0), (0, I)] - T (z, w) ![normalLinearization J (z, w) (v, 0),
            normalLinearization J (z, w) (0, I)]) / 2 : ℝ)) :=
  conjWirtingerDeriv_sliceMoment_pow_add_add_apply hK hTc hT hdT ν μ hνμ
    (fun w n ↦ by rw [normalLinearization_apply_zero_mk, hJ₁]) k v

end TauCeti
