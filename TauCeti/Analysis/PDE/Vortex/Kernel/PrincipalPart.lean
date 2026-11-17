/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Kernel.Dimension
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Isomorphism of the gauge-fixed vortex kernel with principal-part data

Let `x` be a smooth field on the plane whose holomorphicity rows `∂bar_a α = 0` vanish, with
`|α| → 1` at infinity, and let `D` be the zero divisor of its section `α = 2 (p + i q)`. For any
integrating factor `ν` solving `∂bar ν = (b₂ - i b₁) / 2`, every variation `y` in the `C²`
square-integrable kernel `gaugeFixedKernel x` of the gauge-fixed operator `L_x = d₀* ⊕ d₁`
decomposes as `δα = α G + e^ν H` with `G` continuous and `H` entire
(`exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel`). Recording the
Taylor derivatives `H⁽ʲ⁾(z)` for `j < count z D` defines the real-linear principal-part map
`principalPartMap` from `gaugeFixedKernel x` to `D → ℂ`, proved injective in
`TauCeti.Analysis.PDE.Vortex.PrincipalPart`.

This file combines injectivity of `principalPartMap` with the exact real dimension `2 |D|` and
smoothness of `gaugeFixedKernel x` from `TauCeti.Analysis.PDE.Vortex.Kernel.Dimension`
(`finrank_gaugeFixedKernel_eq_two_mul_card`, `contDiff_of_mem_gaugeFixedKernel`) to show that
`principalPartMap` is bijective (`principalPartMap_bijective`, `principalPartMap_surjective`),
defining the real-linear equivalence `gaugeFixedKernelEquivPrincipalPart :
gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ)` and producing a smooth kernel element realizing
any prescribed principal-part tuple (`exists_contDiff_mem_gaugeFixedKernel_principalPart_eq`). The
comparison with the weak `L²` and Sobolev `H^s` kernels of `L_x` is proved in
`TauCeti.Analysis.PDE.Vortex.Kernel.Weak`; no Fredholm operator bundle is constructed here.

## Main declarations

* `TauCeti.Vortex.exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel`:
  decomposition `δα = α G + e^ν H` on `gaugeFixedKernel x`.
* `TauCeti.Vortex.principalPartMap_bijective` and `TauCeti.Vortex.principalPartMap_surjective`:
  bijectivity and surjectivity of `principalPartMap` on `gaugeFixedKernel x`.
* `TauCeti.Vortex.gaugeFixedKernelEquivPrincipalPart`: the real-linear equivalence
  `gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ)`.
* `TauCeti.Vortex.exists_contDiff_mem_gaugeFixedKernel_principalPart_eq`: every tuple in `D → ℂ`
  is the principal-part data of a smooth element of `gaugeFixedKernel x`.

## References

* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory
open scoped ContDiff Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {D : Multiset ℂ}

/-- Every variation `y ∈ gaugeFixedKernel x` at a differentiable field satisfying the
holomorphicity rows admits a decomposition `δα = α G + e^ν H` with `G` continuous and `H` entire,
supplying the domain hypothesis of `TauCeti.Vortex.principalPartMap`. -/
theorem exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel
    (hx : Differentiable ℝ x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    {ν : ℂ → ℂ} (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
  obtain ⟨hy₀, hy₁, hy₂, hy₃, hlin⟩ := gaugeFixedKernel_linearizedEquation y hy
  have hxi (i : Fin 4) : Differentiable ℝ fun w ↦ x w i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable.comp hx
  obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul (k := 2) (by norm_num)
    (hxi 2) (hxi 3) hhol hν hνeq hy₀ hy₁ hy₂ hy₃ hlin
  exact ⟨G, hG.continuous, H, hH, hGH⟩

/-- Any differentiable integrating factor `∂bar ν = (b₂ - i b₁) / 2` for a smooth connection differs
from a `C²` Dolbeault solution by an entire function, hence is `C²`. -/
private theorem contDiff_of_conjWirtingerDeriv_apply_one_eq (hx : ContDiff ℝ ∞ x) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    ContDiff ℝ 2 ν := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    contDiff_euclidean.1 (hx.of_le (by simp)) i
  obtain ⟨ν', hν', hν'eq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq (by norm_num)
      (contDiff_connectionCoeff (hxi 0) (hxi 1))
  have hdiff : Differentiable ℂ (ν - ν') := fun w ↦
    (differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero
      ((hν w).sub (hν'.differentiable (by norm_num) w))).2 <| by
      rw [conjWirtingerDeriv_sub (hν w) (hν'.differentiable (by norm_num) w),
        sub_apply, hνeq w, hν'eq w, sub_self]
  have hsmooth : ContDiff ℝ 2 (ν - ν') :=
    ((hdiff.contDiff (n := ∞)).restrict_scalars ℝ).of_le (by simp)
  simpa using hsmooth.add hν'

/-- **Bijectivity of the principal-part map on `gaugeFixedKernel x`.** -/
theorem principalPartMap_bijective (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    Function.Bijective (principalPartMap hD hν.continuous hdec) := by
  have hx₂ : ContDiff ℝ 2 x := hx.of_le (by simp)
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx₂ i
  have hν₂ : ContDiff ℝ 2 ν := contDiff_of_conjWirtingerDeriv_apply_one_eq hx hν hνeq
  have hinj : Function.Injective (principalPartMap hD hν.continuous hdec) :=
    principalPartMap_injective (k := 2) (by norm_num) (hxi 0) (hxi 1)
      ((hxi 2).differentiable (by norm_num)) ((hxi 3).differentiable (by norm_num)) hhol hD hν₂
      hνeq gaugeFixedKernel_linearizedEquation hdec fun y hy η hη hyη ↦ by
        obtain ⟨hyc, hy₂, hker⟩ := mem_gaugeFixedKernel.1 hy
        exact eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
          (hx.of_le (by simp)) hhol hlim hyc.continuous hy₂ hker hη hyη
  have := finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume) hx₂ hhol hlim hD
    fun _ ↦ mem_gaugeFixedKernel.1
  have hfin : Module.finrank ℝ (gaugeFixedKernel x) =
      Module.finrank ℝ (Multiset.ToType D → ℂ) := by
    rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD, Module.finrank_pi_fintype,
      Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul, Finset.card_univ,
      Multiset.card_coe, mul_comm]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj⟩

/-- **Surjectivity of the principal-part map on `gaugeFixedKernel x`.** -/
theorem principalPartMap_surjective (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧
      ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
        ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    Function.Surjective (principalPartMap hD hν.continuous hdec) :=
  (principalPartMap_bijective hx hhol hlim hD hν hνeq hdec).2

/-- **The principal-part linear equivalence.** At a smooth field `x` with `∂bar_a α = 0`,
`|α|² → 1` at infinity, and section zero divisor `D`, the principal-part map for any
differentiable integrating factor `ν` is a real-linear isomorphism
`gaugeFixedKernel x ≃ₗ[ℝ] (D → ℂ)`. -/
def gaugeFixedKernelEquivPrincipalPart (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ) :=
  LinearEquiv.ofBijective
    (principalPartMap hD hν.continuous fun _ hy ↦
      exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel
        (hx.differentiable (by simp)) hhol hν hνeq hy)
    (principalPartMap_bijective hx hhol hlim hD hν hνeq _)

/-- `gaugeFixedKernelEquivPrincipalPart` evaluates at `(z, k)` to `principalPart x ν y z k`. -/
@[simp]
theorem gaugeFixedKernelEquivPrincipalPart_apply (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (y : gaugeFixedKernel x) (i : Multiset.ToType D) :
    gaugeFixedKernelEquivPrincipalPart hx hhol hlim hD hν hνeq y i =
      principalPart x ν y i.1 i.2 := by
  simp [gaugeFixedKernelEquivPrincipalPart]

/-- **Existence of smooth kernel elements with arbitrary principal-part data.** Let `x` be a smooth
field on the plane with `∂bar_a α = 0` and `|α|² → 1` at infinity, let `D` be the zero divisor of
`α`, and let `∂bar ν = (b₂ - i b₁) / 2`. Every tuple `φ : D → ℂ` is realized as the principal-part
data of a smooth element of `gaugeFixedKernel x`. -/
theorem exists_contDiff_mem_gaugeFixedKernel_principalPart_eq (hx : ContDiff ℝ ∞ x)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) {ν : ℂ → ℂ}
    (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (φ : Multiset.ToType D → ℂ) :
    ∃ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ y ∧ y ∈ gaugeFixedKernel x ∧
      ∀ i : Multiset.ToType D, principalPart x ν y i.1 i.2 = φ i := by
  set e := gaugeFixedKernelEquivPrincipalPart hx hhol hlim hD hν hνeq
  refine ⟨(e.symm φ : ℂ → EuclideanSpace ℝ (Fin 4)),
    contDiff_of_mem_gaugeFixedKernel hx hhol hlim (e.symm φ).2, (e.symm φ).2, fun i ↦ ?_⟩
  simpa [e] using congrFun (e.apply_symm_apply φ) i

end TauCeti.Vortex
