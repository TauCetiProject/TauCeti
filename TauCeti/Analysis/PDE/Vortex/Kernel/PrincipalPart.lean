/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Kernel.Dimension

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

At a smooth field, `TauCeti.Analysis.PDE.Vortex.Kernel.Dimension` packages this map as the
real-linear equivalence `principalPartEquiv : gaugeFixedKernel x ≃ₗ[ℝ] (Multiset.ToType D → ℂ)`
for one particular choice of decomposition. This file records the decomposition for any
differentiable integrating factor at a differentiable field, and that `principalPartMap` is
bijective and surjective for every choice of decomposition (`principalPartMap_bijective`,
`principalPartMap_surjective`). The comparison with the weak `L²` and Sobolev `H^s` kernels of
`L_x` is proved in `TauCeti.Analysis.PDE.Vortex.WeakKernel`.

## Main declarations

* `TauCeti.Vortex.exists_continuous_and_differentiable_sectionValue_eq_of_mem_gaugeFixedKernel`:
  decomposition `δα = α G + e^ν H` on `gaugeFixedKernel x`.
* `TauCeti.Vortex.principalPartMap_bijective` and `TauCeti.Vortex.principalPartMap_surjective`:
  bijectivity and surjectivity of `principalPartMap` on `gaugeFixedKernel x`.

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
  have h : ⇑(principalPartMap hD hν.continuous hdec) = principalPartEquiv hx hhol hlim hD hν hνeq :=
    funext fun y ↦ funext fun i ↦ by rw [principalPartMap_apply, principalPartEquiv_apply]
  exact h ▸ (principalPartEquiv hx hhol hlim hD hν hνeq).bijective

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

end TauCeti.Vortex
