/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.NowhereVanishing
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Duality
import TauCeti.Analysis.Complex.RiemannSurface.Differential.IdentityTheorem
import TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Order
import TauCeti.Analysis.Complex.RiemannSurface.Genus

/-!
# Holomorphic `1`-forms in genus one

Let `X` be a compact connected Hausdorff Riemann surface. Then `X` has genus one, equivalently
Euler characteristic zero, exactly when it carries a holomorphic `1`-form that vanishes nowhere
(`TauCeti.RiemannSurface.exists_mem_holomorphicOneForms_forall_apply_ne_zero_iff_genus_eq_one`,
`TauCeti.RiemannSurface.exists_mem_holomorphicOneForms_forall_apply_ne_zero_iff_eulerChar_eq_zero`).
In genus one every nonzero holomorphic `1`-form vanishes nowhere
(`TauCeti.RiemannSurface.OneForm.apply_ne_zero_of_genus_eq_one`).

In one direction, `h⁰(Ω) = genus X = 1` gives a nonzero holomorphic `1`-form `ω`. Its divisor is
effective and canonical, of degree `2 genus X - 2 = 0`, hence zero, so `ω` has order zero, and is
nonzero, everywhere. Conversely, the divisor of a nowhere vanishing holomorphic `1`-form is zero,
so the zero divisor is canonical and `0 = 2 genus X - 2`.

Such a form is the starting point of the classification of surfaces of genus one by complex tori,
whose lattice is the group of periods of the form. Its local primitives are flat charts, with
translations as transition maps
(`TauCeti.RiemannSurface.OneForm.HolomorphicAt.exists_mem_maximalAtlas_mvfderiv_eq`).

## Main results

* `TauCeti.RiemannSurface.OneForm.apply_ne_zero_of_genus_eq_one`: in genus one, a nonzero
  holomorphic `1`-form vanishes nowhere.
* `TauCeti.RiemannSurface.exists_mem_holomorphicOneForms_forall_apply_ne_zero_iff_genus_eq_one`:
  genus one is equivalent to the existence of a nowhere vanishing holomorphic `1`-form.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the degree of a canonical divisor) and §21 (surfaces of genus one).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter VII §1 (holomorphic `1`-forms in genus one).
-/

public section

open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X]
  [T2Space X] [ConnectedSpace X]

/-- **In genus one, nonzero holomorphic `1`-forms vanish nowhere.** On a compact connected
Hausdorff Riemann surface of genus one, a nonzero holomorphic `1`-form is nonzero at every
point. -/
theorem OneForm.apply_ne_zero_of_genus_eq_one (hg : genus X = 1) {ω : OneForm X}
    (hω : ω ∈ holomorphicOneForms X) (hω₀ : ω ≠ 0) (x : X) : ω x ≠ 0 := by
  have hhol := mem_holomorphicOneForms.1 hω
  have htop : ∀ y, ω.order y ≠ ⊤ := fun y h ↦ hω₀ ((order_eq_top_iff_eq_zero hhol y).1 h)
  -- The divisor of `ω` is effective and canonical, of degree `2 · 1 - 2 = 0`.
  have hdeg := (isCanonicalDivisor_divisor (meromorphicAt_of_mem_holomorphicOneForms hω)
    htop).degree_eq_two_mul_analyticGenus_sub_two
  rw [analyticGenus_eq_genus, hg] at hdeg
  have hdiv : 0 = ω.divisor :=
    WeilDivisor.eq_of_le_of_degree_eq (divisor_nonneg hhol) (by rw [hdeg]; simp)
  have hx := coe_coeff_divisor (meromorphicAt_of_mem_holomorphicOneForms hω) (htop x)
  rw [← hdiv, WeilDivisor.coeff_zero] at hx
  exact ((hhol x).order_eq_zero_iff).1 (by rw [← hx, WithTop.coe_zero])

/-- **Genus one and nowhere vanishing `1`-forms.** A compact connected Hausdorff Riemann surface
carries a nowhere vanishing holomorphic `1`-form exactly when it has genus one. -/
theorem exists_mem_holomorphicOneForms_forall_apply_ne_zero_iff_genus_eq_one :
    (∃ ω ∈ holomorphicOneForms X, ∀ x, ω x ≠ 0) ↔ genus X = 1 := by
  refine ⟨fun ⟨ω, hω, hω₀⟩ ↦ ?_, fun hg ↦ ?_⟩
  · have h := (OneForm.isCanonicalDivisor_zero_of_apply_ne_zero hω hω₀)
      |>.degree_eq_two_mul_analyticGenus_sub_two
    rw [map_zero, analyticGenus_eq_genus] at h
    omega
  · have : Nontrivial (holomorphicOneForms X) := Module.nontrivial_of_finrank_pos (R := ℂ) <| by
      rw [finrank_holomorphicOneForms_eq_genus, hg]
      exact Nat.one_pos
    obtain ⟨⟨ω, hω⟩, hω₀⟩ := exists_ne (0 : holomorphicOneForms X)
    have hω₀ : ω ≠ 0 := fun h ↦ hω₀ (by simp [h])
    exact ⟨ω, hω, OneForm.apply_ne_zero_of_genus_eq_one hg hω hω₀⟩

/-- **Euler characteristic zero and nowhere vanishing `1`-forms.** A compact connected Hausdorff
Riemann surface carries a nowhere vanishing holomorphic `1`-form exactly when its Euler
characteristic is zero. -/
theorem exists_mem_holomorphicOneForms_forall_apply_ne_zero_iff_eulerChar_eq_zero :
    (∃ ω ∈ holomorphicOneForms X, ∀ x, ω x ≠ 0) ↔ eulerChar X = 0 := by
  rw [exists_mem_holomorphicOneForms_forall_apply_ne_zero_iff_genus_eq_one,
    eulerChar_eq_two_sub_two_mul_genus]
  omega

end TauCeti.RiemannSurface
