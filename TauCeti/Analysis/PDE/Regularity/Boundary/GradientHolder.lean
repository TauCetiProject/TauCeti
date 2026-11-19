/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.HyperplaneReflection
public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder

/-!
# Hölder continuity of the gradient up to a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝ^{n+1}`, let `ρ` be the reflection in its
boundary hyperplane, with linear part `T`, and let `U` be an open set with `ρ U ⊆ U`, such as a
ball centred on the hyperplane. Let `u ∈ H¹(U)` vanish on `U ∖ H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `U ∩ H`

weakly, with `f ∈ L^q(U ∩ H)`. So `u` is a weak solution on `U ∩ H` with zero boundary values on
the flat part `U ∩ ∂H` of the boundary. This file proves that `∇u` is Hölder continuous up to that
flat part, with every exponent `β < 1` allowed by the interior estimate, `β ≤ α` and
`β ≤ 1 - (n + 1) / q`, when the coefficients are `α`-Hölder and **invariant under the
reflection**, `a(ρ x) = T a(x) T`
(`exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL_of_holderOnWith`,
in the `TauCeti.PDE` namespace, as are the other declarations of this file). The main case is
Poisson's equation `-Δu = f`, `a = 1`
(`exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL`). This is the
`C^{1,β}` estimate up to a flat boundary on which the solution vanishes.

More precisely, the precise representative of the gradient of the odd reflection
`w = u - u ∘ ρ` is `β`-Hölder on every set `S` whose open `R`-thickening lies in `U`, with
constant

`C (R^(1 - (n + 1)/q - β) ‖f‖_{L^q(U ∩ H)} + R^(-(n + 1)/2 - β) ‖∇w‖_{L²(U)})`,

and `∇w` agrees with `∇u` almost everywhere on `U ∩ H`
(`TauCeti.W1p.gradient_sub_compHyperplaneReflectionL_ae`). The set `S` may meet the hyperplane,
so this is a boundary estimate, not an interior one.

## The argument

By the reflection principle for divergence-form equations, `w` is a weak solution on all of `U`
of the equation with the reflected coefficient and the odd reflection
`x ↦ 1_H f x - 1_H f (ρ x)` of `f` as right-hand side, whose `L^q(U)` norm is at most
`2 ‖f‖_{L^q(U ∩ H)}`. The reflected coefficient is `a` itself when `a` is invariant under the
reflection, so `w` solves the original equation on `U`
(`TauCeti.PDE.energyFormH1_sub_compHyperplaneReflectionL_eq_setIntegral`), and the interior
Schauder estimate for divergence-form equations
(`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`)
applies to `w` on `U`.

The invariance is what the reflection needs. For coefficients given on the closed half-space, it
defines `a` on the other side, and the extended field is continuous across the hyperplane exactly
when `a(x)` commutes with `T` at the points `x` of the hyperplane; for symmetric `a(x)` this says
that the conormal `a(x) ν` is normal there. Otherwise the reflected coefficient jumps across the
hyperplane. The datum must be
a scalar `f`: the odd reflection of a vector field `G` in a datum `-div G` is Hölder continuous
across the hyperplane only when the tangential part of `G` vanishes there.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.32 and 8.33 (interior and global `C^{1,α}` estimates for weak solutions).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace InnerProductSpace TauCeti.MeasureTheory
open scoped Distributions ENNReal Gradient NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Hölder continuity of the gradient up to a flat boundary.** Let `0 < β < 1` with `β ≤ α`,
`2 ≤ q` and `β ≤ 1 - (n + 1) / q`. There is a constant `C`, depending only on `n`, `α`, `β`, `q`,
`λ`, `Λ` and `M`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ`
be the reflection in the hyperplane `∂H`, with linear part `T`, and let `U` be open with
`ρ U ⊆ U`. Let `a` be measurable on `U ∩ H`, uniformly elliptic with constants `λ, Λ` on `U` and
invariant under the reflection, `a(ρ x) = T a(x) T` on `U`, and let `f ∈ L²(U ∩ H) ∩ L^q(U ∩ H)`.
Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to `U ∩ H` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_{U ∩ H} f v` for every `v ∈ H¹₀(U ∩ H)`. If the open
`R`-thickening of a set `S` lies in `U` and `a` is `α`-Hölder there with constant `K_a`, where
`K_a R^α ≤ M`, then the precise representative of the gradient of the odd reflection
`w = u - u ∘ ρ` is `β`-Hölder on `S`, with constant

`C (R^(1 - (n + 1)/q - β) ‖f‖_{L^q(U ∩ H)} + R^(-(n + 1)/2 - β) ‖∇w‖_{L²(U)})`.

The gradient `∇w` agrees with `∇u` almost everywhere on `U ∩ H`
(`TauCeti.W1p.gradient_sub_compHyperplaneReflectionL_ae`), and `S` may meet the hyperplane: this
is the `C^{1,β}` estimate up to the flat part of the boundary of `U ∩ H`, on which `u` vanishes.
-/
theorem
    exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL_of_holderOnWith
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {lam Lam M : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {u : W1p volume U 2} {Ka : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      UniformlyEllipticOn (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam →
      AEStronglyMeasurable a (volume.restrict (U ⊓ H)) →
      (∀ x ∈ U, ∀ η ξ, matrixBilinearForm (a (hyperplaneReflection ν c₀ x))
        ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) = matrixBilinearForm (a x) η ξ) →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (thickening R S) →
      (Ka : ℝ) * R ^ (α : ℝ) ≤ M →
      MemLp f 2 (volume.restrict (U ⊓ H)) → MemLp f q (volume.restrict (U ⊓ H)) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 volume (U ⊓ H) 2,
        energyFormH1 a 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
          (v : W1p volume (U ⊓ H) 2) =
            ∫ x in U ⊓ H, f x * W1p.value (v : W1p volume (U ⊓ H) 2) x) →
      0 < R → thickening R S ⊆ U →
        HolderOnWith (C * (R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) *
            (eLpNorm f q (volume.restrict (U ⊓ H))).toReal +
          R ^ (-(((n : ℝ) + 1) / 2 + β)) *
            ‖W1p.gradient
              (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)‖)).toNNReal
          β (preciseRepresentative volume (W1p.gradient
            (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) :
              EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))) S := by
  -- Bind the interior estimate before destructuring it: elaborating the destructuring pattern
  -- against the instantiated statement directly is much slower.
  have h0 :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp
      (n := n) (α := α) (β := β) (q := q) hβ hβ1 hβα hq hβq (lam := lam) (Lam := Lam) (M := M)
  obtain ⟨C, hC, hhol⟩ := h0
  refine ⟨2 * C, mul_nonneg zero_le_two hC, ?_⟩
  intro U H ν c₀ a f u Ka S R hν hH hU ha ham hinv haK hM hf2 hfq hu0 hu hR hRS
  -- The odd reflection `g` of `f` is the right-hand side of the reflected equation.
  obtain ⟨g, hgdef⟩ : ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      g = fun x => (H : Set (EuclideanSpace ℝ (Fin (n + 1)))).indicator f x -
        (H : Set (EuclideanSpace ℝ (Fin (n + 1)))).indicator f (hyperplaneReflection ν c₀ x) :=
    ⟨_, rfl⟩
  have hg : MemLp g q (volume.restrict U) := hgdef ▸
    memLp_indicator_sub_indicator_comp_hyperplaneReflection H.isOpen.measurableSet
      U.isOpen.measurableSet hU hfq hfq
  have hgf : (eLpNorm g q (volume.restrict (thickening R S))).toReal ≤
      2 * (eLpNorm f q (volume.restrict (U ⊓ H))).toReal := by
    rw [← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfq.eLpNorm_ne_top)
      ((eLpNorm_mono_measure _ (Measure.restrict_mono hRS le_rfl)).trans ?_)
    rw [hgdef]
    exact (eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le (one_le_two.trans hq)
      H.isOpen.measurableSet U.isOpen.measurableSet hU).trans_eq (two_mul _).symm
  -- The odd reflection `w = u - u ∘ ρ` solves `-∂ᵢ(aⁱʲ ∂ⱼw) = g` on `U`.
  have hw : ∀ φ : 𝓓(U, ℝ), energyFormH1 a 0 0
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)
        (W1p.ofTestFunctionₗ volume U 2 φ) =
      (∫ x in U, ⟪(0 : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x,
        ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) + ∫ x in U, g x * φ x := fun φ => by
    rw [energyFormH1_sub_compHyperplaneReflectionL_eq_setIntegral hν hH hU
      (ha.mono_set fun _ hx => hx.1) ham hinv hu0 hf2 hu
      ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
    simp only [Pi.zero_apply, inner_zero_left, integral_zero, zero_add, hgdef]
    refine setIntegral_congr_ae U.isOpen.measurableSet ?_
    filter_upwards [(ae_restrict_iff' U.isOpen.measurableSet).1
      (W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ)] with x hx hxU
    rw [hx hxU]
  have h := hhol (KG := 0) (G := 0) (ha.mono_set ((self_subset_thickening hR S).trans hRS)) haK
    ((holderWith_zero_iff.2 fun _ _ => rfl).holderOnWith _) hM
    (hg.mono_measure (Measure.restrict_mono hRS le_rfl)) hw hR hRS
  refine h.mono_const (Real.toNNReal_le_toNNReal ?_)
  -- The constant: `‖g‖_{L^q} ≤ 2 ‖f‖_{L^q(U ∩ H)}` and the gradient term is nonnegative.
  have key : ∀ X Y A : ℝ, X ≤ 2 * Y → 0 ≤ A →
      C * ((0 : ℝ≥0) * R ^ ((α : ℝ) - β) + X + A) ≤ 2 * C * (Y + A) := fun X Y A hXY hA => by
    push_cast
    nlinarith [mul_nonneg hC (sub_nonneg.2 hXY), mul_nonneg hC hA]
  refine key _ _ _ ?_ (by positivity)
  rw [mul_left_comm]
  gcongr

/-- **Hölder continuity of the gradient up to a flat boundary for Poisson's equation.** Let
`0 < β < 1`, `2 ≤ q` and `β ≤ 1 - (n + 1) / q`. There is a constant `C`, depending only on `n`,
`β` and `q`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ` be
the reflection in the hyperplane `∂H` and let `U` be open with `ρ U ⊆ U`. Let
`f ∈ L²(U ∩ H) ∩ L^q(U ∩ H)`, and let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to
`U ∩ H` be a weak solution of `-Δu = f`. If the open `R`-thickening of a set `S` lies in `U`, then
the precise representative of the gradient of the odd reflection `w = u - u ∘ ρ`, which agrees
with `∇u` almost everywhere on `U ∩ H`, is `β`-Hölder on `S`, with constant

`C (R^(1 - (n + 1)/q - β) ‖f‖_{L^q(U ∩ H)} + R^(-(n + 1)/2 - β) ‖∇w‖_{L²(U)})`.

This is the case `a = 1` of
`exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL_of_holderOnWith`:
the identity matrix is invariant under every reflection. -/
theorem exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL
    {β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {ν : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {u : W1p volume U 2}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      MemLp f 2 (volume.restrict (U ⊓ H)) → MemLp f q (volume.restrict (U ⊓ H)) →
      (∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 volume (U ⊓ H) 2,
        energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
          (v : W1p volume (U ⊓ H) 2) =
            ∫ x in U ⊓ H, f x * W1p.value (v : W1p volume (U ⊓ H) 2) x) →
      0 < R → thickening R S ⊆ U →
        HolderOnWith (C * (R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) *
            (eLpNorm f q (volume.restrict (U ⊓ H))).toReal +
          R ^ (-(((n : ℝ) + 1) / 2 + β)) *
            ‖W1p.gradient
              (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)‖)).toNNReal
          β (preciseRepresentative volume (W1p.gradient
            (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) :
              EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))) S := by
  obtain ⟨C, hC, h⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL_of_holderOnWith
      (n := n) (α := β) hβ hβ1 le_rfl hq hβq (lam := 1) (Lam := 1) (M := 0)
  refine ⟨C, hC, ?_⟩
  intro U H ν c₀ f u S R hν hH hU hf2 hfq hu0 hu hR hRS
  refine h (Ka := 0) hν hH hU (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const
    (fun _ _ η ξ => ?_) ((holderWith_zero_iff.2 fun _ _ => rfl).holderOnWith _) (by simp) hf2 hfq
    hu0 hu hR hRS
  -- The reflection is an isometry, so it preserves the dot product.
  have h := LinearIsometryEquiv.inner_map_map ((ℝ ∙ ν)ᗮ.reflection) ξ η
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa only [matrixBilinearForm_one_apply, star_trivial] using h

end PDE

end TauCeti
