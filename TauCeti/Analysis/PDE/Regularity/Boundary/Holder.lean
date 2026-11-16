/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.HyperplaneReflection
public import TauCeti.Analysis.PDE.Regularity.HolderContinuity
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous

/-!
# De Giorgi's Hölder estimate up to a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝⁿ`, `n ≥ 1`, let `ρ` be the reflection in
its boundary hyperplane, and let `U` be an open set with `ρ U ⊆ U`, such as a ball centred on the
hyperplane. Let `a` be measurable and uniformly elliptic with constants `λ, Λ` on the part of `U`
in the closed half-space, and let `u ∈ H¹(U)` vanish on `U ∖ H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = 0` in `U ∩ H`

weakly. So `u` is a weak solution on `U ∩ H` with zero boundary values on the flat part
`U ∩ ∂H` of the boundary. This file proves that `u` is Hölder continuous up to that flat part,
with De Giorgi's exponent `α` and constants depending only on `λ`, `Λ`, the dimension and the
normalization of the Haar measure
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL`). The same
holds for `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu = 0` with a bounded measurable drift `‖b‖ ≤ β`, on scales `R`
with `βR/λ` bounded
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_drift`),
and for `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with a right-hand side `f ∈ L² ∩ Lʳ(U ∩ H)`, `r > 1` and `r > n/2`,
with `α` and `C` depending also on `r`
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp`).
It also holds for `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with a vector field `F ∈ L² ∩ L^q(U ∩ H; ℝⁿ)`, `q > 2` and
`q > n`
(`exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp_divergence`),
and for `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ` with both data
(`exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp_add_divergence`).
The divergence datum is what a nonzero boundary value turns into: if `u = g` on the flat boundary,
then `u - g` vanishes there and solves the equation with the extra datum `∂ᵢ(aⁱʲ ∂ⱼg)`.

More precisely, for the homogeneous equation the precise representative of the odd reflection
`w = u - u ∘ ρ` is `α`-Hölder on every set `K` whose closed `R`-thickening lies in `U`, with
constant `C R^(-α - n/2) ‖w‖_{L²(U)}`, and `w` agrees with `u` on `U ∩ H`
(`TauCeti.W1p.value_sub_compHyperplaneReflectionL_ae`). With a right-hand side `f` the constant is
`C R^(-α) (R^(-n/2) ‖w‖_{L²(U)} + R^(2 - n/r) ‖f‖_{Lʳ(U ∩ H)} / λ)`. The set `K` may meet the
hyperplane: this is a boundary estimate, not an interior one.

## The argument

By the reflection principle for divergence-form equations
(`TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL`), `w` is a weak
solution on all of `U` of `-∂ᵢ(a'ⁱʲ ∂ⱼw) = 0` with the reflected coefficient `a'`, which is
measurable and uniformly elliptic with the same constants `λ, Λ`
(`TauCeti.PDE.UniformlyEllipticOn.reflectPrincipal`). A drift `b` is reflected to `R b(ρ x)`
below the hyperplane, which keeps the bound `‖b‖ ≤ β` (`TauCeti.PDE.norm_reflectDrift_le`). De
Giorgi's interior theorem (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_drift`) applies
to `w` on `U`, and the reflected coefficients are merely measurable and bounded, which is all that
theorem needs.

A right-hand side `f` is reflected oddly: `w` solves the reflected equation on `U` with right-hand
side `x ↦ 1_H f x - 1_H f (ρ x)`
(`TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral`), whose
`Lʳ(U)` norm is at most `2 ‖f‖_{Lʳ(U ∩ H)}`, and De Giorgi's interior theorem with a right-hand
side (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp`) applies to it.

A vector field `F` is reflected as a vector field: with `R` the linear part of `ρ`, `w` solves the
reflected equation with the datum `∂ᵢGⁱ` for `G = 1_H F - R (1_H F ∘ ρ)`
(`TauCeti.PDE.energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub`),
because the gradient of `φ - φ ∘ ρ` is `∇φ - R (∇φ ∘ ρ)` and `R` is a self-adjoint involution. Its
`L^q(U)` norm is again at most `2 ‖F‖_{L^q(U ∩ H)}`, and De Giorgi's interior theorem with a
right-hand side in divergence form
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp_divergence`, or
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence` with both data)
applies.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.24 and 8.29 (interior and global Hölder estimates for weak solutions).
* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali multipli
  regolari*, Mem. Accad. Sci. Torino 3 (1957), 25–43.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace TauCeti.MeasureTheory
open scoped NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

/-- **De Giorgi's theorem with a drift up to a flat boundary.** Let `n ≥ 1` be the dimension,
and fix a bound `σ` for `βR/λ`. There are `α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`,
`σ`, the dimension and the normalization of the additive Haar measure `mu`, such that the
following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ` be the reflection in the
hyperplane `∂H` and let `U` be open with `ρ U ⊆ U`. Let `a` and `b` be measurable on `U ∩ H`, with
`a` uniformly elliptic with constants `λ, Λ` and `‖b‖ ≤ β` on the part of `U` in the closed
half-space `{x | c₀ ≤ ⟪x, ν⟫}`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to
`U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu = 0`. If the closed `R`-thickening of a set
`K` lies in `U` and `βR ≤ σλ`, then the precise representative of the odd reflection
`w = u - u ∘ ρ`, which agrees with `u` on `U ∩ H`, is Hölder continuous on `K` with exponent `α`
and constant `C R^(-α - n/2) ‖w‖_{L²(U)}`. -/
theorem exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_drift
    [Nonempty ι] (σ : ℝ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ ι)}
      {ν : EuclideanSpace ℝ ι} {c₀ : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {beta : ℝ}
      {u : W1p mu U 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ}, ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      UniformlyEllipticOn {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam →
      AEStronglyMeasurable a (mu.restrict (U ⊓ H)) →
      AEStronglyMeasurable b (mu.restrict (U ⊓ H)) →
      (∀ x ∈ {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ}, ‖b x‖ ≤ beta) →
      (∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 mu (U ⊓ H) 2,
        energyFormH1 a b 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
          (v : W1p mu (U ⊓ H) 2) = 0) →
      0 < R → Metric.cthickening R K ⊆ (U : Set (EuclideanSpace ℝ ι)) → beta * R ≤ σ * lam →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ y in U, W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU
            u) y ^ 2 ∂mu))).toNNReal α
          (preciseRepresentative mu
            (W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u))) K := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_drift (mu := mu) (lam := lam) (Lam := Lam) (ι := ι) σ
  refine ⟨α, C, hα, hα1, hC,
    fun {U H ν c₀ a b beta u K R} hν hH hU ha ham hbm hb hu0 hu hR hRK hβR => ?_⟩
  have ha' : UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) (reflectPrincipal ν c₀ a) lam
      Lam := ha.reflectPrincipal hν hU
  have ham' := aestronglyMeasurable_reflectPrincipal hν hH hU ham
  have hbm' := aestronglyMeasurable_reflectDrift hν hH hU hbm
  have hb' : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)), ‖reflectDrift ν c₀ b x‖ ≤ beta :=
    fun x hx => norm_reflectDrift_le hν hb hU hx
  refine hhol ha' ham' hbm' hb' (fun φ => ?_) hR hRK hβR
  have h := energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL hν hH hU
    (memLp_energyIntegrand_reflectPrincipal (c := 0) (gamma := 0) hν hH hU ha ham hbm
      aestronglyMeasurable_const hb (fun _ _ => by simp)) hu0
    (ℓ := 0) (fun v => by rw [zero_apply]; exact hu v) φ
  rwa [reflectDensity_zero] at h

/-- **De Giorgi's theorem up to a flat boundary.** Let `n ≥ 1` be the dimension. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, the dimension and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H` and let `U` be open with `ρ U ⊆ U`. Let
`a` be measurable on `U ∩ H` and uniformly elliptic with constants `λ, Λ` on the part of `U` in
the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its
restriction to `U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`. If the closed `R`-thickening of
a set `K` lies in `U`, then the precise representative of the odd reflection `w = u - u ∘ ρ`,
which agrees with `u` on `U ∩ H`, is Hölder continuous on `K` with exponent `α` and constant
`C R^(-α - n/2) ‖w‖_{L²(U)}`. This is the case `b = 0` of
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_drift`. -/
theorem exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL [Nonempty ι] :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ ι)}
      {ν : EuclideanSpace ℝ ι} {c₀ : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {u : W1p mu U 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ}, ν ≠ 0 →
      (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      UniformlyEllipticOn {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam →
      AEStronglyMeasurable a (mu.restrict (U ⊓ H)) →
      (∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 mu (U ⊓ H) 2,
        energyFormH1 a 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
          (v : W1p mu (U ⊓ H) 2) = 0) →
      0 < R → Metric.cthickening R K ⊆ (U : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ y in U, W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU
            u) y ^ 2 ∂mu))).toNNReal α
          (preciseRepresentative mu
            (W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u))) K := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_drift (mu := mu)
      (lam := lam) (Lam := Lam) (ι := ι) 0
  exact ⟨α, C, hα, hα1, hC, fun hν hH hU ha ham hu0 hu hR hRK =>
    hhol (beta := 0) hν hH hU ha ham aestronglyMeasurable_const (fun _ _ => by simp) hu0 hu hR hRK
      (by simp)⟩

/-- Doubling the data term: if `0 ≤ A` and `X ≤ 2 Y`, then `k (A + X / λ) ≤ 2 k (A + Y / λ)`.
This absorbs the factor `2` by which odd reflection can increase the norm of a datum. -/
private theorem mul_add_div_le_two_mul_mul_add_div {k A X Y lam : ℝ} (hk : 0 ≤ k) (hA : 0 ≤ A)
    (hlam : 0 < lam) (hXY : X ≤ 2 * Y) : k * (A + X / lam) ≤ 2 * k * (A + Y / lam) := by
  have h : X / lam ≤ 2 * (Y / lam) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right hXY hlam.le
  calc k * (A + X / lam) ≤ k * (2 * (A + Y / lam)) :=
        mul_le_mul_of_nonneg_left (by linarith) hk
    _ = 2 * k * (A + Y / lam) := by ring

omit [DecidableEq ι] in
/-- The odd reflection `1_H f - 1_H f ∘ ρ` of `f ∈ Lʳ(U ∩ H)`, `r ≥ 1`, has `Lʳ(U)` norm at most
twice that of `f`. -/
private theorem toReal_eLpNorm_indicator_sub_indicator_comp_le
    {U H : Opens (EuclideanSpace ℝ ι)} {ν : EuclideanSpace ℝ ι} {c₀ : ℝ}
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {r : ℝ≥0} (hr : 1 ≤ (r : ℝ))
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f r (mu.restrict (U ⊓ H))) :
    (eLpNorm (fun x => (H : Set (EuclideanSpace ℝ ι)).indicator f x -
      (H : Set (EuclideanSpace ℝ ι)).indicator f (hyperplaneReflection ν c₀ x)) r
        (mu.restrict U)).toReal ≤ 2 * (eLpNorm f r (mu.restrict (U ⊓ H))).toReal := by
  rw [← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hf.eLpNorm_ne_top)
    (eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le (by exact_mod_cast hr)
      H.isOpen.measurableSet U.isOpen.measurableSet hU)

omit [DecidableEq ι] in
/-- The odd reflection `1_H F - R (1_H F ∘ ρ)` of a vector field `F ∈ L^q(U ∩ H)`, `q ≥ 1`, where
`R` is the linear part of `ρ`, has `L^q(U)` norm at most twice that of `F`. -/
private theorem toReal_eLpNorm_indicator_sub_reflection_indicator_comp_le
    {U H : Opens (EuclideanSpace ℝ ι)} {ν : EuclideanSpace ℝ ι} {c₀ : ℝ}
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {q : ℝ≥0} (hq : 1 ≤ (q : ℝ))
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hF : MemLp F q (mu.restrict (U ⊓ H))) :
    (eLpNorm (fun x => (H : Set (EuclideanSpace ℝ ι)).indicator F x -
      (ℝ ∙ ν)ᗮ.reflection ((H : Set (EuclideanSpace ℝ ι)).indicator F
        (hyperplaneReflection ν c₀ x))) q (mu.restrict U)).toReal ≤
      2 * (eLpNorm F q (mu.restrict (U ⊓ H))).toReal := by
  rw [← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hF.eLpNorm_ne_top)
    (eLpNorm_indicator_sub_linearIsometry_indicator_comp_hyperplaneReflection_le
      (ℝ ∙ ν)ᗮ.reflection.toLinearIsometry (by exact_mod_cast hq) H.isOpen.measurableSet
      U.isOpen.measurableSet hU)

/-- **De Giorgi's theorem with a right-hand side up to a flat boundary.** Let `n ≥ 1` be the
dimension and let `r > 1` with `r > n/2`. There are `α ∈ (0, 1]` and `C > 0`, depending only on
`λ`, `Λ`, `n`, `r` and the normalization of the additive Haar measure `mu`, such that the following
holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ` be the reflection in the hyperplane
`∂H` and let `U` be open with `ρ U ⊆ U`. Let `a` be measurable on `U ∩ H` and uniformly elliptic
with constants `λ, Λ` on the part of `U` in the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`, and let
`f ∈ L²(U ∩ H) ∩ Lʳ(U ∩ H)`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to
`U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_{U ∩ H} f v` for every
`v ∈ H¹₀(U ∩ H)`. If the closed `R`-thickening of a set `K` lies in `U`, then the precise
representative of the odd reflection `w = u - u ∘ ρ`, which agrees with `u` on `U ∩ H`, is Hölder
continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖w‖_{L²(U)} + R^(2 - n/r) ‖f‖_{Lʳ(U ∩ H)} / λ)`.

The set `K` may meet the hyperplane, so this is an estimate up to the flat part of the boundary
of `U ∩ H`, on which `u` vanishes. -/
theorem exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp
    [Nonempty ι] {lam Lam : ℝ} {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ ι)}
      {ν : EuclideanSpace ℝ ι} {c₀ : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu U 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      UniformlyEllipticOn {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam →
      AEStronglyMeasurable a (mu.restrict (U ⊓ H)) →
      MemLp f 2 (mu.restrict (U ⊓ H)) → MemLp f r (mu.restrict (U ⊓ H)) →
      (∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 mu (U ⊓ H) 2,
        energyFormH1 a 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
          (v : W1p mu (U ⊓ H) 2) =
            ∫ x in U ⊓ H, f x * W1p.value (v : W1p mu (U ⊓ H) 2) x ∂mu) →
      0 < R → Metric.cthickening R K ⊆ (U : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ y in U, W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU
            u) y ^ 2 ∂mu) + R ^ (2 - (Fintype.card ι : ℝ) / r) *
              (eLpNorm f r (mu.restrict (U ⊓ H))).toReal / lam)).toNNReal α
          (preciseRepresentative mu
            (W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u))) K := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_memLp (mu := mu) (lam := lam) (Lam := Lam) hr hrn
  refine ⟨α, 2 * C, hα, hα1, by positivity,
    fun {U H ν c₀ a f u K R} hν hH hU ha ham hf2 hfr hu0 hu hR hRK => ?_⟩
  have ha' : UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) (reflectPrincipal ν c₀ a) lam
      Lam := ha.reflectPrincipal hν hU
  have hlam := ha'.pos
  -- The odd reflection `g` of `f` is the right-hand side of the reflected equation.
  set g : EuclideanSpace ℝ ι → ℝ := fun x => (H : Set (EuclideanSpace ℝ ι)).indicator f x -
    (H : Set (EuclideanSpace ℝ ι)).indicator f (hyperplaneReflection ν c₀ x)
  have hg : MemLp g r (mu.restrict U) :=
    memLp_indicator_sub_indicator_comp_hyperplaneReflection H.isOpen.measurableSet
      U.isOpen.measurableSet hU hfr
  have hgf : (eLpNorm g r (mu.restrict U)).toReal ≤
      2 * (eLpNorm f r (mu.restrict (U ⊓ H))).toReal :=
    toReal_eLpNorm_indicator_sub_indicator_comp_le hU (by exact_mod_cast hr.le) hfr
  have hw : ∀ v : W1p0 mu U 2, energyFormH1 (reflectPrincipal ν c₀ a) 0 0
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) (v : W1p mu U 2) =
        ∫ x in U, g x * W1p.value (v : W1p mu U 2) x ∂mu := fun v => by
    have h := energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral hν hH hU
      (memLp_energyIntegrand_reflectPrincipal (b := 0) (c := 0) (beta := 0) (gamma := 0) hν hH hU
        ha ham aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
        (fun _ _ => by simp)) hu0 hf2 hu v
    rwa [reflectDrift_zero, reflectDensity_zero] at h
  refine (hhol ha' (aestronglyMeasurable_reflectPrincipal hν hH hU ham) hg hw hR hRK).mono_const
    (Real.toNNReal_le_toNNReal ?_)
  -- The constant: `‖g‖_{Lʳ(U)} ≤ 2 ‖f‖_{Lʳ(U ∩ H)}` and the first summand is nonnegative.
  rw [mul_assoc 2]
  exact mul_add_div_le_two_mul_mul_add_div (by positivity) (by positivity) hlam
    (by rw [mul_left_comm]; gcongr)

/-- **De Giorgi's theorem with a right-hand side in divergence form up to a flat boundary.** Let
`n ≥ 1` be the dimension and let `q > 2` with `q > n`. There are `α ∈ (0, 1]` and `C > 0`,
depending only on `λ`, `Λ`, `n`, `q` and the normalization of the additive Haar measure `mu`, such
that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ` be the reflection in
the hyperplane `∂H` and let `U` be open with `ρ U ⊆ U`. Let `a` be measurable on `U ∩ H` and
uniformly elliptic with constants `λ, Λ` on the part of `U` in the closed half-space
`{x | c₀ ≤ ⟪x, ν⟫}`, and let `F ∈ L²(U ∩ H; ℝⁿ) ∩ L^q(U ∩ H; ℝⁿ)`. Let `u ∈ H¹(U)` vanish on
`U ∖ H` and let its restriction to `U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`, that is
`a(u, v) = -∫_{U ∩ H} ⟪F, ∇v⟫` for every `v ∈ H¹₀(U ∩ H)`. If the closed `R`-thickening of a set
`K` lies in `U`, then the precise representative of the odd reflection `w = u - u ∘ ρ`, which
agrees with `u` on `U ∩ H`, is Hölder continuous on `K` with exponent `α` and constant

`C R^(-α) (R^(-n/2) ‖w‖_{L²(U)} + R^(1 - n/q) ‖F‖_{L^q(U ∩ H)} / λ)`.

The set `K` may meet the hyperplane, so this is an estimate up to the flat part of the boundary
of `U ∩ H`, on which `u` vanishes. -/
theorem exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp_divergence
    [Nonempty ι] {lam Lam : ℝ} {q : ℝ≥0} (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ ι)}
      {ν : EuclideanSpace ℝ ι} {c₀ : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {u : W1p mu U 2}
      {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      UniformlyEllipticOn {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam →
      AEStronglyMeasurable a (mu.restrict (U ⊓ H)) →
      MemLp F 2 (mu.restrict (U ⊓ H)) → MemLp F q (mu.restrict (U ⊓ H)) →
      (∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 mu (U ⊓ H) 2,
        energyFormH1 a 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
          (v : W1p mu (U ⊓ H) 2) =
            -∫ x in U ⊓ H, ⟪F x, W1p.gradient (v : W1p mu (U ⊓ H) 2) x⟫_ℝ ∂mu) →
      0 < R → Metric.cthickening R K ⊆ (U : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ y in U, W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU
            u) y ^ 2 ∂mu) + R ^ (1 - (Fintype.card ι : ℝ) / q) *
              (eLpNorm F q (mu.restrict (U ⊓ H))).toReal / lam)).toNNReal α
          (preciseRepresentative mu
            (W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u))) K := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_memLp_divergence (mu := mu) (lam := lam)
      (Lam := Lam) hq hqn
  refine ⟨α, 2 * C, hα, hα1, by positivity,
    fun {U H ν c₀ a F u K R} hν hH hU ha ham hF2 hFq hu0 hu hR hRK => ?_⟩
  have ha' : UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) (reflectPrincipal ν c₀ a) lam
      Lam := ha.reflectPrincipal hν hU
  have hlam := ha'.pos
  -- The odd reflection `G` of `F` is the right-hand side of the reflected equation.
  let G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x =>
    (H : Set (EuclideanSpace ℝ ι)).indicator F x -
      (ℝ ∙ ν)ᗮ.reflection ((H : Set (EuclideanSpace ℝ ι)).indicator F (hyperplaneReflection ν c₀ x))
  have hG : MemLp G q (mu.restrict U) :=
    memLp_indicator_sub_linearIsometry_indicator_comp_hyperplaneReflection
      (ℝ ∙ ν)ᗮ.reflection.toLinearIsometry H.isOpen.measurableSet U.isOpen.measurableSet hU hFq
  have hGF : (eLpNorm G q (mu.restrict U)).toReal ≤
      2 * (eLpNorm F q (mu.restrict (U ⊓ H))).toReal :=
    toReal_eLpNorm_indicator_sub_reflection_indicator_comp_le hU (one_lt_two.trans hq).le hFq
  have hw : ∀ v : W1p0 mu U 2, energyFormH1 (reflectPrincipal ν c₀ a) 0 0
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) (v : W1p mu U 2) =
        -∫ x in U, ⟪G x, W1p.gradient (v : W1p mu U 2) x⟫_ℝ ∂mu := fun v => by
    have h := energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub hν hH
      hU (memLp_energyIntegrand_reflectPrincipal (b := 0) (c := 0) (beta := 0) (gamma := 0) hν hH
        hU ha ham aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
        (fun _ _ => by simp)) hu0 (f := 0) (MemLp.zero' (p := 2)) hF2
      (fun v => by simpa using hu v) v
    simpa [reflectDrift_zero, reflectDensity_zero] using h
  refine (hhol ha' (aestronglyMeasurable_reflectPrincipal hν hH hU ham) hG hw hR hRK).mono_const
    (Real.toNNReal_le_toNNReal ?_)
  -- The constant: `‖G‖_{L^q(U)} ≤ 2 ‖F‖_{L^q(U ∩ H)}` and the first summand is nonnegative.
  rw [mul_assoc 2]
  exact mul_add_div_le_two_mul_mul_add_div (by positivity) (by positivity) hlam
    (by rw [mul_left_comm]; gcongr)

/-- **De Giorgi's theorem with a right-hand side `f + ∂ᵢFⁱ` up to a flat boundary.** Let `n ≥ 1`
be the dimension, let `r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There are
`α ∈ (0, 1]` and `C > 0`, depending only on `λ`, `Λ`, `n`, `r`, `q` and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H` and let `U` be open with `ρ U ⊆ U`. Let
`a` be measurable on `U ∩ H` and uniformly elliptic with constants `λ, Λ` on the part of `U` in
the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`, let `f ∈ L²(U ∩ H) ∩ Lʳ(U ∩ H)` and let
`F ∈ L²(U ∩ H; ℝⁿ) ∩ L^q(U ∩ H; ℝⁿ)`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction
to `U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, that is
`a(u, v) = ∫_{U ∩ H} f v - ∫_{U ∩ H} ⟪F, ∇v⟫` for every `v ∈ H¹₀(U ∩ H)`. If the closed
`R`-thickening of a set `K` lies in `U`, then the precise representative of the odd reflection
`w = u - u ∘ ρ`, which agrees with `u` on `U ∩ H`, is Hölder continuous on `K` with exponent `α`
and constant

`C R^(-α) (R^(-n/2) ‖w‖_{L²(U)} + (R^(2 - n/r) ‖f‖_r + R^(1 - n/q) ‖F‖_q) / λ)`,

where `‖f‖_r` and `‖F‖_q` are the norms in `Lʳ(U ∩ H)` and `L^q(U ∩ H)`. Each datum enters with
its own Morrey gain. This is the form in which a nonzero boundary value `g` enters: if `u` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `u = g` on the flat boundary, then `u - g` vanishes there and solves the
equation with the datum `f + ∂ᵢ(aⁱʲ ∂ⱼg)`. -/
theorem
    exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp_add_divergence
    [Nonempty ι] {lam Lam : ℝ} {r q : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    (hq : 2 < (q : ℝ)) (hqn : (Fintype.card ι : ℝ) < q) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ α ≤ 1 ∧ 0 < C ∧ ∀ {U H : Opens (EuclideanSpace ℝ ι)}
      {ν : EuclideanSpace ℝ ι} {c₀ : ℝ} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
      {u : W1p mu U 2} {K : Set (EuclideanSpace ℝ ι)} {R : ℝ},
      ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ∀ hU : MapsTo (hyperplaneReflection ν c₀) U U,
      UniformlyEllipticOn {x | x ∈ U ∧ c₀ ≤ ⟪x, ν⟫_ℝ} a lam Lam →
      AEStronglyMeasurable a (mu.restrict (U ⊓ H)) →
      MemLp f 2 (mu.restrict (U ⊓ H)) → MemLp f r (mu.restrict (U ⊓ H)) →
      MemLp F 2 (mu.restrict (U ⊓ H)) → MemLp F q (mu.restrict (U ⊓ H)) →
      (∀ᵐ x ∂mu.restrict U, x ∉ H → W1p.value u x = 0) →
      (∀ v : W1p0 mu (U ⊓ H) 2,
        energyFormH1 a 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
          (v : W1p mu (U ⊓ H) 2) =
            ∫ x in U ⊓ H, f x * W1p.value (v : W1p mu (U ⊓ H) 2) x ∂mu -
              ∫ x in U ⊓ H, ⟪F x, W1p.gradient (v : W1p mu (U ⊓ H) 2) x⟫_ℝ ∂mu) →
      0 < R → Metric.cthickening R K ⊆ (U : Set (EuclideanSpace ℝ ι)) →
        HolderOnWith (C * R ^ (-(α : ℝ)) * (R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ y in U, W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU
            u) y ^ 2 ∂mu) + (R ^ (2 - (Fintype.card ι : ℝ) / r) *
              (eLpNorm f r (mu.restrict (U ⊓ H))).toReal + R ^ (1 - (Fintype.card ι : ℝ) / q) *
                (eLpNorm F q (mu.restrict (U ⊓ H))).toReal) / lam)).toNNReal α
          (preciseRepresentative mu
            (W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u))) K := by
  obtain ⟨α, C, hα, hα1, hC, hhol⟩ :=
    exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence (mu := mu) (lam := lam)
      (Lam := Lam) hr hrn hq hqn
  refine ⟨α, 2 * C, hα, hα1, by positivity,
    fun {U H ν c₀ a f F u K R} hν hH hU ha ham hf2 hfr hF2 hFq hu0 hu hR hRK => ?_⟩
  have ha' : UniformlyEllipticOn (U : Set (EuclideanSpace ℝ ι)) (reflectPrincipal ν c₀ a) lam
      Lam := ha.reflectPrincipal hν hU
  have hlam := ha'.pos
  -- The odd reflections `g` of `f` and `G` of `F` are the data of the reflected equation.
  let g : EuclideanSpace ℝ ι → ℝ := fun x => (H : Set (EuclideanSpace ℝ ι)).indicator f x -
    (H : Set (EuclideanSpace ℝ ι)).indicator f (hyperplaneReflection ν c₀ x)
  let G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x =>
    (H : Set (EuclideanSpace ℝ ι)).indicator F x -
      (ℝ ∙ ν)ᗮ.reflection ((H : Set (EuclideanSpace ℝ ι)).indicator F (hyperplaneReflection ν c₀ x))
  have hg : MemLp g r (mu.restrict U) :=
    memLp_indicator_sub_indicator_comp_hyperplaneReflection H.isOpen.measurableSet
      U.isOpen.measurableSet hU hfr
  have hgf : (eLpNorm g r (mu.restrict U)).toReal ≤
      2 * (eLpNorm f r (mu.restrict (U ⊓ H))).toReal :=
    toReal_eLpNorm_indicator_sub_indicator_comp_le hU (by exact_mod_cast hr.le) hfr
  have hG : MemLp G q (mu.restrict U) :=
    memLp_indicator_sub_linearIsometry_indicator_comp_hyperplaneReflection
      (ℝ ∙ ν)ᗮ.reflection.toLinearIsometry H.isOpen.measurableSet U.isOpen.measurableSet hU hFq
  have hGF : (eLpNorm G q (mu.restrict U)).toReal ≤
      2 * (eLpNorm F q (mu.restrict (U ⊓ H))).toReal :=
    toReal_eLpNorm_indicator_sub_reflection_indicator_comp_le hU (one_lt_two.trans hq).le hFq
  have hw : ∀ v : W1p0 mu U 2, energyFormH1 (reflectPrincipal ν c₀ a) 0 0
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) (v : W1p mu U 2) =
        ∫ x in U, g x * W1p.value (v : W1p mu U 2) x ∂mu -
          ∫ x in U, ⟪G x, W1p.gradient (v : W1p mu U 2) x⟫_ℝ ∂mu := fun v => by
    have h := energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub hν hH
      hU (memLp_energyIntegrand_reflectPrincipal (b := 0) (c := 0) (beta := 0) (gamma := 0) hν hH
        hU ha ham aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
        (fun _ _ => by simp)) hu0 hf2 hF2 hu v
    rwa [reflectDrift_zero, reflectDensity_zero] at h
  refine (hhol ha' (aestronglyMeasurable_reflectPrincipal hν hH hU ham) hg hG hw hR hRK).mono_const
    (Real.toNNReal_le_toNNReal ?_)
  -- The constant: each reflected datum has at most twice the norm of the original one.
  rw [mul_assoc 2]
  refine mul_add_div_le_two_mul_mul_add_div (by positivity) (by positivity) hlam ?_
  rw [mul_add, mul_left_comm _ (R ^ (2 - (Fintype.card ι : ℝ) / r)),
    mul_left_comm _ (R ^ (1 - (Fintype.card ι : ℝ) / q))]
  gcongr

end PDE

end TauCeti
