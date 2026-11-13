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
      2 * (eLpNorm f r (mu.restrict (U ⊓ H))).toReal := by
    rw [← ENNReal.toReal_ofNat, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hfr.eLpNorm_ne_top)
      (eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le
        (by exact_mod_cast hr.le) H.isOpen.measurableSet U.isOpen.measurableSet hU)
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
  set A := R ^ (-(Fintype.card ι : ℝ) / 2) *
    √(∫ y in U, W1p.value (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU
      u) y ^ 2 ∂mu)
  have hA : 0 ≤ A := by positivity
  have hB : R ^ (2 - (Fintype.card ι : ℝ) / r) * (eLpNorm g r (mu.restrict U)).toReal / lam ≤
      2 * (R ^ (2 - (Fintype.card ι : ℝ) / r) *
        (eLpNorm f r (mu.restrict (U ⊓ H))).toReal / lam) := by
    rw [mul_div_assoc', mul_left_comm]
    gcongr
  have hCR : 0 ≤ C * R ^ (-(α : ℝ)) := by positivity
  calc C * R ^ (-(α : ℝ)) * (A + R ^ (2 - (Fintype.card ι : ℝ) / r) *
        (eLpNorm g r (mu.restrict U)).toReal / lam)
      ≤ C * R ^ (-(α : ℝ)) * (2 * (A + R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict (U ⊓ H))).toReal / lam)) :=
        mul_le_mul_of_nonneg_left (by linarith) hCR
    _ = 2 * C * R ^ (-(α : ℝ)) * (A + R ^ (2 - (Fintype.card ι : ℝ) / r) *
          (eLpNorm f r (mu.restrict (U ⊓ H))).toReal / lam) := by ring

end PDE

end TauCeti
