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
for `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with a right-hand side `f ∈ L² ∩ Lʳ(U ∩ H)`, `r > 1` and `r > n/2`,
with `α` and `C` depending also on `r`
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp`),
for `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ` with a divergence datum `F ∈ L² ∩ L^q(U ∩ H; ℝⁿ)`, `q > 2` and `q > n`
(`exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp_divergence`),
and for the datum `f + ∂ᵢFⁱ`
(`exists_holderOnWith_preciseRepresentative_sub_compHyperplaneReflectionL_of_memLp_add_divergence`).
These are the boundary counterparts of the interior theorems in
`TauCeti.Analysis.PDE.Regularity.Inhomogeneous`.

More precisely, for the homogeneous equation the precise representative of the odd reflection
`w = u - u ∘ ρ` is `α`-Hölder on every set `K` whose closed `R`-thickening lies in `U`, with
constant `C R^(-α - n/2) ‖w‖_{L²(U)}`, and `w` agrees with `u` on `U ∩ H`
(`TauCeti.W1p.value_sub_compHyperplaneReflectionL_ae`). With a right-hand side `f` the constant is
`C R^(-α) (R^(-n/2) ‖w‖_{L²(U)} + R^(2 - n/r) ‖f‖_{Lʳ(U ∩ H)} / λ)`, and a divergence datum
contributes `R^(1 - n/q) ‖F‖_{L^q(U ∩ H)} / λ` in the same way. The set `K` may meet the
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

A divergence datum `∂ᵢFⁱ` is reflected oddly as a vector field: `w` solves the reflected equation
on `U` with datum `∂ᵢGⁱ`, `G(x) = 1_H F x - R (1_H F (ρ x))`, where `R` is the linear part of `ρ`
(`energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral`).
Since `R` is an isometry, `‖G‖_{L^q(U)} ≤ 2 ‖F‖_{L^q(U ∩ H)}`, and De Giorgi's interior theorem
with a divergence datum
(`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp_divergence`) applies, or the one
with both data (`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_memLp_add_divergence`).

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

omit [DecidableEq ι] in
/-- The real-valued bound on an odd reflection: for `f ∈ Lᵖ(U ∩ H)` and a continuous
norm-preserving `L`, `‖1_H f - L (1_H f ∘ ρ)‖_{Lᵖ(U)} ≤ 2 ‖f‖_{Lᵖ(U ∩ H)}`. -/
private theorem toReal_eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le
    {E : Type*} [NormedAddCommGroup E] (L : E → E) (hLc : Continuous L) (hL : ∀ y, ‖L y‖ = ‖y‖)
    {U H : Opens (EuclideanSpace ℝ ι)} {ν : EuclideanSpace ℝ ι} {c₀ : ℝ}
    (hU : MapsTo (hyperplaneReflection ν c₀) U U) {f : EuclideanSpace ℝ ι → E} {p : ENNReal}
    (hp : 1 ≤ p) (hf : MemLp f p (mu.restrict (U ⊓ H))) :
    (eLpNorm (fun x => (H : Set (EuclideanSpace ℝ ι)).indicator f x -
      L ((H : Set (EuclideanSpace ℝ ι)).indicator f (hyperplaneReflection ν c₀ x))) p
        (mu.restrict U)).toReal ≤ 2 * (eLpNorm f p (mu.restrict (U ⊓ H))).toReal :=
  (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hf.eLpNorm_ne_top)
    (eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le L hLc hL hp
      H.isOpen.measurableSet U.isOpen.measurableSet hU)).trans_eq (by simp)

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
    memLp_indicator_sub_indicator_comp_hyperplaneReflection id continuous_id (fun _ => rfl)
      H.isOpen.measurableSet U.isOpen.measurableSet hU hfr
  have hgf : (eLpNorm g r (mu.restrict U)).toReal ≤
      2 * (eLpNorm f r (mu.restrict (U ⊓ H))).toReal :=
    toReal_eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le id continuous_id
      (fun _ => rfl) hU (by exact_mod_cast hr.le) hfr
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

/-- The bookkeeping of the constants: if reflecting the data at most doubles the datum term
`X / λ ≤ 2 (Y / λ)`, then the constant `C S (A + X / λ)` of the reflected equation is at most
`2 C S (A + Y / λ)`. -/
private theorem mul_add_div_le_two_mul_mul_add_div {C S A X Y l : ℝ} (hCS : 0 ≤ C * S)
    (hA : 0 ≤ A) (hl : 0 < l) (hXY : X ≤ 2 * Y) :
    C * S * (A + X / l) ≤ 2 * C * S * (A + Y / l) := by
  have h := mul_le_mul_of_nonneg_left hXY (div_nonneg hCS hl.le)
  simp only [div_eq_mul_inv] at h ⊢
  linarith [mul_nonneg hCS hA]

/-- **De Giorgi's theorem with a divergence datum up to a flat boundary.** Let `n ≥ 1` be the
dimension and let `q > 2` with `q > n`. There are `α ∈ (0, 1]` and `C > 0`, depending only on
`λ`, `Λ`, `n`, `q` and the normalization of the additive Haar measure `mu`, such that the following
holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ` be the reflection in the hyperplane `∂H`
and let `U` be open with `ρ U ⊆ U`. Let `a` be measurable on `U ∩ H` and uniformly elliptic with
constants `λ, Λ` on the part of `U` in the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}`, and let
`F ∈ L²(U ∩ H; ℝⁿ) ∩ L^q(U ∩ H; ℝⁿ)`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to
`U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = ∂ᵢFⁱ`, that is `a(u, v) = -∫_{U ∩ H} ⟪F, ∇v⟫` for
every `v ∈ H¹₀(U ∩ H)`. If the closed `R`-thickening of a set `K` lies in `U`, then the precise
representative of the odd reflection `w = u - u ∘ ρ`, which agrees with `u` on `U ∩ H`, is Hölder
continuous on `K` with exponent `α` and constant

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
  -- The odd reflection `G` of the vector field `F` is the divergence datum of the reflected
  -- equation.
  set G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x =>
    (H : Set (EuclideanSpace ℝ ι)).indicator F x - (ℝ ∙ ν)ᗮ.reflection
      ((H : Set (EuclideanSpace ℝ ι)).indicator F (hyperplaneReflection ν c₀ x))
  have hG : MemLp G q (mu.restrict U) :=
    memLp_indicator_sub_indicator_comp_hyperplaneReflection (ℝ ∙ ν)ᗮ.reflection
      (ℝ ∙ ν)ᗮ.reflection.continuous (ℝ ∙ ν)ᗮ.reflection.norm_map H.isOpen.measurableSet
      U.isOpen.measurableSet hU hFq
  have hGF : (eLpNorm G q (mu.restrict U)).toReal ≤
      2 * (eLpNorm F q (mu.restrict (U ⊓ H))).toReal :=
    toReal_eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le (ℝ ∙ ν)ᗮ.reflection
      (ℝ ∙ ν)ᗮ.reflection.continuous (ℝ ∙ ν)ᗮ.reflection.norm_map hU
      (by exact_mod_cast (by linarith : (1 : ℝ) ≤ q)) hFq
  have hw : ∀ v : W1p0 mu U 2, energyFormH1 (reflectPrincipal ν c₀ a) 0 0
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) (v : W1p mu U 2) =
        -∫ x in U, ⟪G x, W1p.gradient (v : W1p mu U 2) x⟫_ℝ ∂mu := fun v => by
    have h :=
      energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral
      hν hH hU (memLp_energyIntegrand_reflectPrincipal (b := 0) (c := 0) (beta := 0) (gamma := 0)
        hν hH hU ha ham aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
        (fun _ _ => by simp)) hu0 (f := 0) MemLp.zero hF2
        (fun v => by simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub]; exact hu v) v
    simp only [reflectDrift_zero, reflectDensity_zero, Set.indicator_zero', Pi.zero_apply,
      sub_self, zero_mul, integral_zero, zero_sub] at h
    exact h
  refine (hhol ha' (aestronglyMeasurable_reflectPrincipal hν hH hU ham) hG hw hR hRK).mono_const
    (Real.toNNReal_le_toNNReal ?_)
  -- The constant: `‖G‖_{L^q(U)} ≤ 2 ‖F‖_{L^q(U ∩ H)}`.
  refine mul_add_div_le_two_mul_mul_add_div (by positivity) (by positivity) ha'.pos ?_
  linarith [mul_le_mul_of_nonneg_left hGF
    (by positivity : 0 ≤ R ^ (1 - (Fintype.card ι : ℝ) / q))]

/-- **De Giorgi's theorem with a datum `f + ∂ᵢFⁱ` up to a flat boundary.** Let `n ≥ 1` be the
dimension, let `r > 1` with `r > n/2`, and let `q > 2` with `q > n`. There are `α ∈ (0, 1]` and
`C > 0`, depending only on `λ`, `Λ`, `n`, `r`, `q` and the normalization of the additive Haar
measure `mu`, such that the following holds. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `ρ` be
the reflection in the hyperplane `∂H` and let `U` be open with `ρ U ⊆ U`. Let `a` be measurable on
`U ∩ H` and uniformly elliptic with constants `λ, Λ` on the part of `U` in the closed half-space
`{x | c₀ ≤ ⟪x, ν⟫}`, let `f ∈ L²(U ∩ H) ∩ Lʳ(U ∩ H)` and let
`F ∈ L²(U ∩ H; ℝⁿ) ∩ L^q(U ∩ H; ℝⁿ)`. Let `u ∈ H¹(U)` vanish on `U ∖ H` and let its restriction to
`U ∩ H` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f + ∂ᵢFⁱ`, that is
`a(u, v) = ∫_{U ∩ H} f v - ∫_{U ∩ H} ⟪F, ∇v⟫` for every `v ∈ H¹₀(U ∩ H)`. If the closed
`R`-thickening of a set `K` lies in `U`, then the precise representative of the odd reflection
`w = u - u ∘ ρ`, which agrees with `u` on `U ∩ H`, is Hölder continuous on `K` with exponent `α`
and constant `C R^(-α) (R^(-n/2) ‖w‖_{L²(U)} + B / λ)`, where

`B = R^(2 - n/r) ‖f‖_{Lʳ(U ∩ H)} + R^(1 - n/q) ‖F‖_{L^q(U ∩ H)}`.

The set `K` may meet the hyperplane, so this is an estimate up to the flat part of the boundary
of `U ∩ H`, on which `u` vanishes. -/
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
  -- The odd reflections `g` of `f` and `G` of `F` are the data of the reflected equation.
  let g : EuclideanSpace ℝ ι → ℝ := fun x => (H : Set (EuclideanSpace ℝ ι)).indicator f x -
    (H : Set (EuclideanSpace ℝ ι)).indicator f (hyperplaneReflection ν c₀ x)
  let G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι := fun x =>
    (H : Set (EuclideanSpace ℝ ι)).indicator F x - (ℝ ∙ ν)ᗮ.reflection
      ((H : Set (EuclideanSpace ℝ ι)).indicator F (hyperplaneReflection ν c₀ x))
  have hg : MemLp g r (mu.restrict U) :=
    memLp_indicator_sub_indicator_comp_hyperplaneReflection id continuous_id (fun _ => rfl)
      H.isOpen.measurableSet U.isOpen.measurableSet hU hfr
  have hgf : (eLpNorm g r (mu.restrict U)).toReal ≤
      2 * (eLpNorm f r (mu.restrict (U ⊓ H))).toReal :=
    toReal_eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le id continuous_id
      (fun _ => rfl) hU (by exact_mod_cast hr.le) hfr
  have hG : MemLp G q (mu.restrict U) :=
    memLp_indicator_sub_indicator_comp_hyperplaneReflection (ℝ ∙ ν)ᗮ.reflection
      (ℝ ∙ ν)ᗮ.reflection.continuous (ℝ ∙ ν)ᗮ.reflection.norm_map H.isOpen.measurableSet
      U.isOpen.measurableSet hU hFq
  have hGF : (eLpNorm G q (mu.restrict U)).toReal ≤
      2 * (eLpNorm F q (mu.restrict (U ⊓ H))).toReal :=
    toReal_eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le (ℝ ∙ ν)ᗮ.reflection
      (ℝ ∙ ν)ᗮ.reflection.continuous (ℝ ∙ ν)ᗮ.reflection.norm_map hU
      (by exact_mod_cast (by linarith : (1 : ℝ) ≤ q)) hFq
  have hw : ∀ v : W1p0 mu U 2, energyFormH1 (reflectPrincipal ν c₀ a) 0 0
      (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u) (v : W1p mu U 2) =
        ∫ x in U, g x * W1p.value (v : W1p mu U 2) x ∂mu -
          ∫ x in U, ⟪G x, W1p.gradient (v : W1p mu U 2) x⟫_ℝ ∂mu := fun v => by
    have h :=
      energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral
      hν hH hU (memLp_energyIntegrand_reflectPrincipal (b := 0) (c := 0) (beta := 0) (gamma := 0)
        hν hH hU ha ham aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
        (fun _ _ => by simp)) hu0 hf2 hF2 hu v
    rwa [reflectDrift_zero, reflectDensity_zero] at h
  refine (hhol ha' (aestronglyMeasurable_reflectPrincipal hν hH hU ham) hg hG hw hR
    hRK).mono_const (Real.toNNReal_le_toNNReal ?_)
  -- The constant: each datum's reflection at most doubles its norm.
  refine mul_add_div_le_two_mul_mul_add_div (by positivity) (by positivity) ha'.pos ?_
  linarith [mul_le_mul_of_nonneg_left hgf
    (by positivity : 0 ≤ R ^ (2 - (Fintype.card ι : ℝ) / r)), mul_le_mul_of_nonneg_left hGF
    (by positivity : 0 ≤ R ^ (1 - (Fintype.card ι : ℝ) / q))]

end PDE

end TauCeti
