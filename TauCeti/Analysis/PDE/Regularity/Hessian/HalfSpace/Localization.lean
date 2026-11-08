/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.HalfSpace.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import TauCeti.Analysis.Sobolev.W1p.Localization
import TauCeti.Analysis.Sobolev.Wkp.Extension
import TauCeti.MeasureTheory.Function.Lp.Trace
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The localized Calderón–Zygmund estimate near a flat boundary

Let `E` be a finite-dimensional real inner product space, `1 < p < ∞`, and let
`H = {x | a < x.fst}` be a half-space of `ℝ × E`. This file localizes the half-space `W^{2,p}`
estimate for coefficients of small oscillation (in namespace `TauCeti`,
`exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`)
to a strong solution on a domain `Ω` near a flat part of its boundary (in namespace `TauCeti`,
`exists_lpNorm_smul_iteratedGradient_le_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace`).

There are `C` and `δ > 0`, depending only on `E` and `p`, with the following property. Let `U` be
open with `Ω ∩ U = H ∩ U`, so that inside `U` the domain is the half-space and its boundary is the
hyperplane `∂H`. Let `A₀` be an operator with `λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`, and let `ζ` be
smooth with compact support in `U`, `‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`. Let `A` be a measurable field of
endomorphisms with `‖A x - A₀‖ ≤ ε ≤ δ λ` and `‖A x‖ ≤ Λ` almost everywhere on the support of `ζ`.
Then every `u ∈ W^{2,p}(Ω)` that vanishes on the flat boundary portion in the sense that
`ζ u ∈ W^{1,p}_0(Ω)`, and solves `tr (A ∘ D²u) = f ∈ Lᵖ(Ω)` almost everywhere on `Ω`, satisfies

`‖ζ D²u‖_{Lᵖ(Ω)} ≤ (C / λ) ‖ζ f‖_{Lᵖ(Ω)} + (C N Λ / λ + 1) (2 M₁ ‖∇u‖_{Lᵖ(Ω)} + M₂ ‖u‖_{Lᵖ(Ω)})`,

where `N` is the dimension of `ℝ × E`. The support of `ζ` may meet the boundary hyperplane:
this is the boundary counterpart of the interior localized estimate
`TauCeti.PDE.exists_lpNorm_smul_iteratedGradient_le_of_sum_mul_inner_eq_of_abs_sub_le`. Nothing is
assumed about `∂Ω` outside `U`. When the coefficients are continuous up to the flat boundary, `A₀`
is their value at a boundary point and `ζ` a cutoff near it; after flattening the boundary of a
`C^{1,1}` domain in a chart, this is the local estimate near the boundary behind the global
`W^{2,p}` estimate for the Dirichlet problem.

## The argument

Multiplying by `ζ` preserves `W^{2,p}(Ω)`
(`TauCeti.Wkp.exists_value_ae_eq_mul_of_hasCompactSupport`), and by the Leibniz rule
(`TauCeti.Wkp.iteratedGradient_one_ae_eq_of_value_ae_eq_mul`) `D²(ζ u) = ζ D²u + T` with
`T = ∇ζ ⊗ ∇u + ∇u ⊗ ∇ζ + u D²ζ`, so

`tr (A ∘ D²(ζ u)) = ζ f + tr (A ∘ T)`,

where `|tr (A ∘ T)| ≤ N Λ ‖T‖` on the support `K` of `ζ` (`TauCeti.exists_lp_traceCLM_comp_le`)
and `‖T‖ ≤ 2 M₁ ‖∇u‖ + M₂ |u|` pointwise.

Since `ζ u` vanishes off `K` and `H ∩ K ⊆ Ω`, its extension by zero lies in `W^{2,p}(H)`
(`TauCeti.Wkp.exists_value_ae_eq_indicator_of_isClosed`), with weak Hessian the extension by zero
of `D²(ζ u)` (`TauCeti.Wkp.iteratedGradient_ae_eq_indicator_of_isClosed`). Its first-order part
lies in `W^{1,p}_0(H)` (`TauCeti.W1p.mem_w1p0Submodule_of_inter_eq_of_isCompact`, since `Ω` and
`H` agree on `U ⊇ K`), and it vanishes off `K`, where the coefficients are close to `A₀`.
The half-space estimate therefore bounds `‖D²(ζ u)‖` by `(C / λ)` times the `Lᵖ` norm of
`ζ f + tr (A ∘ T)`, and `ζ D²u = D²(ζ u) - T`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 9.12 and the proof of Theorem 9.13 (the estimate near a flat boundary portion).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace InnerProductSpace
open scoped ENNReal NNReal Gradient ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The half-space estimate near a flat boundary portion.** Let `Ω ∩ U = H ∩ U` for the half-space
`H`, and let `w ∈ W^{2,p}(Ω)`, with first-order part in `W^{1,p}_0(Ω)`, vanish off a compact set
`K ⊆ U` and solve `tr (A ∘ D²w) = g` on `Ω`, where `‖A x - A₀‖ ≤ ε ≤ δ λ` on `K`. Then
`‖D²w‖_{Lᵖ(Ω)} ≤ (C / λ) ‖g‖_{Lᵖ(Ω)}`, with the constants of the half-space estimate: extended by
zero, `w` is a function on `H` to which that estimate applies. -/
private theorem exists_norm_iteratedGradient_le_of_inter_eq_normalHalfSpace_inter
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) {A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
      {lam : ℝ}, 0 < lam → (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) →
      ∀ {Omega U : Opens (WithLp 2 (ℝ × E))},
        (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U →
      ∀ {K : Set (WithLp 2 (ℝ × E))}, IsCompact K → K ⊆ U →
      ∀ {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {ε : ℝ}, ε ≤ δ * lam →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), x ∈ K → ‖A x - A₀‖ ≤ ε) →
      ∀ (w : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (g : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        Wkp.firstOrder 1 w ∈ w1p0Submodule volume Omega p →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), x ∉ K → Wkp.value 2 w x = 0) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 w x) = g x) →
        ‖Wkp.iteratedGradient 1 w‖ ≤ C / lam * ‖g‖ := by
  obtain ⟨C, δ, hδ, hCZ⟩ :=
    exists_norm_iteratedGradient_le_mul_norm_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
      (E := E) hp hp_top
  refine ⟨C, δ, hδ, fun a {A₀ lam} hlam hA₀ {Omega U} hΩU {K} hK hKU {A ε} hε hA w g hw0 hwK hwg =>
    ?_⟩
  have hΩm : MeasurableSet (Omega : Set (WithLp 2 (ℝ × E))) := Omega.isOpen.measurableSet
  have hHm : MeasurableSet (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) :=
    (normalHalfSpace (E := E) a).isOpen.measurableSet
  -- Inside `U`, which contains `K`, the domain `Ω` is the half-space `H`.
  have hHK : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ K ⊆ Omega :=
    fun x hx => ((hΩU.symm ▸ ⟨hx.1, hKU hx.2⟩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E))) ∩ U)).1
  have hΩK : (Omega : Set (WithLp 2 (ℝ × E))) ∩ K ⊆ normalHalfSpace (E := E) a :=
    fun x hx => ((hΩU ▸ ⟨hx.1, hKU hx.2⟩ :
      x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U)).1
  -- The extension `W` of `w` by zero to `H`, with weak Hessian the extension of `D²w`.
  obtain ⟨W, hW⟩ := Wkp.exists_value_ae_eq_indicator_of_isClosed (V := normalHalfSpace a)
    hK.isClosed hHK 2 w hwK
  have hWD := Wkp.iteratedGradient_ae_eq_indicator_of_isClosed hK.isClosed hHK 1 hwK hW
  have hW0 : Wkp.firstOrder 1 W ∈ w1p0Submodule volume (normalHalfSpace a) p := by
    refine W1p.mem_w1p0Submodule_of_inter_eq_of_isCompact hp_top hΩU hK hKU hw0 ?_ ?_
    · simpa only [Wkp.value_firstOrder] using hwK
    · simpa only [Wkp.value_firstOrder] using hW
  have hWK := Wkp.value_ae_eq_zero_of_value_ae_eq_indicator hwK hW
  -- The equation for `W` on `H`, with the extension by zero of `g` on the right.
  have hG : MemLp ((Omega : Set (WithLp 2 (ℝ × E))).indicator g) p
      (volume.restrict (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))) :=
    ((memLp_indicator_iff_restrict hΩm.nullMeasurableSet).2 (Lp.memLp g)).restrict _
  have hWg : ∀ᵐ x ∂volume.restrict (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 W x) = hG.toLp _ x := by
    filter_upwards [hWD, hG.coeFn_toLp, ae_restrict_of_ae ((ae_restrict_iff' hΩm).1 hwg)]
      with x h1 h2 h3
    rw [h1, h2]
    by_cases hxΩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
    · rw [indicator_of_mem hxΩ, indicator_of_mem hxΩ, h3 hxΩ]
    · rw [indicator_of_notMem hxΩ, indicator_of_notMem hxΩ, ContinuousLinearMap.comp_zero,
        map_zero]
  have hAH : ∀ᵐ x ∂volume.restrict (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))),
      x ∈ K → ‖A x - A₀‖ ≤ ε := by
    filter_upwards [ae_restrict_mem hHm, ae_restrict_of_ae ((ae_restrict_iff' hΩm).1 hA)]
      with x hxH hx hxK using hx (hHK ⟨hxH, hxK⟩) hxK
  -- The half-space estimate for `W`, read back on `Ω`.
  have hkey := hCZ a hlam hA₀ hK.isClosed hε hAH W _ hW0 hWK hWg
  -- `D²w` vanishes on `Ω \ K ⊇ Ω \ H`, so its extension by zero has the same norm on `H`.
  have hwD0 := Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen 1 w
    hK.isClosed.isOpen_compl hwK
  have hD : ‖Wkp.iteratedGradient 1 w‖ = ‖Wkp.iteratedGradient 1 W‖ := by
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hWD,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hΩm.nullMeasurableSet,
      ← eLpNorm_indicator_eq_eLpNorm_restrict hHm.nullMeasurableSet]
    refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
    filter_upwards [(ae_restrict_iff' hΩm).1 hwD0] with x hx
    by_cases hxH : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
    · rw [indicator_of_mem hxH]
    · rw [indicator_of_notMem hxH]
      by_cases hxΩ : x ∈ (Omega : Set (WithLp 2 (ℝ × E)))
      · rw [indicator_of_mem hxΩ, hx hxΩ fun hxK => hxH (hΩK ⟨hxΩ, hxK⟩)]
      · exact indicator_of_notMem hxΩ _
  have hGg : ‖hG.toLp _‖ ≤ ‖g‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hΩm.nullMeasurableSet]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  rw [hD]
  exact hkey.trans (by gcongr)

/-- **The localized Calderón–Zygmund estimate near a flat boundary.** Let `1 < p < ∞`. There are
constants `C` and `δ > 0`, depending only on `E` and `p`, with the following property. Let
`H = {x | a < x.fst}` be a half-space of `ℝ × E`, and let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`.
Let `A₀` be an operator on `ℝ × E` with `λ ‖ξ‖² ≤ ⟪A₀ ξ, ξ⟫` and `0 < λ`, and let `ζ` be smooth with
compact support in `U`, `‖∇ζ‖ ≤ M₁` and `‖D²ζ‖ ≤ M₂`. Let `A` be a field of endomorphisms of
`ℝ × E`, measurable on `Ω`, with `‖A x - A₀‖ ≤ ε` and `‖A x‖ ≤ Λ` for almost every `x ∈ Ω` in the
support of `ζ`, where `ε ≤ δ λ` and `0 ≤ Λ`. Then every `u ∈ W^{2,p}(Ω)` with `ζ u ∈ W^{1,p}_0(Ω)`
which solves `tr (A ∘ D²u) = f` almost everywhere on `Ω`, with `f ∈ Lᵖ(Ω)`, satisfies

`‖ζ D²u‖_{Lᵖ(Ω)} ≤ (C / λ) ‖ζ f‖_{Lᵖ(Ω)} + (C N Λ / λ + 1) (2 M₁ ‖∇u‖_{Lᵖ(Ω)} + M₂ ‖u‖_{Lᵖ(Ω)})`,

where `N` is the dimension of `ℝ × E`, `D²u` is the weak Hessian
`TauCeti.Wkp.iteratedGradient 1 u` and `∇u` is the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`. The support of `ζ` may meet the
boundary hyperplane, and nothing is assumed about `∂Ω` outside `U`. -/
theorem exists_lpNorm_smul_iteratedGradient_le_of_traceCLM_comp_eq_of_norm_sub_le_of_normalHalfSpace
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ (a : ℝ) {A₀ : WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)}
      {lam : ℝ}, 0 < lam → (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪A₀ ξ, ξ⟫_ℝ) →
      ∀ {Omega U : Opens (WithLp 2 (ℝ × E))},
        (Omega : Set (WithLp 2 (ℝ × E))) ∩ U =
          (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ∩ U →
      ∀ {zeta : WithLp 2 (ℝ × E) → ℝ} {M₁ M₂ : ℝ}, ContDiff ℝ ∞ zeta → HasCompactSupport zeta →
        tsupport zeta ⊆ U → (∀ x, ‖∇ zeta x‖ ≤ M₁) → (∀ x, ‖fderiv ℝ (∇ zeta) x‖ ≤ M₂) →
      ∀ {A : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E) →L[ℝ] WithLp 2 (ℝ × E)} {ε Λ : ℝ},
        AEStronglyMeasurable A (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) →
        ε ≤ δ * lam →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), x ∈ tsupport zeta →
          ‖A x - A₀‖ ≤ ε) → 0 ≤ Λ →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))), x ∈ tsupport zeta →
          ‖A x‖ ≤ Λ) →
      ∀ (u : Wkp (volume : Measure (WithLp 2 (ℝ × E))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (WithLp 2 (ℝ × E))).restrict Omega)),
        (∃ v : W1p0 (volume : Measure (WithLp 2 (ℝ × E))) Omega p,
          W1p.value (v : W1p volume Omega p) =ᵐ[volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))]
            fun x => zeta x * Wkp.value 2 u x) →
        (∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
          traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 u x) = f x) →
        lpNorm (fun x => zeta x • Wkp.iteratedGradient 1 u x) p
            (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) ≤
          C / lam * lpNorm (fun x => zeta x * f x) p
              (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))) +
            (C / lam * Module.finrank ℝ (WithLp 2 (ℝ × E)) * Λ + 1) *
              (2 * M₁ * ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u)‖ + M₂ * ‖Wkp.value 2 u‖) := by
  obtain ⟨C, δ, hδ, hCZ⟩ := exists_norm_iteratedGradient_le_of_inter_eq_normalHalfSpace_inter
    (E := E) hp hp_top
  refine ⟨C, δ, hδ, fun a {A₀ lam} hlam hA₀ {Omega U} hΩU {zeta M₁ M₂} hζ hcpt hζU hM₁ hM₂
    {A ε Λ} hA_meas hε hA hΛ hAΛ u f hu0 hf => ?_⟩
  generalize hN : (Module.finrank ℝ (WithLp 2 (ℝ × E)) : ℝ) = N
  have hN0 : 0 ≤ N := hN ▸ Nat.cast_nonneg _
  -- The product `w = ζ u ∈ W^{2,p}(Ω)`, with weak Hessian `ζ D²u + T`.
  obtain ⟨w, hwv⟩ := Wkp.exists_value_ae_eq_mul_of_hasCompactSupport 2 hζ hcpt u
  obtain ⟨T, hD, hTK, hTnorm, hζD⟩ :=
    Wkp.exists_iteratedGradient_one_ae_eq_smul_add_of_value_ae_eq_mul hζ hcpt hM₁ hM₂ hwv
  -- The equation `tr (A ∘ D²(ζ u)) = ζ f + tr (A ∘ T)` on `Ω`.
  obtain ⟨g, hg, hgnorm⟩ := exists_lp_traceCLM_comp_le hA_meas hAΛ T hTK
  have hζf : MemLp (fun x => zeta x * f x) p (volume.restrict Omega) :=
    (hζ.continuous.memLp_top_of_hasCompactSupport hcpt _).smul (Lp.memLp f)
  obtain ⟨FL, hFL⟩ : ∃ FL : Lp ℝ p (volume.restrict (Omega : Set (WithLp 2 (ℝ × E)))),
      FL = hζf.toLp _ + g := ⟨_, rfl⟩
  have hFLnorm : ‖FL‖ ≤ lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
      + N * Λ * ‖T‖ := by
    rw [hFL, ← hN]
    exact (norm_add_le _ _).trans (add_le_add (Lp.norm_toLp _ _).le hgnorm)
  have hweq : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      traceCLM ℝ (WithLp 2 (ℝ × E)) (A x ∘L Wkp.iteratedGradient 1 w x) = FL x := by
    filter_upwards [hf, hD, hFL ▸ Lp.coeFn_add (hζf.toLp _) g, hζf.coeFn_toLp, hg]
      with x hxf hDx h₃ h₄ h₅
    rw [h₃, Pi.add_apply, h₄, h₅, hDx, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.comp_smul, map_add, map_smul, smul_eq_mul, hxf]
  have hwK : ∀ᵐ x ∂volume.restrict (Omega : Set (WithLp 2 (ℝ × E))),
      x ∉ tsupport zeta → Wkp.value 2 w x = 0 := by
    filter_upwards [hwv] with x hx hxs
    rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul]
  -- The first-order part of `ζ u` is the zero-boundary function `v`.
  have hw0 : Wkp.firstOrder 1 w ∈ w1p0Submodule volume Omega p := by
    obtain ⟨v, hv⟩ := hu0
    have hfo : Wkp.firstOrder 1 w = (v : W1p volume Omega p) := by
      refine W1p.ext_value (Lp.ext ?_)
      rw [Wkp.value_firstOrder]
      exact hwv.trans hv.symm
    exact hfo ▸ v.2
  -- The half-space estimate for `ζ u`, and `ζ D²u = D²(ζ u) - T`.
  have hkey := hCZ a hlam hA₀ hΩU hcpt.isCompact hζU hε hA w FL hw0 hwK hweq
  have hCl : 0 ≤ (C : ℝ) / lam := by positivity
  rw [hζD]
  calc ‖Wkp.iteratedGradient 1 w - T‖
      ≤ ‖Wkp.iteratedGradient 1 w‖ + ‖T‖ := norm_sub_le _ _
    _ ≤ C / lam * (lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
          + N * Λ * ‖T‖) + ‖T‖ := by
        gcongr
        exact hkey.trans (by gcongr)
    _ = C / lam * lpNorm (fun x => zeta x * f x) p (volume.restrict Omega)
          + (C / lam * N * Λ + 1) * ‖T‖ := by ring
    _ ≤ _ := by gcongr

end TauCeti
