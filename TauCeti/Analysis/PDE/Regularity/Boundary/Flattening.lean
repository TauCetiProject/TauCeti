/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
public import TauCeti.Analysis.PDE.Regularity.Boundary.Flat
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# Local `H²` regularity near a boundary portion that can be flattened

Let `Ω` and `U` be open subsets of `ℝⁿ`, and let `Φ` be a `C²` change of variables from an open
set `U'` onto `U`, with inverse `Ψ`, that maps the flat piece `H ∩ U'` of a half-space `H`
onto `Ω ∩ U`. Thus `∂Ω ∩ U` is the image of a piece of the hyperplane `∂H`, as it is near every
boundary point of a domain of class `C²`. Let `a` be uniformly elliptic on `Ω ∩ U` and Lipschitz
there, up to the boundary, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

that vanishes on `∂Ω ∩ U`, in the sense that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly
supported in `U`. This file proves that `u` is `H²` up to that boundary portion: on `Ω ∩ V` for
every open `V` whose closure is compact and contained in `U`, the restriction of `u` is the
first-order part of an element of `W^{2,2}(Ω ∩ V)`
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_isChangeOfVariables`).
Nothing is assumed about the rest of `∂Ω`.

Together with interior `H²` regularity, covering the closure of a bounded `C²` domain by finitely
many interior balls and boundary charts of this kind gives global `H²` regularity of the weak
solution of the Dirichlet problem.

## The argument

The proof flattens the boundary (Evans, §6.3.2, proof of Theorem 4). The function `u ∘ Φ` is a weak
solution on `H ∩ U'` of an equation of the same form
(`TauCeti.PDE.energyFormH1_compL_eq_setIntegral`), whose principal coefficient
`a'(x) = |det DΦ(x)| DΦ(x)⁻¹ a(Φ x) DΦ(x)⁻ᵀ` is uniformly elliptic
(`TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipal`) and Lipschitz
(`TauCeti.PDE.exists_lipschitzOnWith_matrixBilinearForm_pullbackPrincipal`) once `U'` is shrunk to
an open neighbourhood of the compact set `Ψ(closure V)` with compact closure in `U'`, on which the
`C²` map `Φ` and its derivative are Lipschitz. The transformed equation has
bounded lower-order coefficients and right-hand side in `L²`. The function `u ∘ Φ` vanishes on
the flat boundary portion: for a smooth `ψ` supported in `U'`, take a smooth `χ` supported in `U`
and equal to one on `Φ(supp ψ)`; then `χ u ∈ H¹₀(Ω)`, its restriction lies in `H¹₀(Ω ∩ U)`,
precomposition with `Φ` keeps it in `H¹₀(H ∩ U')`, and multiplying by `ψ` gives `ψ (u ∘ Φ)`
(`TauCeti.W1p.exists_w1p0_value_ae_eq_mul_value_compL`). The
flat-boundary theorem (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_mapsTo`)
puts `u ∘ Φ` in `W^{2,2}` near the preimage of `V`, and precomposition with the `C²` map `Ψ`
(`TauCeti.Wkp.compL`) carries this back to `u` on `Ω ∩ V`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorem 4 and its proof.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.12.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega H U U' V : Opens (EuclideanSpace ℝ ι)}
  {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L L' c₀ c₁ : ℝ}

/-- The flattening argument when `Φ` and `DΦ` are Lipschitz on `U'`. -/
private theorem exists_lowerOrder_eq_restrictL_of_isChangeOfVariables_of_lipschitzOnWith
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c : EuclideanSpace ℝ ι → ℝ} {lam Lam : ℝ} {K KΦ KD : ℝ≥0} {ν : EuclideanSpace ℝ ι}
    (hν : ν ≠ 0) (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΦ : Wkp.IsChangeOfVariables 2 U' U Φ L c₀) (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L' c₁)
    (hΦL : LipschitzOnWith KΦ Φ U') (hDΦL : LipschitzOnWith KD (fderiv ℝ Φ) U')
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U)
    (hΦH : MapsTo Φ ((H : Set (EuclideanSpace ℝ ι)) ∩ U') Omega)
    (hΨΩ : MapsTo Ψ ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U) H)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x))
      ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVU : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ U) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 2,
      Wkp.lowerOrder 1 W = W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u := by
  -- Pull the problem back by `Φ` to `H ∩ U'`, check the hypotheses of the flat-boundary theorem
  -- for `u ∘ Φ` there, apply it, and push the resulting `W^{2,2}` function forward by `Ψ`.
  have hp : (2 : ENNReal) ≠ ⊤ := ENNReal.ofNat_ne_top
  -- The two sides of the chart: `Ω₁ = Ω ∩ U` and its flat preimage `Ω₁' = H ∩ U'`.
  set Ω₁ : Opens (EuclideanSpace ℝ ι) := Omega ⊓ U
  set Ω₁' : Opens (EuclideanSpace ℝ ι) := H ⊓ U'
  have hΦ₁ : Wkp.IsChangeOfVariables 2 Ω₁' Ω₁ Φ L c₀ :=
    hΦ.restrict inf_le_right fun x hx => ⟨hΦH hx, hΦ.mapsTo hx.2⟩
  have hΨ₁ : Wkp.IsChangeOfVariables 2 Ω₁ Ω₁' Ψ L' c₁ :=
    hΨ.restrict inf_le_right fun y hy => ⟨hΨΩ hy, hΨ.mapsTo hy.2⟩
  have hΨΦ₁ : LeftInvOn Ψ Φ Ω₁' := hΨΦ.mono fun _ hx => hx.2
  have hΦΨ₁ : RightInvOn Ψ Φ Ω₁ := hΦΨ.mono fun _ hy => hy.2
  have hΩ₁ : ((Ω₁ : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) ⊆ Omega :=
    fun _ hx => hx.1
  -- `u ∘ Φ` is a weak solution on `Ω₁'` with the transformed coefficients and data.
  set u₁ := W1p.restrictL (inf_le_left : Ω₁ ≤ Omega) u
  set u' := W1p.compL Φ hp hΦ₁.differentiableOn hΦ₁.injOn hΦ₁.mapsTo hΦ₁.norm_fderiv_le
    hΦ₁.pos hΦ₁.le_abs_det u₁
  have hf' := memLp_pullbackDensity hΦ₁.differentiableOn hΦ₁.injOn hΦ₁.mapsTo
    hΦ₁.norm_fderiv_le hΦ₁.pos hΦ₁.le_abs_det
    ((Lp.memLp f).mono_measure (Measure.restrict_mono_set mu hΩ₁))
  have hu' : ∀ v : W1p0 mu Ω₁' 2, energyFormH1 (PDE.pullbackPrincipal Φ a) (pullbackDrift Φ b)
      (pullbackDensity Φ c) u' (v : W1p mu Ω₁' 2) =
        ∫ x in Ω₁', hf'.toLp _ x * W1p.value (v : W1p mu Ω₁' 2) x ∂mu := fun v => by
    rw [energyFormH1_compL_eq_setIntegral hΦ₁.differentiableOn hΦ₁.injOn hΦ₁.mapsTo
      hΦ₁.norm_fderiv_le hΦ₁.pos hΦ₁.le_abs_det hΨ₁.differentiableOn hΨ₁.mapsTo
      hΨ₁.norm_fderiv_le hΨ₁.pos hΨ₁.le_abs_det hΨΦ₁ hΦΨ₁
      (energyFormH1_restrictL_eq_setIntegral inf_le_left hu) v]
    refine integral_congr_ae ?_
    filter_upwards [hf'.coeFn_toLp] with x hx
    rw [hx]
  -- `‖v‖ ≤ L' ‖DΦ(x) v‖` on `Ω₁'`, since `DΨ(Φ x)` inverts `DΦ(x)`.
  have hinv : ∀ x ∈ (Ω₁' : Set (EuclideanSpace ℝ ι)), ∀ v, ‖v‖ ≤ L' * ‖fderiv ℝ Φ x v‖ :=
    fun _ hx => norm_le_mul_norm_fderiv_apply_of_leftInvOn hΦ₁.differentiableOn hΦ₁.mapsTo
      hΨ₁.differentiableOn hΨΦ₁ hx (hΨ₁.norm_fderiv_le _ (hΦ₁.mapsTo hx))
  have hΩ₁' : (Ω₁' : Set (EuclideanSpace ℝ ι)) ∩ U' = Ω₁' := inter_eq_left.2 fun _ hx => hx.2
  -- The transformed principal coefficient is uniformly elliptic on `Ω₁'`. The constants of
  -- `UniformlyEllipticOn.pullbackPrincipal` need a nonempty index type, which `ν ≠ 0` provides,
  -- and a nonempty set; on the empty set any admissible constants do.
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hν (Subsingleton.elim _ _)
  obtain ⟨lam', Lam', ha'⟩ : ∃ lam' Lam', UniformlyEllipticOn
      ((Ω₁' : Set (EuclideanSpace ℝ ι)) ∩ U') (PDE.pullbackPrincipal Φ a) lam' Lam' := by
    rw [hΩ₁']
    rcases (Ω₁' : Set (EuclideanSpace ℝ ι)).eq_empty_or_nonempty with hempty | hne
    · obtain ⟨hlam, hlamLam, -⟩ := uniformlyEllipticOn_iff.1 ha
      exact ⟨lam, Lam, uniformlyEllipticOn_iff.2 ⟨hlam, hlamLam, fun x hx => by
        rw [hempty] at hx
        exact hx.elim⟩⟩
    · exact ⟨_, _, ha.pullbackPrincipal hΦ₁.mapsTo hne hΦ₁.norm_fderiv_le hinv hΦ₁.pos
        hΦ₁.le_abs_det⟩
  -- It is Lipschitz, since `Φ` and `DΦ` are Lipschitz on `U'`.
  have hsub : (Ω₁' : Set (EuclideanSpace ℝ ι)) ∩ U' ⊆ U' := inter_subset_right
  obtain ⟨K', hK'⟩ := exists_lipschitzOnWith_matrixBilinearForm_pullbackPrincipal
    (t := (Omega : Set (EuclideanSpace ℝ ι)) ∩ U) (hΦ₁.mapsTo.mono_left inter_subset_left)
    (hΦL.mono hsub) (hDΦL.mono hsub)
    (fun x hx => hΦ.norm_fderiv_le x hx.2) (fun x hx => hinv x hx.1) hK
    (fun y hy => ha.opNorm_matrixBilinearForm_le hy)
  -- The transformed lower-order coefficients stay bounded.
  have hb' := memLp_pullbackDrift hΦ₁.differentiableOn hΦ₁.mapsTo hΦ₁.norm_fderiv_le hΦ₁.pos
    hΦ₁.le_abs_det hΨ₁.differentiableOn hΨ₁.norm_fderiv_le hΨΦ₁ hΦΨ₁
    (hb.mono_measure (Measure.restrict_mono_set mu hΩ₁))
  have hc' := memLp_pullbackDensity hΦ₁.differentiableOn hΦ₁.injOn hΦ₁.mapsTo
    hΦ₁.norm_fderiv_le hΦ₁.pos hΦ₁.le_abs_det (hc.mono_measure (Measure.restrict_mono_set mu hΩ₁))
  -- `V' = U' ∩ Φ⁻¹(V)` lies in the compact set `Ψ(closure V) ⊆ U'`.
  set V' : Opens (EuclideanSpace ℝ ι) :=
    ⟨(U' : Set (EuclideanSpace ℝ ι)) ∩ Φ ⁻¹' V,
      hΦ.differentiableOn.continuousOn.isOpen_inter_preimage U'.isOpen V.isOpen⟩
  have hKV : IsCompact (Ψ '' closure (V : Set (EuclideanSpace ℝ ι))) :=
    hV.image_of_continuousOn (hΨ.differentiableOn.continuousOn.mono hVU)
  have hclV' : closure (V' : Set (EuclideanSpace ℝ ι)) ⊆ Ψ '' closure V :=
    closure_minimal (fun x hx => ⟨Φ x, subset_closure hx.2, hΨΦ hx.1⟩) hKV.isClosed
  -- The flat-boundary theorem puts `u ∘ Φ` in `W^{2,2}(Ω₁' ∩ V')`.
  obtain ⟨W', hW'⟩ := ha'.exists_lowerOrder_eq_restrictL_of_mapsTo (mu := mu) hν hH
    (by rw [hΩ₁']; rfl) hK' hb' hc' hu'
    (fun ψ hψ hψc hψU => W1p.exists_w1p0_value_ae_eq_mul_value_compL hp
      hΦ₁.differentiableOn hΦ₁.injOn hΦ₁.mapsTo hΦ₁.norm_fderiv_le hΦ₁.pos hΦ₁.le_abs_det
      hΦ.differentiableOn.continuousOn hΦ.mapsTo hΨ₁.differentiableOn.continuousOn hΨ₁.mapsTo
      hΨΦ₁ hu0 hψ hψc hψU)
    (hKV.of_isClosed_subset isClosed_closure hclV')
    (hclV'.trans (hΨ.mapsTo.mono_left hVU).image_subset)
  -- Precomposition with `Ψ` carries it back to `Ω ∩ V`.
  have hΩV : ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) ⊆ Ω₁ :=
    fun y hy => ⟨hy.1, hVU (subset_closure hy.2)⟩
  have hΨ₂ : Wkp.IsChangeOfVariables 2 (Omega ⊓ V) (Ω₁' ⊓ V') Ψ L' c₁ :=
    hΨ.restrict (fun y hy => (hΩV hy).2) fun y hy =>
      ⟨hΨ₁.mapsTo (hΩV hy), hΨ.mapsTo (hΩV hy).2, by
        rw [mem_preimage, hΦΨ (hΩV hy).2]
        exact hy.2⟩
  refine ⟨Wkp.compL hΨ₂ hp W', ?_⟩
  rw [← Wkp.firstOrder_one, Wkp.firstOrder_compL, Wkp.firstOrder_one, hW']
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [W1p.value_compL_ae Ψ hp hΨ₂.differentiableOn hΨ₂.injOn hΨ₂.mapsTo
      hΨ₂.norm_fderiv_le hΨ₂.pos hΨ₂.le_abs_det
      (W1p.restrictL (inf_le_left : Ω₁' ⊓ V' ≤ Ω₁') u'),
    hΨ₂.ae_comp (W1p.value_restrictL_ae (inf_le_left : Ω₁' ⊓ V' ≤ Ω₁') u'),
    hΨ₂.ae_comp (ae_restrict_of_ae_restrict_of_subset (fun _ hx => hx.1)
      (W1p.value_compL_ae Φ hp hΦ₁.differentiableOn hΦ₁.injOn hΦ₁.mapsTo hΦ₁.norm_fderiv_le
        hΦ₁.pos hΦ₁.le_abs_det u₁)),
    ae_restrict_of_ae_restrict_of_subset hΩV (W1p.value_restrictL_ae inf_le_left u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
    ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with y h1 h2 h3 h4 h5 hy
  rw [h1, h2, h3, hΦΨ₁ (hΩV hy), h4, h5]

/-- **Local `H²` regularity near a boundary portion flattened by a `C²` change of variables.** Let
`ν ≠ 0`, and let `H` be an open set mapped into itself by every translation orthogonal to `ν`, as
a half-space `{x | c₀ < ⟪x, ν⟫}` is. Let `Φ` be a change of variables of order two from an open
set `U'` into `U`, with inverse `Ψ` a change of variables of order two from `U` into `U'`,
such that `Φ` maps `H ∩ U'` into `Ω` and `Ψ` maps `Ω ∩ U` into `H`; so `Φ` maps `H ∩ U'` onto
`Ω ∩ U`. Let `a` be uniformly elliptic on `Ω ∩ U`, with `x ↦ a(x)` Lipschitz on `Ω ∩ U` in the
operator norm of its bilinear forms, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

such that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `U`: `u` vanishes on
`∂Ω ∩ U`. Then on every open `V` whose closure is compact and contained in `U`, the restriction
of `u` to `Ω ∩ V` is the first-order part of an element of `W^{2,2}(Ω ∩ V)`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_isChangeOfVariables
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c : EuclideanSpace ℝ ι → ℝ} {lam Lam : ℝ} {K : ℝ≥0} {ν : EuclideanSpace ℝ ι} (hν : ν ≠ 0)
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΦ : Wkp.IsChangeOfVariables 2 U' U Φ L c₀) (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L' c₁)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U)
    (hΦH : MapsTo Φ ((H : Set (EuclideanSpace ℝ ι)) ∩ U') Omega)
    (hΨΩ : MapsTo Ψ ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U) H)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x))
      ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVU : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ U) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 2,
      Wkp.lowerOrder 1 W = W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u := by
  -- Shrink `U'` to an open neighbourhood `W` of the compact set `Ψ(closure V)` with compact closure
  -- in `U'`, and `U` to its image `U ∩ Ψ⁻¹(W)`. The `C²` map `Φ` and its derivative are locally
  -- Lipschitz on `U'`, hence Lipschitz on the compact set `closure W`.
  have hKV : IsCompact (Ψ '' closure (V : Set (EuclideanSpace ℝ ι))) :=
    hV.image_of_continuousOn (hΨ.differentiableOn.continuousOn.mono hVU)
  obtain ⟨W, hWo, hKW, hWU', hWc⟩ := exists_open_between_and_isCompact_closure hKV U'.isOpen
    (hΨ.mapsTo.mono_left hVU).image_subset
  have hW : W ⊆ U' := subset_closure.trans hWU'
  obtain ⟨KΦ, hΦL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hWc (f := Φ) <| by
    intro x hx
    obtain ⟨K, t, ht, h⟩ := ((hΦ.contDiffOn.contDiffAt (U'.isOpen.mem_nhds (hWU' hx))).of_le
      one_le_two).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, h⟩
  have hD : ContDiffOn ℝ 1 (fderiv ℝ Φ) U' := hΦ.contDiffOn.fderiv_of_isOpen U'.isOpen (by norm_num)
  obtain ⟨KD, hDΦL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hWc
      (f := fderiv ℝ Φ) <| by
    intro x hx
    obtain ⟨K, t, ht, h⟩ :=
      (hD.contDiffAt (U'.isOpen.mem_nhds (hWU' hx))).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, h⟩
  set W' : Opens (EuclideanSpace ℝ ι) := ⟨W, hWo⟩
  set U₀ : Opens (EuclideanSpace ℝ ι) :=
    ⟨(U : Set (EuclideanSpace ℝ ι)) ∩ Ψ ⁻¹' W,
      hΨ.differentiableOn.continuousOn.isOpen_inter_preimage U.isOpen hWo⟩
  have hU₀ : (U₀ : Set (EuclideanSpace ℝ ι)) ⊆ U := inter_subset_left
  refine exists_lowerOrder_eq_restrictL_of_isChangeOfVariables_of_lipschitzOnWith (U' := W')
    (U := U₀) hν hH
    (hΦ.restrict (fun x hx => hW hx) fun x hx => ⟨hΦ.mapsTo (hW hx), by
      rw [mem_preimage, hΨΦ (hW hx)]
      exact hx⟩)
    (hΨ.restrict (fun y hy => hU₀ hy) fun y hy => hy.2)
    (hΦL.mono subset_closure) (hDΦL.mono subset_closure) (hΨΦ.mono hW) (hΦΨ.mono hU₀)
    (hΦH.mono_left (inter_subset_inter_right _ hW))
    (hΨΩ.mono_left (inter_subset_inter_right _ hU₀))
    (ha.mono_set (inter_subset_inter_right _ hU₀)) (hK.mono (inter_subset_inter_right _ hU₀))
    hb hc hu (fun ψ hψ hψc hψU => hu0 ψ hψ hψc (hψU.trans hU₀)) hV
    fun y hy => ⟨hVU hy, hKW (mem_image_of_mem Ψ hy)⟩

end PDE

end TauCeti
