/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HalfSpace
public import TauCeti.Analysis.PDE.Regularity.Interior
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.Sobolev.W1p.Localization

/-!
# Local `H²` regularity near a flat part of the boundary

Let `H` be an open half-space `{x | c < ⟪x, ν⟫}` in `ℝⁿ`, and let `Ω` and `U` be open with
`Ω ∩ U = H ∩ U`: inside `U`, the domain is the half-space and its boundary is the flat
hyperplane `∂H`. Let `a` be uniformly elliptic on `Ω ∩ U` and Lipschitz there, up to the flat
boundary, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

that vanishes on the flat boundary portion `∂Ω ∩ U`, in the sense that `ψ u ∈ H¹₀(Ω)` for every
smooth `ψ` compactly supported in `U`. This file proves that `u` is `H²` up to that boundary
portion: on `Ω ∩ V` for every open `V` whose closure is compact and contained in `U`, the
restriction of `u` is the first-order part of an element of `W^{2,2}(Ω ∩ V)`.

Nothing is assumed about the rest of `∂Ω`, nor about `a` away from `U` beyond the weak
formulation; the lower-order coefficients `b` and `c` are still assumed to lie in `L∞(Ω)` on all
of `Ω`. This is the local statement used to prove global `H²` regularity on a `C²`
domain: flattening the boundary in a chart turns the equation into one of the same form on a
half-space, with Lipschitz coefficients, near the flat part of its boundary.

## The argument

The classical proof (Evans, §6.3.2, Theorem 4) localizes the global theorem on the half-space
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`).

* The field `a` agrees, on `Ω ∩ W` for an open `W` with `closure V ⊆ W ⊆ U`, with a bounded
  Lipschitz field `a'` on `ℝⁿ` that is uniformly elliptic on `H`
  (`TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn_inter`).
* On `Ω ∩ W` the restriction of `u` solves the equation with `a'`, and the lower-order terms move
  to the right-hand side.
* For a cutoff `ψ` equal to one near `closure V` and supported in `W`, the zero boundary values of
  `u` give `ψ u ∈ H¹₀(Ω ∩ W)` (`TauCeti.W1p.restrictL_mem_w1p0Submodule_of_isCompact`). Extended by
  zero, `ψ u ∈ H¹₀(H)` solves an equation `-div(a' ∇w) = g` on all of `H` with `g ∈ L²(H)`
  (`TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem`), because
  `tsupport ψ ∩ H ⊆ Ω ∩ W`.
* The global theorem on `H` gives `L²` second derivatives of `ψ u`, which agrees with `u` on
  `Ω ∩ V`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_mapsTo`: local `H²`
  regularity near a part of the boundary along which `Ω` agrees with a domain invariant under
  the translations parallel to a hyperplane.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_halfSpace`: the case of a
  half-space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorem 4 (boundary `H²`
  regularity, flat boundary case).
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
  [mu.IsAddHaarMeasure] {Omega H U V : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam c₀ : ℝ} {K : ℝ≥0} {ν : EuclideanSpace ℝ ι}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-- **Local `H²` regularity near a flat part of the boundary.** Let `ν ≠ 0`, and let `H` be an
open set mapped into itself by every translation orthogonal to `ν`, as a half-space
`{x | c₀ < ⟪x, ν⟫}` is. Let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`. Let `a` be uniformly
elliptic on `Ω ∩ U`, with `x ↦ a(x)` Lipschitz on `Ω ∩ U` in the operator norm of its bilinear
forms, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

such that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `U`: `u` vanishes on
`∂Ω ∩ U`. Then on every open `V` whose closure is compact and contained in `U`, the restriction
of `u` to `Ω ∩ V` is the first-order part of an element of `W^{2,2}(Ω ∩ V)`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_mapsTo (hν : ν ≠ 0)
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
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
  -- Near `closure V`, the field agrees with a Lipschitz field `a'` uniformly elliptic on `H`.
  obtain ⟨a', K', M, W, hVW, hWU, ha', hK', hM', haa'⟩ :=
    ha.exists_lipschitzWith_eqOn_inter (T := H) hK (hΩU ▸ subset_rfl) hV hVU
  set Ω₁ : Opens (EuclideanSpace ℝ ι) := Omega ⊓ W
  have hΩ₁ : Ω₁ ≤ Omega := inf_le_left
  have hWU' : (W : Set (EuclideanSpace ℝ ι)) ⊆ U := SetLike.coe_subset_coe.mpr hWU
  -- Near `U` the domain is the half-space, so `Ω ∩ W ⊆ H`.
  have hΩ₁H : Ω₁ ≤ H := fun x hx => by
    have hxU : x ∈ (Omega : Set (EuclideanSpace ℝ ι)) ∩ U := ⟨hx.1, hWU' hx.2⟩
    rw [hΩU] at hxU
    exact hxU.1
  -- On `Ω ∩ W`, the restriction of `u` solves the equation with the principal coefficient `a'`,
  -- and the lower-order terms move to the right-hand side.
  set u₁ := W1p.restrictL hΩ₁ u
  obtain ⟨g, hg⟩ := exists_forcing_restrictL_of_eqOn hΩ₁
    (fun x hx => haa' ⟨⟨hx.1, hWU' hx.2⟩, hx.2⟩)
    (memLp_energyIntegrand_of_continuous hM' hK'.continuous _) hb hc hu
  -- A cutoff equal to one near `closure V` and supported in `W`.
  obtain ⟨ψ, N, hψ, -, hψ1, hψc, hψs, hN, hψN, hgradN⟩ :=
    hV.exists_contDiff_cutoff_with_bounds W.isOpen hVW
  have hψ_V : ∀ x ∈ closure (V : Set (EuclideanSpace ℝ ι)), ψ x = 1 ∧ ∇ ψ x = 0 := fun x hx => by
    have hev : ψ =ᶠ[nhds x] fun _ => (1 : ℝ) := mem_interior_iff_mem_nhds.1 (hψ1 hx)
    exact ⟨hev.eq_of_nhds, hev.gradient_eq.trans (gradient_fun_const x 1)⟩
  -- The zero boundary values of `u` give `ψ u ∈ H¹₀(Ω ∩ W)`.
  obtain ⟨v, hv⟩ := hu0 ψ hψ hψc (hψs.trans hWU')
  have hv0 : ∀ᵐ x ∂mu.restrict Omega, x ∉ tsupport ψ → W1p.value (v : W1p mu Omega 2) x = 0 := by
    filter_upwards [hv] with x hx hxψ
    rw [hx, image_eq_zero_of_notMem_tsupport hxψ, zero_mul]
  have hmem := W1p.restrictL_mem_w1p0Submodule_of_isCompact (by norm_num) hψc hψs v.2 hv0
  have hψu : W1p.contDiffSMul ψ hψ hN (fun x _ => hψN x) (fun x _ => hgradN x) u₁ =
      W1p.restrictL hΩ₁ (v : W1p mu Omega 2) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hψ hN (fun x _ => hψN x) (fun x _ => hgradN x) u₁,
      W1p.value_restrictL_ae hΩ₁ u, W1p.value_restrictL_ae hΩ₁ (v : W1p mu Omega 2),
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hΩ₁) hv] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4, smul_eq_mul]
  -- Extended by zero, `ψ u` solves an equation on all of `H`.
  have hts : tsupport ψ ∩ H ⊆ (Ω₁ : Set (EuclideanSpace ℝ ι)) := fun x hx => by
    have hxU : x ∈ (H : Set (EuclideanSpace ℝ ι)) ∩ U := ⟨hx.2, hWU' (hψs hx.1)⟩
    rw [← hΩU] at hxU
    exact ⟨hxU.1, hψs hx.1⟩
  obtain ⟨w, g', hw, -, -, hwg⟩ := exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem
    hM' hK' hΩ₁H hg hψ hψc hts hN _ _ (hψu ▸ hmem)
  -- On `Ω ∩ V`, the gradient of `ψ u` is that of `u`.
  have hVW' : (V : Set (EuclideanSpace ℝ ι)) ⊆ W := subset_closure.trans hVW
  have hΩVΩ₁ : ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) ⊆ Ω₁ :=
    fun x hx => ⟨hx.1, hVW' hx.2⟩
  have hΩV : Omega ⊓ V ≤ H := fun x hx => hΩ₁H (hΩVΩ₁ hx)
  have hgradV : ∀ᵐ x ∂mu.restrict (Omega ⊓ V), W1p.gradient (w : W1p mu H 2) x =
      W1p.gradient (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) x := by
    filter_upwards [W1p.gradient_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
      ae_restrict_of_ae_restrict_of_subset hΩVΩ₁ (W1p.gradient_restrictL_ae hΩ₁ u),
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hΩV) hwg,
      ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h1 h2 h3 hx
    have hxV := hψ_V x (subset_closure hx.2)
    rw [h1, h3, indicator_of_mem (hΩVΩ₁ hx), hxV.1, hxV.2, one_smul, smul_zero, add_zero, h2]
  -- The global theorem on `H` gives the second derivatives.
  exact W1p.exists_lowerOrder_eq_of_gradient_eq_of_hasWeakLineDerivOn
    (EuclideanSpace.basisFun ι ℝ) hΩV hgradV fun i j =>
      ha'.exists_hasWeakLineDerivOn_gradient_of_mapsTo hν hH hK'.lipschitzOnWith hw _ _

/-- **Local `H²` regularity near the boundary of a half-space.** Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, and let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`, so that `∂Ω ∩ U` is a piece of the
hyperplane `∂H`. Let `a` be uniformly elliptic on `Ω ∩ U`, with `x ↦ a(x)` Lipschitz on `Ω ∩ U`
in the operator norm of its bilinear forms, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`, such that `ψ u ∈ H¹₀(Ω)`
for every smooth `ψ` compactly supported in `U`. Then on every open `V` whose closure is compact
and contained in `U`, the restriction of `u` to `Ω ∩ V` is the first-order part of an element of
`W^{2,2}(Ω ∩ V)`. This is the half-space case of
`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_halfSpace (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
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
      Wkp.lowerOrder 1 W = W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u :=
  ha.exists_lowerOrder_eq_restrictL_of_mapsTo hν
    (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hH hτ) hΩU hK hb hc hu hu0 hV hVU

end PDE

end TauCeti
