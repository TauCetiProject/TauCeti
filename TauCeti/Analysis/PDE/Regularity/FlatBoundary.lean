/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HalfSpace
public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.Sobolev.W1p.Localization

/-!
# Local `H²` and `H³` regularity near a flat part of the boundary

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

One derivative more is available when the data allow it. If the entries of `a` are smooth on `U`,
up to the flat boundary portion, and `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = F` with `F ∈ H¹(Ω)`, then the
restriction of `u` to `Ω ∩ V` lies in `W^{3,2}(Ω ∩ V)`. This is the flat model of `H³` regularity
up to the boundary (Evans, §6.3.2, Theorem 5): for a domain with smooth boundary and smooth
coefficients, flattening a boundary portion in a chart leads to it.

## The argument

The classical proof (Evans, §6.3.2, Theorem 4) localizes the global theorem on the half-space
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_mapsTo`).

* The field `a` agrees, on `Ω ∩ W` for an open `W` with `closure V ⊆ W ⊆ U`, with a bounded
  Lipschitz field `a'` on `ℝⁿ` that is uniformly elliptic on `H`
  (`TauCeti.PDE.UniformlyEllipticOn.exists_lipschitzWith_eqOn_inter`).
* On `Ω ∩ W` the restriction of `u` solves the equation with `a'`, and the lower-order terms move
  to the right-hand side.
* For a cutoff `ψ` equal to one near `closure V` and supported in `W`, the zero boundary values of
  `u` give `ψ u ∈ H¹₀(Ω ∩ W)` (`TauCeti.W1p.exists_w1p0_value_ae_eq_mul_restrictL`). Extended by
  zero, `ψ u ∈ H¹₀(H)` solves an equation `-div(a' ∇w) = g` on all of `H` with `g ∈ L²(H)`
  (`TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem`), because
  `tsupport ψ ∩ H ⊆ Ω ∩ W`. Near `closure V`, where `ψ = 1`, the function `ψ u` is `u` and `g` is
  the forcing on `Ω ∩ W` (`TauCeti.PDE.exists_isWeakSolutionDirichlet_ae_eq_on_of_inter_eq`).
* The global theorem on `H` gives `L²` second derivatives of `ψ u`, which agrees with `u` on
  `Ω ∩ V`.

The `H³` statement localizes the global `H³` theorem on the half-space
(`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_mapsTo`) in the same way, with two
changes.

* The field `a` is replaced, near `closure V`, by a field `a'` with smooth entries that is
  uniformly elliptic on `H` and equal to `λ I` far away
  (`TauCeti.PDE.UniformlyEllipticOn.exists_contDiff_eqOn_inter`), as the half-space theorem
  requires.
* The forcing of the equation for `ψ u`,
  `ψ F - ⟨∇u, a' ∇ψ⟩ - ⟨∇ψ, a' ∇u⟩ - u div(a' ∇ψ)`, must now lie in `H¹(H)`. It is a combination of
  `F`, the first derivatives of `u` and `u` with smooth compactly supported multipliers, so it lies
  in `H¹(Ω ∩ W)` because `u` is already `H²` there by the first part
  (`TauCeti.PDE.exists_value_ae_eq_localizedForcing`). It vanishes off `tsupport ψ`,
  and `tsupport ψ ∩ H ⊆ Ω ∩ W`, so its extension by zero lies in `H¹(H)`
  (`TauCeti.Wkp.exists_value_ae_eq_indicator_of_isClosed`).

## Main declarations

* `TauCeti.PDE.exists_isWeakSolutionDirichlet_ae_eq_on_of_inter_eq`: near a compact set, a
  solution vanishing on a flat part of the boundary agrees with a solution of a Dirichlet problem
  on the whole flat domain.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_mapsTo`: local `H²`
  regularity near a part of the boundary along which `Ω` agrees with a domain invariant under
  the translations parallel to a hyperplane.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_halfSpace`: the case of a
  half-space.
* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_mapsTo` and
  `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_halfSpace`: local `H³`
  regularity near such a boundary portion for coefficients smooth up to it and forcing in `H¹`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorems 4 and 5 (boundary `H²`
  and higher regularity, flat boundary case).
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

omit [DecidableEq ι] in
/-- **Localizing a solution near a flat part of the boundary.** Let `Ω` and `U` be open with
`Ω ∩ U = H ∩ U`, let `W ⊆ U` be open and let `S ⊆ W` be compact. Let `a` be a coefficient field on
the whole space with `‖a(x)‖ ≤ M` and `x ↦ a(x)` Lipschitz, both measured in the operator norm of
its bilinear forms. Let `u ∈ H¹(Ω)` vanish on `∂Ω ∩ U`, in the sense that `ψ u ∈ H¹₀(Ω)` for every
smooth `ψ` compactly supported in `U`, and let its restriction to `Ω ∩ W` be a weak solution of
`-div(a ∇u) = f` in `Ω ∩ W` with `f ∈ L²(Ω ∩ W)`. Then near `S`, `u` agrees, in value and in
gradient, with a weak solution `w ∈ H¹₀(H)` of an equation `-div(a ∇w) = g` on `H`, with
`g ∈ L²(H)` and `g = f` almost everywhere on `S ∩ H`.

One may take for `w` the product of `u` with a smooth cutoff equal to one near `S` and supported
in `W`, extended by zero
(`TauCeti.PDE.exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem`). This is the
boundary counterpart of `TauCeti.PDE.exists_isWeakSolutionDirichlet_top_ae_eq_on_of_isCompact`. -/
theorem exists_isWeakSolutionDirichlet_ae_eq_on_of_inter_eq {M : ℝ}
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
    {W : Opens (EuclideanSpace ℝ ι)} (hWU : (W : Set (EuclideanSpace ℝ ι)) ⊆ U)
    {S : Set (EuclideanSpace ℝ ι)} (hS : IsCompact S) (hSW : S ⊆ W)
    {u : W1p mu Omega 2} {f : Lp ℝ 2 (mu.restrict (Omega ⊓ W))}
    (hu : ∀ v : W1p0 mu (Omega ⊓ W) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left u) (v : W1p mu (Omega ⊓ W) 2) =
        ∫ x in Omega ⊓ W, f x * W1p.value (v : W1p mu (Omega ⊓ W) 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x) :
    ∃ w : W1p0 mu H 2, ∃ g : Lp ℝ 2 (mu.restrict H), IsWeakSolutionDirichlet a 0 0 g w ∧
      (∀ᵐ x ∂mu.restrict H, x ∈ S → W1p.value (w : W1p mu H 2) x = W1p.value u x) ∧
      (∀ᵐ x ∂mu.restrict H, x ∈ S → W1p.gradient (w : W1p mu H 2) x = W1p.gradient u x) ∧
      ∀ᵐ x ∂mu.restrict H, x ∈ S → g x = f x := by
  set Ω₁ : Opens (EuclideanSpace ℝ ι) := Omega ⊓ W
  have hΩ₁ : Ω₁ ≤ Omega := inf_le_left
  -- Inside `U` the domain is the half-space, so `Ω ∩ W ⊆ H` and `H ∩ W ⊆ Ω ∩ W`.
  have hΩ₁H : Ω₁ ≤ H := fun x hx => by
    have hxU : x ∈ (Omega : Set (EuclideanSpace ℝ ι)) ∩ U := ⟨hx.1, hWU hx.2⟩
    rw [hΩU] at hxU
    exact hxU.1
  have hHW : (H : Set (EuclideanSpace ℝ ι)) ∩ W ⊆ Ω₁ := fun x hx => by
    have hxU : x ∈ (H : Set (EuclideanSpace ℝ ι)) ∩ U := ⟨hx.1, hWU hx.2⟩
    rw [← hΩU] at hxU
    exact ⟨hxU.1, hx.2⟩
  -- A cutoff `ψ` equal to one near `S` and supported in `W`; then `ψ u ∈ H¹₀(Ω ∩ W)`.
  obtain ⟨ψ, N, hψ, -, hψ1, hψc, hψs, hN, hψN, hgradN⟩ :=
    hS.exists_contDiff_cutoff_with_bounds W.isOpen hSW
  have hψS : ∀ x ∈ S, ψ =ᶠ[nhds x] fun _ => (1 : ℝ) := fun x hx =>
    mem_interior_iff_mem_nhds.1 (hψ1 hx)
  obtain ⟨v, hv⟩ := W1p.exists_w1p0_value_ae_eq_mul_restrictL hWU hu0 hψ hψc hψs
  have hψu : W1p.contDiffSMul ψ hψ hN (fun x _ => hψN x) (fun x _ => hgradN x)
      (W1p.restrictL hΩ₁ u) = (v : W1p mu Ω₁ 2) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hψ hN (fun x _ => hψN x) (fun x _ => hgradN x)
      (W1p.restrictL hΩ₁ u), hv] with x h1 h2
    rw [h1, h2, smul_eq_mul]
  -- Extended by zero, `ψ u` solves an equation on all of `H`.
  obtain ⟨w, g, hw, hg, hwv, hwg⟩ :=
    exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem hM hK hΩ₁H hu hψ hψc
      (fun x hx => hHW ⟨hx.2, hψs hx.1⟩) hN _ _ (hψu ▸ v.property)
  -- On `S ∩ H ⊆ Ω ∩ W`, where `ψ` is one nearby, `ψ u` and its forcing are `u` and `f`.
  refine ⟨w, g, hw, ?_, ?_, ?_⟩
  · filter_upwards [hwv, ae_restrict_of_ae (ae_imp_of_ae_restrict (W1p.value_restrictL_ae hΩ₁ u)),
      ae_restrict_mem H.isOpen.measurableSet] with x h1 h2 hxH hxS
    have hx := hHW ⟨hxH, hSW hxS⟩
    rw [h1, indicator_of_mem hx, (hψS x hxS).eq_of_nhds, one_mul, h2 hx]
  · filter_upwards [hwg,
      ae_restrict_of_ae (ae_imp_of_ae_restrict (W1p.gradient_restrictL_ae hΩ₁ u)),
      ae_restrict_mem H.isOpen.measurableSet] with x h1 h2 hxH hxS
    have hx := hHW ⟨hxH, hSW hxS⟩
    rw [h1, indicator_of_mem hx, (hψS x hxS).eq_of_nhds,
      (hψS x hxS).gradient_eq.trans (gradient_fun_const x 1), one_smul, smul_zero, add_zero, h2 hx]
  · filter_upwards [hg, ae_restrict_mem H.isOpen.measurableSet] with x h1 hxH hxS
    rw [h1, indicator_of_mem (hHW ⟨hxH, hSW hxS⟩),
      localizedForcing_eq_of_eventuallyEq_one (hψS x hxS)]

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
  have hΩ₁ : Omega ⊓ W ≤ Omega := inf_le_left
  have hWU' : (W : Set (EuclideanSpace ℝ ι)) ⊆ U := SetLike.coe_subset_coe.mpr hWU
  -- On `Ω ∩ W`, the restriction of `u` solves the equation with the principal coefficient `a'`,
  -- and the lower-order terms move to the right-hand side.
  obtain ⟨g, hg, -⟩ := exists_forcing_restrictL_of_eqOn hΩ₁
    (fun x hx => haa' ⟨⟨hx.1, hWU' hx.2⟩, hx.2⟩)
    (memLp_energyIntegrand_of_continuous hM' hK'.continuous _) hb hc hu
  -- Near `closure V`, `u` agrees with a solution `w ∈ H¹₀(H)` of an equation on all of `H`.
  obtain ⟨w, _, hw, -, hwg, -⟩ :=
    exists_isWeakSolutionDirichlet_ae_eq_on_of_inter_eq hM' hK' hΩU hWU' hV hVW hg hu0
  -- On `Ω ∩ V`, the gradient of `w` is that of `u`.
  have hΩV : Omega ⊓ V ≤ H := fun x hx => by
    have hxU : x ∈ (Omega : Set (EuclideanSpace ℝ ι)) ∩ U :=
      ⟨hx.1, hWU' (subset_closure.trans hVW hx.2)⟩
    rw [hΩU] at hxU
    exact hxU.1
  have hgradV : ∀ᵐ x ∂mu.restrict (Omega ⊓ V), W1p.gradient (w : W1p mu H 2) x =
      W1p.gradient (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) x := by
    filter_upwards [W1p.gradient_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hΩV) hwg,
      ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h1 h2 hx
    rw [h1, h2 (subset_closure hx.2)]
  -- The global theorem on `H` gives the second derivatives.
  exact W1p.exists_lowerOrder_eq_of_gradient_eq_of_hasWeakLineDerivOn
    (EuclideanSpace.basisFun ι ℝ) hΩV hgradV fun i j => by
      obtain ⟨G, -, hG⟩ :=
        ha'.exists_norm_le_hasWeakLineDerivOn_gradient_of_mapsTo hν hH hK'.lipschitzOnWith hw _ _
      exact ⟨G, hG⟩

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

/-! ### `H³` regularity near a flat part of the boundary -/

section ThirdOrder

variable {F u : W1p mu Omega 2}

omit [DecidableEq ι] in
/-- **The localized equation on the whole flat domain.** Let `Ω ⊆ H` and let `u ∈ H²(Ω)` solve
`-div(a ∇u) = F` in `Ω` with `F ∈ H¹(Ω)`, for a bounded Lipschitz field `a` with smooth entries.
Let `ψ` be a smooth cutoff with `tsupport ψ ∩ H ⊆ Ω` and `ψ u ∈ H¹₀(Ω)`. Then `ψ u`, extended by
zero, lies in `H¹₀(H)` and solves `-div(a ∇w) = G` in `H` with `G ∈ H¹(H)`. -/
private theorem exists_isWeakSolutionDirichlet_value_ae_eq_indicator {a' : EuclideanSpace ℝ ι →
    Matrix ι ι ℝ} {M : ℝ} (hM : ∀ x, ‖matrixBilinearForm (a' x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a' x))
    (hsm : ∀ i j, ContDiff ℝ ∞ fun x => a' x i j) (hΩH : Omega ≤ H) {F : W1p mu Omega 2}
    {U : Wkp mu Omega 2 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a' 0 0 (Wkp.lowerOrder 1 U) (v : W1p mu Omega 2) =
      ∫ x in Omega, W1p.value F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {N : ℝ} (hN : 0 ≤ N)
    (hψN : ∀ x ∈ Omega, |ψ x| ≤ N) (hgradN : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N)
    (hmem : W1p.contDiffSMul ψ hψ hN hψN hgradN (Wkp.lowerOrder 1 U) ∈
      w1p0Submodule mu Omega 2) :
    ∃ w : W1p0 mu H 2, ∃ G : W1p mu H 2, IsWeakSolutionDirichlet a' 0 0 (W1p.value G) w ∧
      ∀ᵐ x ∂mu.restrict H, W1p.value (w : W1p mu H 2) x =
        (Omega : Set (EuclideanSpace ℝ ι)).indicator
          (fun y => ψ y * W1p.value (Wkp.lowerOrder 1 U) y) x := by
  obtain ⟨w, g, hw, hg, hwv, -⟩ :=
    exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem hM hK hΩH hu hψ hψc hts hN
      hψN hgradN hmem
  -- The forcing is in `H¹(Ω)`, vanishes off `tsupport ψ` and so extends by zero to `H¹(H)`.
  obtain ⟨h, hh⟩ := exists_value_ae_eq_localizedForcing hsm hψ hψc F U
  have hh0 : ∀ᵐ x ∂mu.restrict Omega, x ∉ tsupport ψ → W1p.value h x = 0 := by
    filter_upwards [hh] with x hx hxψ
    rw [hx, localizedForcing_def a' ψ _ (Wkp.lowerOrder 1 U : W1p mu Omega 2) x,
      image_eq_zero_of_notMem_tsupport hxψ, gradient_of_notMem_tsupport hxψ,
      divMatrixGradient_eq_zero_of_notMem_tsupport hxψ]
    simp
  have h1 : Wkp.value (p := 2) 1 h = W1p.value h := Wkp.value_one h
  obtain ⟨G, hG⟩ := Wkp.exists_value_ae_eq_indicator_of_isClosed (V := H) (p := 2)
    (isClosed_tsupport ψ) (fun x hx => hts ⟨hx.2, hx.1⟩) 1 h (by simpa only [h1] using hh0)
  have hG1 : Wkp.value (p := 2) 1 G = W1p.value G := Wkp.value_one G
  rw [h1, hG1] at hG
  refine ⟨w, G, ?_, hwv⟩
  convert hw using 1
  refine Lp.ext ?_
  filter_upwards [hG, hg, ae_restrict_of_ae ((ae_restrict_iff' Omega.isOpen.measurableSet).1 hh)]
    with x h1 h2 h3
  rw [h1, h2]
  by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
  · rw [indicator_of_mem hx, indicator_of_mem hx, h3 hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

/-- **Local `H³` regularity near a flat part of the boundary, for a smooth field on the whole
space.** The case of `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_mapsTo`
in which the coefficient field is defined on the whole space, uniformly elliptic on `H`, with
smooth entries, Lipschitz first derivatives and bounded Lipschitz bilinear forms. -/
private theorem exists_value_eq_value_restrictL_of_contDiff (hν : ν ≠ 0)
    (hHc : Convex ℝ (H : Set (EuclideanSpace ℝ ι)))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
    (ha : UniformlyEllipticOn (H : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsm : ∀ i j, ContDiff ℝ ∞ fun x => a x i j)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x)) {K' : ℝ≥0}
    (hK' : ∀ i j, LipschitzWith K' fun x => fderiv ℝ (fun y => a y i j) x) {M : ℝ}
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, W1p.value F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVU : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ U) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 3,
      Wkp.value 3 W = W1p.value (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) := by
  obtain ⟨W', hWo, hVW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hV U.isOpen hVU
  set W : Opens (EuclideanSpace ℝ ι) := ⟨W', hWo⟩
  have hWU' : (W : Set (EuclideanSpace ℝ ι)) ⊆ U := subset_closure.trans hWU
  have hΩH : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)),
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) ↔ x ∈ (H : Set (EuclideanSpace ℝ ι)) :=
    fun x hxU => by simpa only [mem_inter_iff, hxU, and_true] using Set.ext_iff.1 hΩU x
  -- Local `H²` regularity: `u` is `H²` on `Ω₁ = Ω ∩ W`, where it solves the same equation.
  set Ω₁ : Opens (EuclideanSpace ℝ ι) := Omega ⊓ W
  have hΩ₁ : Ω₁ ≤ Omega := inf_le_left
  obtain ⟨U2, hU2⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_mapsTo (V := W)
    (b := 0) (c := 0) hν hH hΩU (ha.mono_set fun x hx => (hΩH x hx.2).1 hx.1)
    hK.lipschitzOnWith (MemLp.zero) (MemLp.zero) hu hu0 hWc hWU
  have hΩ₁H : Ω₁ ≤ H := fun x hx => (hΩH x (hWU' hx.2)).1 hx.1
  have hu₁ : ∀ v : W1p0 mu Ω₁ 2, energyFormH1 a 0 0 (Wkp.lowerOrder 1 U2) (v : W1p mu Ω₁ 2) =
      ∫ x in Ω₁, W1p.value (W1p.restrictL hΩ₁ F) x * W1p.value (v : W1p mu Ω₁ 2) x ∂mu :=
    fun v => by
      rw [hU2, energyFormH1_restrictL_eq_setIntegral hΩ₁ hu v]
      refine integral_congr_ae ?_
      filter_upwards [W1p.value_restrictL_ae hΩ₁ F] with x hx
      rw [hx]
  -- A cutoff `ψ` equal to one near `closure V` and supported in `W`; then `ψ u ∈ H¹₀(Ω₁)`.
  obtain ⟨ψ, N, hψ, -, hψ1, hψc, hψs, hN, hψN, hgradN⟩ :=
    hV.exists_contDiff_cutoff_with_bounds hWo hVW
  obtain ⟨v, hv⟩ := W1p.exists_w1p0_value_ae_eq_mul_restrictL hWU' hu0 hψ hψc hψs
  have hψu : W1p.contDiffSMul ψ hψ hN (fun x _ => hψN x) (fun x _ => hgradN x)
      (Wkp.lowerOrder 1 U2) = (v : W1p mu Ω₁ 2) := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_contDiffSMul_ae hψ hN (fun x _ => hψN x) (fun x _ => hgradN x)
      (Wkp.lowerOrder 1 U2), hv] with x h1 h2
    rw [h1, hU2, h2, smul_eq_mul]
  -- `ψ u` extends to a Dirichlet solution on `H` with `H¹` forcing, so it is `H³` there.
  have hts : tsupport ψ ∩ H ⊆ (Ω₁ : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    ⟨(hΩH x (hWU' (hψs hx.1))).2 hx.2, hψs hx.1⟩
  obtain ⟨w, G, hw, hwv⟩ := exists_isWeakSolutionDirichlet_value_ae_eq_indicator hM hK hsm
    hΩ₁H hu₁ hψ hψc hts hN _ _ (hψu ▸ v.property)
  obtain ⟨W3, hW3⟩ := ha.exists_value_eq_value_of_mapsTo hν hHc hH hK.lipschitzOnWith
    (fun i j => (hsm i j).contDiffOn) (fun i j => (hK' i j).lipschitzOnWith) hw
  -- On `Ω ∩ V`, where `ψ = 1`, the function `ψ u` is `u`.
  have hVΩ₁ : ((Omega ⊓ V : Opens (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) ⊆ Ω₁ :=
    fun x hx => ⟨hx.1, subset_closure.trans hVW hx.2⟩
  have hVH : Omega ⊓ V ≤ H := fun x hx => hΩ₁H (hVΩ₁ hx)
  refine ⟨Wkp.restrictL hVH 3 W3, Lp.ext ?_⟩
  filter_upwards [Wkp.value_restrictL_ae hVH 3 W3,
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hVH) hwv,
    ae_restrict_of_ae_restrict_of_subset hVΩ₁ (W1p.value_restrictL_ae hΩ₁ u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
    ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h1 h2 h3 h4 hx
  have hψx : ψ x = 1 := interior_subset (hψ1 (subset_closure hx.2))
  rw [h1, hW3, h2, indicator_of_mem (hVΩ₁ hx), hψx, one_mul, hU2, h3, h4]

/-- **Local `H³` regularity near a flat part of the boundary.** Let `ν ≠ 0`, and let `H` be a
convex open set mapped into itself by every translation orthogonal to `ν`, as a half-space
`{x | c₀ < ⟪x, ν⟫}` is. Let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`. Let `a` be uniformly
elliptic on `Ω ∩ U`, with entries smooth on `U`, up to the flat boundary portion `∂Ω ∩ U`. Let
`F ∈ H¹(Ω)` and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω`

such that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `U`: `u` vanishes on
`∂Ω ∩ U`. Then on every open `V` whose closure is compact and contained in `U`, the restriction
of `u` to `Ω ∩ V` is the value of an element of `W^{3,2}(Ω ∩ V)`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_restrictL_of_mapsTo (hν : ν ≠ 0)
    (hHc : Convex ℝ (H : Set (EuclideanSpace ℝ ι)))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, W1p.value F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVU : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ U) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 3,
      Wkp.value 3 W = W1p.value (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) := by
  -- On a neighbourhood `U₂` of `closure V` with compact closure in `U`, `a` agrees with a smooth
  -- field `a'` on the whole space that is uniformly elliptic on `H`.
  obtain ⟨U₂', hU₂o, hVU₂, hU₂U, hU₂c⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  set U₂ : Opens (EuclideanSpace ℝ ι) := ⟨U₂', hU₂o⟩
  have hU₂U' : (U₂ : Set (EuclideanSpace ℝ ι)) ⊆ U := subset_closure.trans hU₂U
  obtain ⟨a', K, K', M, W₀, hU₂W₀, -, ha', hsm', hK, hK', hM, haa'⟩ :=
    ha.exists_contDiff_eqOn_inter (T := H) hsmooth (hΩU ▸ subset_rfl) hU₂c hU₂U
  -- On `Ω₂ = Ω ∩ U₂`, the restriction of `u` solves the equation with `a'`.
  set Ω₂ : Opens (EuclideanSpace ℝ ι) := Omega ⊓ U₂
  have hΩ₂ : Ω₂ ≤ Omega := inf_le_left
  have hΩ₂U : (Ω₂ : Set (EuclideanSpace ℝ ι)) ∩ U₂ = (H : Set (EuclideanSpace ℝ ι)) ∩ U₂ := by
    ext x
    have h := Set.ext_iff.1 hΩU x
    exact ⟨fun hx => ⟨(h.1 ⟨hx.1.1, hU₂U' hx.2⟩).1, hx.2⟩,
      fun hx => ⟨⟨(h.2 ⟨hx.1, hU₂U' hx.2⟩).1, hx.2⟩, hx.2⟩⟩
  obtain ⟨W, hW⟩ := exists_value_eq_value_restrictL_of_contDiff (Omega := Ω₂) (U := U₂) hν hHc hH
    hΩ₂U ha' hsm' hK hK' hM
    (fun v => by
      rw [energyFormH1_restrictL_eq_setIntegral_of_eqOn hΩ₂
        (fun x hx => haa' (hU₂W₀ (subset_closure hx.2))) hu v]
      refine integral_congr_ae ?_
      filter_upwards [W1p.value_restrictL_ae hΩ₂ F] with x hx
      rw [hx])
    (fun _ hψ hψc hψs => W1p.exists_w1p0_value_ae_eq_mul_restrictL hU₂U' hu0 hψ hψc hψs) hV hVU₂
  -- Since `V ⊆ U₂`, the sets `Ω ∩ V` and `Ω₂ ∩ V` agree.
  have hVV : Omega ⊓ V ≤ Ω₂ ⊓ V := fun x hx => ⟨⟨hx.1, hVU₂ (subset_closure hx.2)⟩, hx.2⟩
  refine ⟨Wkp.restrictL hVV 3 W, Lp.ext ?_⟩
  filter_upwards [Wkp.value_restrictL_ae hVV 3 W,
    ae_restrict_of_ae_restrict_of_subset hVV (W1p.value_restrictL_ae inf_le_left
      (W1p.restrictL hΩ₂ u)),
    ae_restrict_of_ae_restrict_of_subset (hVV.trans inf_le_left) (W1p.value_restrictL_ae hΩ₂ u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u] with x h1 h2 h3 h4
  rw [h1, hW, h2, h3, h4]

/-- **Local `H³` regularity near the boundary of a half-space.** Let `H = {x | c₀ < ⟪x, ν⟫}` with
`ν ≠ 0`, and let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`, so that `∂Ω ∩ U` is a piece of the
hyperplane `∂H`. Let `a` be uniformly elliptic on `Ω ∩ U`, with entries smooth on `U`, let
`F ∈ H¹(Ω)` and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω` such that
`ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `U`. Then on every open `V` whose
closure is compact and contained in `U`, the restriction of `u` to `Ω ∩ V` is the value of an
element of `W^{3,2}(Ω ∩ V)`. This is the half-space case of
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_restrictL_of_halfSpace (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, W1p.value F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVU : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ U) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 3,
      Wkp.value 3 W = W1p.value (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) :=
  ha.exists_value_eq_value_restrictL_of_mapsTo hν (TauCeti.convex_of_halfSpace hH)
    (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hH hτ) hΩU hsmooth hu hu0 hV hVU

end ThirdOrder

end PDE

end TauCeti
