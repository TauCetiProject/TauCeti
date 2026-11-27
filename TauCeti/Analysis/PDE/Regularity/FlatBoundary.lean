/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HalfSpace.HigherOrder
public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.Sobolev.W1p.Localization

/-!
# Local `H²` and `H^{m+2}` regularity near a flat part of the boundary

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

Each derivative of the data buys one more derivative of the solution when the coefficients allow
it. If the entries of `a` are smooth on `U`, up to the flat boundary portion, and `u` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = F` with `F ∈ W^{m,2}(Ω)`, then the restriction of `u` to `Ω ∩ V` lies in
`W^{m+2,2}(Ω ∩ V)`, for every `m ≥ 0`. This is the flat model of higher regularity up to the
boundary (Evans, §6.3.2, Theorem 5): for a domain with smooth boundary and smooth coefficients,
flattening a boundary portion in a chart leads to it.

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

The `H^{m+2}` statement localizes the global `H^{m+2}` theorem on the half-space
(`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_mapsTo_of_contDiffOn`) in the same way,
by induction on `m`, with two changes.

* The field `a` is replaced, near `closure V`, by a field `a'` with smooth entries that is
  uniformly elliptic on `H` and equal to `λ I` far away
  (`TauCeti.PDE.UniformlyEllipticOn.exists_contDiff_eqOn_inter`), so that its derivatives of every
  order are bounded, as the half-space theorem requires.
* The forcing of the equation for `ψ u`,
  `ψ F - ⟨∇u, a' ∇ψ⟩ - ⟨∇ψ, a' ∇u⟩ - u div(a' ∇ψ)`, must now lie in `W^{m+1,2}(H)` when
  `F ∈ W^{m+1,2}(Ω)`. It is a combination of `F`, the first derivatives of `u` and `u` with smooth
  compactly supported multipliers, so it lies in `W^{m+1,2}(Ω ∩ W)` because `u` is already
  `W^{m+2,2}` there by the induction hypothesis, applied on `W`
  (`TauCeti.PDE.exists_value_ae_eq_localizedForcing`). It vanishes off `tsupport ψ`, and
  `tsupport ψ ∩ H ⊆ Ω ∩ W`, so its extension by zero lies in `W^{m+1,2}(H)`
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
  `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_halfSpace`:
  local `H^{m+2}` regularity near such a boundary portion for coefficients smooth up to it and
  forcing in `W^{m,2}`.

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

/-! ### `H^{m+2}` regularity near a flat part of the boundary -/

section HigherOrder

omit [DecidableEq ι] in
/-- **The localized equation on the whole flat domain.** Let `Ω ⊆ H` and let `u ∈ W^{m+1,2}(Ω)`
solve `-div(a ∇u) = F` in `Ω` with `F ∈ W^{m,2}(Ω)`, for a bounded Lipschitz field `a` with smooth
entries. Let `ψ` be a smooth cutoff with `tsupport ψ ∩ H ⊆ Ω` and `ψ u ∈ H¹₀(Ω)`. Then `ψ u`,
extended by zero, lies in `H¹₀(H)` and solves `-div(a ∇w) = G` in `H` with `G ∈ W^{m,2}(H)`. -/
private theorem exists_isWeakSolutionDirichlet_value_ae_eq_indicator {a' : EuclideanSpace ℝ ι →
    Matrix ι ι ℝ} {M : ℝ} (hM : ∀ x, ‖matrixBilinearForm (a' x)‖ ≤ M)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a' x))
    (hsm : ∀ i j, ContDiff ℝ ∞ fun x => a' x i j) (hΩH : Omega ≤ H) (m : ℕ)
    {F : Wkp mu Omega 2 m} {U : Wkp mu Omega 2 (m + 1)}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a' 0 0 (Wkp.firstOrder m U) (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value m F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {N : ℝ} (hN : 0 ≤ N)
    (hψN : ∀ x ∈ Omega, |ψ x| ≤ N) (hgradN : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N)
    (hmem : W1p.contDiffSMul ψ hψ hN hψN hgradN (Wkp.firstOrder m U) ∈
      w1p0Submodule mu Omega 2) :
    ∃ w : W1p0 mu H 2, ∃ G : Wkp mu H 2 m, IsWeakSolutionDirichlet a' 0 0 (Wkp.value m G) w ∧
      ∀ᵐ x ∂mu.restrict H, W1p.value (w : W1p mu H 2) x =
        (Omega : Set (EuclideanSpace ℝ ι)).indicator
          (fun y => ψ y * W1p.value (Wkp.firstOrder m U) y) x := by
  obtain ⟨w, g, hw, hg, hwv, -⟩ :=
    exists_isWeakSolutionDirichlet_extendByZeroL_contDiffSMul_of_mem hM hK hΩH hu hψ hψc hts hN
      hψN hgradN hmem
  -- The forcing is in `W^{m,2}(Ω)`, vanishes off `tsupport ψ` and so extends by zero to
  -- `W^{m,2}(H)`.
  obtain ⟨h, hh⟩ := exists_value_ae_eq_localizedForcing m hsm hψ hψc F U
  have hh0 : ∀ᵐ x ∂mu.restrict Omega, x ∉ tsupport ψ → Wkp.value m h x = 0 := by
    filter_upwards [hh] with x hx hxψ
    rw [hx, localizedForcing_def a' ψ _ (Wkp.firstOrder m U) x,
      image_eq_zero_of_notMem_tsupport hxψ, gradient_of_notMem_tsupport hxψ,
      divMatrixGradient_eq_zero_of_notMem_tsupport hxψ]
    simp
  obtain ⟨G, hG⟩ := Wkp.exists_value_ae_eq_indicator_of_isClosed (V := H) (p := 2)
    (isClosed_tsupport ψ) (fun x hx => hts ⟨hx.2, hx.1⟩) m h hh0
  refine ⟨w, G, ?_, hwv⟩
  convert hw using 1
  refine Lp.ext ?_
  filter_upwards [hG, hg, ae_restrict_of_ae ((ae_restrict_iff' Omega.isOpen.measurableSet).1 hh)]
    with x h1 h2 h3
  rw [h1, h2]
  by_cases hx : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
  · rw [indicator_of_mem hx, indicator_of_mem hx, h3 hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx]

/-- **The localized solution is `W^{m+2,2}` on the whole flat domain.** Under the hypotheses of
`exists_isWeakSolutionDirichlet_value_ae_eq_indicator`, for a field uniformly elliptic on `H`
whose entries have derivatives of every order bounded, the function `ψ u`, extended by zero, is
the value of an element of `W^{m+2,2}(H)`, by the half-space theorem
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_mapsTo_of_contDiffOn`. -/
private theorem exists_wkp_value_ae_eq_indicator_of_bddDerivOn (hν : ν ≠ 0)
    (hHc : Convex ℝ (H : Set (EuclideanSpace ℝ ι)))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (ha : UniformlyEllipticOn (H : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    (hbd : ∀ i j (k : ℕ), BddDerivOn ℝ k (fun x => a x i j) univ) {M : ℝ}
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M) (hΩH : Omega ≤ H) (m : ℕ)
    {F : Wkp mu Omega 2 m} {U : Wkp mu Omega 2 (m + 1)}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (Wkp.firstOrder m U) (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value m F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hts : tsupport ψ ∩ H ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {N : ℝ} (hN : 0 ≤ N)
    (hψN : ∀ x ∈ Omega, |ψ x| ≤ N) (hgradN : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ N)
    (hmem : W1p.contDiffSMul ψ hψ hN hψN hgradN (Wkp.firstOrder m U) ∈
      w1p0Submodule mu Omega 2) :
    ∃ W : Wkp mu H 2 (m + 2), ∀ᵐ x ∂mu.restrict H, Wkp.value (m + 2) W x =
      (Omega : Set (EuclideanSpace ℝ ι)).indicator
        (fun y => ψ y * W1p.value (Wkp.firstOrder m U) y) x := by
  have hsm : ∀ i j, ContDiff ℝ ∞ fun x => a x i j := fun i j =>
    contDiff_infty.2 fun n => contDiffOn_univ.1 (hbd i j n).contDiffOn
  obtain ⟨w, G, hw, hwv⟩ := exists_isWeakSolutionDirichlet_value_ae_eq_indicator hM hK hsm hΩH m
    hu hψ hψc hts hN hψN hgradN hmem
  -- The derivatives of order at most `m + 1` of the entries of `a` have a common bound.
  choose C hC using fun i j => (hbd i j (m + 1)).exists_bound
  obtain ⟨C', hC'⟩ := (finite_range fun p : ι × ι => C p.1 p.2).bddAbove
  obtain ⟨W, hW⟩ := ha.exists_value_eq_value_of_mapsTo_of_contDiffOn hν hHc hH
    hK.lipschitzOnWith m (fun i j => (hbd i j (m + 1)).contDiffOn.mono (subset_univ _))
    (C := C') (fun i j k _ hk x _ => (hC i j k hk x (mem_univ x)).trans
      (hC' ⟨(i, j), rfl⟩)) hw
  exact ⟨W, by filter_upwards [hwv] with x hx; rw [hW, hx]⟩

omit [DecidableEq ι] in
/-- **Back from the whole flat domain.** Let `Ω₁ ⊆ Ω ∩ H` and let `w ∈ W^{k,2}(H)` agree almost
everywhere with `ψ u` on `Ω₁` and with `0` off `Ω₁`. If `Ω ∩ V ⊆ Ω₁` and `ψ = 1` on `V`, then the
restriction of `u` to `Ω ∩ V` is the value of an element of `W^{k,2}(Ω ∩ V)`. -/
private theorem exists_value_eq_value_restrictL_of_eqOn_one {Ω₁ : Opens (EuclideanSpace ℝ ι)}
    (hΩ₁ : Ω₁ ≤ Omega) (hΩ₁H : Ω₁ ≤ H) (hVΩ₁ : Omega ⊓ V ≤ Ω₁) {ψ : EuclideanSpace ℝ ι → ℝ}
    (hψV : ∀ x ∈ V, ψ x = 1) {u : W1p mu Omega 2} {k : ℕ} {w : Wkp mu H 2 k}
    (hw : ∀ᵐ x ∂mu.restrict H, Wkp.value k w x = (Ω₁ : Set (EuclideanSpace ℝ ι)).indicator
      (fun y => ψ y * W1p.value (W1p.restrictL hΩ₁ u) y) x) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 k,
      Wkp.value k W = W1p.value (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) := by
  have hVH : Omega ⊓ V ≤ H := hVΩ₁.trans hΩ₁H
  refine ⟨Wkp.restrictL hVH k w, Lp.ext ?_⟩
  filter_upwards [Wkp.value_restrictL_ae hVH k w,
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hVH) hw,
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hVΩ₁)
      (W1p.value_restrictL_ae hΩ₁ u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u,
    ae_restrict_mem (Omega ⊓ V).isOpen.measurableSet] with x h1 h2 h3 h4 hx
  rw [h1, h2, indicator_of_mem (hVΩ₁ hx), hψV x hx.2, one_mul, h3, h4]

/-- **Local `H^{m+2}` regularity near a flat part of the boundary, for a smooth field on the whole
space.** The case of
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_mapsTo` in which
the coefficient field is defined on the whole space, uniformly elliptic on `H`, with entries whose
derivatives of every order are bounded, and bounded Lipschitz bilinear forms.

The proof is by induction on `m`. The case `m = 0` is local `H²` regularity
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_mapsTo`). For the step, the
induction hypothesis on a neighbourhood `W` of `closure V` puts `u` in `W^{m+2,2}(Ω ∩ W)`, so the
equation of a cutoff `ψ u` has its forcing in `W^{m+1,2}`, and the half-space theorem applies to
it. -/
private theorem exists_value_eq_value_restrictL_of_bddDerivOn (hν : ν ≠ 0)
    (hHc : Convex ℝ (H : Set (EuclideanSpace ℝ ι)))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
    (ha : UniformlyEllipticOn (H : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzWith K fun x => matrixBilinearForm (a x))
    (hbd : ∀ i j (k : ℕ), BddDerivOn ℝ k (fun x => a x i j) univ) {M : ℝ}
    (hM : ∀ x, ‖matrixBilinearForm (a x)‖ ≤ M) {u : W1p mu Omega 2}
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (m : ℕ) {F : Wkp mu Omega 2 m}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value m F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVU : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ U) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 (m + 2),
      Wkp.value (m + 2) W = W1p.value (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) := by
  have hΩH : ∀ x ∈ (U : Set (EuclideanSpace ℝ ι)),
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) ↔ x ∈ (H : Set (EuclideanSpace ℝ ι)) :=
    fun x hxU => by simpa only [mem_inter_iff, hxU, and_true] using Set.ext_iff.1 hΩU x
  induction m generalizing V with
  | zero =>
    -- Local `H²` regularity.
    obtain ⟨W, hW⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_mapsTo (V := V)
      (b := 0) (c := 0) hν hH hΩU (ha.mono_set fun x hx => (hΩH x hx.2).1 hx.1)
      hK.lipschitzOnWith (MemLp.zero) (MemLp.zero) hu hu0 hV hVU
    exact ⟨W, by rw [← Wkp.value_lowerOrder_one, hW]⟩
  | succ m ih =>
    obtain ⟨W', hWo, hVW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hV U.isOpen hVU
    set W : Opens (EuclideanSpace ℝ ι) := ⟨W', hWo⟩
    have hWU' : (W : Set (EuclideanSpace ℝ ι)) ⊆ U := subset_closure.trans hWU
    -- By the induction hypothesis, `u` is `W^{m+2,2}` on `Ω₁ = Ω ∩ W`, where it solves the same
    -- equation.
    set Ω₁ : Opens (EuclideanSpace ℝ ι) := Omega ⊓ W
    have hΩ₁ : Ω₁ ≤ Omega := inf_le_left
    obtain ⟨U2, hU2v⟩ := ih (F := Wkp.lowerOrder m F)
      (fun v => by rw [← Wkp.value_succ]; exact hu v) (V := W) hWc hWU
    have hU2 : Wkp.firstOrder (m + 1) U2 = W1p.restrictL hΩ₁ u :=
      W1p.ext_value (by rw [Wkp.value_firstOrder, hU2v])
    have hu₁ : ∀ v : W1p0 mu Ω₁ 2,
        energyFormH1 a 0 0 (Wkp.firstOrder (m + 1) U2) (v : W1p mu Ω₁ 2) =
          ∫ x in Ω₁, Wkp.value (m + 1) (Wkp.restrictL hΩ₁ (m + 1) F) x *
            W1p.value (v : W1p mu Ω₁ 2) x ∂mu := fun v => by
      rw [hU2, energyFormH1_restrictL_eq_setIntegral hΩ₁ hu v]
      refine integral_congr_ae ?_
      filter_upwards [Wkp.value_restrictL_ae hΩ₁ (m + 1) F] with x hx
      rw [hx]
    -- A cutoff `ψ` equal to one near `closure V` and supported in `W`; then `ψ u ∈ H¹₀(Ω₁)`.
    obtain ⟨ψ, N, hψ, -, hψ1, hψc, hψs, hN, hψN, hgradN⟩ :=
      hV.exists_contDiff_cutoff_with_bounds hWo hVW
    obtain ⟨v, hv⟩ := W1p.exists_w1p0_value_ae_eq_mul_restrictL hWU' hu0 hψ hψc hψs
    have hψu : W1p.contDiffSMul ψ hψ hN (fun x _ => hψN x) (fun x _ => hgradN x)
        (Wkp.firstOrder (m + 1) U2) = (v : W1p mu Ω₁ 2) := by
      refine W1p.ext_value (Lp.ext ?_)
      filter_upwards [W1p.value_contDiffSMul_ae hψ hN (fun x _ => hψN x) (fun x _ => hgradN x)
        (Wkp.firstOrder (m + 1) U2), hv] with x h1 h2
      rw [h1, hU2, h2, smul_eq_mul]
    -- `ψ u` extends to a Dirichlet solution on `H` with `W^{m+1,2}` forcing, so it is
    -- `W^{m+3,2}` there; on `Ω ∩ V`, where `ψ = 1`, it is `u`.
    have hΩ₁H : Ω₁ ≤ H := fun x hx => (hΩH x (hWU' hx.2)).1 hx.1
    obtain ⟨W3, hW3⟩ := exists_wkp_value_ae_eq_indicator_of_bddDerivOn hν hHc hH ha hK hbd hM
      hΩ₁H (m + 1) hu₁ hψ hψc (fun x hx => ⟨(hΩH x (hWU' (hψs hx.1))).2 hx.2, hψs hx.1⟩) hN _ _
      (hψu ▸ v.property)
    exact exists_value_eq_value_restrictL_of_eqOn_one hΩ₁ hΩ₁H
      (fun x hx => ⟨hx.1, subset_closure.trans hVW hx.2⟩)
      (fun x hx => interior_subset (hψ1 (subset_closure hx))) (hU2 ▸ hW3)

/-- **Local `H^{m+2}` regularity near a flat part of the boundary.** Let `ν ≠ 0`, and let `H` be a
convex open set mapped into itself by every translation orthogonal to `ν`, as a half-space
`{x | c₀ < ⟪x, ν⟫}` is. Let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`. Let `a` be uniformly
elliptic on `Ω ∩ U`, with entries smooth on `U`, up to the flat boundary portion `∂Ω ∩ U`. Let
`m ≥ 0`, let `F ∈ W^{m,2}(Ω)` and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω`

such that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `U`: `u` vanishes on
`∂Ω ∩ U`. Then on every open `V` whose closure is compact and contained in `U`, the restriction
of `u` to `Ω ∩ V` is the value of an element of `W^{m+2,2}(Ω ∩ V)`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_restrictL_of_mapsTo (hν : ν ≠ 0)
    (hHc : Convex ℝ (H : Set (EuclideanSpace ℝ ι)))
    (hH : ∀ τ, ⟪τ, ν⟫_ℝ = 0 → ∀ t : ℝ, MapsTo (· + t • τ) H H)
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U) (m : ℕ) {F : Wkp mu Omega 2 m}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value m F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVU : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ U) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 (m + 2),
      Wkp.value (m + 2) W = W1p.value (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) := by
  -- On a neighbourhood `U₂` of `closure V` with compact closure in `U`, `a` agrees with a smooth
  -- field `a'` on the whole space that is uniformly elliptic on `H`.
  obtain ⟨U₂', hU₂o, hVU₂, hU₂U, hU₂c⟩ :=
    exists_open_between_and_isCompact_closure hV U.isOpen hVU
  set U₂ : Opens (EuclideanSpace ℝ ι) := ⟨U₂', hU₂o⟩
  have hU₂U' : (U₂ : Set (EuclideanSpace ℝ ι)) ⊆ U := subset_closure.trans hU₂U
  obtain ⟨a', K, M, W₀, hU₂W₀, -, ha', -, hK, hbd, hM, haa'⟩ :=
    ha.exists_contDiff_eqOn_inter (T := H) hsmooth (hΩU ▸ subset_rfl) hU₂c hU₂U
  -- On `Ω₂ = Ω ∩ U₂`, the restriction of `u` solves the equation with `a'`.
  set Ω₂ : Opens (EuclideanSpace ℝ ι) := Omega ⊓ U₂
  have hΩ₂ : Ω₂ ≤ Omega := inf_le_left
  have hΩ₂U : (Ω₂ : Set (EuclideanSpace ℝ ι)) ∩ U₂ = (H : Set (EuclideanSpace ℝ ι)) ∩ U₂ := by
    ext x
    have h := Set.ext_iff.1 hΩU x
    exact ⟨fun hx => ⟨(h.1 ⟨hx.1.1, hU₂U' hx.2⟩).1, hx.2⟩,
      fun hx => ⟨⟨(h.2 ⟨hx.1, hU₂U' hx.2⟩).1, hx.2⟩, hx.2⟩⟩
  obtain ⟨W, hW⟩ := exists_value_eq_value_restrictL_of_bddDerivOn (Omega := Ω₂) (U := U₂) hν hHc
    hH hΩ₂U ha' hK hbd hM
    (fun _ hψ hψc hψs => W1p.exists_w1p0_value_ae_eq_mul_restrictL hU₂U' hu0 hψ hψc hψs) m
    (F := Wkp.restrictL hΩ₂ m F)
    (fun v => by
      rw [energyFormH1_restrictL_eq_setIntegral_of_eqOn hΩ₂
        (fun x hx => haa' (hU₂W₀ (subset_closure hx.2))) hu v]
      refine integral_congr_ae ?_
      filter_upwards [Wkp.value_restrictL_ae hΩ₂ m F] with x hx
      rw [hx]) hV hVU₂
  -- Since `V ⊆ U₂`, the sets `Ω ∩ V` and `Ω₂ ∩ V` agree.
  have hVV : Omega ⊓ V ≤ Ω₂ ⊓ V := fun x hx => ⟨⟨hx.1, hVU₂ (subset_closure hx.2)⟩, hx.2⟩
  refine ⟨Wkp.restrictL hVV (m + 2) W, Lp.ext ?_⟩
  filter_upwards [Wkp.value_restrictL_ae hVV (m + 2) W,
    ae_restrict_of_ae_restrict_of_subset hVV (W1p.value_restrictL_ae inf_le_left
      (W1p.restrictL hΩ₂ u)),
    ae_restrict_of_ae_restrict_of_subset (hVV.trans inf_le_left) (W1p.value_restrictL_ae hΩ₂ u),
    W1p.value_restrictL_ae (inf_le_left : Omega ⊓ V ≤ Omega) u] with x h1 h2 h3 h4
  rw [h1, hW, h2, h3, h4]

/-- **Local `H^{m+2}` regularity near the boundary of a half-space.** Let `H = {x | c₀ < ⟪x, ν⟫}`
with `ν ≠ 0`, and let `Ω` and `U` be open with `Ω ∩ U = H ∩ U`, so that `∂Ω ∩ U` is a piece of
the hyperplane `∂H`. Let `a` be uniformly elliptic on `Ω ∩ U`, with entries smooth on `U`, let
`m ≥ 0`, let `F ∈ W^{m,2}(Ω)` and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = F` in
`Ω` such that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `U`. Then on every open
`V` whose closure is compact and contained in `U`, the restriction of `u` to `Ω ∩ V` is the value
of an element of `W^{m+2,2}(Ω ∩ V)`. This is the half-space case of
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_mapsTo`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_restrictL_of_halfSpace
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hΩU : (Omega : Set (EuclideanSpace ℝ ι)) ∩ U = (H : Set (EuclideanSpace ℝ ι)) ∩ U)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ U) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U) (m : ℕ) {F : Wkp mu Omega 2 m}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value m F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVU : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ U) :
    ∃ W : Wkp mu (Omega ⊓ V) 2 (m + 2),
      Wkp.value (m + 2) W = W1p.value (W1p.restrictL (inf_le_left : Omega ⊓ V ≤ Omega) u) :=
  ha.exists_value_eq_value_restrictL_of_mapsTo hν (TauCeti.convex_of_halfSpace hH)
    (fun _ hτ => TauCeti.mapsTo_add_smul_of_halfSpace hH hτ) hΩU hsmooth m hu hu0 hV hVU

end HigherOrder

end PDE

end TauCeti
