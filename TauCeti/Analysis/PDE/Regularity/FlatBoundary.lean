/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.ScalarBootstrap
import TauCeti.Analysis.PDE.Regularity.Interior.Basic
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

The `H³` statement is the `k = 1` instance of the finite-order flat-boundary theorem
`TauCeti.PDE.UniformlyEllipticOn.exists_value_succ_succ_eq_value_restrictL_of_mapsTo`
in `Regularity/Boundary/ScalarBootstrap.lean`.

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
  apply ha.exists_value_succ_succ_eq_value_restrictL_of_mapsTo hν hHc hH hΩU hsmooth
    1 (W1p.restrictL inf_le_left F) ?_ hu0 hV hVU
  intro v
  rw [Wkp.value_one (W1p.restrictL (inf_le_left : Omega ⊓ U ≤ Omega) F),
    energyFormH1_restrictL_eq_setIntegral inf_le_left hu]
  exact integral_congr_ae ((W1p.value_restrictL_ae inf_le_left F).mono fun x hx ↦
    congrArg (· * W1p.value (v : W1p mu (Omega ⊓ U) 2) x) hx.symm)

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
