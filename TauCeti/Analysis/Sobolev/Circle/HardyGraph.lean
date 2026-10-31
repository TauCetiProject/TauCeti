/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Neck
public import TauCeti.Analysis.Sobolev.Circle.Nemytskii
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The nonlinear Hardy graph of a plumbing node

Let `0 < |a| < 1`. The neck of the plumbing `xy = a` is the annulus `|a| ≤ |x| ≤ 1` in the first
branch coordinate, with outer boundary circles `|x| = 1` and `|y| = 1`. A holomorphic embedding of
the neck into the node `zw = b` is `x ↦ (f(x), b / f(x))` for a nonvanishing holomorphic `f` of
winding number one on the annulus. Its boundary values are `ξ = f` on `|x| = 1` and
`η(y) = b / f(a / y)` on `|y| = 1`, so they satisfy the **node equation** `ξ(x) η(a / x) = b`.
The nonlinear Hardy graph theorem says that, near the identity pair `(ξ, η) = (x, y)`, the
positive Fourier coefficients of `ξ` and `η` are free parameters, and the nonpositive coefficients
and `b` are determined by them, holomorphically in `a` and the parameters, including at the node
`a = 0`.

This file proves this in exponential coordinates `ξ = x e^F`, `η = y e^G`, with `F` and `G` in the
circle Sobolev space `H^s`, `s > 1/2`. In these coordinates the node equation becomes the linear
equation `F(x) + G(a / x) = F₀ + G₀`, with `b = a e^{F₀ + G₀}`. In Fourier coefficients this says
that `(F, G)` lies in the neck graph `CircleSobolev.neckGraph s ℂ a`
(`CircleSobolev.hasSum_zpow_smul_coeff_of_mem_neckGraph`); the multiplicative form is
`CircleSobolev.mul_exp_mul_mul_exp_eq_of_mem_neckGraph`. The positive coefficients of `ξ = x e^F`
are the nonnegative coefficients of `e^F`, shifted by one. So the theorem asks to solve

`indicator (Set.Ici 0) (e^F) = 1 + p`, `indicator (Set.Ici 0) (e^G) = 1 + q`,
`(F, G) ∈ neckGraph s ℂ a`

for `(F, G)` near `0`, given `a` near `0` and nonnegative-frequency `p`, `q` near `0`. Here `e^F`
is the holomorphic Nemytskii map `CircleSobolev.nemytskii exp F`.

The neck graph is the graph of the bounded operator `CircleSobolev.neckTransfer a` over the
nonnegative Laurent subspaces, which depends holomorphically on `a` and vanishes at `a = 0`. After
substituting this parametrization, the equation is a holomorphic equation in `a`, `p`, `q` and the
nonnegative parts of `F` and `G`, whose derivative in the last two variables at the origin is the
identity, because the derivative of `e^F` at `F = 0` is the identity
(`CircleSobolev.hasFDerivAt_nemytskii`). The holomorphic implicit function theorem then gives the
solution and its local uniqueness.

## Main statements

* `TauCeti.CircleSobolev.mul_exp_mul_mul_exp_eq_of_mem_neckGraph`: for `(F, G)` in the neck graph
  and `a ≠ 0`, the node equation `ξ(x) η(a / x) = a e^{F₀ + G₀}` for `ξ = x e^F`, `η = y e^G`, the
  value `η(a / x)` being given by the Laurent series of `G`.
* `TauCeti.CircleSobolev.exists_analyticAt_hardyGraph`: the nonlinear Hardy graph theorem, with a
  solution map analytic in `(a, p, q)` and unique in a fixed neighbourhood of `0`.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §§9–12 (Hardy decompositions at the nodes of a
  plumbed Riemann surface).
-/

public section

noncomputable section

open Complex Filter Topology
open scoped ContDiff

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ}

section NodeEquation

variable {T : ℝ} [Fact (0 < T)] {a : ℂ}

/-- **The node equation.** For `s > 1/2`, `a ≠ 0` and `(F, G)` in the neck graph, the boundary maps
`ξ = x e^F` on `|x| = 1` and `η = y e^G` on `|y| = 1` satisfy `ξ(x) η(a / x) = a e^{F₀ + G₀}` at
every point `x = fourier 1 x` of the unit circle, where `η(a / x)` is evaluated through the
convergent Laurent series `G(a / x) = ∑ₙ (a / x)ⁿ Gₙ`. -/
theorem mul_exp_mul_mul_exp_eq_of_mem_neckGraph (hs : 1 / 2 < s) (ha₀ : a ≠ 0)
    {p : CircleSobolev s ℂ × CircleSobolev s ℂ} (hp : p ∈ neckGraph s ℂ a) (x : AddCircle T) :
    fourier 1 x * exp (toContinuousMap T hs p.1 x) *
        (a / fourier 1 x * exp (∑' n : ℤ, (a / fourier 1 x) ^ n * p.2.coeff n)) =
      a * exp (p.1.coeff 0 + p.2.coeff 0) := by
  have h := (hasSum_zpow_smul_coeff_of_mem_neckGraph hs ha₀ hp x).tsum_eq
  simp only [smul_eq_mul] at h
  have hz : (fourier 1 x : ℂ) ≠ 0 := by
    rw [fourier_apply]
    exact Circle.coe_ne_zero _
  rw [h, mul_mul_mul_comm, ← exp_add, mul_div_cancel₀ _ hz, add_sub_cancel]

end NodeEquation

section HardyGraph

variable [hs : Fact (1 / 2 < s)]

/-- The projection of `H^s` onto its nonnegative Laurent subspace. -/
private def nonnegPart : CircleSobolev s ℂ →L[ℂ] supported s ℂ (Set.Ici 0) :=
  (indicator (Set.Ici 0)).codRestrict _ (indicator_mem_supported (Set.Ici 0))

private theorem coe_nonnegPart (u : CircleSobolev s ℂ) :
    (nonnegPart u : CircleSobolev s ℂ) = indicator (Set.Ici 0) u :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ u

private theorem nonnegPart_sub_neckTransfer (a : ℂ) (P : supported s ℂ (Set.Ici 0))
    (u : CircleSobolev s ℂ) : nonnegPart ((P : CircleSobolev s ℂ) - neckTransfer a u) = P := by
  ext1
  rw [coe_nonnegPart, map_sub, indicator_eq_self_iff.2 P.2,
    indicator_eq_zero_iff.2 (by rw [Set.compl_Ici]; exact neckTransfer_mem_supported a u),
    sub_zero]

omit hs in
private theorem indicator_Ici_one : indicator (Set.Ici 0) (1 : CircleSobolev s ℂ) = 1 :=
  indicator_eq_self_iff.2 (single_mem_supported (Set.mem_Ici.2 le_rfl) _)

/-- The element of the neck graph with nonnegative parts `PQ`. -/
private def neckPoint (a : ℂ) (PQ : supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)) :
    CircleSobolev s ℂ × CircleSobolev s ℂ :=
  ((PQ.1 : CircleSobolev s ℂ) - neckTransfer a PQ.2,
    (PQ.2 : CircleSobolev s ℂ) - neckTransfer a PQ.1)

omit hs in
private theorem neckPoint_mem_neckGraph {a : ℂ} (ha : ‖a‖ ≤ 1)
    (PQ : supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)) :
    neckPoint a PQ ∈ neckGraph s ℂ a :=
  sub_neckTransfer_mem_neckGraph ha PQ.1.2 PQ.2.2

private theorem neckPoint_nonnegPart {a : ℂ} (ha : ‖a‖ ≤ 1)
    {p : CircleSobolev s ℂ × CircleSobolev s ℂ} (hp : p ∈ neckGraph s ℂ a) :
    neckPoint a (nonnegPart p.1, nonnegPart p.2) = p := by
  simpa only [neckPoint, coe_nonnegPart, neckTransfer_indicator Set.Ioi_subset_Ici_self] using
    (eq_of_mem_neckGraph ha hp).symm

omit hs in
private theorem analyticAt_neckPoint {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {g : X → ℂ} {h : X → supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)} {x : X}
    (hg : AnalyticAt ℂ g x) (hgx : ‖g x‖ < 1) (hh : AnalyticAt ℂ h x) :
    AnalyticAt ℂ (fun y ↦ neckPoint (g y) (h y)) x := by
  have hT : AnalyticAt ℂ (fun y ↦ (neckTransfer (g y) : CircleSobolev s ℂ →L[ℂ] _)) x :=
    (analyticOnNhd_neckTransfer (g x) (mem_ball_zero_iff.2 hgx)).comp hg
  have hι (k : X → supported s ℂ (Set.Ici 0)) (hk : AnalyticAt ℂ k x) :
      AnalyticAt ℂ (fun y ↦ (k y : CircleSobolev s ℂ)) x :=
    ((supported s ℂ (Set.Ici 0)).subtypeL.analyticAt _).comp hk
  have happ (k : X → supported s ℂ (Set.Ici 0)) (hk : AnalyticAt ℂ k x) :
      AnalyticAt ℂ (fun y ↦ neckTransfer (g y) (k y : CircleSobolev s ℂ)) x := by
    simpa [Function.comp_def] using
      ((ContinuousLinearMap.apply ℂ (CircleSobolev s ℂ)).analyticAt_bilinear _).comp
        ((hι k hk).prod hT)
  have h₁ : AnalyticAt ℂ (fun y ↦ (h y).1) x := analyticAt_fst.comp hh
  have h₂ : AnalyticAt ℂ (fun y ↦ (h y).2) x := analyticAt_snd.comp hh
  exact ((hι _ h₁).sub (happ _ h₂)).prod ((hι _ h₂).sub (happ _ h₁))

variable (s) in
/-- The nonlinear Hardy equation of the plumbing node, in the variables
`z = ((a, p, q), (P, Q))`: the difference between `(1 + p, 1 + q)` and the nonnegative parts of
`e^F` and `e^G`, for the element `(F, G)` of the neck graph with nonnegative parts `(P, Q)`, written
so that it vanishes at the origin. -/
private def hardyEquation
    (z : (ℂ × (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0))) ×
      (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0))) :
    supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0) :=
  (nonnegPart (nemytskii exp (neckPoint z.1.1 z.2).1) - z.1.2.1,
    nonnegPart (nemytskii exp (neckPoint z.1.1 z.2).2) - z.1.2.2)

private theorem analyticAt_nemytskii_exp (u : CircleSobolev s ℂ) :
    AnalyticAt ℂ (nemytskii exp) u := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  exact analyticOnNhd_nemytskii 1 isOpen_univ differentiable_exp.differentiableOn u
    fun _ ↦ Set.mem_univ _

private theorem analyticAt_hardyEquation : AnalyticAt ℂ (hardyEquation s) 0 := by
  have hN : AnalyticAt ℂ (fun z : (ℂ × (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0))) ×
      (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)) ↦ neckPoint z.1.1 z.2) 0 :=
    analyticAt_neckPoint (analyticAt_fst.comp analyticAt_fst) (by simp) analyticAt_snd
  exact (((nonnegPart.analyticAt _).comp ((analyticAt_nemytskii_exp _).comp
      (analyticAt_fst.comp hN))).sub
        (analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst))).prod
    (((nonnegPart.analyticAt _).comp ((analyticAt_nemytskii_exp _).comp
      (analyticAt_snd.comp hN))).sub
        (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)))

/-- The derivative of `F ↦ e^F` at `0`, followed by the nonnegative projection, is the identity on
the nonnegative Laurent subspace. -/
private theorem hasFDerivAt_nonnegPart_nemytskii_exp :
    HasFDerivAt
      (fun P : supported s ℂ (Set.Ici 0) ↦ nonnegPart (nemytskii exp (P : CircleSobolev s ℂ)))
      (ContinuousLinearMap.id ℂ _) 0 := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hN := hasFDerivAt_nemytskii 1 isOpen_univ differentiable_exp.differentiableOn
    (u := (supported s ℂ (Set.Ici 0)).subtypeL 0) fun _ ↦ Set.mem_univ _
  have h := nonnegPart.hasFDerivAt.comp (0 : supported s ℂ (Set.Ici 0))
    (hN.comp (0 : supported s ℂ (Set.Ici 0)) (supported s ℂ (Set.Ici 0)).subtypeL.hasFDerivAt)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun P ↦ ?_)
  rw [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    map_zero, Submodule.subtypeL_apply, Complex.deriv_exp, nemytskii_zero, exp_zero, ← one_def,
    ← mul_def, one_mul]
  exact Subtype.ext (indicator_eq_self_iff.2 P.2)

private theorem hasFDerivAt_hardyEquation_zero :
    HasFDerivAt (fun PQ ↦ hardyEquation s ((0 : ℂ × (supported s ℂ (Set.Ici 0) ×
      supported s ℂ (Set.Ici 0))), PQ)) (ContinuousLinearMap.id ℂ _) 0 := by
  have h := (HasFDerivAt.comp (f := Prod.fst) (0 : supported s ℂ (Set.Ici 0) ×
      supported s ℂ (Set.Ici 0)) hasFDerivAt_nonnegPart_nemytskii_exp hasFDerivAt_fst).prodMk
    (HasFDerivAt.comp (f := Prod.snd) (0 : supported s ℂ (Set.Ici 0) ×
      supported s ℂ (Set.Ici 0)) hasFDerivAt_nonnegPart_nemytskii_exp hasFDerivAt_snd)
  convert h using 1
  · funext PQ
    simp [hardyEquation, neckPoint, neckTransfer_zero]
  · ext <;> simp

private theorem isInvertible_fderiv_hardyEquation :
    (fderiv ℂ (hardyEquation s) 0 ∘L .inr ℂ (ℂ × (supported s ℂ (Set.Ici 0) ×
      supported s ℂ (Set.Ici 0))) (supported s ℂ (Set.Ici 0) ×
        supported s ℂ (Set.Ici 0))).IsInvertible := by
  have h := analyticAt_hardyEquation.differentiableAt.hasFDerivAt.comp
    (0 : supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0))
    (hasFDerivAt_prodMk_right (0 : ℂ × (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0))) 0)
  rw [h.unique hasFDerivAt_hardyEquation_zero, ← ContinuousLinearEquiv.coe_refl]
  exact ContinuousLinearMap.isInvertible_equiv

/-- The Hardy equation vanishes exactly when the neck-graph element with nonnegative parts `PQ`
solves the nonlinear Hardy problem with data `y = (a, p, q)`. -/
private theorem hardyEquation_eq_iff
    (y : ℂ × (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)))
    (PQ : supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)) :
    hardyEquation s (y, PQ) = hardyEquation s 0 ↔
      indicator (Set.Ici 0) (nemytskii exp (neckPoint y.1 PQ).1) = 1 + y.2.1 ∧
        indicator (Set.Ici 0) (nemytskii exp (neckPoint y.1 PQ).2) = 1 + y.2.2 := by
  have h0 : neckPoint (s := s) 0 0 = 0 := by simp [neckPoint]
  simp only [hardyEquation, Prod.fst_zero, Prod.snd_zero, h0, nemytskii_zero, exp_zero, ← one_def,
    sub_zero, Prod.ext_iff, Subtype.ext_iff, sub_eq_iff_eq_add, Submodule.coe_add, coe_nonnegPart,
    indicator_Ici_one]

/-- **The nonlinear Hardy graph theorem at a plumbing node.** For `s > 1/2` there are a
neighbourhood `W` of `0` in `H^s × H^s` and a map `ψ`, analytic at the origin with `ψ 0 = 0`, such
that for all data `y = (a, p, q)` near `0`, with `p` and `q` of nonnegative frequencies, `ψ y` is
the unique `(F, G) ∈ W` with

* `(F, G)` in the neck graph of the plumbing `xy = a`, and
* nonnegative parts of `e^F` and `e^G` equal to `1 + p` and `1 + q`.

In terms of the boundary maps `ξ = x e^F` and `η = y e^G`, the conditions say that `(ξ, η)` solves
the node equation `ξ(x) η(a / x) = b` with `b = a e^{F₀ + G₀}`
(`CircleSobolev.mul_exp_mul_mul_exp_eq_of_mem_neckGraph`), and that the positive Fourier
coefficients of `ξ` and `η` are those of `x (1 + p)` and `y (1 + q)`. So the solution, its
nonpositive coefficients and `b` depend holomorphically on `a` and on these positive coefficients,
also at the node `a = 0`. -/
theorem exists_analyticAt_hardyGraph :
    ∃ ψ : ℂ × (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)) →
        CircleSobolev s ℂ × CircleSobolev s ℂ,
      ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧
        ∃ W ∈ 𝓝 (0 : CircleSobolev s ℂ × CircleSobolev s ℂ), ∀ᶠ y in 𝓝 0, ψ y ∈ W ∧
          ∀ p ∈ W, (p ∈ neckGraph s ℂ y.1 ∧
            indicator (Set.Ici 0) (nemytskii exp p.1) = 1 + y.2.1 ∧
            indicator (Set.Ici 0) (nemytskii exp p.2) = 1 + y.2.2) ↔ p = ψ y := by
  have hcd : ContDiffAt ℂ ω (hardyEquation s) 0 := analyticAt_hardyEquation.contDiffAt
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set ψ₀ := hcd.implicitFunction pn isInvertible_fderiv_hardyEquation
  have h₀ : ψ₀ 0 = 0 := hcd.implicitFunction_apply_self pn isInvertible_fderiv_hardyEquation
  have hψ₀ : AnalyticAt ℂ ψ₀ 0 :=
    (hcd.contDiffAt_implicitFunction pn isInvertible_fderiv_hardyEquation).analyticAt
  have hsol := hcd.eventually_apply_implicitFunction pn isInvertible_fderiv_hardyEquation
  have huniq := hcd.eventually_apply_eq_iff_implicitFunction pn isInvertible_fderiv_hardyEquation
  simp only [Prod.fst_zero] at hsol
  have huniq' : ∀ᶠ v in 𝓝 (0 : ℂ × (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0))) ×ˢ
      𝓝 (0 : supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)),
      hardyEquation s v = hardyEquation s 0 ↔ ψ₀ v.1 = v.2 := by
    rw [← nhds_prod_eq]
    exact huniq
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 huniq'
  have hW : (fun p : CircleSobolev s ℂ × CircleSobolev s ℂ ↦ (nonnegPart p.1, nonnegPart p.2)) ⁻¹'
      {x | pb x} ∈ 𝓝 0 :=
    ((nonnegPart.continuous.comp continuous_fst).prodMk
      (nonnegPart.continuous.comp continuous_snd)).tendsto' 0 0 (by simp) hpb
  have hpb' : ∀ᶠ y in 𝓝 0, pb (ψ₀ y) := hψ₀.continuousAt.eventually (h₀ ▸ hpb)
  have hlt : ∀ᶠ y : ℂ × (supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)) in 𝓝 0,
      ‖y.1‖ < 1 :=
    continuous_fst.norm.continuousAt.eventually_lt continuousAt_const (by simp)
  refine ⟨fun y ↦ neckPoint y.1 (ψ₀ y), by simp [h₀, neckPoint],
    analyticAt_neckPoint analyticAt_fst (by simp) hψ₀, _, hW, ?_⟩
  filter_upwards [hpa, hsol, hpb', hlt] with y hya hys hyb hy1
  have hnn (PQ : supported s ℂ (Set.Ici 0) × supported s ℂ (Set.Ici 0)) :
      (nonnegPart (neckPoint y.1 PQ).1, nonnegPart (neckPoint y.1 PQ).2) = PQ :=
    Prod.ext (nonnegPart_sub_neckTransfer _ _ _) (nonnegPart_sub_neckTransfer _ _ _)
  refine ⟨by simpa only [Set.mem_preimage, Set.mem_ofPred_eq, hnn] using hyb,
    fun p hp ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨hpg, h₁, h₂⟩
    have he := neckPoint_nonnegPart hy1.le hpg
    have hf : hardyEquation s (y, (nonnegPart p.1, nonnegPart p.2)) = hardyEquation s 0 :=
      (hardyEquation_eq_iff y _).2 (by rw [he]; exact ⟨h₁, h₂⟩)
    have hψ : ψ₀ y = (nonnegPart p.1, nonnegPart p.2) := (hab hya hp).1 hf
    simp only [hψ, he]
  · rintro rfl
    exact ⟨neckPoint_mem_neckGraph hy1.le _, (hardyEquation_eq_iff y _).1 hys⟩

end HardyGraph

end CircleSobolev

end TauCeti
