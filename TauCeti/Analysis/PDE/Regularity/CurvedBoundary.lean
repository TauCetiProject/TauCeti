/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.FlatBoundary
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.Flattening
import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables.Bounds
import TauCeti.Analysis.Sobolev.Wkp.Gluing
import TauCeti.Topology.Instances.Matrix

/-!
# `H²` and `H³` regularity up to a curved boundary

Let `Ω ⊆ ℝⁿ` be open, let `a` be uniformly elliptic and Lipschitz, let `b, c ∈ L∞(Ω)` and
`f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`.

This file proves that `u` is `H²` up to every part of `∂Ω` that is a `C²` graph and on which `u`
vanishes (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_contDiff_graph`), and
hence that the weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem on a bounded open set with `C²`
boundary lies in `H²(Ω)` (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph`).
A `C²` boundary is described as in Evans, Appendix C.1: near each boundary point, in rigid
coordinates `e : ℝⁿ ≃ ℝ × E` centred there, `Ω` is the region above the graph of a `C²` function
`γ : E → ℝ` with `γ 0 = 0`, inside a normal cylinder. The regularity comes with the global
estimate `‖u‖_{H²(Ω)} ≤ C (‖u‖_{L²(Ω)} + ‖f‖_{L²(Ω)})`
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_and_norm_le_norm_value_of_contDiff_graph`),
with `C` depending only on `Ω` and the coefficients.

One derivative more is available when the boundary and the data allow it. If the boundary portion
is the graph of a smooth function, the entries of `a` are smooth up to it and `u` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = F` with `F ∈ H¹(Ω)`, then `u` is `H³` up to that portion
(`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiff_graph`), and the
weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem on a bounded open set with smooth boundary lies
in `H³(Ω)` (`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_contDiff_graph`). This is
Evans, §6.3.2, Theorem 5, for `m = 1` and `b = c = 0`. Smoothness, rather than finitely many
derivatives, of the boundary and of `a` is what the flat model
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_halfSpace` asks of the
transformed coefficient.

## The argument

The classical proof (Evans, §6.3.2, Theorem 4) flattens the boundary.

* **Flattening.** The shear `Ψ(t, y) = (t - γ y, y)` and its inverse `Φ`, conjugated by `e`, are
  changes of variables of order two with Jacobian one
  (`TauCeti.exists_isChangeOfVariables_of_contDiff`), and `Φ` maps the half-space
  `{0 < (e x).fst}` near the boundary point onto `Ω` near it, fixing the boundary point
  (`TauCeti.exists_isChangeOfVariables_halfSpace_of_contDiff_graph`).
* **The transformed equation.** The function `u ∘ Φ` is a weak solution of an equation of the same
  form on the flat side (`TauCeti.PDE.energyFormH1_compL_eq_setIntegral`), whose principal
  coefficient is again uniformly elliptic (`TauCeti.PDE.UniformlyEllipticOn.pullbackPrincipal`) and
  Lipschitz (`TauCeti.PDE.exists_holderOnWith_matrixBilinearForm_pullbackPrincipal`), since `DΦ`
  is `C¹` and so Lipschitz on compact convex sets, and whose lower-order terms and right-hand side
  stay bounded and square integrable. Zero boundary values are carried along by cutting off
  near the image of the support and pulling back.
* **The flat case.** Near the flat boundary, `u ∘ Φ` is `H²`
  (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_halfSpace`), and
  precomposing with `Ψ`, a change of variables of order two (`TauCeti.Wkp.compL`), carries this
  back to `u` near the boundary point (`TauCeti.Wkp.exists_value_eq_value_restrictL_of_w1pCompL`).
* **Gluing.** On a bounded domain finitely many such neighbourhoods, together with balls inside
  `Ω` where interior regularity applies
  (`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`), cover
  the compact closure, and the local second derivatives glue
  (`TauCeti.Wkp.exists_value_ae_eq_of_isCompact`).
* **The estimate.** The pairs `(u, f)` of a weak solution `u ∈ H¹₀(Ω)` of `L u = f` and its
  datum `f ∈ L²(Ω)` form a closed subspace of `H¹(Ω) × L²(Ω)` (`TauCeti.PDE.dirichletGraph`,
  `TauCeti.PDE.isClosed_dirichletGraph`), and so do the pairs `(w, f)` with
  `w ∈ W^{2,2}(Ω)` whose first-order part solves `L u = f`. Forgetting the second derivatives maps
  the second space continuously onto the first, by the regularity theorem, so the open mapping
  theorem (`ContinuousLinearMap.exists_preimage_norm_le`) bounds `‖w‖_{W^{2,2}}` by
  `C (‖u‖_{H¹} + ‖f‖_{L²})`. Gårding's inequality applied to the equation tested against `u`
  bounds `‖u‖_{H¹}` by `‖u‖_{L²}` and `‖f‖_{L²}`
  (`TauCeti.PDE.UniformlyEllipticOn.norm_le_of_isWeakSolutionDirichlet_of_norm_le`). The
  constant is not explicit; as in Evans's theorem, it depends only on `Ω` and the coefficients.
* **One more derivative.** For a smooth boundary the flattening and its inverse are smooth and
  are changes of variables of order three. The transformed principal coefficient is then smooth
  (`TauCeti.PDE.contDiffOn_pullbackPrincipal_apply`), the transformed right-hand side is
  `F ∘ Φ ∈ H¹` (`TauCeti.PDE.energyFormH1_w1pCompL_restrictL_eq_setIntegral`), and the flat `H³`
  theorem applies to `u ∘ Φ`; precomposing with `Ψ` in `W^{3,2}` carries this back. Interior
  points are covered by interior `H³` regularity
  (`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiffOn`), and the local
  third derivatives glue.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_contDiff_graph`: local `H²`
  regularity near a `C²` boundary portion on which the solution vanishes.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph`: `H²` regularity of
  the Dirichlet problem on a bounded open set with `C²` boundary.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_and_norm_le_of_contDiff_graph`: the
  global `H²` estimate in terms of `‖u‖_{H¹}` and `‖f‖_{L²}`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_and_norm_le_norm_value_of_contDiff_graph`:
  the global `H²` estimate in terms of `‖u‖_{L²}` and `‖f‖_{L²}` (Evans, §6.3.2, Theorem 4).
* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiff_graph`: local `H³`
  regularity near a smooth boundary portion on which the solution vanishes.
* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_of_contDiff_graph`: `H³` regularity of
  the Dirichlet problem on a bounded open set with smooth boundary (Evans, §6.3.2, Theorem 5, for
  `m = 1` and `b = c = 0`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.2, Theorems 4 and 5, and
  Appendix C.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.12.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]

section Local

variable [DecidableEq ι] {Omega W : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {lam Lam : ℝ} {K : ℝ≥0} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
/-- **Transferring local regularity across a straightened boundary portion.** Let `Φ` and `Ψ` be
mutually inverse continuous maps which are changes of variables of order `k ≥ 1` between open sets
`U'` and `U`, with Jacobian determinants at least one in absolute value, such that `Φ` maps the
part of `U'` in an open set `H` onto `Ω ∩ U`. Let `y₀ ∈ U'` with `Φ y₀ ∈ W`, and let `u ∈ H¹(Ω)`
vanish on `∂Ω ∩ W`. Suppose that for every small ball `B = B(y₀, r)`, on `Ω' = H ∩ B` the
function `u ∘ Φ`, which vanishes on `∂Ω' ∩ B`, is `W^{k,2}` on `Ω' ∩ V''` for every open `V''`
with compact closure in `B`. Then `u` is `W^{k,2}` on `Ω ∩ V` for an open neighbourhood `V` of
`Φ y₀`. -/
private theorem exists_value_eq_value_restrictL_of_isChangeOfVariables_of_flat {k : ℕ}
    (hk : 1 ≤ k) {U' U H : Opens (EuclideanSpace ℝ ι)}
    {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L : ℝ}
    (hΦ : Wkp.IsChangeOfVariables k U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables k U U' Ψ L 1)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y) (hΦc : Continuous Φ) (hΨc : Continuous Ψ)
    (himage : Φ '' ((H : Set (EuclideanSpace ℝ ι)) ∩ U') = (Omega : Set (EuclideanSpace ℝ ι)) ∩ U)
    {y₀ : EuclideanSpace ℝ ι} (hy₀ : y₀ ∈ (U' : Set (EuclideanSpace ℝ ι))) (hy₀W : Φ y₀ ∈ W)
    {u : W1p mu Omega 2}
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x)
    (hflat : ∀ r > 0, closedBall y₀ r ⊆ (U' : Set (EuclideanSpace ℝ ι)) ∩ Φ ⁻¹' W →
      ∀ Ω' D : Opens (EuclideanSpace ℝ ι),
      (Ω' : Set (EuclideanSpace ℝ ι)) = (H : Set (EuclideanSpace ℝ ι)) ∩ ball y₀ r →
      ∀ (hD : D ≤ Omega) (hΦ' : Wkp.IsChangeOfVariables 1 Ω' D Φ L 1),
      Wkp.IsChangeOfVariables 1 D Ω' Ψ L 1 →
      MapsTo Φ Ω' ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W) →
      (∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ ball y₀ r → ∃ v : W1p0 mu Ω' 2,
          W1p.value (v : W1p mu Ω' 2) =ᵐ[mu.restrict Ω'] fun x =>
            ψ x * W1p.value (hΦ'.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hD u)) x) →
      ∀ V'' : Opens (EuclideanSpace ℝ ι), IsCompact (closure (V'' : Set (EuclideanSpace ℝ ι))) →
        closure (V'' : Set (EuclideanSpace ℝ ι)) ⊆ ball y₀ r →
        ∃ w : Wkp mu (Ω' ⊓ V'') 2 k, Wkp.value k w = W1p.value
          (W1p.restrictL inf_le_left (hΦ'.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hD u)))) :
    ∃ V : Opens (EuclideanSpace ℝ ι), Φ y₀ ∈ V ∧
      ∃ w : Wkp mu (Omega ⊓ V) 2 k, Wkp.value k w = W1p.value (W1p.restrictL inf_le_left u) := by
  -- A closed ball about `y₀` in `U'` on which `Φ` lands in `W`.
  obtain ⟨r, hr, hrB⟩ : ∃ r > 0, closedBall y₀ r ⊆ (U' : Set _) ∩ Φ ⁻¹' W :=
    nhds_basis_closedBall.mem_iff.1 ((U'.isOpen.inter (W.isOpen.preimage hΦc)).mem_nhds
      ⟨hy₀, hy₀W⟩)
  -- The flat domain `Ω' = H ∩ B(y₀, r)` and the curved one `D = Ω ∩ O`, `O = U ∩ Ψ⁻¹ B(y₀, r)`.
  let B'' : Opens (EuclideanSpace ℝ ι) := ⟨ball y₀ r, isOpen_ball⟩
  let Ω' : Opens (EuclideanSpace ℝ ι) := H ⊓ B''
  let O : Opens (EuclideanSpace ℝ ι) := ⟨U ∩ Ψ ⁻¹' ball y₀ r,
    hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩
  let D : Opens (EuclideanSpace ℝ ι) := Omega ⊓ O
  have hBU' : (B'' : Set (EuclideanSpace ℝ ι)) ⊆ U' :=
    ball_subset_closedBall.trans (hrB.trans inter_subset_left)
  have hOW : (O : Set (EuclideanSpace ℝ ι)) ⊆ W := fun y hy => by
    simpa [hΦΨ] using (hrB (ball_subset_closedBall hy.2)).2
  have hΦmaps : MapsTo Φ Ω' D := fun x hx => by
    have hmem : Φ x ∈ (Omega : Set _) ∩ U := himage ▸ mem_image_of_mem _ ⟨hx.1, hBU' hx.2⟩
    exact ⟨hmem.1, hmem.2, by rw [mem_preimage, hΨΦ]; exact hx.2⟩
  have hΨmaps : MapsTo Ψ D Ω' := fun y hy => by
    have hy' : y ∈ Φ '' ((H : Set (EuclideanSpace ℝ ι)) ∩ U') := by
      rw [himage]; exact ⟨hy.1, hy.2.1⟩
    obtain ⟨x, ⟨hxH, -⟩, rfl⟩ := hy'
    exact ⟨by rw [hΨΦ]; exact hxH, hy.2.2⟩
  have hDU : D ≤ U := fun y hy => hy.2.1
  have hΦ' := (hΦ.mono_set (fun x hx => hBU' hx.2 : Ω' ≤ U') hΦmaps).mono hk
  -- `u ∘ Φ` vanishes on `∂Ω' ∩ B(y₀, r)`.
  have hu0' := hΦ'.exists_w1p0_value_ae_eq_mul_value_w1pCompL ENNReal.ofNat_ne_top
    hΦc.continuousOn hΨc.continuousOn hΨmaps (fun x _ => hΨΦ x)
    (fun x hx => ⟨hΦ.mapsTo (hBU' hx), by rw [mem_preimage, hΨΦ]; exact hx⟩ : MapsTo Φ B'' O)
    (fun χ hχ hχc hχs => hu0 χ hχ hχc (hχs.trans hOW))
  -- Regularity near the flat boundary, on `Ω' ∩ B(y₀, r / 2)`.
  let V'' : Opens (EuclideanSpace ℝ ι) := ⟨ball y₀ (r / 2), isOpen_ball⟩
  have hV''c : closure (V'' : Set (EuclideanSpace ℝ ι)) ⊆ closedBall y₀ (r / 2) :=
    closure_ball_subset_closedBall
  obtain ⟨w'', hw''⟩ := hflat r hr hrB Ω' D rfl inf_le_left hΦ'
    ((hΨ.mono_set hDU hΨmaps).mono hk) (fun x hx => ⟨(hΦmaps hx).1, hOW (hΦmaps hx).2⟩) hu0' V''
    ((isCompact_closedBall y₀ (r / 2)).of_isClosed_subset isClosed_closure hV''c)
    (hV''c.trans (closedBall_subset_ball (half_lt_self hr)))
  -- Push forward to `Ω ∩ V` with `V = U ∩ Ψ⁻¹(B(y₀, r / 2))`.
  let V : Opens (EuclideanSpace ℝ ι) := ⟨U ∩ Ψ ⁻¹' ball y₀ (r / 2),
    hΨc.continuousOn.isOpen_inter_preimage U.isOpen isOpen_ball⟩
  have hVD' : ((Omega ⊓ V : Opens _) : Set (EuclideanSpace ℝ ι)) ⊆ D := fun y hy => by
    simp only [D, O, V, Opens.coe_inf, Opens.coe_mk, mem_inter_iff, mem_preimage] at hy ⊢
    exact ⟨hy.1, hy.2.1, ball_subset_ball (half_le_self hr.le) hy.2.2⟩
  have hVD : Omega ⊓ V ≤ D := SetLike.coe_subset_coe.mp hVD'
  exact ⟨V, ⟨hΦ.mapsTo hy₀, by rw [mem_preimage, hΨΦ]; exact mem_ball_self (half_pos hr)⟩,
    Wkp.exists_value_eq_value_restrictL_of_w1pCompL ENNReal.ofNat_ne_top inf_le_left hVD hΦ'
      (hΨ.mono_set (hVD.trans hDU) fun y hy => ⟨hΨmaps (hVD' hy), hy.2.2⟩) (fun y _ => hΦΨ y)
      hw''⟩

/-- **Local `H²` regularity near a straightened boundary portion.** Let `Φ` and `Ψ` be mutually
inverse changes of variables of order two between open sets `U'` and `U`, with Jacobian
determinants at least one in absolute value, such that `Φ` maps the part of `U'` in the half-space
`H = {c₀ < ⟪x, ν⟫}` onto `Ω ∩ U`. Let `y₀ ∈ U'` lie in the closure of `H`, with `Φ y₀ ∈ W`. Under
the hypotheses of `UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_contDiff_graph`, `u` is
`H²` on `Ω ∩ V` for an open neighbourhood `V` of `Φ y₀`. -/
private theorem exists_lowerOrder_eq_restrictL_of_isChangeOfVariables
    {U' U : Opens (EuclideanSpace ℝ ι)} {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L : ℝ}
    (hΦ : Wkp.IsChangeOfVariables 2 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 2 U U' Ψ L 1)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y) (hΦc : Continuous Φ) (hΨc : Continuous Ψ)
    {ν : EuclideanSpace ℝ ι} (hν : ν ≠ 0) {c₀ : ℝ}
    (himage : Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') = (Omega : Set (EuclideanSpace ℝ ι)) ∩ U)
    {y₀ : EuclideanSpace ℝ ι} (hy₀ : y₀ ∈ (U' : Set (EuclideanSpace ℝ ι)))
    (hy₀H : y₀ ∈ closure {x | c₀ < ⟪x, ν⟫_ℝ}) (hy₀W : Φ y₀ ∈ W)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x))
      ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x) :
    ∃ V : Opens (EuclideanSpace ℝ ι), Φ y₀ ∈ V ∧
      ∃ w : Wkp mu (Omega ⊓ V) 2 2, Wkp.lowerOrder 1 w = W1p.restrictL inf_le_left u := by
  -- `ι` is nonempty, since `ν ≠ 0`.
  have : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    exact hν (by ext i; exact isEmptyElim i)
  let H : Opens (EuclideanSpace ℝ ι) := ⟨{x | c₀ < ⟪x, ν⟫_ℝ}, isOpen_lt continuous_const
    (continuous_id.inner continuous_const)⟩
  obtain ⟨V, hV, w, hw⟩ := exists_value_eq_value_restrictL_of_isChangeOfVariables_of_flat (H := H)
    one_le_two hΦ hΨ hΨΦ hΦΨ hΦc hΨc himage hy₀ hy₀W hu0
    fun r hr hrB Ω' D hΩ' hD hΦ' hΨ' hΦmaps hu0' V'' hV hVU => by
      -- On the flat side, `u ∘ Φ` solves an equation of the same form, with uniformly elliptic
      -- and Lipschitz principal coefficient.
      obtain ⟨hb', hc', f', hu₁⟩ := exists_forall_energyFormH1_compL_restrictL_eq (mu := mu) hD
        hΦ' hΨ' (fun x _ => hΨΦ x) (fun y _ => hΦΨ y) hb hc hu
      obtain ⟨z, hzH, hz⟩ := Metric.mem_closure_iff.1 hy₀H r hr
      obtain ⟨lam', Lam', K', hellip, hK'⟩ :=
        exists_uniformlyEllipticOn_and_lipschitzOnWith_pullbackPrincipal (hΦ.mono one_le_two) hΨ
          (fun x _ => hΨΦ x) (fun y _ => hΦΨ y) (isCompact_closedBall y₀ r)
          (convex_closedBall y₀ r) (hrB.trans inter_subset_left)
          (fun x (hx : x ∈ (Ω' : Set (EuclideanSpace ℝ ι)) ∩ ball y₀ r) =>
            ball_subset_closedBall hx.2)
          ⟨z, by rw [hΩ']; exact ⟨hzH, mem_ball_comm.1 hz⟩, mem_ball_comm.1 hz⟩
          (fun x hx => hΦmaps hx.1) ha hK
      -- `H²` regularity near the flat boundary.
      obtain ⟨w'', hw''⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_halfSpace
        (H := H) (U := ⟨ball y₀ r, isOpen_ball⟩) hν (fun _ => Iff.rfl)
        (by rw [hΩ', inter_assoc]; exact congrArg _ (inter_self _)) hellip hK' hb' hc' hu₁ hu0' hV
        hVU
      exact ⟨w'', by rw [← Wkp.value_lowerOrder_one, hw'']⟩
  exact ⟨V, hV, w, W1p.ext_value (by rw [Wkp.value_lowerOrder_one, hw])⟩

/-- **Local `H²` regularity near a `C²` boundary portion.** Let `Ω` be open, and suppose that in
rigid coordinates `e` centred at `x₀ = e⁻¹ 0`, inside the normal cylinder of half-height `h₀` and
radius `r₀`, `Ω` is the region above the graph of a `C²` function `γ` with `γ 0 = 0`. Let `W` be
an open neighbourhood of `x₀`, let `a` be uniformly elliptic on `Ω ∩ W`, with `x ↦ a(x)` Lipschitz
on `Ω ∩ W` in the operator norm of its bilinear forms, let `b, c ∈ L∞(Ω)`, and let `u ∈ H¹(Ω)` be
a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, with `f ∈ L²(Ω)`,

such that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `W`: `u` vanishes on
`∂Ω ∩ W`. Then there is an open neighbourhood `V` of `x₀` such that the restriction of `u` to
`Ω ∩ V` is the first-order part of an element of `W^{2,2}(Ω ∩ V)`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_contDiff_graph
    {e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {h₀ r₀ : ℝ} (hh₀ : 0 < h₀)
    (hr₀ : 0 < r₀) (hγ0 : γ 0 = 0) (hγ : ContDiff ℝ 2 γ)
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst))
    (hW : e.symm 0 ∈ W)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x))
      ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x) :
    ∃ V : Opens (EuclideanSpace ℝ ι), e.symm 0 ∈ V ∧
      ∃ w : Wkp mu (Omega ⊓ V) 2 2, Wkp.lowerOrder 1 w = W1p.restrictL inf_le_left u := by
  -- Flatten the boundary: `Φ` maps the flat side `U'` into `U`, inverse to `Ψ`, and fixes `x₀`.
  obtain ⟨U', U, L, ν, c₀, hΦ, hΨ, hν, himage, hx₀U', hx₀H, hΦx₀⟩ :=
    exists_isChangeOfVariables_halfSpace_of_contDiff_graph one_le_two hh₀ hr₀ hγ0 hγ hgraph
  have h := exists_lowerOrder_eq_restrictL_of_isChangeOfVariables hΦ hΨ
    (fun x => by simp [-graphFlattening_apply, -graphFlattening_symm_apply])
    (fun y => by simp [-graphFlattening_apply, -graphFlattening_symm_apply])
    (e.symm.continuous.comp ((graphFlattening γ hγ.continuous).symm.continuous.comp e.continuous))
    (e.symm.continuous.comp ((graphFlattening γ hγ.continuous).continuous.comp e.continuous)) hν
    himage hx₀U' hx₀H (by rwa [hΦx₀]) ha hK hb hc hu hu0
  rwa [hΦx₀] at h

/-- **`H²` regularity up to a `C²` boundary.** Let `Ω` be a bounded open set with `C²` boundary:
at every boundary point `x`, in rigid coordinates `e` with `e x = 0`, inside a normal cylinder,
`Ω` is the region above the graph of a `C²` function `γ` with `γ 0 = 0`. Let `a` be uniformly
elliptic on `Ω` and Lipschitz on `Ω` in the operator norm of its bilinear forms, let
`b, c ∈ L∞(Ω)`, and let `u ∈ H¹₀(Ω)` be a weak solution of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, `u = 0` on `∂Ω`, with `f ∈ L²(Ω)`.

Then `u ∈ H²(Ω)`: it is the first-order part of an element of `W^{2,2}(Ω)`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hbdry : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)),
      ∃ (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 2 γ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst))
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2} (hu0 : u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ w : Wkp mu Omega 2 2, Wkp.lowerOrder 1 w = u := by
  -- Every point of `closure Ω` has a neighbourhood `V` with `u ∈ H²(Ω ∩ V)`.
  have hloc (x : EuclideanSpace ℝ ι) (hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ ι))) :
      ∃ V : Opens (EuclideanSpace ℝ ι), x ∈ V ∧
        ∃ w : Wkp mu (Omega ⊓ V) 2 2, Wkp.lowerOrder 1 w = W1p.restrictL inf_le_left u := by
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · -- Interior points, by interior regularity on a small ball.
      obtain ⟨ρ, hρ, hρΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hxΩ)
      have hcl : closure ((Omega ⊓ ⟨ball x ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) :
          Set (EuclideanSpace ℝ ι)) ⊆ closedBall x ρ :=
        (closure_mono inter_subset_right).trans closure_ball_subset_closedBall
      exact ⟨⟨ball x ρ, isOpen_ball⟩, mem_ball_self hρ,
        ha.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn
          (fun _ _ => ⟨K, _, self_mem_nhdsWithin, hK⟩) hb hc hu
          ((isCompact_closedBall x ρ).of_isClosed_subset isClosed_closure hcl) (hcl.trans hρΩ)⟩
    · -- Boundary points, by flattening the boundary.
      obtain ⟨e, γ, h₀, r₀, hex, hh₀, hr₀, hγ0, hγ, hgraph⟩ :=
        hbdry x ⟨hx, by rwa [Omega.isOpen.interior_eq]⟩
      have hx₀ : e.symm 0 = x := by rw [← hex, e.symm_apply_apply]
      obtain ⟨V, hV, hw⟩ :=
        (ha.mono_set inter_subset_left).exists_lowerOrder_eq_restrictL_of_contDiff_graph
        (W := ⊤) hh₀ hr₀ hγ0 hγ hgraph trivial (hK.mono inter_subset_left) hb hc hu
        fun ψ hψ hψc _ => W1p.exists_w1p0_value_ae_eq_mul_of_mem_w1p0Submodule hψ hψc hu0
      exact ⟨V, hx₀ ▸ hV, hw⟩
  -- Finitely many such neighbourhoods cover the compact set `closure Ω`; glue.
  obtain ⟨v, hv⟩ := Wkp.exists_value_ae_eq_of_isCompact hΩ.isCompact_closure subset_closure 2
    (u := W1p.value u) fun x hx => by
      obtain ⟨V, hxV, w, hw⟩ := hloc x hx
      refine ⟨V, hxV, w, ?_⟩
      rw [← Wkp.value_lowerOrder_one, hw]
      exact W1p.value_restrictL_ae inf_le_left u
  exact ⟨v, W1p.ext_value (Lp.ext (by rw [Wkp.value_lowerOrder_one]; exact hv))⟩

end Local

/-! ### The global `H²` estimate -/

section Estimate

variable {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {lam Lam : ℝ} {K : ℝ≥0} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Shortcut normed group instance on `W^{1,2}(Ω)`. Without it, the normed structure of a subspace
of `W^{1,2}(Ω) × L²(Ω)` and its module structure are found along paths that do not unify. -/
private noncomputable local instance instNormedAddCommGroupW1pTwo :
    NormedAddCommGroup (W1p mu Omega 2) := inferInstance

/-- Shortcut normed space instance on `W^{1,2}(Ω)`, for the same reason. -/
private noncomputable local instance instNormedSpaceW1pTwo :
    NormedSpace ℝ (W1p mu Omega 2) := inferInstance

variable [DecidableEq ι]

/-- **The global `H²` estimate up to a `C²` boundary, in terms of the `H¹` norm.** Under the
hypotheses of `UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph`, there is a constant
`C` such that every weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem for `L u = f` with
`f ∈ L²(Ω)` is the first-order part of some `w ∈ W^{2,2}(Ω)` with

`‖w‖_{W^{2,2}(Ω)} ≤ C (‖u‖_{H¹(Ω)} + ‖f‖_{L²(Ω)})`.

The element `w` is unique (`TauCeti.Wkp.ext_lowerOrder`). The constant depends on `Ω` and on the
coefficients, but not on `u` or `f`. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_and_norm_le_of_contDiff_graph
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hbdry : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)),
      ∃ (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 2 γ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst))
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega)) :
    ∃ C : ℝ, ∀ {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2},
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ∃ w : Wkp mu Omega 2 2, Wkp.lowerOrder 1 w = u ∧ ‖w‖ ≤ C * (‖u‖ + ‖f‖) := by
  -- The coefficients are essentially bounded, so the energy form is a continuous bilinear form.
  have hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega) :=
    memLp_energyIntegrand_of_memLp_top ha.upper_nonneg
      ((continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
        Omega.isOpen.measurableSet) (fun _ hx => ha.upper_bound hx) hb hc
  -- The map `(w, f) ↦ (w', f)`, where `w'` is the first-order part of `w`, from the closed
  -- subspace of solutions in `W^{2,2}(Ω) × L²(Ω)` onto the graph of the Dirichlet problem.
  let X := dirichletGraph hcoeff
  let P : Wkp mu Omega 2 2 × Lp ℝ 2 (mu.restrict Omega) →L[ℝ]
      W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega) :=
    (Wkp.lowerOrderL 1).prodMap (ContinuousLinearMap.id ℝ _)
  have hP : ∀ q, P q = (Wkp.lowerOrder 1 q.1, q.2) := fun q =>
    Prod.ext (Wkp.lowerOrderL_apply 1 q.1) rfl
  let S := X.comap P.toLinearMap
  have hX : IsClosed (X : Set (W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega))) :=
    isClosed_dirichletGraph hcoeff
  have : CompleteSpace X := hX.completeSpace_coe
  have : CompleteSpace S := (hX.preimage P.continuous).completeSpace_coe
  let π : S →L[ℝ] X := (P.comp S.subtypeL).codRestrict X fun q => q.property
  -- `π` has the values of `P` (`ContinuousLinearMap.coe_codRestrict_apply`).
  have hπ : ∀ q : S, (π q : W1p mu Omega 2 × Lp ℝ 2 (mu.restrict Omega)) = P q := fun _ => rfl
  -- By the qualitative regularity theorem it is surjective, so the open mapping theorem bounds
  -- a preimage.
  have hsurj : Function.Surjective π := by
    rintro ⟨⟨u, f⟩, hX⟩
    have hu0 := ((mem_dirichletGraph_iff hcoeff).1 hX).1
    obtain ⟨w, hw⟩ := ha.exists_lowerOrder_eq_of_contDiff_graph hΩ hbdry hK hb hc hu0
      ((isWeakSolutionDirichlet_iff f ⟨u, hu0⟩).1 ((mk_mem_dirichletGraph_iff hcoeff _ f).1 hX))
    have hPwf : P (w, f) = (u, f) := (hP (w, f)).trans (Prod.ext hw rfl)
    have hmem : P (w, f) ∈ X := hPwf ▸ hX
    exact ⟨⟨(w, f), Submodule.mem_comap.2 hmem⟩, Subtype.ext ((hπ _).trans hPwf)⟩
  obtain ⟨C, hC, hpre⟩ := π.exists_preimage_norm_le hsurj
  refine ⟨C, fun {f u} hu0 hu => ?_⟩
  obtain ⟨⟨⟨w, g⟩, hq⟩, hwg, hnorm⟩ :=
    hpre ⟨(u, f), (mk_mem_dirichletGraph_iff hcoeff ⟨u, hu0⟩ f).2
      ((isWeakSolutionDirichlet_iff f _).2 hu)⟩
  have hw : P (w, g) = (u, f) := (hπ _).symm.trans (congrArg Subtype.val hwg)
  rw [hP] at hw
  refine ⟨w, (Prod.ext_iff.1 hw).1, ?_⟩
  calc ‖w‖ ≤ ‖((w, g) : Wkp mu Omega 2 2 × Lp ℝ 2 (mu.restrict Omega))‖ :=
        norm_fst_le ((w, g) : Wkp mu Omega 2 2 × Lp ℝ 2 (mu.restrict Omega))
    _ ≤ C * max ‖u‖ ‖f‖ := hnorm
    _ ≤ C * (‖u‖ + ‖f‖) := by
      gcongr
      exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

/-- **The global `H²` estimate up to a `C²` boundary** (Evans, §6.3.2, Theorem 4). Let `Ω` be a
bounded open set with `C²` boundary, described as in
`UniformlyEllipticOn.exists_lowerOrder_eq_of_contDiff_graph`, let `a` be uniformly elliptic and
Lipschitz on `Ω`, and let `b, c` be essentially bounded on `Ω`. There is a
constant `C` such that every weak solution `u ∈ H¹₀(Ω)` of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟨b, ∇u⟩ + c u = f` in `Ω`, `u = 0` on `∂Ω`, with `f ∈ L²(Ω)`,

is the first-order part of some `w ∈ W^{2,2}(Ω)` with

`‖w‖_{W^{2,2}(Ω)} ≤ C (‖u‖_{L²(Ω)} + ‖f‖_{L²(Ω)})`.

The constant depends on `Ω` and on the coefficients, but not on `u` or `f`. No sign condition on
`c` and no smallness of `b` is assumed, so `u` need not be unique, and the `L²` norm of `u` cannot
be dropped from the right-hand side. -/
theorem UniformlyEllipticOn.exists_lowerOrder_eq_and_norm_le_norm_value_of_contDiff_graph
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hbdry : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)),
      ∃ (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 2 γ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst))
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) Omega)
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega)) :
    ∃ C : ℝ, ∀ {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2},
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      ∃ w : Wkp mu Omega 2 2, Wkp.lowerOrder 1 w = u ∧
        ‖w‖ ≤ C * (‖W1p.value u‖ + ‖f‖) := by
  obtain ⟨C, hC⟩ := ha.exists_lowerOrder_eq_and_norm_le_of_contDiff_graph hΩ hbdry hK hb hc
  -- The `L^∞` norms of `b` and `c` bound them almost everywhere on `Ω`.
  set beta := lpNorm b ⊤ (mu.restrict Omega)
  set gamma := lpNorm c ⊤ (mu.restrict Omega)
  have hlam : 0 < lam := ha.pos
  set κ := lam / 2 + |gamma| + beta ^ 2 / (2 * lam)
  refine ⟨max C 0 * (1 + 2 / lam + 2 * κ / lam), fun {f u} hu0 hu => ?_⟩
  obtain ⟨w, hw, hwle⟩ := hC hu0 hu
  refine ⟨w, hw, ?_⟩
  -- Gårding's inequality and the equation tested against `u` itself bound `‖u‖_{H¹}`.
  have hu_le : ‖u‖ ≤ 2 / lam * (‖f‖ + κ * ‖W1p.value u‖) :=
    ha.norm_le_of_isWeakSolutionDirichlet_of_norm_le (u := ⟨u, hu0⟩)
      ((continuousOn_of_continuousOn_matrixBilinearForm hK.continuousOn).aestronglyMeasurable
        Omega.isOpen.measurableSet) hb.aestronglyMeasurable hc.aestronglyMeasurable
      (ae_le_lpNorm_exponent_top hb) (ae_le_lpNorm_exponent_top hc)
      ((isWeakSolutionDirichlet_iff f _).2 hu)
  calc ‖w‖ ≤ C * (‖u‖ + ‖f‖) := hwle
    _ ≤ max C 0 * (‖u‖ + ‖f‖) := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * (2 / lam * (‖f‖ + κ * ‖W1p.value u‖) + ‖f‖) := by gcongr
    _ ≤ max C 0 * (1 + 2 / lam + 2 * κ / lam) * (‖W1p.value u‖ + ‖f‖) := by
      rw [mul_assoc]
      gcongr
      have h1 : 0 ≤ (1 + 2 / lam) * ‖W1p.value u‖ := by positivity
      have h2 : 0 ≤ 2 * κ / lam * ‖f‖ := by positivity
      have hexp : (1 + 2 / lam + 2 * κ / lam) * (‖W1p.value u‖ + ‖f‖) =
          2 / lam * (‖f‖ + κ * ‖W1p.value u‖) + ‖f‖ +
            ((1 + 2 / lam) * ‖W1p.value u‖ + 2 * κ / lam * ‖f‖) := by
        ring
      linarith

end Estimate

/-! ### `H³` regularity up to a smooth boundary -/

section ThirdOrder

variable [DecidableEq ι] {Omega W : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ} {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- **Local `H³` regularity near a straightened boundary portion.** Let `Φ` and `Ψ` be mutually
inverse smooth maps which are changes of variables of order three between open sets `U'` and `U`,
with Jacobian determinants at least one in absolute value, such that `Φ` maps the part of `U'` in
the half-space `H = {c₀ < ⟪x, ν⟫}` onto `Ω ∩ U`. Let `y₀ ∈ U'` lie in the closure of `H`, with
`Φ y₀ ∈ W`. Under the hypotheses of
`UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiff_graph`, `u` is `H³` on `Ω ∩ V`
for an open neighbourhood `V` of `Φ y₀`. -/
private theorem exists_value_eq_value_restrictL_of_isChangeOfVariables
    {U' U : Opens (EuclideanSpace ℝ ι)} {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {L : ℝ}
    (hΦ : Wkp.IsChangeOfVariables 3 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 3 U U' Ψ L 1)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) (hΦΨ : ∀ y, Φ (Ψ y) = y) (hΦs : ContDiff ℝ ∞ Φ)
    (hΨs : ContDiff ℝ ∞ Ψ) {ν : EuclideanSpace ℝ ι} (hν : ν ≠ 0) {c₀ : ℝ}
    (himage : Φ '' ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') = (Omega : Set (EuclideanSpace ℝ ι)) ∩ U)
    {y₀ : EuclideanSpace ℝ ι} (hy₀ : y₀ ∈ (U' : Set (EuclideanSpace ℝ ι)))
    (hy₀H : y₀ ∈ closure {x | c₀ < ⟪x, ν⟫_ℝ}) (hy₀W : Φ y₀ ∈ W)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) W) {F u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, W1p.value F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x) :
    ∃ V : Opens (EuclideanSpace ℝ ι), Φ y₀ ∈ V ∧
      ∃ w : Wkp mu (Omega ⊓ V) 2 3, Wkp.value 3 w = W1p.value (W1p.restrictL inf_le_left u) := by
  -- `ι` is nonempty, since `ν ≠ 0`.
  have : Nonempty ι := by
    by_contra hι
    rw [not_nonempty_iff] at hι
    exact hν (by ext i; exact isEmptyElim i)
  let H : Opens (EuclideanSpace ℝ ι) := ⟨{x | c₀ < ⟪x, ν⟫_ℝ}, isOpen_lt continuous_const
    (continuous_id.inner continuous_const)⟩
  refine exists_value_eq_value_restrictL_of_isChangeOfVariables_of_flat (H := H) (by norm_num) hΦ
    hΨ hΨΦ hΦΨ hΦs.continuous hΨs.continuous himage hy₀ hy₀W hu0
    fun r hr hrB Ω' D hΩ' hD hΦ' hΨ' hΦmaps hu0' V'' hV hVU => ?_
  have hBU' : ball y₀ r ⊆ (U' : Set (EuclideanSpace ℝ ι)) :=
    ball_subset_closedBall.trans (hrB.trans inter_subset_left)
  -- The transformed coefficient is uniformly elliptic on `Ω'` and smooth on `B(y₀, r)`.
  obtain ⟨z, hzH, hz⟩ := Metric.mem_closure_iff.1 hy₀H r hr
  obtain ⟨lam', Lam', hellip⟩ := exists_uniformlyEllipticOn_pullbackPrincipal
    (hΦ.mono (by norm_num : 1 ≤ 3)) (hΨ.mono (by norm_num : 1 ≤ 3)) (fun x _ => hΨΦ x)
    (fun y _ => hΦΨ y) (s := (Ω' : Set (EuclideanSpace ℝ ι)) ∩ ball y₀ r) (fun x hx => hBU' hx.2)
    ⟨z, by rw [hΩ']; exact ⟨hzH, mem_ball_comm.1 hz⟩, mem_ball_comm.1 hz⟩
    (fun x hx => hΦmaps hx.1) ha
  have hsm' (i j : ι) : ContDiffOn ℝ ∞ (fun x => pullbackPrincipal Φ a x i j) (ball y₀ r) :=
    contDiffOn_pullbackPrincipal_apply (hΦ.mono (by norm_num : 1 ≤ 3))
      (hΨ.mono (by norm_num : 1 ≤ 3)) (fun x _ => hΨΦ x) (fun y _ => hΦΨ y) hBU'
      (fun x hx => (hrB (ball_subset_closedBall hx)).2) hΦs.contDiffOn
      (hΨs.of_le (by simp)).contDiffOn hsmooth i j
  -- `H³` regularity near the flat boundary, since `u ∘ Φ` solves `-∂ᵢ(a'ⁱʲ ∂ⱼ(u ∘ Φ)) = F ∘ Φ`.
  exact UniformlyEllipticOn.exists_value_eq_value_restrictL_of_halfSpace (H := H)
    (U := ⟨ball y₀ r, isOpen_ball⟩) hν (fun _ => Iff.rfl)
    (by rw [hΩ', inter_assoc]; exact congrArg _ (inter_self _)) hellip hsm'
    (energyFormH1_w1pCompL_restrictL_eq_setIntegral hD hΦ' hΨ' (fun x _ => hΨΦ x)
      (fun y _ => hΦΨ y) hu) hu0' hV hVU

/-- **Local `H³` regularity near a smooth boundary portion.** Let `Ω` be open, and suppose that
in rigid coordinates `e` centred at `x₀ = e⁻¹ 0`, inside the normal cylinder of half-height `h₀`
and radius `r₀`, `Ω` is the region above the graph of a smooth function `γ` with `γ 0 = 0`. Let
`W` be an open neighbourhood of `x₀`, let `a` be uniformly elliptic on `Ω ∩ W` with entries smooth
on `W`, up to the boundary, let `F ∈ H¹(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω`

such that `ψ u ∈ H¹₀(Ω)` for every smooth `ψ` compactly supported in `W`: `u` vanishes on
`∂Ω ∩ W`. Then there is an open neighbourhood `V` of `x₀` such that the restriction of `u` to
`Ω ∩ V` is the value of an element of `W^{3,2}(Ω ∩ V)`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiff_graph
    {e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {h₀ r₀ : ℝ} (hh₀ : 0 < h₀)
    (hr₀ : 0 < r₀) (hγ0 : γ 0 = 0) (hγ : ContDiff ℝ ∞ γ)
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst))
    (hW : e.symm 0 ∈ W)
    (ha : UniformlyEllipticOn ((Omega : Set (EuclideanSpace ℝ ι)) ∩ W) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) W) {F u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, W1p.value F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hu0 : ∀ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∃ v : W1p0 mu Omega 2,
        W1p.value (v : W1p mu Omega 2) =ᵐ[mu.restrict Omega] fun x => ψ x * W1p.value u x) :
    ∃ V : Opens (EuclideanSpace ℝ ι), e.symm 0 ∈ V ∧
      ∃ w : Wkp mu (Omega ⊓ V) 2 3, Wkp.value 3 w = W1p.value (W1p.restrictL inf_le_left u) := by
  -- Flatten the boundary by changes of variables of order three: `Φ` maps the flat side `U'`
  -- into `U`, inverse to `Ψ`, and fixes `x₀`.
  have hγ3 : ContDiff ℝ 3 γ := hγ.of_le (by simp)
  obtain ⟨U', U, L, ν, c₀, hΦ, hΨ, hν, himage, hx₀U', hx₀H, hΦx₀⟩ :=
    exists_isChangeOfVariables_halfSpace_of_contDiff_graph (by norm_num) hh₀ hr₀ hγ0 hγ3 hgraph
  -- Both are smooth, since `γ` is.
  have he : ContDiff ℝ ∞ e := e.toContinuousAffineEquiv.toContinuousAffineMap.contDiff
  have he' : ContDiff ℝ ∞ e.symm := e.symm.toContinuousAffineEquiv.toContinuousAffineMap.contDiff
  have h := exists_value_eq_value_restrictL_of_isChangeOfVariables hΦ hΨ
    (fun x => by simp [-graphFlattening_apply, -graphFlattening_symm_apply])
    (fun y => by simp [-graphFlattening_apply, -graphFlattening_symm_apply])
    (he'.comp ((contDiff_graphFlattening_symm hγ).comp he))
    (he'.comp ((contDiff_graphFlattening hγ).comp he)) hν himage hx₀U' hx₀H (by rwa [hΦx₀]) ha
    hsmooth hu hu0
  rwa [hΦx₀] at h

/-- **`H³` regularity up to a smooth boundary** (Evans, §6.3.2, Theorem 5, for `m = 1` and
`b = c = 0`). Let `Ω` be a bounded open set with smooth boundary: at every boundary point `x`, in
rigid coordinates `e` with `e x = 0`, inside a normal cylinder, `Ω` is the region above the graph
of a smooth function `γ` with `γ 0 = 0`. Let `a` be uniformly elliptic on `Ω`, with entries smooth
on an open set `W` containing `closure Ω`, let `F ∈ H¹(Ω)`, and let `u ∈ H¹₀(Ω)` be a weak solution
of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω`, `u = 0` on `∂Ω`.

Then `u ∈ H³(Ω)`: it is the value of an element of `W^{3,2}(Ω)`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_of_contDiff_graph
    (hΩ : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hbdry : ∀ x ∈ frontier (Omega : Set (EuclideanSpace ℝ ι)),
      ∃ (e : EuclideanSpace ℝ ι ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ),
        e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ ∞ γ ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst))
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hW : closure (Omega : Set (EuclideanSpace ℝ ι)) ⊆ W)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) W) {F u : W1p mu Omega 2}
    (hu0 : u ∈ w1p0Submodule mu Omega 2)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, W1p.value F x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ w : Wkp mu Omega 2 3, Wkp.value 3 w = W1p.value u := by
  have hΩW : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ W := subset_closure.trans hW
  -- Every point of `closure Ω` has a neighbourhood `V` with `u ∈ H³(Ω ∩ V)`.
  have hloc (x : EuclideanSpace ℝ ι) (hx : x ∈ closure (Omega : Set (EuclideanSpace ℝ ι))) :
      ∃ V : Opens (EuclideanSpace ℝ ι), x ∈ V ∧
        ∃ w : Wkp mu (Omega ⊓ V) 2 3, Wkp.value 3 w = W1p.value (W1p.restrictL inf_le_left u) := by
    by_cases hxΩ : x ∈ (Omega : Set (EuclideanSpace ℝ ι))
    · -- Interior points, by interior `H³` regularity on a small ball.
      obtain ⟨ρ, hρ, hρΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hxΩ)
      have hcl : closure ((Omega ⊓ ⟨ball x ρ, isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) :
          Set (EuclideanSpace ℝ ι)) ⊆ closedBall x ρ :=
        (closure_mono inter_subset_right).trans closure_ball_subset_closedBall
      exact ⟨⟨ball x ρ, isOpen_ball⟩, mem_ball_self hρ,
        ha.exists_value_eq_value_restrictL_of_contDiffOn 1
          (fun i j => ((hsmooth i j).mono hΩW).of_le (by simp)) (b := 0) (c := 0)
          contDiffOn_const contDiffOn_const (F := (F : Wkp mu Omega 2 1))
          -- `Wkp … 1` is `W1p` definitionally but not reducibly, so `Wkp.value_one` converts.
          (fun v => (hu v).trans (congrArg (fun g : Lp ℝ 2 (mu.restrict Omega) =>
            ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu)
            (Wkp.value_one (F : Wkp mu Omega 2 1)).symm))
          ((isCompact_closedBall x ρ).of_isClosed_subset isClosed_closure hcl) (hcl.trans hρΩ)⟩
    · -- Boundary points, by flattening the boundary.
      obtain ⟨e, γ, h₀, r₀, hex, hh₀, hr₀, hγ0, hγ, hgraph⟩ :=
        hbdry x ⟨hx, by rwa [Omega.isOpen.interior_eq]⟩
      have hx₀ : e.symm 0 = x := by rw [← hex, e.symm_apply_apply]
      obtain ⟨V, hV, hw⟩ :=
        (ha.mono_set inter_subset_left).exists_value_eq_value_restrictL_of_contDiff_graph
        hh₀ hr₀ hγ0 hγ hgraph (hx₀ ▸ hW hx) hsmooth hu
        fun ψ hψ hψc _ => W1p.exists_w1p0_value_ae_eq_mul_of_mem_w1p0Submodule hψ hψc hu0
      exact ⟨V, hx₀ ▸ hV, hw⟩
  -- Finitely many such neighbourhoods cover the compact set `closure Ω`; glue.
  obtain ⟨v, hv⟩ := Wkp.exists_value_ae_eq_of_isCompact hΩ.isCompact_closure subset_closure 3
    (u := W1p.value u) fun x hx => by
      obtain ⟨V, hxV, w, hw⟩ := hloc x hx
      exact ⟨V, hxV, w, hw ▸ W1p.value_restrictL_ae inf_le_left u⟩
  exact ⟨v, Lp.ext hv⟩

end ThirdOrder

end PDE

end TauCeti
