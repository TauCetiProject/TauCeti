/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.PDE.Regularity.Inhomogeneous
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.Composition
import TauCeti.Analysis.Sobolev.Wkp.ContDiffRepresentative
import TauCeti.Analysis.Sobolev.Wkp.Leibniz

/-!
# Smoothness of weak solutions of semilinear equations

Let `Ω ⊆ ℝⁿ` be open with `n ≤ 3`, let `a` be a uniformly elliptic coefficient field whose entries
are smooth on `Ω`, let `A` and `C` be smooth on `Ω` and let `Φ : ℝ → ℝ` be smooth. This file
proves that a continuous weak solution `u ∈ H¹(Ω)` of the semilinear equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = A(x) Φ(u) + C(x)` in `Ω`

is smooth on `Ω` (`TauCeti.PDE.UniformlyEllipticOn.contDiffOn_of_energyFormH1_eq`). The weak form
is `∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω (A Φ(u) + C) v` for every `v ∈ H¹₀(Ω)`, with no boundary condition on `u`,
and continuity means that `u` agrees almost everywhere on `Ω` with a function `w` continuous on
`Ω`. The conclusion is that `w` itself is smooth on `Ω`.

Some a priori control of `u` is needed: for `u ∈ H¹(Ω)` the function `Φ(u)` need not even be
locally integrable, and the weak form only makes sense once it is. Continuity is the form in which
the first regularity step, which estimates the nonlinearity for the particular `Φ` at hand,
provides this control.
Alternatively, local square integrability of `A Φ(u) + C` gives continuity by De Giorgi's theorem,
then a smooth representative by
`UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_forall_energyFormH1_ofTestFunctionₗ_eq`.
On relatively compact balls, density extends the test-function equation to all `H¹₀` tests,
so the same bootstrap applies without a global integrability assumption. This is useful for
exponential nonlinearities once exponential integrability has been established.
The model case is Taubes's reduced vortex equation
`Δw = h (exp (2w) - 1) / 8 + k` in the plane, the Euler–Lagrange equation of
`TauCeti.Vortex.taubesFunctional`, whose weak solutions are continuous because Trudinger's
inequality controls `exp (2w)`. In the weak form above it reads `a = 1`, `A = -h / 8`,
`Φ(t) = exp (2t)` and `C = h / 8 - k`.

## The bootstrap

By induction on `j`, `w` is `Cʲ` on `Ω` and lies in `W^{j+1,2}(V)` for every open `V` with compact
closure in `Ω`. For `j = 0` this is the hypothesis. For the step, choose `W` between `V` and `Ω`.
Composition with `Φ` keeps one Sobolev order above the classical regularity of `w`
(`TauCeti.Wkp.exists_value_ae_eq_comp_of_contDiffOn`), so the right-hand side lies in
`W^{j+1,2}(W)`. Interior regularity
(`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiffOn`) gains two orders
and puts `w` in `W^{j+3,2}(V)`. Since `n < 4`, the interior Sobolev embedding
(`TauCeti.Wkp.exists_contDiffOn_ae_eq`) turns `W^{2 + (j+1),2}` into `C^{j+1}`. The dimension
restriction is what makes the bootstrap gain: two Sobolev orders cost at most two classical ones
exactly when `W^{2,2} ⊆ C⁰`.

## Main results

* `TauCeti.PDE.UniformlyEllipticOn.contDiffOn_of_energyFormH1_eq`: a continuous weak solution of
  `-∂ᵢ(aⁱʲ ∂ⱼu) = A(x) Φ(u) + C(x)` in dimension at most three is smooth.
* `TauCeti.PDE.UniformlyEllipticOn.contDiffOn_of_forall_energyFormH1_ofTestFunctionₗ_eq`: the
  same regularity from the equation tested only against compactly supported smooth functions.
* `UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_forall_energyFormH1_ofTestFunctionₗ_eq`:
  local square integrability of the forcing gives a smooth representative of a semilinear weak
  solution, without assuming continuity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.1 and §9.1.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.22 and 8.24.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III, §4.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {Omega : Opens (EuclideanSpace ℝ ι)}

/-- **One step of the bootstrap.** If a continuous weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = A(x) Φ(u) + C(x)` is `Cʲ` on `Ω` and lies in `W^{j+1,2}` of every open set with
compact closure in `Ω`, then it lies in `W^{j+3,2}` of every such set. -/
private theorem UniformlyEllipticOn.exists_value_ae_eq_of_energyFormH1_eq [DecidableEq ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    {A C : EuclideanSpace ℝ ι → ℝ} (hA : ContDiffOn ℝ ∞ A Omega) (hC : ContDiffOn ℝ ∞ C Omega)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {u : W1p volume Omega 2} {w : EuclideanSpace ℝ ι → ℝ}
    (huw : (W1p.value u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (Omega : Set _)] w)
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
      ∫ x in Omega, (A x * Φ (w x) + C x) * W1p.value (v : W1p volume Omega 2) x)
    {j : ℕ} (hwj : ContDiffOn ℝ j w Omega)
    (hj : ∀ W : Opens (EuclideanSpace ℝ ι), IsCompact (closure (W : Set (EuclideanSpace ℝ ι))) →
      closure (W : Set (EuclideanSpace ℝ ι)) ⊆ Omega → ∃ U : Wkp volume W 2 (j + 1),
        (Wkp.value (j + 1) U : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (W : Set _)] w)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : Wkp volume V 2 (j + 1 + 2),
      (Wkp.value (j + 1 + 2) U : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (V : Set _)] w := by
  -- An intermediate open set `W` with `closure V ⊆ W` and `closure W` compact in `Ω`.
  obtain ⟨W₀, hW₀, hVW₀, hWΩ₀, hWc⟩ :=
    exists_open_between_and_isCompact_closure hV Omega.isOpen hVΩ
  set W : Opens (EuclideanSpace ℝ ι) := ⟨W₀, hW₀⟩
  have hWΩ' : (W : Set (EuclideanSpace ℝ ι)) ⊆ Omega := subset_closure.trans hWΩ₀
  have hWΩ : W ≤ Omega := SetLike.coe_subset_coe.mp hWΩ'
  -- The right-hand side lies in `W^{j+1,2}(W)`.
  obtain ⟨U₁, hU₁⟩ := hj W hWc hWΩ₀
  obtain ⟨G, hG⟩ := Wkp.exists_value_ae_eq_comp_of_contDiffOn (by norm_num) Omega.isOpen hWc
    hWΩ₀ j (hΦ.of_le (by exact_mod_cast le_top)) hwj U₁ hU₁
  obtain ⟨GA, hGA⟩ := Wkp.exists_value_ae_eq_mul_of_contDiffOn Omega.isOpen.uniqueDiffOn hWc hWΩ₀
    (j + 1) hA G
  obtain ⟨GC, hGC⟩ := Wkp.exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := W) (p := 2) (j + 1) Omega.isOpen (hC.of_le (by exact_mod_cast le_top)) hWc
    subset_closure hWΩ₀
  have hF : (Wkp.value (j + 1) (GA + GC) : EuclideanSpace ℝ ι → ℝ)
      =ᵐ[volume.restrict (W : Set _)] fun x => A x * Φ (w x) + C x := by
    filter_upwards [Wkp.value_add (j + 1) GA GC ▸ Lp.coeFn_add _ _, hGA, hGC, hG]
      with x hx h₁ h₂ h₃
    rw [hx, Pi.add_apply, h₁, h₂, h₃]
  -- The restriction of `u` to `W` solves the equation there, so it lies in `W^{j+3,2}(V)`.
  have huW : ∀ v : W1p0 volume W 2,
      energyFormH1 a 0 0 (W1p.restrictL hWΩ u) (v : W1p volume W 2) =
        ∫ x in W, Wkp.value (j + 1) (GA + GC) x * W1p.value (v : W1p volume W 2) x := fun v => by
    rw [energyFormH1_restrictL_eq_setIntegral hWΩ hu v]
    refine integral_congr_ae ?_
    filter_upwards [hF] with x hx
    rw [hx]
  obtain ⟨U, hU⟩ := (ha.mono_set hWΩ').exists_value_eq_value_restrictL_of_contDiffOn
    (fun i l => (hsmooth i l).mono hWΩ') contDiffOn_const contDiffOn_const (j + 1) huW hV hVW₀
  refine ⟨U, ?_⟩
  rw [hU]
  exact (W1p.value_restrictL_ae _ _).trans (ae_restrict_of_ae_restrict_of_subset
    (subset_closure.trans hVW₀) ((W1p.value_restrictL_ae hWΩ u).trans
      (ae_restrict_of_ae_restrict_of_subset hWΩ' huw)))

/-- **Smoothness of continuous weak solutions of semilinear equations.** Let `Ω ⊆ ℝⁿ` be open,
with `n ≤ 3`, let `a` be uniformly elliptic on `Ω` with entries smooth on `Ω`, let `A` and `C` be
smooth on `Ω`, and let `Φ : ℝ → ℝ` be smooth. If `u ∈ H¹(Ω)` agrees almost everywhere on `Ω` with
a function `w` continuous on `Ω` and is a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = A(x) Φ(u) + C(x)` in `Ω`,

in the sense that `∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω (A Φ(w) + C) v` for every `v ∈ H¹₀(Ω)`, then `w` is smooth
on `Ω`. No boundary condition on `u` and no regularity of `∂Ω` is assumed. -/
theorem UniformlyEllipticOn.contDiffOn_of_energyFormH1_eq [DecidableEq ι]
    (hι : Fintype.card ι < 4) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    {A C : EuclideanSpace ℝ ι → ℝ} (hA : ContDiffOn ℝ ∞ A Omega) (hC : ContDiffOn ℝ ∞ C Omega)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {u : W1p volume Omega 2} {w : EuclideanSpace ℝ ι → ℝ}
    (hw : ContinuousOn w Omega)
    (huw : (W1p.value u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (Omega : Set _)] w)
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
      ∫ x in Omega, (A x * Φ (w x) + C x) * W1p.value (v : W1p volume Omega 2) x) :
    ContDiffOn ℝ ∞ w Omega := by
  have hdim : finrank ℝ (EuclideanSpace ℝ ι) < 2 * 2 := by
    rw [finrank_euclideanSpace]
    omega
  -- Changing the order index by an equality of natural numbers.
  have hcast : ∀ {V : Opens (EuclideanSpace ℝ ι)} {m n : ℕ}, m = n → ∀ U : Wkp volume V 2 m,
      ∃ U' : Wkp volume V 2 n, Wkp.value n U' = Wkp.value m U := by
    rintro V m n rfl U
    exact ⟨U, rfl⟩
  have key : ∀ j : ℕ, ContDiffOn ℝ j w Omega ∧ ∀ V : Opens (EuclideanSpace ℝ ι),
      IsCompact (closure (V : Set (EuclideanSpace ℝ ι))) →
        closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega → ∃ U : Wkp volume V 2 (j + 1),
          (Wkp.value (j + 1) U : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (V : Set _)] w := by
    intro j
    induction j with
    | zero =>
      refine ⟨by simpa using hw, fun V _ hVΩ => ?_⟩
      have hV : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)
      refine ⟨W1p.restrictL hV u, Filter.EventuallyEq.trans (.of_eq (congrArg
        (fun f : Lp ℝ 2 (volume.restrict (V : Set _)) => (f : EuclideanSpace ℝ ι → ℝ))
        (Wkp.value_one _))) ((W1p.value_restrictL_ae hV u).trans ?_)⟩
      exact ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVΩ) huw
    | succ j ih =>
      obtain ⟨hwj, hj⟩ := ih
      have hstep := fun {V : Opens (EuclideanSpace ℝ ι)} hV hVΩ =>
        ha.exists_value_ae_eq_of_energyFormH1_eq hsmooth hA hC hΦ huw hu hwj hj (V := V) hV hVΩ
      refine ⟨contDiffOn_of_locally_contDiffOn fun x hx => ?_, fun V hV hVΩ => ?_⟩
      · -- On a small ball about `x`, `w` lies in `W^{2 + (j+1),2}`, hence is `C^{j+1}`.
        obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Omega.isOpen x hx
        set V : Opens (EuclideanSpace ℝ ι) := ⟨ball x (r / 2), isOpen_ball⟩
        have hVc : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ closedBall x (r / 2) :=
          closure_ball_subset_closedBall
        have hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega :=
          hVc.trans ((closedBall_subset_ball (half_lt_self hr)).trans hrΩ)
        obtain ⟨U, hU⟩ := hstep ((isCompact_closedBall x (r / 2)).of_isClosed_subset
          isClosed_closure hVc) hVΩ
        obtain ⟨U', hU'⟩ := hcast (by omega : j + 1 + 2 = 2 + (j + 1)) U
        obtain ⟨g, hg, hUg⟩ := Wkp.exists_contDiffOn_ae_eq hdim (j + 1) U'
        have heq : EqOn w g V := Measure.eqOn_open_of_ae_eq (hU.symm.trans (hU' ▸ hUg))
          isOpen_ball (hw.mono (subset_closure.trans hVΩ)) hg.continuousOn
        refine ⟨ball x (r / 2), isOpen_ball, mem_ball_self (half_pos hr), ?_⟩
        exact_mod_cast (hg.congr heq).mono inter_subset_right
      · obtain ⟨U, hU⟩ := hstep hV hVΩ
        exact ⟨Wkp.lowerOrder (j + 2) U, by rwa [← Wkp.value_succ]⟩
  exact contDiffOn_infty.2 fun j => (key j).1

/-- **Semilinear regularity from test functions.** In dimension at most three, let `a` be
uniformly elliptic on `Ω` with smooth entries, and let `A`, `C` and `Φ` be smooth. Then a
continuous representative of a weak solution of `-div(a ∇u) = A Φ(u) + C` is smooth. It
suffices to test the equation against compactly supported smooth functions; no global
integrability of the nonlinear forcing is required. -/
theorem UniformlyEllipticOn.contDiffOn_of_forall_energyFormH1_ofTestFunctionₗ_eq [DecidableEq ι]
    (hι : Fintype.card ι < 4) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) Omega)
    {A C : EuclideanSpace ℝ ι → ℝ} (hA : ContDiffOn ℝ ∞ A Omega) (hC : ContDiffOn ℝ ∞ C Omega)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {u : W1p volume Omega 2} {w : EuclideanSpace ℝ ι → ℝ}
    (hw : ContinuousOn w Omega)
    (huw : (W1p.value u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (Omega : Set _)] w)
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, (A x * Φ (w x) + C x) * φ x) :
    ContDiffOn ℝ ∞ w Omega := by
  refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  let B : Opens (EuclideanSpace ℝ ι) := ⟨ball x r, isOpen_ball⟩
  have hBΩ : B ≤ Omega := ball_subset_closedBall.trans hrΩ
  have haB := ha.mono_set hBΩ
  have hcoeff := memLp_energyIntegrand_of_bounds (mu := volume) (b := 0) (c := 0)
    (beta := 0) (gamma := 0) haB.upper_nonneg
    ((continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
      ((hsmooth i j).continuousOn.mono hBΩ)).aestronglyMeasurable B.isOpen.measurableSet)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ hy η ξ ↦ haB.upper_bound hy η ξ) (fun _ _ ↦ by simp) (fun _ _ ↦ by simp)
  have hf : MemLp (fun y ↦ A y * Φ (w y) + C y) 2 (volume.restrict B) :=
    ContinuousOn.memLp_restrict_of_subset_isCompact
      (((hA.continuousOn.mul (hΦ.continuous.comp_continuousOn hw)).add hC.continuousOn).mono hrΩ)
      (isCompact_closedBall x r) B.isOpen.measurableSet ball_subset_closedBall 2
  have huB := forall_energyFormH1_restrictL_eq_setIntegral hBΩ hcoeff hu hf
  have hwB := haB.contDiffOn_of_energyFormH1_eq hι
    (fun i j ↦ (hsmooth i j).mono hBΩ) (hA.mono hBΩ) (hC.mono hBΩ) hΦ (hw.mono hBΩ)
    ((W1p.value_restrictL_ae hBΩ u).trans
      (ae_restrict_of_ae_restrict_of_subset hBΩ huw)) huB
  exact ⟨B, B.isOpen, mem_ball_self hr, hwB.mono inter_subset_right⟩

/-- **Smooth representatives of semilinear weak solutions.** In dimension at most three,
let `a` be uniformly elliptic with smooth entries, and let `A`, `C` and `Φ` be smooth. If
`u ∈ H¹(Ω)` solves `-div(a ∇u) = A Φ(u) + C` against compactly supported smooth functions and
the nonlinear forcing is square integrable on every compact subset of `Ω`, then `u` has a
smooth representative on `Ω`. Continuity or boundedness of `u` is not assumed. -/
theorem UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_forall_energyFormH1_ofTestFunctionₗ_eq
    [DecidableEq ι] (hι : Fintype.card ι < 4)
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x ↦ a x i j) Omega)
    {A C : EuclideanSpace ℝ ι → ℝ} (hA : ContDiffOn ℝ ∞ A Omega) (hC : ContDiffOn ℝ ∞ C Omega)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) {u : W1p volume Omega 2}
    (hf : ∀ K, IsCompact K → K ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      MemLp (fun x ↦ A x * Φ (W1p.value u x) + C x) 2 (volume.restrict K))
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
      ∫ x in Omega, (A x * Φ (W1p.value u x) + C x) * φ x) :
    ∃ w : EuclideanSpace ℝ ι → ℝ, ContDiffOn ℝ ∞ w Omega ∧
      (W1p.value u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (Omega : Set _)] w := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    -- A zero-dimensional model space is a singleton, so every function is constant.
    have heq : (W1p.value u : EuclideanSpace ℝ ι → ℝ) = fun _ ↦ W1p.value u 0 :=
      funext fun y ↦ congrArg (W1p.value u) (Subsingleton.elim y 0)
    exact ⟨W1p.value u, heq ▸ contDiffOn_const, Filter.EventuallyEq.rfl⟩
  | inr h =>
    let w := TauCeti.MeasureTheory.preciseRepresentative volume
      (W1p.value u : EuclideanSpace ℝ ι → ℝ)
    have hmeas : AEStronglyMeasurable a (volume.restrict Omega) :=
      (continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦ (hsmooth i j).continuousOn)
        |>.aestronglyMeasurable Omega.isOpen.measurableSet
    have hw : ContinuousOn w Omega := continuousOn_preciseRepresentative_of_forall_memLp
      (r := 2) le_rfl (by exact_mod_cast hι) ha hmeas hf hu
    have huw : (W1p.value u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (Omega : Set _)] w :=
      W1p.ae_eq_preciseRepresentative u
    refine ⟨w, ha.contDiffOn_of_forall_energyFormH1_ofTestFunctionₗ_eq hι hsmooth hA hC hΦ
      hw huw (fun φ ↦ (hu φ).trans ?_), huw⟩
    exact integral_congr_ae (huw.mono fun x hx ↦ by dsimp only; rw [hx])

end PDE

end TauCeti
