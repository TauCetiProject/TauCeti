/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Holder
import TauCeti.Analysis.PDE.Regularity.Classical
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.ContinuousRepresentative
import TauCeti.MeasureTheory.Function.LocalRepresentative

/-!
# Classical second differentiability for Poisson's equation with Hölder data

A weak `H¹` solution of `-Δu = f` with Hölder continuous data has a `C²` representative
solving the equation pointwise in the interior. No boundary condition or regularity of the
domain boundary is needed.

The Hölder estimates for weak second derivatives in `Hessian.Holder` alone do not assert
classical differentiability of the solution. Here continuous representatives of these fields
first give `C¹` representatives of the first derivatives, by
`HasWeakFDerivOn.exists_contDiffOn_one_ae_eq`. Their assembly into a `C¹` weak derivative of
`u` then gives a `C²` representative. This requires no extra derivatives of the data. Where
the data is locally Hölder, this `C²` representative is the precise representative of `u`, so
the precise representative is a classical solution there.

For a weak solution tested only against test functions, with data that is locally Hölder but not
necessarily integrable on all of `Ω`, the same holds for each representative that is continuous on
`Ω` (`TauCeti.PDE.contDiffOn_two_and_neg_laplacian_eq_of_forall_testFunction`): on each ball with
closure in `Ω` the equation extends to `H¹₀` of the ball, and the representative is the precise
representative there.

The result is a regularity statement, not a quantitative Schauder estimate: no estimate of
the `C^{2,α}` norm in terms of the data and the value of `u` is asserted here.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 4.6.
-/

public section

noncomputable section

open InnerProductSpace Laplacian LineDeriv MeasureTheory Metric Set TopologicalSpace
open TauCeti.MeasureTheory
open scoped ContDiff Distributions Gradient InnerProductSpace NNReal Topology

namespace TauCeti.PDE

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

/-- A weak solution of `-Δu = f` with Hölder data has a `C²` representative on an open
set whose positive thickening lies in a relatively compact subdomain. Hölder control of
the data is needed only on this thickening, rather than throughout the original domain.
The auxiliary subdomain `V` supplies a compactness margin; no Hölder control is required
outside the thickening. For data locally Hölder throughout the original domain, use
`exists_contDiffOn_two_ae_eq_and_neg_laplacian_eq_of_locally_holderOnWith`. -/
theorem exists_contDiffOn_two_ae_eq_on_of_holderOnWith
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {u : W1p volume Omega 2} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict Omega))
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x)
    {V S : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hVO : closure (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Omega)
    {K : ℝ≥0} {R : ℝ}
    (hfK : HolderOnWith K α f (thickening R (S : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hR : 0 < R)
    (hSV : thickening R (S : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ V) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiffOn ℝ 2 g S ∧
      W1p.value u =ᵐ[volume.restrict S] g := by
  obtain ⟨C, -, hsecond⟩ :=
    exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient hα hα1 (n := n)
  have hSV' : S ≤ V := (self_subset_thickening hR _).trans hSV
  have hSO : S ≤ Omega := hSV'.trans (subset_closure.trans hVO)
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  -- Each directional derivative has a continuous weak gradient, hence a `C¹` representative.
  have hfirst : ∀ i, ∃ gi : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiffOn ℝ 1 gi S ∧ HasWeakLineDerivOn volume S (W1p.value u) gi (b i) := by
    intro i
    obtain ⟨d, hd, hG⟩ := hsecond hf hu hV hVO hfK hR hSV (b i)
    let G := preciseRepresentative volume
      (W1p.gradient d : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    have hGc : ContinuousOn G S := hG.continuousOn hα
    have hdG : (W1p.gradient d : EuclideanSpace ℝ (Fin (n + 1)) → _)
        =ᵐ[volume.restrict S] G :=
      ae_restrict_of_ae_restrict_of_subset hSV'
        (ae_eq_restrict_preciseRepresentative V.isOpen (W1p.locallyIntegrableOn_gradient d))
    have hweak : HasWeakFDerivOn volume S (W1p.value d) (fun x => innerSL ℝ (G x)) :=
      ((W1p.hasWeakFDerivOn d).mono hSV').congr_ae_deriv (hdG.fun_comp (innerSL ℝ))
    obtain ⟨gi, hgi, hdgi, -⟩ := hweak.exists_contDiffOn_one_ae_eq
      ((innerSL ℝ).continuous.comp_continuousOn hGc)
    exact ⟨gi, hgi, (hd.mono hSV').congr_ae_deriv hdgi⟩
  choose g hg hdg using hfirst
  -- Assemble the first derivatives into a `C¹` derivative field, then recover `u` itself.
  obtain ⟨hD, huD⟩ := contDiffOn_sum_innerSL_and_hasWeakFDerivOn hg
    ((W1p.hasWeakFDerivOn u).locallyIntegrableOn.mono_set hSO) hdg
  obtain ⟨g, hg, hug, -⟩ := huD.exists_contDiffOn_succ_ae_eq (n := 1) hD
  exact ⟨g, by exact_mod_cast hg, hug⟩

/-- For a `C²` function, the divergence-form operator of the identity matrix is the Laplacian. -/
theorem divMatrixGradient_one_eq_laplacian {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hg : ContDiffOn ℝ 2 g Omega) {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ Omega) :
    divMatrixGradient (fun _ => 1) g x = Δ g x := by
  rw [divMatrixGradient_eq_sum_fderiv_fderiv_apply hg hx,
    laplacian_eq_sum_fderiv_fderiv_apply (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)
      (((hg.fderiv_of_isOpen Omega.isOpen (by norm_num)).differentiableOn
        one_ne_zero).differentiableAt (Omega.isOpen.mem_nhds hx))]
  simp [Matrix.one_apply]

/-- **Classical second differentiability for Poisson's equation with Hölder data.**
Let `0 < α < 1`. A weak `H¹(Ω)` solution of `-Δu = f`, with `f ∈ L²(Ω)` and `f` locally
`α`-Hölder on `Ω`, agrees almost everywhere with a `C²` function `g` satisfying `-Δg = f`
at every point of `Ω`. The Hölder constants and neighbourhoods may vary with the point.
No boundary condition or boundary regularity is assumed. This does not assert a quantitative
Schauder norm estimate. -/
theorem exists_contDiffOn_two_ae_eq_and_neg_laplacian_eq_of_locally_holderOnWith
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {u : W1p volume Omega 2} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict Omega))
    (hfK : ∀ x ∈ Omega, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α f T)
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) :
    ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiffOn ℝ 2 g Omega ∧
      W1p.value u =ᵐ[volume.restrict Omega] g ∧ ∀ x ∈ Omega, -Δ g x = f x := by
  suffices hregular : ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiffOn ℝ 2 g Omega ∧ W1p.value u =ᵐ[volume.restrict Omega] g by
    obtain ⟨g, hg, hug⟩ := hregular
    have hfc : ContinuousOn f Omega := by
      intro x hx
      obtain ⟨T, hT, K, hfT⟩ := hfK x hx
      exact ((hfT.continuousOn hα).continuousAt hT).continuousWithinAt
    have hpoint := divMatrixGradient_eq_neg_of_forall_energyFormH1_eq (A := 1) hg hfc hug
      fun φ => by
        refine (hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).trans ?_
        exact integral_congr_ae ((W1p.value_ofTestFunctionₗ_ae (p := 2) φ).mono fun x hx =>
          congrArg (f x * ·) hx)
    refine ⟨g, hg, hug, fun x hx => ?_⟩
    rw [← divMatrixGradient_one_eq_laplacian hg hx, hpoint x hx, neg_neg]
  refine exists_contDiffOn_ae_eq_of_locally fun x hx => ?_
  obtain ⟨T, hT, K, hfT⟩ := hfK x hx
  obtain ⟨r, hr, hrOT⟩ := nhds_basis_closedBall.mem_iff.1
    (Filter.inter_mem (Omega.isOpen.mem_nhds hx) hT)
  have hrO := hrOT.trans inter_subset_left
  let V : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x r, isOpen_ball⟩
  let S : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x (r / 4), isOpen_ball⟩
  have hSV : thickening (r / 4) (S : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ V := by
    dsimp [S, V]
    exact (Metric.thickening_ball x (r / 4) (r / 4)).trans (ball_subset_ball (by linarith))
  have hVO : closure (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Omega :=
    closure_ball_subset_closedBall.trans hrO
  obtain ⟨g, hg, hug⟩ := exists_contDiffOn_two_ae_eq_on_of_holderOnWith hα hα1 hf hu
    ((isCompact_closedBall x r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall) hVO
    (hfT.mono (hSV.trans (ball_subset_closedBall.trans (hrOT.trans inter_subset_right))))
    (by positivity) hSV
  exact ⟨S, ball_mem_nhds x (by positivity), g, hg, hug⟩

/-- **The precise representative is a classical solution.** Let `u ∈ H¹(Ω)` be a weak solution
of `-Δu = f` with `f ∈ L²(Ω)`, and let `U ⊆ Ω` be open. If `f` is locally `α`-Hölder on `U`, with
`0 < α < 1`, then the precise representative of `u` is of class `C²` on `U` and solves
`-Δu = f` at every point of `U`. -/
theorem contDiffOn_preciseRepresentative_and_neg_laplacian_eq
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {u : W1p volume Omega 2} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hf : MemLp f 2 (volume.restrict Omega))
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x)
    {U : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hUO : U ≤ Omega)
    (hfK : ∀ x ∈ U, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α f T) :
    ContDiffOn ℝ 2 (preciseRepresentative volume (W1p.value u)) U ∧
      ∀ x ∈ U, -Δ (preciseRepresentative volume (W1p.value u)) x = f x := by
  obtain ⟨g, hg, hug, hΔg⟩ :=
    exists_contDiffOn_two_ae_eq_and_neg_laplacian_eq_of_locally_holderOnWith hα hα1
      (hf.mono_measure (Measure.restrict_mono hUO le_rfl)) hfK
      (energyFormH1_restrictL_eq_setIntegral hUO hu)
  have heq : EqOn (preciseRepresentative volume (W1p.value u)) g U :=
    eqOn_preciseRepresentative_of_continuousOn U.isOpen
      ((W1p.hasWeakFDerivOn u).locallyIntegrableOn.mono_set hUO)
      ((W1p.value_restrictL_ae hUO u).symm.trans hug) hg.continuousOn
  refine ⟨hg.congr fun x hx => heq hx, fun x hx => ?_⟩
  rw [← hΔg x hx, (laplacian_congr_nhds (Filter.eventually_of_mem (U.isOpen.mem_nhds hx)
    fun y hy => heq hy)).self_of_nhds]

/-- **A continuous weak solution with Hölder data is a classical solution.** Let `0 < α < 1`. If
`u ∈ H¹(Ω)` solves `-Δu = f` against test functions, with `f` locally `α`-Hölder on `Ω`, then every
representative `g` of `u` that is continuous on `Ω` is `C²` on `Ω` and satisfies `-Δg = f` at every
point of `Ω`. Unlike `exists_contDiffOn_two_ae_eq_and_neg_laplacian_eq_of_locally_holderOnWith`,
no integrability of `f` on all of `Ω` is assumed, and the equation is only tested against test
functions. -/
theorem contDiffOn_two_and_neg_laplacian_eq_of_forall_testFunction {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {u : W1p volume Omega 2} {g f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hg : ContinuousOn g Omega) (hug : W1p.value u =ᵐ[volume.restrict Omega] g)
    (hf : ∀ x ∈ Omega, ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α f T)
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, f x * φ x) :
    ContDiffOn ℝ 2 g Omega ∧ ∀ x ∈ Omega, -Δ g x = f x := by
  have hfc : ContinuousOn f Omega := fun x hx => by
    obtain ⟨T, hT, K, hK⟩ := hf x hx
    exact ((hK.continuousOn hα).continuousAt hT).continuousWithinAt
  -- On a ball `B` with closure in `Ω`, `g` is the precise representative of `u|_B`, which is a
  -- classical solution by the interior `C²` regularity of Poisson's equation with Hölder data.
  have hloc : ∀ x ∈ Omega, ∃ B : Opens (EuclideanSpace ℝ (Fin (n + 1))), x ∈ B ∧ B ≤ Omega ∧
      ContDiffOn ℝ 2 g B ∧ ∀ y ∈ B, -Δ g y = f y := by
    intro x hx
    obtain ⟨ε, hε, hεΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
    let B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x ε, isOpen_ball⟩
    have hBΩ : B ≤ Omega := ball_subset_closedBall.trans hεΩ
    have : IsFiniteMeasure (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hfB : MemLp f 2 (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
      ((hfc.mono hεΩ).memLp_restrict_of_subset_isCompact (isCompact_closedBall x ε)
        isOpen_ball.measurableSet ball_subset_closedBall 2)
    have hB1 := uniformlyEllipticOn_const_one_one (n := Fin (n + 1))
      (B : Set (EuclideanSpace ℝ (Fin (n + 1))))
    have hcoeff := memLp_energyIntegrand_of_bounds (mu := volume) (Omega := B) (b := 0) (c := 0)
      (beta := 0) (gamma := 0) hB1.upper_nonneg aestronglyMeasurable_const
      aestronglyMeasurable_const aestronglyMeasurable_const
      (fun _ hy eta xi => hB1.upper_bound hy eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
    have huB := forall_energyFormH1_restrictL_eq_setIntegral hBΩ hcoeff hu hfB
    obtain ⟨hC2, hΔ⟩ := contDiffOn_preciseRepresentative_and_neg_laplacian_eq hα hα1 hfB huB le_rfl
      fun y hy => hf y (hBΩ hy)
    have heq : EqOn (preciseRepresentative volume (W1p.value (W1p.restrictL hBΩ u))) g B :=
      eqOn_preciseRepresentative_of_continuousOn B.isOpen
        (W1p.hasWeakFDerivOn _).locallyIntegrableOn
        ((W1p.value_restrictL_ae hBΩ u).trans (ae_restrict_of_ae_restrict_of_subset hBΩ hug))
        (hg.mono hBΩ)
    refine ⟨B, mem_ball_self hε, hBΩ, hC2.congr fun y hy => (heq hy).symm, fun y hy => ?_⟩
    rw [← hΔ y hy, (laplacian_congr_nhds (Filter.eventually_of_mem (B.isOpen.mem_nhds hy)
      fun z hz => heq hz)).self_of_nhds]
  refine ⟨contDiffOn_of_locally_contDiffOn fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨B, hxB, -, hB, -⟩ := hloc x hx
    exact ⟨B, B.isOpen, hxB, hB.mono inter_subset_right⟩
  · obtain ⟨B, hxB, -, -, hB⟩ := hloc x hx
    exact hB x hxB

end TauCeti.PDE
