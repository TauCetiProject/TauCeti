/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.FiniteMeasure
public import TauCeti.LinearAlgebra.BilinearForm.PosSemidef

/-!
# The Dirichlet problem: existence and uniqueness of a weak solution

Lane D, item 17 of `TauCetiRoadmap/PDE/README.md` asks for the first end-to-end existence
theorem of the roadmap: for a divergence-form operator

`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`

whose energy form is coercive on `H¹₀(Ω)`, the homogeneous Dirichlet problem `L u = f` in `Ω`,
`u = 0` on `∂Ω`, has a unique weak solution. This file assembles that theorem out of pieces
that are already in place: the bundled energy form `TauCeti.PDE.energyFormH1L0` and its lower
bounds from `TauCeti/Analysis/PDE/EnergyForm/Sobolev.lean`, and the variational form of
Lax--Milgram `IsCoercive.existsUnique_forall_eq` from
`TauCeti/Analysis/InnerProductSpace/LaxMilgram.lean`.

## The weak formulation

A weak solution is a function `u ∈ H¹₀(Ω)` satisfying

`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,

which is `TauCeti.PDE.IsWeakSolutionDirichlet`. Two hypotheses are hidden in that sentence and
neither is a boundary-regularity assumption. The homogeneous boundary condition is carried by
membership in `H¹₀(Ω) = W^{1,2}_0(Ω)`, the closure of `C_c^∞(Ω)`, so no trace operator and no
regularity of `∂Ω` is needed to state it. The right-hand side is an `L²(Ω)` function paired
against the *value* component of the test function, which is what makes it a continuous linear
functional on `H¹₀(Ω)`: `TauCeti.PDE.dirichletForcing`, of norm at most `‖f‖_{L²}` because the
value component of a Sobolev jet is dominated by the graph norm.

## Where coercivity comes from

Lax--Milgram needs `IsCoercive`, that is `∃ C > 0, ∀ u, C‖u‖‖u‖ ≤ a(u, u)`, and the energy-form
file supplies exactly such diagonal lower bounds without packaging them.
`TauCeti.PDE.isCoercive_energyFormH1L0` converts any of them, and the two geometric routes of
that file are instantiated here: a domain trapped between two hyperplanes and a domain contained
in a ball, whose Poincaré constants are the slab width `t - s` and the diameter bound `2R`. In
both cases the drift smallness condition `βP < λ` is what makes the resulting constant positive,
and with no drift it is vacuous.

A mass floor `δ` satisfying `β² < 4λδ` gives another route. Choose `0 < ε < λ` with
`β² < 4εδ`; the coercivity constant is `min (λ - ε) (δ - β²/(4ε))`, on any open domain,
including all of Euclidean space. The theorem
`TauCeti.PDE.UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_mass_lower_bound`
therefore needs no geometric or Poincaré hypothesis. These are sufficient conditions; when
coercivity is unavailable the Fredholm alternative (Lane D, item 18) replaces Lax--Milgram.

## The `-Δ` payoff

Specialising to `a = 1`, `b = 0`, `c = 0` on a ball gives
`TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball`: the Poisson problem
`-Δu = f` in `Ω`, `u = 0` on `∂Ω`, has a unique weak solution whenever `Ω` is contained in a
ball. Unfolded through `TauCeti.PDE.isWeakSolutionDirichlet_one_zero_zero_iff` the variational
equation reads `∫_Ω ∇v · ∇u = ∫_Ω f v`, the classical weak form of Poisson's equation. This is
the existence half of the roadmap's "end-to-end existence" acceptance criterion; the smoothness
half is Lane E and the identification with the Newtonian potential is Lane C.

## Prescribed boundary values

The inhomogeneous boundary condition `u = g` on `∂Ω`, for boundary values given by a function
`g ∈ H¹(Ω)`, is again carried by `H¹₀(Ω)`: it means `u - g ∈ H¹₀(Ω)`. The forcing may be any
`ℓ ∈ H⁻¹(Ω) = (H¹₀(Ω))*`, not only an `L²` function. `TauCeti.PDE.dirichletSolution` solves the
resulting problem by applying Lax--Milgram to `u - g`, with right-hand side `v ↦ ℓ v - a(g, v)`,
and bundles the solution as a continuous linear map of the pair `(g, ℓ)`, with the explicit bound
`‖u‖_{H¹} ≤ (1 + ‖a‖/C) ‖g‖_{H¹} + ‖ℓ‖/C`. For `L = -Δ` and zero forcing this is the *harmonic
replacement* of `g`, the comparison function of the Campanato approach to regularity
(`TauCeti/Analysis/PDE/Regularity/HarmonicReplacement.lean`).

The solution depends Lipschitz continuously on the coefficients: if two operators share the
boundary values and the forcing, and the first is coercive with constant `C`, then the two
solutions differ in `H¹` by at most `(Λ + β + γ) ‖u'‖_{H¹} / C`, where `Λ`, `β` and `γ` bound the
differences of the principal, drift and mass coefficients on `Ω`.

When the energy form is symmetric, as for `-∂ᵢ(aⁱʲ ∂ⱼu) + c u` with symmetric `a`, and
nonnegative on `H¹₀(Ω)`, the weak solution is characterized variationally by the **Dirichlet
principle**: `g + w` solves the problem exactly when `w ∈ H¹₀(Ω)` minimizes the Dirichlet energy
`v ↦ a(g + v, g + v)/2 - ℓ v`. This is the specialization of
`LinearMap.BilinForm.IsPosSemidef.forall_apply_eq_iff_isMinOn` to the energy form.

## A priori bound

`TauCeti.PDE.norm_le_of_isWeakSolutionDirichlet` records the energy estimate `‖u‖_{H¹} ≤ ‖f‖/C`
attached to a coercivity constant `C`. It is proved for *every* weak solution rather than for
the constructed one, so it is available before, and independently of, uniqueness.

## Main declarations

* `TauCeti.PDE.dirichletForcing`: the `L²` right-hand side as a continuous linear functional on
  `H¹₀(Ω)`, with `TauCeti.PDE.norm_dirichletForcing_le`.
* `TauCeti.PDE.IsWeakSolutionDirichlet`: the weak formulation of `L u = f` in `Ω`, `u = 0` on
  `∂Ω`.
* `TauCeti.PDE.forall_energyFormH1_eq_setIntegral_iff_forall_testFunction` and
  `TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction`: for bounded coefficients it is
  enough to test the weak formulation against `C_c^∞(Ω)`; conversely
  `TauCeti.PDE.IsWeakSolutionDirichlet.energyFormH1_ofTestFunctionₗ` tests a weak solution against
  `C_c^∞(Ω)` with no hypothesis on the coefficients.
* `TauCeti.PDE.isCoercive_energyFormH1L0`: a diagonal lower bound packaged as `IsCoercive`, and
  `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyFormH1L0_of_mass_lower_bound`: coercivity
  when the potential absorbs the drift.
* `TauCeti.PDE.weakSolutionDirichlet` and
  `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet`: the Lax--Milgram solution and the
  existence-and-uniqueness theorem.
* `TauCeti.PDE.norm_le_of_isWeakSolutionDirichlet`: the energy estimate `‖u‖ ≤ ‖f‖/C`.
* `TauCeti.PDE.dirichletSolution`: the solution operator `(g, ℓ) ↦ u` of the Dirichlet problem
  with boundary values `g ∈ H¹(Ω)` and forcing `ℓ ∈ H⁻¹(Ω)`, characterized by
  `TauCeti.PDE.dirichletSolution_sub_mem_w1p0Submodule`,
  `TauCeti.PDE.energyFormH1_dirichletSolution` and `TauCeti.PDE.eq_dirichletSolution`.
* `TauCeti.PDE.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq`: existence and
  uniqueness for prescribed boundary values `u = g` on `∂Ω`, `g ∈ H¹(Ω)`, and forcing in
  `H⁻¹(Ω)`; `TauCeti.PDE.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_setIntegral`
  is its case of `L²` forcing, with its case of a ball-contained domain
  `UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball`.
* `TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_eq` and
  `TauCeti.PDE.norm_dirichletSolution_le`: the energy estimates with boundary values.
* `TauCeti.PDE.norm_sub_le_of_forall_energyFormH1_eq_energyFormH1`: stability under perturbation
  of the coefficients.
* `TauCeti.PDE.forall_energyFormH1_eq_iff_isMinOn`: the Dirichlet principle.
* `TauCeti.PDE.UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_mass_lower_bound`:
  existence and uniqueness on an arbitrary open domain when the potential absorbs the drift.
* `TauCeti.PDE.UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp`:
  existence and uniqueness for `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f`, `c ≥ 0`, on a domain of finite measure
  with data `f ∈ Lʳ(Ω)`, `r > max 1 (2n/(n+2))`, which need not be square integrable.
* `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_of_subset_slab` and
  `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_of_subset_ball`: existence and uniqueness
  under the geometric hypotheses that make the energy form coercive.
* `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball`: the Poisson
  problem `-Δu = f` on a ball-contained domain.

## References

Lane D, item 17 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial Differential
Equations*, Section 2.2.5 (Dirichlet's principle), Section 6.2.1 (the lifting of boundary values)
and Section 6.2.2 (existence of weak solutions); D. Gilbarg and N. Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Chapter 8, Theorem 8.3; H. Brezis, *Functional Analysis,
Sobolev Spaces and Partial Differential Equations*, Corollary 5.8 (Lax--Milgram, with the
minimization characterization for symmetric forms).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Matrix NNReal

section Domain

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {C : ℝ}

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-! ### The forcing functional -/

/-- The **right-hand side of the Dirichlet problem** as a continuous linear functional on
`H¹₀(Ω)`: an `L²(Ω)` function `f` acts by `v ↦ ∫_Ω f v`, pairing against the value component of
the Sobolev jet. Continuity is automatic from the construction, the value map
`TauCeti.W1p0.valueL` being continuous and the pairing being the `L²` inner product. -/
def dirichletForcing (f : Lp ℝ 2 (mu.restrict Omega)) : StrongDual ℝ (W1p0 mu Omega 2) :=
  (innerSL ℝ f).comp W1p0.valueL

/-- The forcing functional is the `L²` inner product against the value component. -/
@[simp] theorem dirichletForcing_apply (f : Lp ℝ 2 (mu.restrict Omega)) (v : W1p0 mu Omega 2) :
    dirichletForcing f v = ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
  rw [dirichletForcing, ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p0.valueL_apply]

/-- The forcing functional written as the integral `∫_Ω f v` it names. -/
theorem dirichletForcing_apply_eq_setIntegral (f : Lp ℝ 2 (mu.restrict Omega))
    (v : W1p0 mu Omega 2) :
    dirichletForcing f v = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  rw [dirichletForcing_apply, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [RCLike.inner_apply, mul_comm])

/-- The forcing functional is bounded by the `L²` norm of its density, because the value
component of a Sobolev jet is dominated by the graph norm. -/
theorem norm_dirichletForcing_apply_le (f : Lp ℝ 2 (mu.restrict Omega))
    (v : W1p0 mu Omega 2) : ‖dirichletForcing f v‖ ≤ ‖f‖ * ‖v‖ := by
  rw [dirichletForcing_apply]
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (W1p.norm_value_le (v : W1p mu Omega 2)) (norm_nonneg f)

/-- The operator norm of the forcing functional is at most `‖f‖_{L²(Ω)}`. -/
theorem norm_dirichletForcing_le (f : Lp ℝ 2 (mu.restrict Omega)) :
    ‖dirichletForcing f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (norm_dirichletForcing_apply_le f)

/-! ### The weak formulation -/

/-- **The weak formulation of the homogeneous Dirichlet problem.** `u ∈ H¹₀(Ω)` is a weak
solution of `L u = f` in `Ω`, `u = 0` on `∂Ω`, for
`L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u`, when

`a(u, v) = ∫_Ω f v` for every test function `v ∈ H¹₀(Ω)`.

The boundary condition is not a side condition here: it is membership of `u` in `H¹₀(Ω)`, the
closure of `C_c^∞(Ω)`, so no regularity of `∂Ω` and no trace operator enters the statement.
Nothing is assumed about the coefficients; each theorem below names the hypotheses it uses. -/
def IsWeakSolutionDirichlet (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ)
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) : Prop :=
  ∀ v : W1p0 mu Omega 2,
    energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) = dirichletForcing f v

/-- Being a weak solution, written out as the integral identity `a(u, v) = ∫_Ω f v`. -/
@[simp] theorem isWeakSolutionDirichlet_iff (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet a b c f u ↔
      ∀ v : W1p0 mu Omega 2,
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2)
          = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [IsWeakSolutionDirichlet, dirichletForcing_apply_eq_setIntegral]

/-- **Testing against test functions suffices.** When the energy density is essentially bounded,
so that the energy form is continuous on `H¹(Ω)`, a function `u ∈ H¹(Ω)` satisfies the weak
equation `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)` as soon as it does for every test function
`v ∈ C_c^∞(Ω)`: both sides are continuous in `v`, and `H¹₀(Ω)` is the closure of `C_c^∞(Ω)`.
No boundary condition is imposed on `u`. -/
theorem forall_energyFormH1_eq_setIntegral_iff_forall_testFunction
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p mu Omega 2) :
    (∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2)
        = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) ↔
      ∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 a b c u (W1p.ofTestFunctionₗ mu Omega 2 φ)
          = ∫ x in Omega, f x * φ x ∂mu := by
  -- On `H¹₀(Ω)`, the integral against `f` is the `L²` inner product with `f`.
  have hforce : ∀ v : W1p0 mu Omega 2, ⟪f, W1p.value (v : W1p mu Omega 2)⟫_ℝ
      = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := fun v =>
    (dirichletForcing_apply f v).symm.trans (dirichletForcing_apply_eq_setIntegral f v)
  have htest : ∀ φ : 𝓓(Omega, ℝ),
      ∫ x in Omega, f x * W1p.value (W1p.ofTestFunctionₗ mu Omega 2 φ) x ∂mu
        = ∫ x in Omega, f x * φ x ∂mu := fun φ =>
    integral_congr_ae ((W1p.value_ofTestFunctionₗ_ae (p := 2) φ).mono fun x hx =>
      congrArg (f x * ·) hx)
  refine ⟨fun h φ => (h ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).trans (htest φ),
    fun h v => ?_⟩
  have hclosed : IsClosed {v : W1p mu Omega 2 |
      energyFormH1L hcoeff u v = ⟪f, W1p.value v⟫_ℝ} :=
    isClosed_eq (energyFormH1L hcoeff u).continuous
      (((innerSL ℝ f).continuous.comp W1p.valueL.continuous).congr fun v => by
        simp only [Function.comp_apply, innerSL_apply_apply]
        exact congrArg _ (W1p.valueL_apply v))
  have hmem := w1p0Submodule_subset_of_isClosed hclosed (fun φ =>
    ((energyFormH1L_apply hcoeff _ _).trans ((h φ).trans (htest φ).symm)).trans
      (hforce ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).symm) v.2
  rw [← energyFormH1L_apply hcoeff, ← hforce v]
  exact hmem

/-- A weak solution satisfies the weak equation `a(u, φ) = ∫_Ω f φ` against every test function
`φ ∈ C_c^∞(Ω)`. Unlike the converse in
`TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction`, this needs no bound on the
coefficients. -/
theorem IsWeakSolutionDirichlet.energyFormH1_ofTestFunctionₗ {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p0 mu Omega 2} (hu : IsWeakSolutionDirichlet a b c f u) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 a b c (u : W1p mu Omega 2) (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu :=
  ((isWeakSolutionDirichlet_iff f u).1 hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).trans
    (integral_congr_ae ((W1p.value_ofTestFunctionₗ_ae (p := 2) φ).mono fun x hx =>
      congrArg (f x * ·) hx))

/-- **Testing against test functions suffices.** When the energy density is essentially bounded,
so that the energy form is continuous on `H¹(Ω)`, `u` is a weak solution as soon as the weak
equation `a(u, φ) = ∫_Ω f φ` holds for every test function `φ ∈ C_c^∞(Ω)`: both sides are
continuous in the test function, and `H¹₀(Ω)` is the closure of `C_c^∞(Ω)`. -/
theorem isWeakSolutionDirichlet_iff_forall_testFunction
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet a b c f u ↔
      ∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 a b c (u : W1p mu Omega 2) (W1p.ofTestFunctionₗ mu Omega 2 φ)
          = ∫ x in Omega, f x * φ x ∂mu :=
  (isWeakSolutionDirichlet_iff f u).trans
    (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff f u)

/-- **The energy estimate.** Any weak solution is bounded in `H¹` by the `L²` norm of the data,
with the coercivity constant as the only other ingredient. The estimate is stated for every
weak solution, so it does not presuppose uniqueness. -/
theorem norm_le_of_isWeakSolutionDirichlet (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p0 mu Omega 2}
    (hu : IsWeakSolutionDirichlet a b c f u) : ‖u‖ ≤ ‖f‖ / C := by
  have hkey : C * ‖u‖ ^ 2 ≤ ‖f‖ * ‖u‖ :=
    ((hlower u).trans_eq (hu u)).trans ((le_abs_self _).trans (norm_dirichletForcing_apply_le f u))
  rcases eq_or_lt_of_le (norm_nonneg u) with hzero | hpos
  · rw [← hzero]
    exact div_nonneg (norm_nonneg f) hC.le
  · rw [le_div_iff₀ hC]
    nlinarith [hkey, hpos]

/-! ### Coercivity and Lax--Milgram -/

/-- **A diagonal lower bound is coercivity.** The energy-form file proves bounds of the shape
`C‖u‖² ≤ a(u, u)`; this packages one, together with positivity of its constant, as the
`IsCoercive` hypothesis of Mathlib's Lax--Milgram theorem. -/
theorem isCoercive_energyFormH1L0
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2)) :
    IsCoercive (energyFormH1L0 hcoeff) := by
  refine ⟨C, hC, fun w => ?_⟩
  rw [energyFormH1L0_apply]
  calc C * ‖w‖ * ‖w‖ = C * ‖w‖ ^ 2 := by ring
    _ ≤ _ := hlower w

/-- **The weak solution of the Dirichlet problem**, produced by Lax--Milgram from coercivity of
the energy form. It is characterised by
`TauCeti.PDE.isWeakSolutionDirichlet_weakSolutionDirichlet` together with
`TauCeti.PDE.eq_weakSolutionDirichlet`. -/
def weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    W1p0 mu Omega 2 :=
  hcoercive.solutionOfFunctional (dirichletForcing f)

/-- The Lax--Milgram solution is a weak solution of the Dirichlet problem. -/
theorem isWeakSolutionDirichlet_weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    IsWeakSolutionDirichlet a b c f (weakSolutionDirichlet hcoeff hcoercive f) := by
  intro v
  rw [← energyFormH1L0_apply hcoeff]
  exact hcoercive.apply_solutionOfFunctional_eq (dirichletForcing f) v

/-- A weak solution of the Dirichlet problem is *the* Lax--Milgram solution. -/
theorem eq_weakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p0 mu Omega 2} (hu : IsWeakSolutionDirichlet a b c f u) :
    u = weakSolutionDirichlet hcoeff hcoercive f :=
  hcoercive.eq_solutionOfFunctional fun v => by
    rw [energyFormH1L0_apply hcoeff]; exact hu v

/-- **Existence and uniqueness of the weak solution of the Dirichlet problem.** For a
divergence-form operator whose energy form is bounded and coercive on `H¹₀(Ω)`, and for every
`f ∈ L²(Ω)`, there is exactly one `u ∈ H¹₀(Ω)` with

`a(u, v) = ∫_Ω f v` for all `v ∈ H¹₀(Ω)`.

This is Lane D, item 17 of the PDE roadmap: the energy method's existence theorem, obtained by
consuming Mathlib's Lax--Milgram theorem through the variational interface. -/
theorem existsUnique_isWeakSolutionDirichlet
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u :=
  ⟨weakSolutionDirichlet hcoeff hcoercive f,
    isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive f,
    fun _ hu => eq_weakSolutionDirichlet hcoeff hcoercive hu⟩

/-- Existence and uniqueness of the weak solution, stated from a diagonal lower bound on the
energy form instead of a packaged `IsCoercive` hypothesis. -/
theorem existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u :=
  existsUnique_isWeakSolutionDirichlet hcoeff (isCoercive_energyFormH1L0 hcoeff hC hlower) f

/-! ### Prescribed boundary values -/

section SolutionOperator

attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

/-- **The solution operator of the Dirichlet problem with boundary values.** For a divergence-form
operator whose energy form `a` is bounded and coercive on `H¹₀(Ω)`, it sends boundary values
`g ∈ H¹(Ω)` and a forcing `ℓ ∈ H⁻¹(Ω) = (H¹₀(Ω))*` to the weak solution of `L u = ℓ` in `Ω`,
`u = g` on `∂Ω`: the unique `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and `a(u, v) = ℓ v` for every
`v ∈ H¹₀(Ω)` (`TauCeti.PDE.dirichletSolution_sub_mem_w1p0Submodule`,
`TauCeti.PDE.energyFormH1_dirichletSolution` and `TauCeti.PDE.eq_dirichletSolution`). Being a
continuous linear map, the solution depends linearly and boundedly on the pair `(g, ℓ)`; an
explicit bound is `TauCeti.PDE.norm_dirichletSolution_le`. -/
def dirichletSolution
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    W1p mu Omega 2 × StrongDual ℝ (W1p0 mu Omega 2) →L[ℝ] W1p mu Omega 2 :=
  -- `(g, ℓ) ↦ (g - S (a(g, ·))) + S ℓ`, where `S` is the Lax--Milgram solution map into
  -- `H¹₀(Ω) ⊆ H¹(Ω)` and `a(g, ·)` is restricted to `H¹₀(Ω)`. The sum is formed in `H¹(Ω)`, not
  -- in `H⁻¹(Ω)`: instance search for the topology of `H⁻¹(Ω)` times out.
  let S : StrongDual ℝ (W1p0 mu Omega 2) →L[ℝ] W1p mu Omega 2 :=
    (w1p0Submodule mu Omega 2).toSubmodule.subtypeL.comp hcoercive.solutionOfFunctionalCLM
  let A : W1p mu Omega 2 →L[ℝ] StrongDual ℝ (W1p0 mu Omega 2) :=
    (energyFormH1L hcoeff).bilinearComp (ContinuousLinearMap.id ℝ (W1p mu Omega 2))
      (w1p0Submodule mu Omega 2).toSubmodule.subtypeL
  (ContinuousLinearMap.id ℝ (W1p mu Omega 2) - S.comp A).coprod S

/-- The solution of the Dirichlet problem with boundary values `g` and forcing `ℓ` is `g` plus
the Lax--Milgram solution in `H¹₀(Ω)` for the functional `v ↦ ℓ v - a(g, v)`. -/
theorem dirichletSolution_apply
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletSolution hcoeff hcoercive (g, ℓ) = g + hcoercive.solutionOfFunctional
      (ℓ - (energyFormH1L hcoeff g).comp (w1p0Submodule mu Omega 2).toSubmodule.subtypeL) := by
  have hA : (energyFormH1L hcoeff).bilinearComp (ContinuousLinearMap.id ℝ (W1p mu Omega 2))
      (w1p0Submodule mu Omega 2).toSubmodule.subtypeL g =
        (energyFormH1L hcoeff g).comp (w1p0Submodule mu Omega 2).toSubmodule.subtypeL :=
    ContinuousLinearMap.ext fun v => by simp
  -- Unfold the definition: `g - S (a(g, ·)) + S ℓ`.
  have hdef : dirichletSolution hcoeff hcoercive (g, ℓ) =
      g - (hcoercive.solutionOfFunctionalCLM ((energyFormH1L hcoeff).bilinearComp
        (ContinuousLinearMap.id ℝ (W1p mu Omega 2))
          (w1p0Submodule mu Omega 2).toSubmodule.subtypeL g) : W1p mu Omega 2) +
        (hcoercive.solutionOfFunctionalCLM ℓ : W1p mu Omega 2) :=
    rfl
  -- The Lax--Milgram solution is additive in the functional.
  have hsub : ∀ x : StrongDual ℝ (W1p0 mu Omega 2), hcoercive.solutionOfFunctional ℓ -
      hcoercive.solutionOfFunctional x = hcoercive.solutionOfFunctional (ℓ - x) := fun x =>
    hcoercive.eq_solutionOfFunctional fun v => by
      simp only [map_sub, sub_apply, IsCoercive.apply_solutionOfFunctional_eq]
  rw [hdef]
  simp only [hA, IsCoercive.solutionOfFunctionalCLM_apply]
  calc _ = g + ((hcoercive.solutionOfFunctional ℓ : W1p mu Omega 2) -
        hcoercive.solutionOfFunctional
          ((energyFormH1L hcoeff g).comp (w1p0Submodule mu Omega 2).toSubmodule.subtypeL)) := by
        abel
    _ = _ := congrArg (g + ·) ((Submodule.coe_sub _ _ _).symm.trans (congrArg Subtype.val (hsub _)))

/-- The solution of the Dirichlet problem has the prescribed boundary values: its difference
with `g` lies in `H¹₀(Ω)`. -/
theorem dirichletSolution_sub_mem_w1p0Submodule
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    dirichletSolution hcoeff hcoercive (g, ℓ) - g ∈ w1p0Submodule mu Omega 2 := by
  rw [dirichletSolution_apply, add_sub_cancel_left, ← ClosedSubmodule.mem_toSubmodule_iff]
  exact Subtype.prop _

/-- The solution of the Dirichlet problem satisfies the weak equation `a(u, v) = ℓ v` for every
`v ∈ H¹₀(Ω)`. -/
@[simp]
theorem energyFormH1_dirichletSolution
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) (v : W1p0 mu Omega 2) :
    energyFormH1 a b c (dirichletSolution hcoeff hcoercive (g, ℓ)) v = ℓ v := by
  have h := hcoercive.apply_solutionOfFunctional_eq
    (ℓ - (energyFormH1L hcoeff g).comp (w1p0Submodule mu Omega 2).toSubmodule.subtypeL) v
  rw [energyFormH1L0_apply] at h
  rw [dirichletSolution_apply, energyFormH1_add_left hcoeff, h]
  simp

/-- **Uniqueness for the Dirichlet problem with boundary values.** A function `u ∈ H¹(Ω)` with
`u - g ∈ H¹₀(Ω)` and `a(u, v) = ℓ v` for every `v ∈ H¹₀(Ω)` is
`TauCeti.PDE.dirichletSolution` of `(g, ℓ)`. -/
theorem eq_dirichletSolution
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {g u : W1p mu Omega 2}
    {ℓ : StrongDual ℝ (W1p0 mu Omega 2)} (hu : u - g ∈ w1p0Submodule mu Omega 2)
    (h : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v) :
    u = dirichletSolution hcoeff hcoercive (g, ℓ) := by
  have hu₀ : u - g ∈ W1p0 mu Omega 2 := (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hu
  set ℓ' : StrongDual ℝ (W1p0 mu Omega 2) :=
    ℓ - (energyFormH1L hcoeff g).comp (w1p0Submodule mu Omega 2).toSubmodule.subtypeL with hℓ'
  -- `u - g` is the Lax--Milgram solution for `ℓ' = ℓ - a(g, ·)`.
  have hw : ∀ v, energyFormH1L0 hcoeff ⟨u - g, hu₀⟩ v = ℓ' v := fun v => by
    rw [energyFormH1L0_apply, Submodule.coe_mk, energyFormH1_sub_left hcoeff, h, hℓ']
    simp
  rw [dirichletSolution_apply, ← hcoercive.eq_solutionOfFunctional hw, Submodule.coe_mk,
    add_sub_cancel]

/-- **The Dirichlet problem with boundary values in `H¹(Ω)` and forcing in `H⁻¹(Ω)`.** For a
divergence-form operator whose energy form is bounded and coercive on `H¹₀(Ω)`, every
`g ∈ H¹(Ω)` and every `ℓ ∈ H⁻¹(Ω) = (H¹₀(Ω))*`, there is exactly one `u ∈ H¹(Ω)` with
`u - g ∈ H¹₀(Ω)` and

`a(u, v) = ℓ v` for all `v ∈ H¹₀(Ω)`.

This is the weak form of `L u = ℓ` in `Ω`, `u = g` on `∂Ω`: the boundary condition is carried by
membership of `u - g` in `H¹₀(Ω)`, so neither a trace operator nor any regularity of `∂Ω`
enters. The solution is `TauCeti.PDE.dirichletSolution`. -/
theorem existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (g : W1p mu Omega 2)
    (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1p0Submodule mu Omega 2 ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v :=
  ⟨dirichletSolution hcoeff hcoercive (g, ℓ),
    ⟨dirichletSolution_sub_mem_w1p0Submodule hcoeff hcoercive g ℓ,
      energyFormH1_dirichletSolution hcoeff hcoercive g ℓ⟩,
    fun _ hu => eq_dirichletSolution hcoeff hcoercive hu.1 hu.2⟩

/-- **The Dirichlet problem with boundary values in `H¹(Ω)` and forcing in `L²(Ω)`.** For a
divergence-form operator whose energy form is bounded and coercive on `H¹₀(Ω)`, every
`f ∈ L²(Ω)` and every `g ∈ H¹(Ω)`, there is exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and

`a(u, v) = ∫_Ω f v` for all `v ∈ H¹₀(Ω)`.

For `g = 0` it is `TauCeti.PDE.existsUnique_isWeakSolutionDirichlet`. -/
theorem existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_setIntegral
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega))
    (g : W1p mu Omega 2) :
    ∃! u : W1p mu Omega 2, u - g ∈ w1p0Submodule mu Omega 2 ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simpa only [dirichletForcing_apply_eq_setIntegral] using
    existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq hcoeff hcoercive g
      (dirichletForcing f)

/-- With zero boundary values and `L²` forcing, the solution of the Dirichlet problem is the weak
solution `TauCeti.PDE.weakSolutionDirichlet` of the homogeneous problem. -/
@[simp]
theorem dirichletSolution_zero_dirichletForcing
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (f : Lp ℝ 2 (mu.restrict Omega)) :
    dirichletSolution hcoeff hcoercive (0, dirichletForcing f) =
      weakSolutionDirichlet hcoeff hcoercive f := by
  refine (eq_dirichletSolution hcoeff hcoercive ?_ fun v => ?_).symm
  · rw [sub_zero, ← ClosedSubmodule.mem_toSubmodule_iff]
    exact Subtype.prop _
  · exact isWeakSolutionDirichlet_weakSolutionDirichlet hcoeff hcoercive f v

/-! ### Energy estimates for prescribed boundary values -/

/-- **The energy estimate with boundary values.** If the energy form `a` satisfies
`C ‖w‖² ≤ a(w, w)` on `H¹₀(Ω)`, then every `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and
`a(u, v) = ℓ v` for all `v ∈ H¹₀(Ω)` satisfies

`‖u - g‖_{H¹} ≤ (‖ℓ‖ + ‖a‖ ‖g‖_{H¹}) / C`,

where `‖a‖` is the norm of the energy form as a bilinear form on `H¹(Ω)`. -/
theorem norm_sub_le_of_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    {g u : W1p mu Omega 2} {ℓ : StrongDual ℝ (W1p0 mu Omega 2)}
    (hu : u - g ∈ w1p0Submodule mu Omega 2)
    (h : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = ℓ v) :
    ‖u - g‖ ≤ (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C := by
  let w : W1p0 mu Omega 2 := ⟨u - g, (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hu⟩
  have hw : ‖u - g‖ = ‖w‖ := Submodule.norm_coe w
  -- Test the equation against `w = u - g` itself: `a(w, w) = ℓ w - a(g, w)`.
  have heq : energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2) =
      ℓ w - energyFormH1L hcoeff g w := by
    rw [energyFormH1L_apply, ← h w, ← energyFormH1_sub_left hcoeff]
  have hℓ : ℓ w ≤ ‖ℓ‖ * ‖w‖ := (le_abs_self _).trans (ℓ.le_opNorm w)
  have hB : -(energyFormH1L hcoeff g w) ≤ ‖energyFormH1L hcoeff‖ * ‖g‖ * ‖w‖ := by
    refine (neg_le_abs _).trans ?_
    rw [← Real.norm_eq_abs, ← hw]
    exact (energyFormH1L hcoeff).le_opNorm₂ g w
  rw [hw, le_div_iff₀ hC]
  nlinarith [hlower w, norm_nonneg w, norm_nonneg ℓ,
    mul_nonneg (norm_nonneg (energyFormH1L hcoeff)) (norm_nonneg g)]

/-- **A bound for the solution operator of the Dirichlet problem.** If the energy form `a`
satisfies `C ‖w‖² ≤ a(w, w)` on `H¹₀(Ω)`, then the solution with boundary values `g` and forcing
`ℓ` satisfies

`‖u‖_{H¹} ≤ (1 + ‖a‖ / C) ‖g‖_{H¹} + ‖ℓ‖ / C`. -/
theorem norm_dirichletSolution_le
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) :
    ‖dirichletSolution hcoeff hcoercive (g, ℓ)‖ ≤
      (1 + ‖energyFormH1L hcoeff‖ / C) * ‖g‖ + ‖ℓ‖ / C := by
  have h := norm_sub_le_of_forall_energyFormH1_eq hcoeff hC hlower
    (dirichletSolution_sub_mem_w1p0Submodule hcoeff hcoercive g ℓ)
    (energyFormH1_dirichletSolution hcoeff hcoercive g ℓ)
  calc ‖dirichletSolution hcoeff hcoercive (g, ℓ)‖
      ≤ ‖g‖ + ‖dirichletSolution hcoeff hcoercive (g, ℓ) - g‖ := norm_le_insert' _ _
    _ ≤ ‖g‖ + (‖ℓ‖ + ‖energyFormH1L hcoeff‖ * ‖g‖) / C := by gcongr
    _ = (1 + ‖energyFormH1L hcoeff‖ / C) * ‖g‖ + ‖ℓ‖ / C := by
      field_simp
      ring

/-- **Stability of the Dirichlet problem under perturbation of the coefficients.** Let `u` solve
the problem for the coefficients `(a, b, c)`, whose energy form satisfies `C ‖w‖² ≤ a(w, w)` on
`H¹₀(Ω)`, and let `u'` solve the problem with the same boundary values and the same forcing for
the coefficients `(a', b', c')`: `u - u' ∈ H¹₀(Ω)` and `a(u, v) = a'(u', v)` for every
`v ∈ H¹₀(Ω)`. If the coefficient differences are bounded on `Ω` by `Λ`, `β` and `γ`, in the
sense of `TauCeti.PDE.norm_energyFormH1_le_of_bounds`, then

`‖u - u'‖_{H¹} ≤ (Λ + β + γ) ‖u'‖_{H¹} / C`.

So, for a fixed coercivity constant, the solution depends Lipschitz continuously on the
coefficients in the uniform norm. -/
theorem norm_sub_le_of_forall_energyFormH1_eq_energyFormH1
    {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {b' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    {c' : EuclideanSpace ℝ ι → ℝ} {Lam beta gamma : ℝ}
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeff' : MemLp (fun x => energyIntegrand (a' x) (b' x) (c' x)) ⊤ (mu.restrict Omega))
    (hC : 0 < C)
    (hlower : ∀ w : W1p0 mu Omega 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2))
    (hLam : 0 ≤ Lam)
    (ha_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ∀ eta xi : EuclideanSpace ℝ ι,
      |dotProduct eta (Matrix.mulVec (a x - a' x) xi)| ≤ Lam * ‖eta‖ * ‖xi‖)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x - b' x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x - c' x‖ ≤ gamma)
    {u u' : W1p mu Omega 2} (hu : u - u' ∈ w1p0Submodule mu Omega 2)
    (h : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u v = energyFormH1 a' b' c' u' v) :
    ‖u - u'‖ ≤ (Lam + beta + gamma) * ‖u'‖ / C := by
  let w : W1p0 mu Omega 2 := ⟨u - u', (ClosedSubmodule.mem_toSubmodule_iff _ _).2 hu⟩
  have hw : ‖u - u'‖ = ‖w‖ := Submodule.norm_coe w
  -- On `w = u - u'` the form `a` sees only the coefficient difference applied to `u'`:
  -- `a(w, w) = a(u, w) - a(u', w) = a'(u', w) - a(u', w)`.
  have heq : energyFormH1 a b c (w : W1p mu Omega 2) (w : W1p mu Omega 2) =
      -energyFormH1 (fun x => a x - a' x) (fun x => b x - b' x) (fun x => c x - c' x) u'
        (w : W1p mu Omega 2) := by
    rw [energyFormH1_sub hcoeff hcoeff', ← h w]
    exact energyFormH1_sub_left hcoeff u (w : W1p mu Omega 2) u' |>.trans (by ring)
  have hdiff := norm_energyFormH1_le_of_bounds hLam ha_bound hbeta hgamma hb_bound hc_bound u'
    (w : W1p mu Omega 2)
  rw [Real.norm_eq_abs, Submodule.norm_coe] at hdiff
  rw [hw, le_div_iff₀ hC]
  nlinarith [hlower w, norm_nonneg w, mul_nonneg (by linarith : 0 ≤ Lam + beta + gamma)
    (norm_nonneg u'), neg_le_abs (energyFormH1 (fun x => a x - a' x) (fun x => b x - b' x)
    (fun x => c x - c' x) u' (w : W1p mu Omega 2))]

end SolutionOperator

/-! ### The Dirichlet principle -/

/-- **The Dirichlet principle.** Let the energy form `a` be symmetric whenever one argument lies
in `H¹₀(Ω)`, and nonnegative on `H¹₀(Ω)`. Both hold for `-∂ᵢ(aⁱʲ ∂ⱼu) + c u` with symmetric `a`
(`TauCeti.PDE.energyFormH1_comm_of_isSymm_ae`) and coercive form. For boundary values
`g ∈ H¹(Ω)` and forcing `ℓ ∈ H⁻¹(Ω)`, the function `g + w`, `w ∈ H¹₀(Ω)`, is a weak solution of
`L u = ℓ` in `Ω`, `u = g` on `∂Ω`, exactly when `w` minimizes the Dirichlet energy

`v ↦ a(g + v, g + v) / 2 - ℓ v`

over `H¹₀(Ω)`, that is, when `g + w` minimizes `a(u, u) / 2 - ℓ (u - g)` over the affine space
`g + H¹₀(Ω)`. -/
theorem forall_energyFormH1_eq_iff_isMinOn
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hsymm : ∀ (u : W1p mu Omega 2) (v : W1p0 mu Omega 2),
      energyFormH1 a b c u (v : W1p mu Omega 2) = energyFormH1 a b c (v : W1p mu Omega 2) u)
    (hpos : ∀ v : W1p0 mu Omega 2,
      0 ≤ energyFormH1 a b c (v : W1p mu Omega 2) (v : W1p mu Omega 2))
    (g : W1p mu Omega 2) (ℓ : StrongDual ℝ (W1p0 mu Omega 2)) (w : W1p0 mu Omega 2) :
    (∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c (g + (w : W1p mu Omega 2)) (v : W1p mu Omega 2) = ℓ v) ↔
      IsMinOn (fun v : W1p0 mu Omega 2 =>
        energyFormH1 a b c (g + (v : W1p mu Omega 2)) (g + (v : W1p mu Omega 2)) / 2 - ℓ v)
        univ w := by
  -- Up to the constant `a(g, g) / 2`, the Dirichlet energy is the quadratic functional of the
  -- form `a` on `H¹₀(Ω)` and the functional `v ↦ ℓ v - a(g, v)`.
  obtain ⟨B, hB⟩ : ∃ B : LinearMap.BilinForm ℝ (W1p0 mu Omega 2), ∀ u v,
      B u v = energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) :=
    ⟨(energyFormH1L0 hcoeff).toLinearMap₁₂, fun u v => energyFormH1L0_apply hcoeff u v⟩
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : Module.Dual ℝ (W1p0 mu Omega 2), ∀ v,
      ℓ' v = ℓ v - energyFormH1 a b c g (v : W1p mu Omega 2) :=
    ⟨(ℓ - (energyFormH1L hcoeff g).comp
      (w1p0Submodule mu Omega 2).toSubmodule.subtypeL).toLinearMap, fun v => by simp⟩
  have hBpsd : B.IsPosSemidef := LinearMap.BilinForm.isPosSemidef_def.2
    ⟨⟨fun u v => by rw [hB, hB, hsymm]⟩, ⟨fun v => by rw [hB]; exact hpos v⟩⟩
  have hJ : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c (g + (v : W1p mu Omega 2)) (g + (v : W1p mu Omega 2)) / 2 - ℓ v =
        B v v / 2 - ℓ' v + energyFormH1 a b c g g / 2 := fun v => by
    -- Expand `a(g + v, g + v)` by bilinearity and use `a(v, g) = a(g, v)`.
    have h₁ := energyFormH1_add_left hcoeff g (g + (v : W1p mu Omega 2)) v
    have h₂ := energyFormH1_add_right hcoeff g g v
    have h₃ := energyFormH1_add_right hcoeff (v : W1p mu Omega 2) g v
    linarith [hB v v, hℓ' v, hsymm g v]
  have hsol : (∀ v : W1p0 mu Omega 2,
      energyFormH1 a b c (g + (w : W1p mu Omega 2)) (v : W1p mu Omega 2) = ℓ v) ↔
      ∀ v, B w v = ℓ' v := forall_congr' fun v => by
    have h₁ := energyFormH1_add_left hcoeff g (v : W1p mu Omega 2) w
    rw [hB, hℓ']
    constructor <;> intro h <;> linarith
  rw [hsol, hBpsd.forall_apply_eq_iff_isMinOn ℓ' w]
  simp only [isMinOn_univ_iff]
  constructor <;> intro h v <;> linarith [h v, hJ v, hJ w]

/-- **Coercivity under the mass-floor condition** `β² < 4λδ`. A Young parameter between
`β²/(4δ)` and `λ` makes the gradient and value coefficients of Gårding's inequality positive, so
the energy form of a uniformly elliptic operator whose potential is at least `δ` is coercive on
`H¹₀(Ω)`. No domain boundedness, Poincaré inequality, or symmetry of the principal coefficient
is required. -/
theorem UniformlyEllipticOn.isCoercive_energyFormH1L0_of_mass_lower_bound
    [DecidableEq ι] {lam Lam beta gamma delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), delta ≤ c x)
    (hmass : beta ^ 2 < 4 * lam * delta)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega)) :
    IsCoercive (energyFormH1L0 hcoeff) := by
  have hdelta : 0 < delta := by
    have : 0 < 4 * lam * delta := lt_of_le_of_lt (sq_nonneg beta) hmass
    exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) h.pos)).mp this
  have hquot : beta ^ 2 / (4 * delta) < lam := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hdelta)).mpr
    nlinarith [hmass]
  obtain ⟨eps, hlo, hhi⟩ := exists_between hquot
  have heps : 0 < eps := lt_of_le_of_lt (by positivity) hlo
  have hdefect : beta ^ 2 / (4 * eps) < delta := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) heps)).mpr
    have hmul := (div_lt_iff₀ (mul_pos (by norm_num) hdelta)).mp hlo
    nlinarith [hmul]
  exact isCoercive_energyFormH1L0 hcoeff (lt_min (sub_pos.mpr hhi) (sub_pos.mpr hdefect))
    (fun w => h.min_mul_norm_sq_le_energyFormH1_self_of_mass_lower_bound_with_parameter ha hb hc
      hb_bound hc_bound hc_lower heps w)

/-- Existence and uniqueness on an arbitrary open domain under the mass-floor condition
`β² < 4λδ`, which makes the energy form coercive
(`TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyFormH1L0_of_mass_lower_bound`). No domain
boundedness, Poincaré inequality, or symmetry of the principal coefficient is required. -/
theorem UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_mass_lower_bound
    [DecidableEq ι] {lam Lam beta gamma delta : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), delta ≤ c x)
    (hmass : beta ^ 2 < 4 * lam * delta) (f : Lp ℝ 2 (mu.restrict Omega)) :
    ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u := by
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  exact existsUnique_isWeakSolutionDirichlet hcoeff
    (h.isCoercive_energyFormH1L0_of_mass_lower_bound ha hb hc hb_bound hc_bound hc_lower hmass
      hcoeff) f

/-! ### Data in `Lʳ` on a domain of finite measure -/

/-- **Weak solvability of the Dirichlet problem with `Lʳ` data.** Let `n ≥ 1` be the dimension
and let `r > 1` with `n (2 - r) < 2 r`, that is `r > 2n/(n + 2)`. On a domain `Ω` of finite
measure, let `a` be measurable and uniformly elliptic, and let `c` be measurable, bounded and
nonnegative. For every `f ∈ Lʳ(Ω)` there is exactly one `w ∈ H¹₀(Ω)` with

`a(w, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,

the weak solution of `-∂ᵢ(aⁱʲ ∂ⱼw) + c w = f` in `Ω`, `w = 0` on `∂Ω`. Unlike
`TauCeti.PDE.existsUnique_isWeakSolutionDirichlet`, the data need not be square integrable. The
range `r > max 1 (2n/(n + 2))` is the one in which `v ↦ ∫_Ω f v` is continuous on `H¹₀(Ω)`
(`TauCeti.W1p0.exists_strongDual_apply_eq_setIntegral_of_memLp`). -/
theorem UniformlyEllipticOn.existsUnique_forall_energyFormH1_eq_setIntegral_of_memLp
    [DecidableEq ι] [Nonempty ι] {lam Lam gamma : ℝ} {r : ℝ≥0} {f : EuclideanSpace ℝ ι → ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), 0 ≤ c x) (hOmega : mu Omega ≠ ∞)
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) * (2 - r) < 2 * r)
    (hf : MemLp f r (mu.restrict Omega)) :
    ∃! w : W1p0 mu Omega 2, ∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 c (w : W1p mu Omega 2) (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
  set ν := mu.restrict (Omega : Set (EuclideanSpace ℝ ι))
  obtain ⟨P, hPfin, hP⟩ : ∃ P : ℝ≥0∞, P ≠ ∞ ∧ ∀ v : W1p0 mu Omega 2,
      eLpNorm (W1p.value (v : W1p mu Omega 2)) 2 ν ≤ P * ‖W1p.gradient (v : W1p mu Omega 2)‖ₑ :=
    ⟨_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by rw [hfin, sub_zero]; positivity) hOmega), fun v =>
      W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt (mu := mu) (q := 2)
        ENNReal.ofNat_ne_top hOmega le_rfl (δ := 0) (by simp) (by rw [hfin]; positivity) v.2⟩
  have hPR : ∀ v : W1p0 mu Omega 2,
      ‖W1p.value (v : W1p mu Omega 2)‖ ≤ P.toReal * ‖W1p.gradient (v : W1p mu Omega 2)‖ :=
    fun v => by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top hPfin enorm_ne_top) (hP v)
      rwa [ENNReal.toReal_mul, toReal_enorm, ← Lp.norm_def] at this
  -- The energy form is coercive on `H¹₀(Ω)`, by the Poincaré inequality.
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (beta := 0)
    h.upper_nonneg ha aestronglyMeasurable_const hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) (fun _ _ => by simp) hc_bound
  have hlower : ∀ w : W1p0 mu Omega 2, lam / (P.toReal ^ 2 + 1) * ‖w‖ ^ 2 ≤
      energyFormH1 a 0 c (w : W1p mu Omega 2) (w : W1p mu Omega 2) := fun w =>
    h.div_mul_norm_sq_le_energyFormH1_self_of_zero_drift (b := 0) ha hc (fun _ _ => rfl)
      hc_bound hc_nonneg (hPR w)
  have hcoer : IsCoercive (energyFormH1L0 hcoeff) :=
    isCoercive_energyFormH1L0 hcoeff (by have := h.pos; positivity) hlower
  obtain ⟨ℓ, hℓ⟩ := W1p0.exists_strongDual_apply_eq_setIntegral_of_memLp hOmega hr
    (by rwa [hfin]) hf
  simpa only [energyFormH1L0_apply, hℓ] using hcoer.existsUnique_forall_eq ℓ

/-! ### The Laplacian model -/

/-- The energy form of the Laplacian model `-Δ` (`a = 1`, no drift, no mass) is the Dirichlet
form `∫_Ω ∇v · ∇u`. -/
@[simp] theorem energyFormH1_one_zero_zero_apply [DecidableEq ι] (u v : W1p mu Omega 2) :
    energyFormH1 (fun _ => 1) 0 0 u v =
      ∫ x in Omega, W1p.gradient v x ⬝ᵥ W1p.gradient u x ∂mu := by
  rw [energyFormH1_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp)

open scoped InnerProductSpace in
/-- The energy form of the Laplacian model `-Δ` is the `L²` inner product of the gradients,
`⟪∇u, ∇v⟫_{L²(Ω)}`. -/
theorem energyFormH1_one_zero_zero_eq_inner [DecidableEq ι] (u v : W1p mu Omega 2) :
    energyFormH1 (fun _ => 1) 0 0 u v = ⟪W1p.gradient u, W1p.gradient v⟫_ℝ := by
  rw [energyFormH1_one_zero_zero_apply, L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [EuclideanSpace.inner_eq_star_dotProduct])

/-- The weak formulation of the Laplacian model `-Δ` is the classical one: `u ∈ H¹₀(Ω)` solves
`-Δu = f` weakly exactly when `∫_Ω ∇v · ∇u = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. -/
theorem isWeakSolutionDirichlet_one_zero_zero_iff [DecidableEq ι]
    (f : Lp ℝ 2 (mu.restrict Omega))
    (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u ↔
      ∀ v : W1p0 mu Omega 2,
        ∫ x in Omega, W1p.gradient (v : W1p mu Omega 2) x ⬝ᵥ
            W1p.gradient (u : W1p mu Omega 2) x ∂mu
          = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  simp only [isWeakSolutionDirichlet_iff, energyFormH1_one_zero_zero_apply]

end Domain

/-! ### Existence on a slab- or ball-contained domain -/

section Euclidean

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {b : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {c : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {lam Lam beta gamma : ℝ}

namespace UniformlyEllipticOn

/-- **Existence and uniqueness for a domain trapped in a slab.** If `Ω ⊆ ℝ^{n+1}` lies between
the hyperplanes `xᵢ = s` and `xᵢ = t`, the principal part is uniformly elliptic with constants
`λ ≤ Λ`, the drift is bounded by `β`, the mass coefficient is bounded by `γ` and nonnegative,
and the drift is small in the sense `β(t - s) < λ`, then the Dirichlet problem has exactly one
weak solution for every `f ∈ L²(Ω)`. The Poincaré constant of the slab is its width, and the
domain need not be bounded: boundedness in one direction is enough. Neither `0 ≤ β` nor `s ≤ t`
is assumed, since either failing forces `Ω` to be empty. -/
theorem existsUnique_isWeakSolutionDirichlet_of_subset_slab
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {i : Fin (n + 1)} {s t : ℝ}
    (hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc s t)
    (hsmall : beta * (t - s) < lam)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet a b c f u := by
  -- Run the argument with the drift bound `max β 0` and the slab `Icc s (max s t)`.
  have hsmall' : max beta 0 * (max s t - s) < lam := by
    have := max_mul_max_lt_of_mul_lt h.pos hsmall
    have e : max (t - s) 0 = max s t - s := by
      rcases le_total s t with hst | hst <;> simp [hst]
    rwa [e] at this
  exact existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (energyFormH1_poincare_constant_pos h.pos (le_max_right beta 0)
      (sub_nonneg.2 (le_max_left s t)) hsmall')
    (fun w => mul_norm_sq_le_energyFormH1_self_of_subset_slab h ha hb hc
      (fun x hx => (hb_bound x hx).trans (le_max_left beta 0)) hc_bound hc_nonneg
      (fun x hx => Icc_subset_Icc_right (le_max_right s t) (hslab x hx)) w.2) f

/-- **Existence and uniqueness for a domain inside a ball.** For `Ω ⊆ B(z, R) ⊆ ℝ^{n+1}` with a
uniformly elliptic principal part, a drift bounded by `β`, a bounded nonnegative mass
coefficient and the smallness condition `2βR < λ`, the Dirichlet problem has exactly one weak
solution for every `f ∈ L²(Ω)`. The Poincaré constant used is the diameter bound `2R`, not the
sharp one, so the smallness condition is not sharp either. Neither `0 ≤ β` nor `0 ≤ R` is
assumed, since either failing forces `Ω` to be empty. -/
theorem existsUnique_isWeakSolutionDirichlet_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hsmall : beta * (2 * R) < lam)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet a b c f u := by
  -- Run the argument with the drift bound `max β 0` and the radius `max R 0`.
  have hsmall' : max beta 0 * (2 * max R 0) < lam := by
    exact max_mul_two_mul_max_lt_of_mul_two_mul_lt h.pos hsmall
  exact existsUnique_isWeakSolutionDirichlet_of_mul_norm_sq_le
    (memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound)
    (energyFormH1_poincare_constant_pos h.pos (le_max_right beta 0) (by positivity) hsmall')
    (fun w => mul_norm_sq_le_energyFormH1_self_of_subset_ball h ha hb hc
      (fun x hx => (hb_bound x hx).trans (le_max_left beta 0)) hc_bound hc_nonneg
      (hball.trans (Metric.ball_subset_ball (le_max_left R 0))) w.2) f

/-- **The Dirichlet problem with boundary values in `H¹(Ω)`, for a domain inside a ball.** Under
the hypotheses of
`TauCeti.PDE.UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball`, for every
`f ∈ L²(Ω)` and every `g ∈ H¹(Ω)` there is exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and
`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`: the weak solution of `L u = f` in `Ω`, `u = g` on
`∂Ω`. -/
theorem existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict Omega))
    (hb : AEStronglyMeasurable b (volume.restrict Omega))
    (hc : AEStronglyMeasurable c (volume.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ gamma)
    (hc_nonneg : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (hsmall : beta * (2 * R) < lam)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (g : W1p volume Omega 2) :
    ∃! u : W1p volume Omega 2, u - g ∈ w1p0Submodule volume Omega 2 ∧
      ∀ v : W1p0 volume Omega 2, energyFormH1 a b c u (v : W1p volume Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x := by
  -- Run the argument with the drift bound `max β 0` and the radius `max R 0`.
  have hsmall' : max beta 0 * (2 * max R 0) < lam := by
    exact max_mul_two_mul_max_lt_of_mul_two_mul_lt h.pos hsmall
  have hcoeff := memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
    (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  exact existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_setIntegral hcoeff
    (isCoercive_energyFormH1L0 hcoeff
      (energyFormH1_poincare_constant_pos h.pos (le_max_right beta 0) (by positivity) hsmall')
      fun w => mul_norm_sq_le_energyFormH1_self_of_subset_ball h ha hb hc
        (fun x hx => (hb_bound x hx).trans (le_max_left beta 0)) hc_bound hc_nonneg
        (hball.trans (Metric.ball_subset_ball (le_max_left R 0))) w.2) f g

end UniformlyEllipticOn

/-! ### The Poisson problem -/

/-- **The Poisson problem on a ball-contained domain.** For `Ω ⊆ B(z, R) ⊆ ℝ^{n+1}` and every
`f ∈ L²(Ω)` there is exactly one `u ∈ H¹₀(Ω)` solving `-Δu = f` in `Ω`, `u = 0` on `∂Ω`,
weakly. This is the constant-coefficient case `a = 1`, `b = 0`, `c = 0` of
`TauCeti.PDE.UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball`, where the
drift smallness condition is vacuous; unfolded through
`TauCeti.PDE.isWeakSolutionDirichlet_one_zero_zero_iff` the equation reads
`∫_Ω ∇v · ∇u = ∫_Ω f v`. It is the existence half of the roadmap's end-to-end acceptance
criterion for the Dirichlet problem on a ball. -/
theorem existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball z R)
    (f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    ∃! u : W1p0 volume Omega 2, IsWeakSolutionDirichlet (fun _ => 1) 0 0 f u :=
  UniformlyEllipticOn.existsUnique_isWeakSolutionDirichlet_of_subset_ball
    (uniformlyEllipticOn_const_one_one _) aestronglyMeasurable_const aestronglyMeasurable_const
    aestronglyMeasurable_const (beta := 0) (fun _ _ => by simp) (gamma := 0)
    (fun _ _ => by simp) (fun _ _ => le_rfl) hball (by simp) f

end Euclidean

end PDE

end TauCeti
