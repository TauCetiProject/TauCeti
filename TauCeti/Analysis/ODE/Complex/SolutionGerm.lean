/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Complex.LinearEquation
public import TauCeti.Analysis.Calculus.IteratedDeriv.Germ
import TauCeti.Analysis.ODE.Complex.OrdinaryPoint

/-!
# Solution germs of analytic linear equations and the local initial-value theorem

For a monic analytic equation `E : TauCeti.LinearEquation U n` and a point `a ∈ U`,
`E.solutionGerms ha` is the complex subspace of function germs at `a` represented by a function
that is analytic near `a` and solves `E` there (`LinearEquation.IsSolutionNear`). The unscaled
initial jet `(y(a), y'(a), …, y⁽ⁿ⁻¹⁾(a))` depends only on the germ, giving the linear map
`LinearEquation.initialJetGerm`.

The main result is the analytic linear initial-value theorem in germ form:
`LinearEquation.initialJetGermEquiv` is a complex linear equivalence between the solution germs at
`a` and `Fin n → ℂ`. Its inverse solves the equation with a prescribed jet, and its values at the
standard coordinate vectors form the normalized fundamental basis
`LinearEquation.fundamentalBasis`. Germs of solutions on the domain are compared with solution
germs by `LinearEquation.toSolutionGerms`; on a disc centred at `a` this is the linear equivalence
`LinearEquation.solutionSpaceEquivSolutionGermsBall`, compatible with the disc initial-value
theorem `LinearEquation.initialJetEquivBall`.
`LinearEquation.IsSolutionNear.exists_isSolutionNear_eball` extends a local solution at any point of
a disc of extended nonnegative radius contained in the coefficient domain throughout that disc.

Solution germs are what analytic continuation of solutions transports along paths, and what
global solutions on simply connected domains are assembled from.

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, §4.3, Theorem 4.7.
-/

public noncomputable section

open Filter Set Topology TopologicalSpace
open scoped ENNReal

namespace TauCeti.LinearEquation

variable {U : Opens ℂ} {n : ℕ} (E : LinearEquation U n)

/-- A scalar representative `y` solves `E` near `a`: at every point of some neighbourhood of `a`,
the point lies in the domain, `y` is analytic there, and `y` satisfies the equation there. -/
def IsSolutionNear (a : ℂ) (y : ℂ → ℂ) : Prop :=
  ∀ᶠ z in 𝓝 a, z ∈ U ∧ AnalyticAt ℂ y z ∧
    iteratedDeriv n y z + ∑ j, HolomorphicFunctions.extend (E.coeff j) z *
      iteratedDeriv j y z = 0

variable {E} {a : ℂ} {y f g : ℂ → ℂ}

/-- Being a solution near `a` is the eventual conjunction of domain membership, analyticity and
the homogeneous equation. -/
theorem isSolutionNear_iff :
    E.IsSolutionNear a y ↔ ∀ᶠ z in 𝓝 a, z ∈ U ∧ AnalyticAt ℂ y z ∧
      iteratedDeriv n y z + ∑ j, HolomorphicFunctions.extend (E.coeff j) z *
        iteratedDeriv j y z = 0 := (Iff.rfl)

/-- A function solving the equation near `a` forces `a` into the domain. -/
theorem IsSolutionNear.mem (hy : E.IsSolutionNear a y) : a ∈ U :=
  hy.self_of_nhds.1

/-- A function solving the equation near `a` is analytic at `a`. -/
theorem IsSolutionNear.analyticAt (hy : E.IsSolutionNear a y) : AnalyticAt ℂ y a :=
  hy.self_of_nhds.2.1

/-- Being a solution near `a` depends only on the germ of the representative at `a`. -/
theorem IsSolutionNear.congr (hy : E.IsSolutionNear a y) (hyf : y =ᶠ[𝓝 a] f) :
    E.IsSolutionNear a f := by
  filter_upwards [hy, hyf.eventuallyEq_nhds] with z ⟨hzU, han, heq⟩ hz
  refine ⟨hzU, han.congr hz, ?_⟩
  simpa only [hz.iteratedDeriv_eq] using heq

/-- A solution on the whole domain solves the equation near each point of the domain. -/
theorem IsSolution.isSolutionNear (hy : E.IsSolution y) (ha : a ∈ U) :
    E.IsSolutionNear a y := by
  filter_upwards [U.isOpen.mem_nhds ha] with z hz
  exact ⟨hz, hy.analyticOnNhd z hz, hy.eq_zero z hz⟩

/-- The zero function solves every equation near each point of the domain. -/
theorem isSolutionNear_zero (ha : a ∈ U) : E.IsSolutionNear a 0 :=
  isSolution_zero.isSolutionNear ha

/-- Sums of local solutions are local solutions. -/
theorem IsSolutionNear.add (hf : E.IsSolutionNear a f) (hg : E.IsSolutionNear a g) :
    E.IsSolutionNear a (f + g) := by
  filter_upwards [hf, hg] with z ⟨hzU, hfz, hf0⟩ ⟨_, hgz, hg0⟩
  refine ⟨hzU, hfz.add hgz, ?_⟩
  simp only [iteratedDeriv_add hfz.contDiffAt hgz.contDiffAt, mul_add, Finset.sum_add_distrib]
  linear_combination hf0 + hg0

/-- Constant complex multiples of local solutions are local solutions. -/
theorem IsSolutionNear.const_smul (hf : E.IsSolutionNear a f) (c : ℂ) :
    E.IsSolutionNear a (c • f) := by
  filter_upwards [hf] with z ⟨hzU, hfz, hf0⟩
  refine ⟨hzU, hfz.const_smul, ?_⟩
  simp only [iteratedDeriv_const_smul_field, smul_eq_mul]
  simpa [Finset.mul_sum, mul_add, mul_left_comm] using congrArg (c * ·) hf0

/-- On a smaller open domain containing `a`, the restricted equation has the same local solutions
near `a`. -/
@[simp]
theorem isSolutionNear_restrict_iff {V : Opens ℂ} (h : V ≤ U) (ha : a ∈ V) :
    (E.restrict h).IsSolutionNear a y ↔ E.IsSolutionNear a y := by
  constructor
  · intro hy
    filter_upwards [hy] with z ⟨hzV, hyz, hy0⟩
    exact ⟨h hzV, hyz, by simpa only [E.extend_restrict_coeff_of_mem h hzV] using hy0⟩
  · intro hy
    filter_upwards [hy, V.isOpen.mem_nhds ha] with z ⟨_, hyz, hy0⟩ hzV
    exact ⟨hzV, hyz, by simpa only [E.extend_restrict_coeff_of_mem h hzV] using hy0⟩

/-- A function solves the equation near `a` exactly when it solves the restriction of the equation
to some positive-radius disc about `a` inside the domain. -/
theorem isSolutionNear_iff_exists_ball :
    E.IsSolutionNear a y ↔ ∃ r > 0, ∃ h : (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens ℂ) ≤ U,
      (E.restrict h).IsSolution y := by
  constructor
  · intro hy
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hy
    have h : (⟨Metric.ball a r, Metric.isOpen_ball⟩ : Opens ℂ) ≤ U := fun z hz ↦ (hball z hz).1
    refine ⟨r, hr, h, (isSolution_iff _ _).mpr ⟨fun z hz ↦ (hball z hz).2.1, fun z hz ↦ ?_⟩⟩
    simpa only [E.extend_restrict_coeff_of_mem h hz] using (hball z hz).2.2
  · rintro ⟨r, hr, h, hy⟩
    exact (isSolutionNear_restrict_iff h (Metric.mem_ball_self hr)).mp
      (hy.isSolutionNear (Metric.mem_ball_self hr))

/-! ### The space of solution germs -/

variable (E) in
/-- The complex subspace of function germs at a point `a` of the domain represented by a local
solution of `E` near `a`. -/
def solutionGerms (ha : a ∈ U) : Submodule ℂ (Germ (𝓝 a) ℂ) where
  carrier := {φ | ∃ y : ℂ → ℂ, E.IsSolutionNear a y ∧ (y : Germ (𝓝 a) ℂ) = φ}
  zero_mem' := ⟨0, isSolutionNear_zero ha, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    exact ⟨c • f, hf.const_smul c, rfl⟩

/-- Membership in the solution germs means having a representative solving the equation near the
base point. -/
theorem mem_solutionGerms_iff (ha : a ∈ U) {φ : Germ (𝓝 a) ℂ} :
    φ ∈ E.solutionGerms ha ↔ ∃ y : ℂ → ℂ, E.IsSolutionNear a y ∧ (y : Germ (𝓝 a) ℂ) = φ :=
  Iff.rfl

/-- The germ of a function is a solution germ exactly when the function solves the equation near
the base point. -/
@[simp]
theorem coe_mem_solutionGerms (ha : a ∈ U) :
    (y : Germ (𝓝 a) ℂ) ∈ E.solutionGerms ha ↔ E.IsSolutionNear a y :=
  ⟨fun ⟨_, hf, hfy⟩ ↦ hf.congr (Germ.coe_eq.mp hfy), fun hy ↦ ⟨y, hy, rfl⟩⟩

/-- The solution germs of a restricted equation at a point of the smaller domain are the solution
germs of the original equation. -/
@[simp]
theorem solutionGerms_restrict {V : Opens ℂ} (h : V ≤ U) (ha : a ∈ V) :
    (E.restrict h).solutionGerms ha = E.solutionGerms (h ha) := by
  ext φ
  simp only [mem_solutionGerms_iff, isSolutionNear_restrict_iff h ha]

variable (E) in
/-- The unscaled initial jet `(y(a), y'(a), …, y⁽ⁿ⁻¹⁾(a))` of a solution germ at `a`. It is
computed on any representative, and no factorials enter it. -/
def initialJetGerm (ha : a ∈ U) : E.solutionGerms ha →ₗ[ℂ] (Fin n → ℂ) where
  toFun φ := (φ : Germ (𝓝 a) ℂ).iteratedDerivJet n
  map_add' := by
    rintro ⟨_, f, hf, rfl⟩ ⟨_, g, hg, rfl⟩
    funext j
    simp only [Submodule.coe_add, ← Germ.coe_add, Germ.iteratedDerivJet_coe, Pi.add_apply]
    exact iteratedDeriv_add hf.analyticAt.contDiffAt hg.analyticAt.contDiffAt
  map_smul' := by
    rintro c ⟨_, f, hf, rfl⟩
    funext j
    simp only [Submodule.coe_smul, ← Germ.coe_smul, Germ.iteratedDerivJet_coe, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    exact iteratedDeriv_const_smul_field c f

/-- The components of the initial jet of a solution germ are the iterated derivatives of any of
its representatives at the base point. -/
theorem initialJetGerm_apply (ha : a ∈ U) (φ : E.solutionGerms ha) (hφ : (φ : Germ (𝓝 a) ℂ) = y)
    (j : Fin n) : E.initialJetGerm ha φ j = iteratedDeriv j y a := by
  simp only [initialJetGerm, LinearMap.coe_mk, AddHom.coe_mk, hφ, Germ.iteratedDerivJet_coe]

/-- The initial jet of the germ of a local solution is its vector of unscaled derivatives. -/
@[simp]
theorem initialJetGerm_mk (ha : a ∈ U) (hy : (y : Germ (𝓝 a) ℂ) ∈ E.solutionGerms ha)
    (j : Fin n) : E.initialJetGerm ha ⟨y, hy⟩ j = iteratedDeriv j y a :=
  initialJetGerm_apply ha _ rfl j

/-- Solution germs with the same initial jet are equal: two local solutions with the same unscaled
`n`-jet at `a` agree on a neighbourhood of `a`. -/
theorem initialJetGerm_injective (ha : a ∈ U) : Function.Injective (E.initialJetGerm ha) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ h0
  obtain ⟨y, hy, hφ⟩ := φ.property
  obtain ⟨r, hr, h, hyr⟩ := isSolutionNear_iff_exists_ball.mp hy
  have heq := hyr.eqOn_of_isPreconnected_of_iteratedDeriv_eq (convex_ball a r).isPreconnected
    isSolution_zero (Metric.mem_ball_self hr) fun j ↦ by
      rw [← initialJetGerm_apply ha φ hφ.symm j, h0]
      simp
  refine Subtype.ext ?_
  rw [← hφ, Submodule.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
  filter_upwards [Metric.ball_mem_nhds a hr] with z hz using heq hz

/-- Every unscaled initial jet at `a` is the jet of a solution germ: the restriction of the
equation to a disc about `a` inside the domain has a solution with that jet. -/
theorem initialJetGerm_surjective (ha : a ∈ U) : Function.Surjective (E.initialJetGerm ha) := by
  intro c
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen a ha
  let E' := E.restrict (V := ⟨Metric.ball a r, Metric.isOpen_ball⟩) hball
  obtain ⟨y, hy, hyc, -⟩ := E'.exists_isSolution_ball c
  have hloc : E.IsSolutionNear a y :=
    (isSolutionNear_restrict_iff hball (Metric.mem_ball_self hr)).mp
      (hy.isSolutionNear (Metric.mem_ball_self hr))
  exact ⟨⟨y, (coe_mem_solutionGerms ha).mpr hloc⟩, funext fun j ↦ by simp [hyc]⟩

variable (E) in
/-- **The analytic linear initial-value theorem in germ form.** At a point `a` of the domain, the
unscaled initial jet is a complex linear equivalence between the solution germs at `a` and
`Fin n → ℂ`: every jet has exactly one solution germ. -/
def initialJetGermEquiv (ha : a ∈ U) : E.solutionGerms ha ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (E.initialJetGerm ha)
    ⟨initialJetGerm_injective ha, initialJetGerm_surjective ha⟩

/-- The forward map of `initialJetGermEquiv` evaluates the unscaled initial jet. -/
@[simp]
theorem initialJetGermEquiv_apply (ha : a ∈ U) (φ : E.solutionGerms ha) :
    E.initialJetGermEquiv ha φ = E.initialJetGerm ha φ := (rfl)

/-- The inverse of `initialJetGermEquiv` has the prescribed initial jet. -/
@[simp]
theorem initialJetGerm_initialJetGermEquiv_symm (ha : a ∈ U) (c : Fin n → ℂ) :
    E.initialJetGerm ha ((E.initialJetGermEquiv ha).symm c) = c :=
  (E.initialJetGermEquiv ha).apply_symm_apply c

/-- The inverse of `initialJetGermEquiv` sends a jet to the germ of any local solution with that
unscaled initial jet. -/
theorem initialJetGermEquiv_symm_apply (ha : a ∈ U) {c : Fin n → ℂ}
    (hy : E.IsSolutionNear a y) (hyc : ∀ j : Fin n, iteratedDeriv j y a = c j) :
    ((E.initialJetGermEquiv ha).symm c : Germ (𝓝 a) ℂ) = y := by
  have hmem := (coe_mem_solutionGerms ha).mpr hy
  have hc : c = E.initialJetGermEquiv ha ⟨y, hmem⟩ :=
    funext fun j ↦ by simp [hyc]
  rw [hc, LinearEquiv.symm_apply_apply]

/-- The solution germs at a point of the domain form an `n`-dimensional complex space. -/
theorem finrank_solutionGerms (ha : a ∈ U) : Module.finrank ℂ (E.solutionGerms ha) = n := by
  simpa using (E.initialJetGermEquiv ha).finrank_eq

variable (E) in
/-- The normalized fundamental basis of solution germs at `a`: the `j`-th basis germ has unscaled
initial jet the `j`-th standard coordinate vector. -/
def fundamentalBasis (ha : a ∈ U) : Module.Basis (Fin n) ℂ (E.solutionGerms ha) :=
  (Pi.basisFun ℂ (Fin n)).map (E.initialJetGermEquiv ha).symm

/-- The initial jet of the `i`-th fundamental solution germ is the `i`-th standard basis vector. -/
@[simp]
theorem initialJetGerm_fundamentalBasis (ha : a ∈ U) (i : Fin n) :
    E.initialJetGerm ha (E.fundamentalBasis ha i) = Pi.single i 1 := by
  simp [fundamentalBasis]

/-- Coordinates in the normalized fundamental basis are the components of the initial jet. -/
@[simp]
theorem fundamentalBasis_repr (ha : a ∈ U) (φ : E.solutionGerms ha) (i : Fin n) :
    (E.fundamentalBasis ha).repr φ i = E.initialJetGerm ha φ i := by
  simp [fundamentalBasis]

/-! ### Comparison with solutions on open domains -/

variable (E) in
/-- The germ at a point `a` of the domain of a bundled solution on the whole domain. -/
def toSolutionGerms (ha : a ∈ U) : E.solutionSpace →ₗ[ℂ] E.solutionGerms ha where
  toFun f := ⟨HolomorphicFunctions.extend f.val,
    (coe_mem_solutionGerms ha).mpr (((E.mem_solutionSpace _).mp f.property).isSolutionNear ha)⟩
  map_add' f g := Subtype.ext <| by
    simp only [Submodule.coe_add, ← Germ.coe_add]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [U.isOpen.mem_nhds ha] with z hz
    simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩, Subalgebra.coe_add]
  map_smul' c f := Subtype.ext <| by
    simp only [Submodule.coe_smul, RingHom.id_apply, ← Germ.coe_smul]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [U.isOpen.mem_nhds ha] with z hz
    simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩]

/-- The germ of a bundled solution is represented by its zero extension. -/
@[simp]
theorem coe_toSolutionGerms (ha : a ∈ U) (f : E.solutionSpace) :
    (E.toSolutionGerms ha f : Germ (𝓝 a) ℂ) = HolomorphicFunctions.extend f.val := (rfl)

/-- Taking germs preserves the unscaled initial jet. -/
@[simp]
theorem initialJetGerm_toSolutionGerms (ha : a ∈ U) (f : E.solutionSpace) :
    E.initialJetGerm ha (E.toSolutionGerms ha f) = E.initialJet ha f :=
  funext fun j ↦ (initialJetGerm_apply ha _ (coe_toSolutionGerms ha f) j).trans
    (initialJet_apply (E := E) ha f j).symm

/-- On a preconnected domain, a bundled solution is determined by its germ at any point. -/
theorem toSolutionGerms_injective_of_isPreconnected (hU : IsPreconnected (U : Set ℂ))
    (ha : a ∈ U) : Function.Injective (E.toSolutionGerms ha) := by
  intro f g hfg
  apply E.initialJet_injective_of_isPreconnected hU ha
  rw [← initialJetGerm_toSolutionGerms, hfg, initialJetGerm_toSolutionGerms]

/-- **Germs of disc solutions.** On a positive-radius disc, taking germs at the centre is a linear
equivalence from the bundled solutions on the disc onto the solution germs at the centre. -/
def solutionSpaceEquivSolutionGermsBall {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ n) :
    E.solutionSpace ≃ₗ[ℂ] E.solutionGerms (Metric.mem_ball_self hr) :=
  (E.initialJetEquivBall hr).trans (E.initialJetGermEquiv (Metric.mem_ball_self hr)).symm

/-- The disc comparison `solutionSpaceEquivSolutionGermsBall` takes the germ at the centre. -/
@[simp]
theorem solutionSpaceEquivSolutionGermsBall_apply {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (E : LinearEquation ⟨Metric.ball z₀ r, Metric.isOpen_ball⟩ n) (f : E.solutionSpace) :
    E.solutionSpaceEquivSolutionGermsBall hr f = E.toSolutionGerms (Metric.mem_ball_self hr) f := by
  rw [solutionSpaceEquivSolutionGermsBall, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq,
    initialJetGermEquiv_apply, initialJetGerm_toSolutionGerms, initialJetEquivBall_apply]

/-- A local solution at any point of a disc of extended nonnegative radius inside the coefficient
domain extends throughout the disc, with the same germ at that point. The radius may be infinite. -/
theorem IsSolutionNear.exists_isSolutionNear_eball {a c : ℂ} {f : ℂ → ℂ} {r : ℝ≥0∞}
    (hf : E.IsSolutionNear a f)
    (hball : (⟨Metric.eball c r, Metric.isOpen_eball⟩ : Opens ℂ) ≤ U)
    (ha : a ∈ Metric.eball c r) :
    ∃ g : ℂ → ℂ, (∀ z ∈ Metric.eball c r, E.IsSolutionNear z g) ∧ g =ᶠ[𝓝 a] f := by
  let V : Opens ℂ := ⟨Metric.eball c r, Metric.isOpen_eball⟩
  have hV : (V : Set ℂ) = Metric.eball c r := rfl
  have haV : a ∈ V := Opens.mem_mk.mpr ha
  let E' := E.restrict hball
  let s := (E'.initialJetEquivOfEqEBall hV haV).symm (fun j ↦ iteratedDeriv j f a)
  have hf' : E'.IsSolutionNear a f := (isSolutionNear_restrict_iff hball haV).mpr hf
  have hs := (E'.mem_solutionSpace _).mp s.property
  refine ⟨HolomorphicFunctions.extend s.val, fun z hz ↦ ?_, ?_⟩
  · have hzV : z ∈ V := Opens.mem_mk.mpr hz
    exact (isSolutionNear_restrict_iff hball hzV).mp (hs.isSolutionNear hzV)
  · apply Germ.coe_eq.mp
    exact (initialJetGermEquiv_symm_apply haV (hs.isSolutionNear haV)
      (E'.iteratedDeriv_extend_initialJetEquivOfEqEBall_symm hV haV _)).symm.trans
        (initialJetGermEquiv_symm_apply haV hf' fun _ ↦ rfl)

/-! The following checks fix the unscaled-jet convention of the inverse equivalence. -/

/-- For `y' = 0`, the inverse sends `c` to the constant germ `c 0`. -/
example (ha : a ∈ U) (c : Fin 1 → ℂ) :
    (((⟨by omega, fun _ ↦ 0⟩ : LinearEquation U 1).initialJetGermEquiv ha).symm c :
      Germ (𝓝 a) ℂ) = (fun _ ↦ c 0 : ℂ → ℂ) := by
  refine initialJetGermEquiv_symm_apply ha ?_ fun j ↦ by fin_cases j; simp
  filter_upwards [U.isOpen.mem_nhds ha] with z hz
  exact ⟨hz, analyticAt_const, by simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩]⟩

/-- For `y'' = 0`, the inverse sends `(u, v)` to the germ of `u + v (x - a)`. -/
example (ha : a ∈ U) (u v : ℂ) :
    (((⟨by omega, fun _ ↦ 0⟩ : LinearEquation U 2).initialJetGermEquiv ha).symm ![u, v] :
      Germ (𝓝 a) ℂ) = (fun x ↦ u + v * (x - a) : ℂ → ℂ) := by
  refine initialJetGermEquiv_symm_apply ha ?_ fun j ↦ ?_
  · filter_upwards [U.isOpen.mem_nhds ha] with z hz
    refine ⟨hz, by fun_prop, ?_⟩
    simp [HolomorphicFunctions.extend_apply _ ⟨z, hz⟩, iteratedDeriv_succ]
  · fin_cases j <;> simp [iteratedDeriv_succ]

/-- For `y''' = 0` at zero, the jet `(0, 0, 2)` corresponds to `x²`, not to `2 x²`. -/
example :
    (((⟨by omega, fun _ ↦ 0⟩ : LinearEquation (⊤ : Opens ℂ) 3).initialJetGermEquiv
      (a := 0) (by simp)).symm ![0, 0, 2] : Germ (𝓝 (0 : ℂ)) ℂ) = (fun x ↦ x ^ 2 : ℂ → ℂ) := by
  refine initialJetGermEquiv_symm_apply _ ?_ fun j ↦ ?_
  · filter_upwards with z
    refine ⟨by simp, by fun_prop, ?_⟩
    simp [HolomorphicFunctions.extend_apply (0 : holomorphicFunctions ⊤) ⟨z, trivial⟩,
      iteratedDeriv_pow]
  · fin_cases j <;> simp [iteratedDeriv_pow]

end TauCeti.LinearEquation
