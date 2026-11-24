/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov

/-!
# The pure Neumann problem

Let `Ω` be an open set of finite measure, `a` an essentially bounded coefficient field with
`λ‖ξ‖² ≤ ξ · a(x) ξ` almost everywhere on `Ω` for some `λ > 0`, and `B(u, v) = ∫_Ω ∇v · a ∇u` the
energy form of `-div(a ∇u)` on `H¹(Ω)`, with no drift and no mass term. The **weak Neumann
problem** for a continuous linear functional `ℓ` on `H¹(Ω)` asks for `u ∈ H¹(Ω)` with

`B(u, v) = ℓ(v)` for every `v ∈ H¹(Ω)`.

The test space is all of `H¹(Ω)` and no boundary values are imposed: the boundary condition is the
natural one, `a ∇u · ν = 0` for `ℓ(v) = ∫_Ω f v`, and more generally a boundary integral
`∫_{∂Ω} h v` in `ℓ` prescribes the conormal derivative `h`. Testing against the constant `1`, which
lies in `H¹(Ω)` and has gradient zero, shows that `ℓ(1) = 0` is necessary. This file proves that it
is also sufficient when `Ω` is connected and the value map `H¹(Ω) → L²(Ω)` is compact, as on a
bounded Lipschitz domain, and that the solution is then unique up to an additive constant.

The proof follows the classical route. On the closed subspace of `H¹(Ω)` of functions with
integral zero over `Ω`, the gradient controls the full `H¹` norm by the Poincaré–Wirtinger
inequality `TauCeti.W1p.exists_pos_mul_norm_le_norm_gradient_of_isCompactOperator`. So `B` is
coercive on that subspace and Lax–Milgram gives a unique solution there. Every `v ∈ H¹(Ω)` is a
function of integral zero plus a constant, and both `B(u, ·)` and `ℓ` vanish on constants, so the
solution tests correctly against all of `H¹(Ω)`. Two solutions differ by a function `w` with
`B(w, w) = 0`, hence `∇w = 0`, and `w` is constant on the connected domain.

Neither hypothesis can be dropped. On `Ω = (0, 1) ∪ (2, 3)` the indicator of `(0, 1)` minus that of
`(2, 3)` has gradient zero, so `ℓ(v) = ∫_Ω v (1_{(0,1)} - 1_{(2,3)})` satisfies `ℓ(1) = 0` but has
no solution, and solutions differ by locally constant functions. Without compactness the
Poincaré–Wirtinger inequality fails (for instance on a chain of rooms joined by ever thinner
passages) and the range of the Neumann operator is not closed.

## Main declarations

* `TauCeti.PDE.existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq`: for `ℓ(1) = 0`, the
  Neumann problem has exactly one solution of integral zero.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_iff`: the Neumann problem is solvable exactly when
  `ℓ(1) = 0`.
* `TauCeti.PDE.forall_energyFormH1_eq_iff_exists_eq_add_const`: on a connected domain, two
  functions have the same Neumann data exactly when they differ by a constant.
* `TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_iff`: for `f ∈ L²(Ω)`, the problem
  `-div(a ∇u) = f`, `a ∇u · ν = 0` is weakly solvable exactly when `∫_Ω f = 0`.
* `Set.IsLipschitzDomain.exists_forall_energyFormH1_eq_setIntegral_iff`: the same on every bounded
  connected Lipschitz domain, through Rellich–Kondrachov compactness
  `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomain`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Proposition 9.24 and Problem 47.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.1, Theorem 1 (Poincaré–Wirtinger),
  and §6.2.2 (the energy method).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Matrix

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam : ℝ}

-- The shortcut instances of the energy-form file, so that the operator norm of the bundled
-- energy form `TauCeti.PDE.energyFormH1L` is found by instance search.
attribute [local instance] instSeminormedAddCommGroupW1p instNormedSpaceW1p

section FiniteMeasure

variable [IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))]

/-- The kernel of the integral over `Ω` consists of the functions of integral zero. -/
private theorem mem_ker_setIntegralL_iff {u : W1p mu Omega 2} :
    u ∈ LinearMap.ker (W1p.setIntegralL (mu := mu) (Omega := Omega) (p := 2)
      (Omega : Set (EuclideanSpace ℝ ι)) (measure_lt_top _ _) : W1p mu Omega 2 →ₗ[ℝ] ℝ) ↔
      ∫ x in Omega, W1p.value u x ∂mu = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, W1p.setIntegralL_apply,
    Measure.restrict_restrict_of_subset subset_rfl]

/-- Subtracting its mean from a function of `H¹(Ω)` leaves a function of integral zero. On a null
set both the integral and the measure vanish, and nothing is subtracted. -/
private theorem sub_smul_const_one_mem_ker_setIntegralL (v : W1p mu Omega 2) :
    v - (W1p.setIntegralL (Omega : Set (EuclideanSpace ℝ ι)) (measure_lt_top _ _) v /
        mu.real Omega) • W1p.const 1 ∈
      LinearMap.ker (W1p.setIntegralL (mu := mu) (Omega := Omega) (p := 2)
        (Omega : Set (EuclideanSpace ℝ ι)) (measure_lt_top _ _) : W1p mu Omega 2 →ₗ[ℝ] ℝ) := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, map_smul, W1p.setIntegralL_const,
    measureReal_restrict_apply_self, mul_one, smul_eq_mul, div_mul_cancel_of_imp, sub_self]
  intro h0
  rw [measureReal_eq_zero_iff (isFiniteMeasure_restrict.1 inferInstance)] at h0
  rw [W1p.setIntegralL_apply, Measure.restrict_restrict_of_subset subset_rfl,
    setIntegral_measure_zero _ h0]

/-- **Poincaré–Wirtinger for functions of integral zero.** On a connected domain with compact
value map, the gradient controls the `H¹` norm on the functions of integral zero over `Ω`. -/
private theorem exists_pos_mul_norm_le_norm_gradient
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι))) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : W1p mu Omega 2, ∫ x in Omega, W1p.value u x ∂mu = 0 →
      c * ‖u‖ ≤ ‖W1p.gradient u‖ := by
  rcases eq_or_ne (mu Omega) 0 with h0 | h0
  · -- On a null set every Sobolev function vanishes.
    refine ⟨1, one_pos, fun u _ => ?_⟩
    have hu : u = 0 := by
      refine W1p.ext_value (Lp.ext ?_)
      rw [Filter.EventuallyEq, ae_eq_bot.2 (Measure.restrict_eq_zero.2 h0)]
      exact Filter.eventually_bot
    simp [hu]
  exact W1p.exists_pos_mul_norm_le_norm_gradient_of_isCompactOperator hK hconn
    (isFiniteMeasure_restrict.1 inferInstance) subset_rfl h0

/-- **The Neumann problem has a unique solution of integral zero.** Let `Ω` be connected with
compact value map `H¹(Ω) → L²(Ω)`, let `a` be essentially bounded with `λ‖ξ‖² ≤ ξ · a(x) ξ` almost
everywhere on `Ω` for some `λ > 0`, and let `ℓ` be a continuous linear functional on `H¹(Ω)` with
`ℓ(1) = 0`. Then exactly one `u ∈ H¹(Ω)` with `∫_Ω u = 0` satisfies

`∫_Ω ∇v · a ∇u = ℓ(v)` for every `v ∈ H¹(Ω)`. -/
theorem existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    {ℓ : StrongDual ℝ (W1p mu Omega 2)} (hℓ : ℓ (W1p.const 1) = 0) :
    ∃! u : W1p mu Omega 2, ∫ x in Omega, W1p.value u x ∂mu = 0 ∧
      ∀ v : W1p mu Omega 2, energyFormH1 a 0 0 u v = ℓ v := by
  -- The energy form is coercive on the functions of integral zero.
  obtain ⟨c, hc, hcM⟩ := exists_pos_mul_norm_le_norm_gradient hK hconn
  set I := W1p.setIntegralL (mu := mu) (Omega := Omega) (p := 2)
    (Omega : Set (EuclideanSpace ℝ ι)) (measure_lt_top _ _)
  set M := LinearMap.ker (I : W1p mu Omega 2 →ₗ[ℝ] ℝ)
  -- Shortcut instances: the nested Sobolev subtypes make their synthesis slow.
  let : NormedAddCommGroup M := inferInstance
  let : InnerProductSpace ℝ M := inferInstance
  have : CompleteSpace M := I.isClosed_ker.completeSpace_coe
  let BM : M →L[ℝ] M →L[ℝ] ℝ :=
    (energyFormH1L (b := 0) (c := 0) hcoeff).bilinearComp M.subtypeL M.subtypeL
  have hBM (w v : M) : BM w v = energyFormH1 a 0 0 (w : W1p mu Omega 2) v := by
    simp [BM, Pi.zero_def]
  have hcoer : IsCoercive BM := by
    refine ⟨lam * c ^ 2, by positivity, fun w => ?_⟩
    rw [hBM]
    calc lam * c ^ 2 * ‖w‖ * ‖w‖ = lam * (c * ‖(w : W1p mu Omega 2)‖) ^ 2 := by
          rw [Submodule.norm_coe]; ring
      _ ≤ lam * ‖W1p.gradient (w : W1p mu Omega 2)‖ ^ 2 := by
          gcongr
          exact hcM w (mem_ker_setIntegralL_iff.1 w.property)
      _ ≤ _ := mul_norm_gradient_sq_le_energyFormH1_self_of_ae_lower_bound hcoeff ha w
  obtain ⟨w, hw, huniq⟩ := hcoer.existsUnique_forall_eq (ℓ.comp M.subtypeL)
  -- Every `v` is a function of integral zero plus a multiple of `1`, on which both sides vanish.
  have hsol (u : M) (hu : ∀ v : M, BM u v = (ℓ.comp M.subtypeL) v) (v : W1p mu Omega 2) :
      energyFormH1 a 0 0 (u : W1p mu Omega 2) v = ℓ v := by
    simpa [hBM, energyFormH1_sub_right (b := 0) (c := 0) hcoeff, hℓ] using
      hu ⟨_, sub_smul_const_one_mem_ker_setIntegralL v⟩
  refine ⟨w, ⟨mem_ker_setIntegralL_iff.1 w.property, hsol w hw⟩, ?_⟩
  rintro u ⟨hu0, hu⟩
  exact congrArg Subtype.val (huniq ⟨u, mem_ker_setIntegralL_iff.2 hu0⟩ fun v => by
    rw [hBM, hu, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply])

/-- **Solvability of the Neumann problem.** Under the hypotheses of
`TauCeti.PDE.existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq`, for a continuous linear
functional `ℓ` on `H¹(Ω)` there is `u ∈ H¹(Ω)` with `∫_Ω ∇v · a ∇u = ℓ(v)` for every
`v ∈ H¹(Ω)` exactly when `ℓ(1) = 0`. For `ℓ(v) = ∫_Ω f v + ∫_{∂Ω} h v`, the boundary integral
taken against the trace of `v`, this is the compatibility condition `∫_Ω f + ∫_{∂Ω} h = 0` between
the source and the prescribed conormal derivative. -/
theorem exists_forall_energyFormH1_eq_iff
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (ℓ : StrongDual ℝ (W1p mu Omega 2)) :
    (∃ u : W1p mu Omega 2, ∀ v, energyFormH1 a 0 0 u v = ℓ v) ↔ ℓ (W1p.const 1) = 0 := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun hℓ => ?_⟩
  · rw [← hu, energyFormH1_const_right]
  · obtain ⟨u, ⟨-, hu⟩, -⟩ :=
      existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq hcoeff hlam ha hK hconn hℓ
    exact ⟨u, hu⟩

/-- **Uniqueness up to constants for the Neumann problem.** On a connected domain, if `a` is
essentially bounded with `λ‖ξ‖² ≤ ξ · a(x) ξ` almost everywhere on `Ω` for some `λ > 0`, two
functions `u, u' ∈ H¹(Ω)` satisfy `∫_Ω ∇v · a ∇u = ∫_Ω ∇v · a ∇u'` for every `v ∈ H¹(Ω)`
exactly when `u - u'` is constant. No compactness is needed. -/
theorem forall_energyFormH1_eq_iff_exists_eq_add_const
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι))) {u u' : W1p mu Omega 2} :
    (∀ v, energyFormH1 a 0 0 u v = energyFormH1 a 0 0 u' v) ↔
      ∃ c : ℝ, u = u' + W1p.const c := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ v => by rw [hc, energyFormH1_add_const_left]⟩
  -- The difference has zero energy, hence zero gradient, hence is constant.
  have hw : energyFormH1 a 0 0 (u - u') (u - u') = 0 := by
    rw [energyFormH1_sub_left (b := 0) (c := 0) hcoeff, h, sub_self]
  have hgrad : W1p.gradient (u - u') = 0 := by
    have hle := mul_norm_gradient_sq_le_energyFormH1_self_of_ae_lower_bound hcoeff ha (u - u')
    rw [hw] at hle
    have : ‖W1p.gradient (u - u')‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1
      (le_antisymm this (sq_nonneg _)))
  obtain ⟨c, hc⟩ := W1p.exists_eq_const_of_gradient_eq_zero hconn hgrad
  exact ⟨c, by rw [← hc, add_sub_cancel]⟩

/-- **The Neumann problem with an `L²` source.** Under the hypotheses of
`TauCeti.PDE.existsUnique_setIntegral_eq_zero_and_forall_energyFormH1_eq`, for `f ∈ L²(Ω)` the
problem `-div(a ∇u) = f` in `Ω`, `a ∇u · ν = 0` on `∂Ω`, has a weak solution, a `u ∈ H¹(Ω)` with
`∫_Ω ∇v · a ∇u = ∫_Ω f v` for every `v ∈ H¹(Ω)`, exactly when `∫_Ω f = 0`. -/
theorem exists_forall_energyFormH1_eq_setIntegral_iff
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega)) (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (hK : IsCompactOperator (W1p.valueL (mu := mu) (Omega := Omega) (p := 2)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    (∃ u : W1p mu Omega 2, ∀ v : W1p mu Omega 2,
        energyFormH1 a 0 0 u v = ∫ x in Omega, f x * W1p.value v x ∂mu) ↔
      ∫ x in Omega, f x ∂mu = 0 := by
  have hℓ (v : W1p mu Omega 2) :
      ((innerSL ℝ f).comp W1p.valueL) v = ∫ x in Omega, f x * W1p.value v x ∂mu := by
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.valueL_apply, L2.inner_def]
    simp [mul_comm]
  have hone : ((innerSL ℝ f).comp W1p.valueL) (W1p.const 1 : W1p mu Omega 2) =
      ∫ x in Omega, f x ∂mu := by
    rw [hℓ]
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_const_ae (mu := mu) (Omega := Omega) (p := 2) 1] with x hx
    rw [hx, mul_one]
  simp_rw [← hℓ, ← hone]
  exact exists_forall_energyFormH1_eq_iff hcoeff hlam ha hK hconn _

end FiniteMeasure

end TauCeti.PDE

namespace Set.IsLipschitzDomain

open TauCeti TauCeti.PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam : ℝ}

/-- **The Neumann problem on a bounded Lipschitz domain.** Let `Ω ⊆ ℝⁿ` be a bounded connected
Lipschitz domain and `a` an essentially bounded coefficient field with `λ‖ξ‖² ≤ ξ · a(x) ξ` almost
everywhere on `Ω` for some `λ > 0`, as for inverse-coercive coefficients
(`TauCeti.PDE.IsUniformlyEllipticAE`). For `f ∈ L²(Ω)` there is `u ∈ H¹(Ω)` with

`∫_Ω ∇v · a ∇u = ∫_Ω f v` for every `v ∈ H¹(Ω)`,

a weak solution of `-div(a ∇u) = f` in `Ω`, `a ∇u · ν = 0` on `∂Ω`, exactly when `∫_Ω f = 0`. By
`TauCeti.PDE.forall_energyFormH1_eq_iff_exists_eq_add_const` it is then unique up to an additive
constant. -/
theorem exists_forall_energyFormH1_eq_setIntegral_iff
    (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hconn : IsPreconnected (Omega : Set (EuclideanSpace ℝ ι)))
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict Omega))
    (hlam : 0 < lam)
    (ha : ∀ᵐ x ∂mu.restrict Omega, ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (a x *ᵥ ξ))
    (f : Lp ℝ 2 (mu.restrict Omega)) :
    (∃ u : W1p mu Omega 2, ∀ v : W1p mu Omega 2,
        energyFormH1 a 0 0 u v = ∫ x in Omega, f x * W1p.value v x ∂mu) ↔
      ∫ x in Omega, f x ∂mu = 0 := by
  have : IsFiniteMeasure (mu.restrict (Omega : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  exact TauCeti.PDE.exists_forall_energyFormH1_eq_setIntegral_iff hcoeff hlam ha
    (W1p.isCompactOperator_valueL_of_isLipschitzDomain hΩ hb) hconn f

end Set.IsLipschitzDomain
