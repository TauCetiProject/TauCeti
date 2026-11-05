/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Liouville.CylindricalEnd
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Manifold.Rescale

/-!
# Radial Hamiltonians on the cylindrical end of a Liouville completion

Let `M` be a completion of the Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleCompletion`), for the
form `ω` with primitive `α`, Liouville field `Z` (`ι_Z ω = α`) and Liouville flow `ψ`, and let
`r = TauCeti.liouvilleRadialCoordinate Z W` be the radial coordinate of its cylindrical end
`M \ W`. Symplectic homology is built from Hamiltonians which are functions `φ ∘ r` of the radial
coordinate on the cylindrical end, typically linear at infinity, `φ(r) = a r + b`
(`TauCeti.IsLinearAtInfinity`). This file computes the Hamiltonian dynamics of such functions
there, with the convention `ι_{X_H} ω = dH`.

The basic field is the Hamiltonian vector field `X_r` of the radial coordinate. On the cylindrical
end:

* `α(X_r) = -r`, since `α(X_r) = ω(Z, X_r) = -dr(Z)` and `dr(Z) = r`
  (`TauCeti.IsLiouvilleCompletion.apply_hamiltonianVectorField_liouvilleRadialCoordinate`); in
  particular `X_r` vanishes nowhere there;
* `X_r` is tangent to the levels of `r`, `dr(X_r) = 0`, as for every Hamiltonian vector field;
* `X_{φ ∘ r} = φ'(r) X_r` wherever the Hamiltonian agrees with `φ ∘ r` near the point
  (`TauCeti.IsLiouvilleCompletion.hamiltonianVectorField_eq_smul_of_eventuallyEq`), so that
  `α(X_{φ ∘ r}) = -r φ'(r)`;
* `X_r` is invariant under the Liouville flow, `dψ_s(X_r) = X_r ∘ ψ_s`, as long as both points lie
  on the cylindrical end
  (`TauCeti.IsLiouvilleCompletion.mfderiv_flowOf_hamiltonianVectorField_liouvilleRadialCoordinate`):
  `ψ_s` multiplies both `ω` and `r` by `e^s`.

On the level `{r = c}` the field `X_r` is `-c` times the Reeb field of the contact form that `α`
restricts to, and the Liouville flow identifies these levels with the boundary `∂W`, conjugating
`X_r` with minus the Reeb field of `α|∂W`; this description is not formalized here, and the
results below are stated for the intrinsic field `X_r`.

The integral curves of the Hamiltonian vector field of a function `H` with `H = φ ∘ r` on a region
`{r > R}`, `R ≥ 1`, stay on the levels of `r` they start on
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_eq_of_isMIntegralCurve`), and on the
level `c` they are the integral curves of `X_r` run at the constant speed `φ'(c)`. Since the
Liouville flow conjugates `X_r` on different levels, the periods of the closed orbits of `X_r` do
not depend on the level
(`IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_liouvilleRadialCoordinate_iff`).
Hence, when `φ'(c) ≠ 0`, `H` has a `1`-periodic orbit on the level `c > R` exactly when `X_r` has
a closed orbit of period `φ'(c)`, on any level
(`TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_iff`). For a Hamiltonian
linear at infinity with a slope `a ≠ 0` that is not such a period, all `1`-periodic orbits lie in
a compact set (`TauCeti.IsLinearAtInfinity.exists_isCompact_forall_mem`). This is the condition on
the slopes imposed in the construction of symplectic homology; finiteness of the generators of the
Floer complexes additionally needs a nondegeneracy assumption on the orbits, not treated here.

## Main results

* `TauCeti.IsLiouvilleCompletion.apply_hamiltonianVectorField_liouvilleRadialCoordinate`:
  `α(X_r) = -r` on the cylindrical end.
* `TauCeti.IsLiouvilleCompletion.hamiltonianVectorField_eq_smul_of_eventuallyEq`:
  `X_{φ ∘ r} = φ'(r) X_r` on the cylindrical end.
* `TauCeti.IsLiouvilleCompletion.mfderiv_flowOf_hamiltonianVectorField_liouvilleRadialCoordinate`:
  the Liouville flow preserves `X_r` on the cylindrical end.
* `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_eq_of_isMIntegralCurve`: the orbits
  of a radial Hamiltonian stay on the levels of `r`.
* `TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_iff`: if `φ'(c) ≠ 0`, the
  `1`-periodic orbits of `φ ∘ r` on the level `c` correspond to the closed orbits of `X_r` of period
  `φ'(c)`.
* `TauCeti.IsLinearAtInfinity.exists_isCompact_forall_mem`: the `1`-periodic orbits of a
  Hamiltonian linear at infinity whose slope is not a period of `X_r` lie in a compact set.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Hamiltonians linear at infinity and their periodic orbits).
* A. Oancea, *A survey of Floer homology for manifolds with contact type boundary or symplectic
  homology*, Ensaios Matemáticos 7 (2004), Section 3.
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1.
-/

public section

open Filter Function Set
open scoped Manifold Topology

namespace TauCeti

namespace IsLiouvilleCompletion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {x : M} {F : M → ℝ} {φ : ℝ → ℝ}

/-- **The primitive on the radial field.** On the cylindrical end of a completion, the primitive
`α` takes the value `-r` on the Hamiltonian vector field `X_r` of the radial coordinate:
`α(X_r) = ω(Z, X_r) = -dr(Z) = -r`. -/
theorem apply_hamiltonianVectorField_liouvilleRadialCoordinate (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ W) :
    α.1 x ![ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) x] =
      -liouvilleRadialCoordinate Z W x := by
  have hα : α.1 x ![ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) x] =
      SmoothBundleForm.eval₂ ω x (Z x)
        (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) x) := by
    rw [← hZ, RoughForm.interior_apply, SmoothBundleForm.eval₂_apply]
  rw [hα, SmoothBundleForm.eval₂_swap, h.isNondegenerate.eval₂_hamiltonianVectorField,
    h.mvfderiv_liouvilleRadialCoordinate_apply hZ hx]

/-- The Hamiltonian vector field of the radial coordinate vanishes nowhere on the cylindrical
end. -/
theorem hamiltonianVectorField_liouvilleRadialCoordinate_ne_zero
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ W) :
    ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) x ≠ 0 := by
  intro h0
  have := h.apply_hamiltonianVectorField_liouvilleRadialCoordinate hZ hx
  rw [h0, ← SmoothForm.degreeOneEquiv_coe_apply, map_zero] at this
  linarith [one_le_liouvilleRadialCoordinate Z W x]

/-- **Hamiltonian vector fields of radial functions.** On the cylindrical end of a completion,
if a Hamiltonian `F` agrees with `φ ∘ r` near `x`, then `X_F(x) = φ'(r x) X_r(x)`. -/
theorem hamiltonianVectorField_eq_smul_of_eventuallyEq (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ W)
    (hF : F =ᶠ[𝓝 x] φ ∘ liouvilleRadialCoordinate Z W)
    (hφ : DifferentiableAt ℝ φ (liouvilleRadialCoordinate Z W x)) :
    ω.hamiltonianVectorField F x =
      deriv φ (liouvilleRadialCoordinate Z W x) •
        ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) x := by
  rw [hF.hamiltonianVectorField_eq, SmoothTwoForm.hamiltonianVectorField_comp hφ
    ((h.contMDiffAt_liouvilleRadialCoordinate hZ hx).mdifferentiableAt (by simp))]

/-- **The primitive on the field of a radial Hamiltonian.** On the cylindrical end of a
completion, if a Hamiltonian `F` agrees with `φ ∘ r` near `x`, then `α(X_F) = -r φ'(r)` at `x`. -/
theorem apply_hamiltonianVectorField_of_eventuallyEq (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ W)
    (hF : F =ᶠ[𝓝 x] φ ∘ liouvilleRadialCoordinate Z W)
    (hφ : DifferentiableAt ℝ φ (liouvilleRadialCoordinate Z W x)) :
    α.1 x ![ω.hamiltonianVectorField F x] =
      -(liouvilleRadialCoordinate Z W x * deriv φ (liouvilleRadialCoordinate Z W x)) := by
  rw [h.hamiltonianVectorField_eq_smul_of_eventuallyEq hZ hx hF hφ,
    ← SmoothForm.degreeOneEquiv_coe_apply, map_smul, SmoothForm.degreeOneEquiv_coe_apply,
    h.apply_hamiltonianVectorField_liouvilleRadialCoordinate hZ hx, smul_eq_mul]
  ring

/-- **The Liouville flow preserves the radial field.** On a completion, the time-`s` map `ψ_s` of
the Liouville flow carries the Hamiltonian vector field of the radial coordinate at a point `x` of
the cylindrical end to the same field at `ψ_s x`, provided `ψ_s x` also lies on the cylindrical
end: `ψ_s` multiplies both `ω` and `r` by `e^s` there, and `X^{e^s ω}_{e^s r} = X^ω_r`. -/
theorem mfderiv_flowOf_hamiltonianVectorField_liouvilleRadialCoordinate
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.1 = α.1) {s : ℝ}
    (hx : x ∉ W) (hsx : flowOf Z s x ∉ W) :
    mfderiv I I (flowOf Z s) x (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) x) =
      ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) (flowOf Z s x) := by
  set r := liouvilleRadialCoordinate Z W
  set ψ := globalFlowDiffeomorph (h.isCompleteVectorField hZ) le_top
    (h.contMDiff_of_interior_eq hZ) s
  have hψ : flowOf Z s = ψ := h.flowOf_eq_globalFlowDiffeomorph hZ s
  -- The time-`s` map is conformally symplectic, `ψ_s^* ω = e^s ω`.
  have hpull : SmoothForm.mpullback ψ ψ.contMDiff ω = Real.exp s • ω :=
    h.mpullback_globalFlowDiffeomorph_eq_exp_smul hZ s
  have hes : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  -- Near `x` the radial coordinate is rescaled by the flow, `r ∘ ψ_s = e^s r`.
  have hloc : r ∘ ψ =ᶠ[𝓝 x] Real.exp s • r := by
    have hopen : IsOpen (Wᶜ ∩ ψ ⁻¹' Wᶜ) :=
      h.isClosed.isOpen_compl.inter (h.isClosed.isOpen_compl.preimage ψ.continuous)
    filter_upwards [hopen.mem_nhds ⟨hx, by rwa [mem_preimage, ← hψ]⟩] with y hy
    rw [comp_apply, Pi.smul_apply, smul_eq_mul, ← hψ]
    exact h.liouvilleRadialCoordinate_flowOf_of_notMem hZ hy.1 (by rw [hψ]; exact hy.2)
  have hnat := (h.isNondegenerate.smul _ hes).mfderiv_hamiltonianVectorField_comp h.isNondegenerate
    ψ.contMDiff hpull ((ψ.isInvertible_mfderiv (by simp) (x := x)).surjective)
    ((h.contMDiffAt_liouvilleRadialCoordinate hZ (by rwa [← hψ])).mdifferentiableAt (by simp))
  rw [hloc.hamiltonianVectorField_eq,
    h.isNondegenerate.hamiltonianVectorField_smul_smul hes] at hnat
  rw [hψ]
  exact hnat

/-- **The Liouville flow maps orbits of the radial field to orbits of the radial field.** On a
completion, if `γ` is an integral curve of the Hamiltonian vector field `X_r` of the radial
coordinate along the cylindrical end, and its image under the time-`s` map `ψ_s` of the Liouville
flow also lies on the cylindrical end, then `ψ_s ∘ γ` is an integral curve of `X_r`. -/
theorem isMIntegralCurve_flowOf_comp (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) {s : ℝ} {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)))
    (hγW : ∀ t, γ t ∉ W) (hsγW : ∀ t, flowOf Z s (γ t) ∉ W) :
    IsMIntegralCurve (flowOf Z s ∘ γ)
      (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ ⊢
  refine hγ.map_of_mfderiv_eq (fun t _ ↦ ?_) fun t _ ↦
    h.mfderiv_flowOf_hamiltonianVectorField_liouvilleRadialCoordinate hZ (hγW t) (hsγW t)
  rw [h.flowOf_eq_globalFlowDiffeomorph hZ s]
  exact (Diffeomorph.contMDiff _).mdifferentiableAt (by simp)

/-- **The periods of the radial field do not depend on the level.** On a completion, for levels
`c, c' > 1` of the radial coordinate, the Hamiltonian vector field `X_r` of the radial coordinate
has a `T`-periodic integral curve on the level `c` exactly when it has one on the level `c'`: the
Liouville flow `ψ_{log (c' / c)}` carries one to the other. -/
theorem exists_periodic_hamiltonianVectorField_liouvilleRadialCoordinate_iff
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.1 = α.1) {c c' T : ℝ}
    (hc : 1 < c) (hc' : 1 < c') :
    (∃ δ : ℝ → M, IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) ∧
        Periodic δ T ∧ ∀ t, liouvilleRadialCoordinate Z W (δ t) = c) ↔
      ∃ δ : ℝ → M, IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) ∧
        Periodic δ T ∧ ∀ t, liouvilleRadialCoordinate Z W (δ t) = c' := by
  -- Transport from any level `c₁ > 1` to any level `c₂ > 1` by `ψ_s`, `s = log c₂ - log c₁`.
  have key : ∀ c₁ c₂ : ℝ, 1 < c₁ → 1 < c₂ →
      (∃ δ : ℝ → M, IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) ∧
        Periodic δ T ∧ ∀ t, liouvilleRadialCoordinate Z W (δ t) = c₁) →
      ∃ δ : ℝ → M, IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) ∧
        Periodic δ T ∧ ∀ t, liouvilleRadialCoordinate Z W (δ t) = c₂ := by
    rintro c₁ c₂ hc₁ hc₂ ⟨δ, hδ, hδT, hδc⟩
    set s := Real.log c₂ - Real.log c₁
    have hes : Real.exp s = c₂ / c₁ := by
      rw [Real.exp_sub, Real.exp_log (zero_lt_one.trans hc₂), Real.exp_log (zero_lt_one.trans hc₁)]
    have hδW : ∀ t, δ t ∉ W := fun t ↦
      (h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (by rw [hδc t]; exact hc₁)
    -- The radial coordinate of `ψ_s (δ t)` is `e^s c₁ = c₂`.
    have hr : ∀ t, liouvilleRadialCoordinate Z W (flowOf Z s (δ t)) = c₂ := fun t ↦ by
      have hc₂' : Real.exp s * liouvilleRadialCoordinate Z W (δ t) = c₂ := by
        rw [hδc t, hes, div_mul_cancel₀ _ (zero_lt_one.trans hc₁).ne']
      rw [h.liouvilleRadialCoordinate_flowOf_of_notMem hZ (hδW t)
        (h.flowOf_notMem_of_one_lt_exp_mul hZ (hδW t) (hc₂' ▸ hc₂)), hc₂']
    refine ⟨flowOf Z s ∘ δ, h.isMIntegralCurve_flowOf_comp hZ hδ hδW fun t ↦
      (h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (by rw [hr t]; exact hc₂),
      fun t ↦ by rw [comp_apply, comp_apply, hδT t], hr⟩
  exact ⟨key c c' hc hc', key c' c hc' hc⟩

variable {R c : ℝ}

/-- On the region `{r > R}`, `R ≥ 1`, where a Hamiltonian agrees with `φ ∘ r`, its Hamiltonian
vector field is `φ'(r) X_r`. -/
private theorem hamiltonianVectorField_eq_smul_of_lt (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hx : R < liouvilleRadialCoordinate Z W x)
    (hφ : DifferentiableAt ℝ φ (liouvilleRadialCoordinate Z W x)) :
    ω.hamiltonianVectorField F x =
      deriv φ (liouvilleRadialCoordinate Z W x) •
        ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W) x := by
  refine h.hamiltonianVectorField_eq_smul_of_eventuallyEq hZ
    ((h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (hR.trans_lt hx)) ?_ hφ
  filter_upwards [(isOpen_lt continuous_const (h.continuous_liouvilleRadialCoordinate hZ)).mem_nhds
    hx] with y hy using hF y hy

/-- **Orbits of radial Hamiltonians stay on the levels of the radial coordinate.** On a
completion, let `F` agree with `φ ∘ r` on the region `{r > R}`, `R ≥ 1`, with `φ` differentiable
on `(R, ∞)`. Then an integral curve of the Hamiltonian vector field of `F` which meets the region
`{r > R}` stays on the level of `r` it meets it on. -/
theorem liouvilleRadialCoordinate_eq_of_isMIntegralCurve (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hφ : DifferentiableOn ℝ φ (Ioi R)) {γ : ℝ → M}
    (hγ : IsMIntegralCurve γ (ω.hamiltonianVectorField F)) {t₀ : ℝ}
    (ht₀ : R < liouvilleRadialCoordinate Z W (γ t₀)) (t : ℝ) :
    liouvilleRadialCoordinate Z W (γ t) = liouvilleRadialCoordinate Z W (γ t₀) := by
  set r := liouvilleRadialCoordinate Z W
  have hr : Continuous r := h.continuous_liouvilleRadialCoordinate hZ
  -- The set of times at which `γ` is on the level of `γ t₀` is clopen and nonempty.
  have hclosed : IsClosed {t | r (γ t) = r (γ t₀)} :=
    isClosed_eq (hr.comp hγ.continuous) continuous_const
  have hopen : IsOpen {t | r (γ t) = r (γ t₀)} := by
    refine Metric.isOpen_iff.2 fun u hu ↦ ?_
    rw [mem_ofPred_eq] at hu
    have hU : IsOpen (γ ⁻¹' {y | R < r y}) :=
      (isOpen_lt continuous_const hr).preimage hγ.continuous
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU u (by
      rw [mem_preimage, mem_ofPred_eq, hu]
      exact ht₀)
    refine ⟨ε, hε, fun v hv ↦ ?_⟩
    -- On the ball `γ` stays in `{r > R}`, where `dr(X_F) = φ'(r) dr(X_r) = 0`.
    have hrR : ∀ w ∈ Metric.ball u ε, R < r (γ w) := fun w hw ↦ hball hw
    have hnotW : ∀ w ∈ Metric.ball u ε, γ w ∉ W := fun w hw ↦
      (h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (hR.trans_lt (hrR w hw))
    have heq := (hγ.isMIntegralCurveOn (Metric.ball u ε)).apply_eq_of_mvfderiv_apply_eq_zero
      Metric.isOpen_ball (convex_ball u ε).isPreconnected
      (fun w hw ↦ (h.contMDiffAt_liouvilleRadialCoordinate hZ (hnotW w hw)).mdifferentiableAt
        (by simp))
      (fun w hw ↦ by
        rw [h.hamiltonianVectorField_eq_smul_of_lt hZ hR hF (hrR w hw)
          (hφ.differentiableAt (Ioi_mem_nhds (hrR w hw))), map_smul,
          (h.isNondegenerate.isHamiltonianVectorField_hamiltonianVectorField _).mvfderiv_apply_self,
          smul_zero])
      (Metric.mem_ball_self hε) hv
    rw [mem_ofPred_eq]
    exact heq.trans hu
  have hS := (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left
    (Nonempty.ne_empty ⟨t₀, by rw [mem_ofPred_eq]⟩)
  simpa using eq_univ_iff_forall.1 hS t

/-- **Periodic orbits of radial Hamiltonians.** On a completion, let `F` agree with `φ ∘ r` on
the region `{r > R}`, `R ≥ 1`, and let `c > R` be a level at which `φ` is differentiable with
`φ'(c) ≠ 0`. Then `F` has a `1`-periodic orbit on the level `c` of the radial coordinate exactly
when the Hamiltonian vector field `X_r` of the radial coordinate has a `φ'(c)`-periodic integral
curve on some, equivalently any, level `c' > 1`. On the level `c` the orbits of `F` are those of
`X_r` run at speed `φ'(c)`, and the Liouville flow moves them between levels. -/
theorem exists_periodic_hamiltonianVectorField_iff (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hc : R < c) (hφ : DifferentiableAt ℝ φ c) (hφc : deriv φ c ≠ 0) {c' : ℝ} (hc' : 1 < c') :
    (∃ γ : ℝ → M, IsMIntegralCurve γ (ω.hamiltonianVectorField F) ∧ Periodic γ 1 ∧
        ∀ t, liouvilleRadialCoordinate Z W (γ t) = c) ↔
      ∃ δ : ℝ → M, IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) ∧
        Periodic δ (deriv φ c) ∧ ∀ t, liouvilleRadialCoordinate Z W (δ t) = c' := by
  set a := deriv φ c
  rw [← h.exists_periodic_hamiltonianVectorField_liouvilleRadialCoordinate_iff hZ
    (hR.trans_lt hc) hc']
  -- On the level `c` the Hamiltonian vector field of `F` is `a X_r`.
  have hfield : ∀ γ : ℝ → M, (∀ t, liouvilleRadialCoordinate Z W (γ t) = c) →
      (IsMIntegralCurve γ (ω.hamiltonianVectorField F) ↔
        IsMIntegralCurve γ (a • ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W))) :=
    fun γ hγc ↦ isMIntegralCurve_congr_vectorField fun t ↦ by
      rw [Pi.smul_apply, h.hamiltonianVectorField_eq_smul_of_lt hZ hR hF (by rw [hγc t]; exact hc)
        (by rw [hγc t]; exact hφ), hγc t]
  constructor
  · -- Reparametrize a `1`-periodic orbit of `F` to an `a`-periodic orbit of `X_r`.
    rintro ⟨γ, hγ, hγ1, hγc⟩
    refine ⟨γ ∘ (· * a⁻¹), ?_, fun t ↦ ?_, fun t ↦ hγc _⟩
    · have := ((hfield γ hγc).1 hγ).comp_mul a⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hφc, one_smul] at this
    · simp only [comp_apply, add_mul, mul_inv_cancel₀ hφc, hγ1 (t * a⁻¹)]
  · -- Reparametrize an `a`-periodic orbit of `X_r` to a `1`-periodic orbit of `F`.
    rintro ⟨δ, hδ, hδa, hδc⟩
    refine ⟨δ ∘ (· * a), (hfield _ fun t ↦ hδc _).2 (hδ.comp_mul a), fun t ↦ ?_,
      fun t ↦ hδc _⟩
    simp only [comp_apply, add_mul, one_mul, hδa (t * a)]

end IsLiouvilleCompletion

/-- **Periodic orbits of Hamiltonians linear at infinity lie in a compact set** when the slope is
not a period. On a completion of the Liouville domain `W`, let `F` be linear at infinity with
slope `a ≠ 0`, and suppose that the Hamiltonian vector field `X_r` of the radial coordinate has no
`a`-periodic integral curve on some level `c' > 1` (equivalently, on any such level). Then a
compact set contains every `1`-periodic orbit of `F`. -/
theorem IsLinearAtInfinity.exists_isCompact_forall_mem {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [T2Space M] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M}
    {Z : (x : M) → TangentSpace I x} {F : M → ℝ} {a : ℝ}
    (hF : IsLinearAtInfinity Z W F a) (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (ha : a ≠ 0) {c' : ℝ} (hc' : 1 < c')
    (hper : ¬∃ δ : ℝ → M,
      IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) ∧
        Periodic δ a ∧ ∀ t, liouvilleRadialCoordinate Z W (δ t) = c') :
    ∃ K : Set M, IsCompact K ∧ ∀ γ : ℝ → M, IsMIntegralCurve γ (ω.hamiltonianVectorField F) →
      Periodic γ 1 → ∀ t, γ t ∈ K := by
  obtain ⟨R₀, b, hb⟩ := (h.isLinearAtInfinity_iff hZ).1 hF
  set R := max R₀ 1
  have hFR : ∀ y, R < liouvilleRadialCoordinate Z W y →
      F y = (fun s ↦ a * s + b) (liouvilleRadialCoordinate Z W y) :=
    fun y hy ↦ hb y ((le_max_left _ _).trans hy.le)
  have hderiv : ∀ s, deriv (fun s ↦ a * s + b) s = a := fun s ↦ by
    simp [deriv_add_const]
  have hdiff : ∀ s, DifferentiableAt ℝ (fun s ↦ a * s + b) s := fun s ↦ by fun_prop
  refine ⟨{y | liouvilleRadialCoordinate Z W y ≤ R},
    h.isCompact_setOf_liouvilleRadialCoordinate_le hZ R, fun γ hγ hγ1 t ↦ ?_⟩
  by_contra hlt
  rw [mem_ofPred_eq, not_le] at hlt
  -- The orbit stays on the level `c = r (γ t) > R`, where it is a `1`-periodic orbit of `F`.
  have hlevel := h.liouvilleRadialCoordinate_eq_of_isMIntegralCurve hZ (le_max_right _ _) hFR
    (fun s _ ↦ (hdiff s).differentiableWithinAt) hγ hlt
  refine hper ?_
  have := (h.exists_periodic_hamiltonianVectorField_iff hZ (le_max_right _ _) hFR hlt (hdiff _)
    (by rwa [hderiv]) hc').1 ⟨γ, hγ, hγ1, hlevel⟩
  rwa [hderiv] at this

end TauCeti
