/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.Basic
public import TauCeti.Geometry.Symplectic.Liouville.RadialHamiltonian
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv

/-!
# The action of the periodic orbits of radial Hamiltonians

Let `M` be a completion of the Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleCompletion`) for the
form `ω = dα`, with Liouville field `Z` and radial coordinate `r = TauCeti.liouvilleRadialCoordinate
Z W` on the cylindrical end `M \ W`. On an exact symplectic manifold the Hamiltonian action of an
arbitrary loop `γ` is

`A_F(γ) = -∫_γ α - ∫₀¹ F(γ(t)) dt`,

the action for which the energy of a Floer cylinder is the drop of the action between its ends
(`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_eq_sub_of_mextDeriv_eq`); for a
loop with a cap it is the action `TauCeti.contractibleLoopAction` of contractible loops.

This file computes it on the orbits of a Hamiltonian `F` that agrees with `φ ∘ r` on a region
`{r > R}`, `R ≥ 1`. Such an orbit stays on a level `r = c` and has velocity `φ'(c) X_r`
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_eq_of_isMIntegralCurve`), and
`α(X_r) = -r` there, so `α` takes the constant value `-c φ'(c)` on its velocity
(`TauCeti.IsLiouvilleCompletion.apply_curveVelocity_of_isMIntegralCurve`). Hence

`A_F(γ) = c φ'(c) - φ(c)`

(`TauCeti.IsLiouvilleCompletion.neg_pathIntegral_sub_integral_of_isMIntegralCurve`), the value at
`c` of the Legendre-type function `c ↦ c φ'(c) - φ(c)`. For a `1`-periodic orbit with `φ'(c) ≠ 0`
the number `φ'(c)` is a period of the closed orbits of `X_r`, that is, of the Reeb flow of the
boundary `∂W` (`TauCeti.IsLiouvilleCompletion.exists_periodic_hamiltonianVectorField_iff`).

If `φ` is convex, the tangent line at `c` lies below `φ` at `R`, which bounds the action from below
by `R φ'(c) - φ(R)`
(`TauCeti.IsLiouvilleCompletion.mul_deriv_sub_le_neg_pathIntegral_sub_integral`). If moreover `φ`
is nondecreasing, `φ'(c) = 0` forces `φ(c) = φ(R)`. This separates the orbits on the end into two
**action windows**: an orbit with `φ'(c) = 0`, a constant orbit, has action `-φ(R)`, and every
other `1`-periodic orbit has action greater than `ε` as soon as `ε + φ(R) < R T` for every period
`T` of the Reeb flow
(`TauCeti.IsLiouvilleCompletion.neg_pathIntegral_sub_integral_eq_or_lt`). For `R = 1` and
`|φ(1)| < ε` the first value lies in the window `(-ε, ε)` and the others in `(ε, ∞)`. This is the
cylindrical-end half of the splitting of the generators of the Floer complex of a Hamiltonian that
is `C²`-small on `W` and convex on the end into constant orbits, of action in `(-ε, ε)`, and
nonconstant ones, of action greater than `ε`, along which symplectic homology splits into its
zero-energy and positive parts; the orbits inside `W` are not treated here.

## Main results

* `TauCeti.IsLiouvilleCompletion.pathIntegral_of_isMIntegralCurve`: along an orbit on the level
  `c`, the primitive integrates to `-(b - a) c φ'(c)` over `[a, b]`.
* `TauCeti.IsLiouvilleCompletion.neg_pathIntegral_sub_integral_of_isMIntegralCurve`: the action of
  an orbit on the level `c` is `c φ'(c) - φ(c)`.
* `TauCeti.IsLiouvilleCompletion.contractibleLoopAction_of_isMIntegralCurve`: the same for the
  action of a capped orbit.
* `TauCeti.IsLiouvilleCompletion.mul_deriv_sub_le_neg_pathIntegral_sub_integral`: for convex `φ`
  the action is at least `R φ'(c) - φ(R)`.
* `TauCeti.IsLiouvilleCompletion.neg_pathIntegral_sub_integral_eq_or_lt`: for convex nondecreasing
  `φ`, a `1`-periodic orbit on the end has action `-φ(R)` or action greater than `ε`.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Hamiltonians on the cylindrical end and the actions of their orbits).
* A. Oancea, *A survey of Floer homology for manifolds with contact type boundary or symplectic
  homology*, Ensaios Matemáticos 7 (2004), Section 3.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Propositions 3.44 and 3.45 (the
  zero-energy and positive parts of symplectic homology).
-/

public section

open Function Set
open scoped Manifold Topology

namespace TauCeti

namespace IsLiouvilleCompletion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {F : M → ℝ} {φ : ℝ → ℝ} {R : ℝ} {γ : ℝ → M} {t₀ : ℝ}

/-- **The primitive along an orbit of a radial Hamiltonian.** On a completion, let `F` agree with
`φ ∘ r` on the region `{r > R}`, `R ≥ 1`, with `φ` differentiable on `(R, ∞)`. Along an integral
curve `γ` of `X_F` that meets this region on the level `c`, the primitive takes the constant value
`-c φ'(c)` on the velocity of `γ`. -/
theorem apply_curveVelocity_of_isMIntegralCurve (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hφ : DifferentiableOn ℝ φ (Ioi R)) (hγ : IsMIntegralCurve γ (ω.hamiltonianVectorField F))
    (ht₀ : R < liouvilleRadialCoordinate Z W (γ t₀)) (t : ℝ) :
    α.val (γ t) (fun _ ↦ Manifold.curveVelocity I γ t) =
      -(liouvilleRadialCoordinate Z W (γ t₀) * deriv φ (liouvilleRadialCoordinate Z W (γ t₀))) := by
  set r := liouvilleRadialCoordinate Z W
  have hc : r (γ t) = r (γ t₀) :=
    h.liouvilleRadialCoordinate_eq_of_isMIntegralCurve hZ hR hF hφ hγ ht₀ t
  have hRt : R < r (γ t) := hc ▸ ht₀
  have hv : (fun _ : Fin 1 ↦ Manifold.curveVelocity I γ t) =
      ![ω.hamiltonianVectorField F (γ t)] := by
    funext k
    fin_cases k
    rw [← Manifold.curveVelocityWithin_univ]
    exact Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt (hγ t).hasMFDerivWithinAt
      uniqueDiffWithinAt_univ
  have hFr : F =ᶠ[𝓝 (γ t)] φ ∘ r := by
    filter_upwards [(isOpen_lt continuous_const
      (h.continuous_liouvilleRadialCoordinate hZ)).mem_nhds hRt] with y hy using hF y hy
  rw [hv, h.apply_hamiltonianVectorField_of_eventuallyEq hZ
    ((h.one_lt_liouvilleRadialCoordinate_iff hZ).1 (hR.trans_lt hRt)) hFr
    (hφ.differentiableAt (Ioi_mem_nhds hRt))]
  exact congrArg (fun c ↦ -(c * deriv φ c)) hc

/-- **The line integral of the primitive along an orbit of a radial Hamiltonian.** Under the
hypotheses of `TauCeti.IsLiouvilleCompletion.apply_curveVelocity_of_isMIntegralCurve`, the
integral of the primitive along `γ` over `[a, b]` is `-(b - a) c φ'(c)`, where `c` is the level of
`γ`. -/
theorem pathIntegral_of_isMIntegralCurve (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hφ : DifferentiableOn ℝ φ (Ioi R)) (hγ : IsMIntegralCurve γ (ω.hamiltonianVectorField F))
    (ht₀ : R < liouvilleRadialCoordinate Z W (γ t₀)) (a b : ℝ) :
    pathIntegral α.val γ a b =
      -((b - a) * (liouvilleRadialCoordinate Z W (γ t₀) *
        deriv φ (liouvilleRadialCoordinate Z W (γ t₀)))) := by
  simp only [pathIntegral_def, h.apply_curveVelocity_of_isMIntegralCurve hZ hR hF hφ hγ ht₀,
    intervalIntegral.integral_const, smul_eq_mul, mul_neg]

/-- **The action of an orbit of a radial Hamiltonian.** On a completion, let `F` agree with
`φ ∘ r` on the region `{r > R}`, `R ≥ 1`, with `φ` differentiable on `(R, ∞)`. An integral curve
`γ` of `X_F` that meets this region on the level `c` has action
`-∫_γ α - ∫₀¹ F(γ(t)) dt = c φ'(c) - φ(c)`. -/
theorem neg_pathIntegral_sub_integral_of_isMIntegralCurve (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hφ : DifferentiableOn ℝ φ (Ioi R)) (hγ : IsMIntegralCurve γ (ω.hamiltonianVectorField F))
    (ht₀ : R < liouvilleRadialCoordinate Z W (γ t₀)) :
    -pathIntegral α.val γ 0 1 - ∫ t in 0..1, F (γ t) =
      liouvilleRadialCoordinate Z W (γ t₀) * deriv φ (liouvilleRadialCoordinate Z W (γ t₀)) -
        φ (liouvilleRadialCoordinate Z W (γ t₀)) := by
  have hFγ : ∀ t, F (γ t) = φ (liouvilleRadialCoordinate Z W (γ t₀)) := fun t ↦ by
    have hc := h.liouvilleRadialCoordinate_eq_of_isMIntegralCurve hZ hR hF hφ hγ ht₀ t
    rw [hF _ (hc ▸ ht₀), hc]
  simp only [h.pathIntegral_of_isMIntegralCurve hZ hR hF hφ hγ ht₀, hFγ,
    intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **The action of a capped orbit of a radial Hamiltonian.** Under the hypotheses of
`TauCeti.IsLiouvilleCompletion.neg_pathIntegral_sub_integral_of_isMIntegralCurve`, if the orbit
`γ` on the level `c` has a cap, its action as a contractible loop is `c φ'(c) - φ(c)`. -/
theorem contractibleLoopAction_of_isMIntegralCurve (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hφ : DifferentiableOn ℝ φ (Ioi R)) (hγ : IsMIntegralCurve γ (ω.hamiltonianVectorField F))
    (ht₀ : R < liouvilleRadialCoordinate Z W (γ t₀)) {u : ℝ × ℝ → M} (hu : IsCap I u γ) :
    contractibleLoopAction ω.val (fun _ ↦ F) γ =
      liouvilleRadialCoordinate Z W (γ t₀) * deriv φ (liouvilleRadialCoordinate Z W (γ t₀)) -
        φ (liouvilleRadialCoordinate Z W (γ t₀)) := by
  rw [← h.mextDeriv_eq, contractibleLoopAction_mextDeriv (α.isSmoothForm.of_le (by simp)) _ hu]
  exact h.neg_pathIntegral_sub_integral_of_isMIntegralCurve hZ hR hF hφ hγ ht₀

/-- **The action of an orbit of a convex radial Hamiltonian is bounded below.** If moreover `φ` is
convex on `[R, ∞)`, an integral curve `γ` of `X_F` meeting the region `{r > R}` on the level `c`
has action at least `R φ'(c) - φ(R)`: the tangent line of `φ` at `c` lies below `φ` at `R`. -/
theorem mul_deriv_sub_le_neg_pathIntegral_sub_integral (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hφ : DifferentiableOn ℝ φ (Ioi R)) (hφc : ConvexOn ℝ (Ici R) φ)
    (hγ : IsMIntegralCurve γ (ω.hamiltonianVectorField F))
    (ht₀ : R < liouvilleRadialCoordinate Z W (γ t₀)) :
    R * deriv φ (liouvilleRadialCoordinate Z W (γ t₀)) - φ R ≤
      -pathIntegral α.val γ 0 1 - ∫ t in 0..1, F (γ t) := by
  set c := liouvilleRadialCoordinate Z W (γ t₀)
  rw [h.neg_pathIntegral_sub_integral_of_isMIntegralCurve hZ hR hF hφ hγ ht₀]
  have hslope := hφc.slope_le_deriv self_mem_Ici ht₀.le ht₀
    (hφ.differentiableAt (Ioi_mem_nhds ht₀))
  rw [slope_def_field, div_le_iff₀ (sub_pos.2 ht₀)] at hslope
  linarith

/-- **Action windows of a convex radial Hamiltonian.** On a completion, let `F` agree with
`φ ∘ r` on the region `{r > R}`, `R ≥ 1`, with `φ` convex and nondecreasing on `[R, ∞)` and
differentiable on `(R, ∞)`. Suppose that `ε + φ(R) < R T` for every period `T > 0` of a closed
orbit of `X_r`, that is, of the Reeb flow of the boundary, on some level `c' > 1`. Then every
`1`-periodic orbit of `X_F` meeting the region `{r > R}` either has action `-φ(R)` or has action
greater than `ε`. The first case is that of the levels `c` with `φ'(c) = 0`, on which `X_F`
vanishes.

For `R = 1` and `|φ(1)| < ε`, the first window lies in `(-ε, ε)` and the second in `(ε, ∞)`. -/
theorem neg_pathIntegral_sub_integral_eq_or_lt (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.val = α.val) (hR : 1 ≤ R)
    (hF : ∀ y, R < liouvilleRadialCoordinate Z W y → F y = φ (liouvilleRadialCoordinate Z W y))
    (hφ : DifferentiableOn ℝ φ (Ioi R)) (hφc : ConvexOn ℝ (Ici R) φ)
    (hφm : MonotoneOn φ (Ici R)) {ε c' : ℝ} (hc' : 1 < c')
    (hper : ∀ T, 0 < T → (∃ δ : ℝ → M,
      IsMIntegralCurve δ (ω.hamiltonianVectorField (liouvilleRadialCoordinate Z W)) ∧
        Periodic δ T ∧ ∀ t, liouvilleRadialCoordinate Z W (δ t) = c') → ε + φ R < R * T)
    (hγ : IsMIntegralCurve γ (ω.hamiltonianVectorField F)) (hγ1 : Periodic γ 1)
    (ht₀ : R < liouvilleRadialCoordinate Z W (γ t₀)) :
    -pathIntegral α.val γ 0 1 - ∫ t in 0..1, F (γ t) = -φ R ∨
      ε < -pathIntegral α.val γ 0 1 - ∫ t in 0..1, F (γ t) := by
  set c := liouvilleRadialCoordinate Z W (γ t₀)
  have hφd : DifferentiableAt ℝ φ c := hφ.differentiableAt (Ioi_mem_nhds ht₀)
  -- `φ` is nondecreasing, so `φ'(c) ≥ 0`.
  have hd : 0 ≤ deriv φ c := by
    rw [← derivWithin_of_mem_nhds (Ici_mem_nhds ht₀)]
    exact hφm.derivWithin_nonneg
  rcases hd.eq_or_lt with hd | hd
  · -- If `φ'(c) = 0`, convexity and monotonicity give `φ(c) = φ(R)`.
    left
    have hslope := hφc.slope_le_deriv self_mem_Ici ht₀.le ht₀ hφd
    rw [← hd, slope_def_field, div_le_iff₀ (sub_pos.2 ht₀), zero_mul, sub_nonpos] at hslope
    have hle : φ R ≤ φ c := hφm self_mem_Ici ht₀.le ht₀.le
    rw [h.neg_pathIntegral_sub_integral_of_isMIntegralCurve hZ hR hF hφ hγ ht₀, ← hd, mul_zero,
      zero_sub, le_antisymm hslope hle]
  · -- If `φ'(c) > 0`, it is a period of the Reeb flow, and the lower bound applies.
    right
    have hlevel : ∀ t, liouvilleRadialCoordinate Z W (γ t) = c :=
      h.liouvilleRadialCoordinate_eq_of_isMIntegralCurve hZ hR hF hφ hγ ht₀
    have hT := hper _ hd ((h.exists_periodic_hamiltonianVectorField_iff hZ hR hF ht₀ hφd hd.ne'
      hc').1 ⟨γ, hγ, hγ1, hlevel⟩)
    have hlow := h.mul_deriv_sub_le_neg_pathIntegral_sub_integral hZ hR hF hφ hφc hγ ht₀
    linarith

end IsLiouvilleCompletion

end TauCeti
