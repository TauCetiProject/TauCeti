/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.Corrector
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Reflection
import TauCeti.Analysis.PDE.Perron.Poisson
/-!
# Schauder regularity up to a flat boundary for Poisson's equation

Let `0 < α < 1`, and let `u` be a function on an open set `U ⊆ ℝ^{n+1}` that is `C²` above the
hyperplane `y 0 = 0`, continuous up to the hyperplane from above, and zero on it, and whose
Laplacian is `α`-Hölder above the hyperplane near each point of `U` on or above it. This file
proves that the second derivatives of `u` are then `α`-Hölder above the hyperplane near each such
point, so that they extend continuously to the hyperplane
(`TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian_of_continuousOn`).
Nothing is assumed of `u` below the hyperplane, nor of its derivatives at the hyperplane. This is
the regularity up to a flat boundary portion of classical solutions of Poisson's equation with zero
Dirichlet data, which Perron's method produces only in `C²(Ω) ∩ C⁰(closure Ω)`
(`TauCeti.PDE.exists_contDiffOn_laplacian_eq_continuousOn_closure_eqOn_frontier`): it is the flat
model of the boundary regularity in Kellogg's theorem, that such solutions are `C^{2,α}` up to a
`C^{2,α}` boundary. For `u` that is `C²` across the hyperplane the conclusion holds on the closed
half-space (`TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian`).
Away from the hyperplane both are the interior Schauder regularity
`TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian`.

## The argument

At a point `x` of the hyperplane, the proof removes the jump that the odd reflection of `u` would
have in its second normal derivative, and then reflects.

* **The corrector.** Let `f` be `Δu` extended to the hyperplane, which is possible since it is
  Hölder, let `g` be its restriction to the hyperplane, extended to a bounded `α`-Hölder function on
  the whole hyperplane, and let `P = (y₀² / 2) P[g]` be the corrector
  (`TauCeti.PDE.FlatBoundary.corrector`), `P[g]` the Poisson integral of `g` in the half-space. The
  second derivative of `P`, extended to the hyperplane by `g e₀* ⊗ e₀*`, is `α`-Hölder up to the
  hyperplane (`TauCeti.PDE.FlatBoundary.exists_holderOnWith_correctorHessian`), so `ΔP` tends to `g`
  there. Hence `f - ΔP` vanishes on the hyperplane, and its odd extension `h` is `α`-Hölder on a
  ball centred at `x` (`TauCeti.holderOnWith_ite_neg_comp_hyperplaneReflection`).
* **An odd particular solution.** Poisson's equation `ΔW = h` has a solution `C²` on the ball
  (`TauCeti.PDE.exists_contDiffOn_continuousOn_closure_laplacian_eq`), and since `h` is odd, so is
  the odd part of that solution, which therefore vanishes on the hyperplane.
* **The reflection.** Now `u - P - W` is harmonic above the hyperplane, continuous up to it and
  zero on it, so by the Schwarz reflection principle
  (`TauCeti.harmonicOnNhd_ite_neg_comp_hyperplaneReflection`) it agrees above the hyperplane with a
  function `H` harmonic on the whole ball.
* **Conclusion.** Above the hyperplane `u = P + (W + H)`. The interior Schauder regularity applies
  to `W + H`, whose Laplacian `h` is Hölder on the whole ball, and `D²P` is Hölder up to the
  hyperplane.

When `u` is `C²` across the hyperplane, `D²u` is continuous, so the Hölder bound above the
hyperplane passes to the hyperplane. This replaces the potential-theoretic estimates of the
Newtonian potential in a half-ball of the classical proof by the Poisson integral of the
half-space, Perron's method and the reflection principle. Only the Laplacian on the coordinate
half-space is treated.

## Main declarations

* `TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian_of_continuousOn`:
  `C^{2,α}` regularity up to the hyperplane for functions `C²` above it, continuous up to it and
  zero on it, with `α`-Hölder Laplacian.
* `TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian`: the same for
  `C²` functions on an open set, with the Hölder bound on the closed half-space.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.4 (Hölder estimates at the boundary) and Lemma 6.4.
* L. C. Evans, *Partial Differential Equations*, Section 2.2.4 (the Poisson integral of the
  half-space).
* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137 (the
  Schwarz reflection principle).
-/

public section

noncomputable section

open InnerProductSpace Laplacian Metric Set Filter Topology
open Submodule (orthogonalProjectionOnto)
open scoped NNReal RealInnerProductSpace

namespace TauCeti

namespace PDE

open FlatBoundary

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The first coordinate vector `e₀`, the inner normal of the half-space `0 < x 0`. -/
local notation "e₀" => (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) : E)

/-- The first coordinate, the height above the hyperplane `x 0 = 0`. -/
local notation "ℓ₀" => (EuclideanSpace.proj (0 : Fin (n + 1)) : E →L[ℝ] ℝ)

local notation "v₀" => (unitNormal (n := n))

/-- The bounding hyperplane `y 0 = 0`, as a subspace. -/
local notation "V" => (ℝ ∙ ((v₀ : {w : E // ‖w‖ = 1}) : E))ᗮ

/-- A function bounded by a power of the height tends to zero at the hyperplane, from the closed
upper half-space. -/
private theorem tendsto_nhdsWithin_of_norm_le {G : Type*} [NormedAddCommGroup G] {f : E → G}
    {p : E} (hp0 : p 0 = 0) {b : ℝ → ℝ} (hb : ContinuousAt b 0) (hb0 : b 0 = 0)
    (hf : ∀ᶠ z in 𝓝[{z : E | 0 ≤ z 0}] p, ‖f z‖ ≤ b (z 0)) :
    Tendsto f (𝓝[{z : E | 0 ≤ z 0}] p) (𝓝 0) := by
  refine squeeze_zero_norm' hf ?_
  have hc : ContinuousAt (fun z : E ↦ z 0) p := (ℓ₀).continuous.continuousAt
  have := (hb.comp_of_eq hc hp0).tendsto
  rw [Function.comp_apply, hp0, hb0] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- **The corrector vanishes continuously at the hyperplane.** At a point `p` of the hyperplane,
the corrector is continuous within the closed upper half-space, since it vanishes on the hyperplane
and `|P y| ≤ C (y 0)²` above it. -/
private theorem continuousWithinAt_corrector {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {g : V → ℝ}
    {Mg : ℝ} {Kg : ℝ≥0} (hgb : ∀ y, |g y| ≤ Mg) (hgH : HolderWith Kg α g) {p : E}
    (hp0 : p 0 = 0) : ContinuousWithinAt (corrector g) {z : E | 0 ≤ z 0} p := by
  obtain ⟨C, -, hP⟩ := exists_corrector_bounds hα hα1 hgb hgH
  have hev : ∀ᶠ z in 𝓝[{z : E | 0 ≤ z 0}] p, 0 ≤ z 0 := self_mem_nhdsWithin
  rw [ContinuousWithinAt, corrector_eq_zero g hp0]
  refine tendsto_nhdsWithin_of_norm_le hp0 (b := fun t ↦ C * t ^ 2) (by fun_prop) (by simp)
    (hev.mono fun z hz ↦ ?_)
  rcases hz.lt_or_eq with hz | hz
  · exact (hP z hz).2.1
  · simp [corrector_eq_zero g hz.symm, ← hz]

/-- Boundary data on the hyperplane: a function `φ`, Hölder up to the hyperplane near `x`, extended
from the ball `B(x, r)` of the hyperplane by the radial retraction onto it. -/
private theorem exists_boundaryData {α : ℝ≥0} {φ : E → ℝ} {x : E} (hx : x 0 = 0) {r : ℝ}
    (hr : 0 < r) {T : Set E} (hrT : closedBall x r ⊆ T) {K₀ : ℝ≥0}
    (hK₀ : HolderOnWith K₀ α φ (T ∩ {y | 0 ≤ y 0})) :
    ∃ g : V → ℝ, ∃ Mg : ℝ, ∃ Kg : ℝ≥0, (∀ y, |g y| ≤ Mg) ∧ HolderWith Kg α g ∧
      ∀ y ∈ closedBall x r, y 0 = 0 → g (orthogonalProjectionOnto V y) = φ y := by
  set p₀ : V := ⟨x, (mem_hyperplane_iff x).2 hx⟩
  set q : V → E := fun y ↦ ((p₀ + radialRetraction r (y - p₀) : V) : E)
  have hqx : ∀ y, dist (q y) x ≤ r := fun y ↦ by
    simp only [q, p₀, Submodule.coe_add, dist_eq_norm, add_sub_cancel_left, Submodule.norm_coe]
    rw [norm_radialRetraction hr.le]
    exact min_le_right _ _
  have hqT : ∀ y, q y ∈ T ∩ {z | 0 ≤ z 0} := fun y ↦
    ⟨hrT (mem_closedBall.2 (hqx y)), ((mem_hyperplane_iff _).1 (p₀ + _).property).ge⟩
  have hq : LipschitzWith 2 q := LipschitzWith.of_dist_le_mul fun y y' ↦ by
    simp only [q, ← Subtype.dist_eq, dist_add_left]
    refine ((lipschitzWith_radialRetraction hr.le).dist_le_mul _ _).trans ?_
    rw [dist_sub_right]
  have hxT : x ∈ T ∩ {z | 0 ≤ z 0} := ⟨hrT (mem_closedBall_self hr.le), hx.ge⟩
  refine ⟨fun y ↦ φ (q y), |φ x| + K₀ * r ^ (α : ℝ), K₀ * 2 ^ (α : ℝ), fun y ↦ ?_, ?_,
    fun y hy hy0 ↦ ?_⟩
  · have h := hK₀.dist_le (hqT y) hxT
    rw [Real.dist_eq] at h
    have := abs_sub_abs_le_abs_sub (φ (q y)) (φ x)
    calc |φ (q y)| ≤ |φ x| + K₀ * dist (q y) x ^ (α : ℝ) := by linarith
      _ ≤ |φ x| + K₀ * r ^ (α : ℝ) := by
          gcongr
          exact hqx y
  · have h := hK₀.comp ((hq.holderWith).holderOnWith univ) fun y _ ↦ hqT y
    rw [mul_one] at h
    exact holderOnWith_univ.1 h
  · simp only [q]
    have hyx : ‖(orthogonalProjectionOnto V y : V) - p₀‖ ≤ r := by
      rw [← Submodule.norm_coe, Submodule.coe_sub,
        coe_orthogonalProjectionOnto_hyperplane_of_apply_eq_zero hy0, ← dist_eq_norm]
      exact hy
    rw [radialRetraction_of_norm_le hyx, add_sub_cancel,
      coe_orthogonalProjectionOnto_hyperplane_of_apply_eq_zero hy0]

/-- The trace of a bilinear form on `E` in the standard orthonormal basis, through which the
Laplacian is read off the second derivative. -/
private def traceHessian : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ →L[ℝ] ℝ :=
  ∑ i, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) ℝ
    ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]

private theorem laplacian_eq_traceHessian (f : E → ℝ) (y : E) :
    Δ f y = traceHessian (iteratedFDeriv ℝ 2 f y) :=
  laplacian_eq_traceL_iteratedFDeriv f y

/-- The odd extension across the hyperplane of `φ - tr Ψ`, where `Ψ = correctorHessian g` is the
second derivative of the corrector extended to the hyperplane, so that `tr Ψ` is the Laplacian of
the corrector above the hyperplane and `g` on it. -/
private def oddExtension (φ : E → ℝ) (g : V → ℝ) (y : E) : ℝ :=
  if 0 ≤ ⟪y, e₀⟫ then φ y - traceHessian (correctorHessian g y)
  else -(φ (hyperplaneReflection e₀ 0 y) -
    traceHessian (correctorHessian g (hyperplaneReflection e₀ 0 y)))

/-- **The odd extension of `φ - tr Ψ` is Hölder.** Let `φ` be `α`-Hölder on a closed half-ball
centred on the hyperplane and equal on the hyperplane to the boundary data `g` of the corrector.
Then `φ - tr Ψ` vanishes on the hyperplane, so its odd extension is `α`-Hölder on the closed ball;
it is odd under the reflection. -/
private theorem exists_holderOnWith_oddExtension {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1)
    {g : V → ℝ} {Mg : ℝ} {Kg : ℝ≥0} (hgb : ∀ y, |g y| ≤ Mg) (hgH : HolderWith Kg α g)
    {φ : E → ℝ} {x : E} (hx : x 0 = 0) {r : ℝ} {K₀ : ℝ≥0}
    (hφ : HolderOnWith K₀ α φ (closedBall x r ∩ {y | 0 ≤ y 0}))
    (hφg : ∀ y ∈ closedBall x r, y 0 = 0 → g (orthogonalProjectionOnto V y) = φ y) :
    ∃ K : ℝ≥0, HolderOnWith K α (oddExtension φ g) (closedBall x r) ∧
      ∀ y ∈ closedBall x r,
        oddExtension φ g (hyperplaneReflection e₀ 0 y) = -oddExtension φ g y := by
  obtain ⟨KΨ, hΨ⟩ := exists_holderOnWith_correctorHessian hα hα1 hgb hgH hx r
  have hinner : ∀ y : E, ⟪y, e₀⟫ = y 0 := fun y ↦ EuclideanSpace.real_inner_single_one_right y 0
  have hx' : ⟪x, e₀⟫ = 0 := by rw [hinner, hx]
  have hψ : HolderOnWith (‖traceHessian (n := n)‖₊ * KΨ) α
      (fun y ↦ traceHessian (correctorHessian g y)) (closedBall x r ∩ {y | 0 ≤ y 0}) :=
    HolderOnWith.of_dist_le fun y hy y' hy' ↦ by
      rw [NNReal.coe_mul, coe_nnNorm, mul_assoc]
      exact ((traceHessian (n := n)).lipschitzWith.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (hΨ.dist_le hy hy') (norm_nonneg _))
  have hφ0 : ∀ y ∈ closedBall x r, y 0 = 0 → φ y - traceHessian (correctorHessian g y) = 0 := by
    intro y hy hy0
    rw [correctorHessian_of_apply_eq_zero g hy0, map_smul, ← laplacian_eq_traceHessian,
      laplacian_halfSq, smul_eq_mul, mul_one, hφg y hy hy0, sub_self]
  have hinS : {y : E | 0 ≤ ⟪y, e₀⟫} = {y | 0 ≤ y 0} := by simp_rw [hinner]
  refine ⟨_, holderOnWith_ite_neg_comp_hyperplaneReflection (by simp) (convex_closedBall x r)
    (fun y hy ↦ (hyperplaneReflection_mem_closedBall_iff hx').2 hy) (by rw [hinS]; exact hφ.sub hψ)
    (fun y hy hy0 ↦ hφ0 y hy (by rwa [hinner] at hy0)), fun y hy ↦ ?_⟩
  have hρ : ⟪hyperplaneReflection e₀ 0 y, e₀⟫ = -⟪y, e₀⟫ := by
    rw [inner_hyperplaneReflection (by simp)]
    ring
  rcases lt_trichotomy ⟪y, e₀⟫ 0 with h | h | h
  · have h1 : 0 ≤ ⟪hyperplaneReflection e₀ 0 y, e₀⟫ := by rw [hρ]; linarith
    simp only [oddExtension, h1, not_le.2 h, ↓reduceIte, neg_neg]
  · simp only [oddExtension, hyperplaneReflection_eq_self_of_inner_eq h, h, le_refl, ↓reduceIte,
      hφ0 y hy (by rwa [hinner] at h), neg_zero]
  · have h1 : ¬0 ≤ ⟪hyperplaneReflection e₀ 0 y, e₀⟫ := by rw [hρ]; linarith
    simp only [oddExtension, h1, h.le, ↓reduceIte, hyperplaneReflection_hyperplaneReflection]

/-! ### Solutions continuous up to the hyperplane -/

/-- **Extension to the hyperplane.** A function `α`-Hölder on the part of a ball above the
hyperplane agrees there with a function `α`-Hölder, with the same constant, on the part of the ball
on or above the hyperplane. -/
private theorem exists_holderOnWith_eqOn_of_holderOnWith_inter_pos {α : ℝ≥0} (hα : 0 < α)
    {φ : E → ℝ} {x : E} {r : ℝ} {K₀ : ℝ≥0}
    (hφ : HolderOnWith K₀ α φ (ball x r ∩ {y | 0 < y 0})) :
    ∃ f : E → ℝ, EqOn f φ (ball x r ∩ {y | 0 < y 0}) ∧
      HolderOnWith K₀ α f (ball x r ∩ {y | 0 ≤ y 0}) := by
  obtain ⟨f, heq, hH⟩ := hφ.exists_eqOn_holderOnWith_closure hα
  refine ⟨f, heq, hH.mono fun y hy ↦ ?_⟩
  have h := mem_closure_setOf_lt_inner_inter (ν := e₀) (c := 0) (by simp)
    (by rw [EuclideanSpace.real_inner_single_one_right]; exact hy.2) isOpen_ball hy.1
  simp_rw [EuclideanSpace.real_inner_single_one_right] at h
  rwa [inter_comm] at h

/-- **An odd solution of Poisson's equation.** If `h` is `α`-Hölder on a closed ball centred on
the hyperplane and odd under the reflection in it, then `ΔW = h` has a solution `W` that is `C²` on
the open ball and vanishes on the hyperplane. -/
private theorem exists_laplacian_eq_of_odd {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {x : E}
    (hx : x 0 = 0) {s : ℝ} {h : E → ℝ} {K : ℝ≥0} (hh : HolderOnWith K α h (closedBall x s))
    (hodd : ∀ y ∈ ball x s, h (hyperplaneReflection e₀ 0 y) = -h y) :
    ∃ W : E → ℝ, ContDiffOn ℝ 2 W (ball x s) ∧ (∀ y ∈ ball x s, Δ W y = h y) ∧
      ∀ y ∈ ball x s, y 0 = 0 → W y = 0 := by
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ e₀)ᗮ.reflection
  have hR : ∀ y, R y = hyperplaneReflection e₀ 0 y := fun y ↦ by
    simp [R, hyperplaneReflection_eq_reflection_add]
  have hx' : ⟪x, e₀⟫ = 0 := by rw [EuclideanSpace.real_inner_single_one_right, hx]
  have hRB : MapsTo R (ball x s) (ball x s) := fun y hy ↦ by
    rw [hR]
    exact (hyperplaneReflection_mem_ball_iff hx').2 hy
  -- Solve `ΔW₁ = h / 2` on the ball, and take the odd part `W = W₁ - W₁ ∘ R`.
  have hh' := hh.smul (2⁻¹ : ℝ)
  obtain ⟨W₁, hW₁, -, hΔW₁⟩ := exists_contDiffOn_continuousOn_closure_laplacian_eq hα hα1
    isOpen_ball isBounded_ball
    ((hh'.isBounded_image isBounded_closedBall).subset (image_mono ball_subset_closedBall))
    (fun y hy ↦ ⟨ball x s, isOpen_ball.mem_nhds hy, _, hh'.mono ball_subset_closedBall⟩)
  have hW₁R : ContDiffOn ℝ 2 (W₁ ∘ R) (ball x s) := hW₁.comp R.contDiff.contDiffOn hRB
  refine ⟨W₁ - W₁ ∘ R, hW₁.sub hW₁R, fun y hy ↦ ?_, fun y _ hy0 ↦ ?_⟩
  · rw [(hW₁.contDiffAt (isOpen_ball.mem_nhds hy)).laplacian_sub
      (hW₁R.contDiffAt (isOpen_ball.mem_nhds hy)), laplacian_comp_linearIsometryEquiv_right,
      Function.comp_apply, hΔW₁ y hy, hΔW₁ _ (hRB hy), Pi.smul_apply, Pi.smul_apply, hR,
      hodd y hy, smul_eq_mul, smul_eq_mul]
    ring
  · have hRy : R y = y := by
      rw [hR]
      exact hyperplaneReflection_eq_self_of_inner_eq
        (by rw [EuclideanSpace.real_inner_single_one_right, hy0])
    simp [hRy]

/-- **The harmonic remainder.** Let `u` be `C²` on the part of `B(x, s)` above the hyperplane,
`x` on the hyperplane, continuous up to the hyperplane and zero on it, and let `W` be `C²` on
`B(x, s)` and zero on the hyperplane. If `Δu = ΔP + ΔW` above the hyperplane, `P` the corrector,
then above the hyperplane `u - P - W` agrees with a function harmonic on `B(x, s)`, its odd
reflection. -/
private theorem exists_harmonicOnNhd_eq_sub_corrector_sub {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {g : V → ℝ} {Mg : ℝ} {Kg : ℝ≥0} (hgb : ∀ y, |g y| ≤ Mg)
    (hgH : HolderWith Kg α g) {x : E} (hx : x 0 = 0) {s : ℝ} {u W : E → ℝ}
    (hu : ContDiffOn ℝ 2 u (ball x s ∩ {y | 0 < y 0}))
    (huc : ContinuousOn u (ball x s ∩ {y | 0 ≤ y 0})) (h0 : ∀ y ∈ ball x s, y 0 = 0 → u y = 0)
    (hW : ContDiffOn ℝ 2 W (ball x s)) (hW0 : ∀ y ∈ ball x s, y 0 = 0 → W y = 0)
    (hΔ : ∀ y ∈ ball x s, 0 < y 0 → Δ u y = Δ (corrector g) y + Δ W y) :
    ∃ H : E → ℝ, HarmonicOnNhd H (ball x s) ∧
      ∀ y ∈ ball x s, 0 < y 0 → H y = u y - corrector g y - W y := by
  obtain ⟨C, -, hP⟩ := exists_corrector_bounds hα hα1 hgb hgH
  have hinner : ∀ y : E, ⟪y, e₀⟫ = y 0 := fun y ↦ EuclideanSpace.real_inner_single_one_right y 0
  have hx' : ⟪x, e₀⟫ = 0 := by rw [hinner, hx]
  set v := u - corrector g - W with hv_def
  have hupper : IsOpen (ball x s ∩ {y : E | 0 < y 0}) :=
    isOpen_ball.inter (EuclideanSpace.isOpen_setOf_pos_apply 0)
  have hd : ∀ y ∈ ball x s ∩ {y : E | 0 < y 0}, ContDiffAt ℝ 2 u y ∧
      ContDiffAt ℝ 2 (corrector g) y ∧ ContDiffAt ℝ 2 W y := fun y hy ↦
    ⟨hu.contDiffAt (hupper.mem_nhds hy), ((hP y hy.2).1).of_le le_top,
      hW.contDiffAt (isOpen_ball.mem_nhds hy.1)⟩
  -- `v = u - P - W` is harmonic above the hyperplane, continuous up to it and zero on it.
  have hv : HarmonicOnNhd v (ball x s ∩ {y | 0 < ⟪y, e₀⟫}) := by
    simp_rw [hinner]
    intro y hy
    obtain ⟨h1, h2, h3⟩ := hd y hy
    refine ⟨(h1.sub h2).sub h3, eventually_of_mem (hupper.mem_nhds hy) fun z hz ↦ ?_⟩
    obtain ⟨h1, h2, h3⟩ := hd z hz
    rw [hv_def, ContDiffAt.laplacian_sub (f₁ := u - corrector g) (h1.sub h2) h3,
      h1.laplacian_sub h2, hΔ z hz.1 hz.2, Pi.zero_apply]
    ring
  have hvc : ContinuousOn v (ball x s ∩ {y | 0 ≤ ⟪y, e₀⟫}) := by
    simp_rw [hinner]
    refine (huc.sub fun y hy ↦ ?_).sub (hW.continuousOn.mono inter_subset_left)
    rcases (show 0 ≤ y 0 from hy.2).lt_or_eq with h | h
    · exact (hP y h).1.continuousAt.continuousWithinAt
    · exact (continuousWithinAt_corrector hα hα1 hgb hgH h.symm).mono inter_subset_right
  have hv0 : ∀ y ∈ ball x s, ⟪y, e₀⟫ = 0 → v y = 0 := fun y hy h ↦ by
    rw [hinner] at h
    simp [hv_def, h0 y hy h, corrector_eq_zero g h, hW0 y hy h]
  refine ⟨_, harmonicOnNhd_ite_neg_comp_hyperplaneReflection (by simp) isOpen_ball
    (fun y hy ↦ (hyperplaneReflection_mem_ball_iff hx').2 hy) hv hvc hv0, fun y _ hy0 ↦ ?_⟩
  simp [hinner, hy0.le, hv_def]

/-- **The boundary case for solutions continuous up to the hyperplane.** At a point `x` of the
hyperplane, a function `C²` above the hyperplane, continuous up to it and zero on it, whose
Laplacian is `α`-Hölder above the hyperplane near `x`, has `α`-Hölder second derivatives above the
hyperplane near `x`. -/
private theorem exists_mem_nhds_holderOnWith_inter_pos_of_apply_zero_eq_zero {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {U : Set E} {u : E → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u (U ∩ {y | 0 < y 0})) (huc : ContinuousOn u (U ∩ {y | 0 ≤ y 0}))
    (h0 : ∀ y ∈ U, y 0 = 0 → u y = 0) {x : E} (hx : x ∈ U) (hx0 : x 0 = 0) {T : Set E}
    (hT : T ∈ 𝓝 x) {K₀ : ℝ≥0} (hK₀ : HolderOnWith K₀ α (Δ u) (T ∩ {y | 0 < y 0})) :
    ∃ T' ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ 2 u) (T' ∩ {y | 0 < y 0}) := by
  obtain ⟨r, hr, hrUT⟩ := nhds_basis_ball.mem_iff.1 (inter_mem (hU.mem_nhds hx) hT)
  have hs : 0 < r / 2 := half_pos hr
  have hsr : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (by linarith)
  have hBU : ball x (r / 2) ⊆ U := fun y hy ↦ (hrUT (hsr (ball_subset_closedBall hy))).1
  -- The Laplacian `f` of `u`, extended to the hyperplane, and its boundary values `g` there.
  obtain ⟨f, hfeq, hfH⟩ := exists_holderOnWith_eqOn_of_holderOnWith_inter_pos hα
    (hK₀.mono (inter_subset_inter_left _ (hrUT.trans inter_subset_right)))
  have hfH' := hfH.mono (inter_subset_inter_left {y : E | 0 ≤ y 0} hsr)
  obtain ⟨g, Mg, Kg, hgb, hgH, hgf⟩ := exists_boundaryData hx0 hs subset_rfl hfH'
  -- An odd `W` with `ΔW = f - ΔP` above the hyperplane, `P` the corrector, and the harmonic
  -- function `H` with `u = P + W + H` there.
  obtain ⟨Kh, hh, hodd⟩ := exists_holderOnWith_oddExtension hα hα1 hgb hgH hx0 hfH' hgf
  obtain ⟨W, hW, hΔW, hW0⟩ := exists_laplacian_eq_of_odd hα hα1 hx0 hh
    fun y hy ↦ hodd y (ball_subset_closedBall hy)
  obtain ⟨H, hH, hHeq⟩ := exists_harmonicOnNhd_eq_sub_corrector_sub hα hα1 hgb hgH hx0
    (hu.mono (inter_subset_inter_left _ hBU)) (huc.mono (inter_subset_inter_left _ hBU))
    (fun y hy ↦ h0 y (hBU hy)) hW hW0 fun y hy hy0 ↦ by
      rw [hΔW y hy, laplacian_eq_traceHessian (corrector g), ← correctorHessian_of_pos g hy0]
      simp only [oddExtension, EuclideanSpace.real_inner_single_one_right, hy0.le, ↓reduceIte]
      rw [hfeq ⟨hsr (ball_subset_closedBall hy), hy0⟩]
      ring
  -- `Z = W + H` is `C²` on the ball with Hölder Laplacian, so `D²Z` is Hölder near `x`.
  have hZ : ContDiffOn ℝ 2 (W + H) (ball x (r / 2)) := hW.add hH.contDiffOn
  obtain ⟨T₁, hT₁, K₁, hK₁⟩ := exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian hα1
    isOpen_ball hZ (fun y hy ↦ ⟨ball x (r / 2), isOpen_ball.mem_nhds hy, Kh,
      (hh.mono ball_subset_closedBall).congr fun z hz ↦ by
        rw [(hW.contDiffAt (isOpen_ball.mem_nhds hz)).laplacian_add (hH z hz).1, hΔW z hz,
          (hH z hz).2.self_of_nhds, Pi.zero_apply, add_zero]⟩) (mem_ball_self hs)
  -- Above the hyperplane `D²u = Ψ + D²Z`, `Ψ` the extended Hessian of the corrector.
  obtain ⟨KΨ, hΨ⟩ := exists_holderOnWith_correctorHessian hα hα1 hgb hgH hx0 (r / 2)
  obtain ⟨C, -, hP⟩ := exists_corrector_bounds hα hα1 hgb hgH
  set S := (T₁ ∩ ball x (r / 2)) ∩ {y : E | 0 < y 0}
  refine ⟨T₁ ∩ ball x (r / 2), inter_mem hT₁ (ball_mem_nhds x hs), KΨ + K₁,
    ((hΨ.mono fun y (hy : y ∈ S) ↦
      ⟨ball_subset_closedBall hy.1.2, mem_ofPred.2 (mem_ofPred.1 hy.2).le⟩).add
      (hK₁.mono fun y (hy : y ∈ S) ↦ hy.1.1)).congr fun y (hy : y ∈ S) ↦ ?_⟩
  have hy0 : 0 < y 0 := hy.2
  have hev : u =ᶠ[𝓝 y] corrector g + (W + H) :=
    eventually_of_mem ((isOpen_ball.inter (EuclideanSpace.isOpen_setOf_pos_apply 0)).mem_nhds
      ⟨hy.1.2, hy0⟩) fun z hz ↦ by
      rw [Pi.add_apply, Pi.add_apply, hHeq z hz.1 hz.2]
      ring
  rw [Pi.add_apply, correctorHessian_of_pos g hy0, (hev.iteratedFDeriv ℝ 2).eq_of_nhds,
    iteratedFDeriv_add_apply ((hP y hy0).1.of_le le_top)
      (hZ.contDiffAt (isOpen_ball.mem_nhds hy.1.2))]

/-- **`C^{2,α}` regularity up to a flat boundary for solutions continuous up to it.** Let
`0 < α < 1`, let `U ⊆ ℝ^{n+1}` be open, and let `u` be `C²` on the part of `U` above the hyperplane
`y 0 = 0`, continuous on the part on or above it, and zero on the part in it. Suppose that `Δu` is
`α`-Hölder above the hyperplane near each point of `U` on or above it. Then so is `D²u`: every point
of `U` on or above the hyperplane has a neighbourhood `T` such that `D²u` is `α`-Hölder on
`T ∩ {y | 0 < y 0}`, so that `D²u` extends continuously to the hyperplane. Nothing is assumed of `u`
below the hyperplane, nor of its derivatives at the hyperplane; for `u` that is `C²` across the
hyperplane this is `TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian`.
-/
theorem exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian_of_continuousOn
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {U : Set E} {u : E → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u (U ∩ {y | 0 < y 0})) (huc : ContinuousOn u (U ∩ {y | 0 ≤ y 0}))
    (h0 : ∀ y ∈ U, y 0 = 0 → u y = 0)
    (hΔ : ∀ y ∈ U, 0 ≤ y 0 → ∃ T ∈ 𝓝 y, ∃ K : ℝ≥0,
      HolderOnWith K α (Δ u) (T ∩ {z | 0 < z 0}))
    {x : E} (hx : x ∈ U) (hx0 : 0 ≤ x 0) :
    ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ 2 u) (T ∩ {z | 0 < z 0}) := by
  rcases hx0.lt_or_eq with hx0 | hx0
  · -- Above the hyperplane this is the interior regularity.
    have hΩ := EuclideanSpace.isOpen_setOf_pos_apply (0 : Fin (n + 1))
    obtain ⟨T, hT, K, hK⟩ := exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian hα1
      (hU.inter hΩ) hu (fun z hz ↦ by
        obtain ⟨T, hT, K, hK⟩ := hΔ z hz.1 hz.2.le
        exact ⟨T ∩ {z | 0 < z 0}, inter_mem hT (hΩ.mem_nhds hz.2), K, hK⟩) ⟨hx, hx0⟩
    exact ⟨T, hT, K, hK.mono inter_subset_left⟩
  · obtain ⟨T, hT, K, hK⟩ := hΔ x hx hx0.le
    exact exists_mem_nhds_holderOnWith_inter_pos_of_apply_zero_eq_zero hα hα1 hU hu huc h0 hx
      hx0.symm hT hK

/-- **`C^{2,α}` regularity up to a flat boundary for Poisson's equation.** Let `0 ≤ α < 1`, let
`u` be `C²` on an open set `U ⊆ ℝ^{n+1}` and vanish on the hyperplane `y 0 = 0`, and suppose that
`Δu` is `α`-Hölder up to the hyperplane near each point of `U` in the closed half-space
`0 ≤ y 0`. Then so is `D²u`: every point of `U` in the closed half-space has a neighbourhood `T`
such that `D²u` is `α`-Hölder on `T ∩ {y | 0 ≤ y 0}`. Only the values of `u` on the closed
half-space enter the hypotheses on `Δu` and the conclusion. -/
theorem exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian {α : ℝ≥0}
    (hα1 : α < 1) {U : Set E} {u : E → ℝ} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (h0 : ∀ y ∈ U, y 0 = 0 → u y = 0)
    (hΔ : ∀ y ∈ U, 0 ≤ y 0 → ∃ T ∈ 𝓝 y, ∃ K : ℝ≥0,
      HolderOnWith K α (Δ u) (T ∩ {z | 0 ≤ z 0}))
    {x : E} (hx : x ∈ U) (hx0 : 0 ≤ x 0) :
    ∃ T ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ 2 u) (T ∩ {z | 0 ≤ z 0}) := by
  have hc : ContinuousOn (iteratedFDeriv ℝ 2 u) U :=
    ContinuousOn.continuousOn_iteratedFDeriv hu hU (by norm_num)
  -- For `α = 0` the Hölder condition is boundedness of `D²u`, which holds near `x` by continuity.
  rcases eq_or_ne α 0 with rfl | hα0
  · refine ⟨_, (hc.continuousAt (hU.mem_nhds hx)).preimage_mem_nhds (ball_mem_nhds _ one_pos), 2,
      (HolderOnWith.of_dist_le fun a ha b hb ↦ ?_).mono inter_subset_left⟩
    simp only [NNReal.coe_zero, Real.rpow_zero, mul_one, NNReal.coe_ofNat]
    linarith [dist_triangle_right (iteratedFDeriv ℝ 2 u a) (iteratedFDeriv ℝ 2 u b)
      (iteratedFDeriv ℝ 2 u x), mem_ball.1 ha, mem_ball.1 hb]
  -- Otherwise `D²u` is Hölder above the hyperplane, and by continuity also on it.
  obtain ⟨T, hT, K, hK⟩ :=
    exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian_of_continuousOn
      (pos_iff_ne_zero.2 hα0) hα1 hU (hu.mono inter_subset_left)
      (hu.continuousOn.mono inter_subset_left) h0 (fun y hy hy0 ↦ by
        obtain ⟨T, hT, K, hK⟩ := hΔ y hy hy0
        exact ⟨T, hT, K, hK.mono (inter_subset_inter_right _ fun z (hz : 0 < z 0) ↦ hz.le)⟩)
      hx hx0
  refine ⟨interior T ∩ U, inter_mem (interior_mem_nhds.2 hT) (hU.mem_nhds hx), K,
    hK.of_subset_closure (fun y hy ↦ ?_) fun y hy ↦
      (hc.continuousAt (hU.mem_nhds hy.1.2)).continuousWithinAt⟩
  have h := mem_closure_setOf_lt_inner_inter (ν := e₀) (c := 0) (by simp)
    (by rw [EuclideanSpace.real_inner_single_one_right]; exact hy.2)
    (isOpen_interior.inter hU) hy.1
  simp_rw [EuclideanSpace.real_inner_single_one_right] at h
  exact closure_mono (t := T ∩ {z : E | 0 < z 0})
    (fun z (hz : z ∈ {z : E | 0 < z 0} ∩ (interior T ∩ U)) ↦ ⟨interior_subset hz.2.1, hz.1⟩) h

end PDE

end TauCeti
