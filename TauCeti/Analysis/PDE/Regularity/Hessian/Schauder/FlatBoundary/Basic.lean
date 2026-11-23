/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Basic
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary.Corrector
public import TauCeti.Analysis.Calculus.FDeriv.Hyperplane
import TauCeti.Analysis.Analytic.AffineHyperplane
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Normed.Module.Ball.Retraction
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
/-!
# Schauder regularity up to a flat boundary for Poisson's equation

Let `0 ≤ α < 1`, and let `u` be a `C²` function on an open set `U ⊆ ℝ^{n+1}` that vanishes on the
hyperplane `y 0 = 0` and whose Laplacian is `α`-Hölder up to the hyperplane from the closed
half-space `0 ≤ y 0`. This file proves that the second derivatives of `u` are then `α`-Hölder up to
the hyperplane as well: every point of `U` in the closed half-space has a neighbourhood `T` with
`D²u` `α`-Hölder on `T ∩ {y | 0 ≤ y 0}`
(`TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian`). Away from the
hyperplane this is the interior Schauder regularity
`TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian`. At the hyperplane it is
the regularity of solutions of Poisson's equation with zero Dirichlet data on a flat boundary, the
model case of the Schauder theory up to the boundary that the global estimate on `C^{2,α}`
domains is built from. For `α = 0` the statement is the boundedness of the continuous `D²u` near
each point; the argument below is for `0 < α`.

## The argument

The odd reflection of `u` is not `C²` across the hyperplane in general: its second normal
derivative jumps by `2 Δu`. The proof first removes this jump with an explicit corrector.

* **The corrector.** Let `g` be the restriction of `Δu` to the hyperplane, extended to a bounded
  `α`-Hölder function on the whole hyperplane, and let `h = P[g]` be its Poisson integral in the
  half-space (`TauCeti.halfSpacePoissonIntegral`). The corrector `P = (y₀² / 2) h` vanishes on the
  hyperplane together with its first derivatives, and its second derivative tends to
  `g e₀* ⊗ e₀*` there from above. The derivatives of the Poisson integral of Hölder data blow up
  like `‖D^k h‖ ≤ C y₀^(α - k)` (`TauCeti.exists_norm_iteratedFDeriv_halfSpacePoissonIntegral_le`),
  so the Leibniz rule gives `‖D³P‖ = O(y₀^(α - 1))` and
  `‖D²P - g(y') e₀* ⊗ e₀*‖ = O(y₀^α)`, `y'` the foot of `y`. Hence `D²P` and `ΔP`, extended to
  the hyperplane by `g e₀* ⊗ e₀*` and `g`, are `α`-Hölder up to the hyperplane
  (`TauCeti.holderOnWith_of_norm_fderiv_le_mul_rpow`).
* **The reflection.** Now `w = u - P` vanishes on the hyperplane, and so does `∂₀∂₀w`, since
  `∂₀∂₀u = Δu = g` there. So the tangential second derivatives of `w` vanish on the hyperplane,
  the mixed ones are even under the reflection, and the odd reflection `W` of `w` is `C²` across
  the hyperplane (`TauCeti.contDiffOn_two_of_forall_ne_zero_hasFDerivAt`). Its Laplacian is the
  odd reflection of `Δu - ΔP`, which vanishes on the hyperplane and is therefore `α`-Hölder on
  whole balls centred there (`TauCeti.holderOnWith_ite_neg_comp_hyperplaneReflection`).
* **Conclusion.** The interior Schauder regularity applies to `W` on a ball centred on the
  hyperplane, and `D²u = D²W + D²P` up to the hyperplane.

This replaces the potential-theoretic estimates of the Newtonian potential in a half-ball of the
classical proof by the Poisson integral and the interior theory. Only the Laplacian on the
coordinate half-space is treated; constant-coefficient operators reduce to it by a linear change of
variables, and curved boundaries by flattening, neither of which is done here.

## Main declarations

* `TauCeti.PDE.exists_mem_nhds_holderOnWith_iteratedFDeriv_two_inter_of_laplacian`: `C^{2,α}`
  regularity up to the hyperplane for `C²` functions vanishing on it with `α`-Hölder Laplacian.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.4 (Hölder estimates at the boundary) and Lemma 6.4.
* L. C. Evans, *Partial Differential Equations*, Section 2.2.4 (the Poisson integral of the
  half-space).
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

/-! ### Matching across the hyperplane -/

/-- The linear reflection `m ↦ m - 2 m₀ e₀` in the hyperplane `m 0 = 0`. -/
private abbrev reflectionL : E →L[ℝ] E := ((ℝ ∙ e₀)ᗮ.reflection : E →L[ℝ] E)

local notation "Rℓ" => (reflectionL (n := n))

/-- Splitting a vector into its tangential part and its component along `e₀`. -/
private theorem exists_eq_add_smul (m : E) : ∃ (τ : E) (a : ℝ), τ 0 = 0 ∧ m = τ + a • e₀ :=
  ⟨m - m 0 • e₀, m 0, by simp, by abel⟩

private theorem reflection_add_smul {τ : E} (hτ : τ 0 = 0) (a : ℝ) :
    Rℓ (τ + a • e₀) = τ - a • e₀ := by
  rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    reflection_single_one_apply]
  simp only [PiLp.add_apply, PiLp.smul_apply, hτ, smul_eq_mul, zero_add]
  simp
  module

/-- A function vanishing on the hyperplane has zero tangential derivative at its points. -/
private theorem fderiv_apply_eq_zero_of_forall_eq_zero {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    {p : E} (hp : p ∈ U) (hp0 : p 0 = 0) (hd : DifferentiableAt ℝ f p)
    (h0 : ∀ y ∈ U, y 0 = 0 → f y = 0) {τ : E} (hτ : τ 0 = 0) : fderiv ℝ f p τ = 0 :=
  hd.fderiv_apply_eq_zero_of_eventually_eq_zero (ℓ := ℓ₀) (b := 0) (by simpa using hp0)
    (Filter.eventually_of_mem (hU.mem_nhds hp) fun y hy h ↦ h0 y hy (by simpa using h))
    (by simpa using hτ)

/-- The derivative at a point of the hyperplane of a function vanishing on it is odd under the
reflection. -/
private theorem fderiv_comp_reflection {U : Set E} (hU : IsOpen U) {u : E → ℝ} {p : E}
    (hp : p ∈ U) (hp0 : p 0 = 0) (hd : DifferentiableAt ℝ u p)
    (h0 : ∀ y ∈ U, y 0 = 0 → u y = 0) :
    (fderiv ℝ u p).comp Rℓ = -fderiv ℝ u p := by
  ext m
  obtain ⟨τ, a, hτ, rfl⟩ := exists_eq_add_smul m
  have h := fderiv_apply_eq_zero_of_forall_eq_zero hU hp hp0 hd h0 hτ
  rw [ContinuousLinearMap.comp_apply, reflection_add_smul hτ]
  simp [h]

/-- A bilinear form vanishing on pairs of tangential vectors and on `(e₀, e₀)` is odd under the
reflection in both arguments. -/
private theorem neg_apply_reflection_apply_reflection {Q : E →L[ℝ] E →L[ℝ] ℝ}
    (htan : ∀ τ τ' : E, τ 0 = 0 → τ' 0 = 0 → Q τ τ' = 0) (hee : Q e₀ e₀ = 0) (m m' : E) :
    -Q (Rℓ m) (Rℓ m') = Q m m' := by
  obtain ⟨τ, a, hτ, rfl⟩ := exists_eq_add_smul m
  obtain ⟨τ', a', hτ', rfl⟩ := exists_eq_add_smul m'
  rw [reflection_add_smul hτ, reflection_add_smul hτ']
  simp only [map_sub, map_add, map_smul, sub_apply, add_apply, smul_apply, smul_eq_mul,
    htan τ τ' hτ hτ', hee]
  ring

/-- **The Hessian at the hyperplane of a function vanishing on it.** Let `u` be `C²` near a point
`p` of the hyperplane, vanish on it, and have `Δu p = γ`. Then `D²u p - γ e₀* ⊗ e₀*` vanishes on
pairs of tangential vectors and on `(e₀, e₀)`, so it is odd under the reflection. -/
private theorem neg_hessian_sub_apply_reflection {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : ContDiffOn ℝ 2 u U) {p : E} (hp : p ∈ U) (hp0 : p 0 = 0)
    (h0 : ∀ y ∈ U, y 0 = 0 → u y = 0) {γ : ℝ} (hγ : Δ u p = γ) (m m' : E) :
    -((fderiv ℝ (fderiv ℝ u) p - γ • ContinuousLinearMap.smulRight ℓ₀ ℓ₀) (Rℓ m)) (Rℓ m') =
      (fderiv ℝ (fderiv ℝ u) p - γ • ContinuousLinearMap.smulRight ℓ₀ ℓ₀) m m' := by
  have hdu : ∀ y ∈ U, DifferentiableAt ℝ u y := fun y hy ↦
    (hu.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ u) p :=
    ((hu.contDiffAt (hU.mem_nhds hp)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  -- The second derivative vanishes on pairs of tangential vectors.
  have htan : ∀ τ τ' : E, τ 0 = 0 → τ' 0 = 0 → fderiv ℝ (fderiv ℝ u) p τ τ' = 0 := by
    intro τ τ' hτ hτ'
    have hf : DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z τ') p :=
      hd2.clm_apply (differentiableAt_const τ')
    have h0' : ∀ y ∈ U, y 0 = 0 → fderiv ℝ u y τ' = 0 := fun y hy hy0 ↦
      fderiv_apply_eq_zero_of_forall_eq_zero hU hy hy0 (hdu y hy) h0 hτ'
    have := fderiv_apply_eq_zero_of_forall_eq_zero hU hp hp0 hf h0' hτ
    rwa [fderiv_clm_apply hd2 (differentiableAt_const τ'), fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] at this
  -- Along the normal, the second derivative is the Laplacian.
  have hee : fderiv ℝ (fderiv ℝ u) p e₀ e₀ = γ := by
    rw [← hγ, laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
    dsimp only
    rw [Fin.sum_univ_succ]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      EuclideanSpace.basisFun_apply]
    rw [Finset.sum_eq_zero fun i _ ↦ htan _ _ (by simp) (by simp), add_zero]
  refine neg_apply_reflection_apply_reflection (fun τ τ' hτ hτ' ↦ ?_) ?_ m m'
  · simp [htan τ τ' hτ hτ', hτ]
  · simp [hee]

/-! ### The odd reflection of `u - P` -/

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

private theorem continuousAt_rpow_mul (C β : ℝ) (hβ : 0 ≤ β) :
    ContinuousAt (fun t : ℝ ↦ C * t ^ β) 0 :=
  (continuous_const.mul (continuous_id.rpow_const fun _ ↦ Or.inr hβ)).continuousAt

/-- **The corrector is negligible at the hyperplane.** At a point `p` of the hyperplane, from the
closed upper half-space, the corrector `P` and its first derivative tend to zero, and its second
derivative minus `g(z') e₀* ⊗ e₀*` tends to zero, the derivatives taken above the hyperplane. -/
private theorem tendsto_corrector_nhdsWithin {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {g : V → ℝ}
    {Mg : ℝ} {Kg : ℝ≥0} (hgb : ∀ y, |g y| ≤ Mg) (hgH : HolderWith Kg α g) {p : E}
    (hp0 : p 0 = 0) :
    Tendsto (corrector g) (𝓝[{z : E | 0 ≤ z 0}] p) (𝓝 0) ∧
    Tendsto (fun z : E ↦ if 0 < z 0 then fderiv ℝ (corrector g) z else 0)
      (𝓝[{z : E | 0 ≤ z 0}] p) (𝓝 0) ∧
    Tendsto (fun z : E ↦ if 0 < z 0 then
        fderiv ℝ (fderiv ℝ (corrector g)) z -
          g (orthogonalProjectionOnto V z) • ContinuousLinearMap.smulRight ℓ₀ ℓ₀ else 0)
      (𝓝[{z : E | 0 ≤ z 0}] p) (𝓝 0) := by
  obtain ⟨C, hC, hP⟩ := exists_corrector_bounds hα hα1 hgb hgH
  have hev : ∀ᶠ z in 𝓝[{z : E | 0 ≤ z 0}] p, 0 ≤ z 0 := self_mem_nhdsWithin
  refine ⟨?_, ?_, ?_⟩
  · refine tendsto_nhdsWithin_of_norm_le hp0 (b := fun t ↦ C * t ^ 2) (by fun_prop) (by simp)
      (hev.mono fun z hz ↦ ?_)
    rcases hz.lt_or_eq with hz | hz
    · exact (hP z hz).2.1
    · simp [corrector_eq_zero g hz.symm, ← hz]
  · refine tendsto_nhdsWithin_of_norm_le hp0 (b := fun t ↦ C * (t ^ ((α : ℝ) + 1) + t))
      ((continuous_const.mul ((continuous_id.rpow_const fun _ ↦ Or.inr (by positivity)).add
        continuous_id)).continuousAt) (by simp [Real.zero_rpow (by positivity : (α : ℝ) + 1 ≠ 0)])
      (hev.mono fun z hz ↦ ?_)
    by_cases hz0 : 0 < z 0
    · simp only [hz0, ↓reduceIte]
      rw [← norm_iteratedFDeriv_one]
      exact (hP z hz0).2.2.1
    · have : 0 ≤ z 0 ^ ((α : ℝ) + 1) := Real.rpow_nonneg hz _
      simp only [hz0, ↓reduceIte, norm_zero]
      positivity
  · refine tendsto_nhdsWithin_of_norm_le (G := E →L[ℝ] E →L[ℝ] ℝ) hp0 (b := fun t ↦ C * t ^ (α : ℝ))
      (continuousAt_rpow_mul C α α.property)
      (by simp [Real.zero_rpow (by positivity : (α : ℝ) ≠ 0)])
      (hev.mono fun z hz ↦ ?_)
    by_cases hz0 : 0 < z 0
    · simp only [hz0, ↓reduceIte]
      -- The second derivative, read as a bilinear map through the currying isometry.
      refine le_of_eq_of_le ?_ (hP z hz0).2.2.2.1
      rw [← (continuousMultilinearCurryFin2 ℝ E ℝ).symm.norm_map]
      congr 1
      ext m
      simp [iteratedFDeriv_two_apply, fderiv_fderiv_halfSq]
    · have : 0 ≤ z 0 ^ (α : ℝ) := Real.rpow_nonneg hz _
      simp only [hz0, ↓reduceIte]
      exact le_trans (le_of_eq ContinuousLinearMap.opNorm_zero) (by positivity)

/-- Continuity at a point from continuity within the closed upper and the open lower half-space. -/
private theorem continuousAt_of_continuousWithinAt_nonneg_of_neg {G : Type*} [TopologicalSpace G]
    {f : E → G} {q : E} (h₁ : ContinuousWithinAt f {z | 0 ≤ z 0} q)
    (h₂ : ContinuousWithinAt f {z | z 0 < 0} q) : ContinuousAt f q := by
  have hunion : {z : E | 0 ≤ z 0} ∪ {z | z 0 < 0} = univ := by
    ext z
    simp [le_or_gt]
  rw [← continuousWithinAt_univ, ← hunion]
  exact h₁.union h₂

/-- **Continuity of a reflected function at the hyperplane.** Let `q` be a point of the
hyperplane and `f` continuous at `q` within the closed upper half-space. If below the hyperplane,
and at `q`, `f` is obtained from its value at the reflected point by a continuous map `Φ`, then `f`
is continuous at `q`. -/
private theorem continuousAt_of_eq_comp_hyperplaneReflection {G : Type*} [TopologicalSpace G]
    {f : E → G} {Φ : G → G} (hΦ : Continuous Φ) {q : E} (hq : q 0 = 0)
    (hf : ContinuousWithinAt f {z | 0 ≤ z 0} q)
    (hsym : ∀ z : E, z 0 < 0 → f z = Φ (f (hyperplaneReflection e₀ 0 z)))
    (hfix : f q = Φ (f q)) : ContinuousAt f q := by
  have hρq : hyperplaneReflection e₀ 0 q = q := hyperplaneReflection_eq_self_of_inner_eq
    (by rw [EuclideanSpace.real_inner_single_one_right, hq])
  have hmaps : MapsTo (hyperplaneReflection e₀ 0) {z : E | z 0 < 0} {z | 0 ≤ z 0} :=
    fun z (hz : z 0 < 0) ↦ show 0 ≤ hyperplaneReflection e₀ 0 z 0 by
      rw [hyperplaneReflection_single_one_apply_self]
      linarith
  have hf' : ContinuousWithinAt f {z | 0 ≤ z 0} (hyperplaneReflection e₀ 0 q) := by rwa [hρq]
  refine continuousAt_of_continuousWithinAt_nonneg_of_neg hf ?_
  exact (hΦ.continuousAt.comp_continuousWithinAt
    (hf'.comp (hyperplaneReflection e₀ 0).continuous.continuousWithinAt hmaps)).congr
    (fun z hz ↦ hsym z hz) (by rw [Function.comp_apply, Function.comp_apply, hρq]; exact hfix)

/-- The odd reflection of `u - P` across the hyperplane, `P` the corrector. -/
private def oddRemainder (u : E → ℝ) (g : V → ℝ) (z : E) : ℝ :=
  if 0 ≤ z 0 then u z - corrector g z
  else -(u (hyperplaneReflection e₀ 0 z) - corrector g (hyperplaneReflection e₀ 0 z))

/-- **The odd reflection of `u - P` is `C²` across the hyperplane.** Let `u` be `C²` on an open
set `U ⊇ B(x, r)`, `x` on the hyperplane, vanish on the hyperplane, and have Laplacian `g` there.
Subtracting the corrector `P = halfSq · P[g]` makes the second normal derivative vanish on the
hyperplane, and then the odd reflection of `u - P` is `C²` on `B(x, r)`; on the hyperplane its
second derivative is `D²u - g e₀* ⊗ e₀*`. -/
private theorem contDiffOn_oddRemainder {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {g : V → ℝ}
    {Mg : ℝ} {Kg : ℝ≥0} (hgb : ∀ y, |g y| ≤ Mg) (hgH : HolderWith Kg α g) {U : Set E}
    (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (h0 : ∀ y ∈ U, y 0 = 0 → u y = 0)
    {x : E} (hx : x 0 = 0) {r : ℝ} (hrU : ball x r ⊆ U)
    (hΔ : ∀ y ∈ ball x r, y 0 = 0 → Δ u y = g (orthogonalProjectionOnto V y)) :
    ContDiffOn ℝ 2 (oddRemainder u g) (ball x r) ∧ ∀ y ∈ ball x r, y 0 = 0 →
      iteratedFDeriv ℝ 2 (oddRemainder u g) y =
        iteratedFDeriv ℝ 2 u y -
          g (orthogonalProjectionOnto V y) • iteratedFDeriv ℝ 2 halfSq y := by
  obtain ⟨_, -, hP⟩ := exists_corrector_bounds hα hα1 hgb hgH
  have hlimP := fun (p : E) (hp0 : p 0 = 0) ↦ tendsto_corrector_nhdsWithin hα hα1 hgb hgH hp0
  set B := ball x r
  set ρ := hyperplaneReflection e₀ 0
  set P := corrector g
  set w : E → ℝ := fun z ↦ u z - P z
  set Q₀' : E →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.smulRight ℓ₀ ℓ₀
  set pre : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ E E ℝ).flip Rℓ
  have hpre : ∀ L : E →L[ℝ] ℝ, pre L = L.comp Rℓ := fun L ↦ rfl
  have hρ : ∀ z, HasFDerivAt ρ Rℓ z := hasFDerivAt_hyperplaneReflection e₀ 0
  have hρ0 : ∀ z, ρ z 0 = -z 0 := hyperplaneReflection_single_one_apply_self 0
  have hρB : ∀ z ∈ B, ρ z ∈ B := fun z hz ↦ (hyperplaneReflection_mem_ball_iff
    (by rw [EuclideanSpace.real_inner_single_one_right, hx])).2 hz
  have hρc : Continuous ρ := (hyperplaneReflection e₀ 0).continuous
  have hup : ∀ z : E, 0 ≤ z 0 → oddRemainder u g z = w z := fun z hz ↦ by
    simp only [oddRemainder, hz, ↓reduceIte, w, P]
  have hdown : ∀ z : E, z 0 < 0 → oddRemainder u g z = -w (ρ z) := fun z hz ↦ by
    simp only [oddRemainder, not_le.2 hz, ↓reduceIte, w, P, ρ]
  have hucd : ∀ z ∈ B, ContDiffAt ℝ 2 u z := fun z hz ↦ hu.contDiffAt (hU.mem_nhds (hrU hz))
  have hwcd : ∀ z ∈ B, 0 < z 0 → ContDiffAt ℝ 2 w z := fun z hz hz0 ↦
    (hucd z hz).sub (((hP z hz0).1).of_le le_top)
  have hdw : ∀ z ∈ B, 0 < z 0 → DifferentiableAt ℝ w z := fun z hz hz0 ↦
    (hwcd z hz hz0).differentiableAt (by norm_num)
  have hdfw : ∀ z ∈ B, 0 < z 0 → DifferentiableAt ℝ (fderiv ℝ w) z := fun z hz hz0 ↦
    ((hwcd z hz hz0).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfw : ∀ z ∈ B, 0 < z 0 → fderiv ℝ w z = fderiv ℝ u z - fderiv ℝ P z := fun z hz hz0 ↦
    fderiv_sub ((hucd z hz).differentiableAt (by norm_num))
      ((hP z hz0).1.differentiableAt (by simp))
  have hffw : ∀ z ∈ B, 0 < z 0 →
      fderiv ℝ (fderiv ℝ w) z = fderiv ℝ (fderiv ℝ u) z - fderiv ℝ (fderiv ℝ P) z := by
    intro z hz hz0
    have hev : fderiv ℝ w =ᶠ[𝓝 z] fun z' ↦ fderiv ℝ u z' - fderiv ℝ P z' :=
      eventually_of_mem (inter_mem (isOpen_ball.mem_nhds hz)
        ((EuclideanSpace.isOpen_setOf_pos_apply 0).mem_nhds hz0))
        fun z' hz' ↦ hfw z' hz'.1 hz'.2
    rw [hev.fderiv_eq]
    exact fderiv_sub (((hucd z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) ((((hP z hz0).1).fderiv_right (m := 1) (by simp)).differentiableAt
      (by norm_num))
  -- The candidate first and second derivatives.
  set F₁ : E → E →L[ℝ] ℝ := fun z ↦
    if 0 < z 0 then fderiv ℝ w z else if z 0 = 0 then fderiv ℝ u z else -pre (fderiv ℝ w (ρ z))
  set F₂ : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦
    if 0 < z 0 then fderiv ℝ (fderiv ℝ w) z
    else if z 0 = 0 then fderiv ℝ (fderiv ℝ u) z - g (orthogonalProjectionOnto V z) • Q₀'
    else -(pre.comp (fderiv ℝ (fderiv ℝ w) (ρ z))).comp Rℓ
  have hℓ : (ℓ₀ : E →L[ℝ] ℝ) ≠ 0 := fun h ↦ by
    have := congrArg (fun L : E →L[ℝ] ℝ ↦ L e₀) h
    simp at this
  have hF₁p : ∀ z : E, 0 < z 0 → F₁ z = fderiv ℝ w z := fun z hz ↦ by simp [F₁, hz]
  have hF₂p : ∀ z : E, 0 < z 0 → F₂ z = fderiv ℝ (fderiv ℝ w) z := fun z hz ↦ by simp [F₂, hz]
  have hF₁0 : ∀ z : E, z 0 = 0 → F₁ z = fderiv ℝ u z := fun z hz ↦ by simp [F₁, hz]
  have hF₂0 : ∀ z : E, z 0 = 0 →
      F₂ z = fderiv ℝ (fderiv ℝ u) z - g (orthogonalProjectionOnto V z) • Q₀' := fun z hz ↦ by
    simp [F₂, hz]
  have hF₁n : ∀ z : E, z 0 < 0 → F₁ z = -pre (fderiv ℝ w (ρ z)) := fun z hz ↦ by
    simp [F₁, hz.ne, not_lt.2 hz.le]
  have hF₂n : ∀ z : E, z 0 < 0 →
      F₂ z = -(pre.comp (fderiv ℝ (fderiv ℝ w) (ρ z))).comp Rℓ := fun z hz ↦ by
    simp [F₂, hz.ne, not_lt.2 hz.le]
  -- The corrector and its first two derivatives are negligible at the hyperplane.
  set D₁ : E → E →L[ℝ] ℝ := fun z ↦ if 0 < z 0 then fderiv ℝ P z else 0
  set D₂ : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦
    if 0 < z 0 then fderiv ℝ (fderiv ℝ P) z - g (orthogonalProjectionOnto V z) • Q₀' else 0
  -- Continuity from above at a point of the hyperplane.
  have habove : ∀ p ∈ B, p 0 = 0 →
      ContinuousWithinAt (oddRemainder u g) {z | 0 ≤ z 0} p ∧
      ContinuousWithinAt F₁ {z | 0 ≤ z 0} p ∧ ContinuousWithinAt F₂ {z | 0 ≤ z 0} p := by
    intro p hp hp0
    obtain ⟨hPt, hD₁t, hD₂t⟩ := hlimP p hp0
    have hBp : ∀ᶠ z in 𝓝[{z : E | 0 ≤ z 0}] p, z ∈ B ∧ 0 ≤ z 0 :=
      inter_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hp)) self_mem_nhdsWithin
    have hu2 := hucd p hp
    have hfu : ContinuousAt (fderiv ℝ u) p :=
      (hu2.fderiv_right (m := 0) (by norm_num)).continuousAt
    have hffu : ContinuousAt (fderiv ℝ (fderiv ℝ u)) p :=
      ((hu2.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
    have hgf : ContinuousAt (fun z ↦ g (orthogonalProjectionOnto V z)) p :=
      ((hgH.continuous hα).comp (orthogonalProjectionOnto V).continuous).continuousAt
    have hP0 : P p = 0 := corrector_eq_zero g hp0
    refine ⟨?_, ?_, ?_⟩
    · have hw : Tendsto w (𝓝[{z : E | 0 ≤ z 0}] p) (𝓝 (u p - 0)) :=
        (hu2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub hPt
      rw [ContinuousWithinAt, hup p hp0.ge, show w p = u p - 0 by simp [w, hP0]]
      exact hw.congr' (eventually_of_mem self_mem_nhdsWithin fun z hz ↦ (hup z hz).symm)
    · have hlim := (hfu.tendsto.mono_left nhdsWithin_le_nhds).sub hD₁t
      rw [sub_zero] at hlim
      rw [ContinuousWithinAt, hF₁0 p hp0]
      refine hlim.congr' (hBp.mono fun z hz ↦ ?_)
      rcases hz.2.lt_or_eq with hz0 | hz0
      · simp only [D₁, hz0, ↓reduceIte, hF₁p z hz0, hfw z hz.1 hz0]
      · simp only [D₁, ← hz0, lt_irrefl, ↓reduceIte, sub_zero, hF₁0 z hz0.symm]
    · have hlim := ((hffu.sub (hgf.smul (continuousAt_const (y := Q₀')))).tendsto.mono_left
        nhdsWithin_le_nhds).sub hD₂t
      rw [sub_zero] at hlim
      rw [ContinuousWithinAt, hF₂0 p hp0]
      refine hlim.congr' (hBp.mono fun z hz ↦ ?_)
      rcases hz.2.lt_or_eq with hz0 | hz0
      · simp only [D₂, hz0, ↓reduceIte, hF₂p z hz0, hffw z hz.1 hz0, Pi.sub_apply,
          Pi.smul_apply']
        abel
      · simp only [D₂, ← hz0, lt_irrefl, ↓reduceIte, sub_zero, hF₂0 z hz0.symm, Pi.sub_apply,
          Pi.smul_apply']
  -- Below the hyperplane everything is the reflection of its value above.
  set Φ : (E →L[ℝ] E →L[ℝ] ℝ) → E →L[ℝ] E →L[ℝ] ℝ := fun Q ↦ ((-pre).comp Q).comp Rℓ
  have hΦ : ∀ Q, Φ Q = -(pre.comp Q).comp Rℓ := fun Q ↦ by
    simp only [Φ, ContinuousLinearMap.neg_comp]
  have hΦc : Continuous Φ :=
    (continuous_const.clm_comp continuous_id).clm_comp continuous_const
  have hρpos : ∀ z : E, z 0 < 0 → 0 < ρ z 0 := fun z hz ↦ by rw [hρ0]; linarith
  have hsym0 : ∀ z : E, z 0 < 0 → oddRemainder u g z = -oddRemainder u g (ρ z) := fun z hz ↦ by
    rw [hdown z hz, hup (ρ z) (hρpos z hz).le]
  have hsym1 : ∀ z : E, z 0 < 0 → F₁ z = (-pre) (F₁ (ρ z)) := fun z hz ↦ by
    rw [hF₁n z hz, hF₁p (ρ z) (hρpos z hz), neg_apply]
  have hsym2 : ∀ z : E, z 0 < 0 → F₂ z = Φ (F₂ (ρ z)) := fun z hz ↦ by
    rw [hF₂n z hz, hF₂p (ρ z) (hρpos z hz), hΦ]
  -- On the hyperplane the reflection fixes the point, and the values match.
  have hfix0 : ∀ q ∈ B, q 0 = 0 → oddRemainder u g q = -oddRemainder u g q := fun q hq hq0 ↦ by
    rw [hup q hq0.ge]
    simp [w, P, corrector_eq_zero g hq0, h0 q (hrU hq) hq0]
  have hfix1 : ∀ q ∈ B, q 0 = 0 → F₁ q = (-pre) (F₁ q) := fun q hq hq0 ↦ by
    rw [hF₁0 q hq0, neg_apply, hpre, fderiv_comp_reflection hU (hrU hq) hq0
      ((hucd q hq).differentiableAt (by norm_num)) h0, neg_neg]
  have hfix2 : ∀ q ∈ B, q 0 = 0 → F₂ q = Φ (F₂ q) := fun q hq hq0 ↦ by
    rw [hF₂0 q hq0, hΦ]
    ext m m'
    exact (neg_hessian_sub_apply_reflection hU hu (hrU hq) hq0 h0 (hΔ q hq hq0) m m').symm
  -- Local descriptions off the hyperplane.
  have hevp : ∀ z : E, 0 < z 0 → ∀ᶠ z' in 𝓝 z, 0 < z' 0 := fun z hz ↦
    (EuclideanSpace.isOpen_setOf_pos_apply 0).mem_nhds hz
  have hevn : ∀ z : E, z 0 < 0 → ∀ᶠ z' in 𝓝 z, z' 0 < 0 := fun z hz ↦
    (EuclideanSpace.isOpen_setOf_apply_neg 0).mem_nhds hz
  have hd₁ : ∀ z ∈ B, ℓ₀ z ≠ 0 → HasFDerivAt (oddRemainder u g) (F₁ z) z := by
    intro z hz hz0
    replace hz0 : z 0 ≠ 0 := by simpa using hz0
    rcases hz0.lt_or_gt with hz0 | hz0
    · rw [hF₁n z hz0, hpre]
      exact (((hdw (ρ z) (hρB z hz) (hρpos z hz0)).hasFDerivAt.comp z
        (hρ z)).neg).congr_of_eventuallyEq
        ((hevn z hz0).mono fun z' hz' ↦ hdown z' hz')
    · rw [hF₁p z hz0]
      exact (hdw z hz hz0).hasFDerivAt.congr_of_eventuallyEq
        ((hevp z hz0).mono fun z' hz' ↦ hup z' hz'.le)
  have hd₂ : ∀ z ∈ B, ℓ₀ z ≠ 0 → HasFDerivAt F₁ (F₂ z) z := by
    intro z hz hz0
    replace hz0 : z 0 ≠ 0 := by simpa using hz0
    rcases hz0.lt_or_gt with hz0 | hz0
    · rw [hF₂n z hz0]
      have := ((pre.hasFDerivAt.comp z
        ((hdfw (ρ z) (hρB z hz) (hρpos z hz0)).hasFDerivAt.comp z (hρ z))).neg)
      exact this.congr_of_eventuallyEq ((hevn z hz0).mono fun z' hz' ↦ hF₁n z' hz')
    · rw [hF₂p z hz0]
      exact (hdfw z hz hz0).hasFDerivAt.congr_of_eventuallyEq
        ((hevp z hz0).mono fun z' hz' ↦ hF₁p z' hz')
  have hcont : ∀ z ∈ B, ContinuousAt (oddRemainder u g) z ∧ ContinuousAt F₁ z ∧
      ContinuousAt F₂ z := by
    intro z hz
    rcases lt_trichotomy (z 0) 0 with hz0 | hz0 | hz0
    · have hd2w : ContinuousAt (fderiv ℝ (fderiv ℝ w)) (ρ z) :=
        (((hwcd (ρ z) (hρB z hz) (hρpos z hz0)).fderiv_right (m := 1) (by norm_num)).fderiv_right
          (m := 0) (by norm_num)).continuousAt
      refine ⟨?_, ?_, ?_⟩
      · exact ((hdw (ρ z) (hρB z hz) (hρpos z hz0)).continuousAt.comp
          hρc.continuousAt).neg.congr_of_eventuallyEq ((hevn z hz0).mono fun z' hz' ↦ hdown z' hz')
      · exact (pre.continuous.continuousAt.comp ((hdfw (ρ z) (hρB z hz)
          (hρpos z hz0)).continuousAt.comp hρc.continuousAt)).neg.congr_of_eventuallyEq
          ((hevn z hz0).mono fun z' hz' ↦ hF₁n z' hz')
      · exact (hΦc.continuousAt.comp (hd2w.comp hρc.continuousAt)).congr_of_eventuallyEq
          ((hevn z hz0).mono fun z' hz' ↦ (hF₂n z' hz').trans (hΦ _).symm)
    · obtain ⟨a1, a2, a3⟩ := habove z hz hz0
      exact ⟨continuousAt_of_eq_comp_hyperplaneReflection continuous_neg hz0 a1 hsym0
          (hfix0 z hz hz0),
        continuousAt_of_eq_comp_hyperplaneReflection (-pre).continuous hz0 a2 hsym1
          (hfix1 z hz hz0),
        continuousAt_of_eq_comp_hyperplaneReflection hΦc hz0 a3 hsym2 (hfix2 z hz hz0)⟩
    · refine ⟨(hdw z hz hz0).continuousAt.congr_of_eventuallyEq
        ((hevp z hz0).mono fun z' hz' ↦ hup z' hz'.le),
        (hdfw z hz hz0).continuousAt.congr_of_eventuallyEq
          ((hevp z hz0).mono fun z' hz' ↦ hF₁p z' hz'), ?_⟩
      exact (((hwcd z hz hz0).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
        (by norm_num)).continuousAt.congr_of_eventuallyEq
        ((hevp z hz0).mono fun z' hz' ↦ hF₂p z' hz')
  obtain ⟨hC2, hder⟩ := contDiffOn_two_of_forall_ne_zero_hasFDerivAt hℓ isOpen_ball
    (fun z hz ↦ (hcont z hz).1.continuousWithinAt) (fun z hz ↦ (hcont z hz).2.1.continuousWithinAt)
    (fun z hz ↦ (hcont z hz).2.2.continuousWithinAt) hd₁ hd₂
  refine ⟨hC2, fun y hy hy0 ↦ ?_⟩
  ext m
  rw [iteratedFDeriv_two_apply, (hder y hy).2, hF₂0 y hy0]
  simp [iteratedFDeriv_two_apply, fderiv_fderiv_halfSq, Q₀']

/-- Boundary data on the hyperplane: the Laplacian of `u` near `x`, extended by the radial
retraction onto the ball `B(x, r)` of the hyperplane. -/
private theorem exists_boundaryData {α : ℝ≥0} {u : E → ℝ} {x : E} (hx : x 0 = 0) {r : ℝ}
    (hr : 0 < r) {T : Set E} (hrT : closedBall x r ⊆ T) {K₀ : ℝ≥0}
    (hK₀ : HolderOnWith K₀ α (Δ u) (T ∩ {y | 0 ≤ y 0})) :
    ∃ g : V → ℝ, ∃ Mg : ℝ, ∃ Kg : ℝ≥0, (∀ y, |g y| ≤ Mg) ∧ HolderWith Kg α g ∧
      ∀ y ∈ closedBall x r, y 0 = 0 → g (orthogonalProjectionOnto V y) = Δ u y := by
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
  refine ⟨fun y ↦ Δ u (q y), |Δ u x| + K₀ * r ^ (α : ℝ), K₀ * 2 ^ (α : ℝ), fun y ↦ ?_, ?_,
    fun y hy hy0 ↦ ?_⟩
  · have h := hK₀.dist_le (hqT y) hxT
    rw [Real.dist_eq] at h
    have := abs_sub_abs_le_abs_sub (Δ u (q y)) (Δ u x)
    calc |Δ u (q y)| ≤ |Δ u x| + K₀ * dist (q y) x ^ (α : ℝ) := by linarith
      _ ≤ |Δ u x| + K₀ * r ^ (α : ℝ) := by
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

/-- **The boundary case.** At a point `x` of the hyperplane, a `C²` function vanishing on the
hyperplane whose Laplacian is `α`-Hölder up to it near `x` has `α`-Hölder second derivatives up to
the hyperplane near `x`. -/
private theorem exists_mem_nhds_holderOnWith_of_apply_zero_eq_zero {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {U : Set E} {u : E → ℝ} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (h0 : ∀ y ∈ U, y 0 = 0 → u y = 0) {x : E} (hx : x ∈ U) (hx0 : x 0 = 0) {T : Set E}
    (hT : T ∈ 𝓝 x) {K₀ : ℝ≥0} (hK₀ : HolderOnWith K₀ α (Δ u) (T ∩ {y | 0 ≤ y 0})) :
    ∃ T' ∈ 𝓝 x, ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ 2 u) (T' ∩ {y | 0 ≤ y 0}) := by
  obtain ⟨r, hr, hrUT⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem (hU.mem_nhds hx) hT)
  obtain ⟨g, Mg, Kg, hgb, hgH, hgΔ⟩ :=
    exists_boundaryData hx0 hr (hrUT.trans inter_subset_right) hK₀
  have hBU : ball x r ⊆ U := ball_subset_closedBall.trans (hrUT.trans inter_subset_left)
  have hΔg : ∀ y ∈ ball x r, y 0 = 0 → Δ u y = g (orthogonalProjectionOnto V y) := fun y hy hy0 ↦
    (hgΔ y (ball_subset_closedBall hy) hy0).symm
  obtain ⟨hC2, hhess⟩ := contDiffOn_oddRemainder hα hα1 hgb hgH hU hu h0 hx0 hBU hΔg
  obtain ⟨KΨ, hΨ⟩ := exists_holderOnWith_correctorHessian hα hα1 hgb hgH hx0 (r / 2)
  obtain ⟨C, -, hP⟩ := exists_corrector_bounds hα hα1 hgb hgH
  set Ψ := correctorHessian g
  set S := closedBall x (r / 2) ∩ {y : E | 0 ≤ y 0}
  set ur := oddRemainder u g
  set ρ := hyperplaneReflection e₀ 0
  have hx' : ⟪x, e₀⟫ = 0 := by rw [EuclideanSpace.real_inner_single_one_right, hx0]
  have hucd : ∀ z ∈ ball x r, ContDiffAt ℝ 2 u z := fun z hz ↦ hu.contDiffAt (hU.mem_nhds (hBU hz))
  -- The Laplacian is the trace `L` of the second derivative; the trace of `Ψ` is `g` on the
  -- hyperplane.
  set L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ →L[ℝ] ℝ :=
    ∑ i, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) ℝ
      ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]
  have hL : ∀ (f : E → ℝ) y, Δ f y = L (iteratedFDeriv ℝ 2 f y) :=
    laplacian_eq_traceL_iteratedFDeriv
  have hψ : HolderOnWith (‖L‖₊ * KΨ) α (fun y ↦ L (Ψ y)) S :=
    HolderOnWith.of_dist_le fun y hy y' hy' ↦ by
      rw [NNReal.coe_mul, coe_nnNorm, mul_assoc]
      exact (L.lipschitzWith.dist_le_mul _ _).trans
        (mul_le_mul_of_nonneg_left (hΨ.dist_le hy hy') (norm_nonneg _))
  have hφ : HolderOnWith (K₀ + ‖L‖₊ * KΨ) α (fun y ↦ Δ u y - L (Ψ y)) S :=
    (hK₀.mono fun y (hy : y ∈ S) ↦
      ⟨(hrUT (closedBall_subset_closedBall (by linarith) hy.1)).2, hy.2⟩).sub hψ
  have hφ0 : ∀ y ∈ closedBall x (r / 2), y 0 = 0 → Δ u y - L (Ψ y) = 0 := by
    intro y hy hy0
    have : L (Ψ y) = g (orthogonalProjectionOnto V y) := by
      rw [show Ψ y = _ from correctorHessian_of_apply_eq_zero g hy0, map_smul, ← hL,
        laplacian_halfSq, smul_eq_mul, mul_one]
    rw [this, hgΔ y (closedBall_subset_closedBall (by linarith) hy) hy0, sub_self]
  -- The odd extension of `Δu - tr Ψ` is Hölder on the closed ball.
  have hinS : {y : E | 0 ≤ ⟪y, e₀⟫} = {y | 0 ≤ y 0} := by
    simp_rw [EuclideanSpace.real_inner_single_one_right]
  have hodd := holderOnWith_ite_neg_comp_hyperplaneReflection (by simp)
    (convex_closedBall x (r / 2)) (fun y hy ↦ (hyperplaneReflection_mem_closedBall_iff hx').2 hy)
    (by rw [hinS]; exact hφ)
    (fun y hy hy0 ↦ hφ0 y hy (by rwa [EuclideanSpace.real_inner_single_one_right] at hy0))
  -- Above the hyperplane `ur = u - P` near each point, below it `ur = -(u - P) ∘ ρ`.
  have hup : ∀ z : E, 0 < z 0 → ur =ᶠ[𝓝 z] (u - corrector g) := fun z hz ↦
    eventually_of_mem ((EuclideanSpace.isOpen_setOf_pos_apply 0).mem_nhds hz)
      fun z' (hz' : 0 < z' 0) ↦ by
      simp only [ur, oddRemainder, hz'.le, ↓reduceIte, Pi.sub_apply]
  have hρL : ⇑ρ = ⇑((ℝ ∙ e₀)ᗮ.reflection) := funext fun z ↦ by
    simp [ρ, hyperplaneReflection_eq_reflection_add]
  have hdown : ∀ z : E, z 0 < 0 →
      ur =ᶠ[𝓝 z] -((u - corrector g) ∘ ((ℝ ∙ e₀)ᗮ.reflection)) := fun z hz ↦
    eventually_of_mem ((EuclideanSpace.isOpen_setOf_apply_neg 0).mem_nhds hz)
      fun z' (hz' : z' 0 < 0) ↦ by
      simp only [ur, oddRemainder, not_le.2 hz', ↓reduceIte, Pi.neg_apply, Function.comp_apply,
        Pi.sub_apply, ← hρL, ρ]
  have hΨp : ∀ z : E, 0 < z 0 → Ψ z = iteratedFDeriv ℝ 2 (corrector g) z := fun z hz ↦
    correctorHessian_of_pos g hz
  have hΔp : ∀ z ∈ ball x r, 0 < z 0 → Δ ur z = Δ u z - L (Ψ z) := by
    intro z hz hz0
    rw [(laplacian_congr_nhds (hup z hz0)).eq_of_nhds,
      ContDiffAt.laplacian_sub (hucd z hz) (((hP z hz0).1).of_le le_top), hL (corrector g),
      hΨp z hz0]
  have hΔur : ∀ y ∈ ball x (r / 2), Δ ur y = if 0 ≤ ⟪y, e₀⟫ then Δ u y - L (Ψ y)
      else -(Δ u (ρ y) - L (Ψ (ρ y))) := by
    intro y hy
    have hyB : y ∈ ball x r := ball_subset_ball (by linarith) hy
    rw [EuclideanSpace.real_inner_single_one_right]
    rcases lt_trichotomy (y 0) 0 with hy0 | hy0 | hy0
    · have hρy : ρ y ∈ ball x r := (hyperplaneReflection_mem_ball_iff hx').2 hyB
      have hρy0 : 0 < ρ y 0 := by rw [hyperplaneReflection_single_one_apply_self]; linarith
      simp only [not_le.2 hy0, ↓reduceIte]
      rw [(laplacian_congr_nhds (hdown y hy0)).eq_of_nhds, laplacian_neg,
        laplacian_comp_linearIsometryEquiv_right, Pi.neg_apply, Function.comp_apply, ← hρL,
        ← (laplacian_congr_nhds (hup (ρ y) hρy0)).eq_of_nhds, hΔp (ρ y) hρy hρy0]
    · simp only [hy0.ge, ↓reduceIte]
      rw [hL, hhess y hyB hy0, map_sub, map_smul, ← hL,
        show Ψ y = _ from correctorHessian_of_apply_eq_zero g hy0, map_smul]
    · simp only [hy0.le, ↓reduceIte]
      rw [hΔp y hyB hy0]
  -- The interior estimate for `ur`, whose Laplacian is Hölder on the whole ball.
  obtain ⟨T₁, hT₁, K₁, h₁⟩ := exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian hα1
    isOpen_ball (hC2.mono (ball_subset_ball (by linarith)))
    (fun z hz ↦ ⟨ball x (r / 2), isOpen_ball.mem_nhds hz, _,
      (hodd.mono ball_subset_closedBall).congr fun y hy ↦ (hΔur y hy).symm⟩)
    (mem_ball_self (half_pos hr))
  refine ⟨T₁ ∩ ball x (r / 2), inter_mem hT₁ (ball_mem_nhds x (half_pos hr)), K₁ + KΨ, ?_⟩
  have hsum := (h₁.mono fun y (hy : y ∈ (T₁ ∩ ball x (r / 2)) ∩ {y | 0 ≤ y 0}) ↦ hy.1.1).add
    (hΨ.mono fun y (hy : y ∈ (T₁ ∩ ball x (r / 2)) ∩ {y | 0 ≤ y 0}) ↦
      ⟨ball_subset_closedBall hy.1.2, hy.2⟩)
  refine hsum.congr fun y hy ↦ ?_
  have hyB : y ∈ ball x r := ball_subset_ball (by linarith) hy.1.2
  rcases (show 0 ≤ y 0 from hy.2).lt_or_eq with hy0 | hy0
  · rw [Pi.add_apply, ((hup y hy0).iteratedFDeriv ℝ 2).eq_of_nhds, iteratedFDeriv_sub_apply
      (hucd y hyB) (((hP y hy0).1).of_le le_top), hΨp y hy0, sub_add_cancel]
  · rw [Pi.add_apply, hhess y hyB hy0.symm]
    rw [show Ψ y = _ from correctorHessian_of_apply_eq_zero g hy0.symm, sub_add_cancel]

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
  -- For `α = 0` the Hölder condition is boundedness of `D²u`, which holds near `x` by continuity.
  rcases eq_or_ne α 0 with rfl | hα0
  · have hc : ContinuousAt (iteratedFDeriv ℝ 2 u) x :=
      (ContinuousOn.continuousOn_iteratedFDeriv hu hU (by norm_num)).continuousAt (hU.mem_nhds hx)
    refine ⟨_, hc.preimage_mem_nhds (ball_mem_nhds _ one_pos), 2,
      (HolderOnWith.of_dist_le fun a ha b hb ↦ ?_).mono inter_subset_left⟩
    simp only [NNReal.coe_zero, Real.rpow_zero, mul_one, NNReal.coe_ofNat]
    linarith [dist_triangle_right (iteratedFDeriv ℝ 2 u a) (iteratedFDeriv ℝ 2 u b)
      (iteratedFDeriv ℝ 2 u x), mem_ball.1 ha, mem_ball.1 hb]
  have hα : 0 < α := pos_iff_ne_zero.2 hα0
  rcases hx0.lt_or_eq with hx0 | hx0
  · -- Above the hyperplane this is the interior estimate.
    have hΩ := EuclideanSpace.isOpen_setOf_pos_apply (0 : Fin (n + 1))
    obtain ⟨T, hT, K, hK⟩ := exists_mem_nhds_holderOnWith_iteratedFDeriv_two_of_laplacian hα1
      (hU.inter hΩ) (hu.mono inter_subset_left) (fun z hz ↦ by
        obtain ⟨T, hT, K, hK⟩ := hΔ z hz.1 hz.2.le
        exact ⟨T ∩ {z | 0 < z 0}, inter_mem hT (hΩ.mem_nhds hz.2), K,
          hK.mono fun y (hy : y ∈ T ∩ {z : E | 0 < z 0}) ↦
            ⟨hy.1, show 0 ≤ y 0 from le_of_lt (show 0 < y 0 from hy.2)⟩⟩)
      ⟨hx, hx0⟩
    exact ⟨T, hT, K, hK.mono inter_subset_left⟩
  · obtain ⟨T, hT, K, hK⟩ := hΔ x hx hx0.le
    exact exists_mem_nhds_holderOnWith_of_apply_zero_eq_zero hα hα1 hU hu h0 hx hx0.symm hT hK

end PDE

end TauCeti
