/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
public import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.InnerProductSpace.Harmonic.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Harmonic replacement

Let `u ∈ H¹(Ω)`. Its **harmonic replacement** on `Ω` is the weak solution `w` of the Dirichlet
problem `Δw = 0` in `Ω`, `w = u` on `∂Ω`: the function `w ∈ H¹(Ω)` with `u - w ∈ H¹₀(Ω)` and
`∫_Ω ⟨∇w, ∇v⟩ = 0` for every `v ∈ H¹₀(Ω)`. Replacing a function by the solution of the frozen
problem with the same boundary values on each ball is the comparison step of Campanato's approach
to Schauder estimates. Two facts make it work:

* the replacement is harmonic (after modification on a null set), so the decay estimates of
  harmonic functions apply to it;
* the error `u - w` is controlled in energy by the equation `u` satisfies. If
  `∫_Ω ⟨∇u, ∇v⟩ = ⟪G, ∇v⟫_{L²}` for every `v ∈ H¹₀(Ω)`, for instance when `u` solves
  `-Δu = -div G` weakly, then `‖∇(u - w)‖_{L²(Ω)} ≤ ‖G‖_{L²(Ω)}`.

The energy estimate holds for every measurable, uniformly elliptic `a` with constants
`0 < λ ≤ Λ`, in the form `λ ‖∇(u - w)‖ ≤ ‖G‖` for any `w` with `u - w ∈ H¹₀(Ω)` and
`a(w, v) = 0` for every `v ∈ H¹₀(Ω)`, as is needed when the frozen problem has a constant
coefficient matrix other than the identity. Its proof is one line: test the equation for
`u - w ∈ H¹₀(Ω)` against itself and use ellipticity.

Harmonicity comes from Weyl's lemma. A function `w ∈ H¹(Ω)` with `∫_Ω ⟨∇w, ∇φ⟩ = 0` for every
test function `φ` on `Ω` is weakly harmonic, `∫ Δφ • w = -∫ ⟪∇φ, ∇w⟫ = 0`, so it agrees almost
everywhere on `Ω` with a harmonic function. Existence and uniqueness of the replacement on a
bounded domain are the Dirichlet problem with boundary values in `H¹(Ω)`,
`UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball`.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.mul_norm_gradient_sub_le`: the energy estimate
  `λ ‖∇(u - w)‖ ≤ ‖G‖` for the replacement relative to a general elliptic `a`.
* `TauCeti.PDE.exists_harmonicOnNhd_ae_eq_of_forall_energyFormH1_eq_zero`: a function of `H¹(Ω)`
  that solves `Δw = 0` weakly agrees almost everywhere with a harmonic function.
* `TauCeti.PDE.W1p.exists_harmonicOnNhd_ae_eq_gradient`: so does its weak gradient, since the
  weak derivatives of a weakly harmonic function are weakly harmonic.
* `TauCeti.PDE.exists_sub_mem_w1p0Submodule_harmonicOnNhd_ae_eq_of_subset_ball`: **harmonic
  replacement** on a bounded domain, with its harmonic representative and the energy estimate.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.3 (Schauder estimates by comparison with
  the frozen problem).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 6.2.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped Distributions Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}

/-- **The energy estimate for the replacement.** Let `a` be measurable and uniformly elliptic on
`Ω` with constants `0 < λ ≤ Λ`, and let `u, w ∈ H¹(Ω)` have the same boundary values,
`u - w ∈ H¹₀(Ω)`, with `w` a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢw) = 0`, that is `a(w, v) = 0` for
every `v ∈ H¹₀(Ω)`. If the functional `v ↦ a(u, v)` on `H¹₀(Ω)` is represented by a field
`G ∈ L²(Ω; ℝⁿ)` as `a(u, v) = ⟪G, ∇v⟫_{L²}`, then `λ ‖∇(u - w)‖_{L²} ≤ ‖G‖_{L²}`. -/
theorem UniformlyEllipticOn.mul_norm_gradient_sub_le {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {lam Lam : ℝ} (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u w : W1p mu Omega 2}
    (huw : u - w ∈ w1p0Submodule mu Omega 2)
    (hw : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 w (v : W1p mu Omega 2) = 0)
    {G : Lp (EuclideanSpace ℝ ι) 2 (mu.restrict Omega)}
    (hG : ∀ v : W1p0 mu Omega 2,
      energyFormH1 a 0 0 u (v : W1p mu Omega 2) = ⟪G, W1p.gradient (v : W1p mu Omega 2)⟫_ℝ) :
    lam * ‖W1p.gradient (u - w)‖ ≤ ‖G‖ := by
  have hcoeff := memLp_energyIntegrand_of_bounds (b := 0) (c := 0) (beta := 0) (gamma := 0)
    h.upper_nonneg ha aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => h.upper_bound hx eta xi) (fun _ _ => by simp) (fun _ _ => by simp)
  have hd : u - w ∈ W1p0 mu Omega 2 := (ClosedSubmodule.mem_toSubmodule_iff _ _).2 huw
  -- Test the equation for `u - w` against `u - w` itself.
  have henergy : energyFormH1 a 0 0 (u - w) (u - w) =
      ⟪G, W1p.gradient (u - w)⟫_ℝ := by
    rw [energyFormH1_sub_left hcoeff]
    have hu := hG ⟨u - w, hd⟩
    have hw := hw ⟨u - w, hd⟩
    simp only at hu hw
    rw [hu, hw, sub_zero]
  -- Ellipticity bounds the left side below by `λ ‖∇(u - w)‖²`, Cauchy–Schwarz the right side
  -- above by `‖G‖ ‖∇(u - w)‖`.
  have hlower := mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift (b := 0) (c := 0)
    (gamma := 0) h ha aestronglyMeasurable_const (fun _ _ => rfl) (fun _ _ => by simp)
    (fun _ _ => le_rfl) (u - w)
  rw [henergy] at hlower
  have hCS := (real_inner_le_norm G (W1p.gradient (u - w))).trans_eq (mul_comm _ _)
  rcases (norm_nonneg (W1p.gradient (u - w))).eq_or_lt with hzero | hpos
  · rw [← hzero, mul_zero]
    exact norm_nonneg G
  · exact le_of_mul_le_mul_right (by nlinarith) hpos

/-- **Weakly harmonic Sobolev functions are harmonic.** If `w ∈ H¹(Ω)` solves `Δw = 0` weakly,
in the sense that `∫_Ω ⟨∇w, ∇φ⟩ = 0` for every test function `φ` on `Ω`, then `w` agrees almost
everywhere on `Ω` with a function harmonic on `Ω`. No boundary condition on `w` and no regularity
of `Ω` is assumed. -/
theorem exists_harmonicOnNhd_ae_eq_of_forall_energyFormH1_eq_zero {w : W1p mu Omega 2}
    (hw : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => 1) 0 0 w (W1p.ofTestFunctionₗ mu Omega 2 φ) = 0) :
    ∃ h : EuclideanSpace ℝ ι → ℝ, HarmonicOnNhd h Omega ∧
      (W1p.value w : EuclideanSpace ℝ ι → ℝ) =ᵐ[mu.restrict Omega] h := by
  refine WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq ((weaklyHarmonicOn_iff).2
    ⟨(W1p.hasWeakFDerivOn w).locallyIntegrableOn, fun φ => ?_⟩)
  rw [(W1p.hasWeakFDerivOn w).integral_laplacian_smul_eq_neg_integral_inner φ, neg_eq_zero,
    ← hw φ, energyFormH1_const_eq_setIntegral]
  simp_rw [real_inner_comm (W1p.gradient w _)]
  rw [← φ.setIntegral_inner_gradient_eq_integral_inner_gradient _ φ.tsupport_subset]
  refine integral_congr_ae ?_
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
  rw [W1p.gradient_ofTestFunctionₗ, hx, matrixBilinearForm_one_apply]
  exact EuclideanSpace.inner_eq_star_dotProduct _ _

omit [DecidableEq ι] in
/-- **The weak gradient of a weakly harmonic Sobolev function is harmonic.** If the value of
`w ∈ W^{1,p}(Ω)` is weakly harmonic on `Ω`, then the weak gradient of `w` agrees almost
everywhere on `Ω` with a function `Ω → ℝⁿ` harmonic on `Ω`. -/
theorem W1p.exists_harmonicOnNhd_ae_eq_gradient {p : ENNReal} [Fact (1 ≤ p)]
    {w : W1p mu Omega p} (hw : WeaklyHarmonicOn mu Omega (W1p.value w)) :
    ∃ H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι, HarmonicOnNhd H Omega ∧
      (W1p.gradient w : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) =ᵐ[mu.restrict Omega] H := by
  classical
  set b := EuclideanSpace.basisFun ι ℝ
  -- Each coordinate `⟪bᵢ, ∇w⟫` is a weak derivative of the weakly harmonic `w`, so it is weakly
  -- harmonic, and Weyl's lemma gives it a harmonic representative.
  have hi : ∀ i, ∃ h : EuclideanSpace ℝ ι → ℝ, HarmonicOnNhd h Omega ∧
      (fun x => ⟪b i, W1p.gradient w x⟫_ℝ) =ᵐ[mu.restrict Omega] h := fun i => by
    have hd := (hasWeakFDerivOn_iff.1 (W1p.hasWeakFDerivOn w)) (b i)
    simp only [innerSL_apply_apply, real_inner_comm (b i)] at hd
    exact (hd.weaklyHarmonicOn hw).exists_harmonicOnNhd_ae_eq
  choose h hh hae using hi
  refine ⟨fun x => ∑ i, h i x • b i, HarmonicOnNhd.sum _ fun i _ =>
    (hh i).comp_CLM (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (b i)), ?_⟩
  filter_upwards [ae_all_iff.2 hae] with x hx
  conv_lhs => rw [← b.sum_repr' (W1p.gradient w x)]
  exact Finset.sum_congr rfl fun i _ => by rw [hx i]

/-- **Harmonic replacement.** Let `Ω ⊆ ℝ^{n+1}` be an open set contained in a ball, and let
`u ∈ H¹(Ω)`. There is `w ∈ H¹(Ω)` with the same boundary values, `u - w ∈ H¹₀(Ω)`, solving
`Δw = 0` weakly, `∫_Ω ⟨∇w, ∇v⟩ = 0` for every `v ∈ H¹₀(Ω)`, such that:

* `w` agrees almost everywhere on `Ω` with a function harmonic on `Ω`;
* if `∫_Ω ⟨∇u, ∇v⟩ = ⟪G, ∇v⟫_{L²}` for every `v ∈ H¹₀(Ω)`, then
  `‖∇(u - w)‖_{L²(Ω)} ≤ ‖G‖_{L²(Ω)}`.

The replacement is unique, by
`UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball`. -/
theorem exists_sub_mem_w1p0Submodule_harmonicOnNhd_ae_eq_of_subset_ball {n : ℕ}
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hball : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z R)
    (u : W1p volume Omega 2) :
    ∃ w : W1p volume Omega 2, u - w ∈ w1p0Submodule volume Omega 2 ∧
      (∀ v : W1p0 volume Omega 2,
        energyFormH1 (fun _ => 1) 0 0 w (v : W1p volume Omega 2) = 0) ∧
      (∃ h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, HarmonicOnNhd h Omega ∧
        (W1p.value w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
          =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] h) ∧
      ∀ G : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
          (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))),
        (∀ v : W1p0 volume Omega 2, energyFormH1 (fun _ => 1) 0 0 u (v : W1p volume Omega 2) =
          ⟪G, W1p.gradient (v : W1p volume Omega 2)⟫_ℝ) →
        ‖W1p.gradient (u - w)‖ ≤ ‖G‖ := by
  have h1 := uniformlyEllipticOn_const_one_one (n := Fin (n + 1))
    (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))
  obtain ⟨w, ⟨huw, hw⟩, -⟩ :=
    UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (b := 0) (c := 0) h1 aestronglyMeasurable_const aestronglyMeasurable_const
      aestronglyMeasurable_const le_rfl
      (fun _ _ => by simp) (gamma := 0) (fun _ _ => by simp) (fun _ _ => le_rfl)
      (le_max_right R 0) (hball.trans (ball_subset_ball (le_max_left R 0))) (by simp) 0 u
  have hw0 : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => 1) 0 0 w (v : W1p volume Omega 2) = 0 := fun v => by
    rw [hw v, ← dirichletForcing_apply_eq_setIntegral, dirichletForcing_apply, inner_zero_left]
  have hsub : u - w ∈ w1p0Submodule volume Omega 2 := by
    have hwu :=
      (ClosedSubmodule.mem_toSubmodule_iff (w - u) (w1p0Submodule volume Omega 2)).2 huw
    exact (ClosedSubmodule.mem_toSubmodule_iff (u - w) _).1 (sub_mem_comm_iff.1 hwu)
  refine ⟨w, hsub, hw0,
    exists_harmonicOnNhd_ae_eq_of_forall_energyFormH1_eq_zero fun φ =>
      hw0 ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩, fun G hG => ?_⟩
  simpa using h1.mul_norm_gradient_sub_le aestronglyMeasurable_const hsub hw0 hG

end PDE

end TauCeti
