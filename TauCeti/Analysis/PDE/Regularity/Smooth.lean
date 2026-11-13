/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HigherOrder
public import TauCeti.Analysis.Sobolev.Wkp.ContDiffRepresentative
import TauCeti.MeasureTheory.Function.LocalRepresentative

/-!
# Smoothness of weak solutions for smooth coefficients

Let `a` be a uniformly elliptic coefficient field on `Ω` whose entries are smooth on `Ω`, let the
drift `b` and the mass `c` be smooth on `Ω`, and let `u ∈ H¹(Ω)` be a weak solution of the
divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟪b, ∇u⟫ + c u = f` in `Ω`,

meaning `∫_Ω (⟨∇v, a ∇u⟩ + ⟪b, ∇u⟫ v + c u v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with no
boundary condition on `u`.
If, near every point of `Ω`, `f` lies in `W^{k,2}` for every `k` (as it does when `f` is smooth
on `Ω`), then `u` agrees almost everywhere on `Ω` with a function that is smooth on `Ω`. So a weak
solution with smooth coefficients and data is, after modification on a null set, a classical
solution in the interior. No regularity of `∂Ω`, no sign of `c`, no global bound on the derivatives
of the coefficients, and no global integrability of the derivatives of `f` is assumed.

The proof is local. Near a point of `Ω`, the restriction of `u` to a small ball `W` solves the
equation on `W` (`TauCeti.PDE.energyFormH1_restrictL_eq_setIntegral`), with data in every
`W^{k,2}(W)`. Interior `H^{k+2}` regularity
(`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiffOn`) then puts `u` in
every `W^{m,2}(B)` for the concentric ball `B` of half the radius, and the interior Sobolev
embedding (`TauCeti.exists_contDiffOn_ae_eq_of_forall_wkp`) makes `u` smooth on `B`. The smooth
representatives on these balls glue to one on `Ω` (`TauCeti.exists_contDiffOn_ae_eq_of_locally`).

A weak solution of the Dirichlet problem (`TauCeti.PDE.IsWeakSolutionDirichlet`) satisfies the
hypothesis by `TauCeti.PDE.isWeakSolutionDirichlet_iff`. With `a = 1` this covers the Poisson
problem `-Δu = f`, whose weak solution on a domain contained in a ball exists and is unique by
`TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball`.

The statements are for Lebesgue measure `volume`, the measure of the Sobolev embedding.

## Main results

* `TauCeti.PDE.UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_contDiffOn`: for smooth
  coefficients, a weak solution whose data lies locally in every `W^{k,2}` has a representative
  smooth on `Ω`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_energyFormH1_eq_mul_inner`: for
  smooth coefficients, eigenfunctions, such as those of the Dirichlet spectrum, are smooth inside
  `Ω`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_contDiffOn_ae_eq`: the constant-coefficient case.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §6.3.1, Theorem 3 (infinite
  differentiability in the interior).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Corollary 8.11.
-/

public section

open MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {Omega : Opens (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ}

/-- **Interior smoothness for smooth coefficients.** Let `a` be uniformly elliptic on `Ω`, with
entries smooth on `Ω`, let the drift `b` and the mass `c` be smooth on `Ω`, let `f` lie in
`W^{k,2}` of a neighbourhood of each point of `Ω` for every `k`, and let `u ∈ H¹(Ω)` be a weak
solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟪b, ∇u⟫ + c u = f` in `Ω`,

in the sense that `∫_Ω (⟨∇v, a ∇u⟩ + ⟪b, ∇u⟫ v + c u v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,
with no boundary condition on `u`. Then `u` agrees almost everywhere on `Ω` with a function
smooth on `Ω`.

No regularity of `∂Ω` and no sign of `c` is assumed. -/
theorem UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_contDiffOn [DecidableEq ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hb : ContDiffOn ℝ ∞ b Omega) (hc : ContDiffOn ℝ ∞ c Omega) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ x ∈ Omega, ∃ V : Opens (EuclideanSpace ℝ ι), x ∈ V ∧ ∀ k, ∃ F : Wkp volume V 2 k,
      (Wkp.value k F : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (V : Set _)] f)
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a b c u (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) :
    ∃ g : EuclideanSpace ℝ ι → ℝ, ContDiffOn ℝ ∞ g Omega ∧
      (W1p.value u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (Omega : Set _)] g := by
  refine exists_contDiffOn_ae_eq_of_locally fun x hx => ?_
  obtain ⟨V, hxV, hFV⟩ := hf x hx
  obtain ⟨R, hR, hRΩ⟩ := nhds_basis_closedBall.mem_iff.1
    (Filter.inter_mem (Omega.isOpen.mem_nhds hx) (V.isOpen.mem_nhds hxV))
  -- On `W = ball x R` the data lies in every `W^{k,2}(W)`; `u` is smooth on `B = ball x (R / 2)`.
  set W : Opens (EuclideanSpace ℝ ι) := ⟨ball x R, isOpen_ball⟩
  have hWΩ : W ≤ Omega := fun y hy => (hRΩ (ball_subset_closedBall hy)).1
  have hWV : W ≤ V := fun y hy => (hRΩ (ball_subset_closedBall hy)).2
  set B : Opens (EuclideanSpace ℝ ι) := ⟨ball x (R / 2), isOpen_ball⟩
  have hBc : closure (B : Set (EuclideanSpace ℝ ι)) ⊆ closedBall x (R / 2) :=
    closure_ball_subset_closedBall
  have hBW : closure (B : Set (EuclideanSpace ℝ ι)) ⊆ W :=
    hBc.trans (closedBall_subset_ball (half_lt_self hR))
  have hm : ∀ m, ∃ w : Wkp volume B 2 m,
      (Wkp.value m w : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (B : Set _)] W1p.value u := by
    intro m
    obtain ⟨F, hF⟩ := hFV m
    have hFW : (Wkp.value m (Wkp.restrictL hWV m F) : EuclideanSpace ℝ ι → ℝ)
        =ᵐ[volume.restrict (W : Set _)] f :=
      (Wkp.value_restrictL_ae hWV m F).trans (ae_restrict_of_ae_restrict_of_subset hWV hF)
    -- The restriction of `u` to `W` solves the equation there.
    have huW : ∀ v : W1p0 volume W 2,
        energyFormH1 a b c (W1p.restrictL hWΩ u) (v : W1p volume W 2) =
          ∫ y in W, Wkp.value m (Wkp.restrictL hWV m F) y * W1p.value (v : W1p volume W 2) y := by
      intro v
      rw [energyFormH1_restrictL_eq_setIntegral hWΩ hu v]
      refine integral_congr_ae ?_
      filter_upwards [hFW] with y hy
      rw [hy]
    have hWΩ' : (W : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hWΩ
    obtain ⟨U, hU⟩ := (ha.mono_set hWΩ').exists_value_eq_value_restrictL_of_contDiffOn
      (fun i j => (hsmooth i j).mono hWΩ') (hb.mono hWΩ') (hc.mono hWΩ') m huW
      ((isCompact_closedBall x (R / 2)).of_isClosed_subset isClosed_closure hBc) hBW
    refine ⟨Wkp.lowerOrder m (Wkp.lowerOrder (m + 1) U), ?_⟩
    rw [← Wkp.value_succ, ← Wkp.value_succ, hU]
    exact (W1p.value_restrictL_ae _ _).trans (ae_restrict_of_ae_restrict_of_subset
      (subset_closure.trans hBW) (W1p.value_restrictL_ae hWΩ u))
  obtain ⟨g, hg, hug⟩ := exists_contDiffOn_ae_eq_of_forall_wkp hm
  exact ⟨B, isOpen_ball.mem_nhds (mem_ball_self (half_pos hR)), g, hg, hug⟩

open scoped InnerProductSpace in
/-- **Eigenfunctions are smooth in the interior.** Let `a` be uniformly elliptic on `Ω`, with
entries smooth on `Ω`, let the drift `b` and the mass `c` be smooth on `Ω`, with the energy density
of `(a, b, c)` essentially bounded on `Ω`, and let `u ∈ H¹(Ω)` satisfy
`a(u, v) = κ ⟪u, v⟫_{L²(Ω)}` for every `v ∈ H¹₀(Ω)`, that is,

`-∂ᵢ(aⁱʲ ∂ⱼu) + ⟪b, ∇u⟫ + c u = κ u` weakly in `Ω`.

Then `u` agrees almost everywhere on `Ω` with a function smooth on `Ω`. No boundary condition is
used, so in particular every eigenfunction of a Dirichlet eigenvalue
(`TauCeti.PDE.IsDirichletEigenvalue`) is smooth inside `Ω`. -/
theorem UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_energyFormH1_eq_mul_inner [DecidableEq ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega)
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hb : ContDiffOn ℝ ∞ b Omega) (hc : ContDiffOn ℝ ∞ c Omega)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤
      (volume.restrict (Omega : Set (EuclideanSpace ℝ ι))))
    {kappa : ℝ} {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a b c u (v : W1p volume Omega 2) =
      kappa * ⟪W1p.value u, W1p.value (v : W1p volume Omega 2)⟫_ℝ) :
    ∃ g : EuclideanSpace ℝ ι → ℝ, ContDiffOn ℝ ∞ g Omega ∧
      (W1p.value u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (Omega : Set _)] g := by
  -- With the mass shifted by `κ`, `u` solves the homogeneous equation.
  refine ha.exists_contDiffOn_ae_eq_of_contDiffOn hsmooth hb
    (hc.sub (contDiffOn_const (c := kappa))) (f := 0)
    (fun x hx => ⟨Omega, hx, fun k => ⟨0, ?_⟩⟩) fun v => ?_
  · rw [← Wkp.valueL_apply, map_zero]
    exact Lp.coeFn_zero _ _ _
  · rw [energyFormH1_mass_sub_const hcoeff, hu, sub_self]
    simp

/-- **Interior smoothness for a constant principal coefficient.** Let `A` be a constant, uniformly
elliptic matrix, let the drift `b` and the mass `c` be smooth on `Ω`, let `f` lie in `W^{k,2}`
of a neighbourhood of each point of `Ω` for every `k`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(Aⁱʲ ∂ⱼu) + ⟪b, ∇u⟫ + c u = f` in `Ω`,

in the sense that `∫_Ω (⟨∇v, A ∇u⟩ + ⟪b, ∇u⟫ v + c u v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,
with no boundary condition on `u`. Then `u` agrees almost everywhere on `Ω` with a function
smooth on `Ω`. This is the constant case of
`TauCeti.PDE.UniformlyEllipticOn.exists_contDiffOn_ae_eq_of_contDiffOn`. -/
theorem UniformlyEllipticOn.exists_contDiffOn_ae_eq {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hb : ContDiffOn ℝ ∞ b Omega) (hc : ContDiffOn ℝ ∞ c Omega) {f : EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ x ∈ Omega, ∃ V : Opens (EuclideanSpace ℝ ι), x ∈ V ∧ ∀ k, ∃ F : Wkp volume V 2 k,
      (Wkp.value k F : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (V : Set _)] f)
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 (fun _ => A) b c u (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) :
    ∃ g : EuclideanSpace ℝ ι → ℝ, ContDiffOn ℝ ∞ g Omega ∧
      (W1p.value u : EuclideanSpace ℝ ι → ℝ) =ᵐ[volume.restrict (Omega : Set _)] g := by
  classical
  exact (uniformlyEllipticOn_const _ hlam hA).exists_contDiffOn_ae_eq_of_contDiffOn
    (fun _ _ => contDiffOn_const) hb hc hf hu

end PDE

end TauCeti
