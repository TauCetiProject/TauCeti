/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.ClassicalSolution
public import TauCeti.Analysis.PDE.FundamentalSolution.Euclidean.Potential
import TauCeti.Analysis.PDE.PoissonIntegral.Ball

/-!
# The Dirichlet problem on a ball via the Newtonian potential

Let `B = B(z, R) ⊆ ℝⁿ`, `n ≥ 3`, and let `f` be of class `C²` with compact support. The
classical solution of `-Δu = f` in `B`, `u = 0` on `∂B`, is the Newtonian potential `Gₙ ⋆ f`
corrected by the harmonic function `h` on `B` with boundary values `Gₙ ⋆ f` on the sphere:
`u = Gₙ ⋆ f - h`. Such an `h` exists, given by the Poisson integral
(`TauCeti.exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere`).

This file shows that this classical solution is the weak solution: the unique `u ∈ H¹₀(B)` with
`∫_B ∇v · ∇u = ∫_B f v` for every `v ∈ H¹₀(B)`
(`TauCeti.PDE.existsUnique_isWeakSolutionDirichlet_laplacian_of_subset_ball`) agrees almost
everywhere with `Gₙ ⋆ f - h`. So the variational solution produced by Lax--Milgram, the
Newtonian potential, and the Poisson integral describe the same function. The comparison rests on
`TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_of_contDiffOn`: a function of class `C²` inside
a bounded domain, continuous up to the boundary and vanishing there, is the weak solution of the
Dirichlet problem for its own Laplacian.

## Main declarations

* `TauCeti.PDE.IsWeakSolutionDirichlet.value_ae_eq_newtonianKernel_convolution_sub`: the weak
  solution on a ball is `Gₙ ⋆ f - h` for every harmonic `h` with boundary values `Gₙ ⋆ f`.
* `TauCeti.PDE.IsWeakSolutionDirichlet.exists_harmonicOnNhd_value_ae_eq`: such an `h` exists.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.1 (the Newtonian potential), Section
  2.2.4 (Green's function) and Section 6.2 (weak solutions).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 2.5 and Theorem 8.3.
-/

public section

namespace TauCeti

namespace PDE

open InnerProductSpace Laplacian MeasureTheory Metric Set TopologicalSpace
open scoped Convolution

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {z : EuclideanSpace ℝ (Fin (n + 1))}
  {R : ℝ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {g : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
  {u : W1p0 volume Omega 2}

/-- **The weak solution of Poisson's equation on a ball is the corrected Newtonian potential.**
Let `n ≥ 2`, let `f` be of class `C²` with compact support on `ℝ^{n+1}`, and let `h` be harmonic
on the ball `B(z, R)`, continuous on its closure and equal to the Newtonian potential `G ⋆ f` on
the sphere. If `u ∈ H¹₀(B)` is the weak solution of `-Δu = f` in `B`, `u = 0` on `∂B`, then
`u = G ⋆ f - h` almost everywhere on `B`. -/
theorem IsWeakSolutionDirichlet.value_ae_eq_newtonianKernel_convolution_sub (hn : 2 ≤ n)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) {h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hh : HarmonicOnNhd h (ball z R)) (hhc : ContinuousOn h (closedBall z R))
    (hhG : EqOn h (newtonianKernel (n + 1) ⋆ f) (sphere z R))
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball z R)
    (hg : g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] f)
    (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 g u) :
    W1p.value (u : W1p volume Omega 2)
      =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
        newtonianKernel (n + 1) ⋆ f - h := by
  rcases le_or_gt R 0 with hR | hR
  · -- The ball is empty, and there is nothing to prove.
    refine (ae_restrict_iff' Omega.isOpen.measurableSet).2 (ae_of_all _ fun x hx => ?_)
    rw [hΩ, ball_eq_empty.2 hR] at hx
    exact absurd hx (notMem_empty x)
  have hv := contDiff_newtonianKernel_convolution (n := n + 1) hf hc
  have hΔ : ∀ x ∈ ball z R, Δ (newtonianKernel (n + 1) ⋆ f - h) x = -f x := fun x hx => by
    rw [hv.contDiffAt.laplacian_sub (hh x hx).1, laplacian_newtonianKernel_convolution
      (by omega) hf hc, (hh x hx).2.eq_of_nhds, Pi.zero_apply, sub_zero, Pi.neg_apply]
  refine hu.value_ae_eq_of_contDiffOn hΩ.le ?_ ?_ ?_ ?_
  · rw [hΩ]
    exact hv.contDiffOn.sub fun x hx => (hh x hx).1.contDiffWithinAt
  · rw [hΩ, closure_ball z hR.ne']
    exact hv.continuous.continuousOn.sub hhc
  · intro x hx
    rw [hΩ, frontier_ball z hR.ne'] at hx
    rw [Pi.sub_apply, hhG hx, sub_self]
  · filter_upwards [hg, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
    rw [hx, Pi.neg_apply, hΔ x (hΩ ▸ hxΩ), neg_neg]

/-- **The Dirichlet problem for Poisson's equation on a ball.** Let `n ≥ 2` and let `f` be of
class `C²` with compact support on `ℝ^{n+1}`. The weak solution `u ∈ H¹₀(B)` of `-Δu = f` in the
ball `B = B(z, R)`, `u = 0` on `∂B`, is the Newtonian potential corrected by a harmonic function:
there is `h`, harmonic on `B`, continuous on its closure and equal to `G ⋆ f` on the sphere, with
`u = G ⋆ f - h` almost everywhere on `B`. -/
theorem IsWeakSolutionDirichlet.exists_harmonicOnNhd_value_ae_eq (hn : 2 ≤ n)
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (hΩ : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball z R)
    (hg : g =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))] f)
    (hu : IsWeakSolutionDirichlet (fun _ => 1) 0 0 g u) :
    ∃ h : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, HarmonicOnNhd h (ball z R) ∧
      ContinuousOn h (closedBall z R) ∧ EqOn h (newtonianKernel (n + 1) ⋆ f) (sphere z R) ∧
      W1p.value (u : W1p volume Omega 2)
        =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
          newtonianKernel (n + 1) ⋆ f - h := by
  obtain ⟨h, hh, hhc, hhG⟩ := exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere
    (contDiff_newtonianKernel_convolution (n := n + 1) hf hc).continuous.continuousOn
  exact ⟨h, hh, hhc, hhG,
    hu.value_ae_eq_newtonianKernel_convolution_sub hn hf hc hh hhc hhG hΩ hg⟩

end PDE

end TauCeti
