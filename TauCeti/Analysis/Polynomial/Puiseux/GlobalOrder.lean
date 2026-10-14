/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.AmbientOrder
public import TauCeti.Topology.LocallyConstant.Preconnected

/-!
# Ambient order on root sections over connected open bases

The local discriminant-order theorem gives local constancy of ambient polynomial order along a
continuous root section. On a preconnected open base, that local result gives a single constant
order on the whole section. This global form is useful when assembling local McCallum lifting
data over connected base regions.
-/

public section

open Filter Polynomial Set Topology

namespace Polynomial.Monic

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- **Ambient order is constant on a root section.** Let a monic polynomial family have
discriminant of constant finite ambient order along a real analytic map on an open preconnected
set. Every continuous section consisting of roots then has constant ambient order there. -/
theorem orderAt_root_eq_of_orderAt_discr_eq
    {p : Polynomial (MvPolynomial (Fin n) ℝ)} (hp : p.Monic)
    {φ : (ι → ℝ) → Fin n → ℝ} {θ : (ι → ℝ) → ℝ} {U : Set (ι → ℝ)} {m : ℕ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hφ : AnalyticOnNhd ℝ φ U)
    (hm : ∀ x ∈ U, p.discr.orderAt (φ x) = m)
    (hθ : ContinuousOn θ U)
    (hroot : ∀ x ∈ U, (p.map (MvPolynomial.eval (φ x))).IsRoot (θ x))
    {x y : ι → ℝ} (hx : x ∈ U) (hy : y ∈ U) :
    ((MvPolynomial.finSuccEquiv ℝ n).symm p).orderAt (Fin.cons (θ x) (φ x)) =
      ((MvPolynomial.finSuccEquiv ℝ n).symm p).orderAt (Fin.cons (θ y) (φ y)) := by
  apply hconn.apply_eq_of_eventually_eq _ hx hy
  intro a ha
  have hdiscr : ∀ᶠ z in 𝓝 a, p.discr.orderAt (φ z) = m := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hm z hz
  have hroot' : ∀ᶠ z in 𝓝 a, (p.map (MvPolynomial.eval (φ z))).IsRoot (θ z) := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hroot z hz
  exact (Polynomial.eventually_orderAt_root_eq_of_orderAt_discr_eq (hφ a ha)
    (hp.map _).ne_zero hdiscr (hθ.continuousAt (hU.mem_nhds ha)) hroot').filter_mono
      nhdsWithin_le_nhds

end Polynomial.Monic
