/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic

/-!
# The second fundamental form through the inward unit normal

The second fundamental form of the boundary is `II_q(u, w) = ⟨∇_{dι u} N, dι w⟩` for every
extension `N` of the outward unit normal
(`TauCeti.boundarySecondFundamentalForm_apply_eq_inner_of_eq_outwardUnitNormal`). With an
extension `N` of the inward unit normal the same expression is `-II_q(u, w)`
(`TauCeti.inner_leviCivitaConnection_of_eq_inwardUnitNormal`): the sign convention of `II` is
tied to the outward normal, and using the inward normal in the first description reverses it.
-/

public section

open Bundle Filter
open scoped Manifold ContDiff InnerProductSpace Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
  [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- **The inward normal reverses the sign of the second fundamental form.** For every vector
field `N` on `M`, differentiable at `q ∈ ∂M` and equal to the inward unit normal at the boundary
points near `q`, `⟨∇_{dι u} N, dι w⟩ = -II_q(u, w)`. -/
theorem inner_leviCivitaConnection_of_eq_inwardUnitNormal
    (q : (𝓡∂ (n + 1)).boundary M) (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    {N : (y : M) → TangentSpace (𝓡∂ (n + 1)) y} (hN : MDiffAt (T% N) (q : M))
    (hNν : ∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q, N p = inwardUnitNormal p) :
    ⟪CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M N q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q u),
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) q w⟫_ℝ =
      -boundarySecondFundamentalForm q u w := by
  -- `-N` extends the outward unit normal.
  have hN' : MDiffAt (T% ((-1 : ℝ) • N)) (q : M) :=
    mdifferentiableAt_const.smul_section hN
  have hNν' : ∀ᶠ p : (𝓡∂ (n + 1)).boundary M in 𝓝 q,
      ((-1 : ℝ) • N) (p : M) = outwardUnitNormal p := by
    filter_upwards [hNν] with p hp
    rw [Pi.smul_apply, hp, neg_one_smul, neg_inwardUnitNormal]
  rw [boundarySecondFundamentalForm_apply_eq_inner_of_eq_outwardUnitNormal q u w hN' hNν',
    (CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) M).isCovariantDerivativeOn.smul_const
      (s := Set.univ) (-1 : ℝ) hN, neg_one_smul, neg_apply, inner_neg_left, neg_neg]

end TauCeti
