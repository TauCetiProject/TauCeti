/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Projection.McCallum.SignInvariant

/-!
# Final sign-invariant CAD lifting by McCallum projection

Lift an analytic CAD adapted to the ambient orders of a McCallum projection to a
sign-invariant CAD for the original family. The projection of the new CAD is exactly the
supplied base CAD, and every lifted cell is an analytic submanifold. Basis members nullified
on a base cell are omitted from its root stack and have sign zero throughout its cylinder.

Unlike an intermediate order-invariant lift, this final sign-invariant lift needs no
well-orientedness assumption at the top level. The lower CAD must still be order-invariant
for the projection; mere sign-invariance of that projection is not substituted for it.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), Sections 2–3.
* C. W. Brown, *The McCallum projection, lifting, and order-invariance* (2005).
-/

public section

open MvPolynomial Polynomial Set

namespace TauCeti.IsCAD

variable {n : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))}
  {𝒟 : Set (Set (Fin n → ℝ))}

/-- **Final sign-invariant CAD lifting.** An analytic base CAD that is order-invariant for
McCallum's projection lifts to a sign-invariant CAD for the original family, with analytic
cells and exactly the given base projections. Nullified basis members are allowed at this
final level, including over positive-dimensional cells. -/
theorem exists_isCAD_signInvariant_of_mcCallumProjection (h𝒟 : IsCAD n 𝒟)
    (hB : F.IsIrreducibleBasis B)
    (hanalytic : ∀ C ∈ 𝒟, ∃ d, IsAnalyticSubmanifold d C)
    (hproj : ∀ q ∈ F.mcCallumProjection B, ∀ C ∈ 𝒟, ∀ x ∈ C, ∀ y ∈ C,
      q.orderAt x = q.orderAt y) :
    ∃ 𝒞, IsCAD (n + 1) 𝒞 ∧ (image Fin.tail '' 𝒞 = 𝒟) ∧
      ∀ E ∈ 𝒞, (∃ e, IsAnalyticSubmanifold e E) ∧
        ∀ f ∈ F, SignInvariant
          (fun y ↦ MvPolynomial.eval y ((finSuccEquiv ℝ n).symm f)) E := by
  apply h𝒟.exists_succ_of_forall_exists_stack
  intro C hC
  obtain ⟨d, hd⟩ := hanalytic C hC
  obtain ⟨k, θ, hθ, hsign⟩ :=
    hB.isSquarefreeBasis.exists_isSemialgebraicStack_signInvariant_of_mcCallumProjection
      hd (h𝒟.isConnected hC).isPreconnected (h𝒟.isSemialgebraic hC)
      (fun q hq ↦ hproj q hq C hC)
  refine ⟨k, θ, hθ, fun E hE ↦ ?_⟩
  obtain ⟨⟨e, -, he⟩, hE⟩ := hsign E hE
  exact ⟨⟨e, he⟩, hE⟩

end TauCeti.IsCAD
