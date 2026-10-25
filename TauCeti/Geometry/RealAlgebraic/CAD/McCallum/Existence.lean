/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.CAD.McCallum.Basic
public import TauCeti.Geometry.RealAlgebraic.CAD.McCallum.SignInvariant

/-!
# Recursive sign-invariant McCallum decompositions

Construct a sign-invariant CAD with analytic cells when the McCallum projection is
well-oriented. The top-level basis may be any squarefree, pairwise relatively prime primitive
basis. Recursive order-invariant decomposition is applied to the projection, and
sign-invariant lifting is used at the final level. Thus the input basis may be nullified on
positive-dimensional base cells; the finite-nullification condition is required only at the
lower levels. The resulting CAD retains order-invariance of the projection on its base cells.

In three variables the projection is bivariate and hence always well-oriented. Consequently
McCallum projection gives a sign-invariant analytic CAD for every three-variable family,
even without a well-orientedness hypothesis on that family.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  Springer (1998), Section 5.
* C. W. Brown, *The McCallum projection, lifting, and order-invariance* (2005).
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {n : ℕ} [∀ m, NormalizedGCDMonoid (MvPolynomial (Fin m) ℝ)]

/-- **Recursive sign-invariant McCallum correctness.** If the McCallum projection of a
squarefree basis of `F` is well-oriented, there is a sign-invariant CAD for `F` with analytic
cells. Its base CAD is order-invariant for that projection. No restriction is imposed on
nullification of the top-level basis, including over positive-dimensional base cells. -/
theorem exists_isCAD_signInvariant_of_isMcCallumWellOriented_projection
    {F : Finset (MvPolynomial (Fin (n + 1)) ℝ)}
    {B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))}
    (hB : (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).IsSquarefreeBasis B)
    (hproj : IsMcCallumWellOriented n
      ((F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).mcCallumProjection B)) :
    ∃ 𝒞, IsCAD (n + 1) 𝒞 ∧
      (∀ E ∈ 𝒞, ∃ d, IsAnalyticSubmanifold d E) ∧
      (∀ f ∈ F, ∀ E ∈ 𝒞, SignInvariant (fun x ↦ eval x f) E) ∧
      ∀ q ∈ (F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding).mcCallumProjection B,
        ∀ C ∈ image Fin.tail '' 𝒞, ∀ x ∈ C, ∀ y ∈ C, q.orderAt x = q.orderAt y := by
  obtain ⟨𝒟, h𝒟, ha, ho⟩ := exists_isCAD_orderAt_eq_of_isMcCallumWellOriented hproj
  obtain ⟨𝒞, h𝒞, htail, hc⟩ :=
    h𝒟.exists_isCAD_signInvariant_of_mcCallumProjection hB ha ho
  refine ⟨𝒞, h𝒞, fun E hE ↦ (hc E hE).1, fun f hf E hE ↦ ?_, ?_⟩
  · have hmem : finSuccEquiv ℝ n f ∈ F.map (finSuccEquiv ℝ n).toEquiv.toEmbedding :=
      Finset.mem_map.mpr ⟨f, hf, rfl⟩
    simpa only [AlgEquiv.symm_apply_apply] using (hc E hE).2 _ hmem
  · rw [htail]
    exact ho

end TauCeti
