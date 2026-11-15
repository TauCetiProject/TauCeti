/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Submersion
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Recognizing diffeomorphisms through submersions

A bijection commuting with two submersions out of a common boundaryless manifold, the first of
which is surjective, is a diffeomorphism. Unlike the immersion counterpart in
`TauCeti.Geometry.Manifold.Immersion.Diffeomorph`, continuity of the bijection is not assumed:
smoothness (and hence continuity) in both directions descends from the ambient manifold along the
surjective submersions via `Manifold.IsSubmersion.contMDiff_comp_iff`. This identifies smooth
structures induced on the same quotient space, or compares an abstract orbit space with a concrete
quotient manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.29 and Corollary 4.31 (uniqueness of quotient manifold structures).
-/

public section

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F V H G W : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [TopologicalSpace W]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {K : ModelWithCorners 𝕜 V W} [K.Boundaryless]
  {P M N : Type*} [TopologicalSpace P] [ChartedSpace W P]
  [TopologicalSpace M] [cM : ChartedSpace H M]
  [TopologicalSpace N] [cN : ChartedSpace G N]
  {n : ℕ∞ω} {p : P → M} {q : P → N}

namespace Equiv

/-- A bijection commuting with two `C^n` submersions out of a common boundaryless manifold, the
first of which is surjective, is a `C^n` diffeomorphism. Neither continuity of `e` nor
finite-dimensionality, separation, or target boundarylessness is required. -/
def diffeomorphOfSubmersions (e : M ≃ N)
    (hp : Manifold.IsSubmersion K I n p) (hpsurj : Function.Surjective p)
    (hq : Manifold.IsSubmersion K J n q)
    (h : e ∘ p = q) : M ≃ₘ^n⟮I, J⟯ N where
  toEquiv := e
  contMDiff_toFun := (hp.contMDiff_comp_iff hpsurj le_rfl).1 (h.symm ▸ hq.contMDiff)
  contMDiff_invFun := by
    have hqsurj : Function.Surjective q := h ▸ e.surjective.comp hpsurj
    have h' : e.symm ∘ q = p := by
      ext x
      simpa only [Function.comp_apply, e.symm_apply_apply] using congrArg e.symm (congrFun h x).symm
    exact (hq.contMDiff_comp_iff hqsurj le_rfl).1 (h'.symm ▸ hp.contMDiff)

/-- Recognizing smoothness through submersions does not change the underlying equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_toEquiv (e : M ≃ N)
    (hp : Manifold.IsSubmersion K I n p) (hpsurj : Function.Surjective p)
    (hq : Manifold.IsSubmersion K J n q)
    (h : e ∘ p = q) : (e.diffeomorphOfSubmersions hp hpsurj hq h).toEquiv = e := by
  ext x
  rfl

/-- The diffeomorphism acts by the original equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_apply (e : M ≃ N)
    (hp : Manifold.IsSubmersion K I n p) (hpsurj : Function.Surjective p)
    (hq : Manifold.IsSubmersion K J n q)
    (h : e ∘ p = q) (x : M) : e.diffeomorphOfSubmersions hp hpsurj hq h x = e x :=
  (rfl)

/-- The inverse diffeomorphism acts by the inverse equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_symm_apply (e : M ≃ N)
    (hp : Manifold.IsSubmersion K I n p) (hpsurj : Function.Surjective p)
    (hq : Manifold.IsSubmersion K J n q)
    (h : e ∘ p = q) (y : N) : (e.diffeomorphOfSubmersions hp hpsurj hq h).symm y = e.symm y :=
  (rfl)

end Equiv

namespace ChartedSpace

omit cM in
/-- Two atlases on the same topological space are `C^n` diffeomorphic by the identity whenever the
same surjective map out of a boundaryless manifold is a `C^n` submersion for both atlases. -/
theorem exists_diffeomorph_apply_eq_self_of_isSubmersion (a : ChartedSpace H M)
    (b : ChartedSpace G M)
    (hp : letI := a; Manifold.IsSubmersion K I n p) (hpsurj : Function.Surjective p)
    (hq : letI := b; Manifold.IsSubmersion K J n p) :
    ∃ e : @Diffeomorph 𝕜 _ _ _ _ _ _ _ _ _ _ _ I J M _ a M _ b n, ∀ x, e x = x :=
  ⟨Equiv.diffeomorphOfSubmersions (cM := a) (cN := b)
    (Equiv.refl _) hp hpsurj hq rfl, fun _ ↦ rfl⟩

end ChartedSpace
