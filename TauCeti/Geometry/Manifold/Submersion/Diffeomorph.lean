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
# Recognizing diffeomorphisms through surjective submersions

A bijection commuting with two surjective `C^n` submersions out of a common boundaryless manifold is
a `C^n` diffeomorphism (`Equiv.diffeomorphOfSubmersions`). Unlike the immersion counterpart
`Homeomorph.diffeomorphOfImmersions`, no continuity hypothesis on the bijection is required: local
`C^n` sections of each submersion descend smoothness of both directions directly
(`Manifold.IsSubmersion.contMDiff_comp_iff`). In particular, two atlases on the same space making a
common surjective map out of a boundaryless manifold a `C^n` submersion are `C^n`-diffeomorphic by
the identity (`ChartedSpace.exists_diffeomorph_apply_eq_self_of_isSubmersion`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 4.31
  (uniqueness of quotient manifold structures).
-/

public section

open Function Manifold
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F V H G W : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [TopologicalSpace W]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {K : ModelWithCorners 𝕜 V W} [K.Boundaryless]
  {M N P : Type*} [TopologicalSpace M] [cM : ChartedSpace H M]
  [TopologicalSpace N] [cN : ChartedSpace G N] [TopologicalSpace P] [ChartedSpace W P]
  {n : ℕ∞ω} {p : P → M} {q : P → N}

namespace Equiv

/-- **Recognizing diffeomorphisms through surjective submersions.** A bijection commuting with two
surjective `C^n` submersions out of a common boundaryless manifold is a `C^n` diffeomorphism. No
continuity assumption on `e` and no finite-dimensionality or separation hypotheses are required. -/
def diffeomorphOfSubmersions (e : M ≃ N)
    (hp : IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : IsSubmersion K J n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) : M ≃ₘ^n⟮I, J⟯ N where
  toEquiv := e
  contMDiff_toFun := (hp.contMDiff_comp_iff hp_surj le_rfl).1 (h.symm ▸ hq.contMDiff)
  contMDiff_invFun := by
    refine (hq.contMDiff_comp_iff hq_surj le_rfl).1 ?_
    have h' : e.symm ∘ q = p := by
      ext z
      simpa only [comp_apply, e.symm_apply_apply] using congrArg e.symm (congrFun h z).symm
    exact h'.symm ▸ hp.contMDiff

/-- Recognizing smoothness through surjective submersions preserves the underlying equivalence. -/
@[simp]
theorem diffeomorphOfSubmersions_toEquiv (e : M ≃ N)
    (hp : IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : IsSubmersion K J n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) : (e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h).toEquiv = e :=
  (rfl)

/-- `diffeomorphOfSubmersions` acts by the original bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_apply (e : M ≃ N)
    (hp : IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : IsSubmersion K J n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) (x : M) : e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h x = e x :=
  (rfl)

/-- The inverse of `diffeomorphOfSubmersions` acts by the inverse bijection. -/
@[simp]
theorem diffeomorphOfSubmersions_symm_apply (e : M ≃ N)
    (hp : IsSubmersion K I n p) (hp_surj : Surjective p)
    (hq : IsSubmersion K J n q) (hq_surj : Surjective q)
    (h : e ∘ p = q) (y : N) :
    (e.diffeomorphOfSubmersions hp hp_surj hq hq_surj h).symm y = e.symm y :=
  (rfl)

end Equiv

namespace ChartedSpace

omit cM in
/-- **Uniqueness of quotient smooth structures.** Two atlases on the same topological space `M` are
`C^n`-diffeomorphic via the identity whenever the same surjective map out of a boundaryless manifold
is a `C^n` submersion for both atlases. -/
theorem exists_diffeomorph_apply_eq_self_of_isSubmersion (a : ChartedSpace H M)
    (b : ChartedSpace G M) (hp_surj : Surjective p)
    (ha : letI := a; IsSubmersion K I n p)
    (hb : letI := b; IsSubmersion K J n p) :
    ∃ e : @Diffeomorph 𝕜 _ _ _ _ _ _ _ _ _ _ _ I J M _ a M _ b n, ∀ x, e x = x :=
  ⟨Equiv.diffeomorphOfSubmersions (cM := a) (cN := b)
    (Equiv.refl M) ha hp_surj hb hp_surj rfl, fun _ ↦ rfl⟩

end ChartedSpace
