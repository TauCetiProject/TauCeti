/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Descending diffeomorphisms through smooth retractions

A diffeomorphism that carries the fibres of one smooth retraction onto the fibres of
another induces a unique diffeomorphism between the bases. Smooth sections give formulas
for both the induced map and its inverse, so no smooth structure on a quotient needs to
be constructed. This applies, for example, to the hyperbolic base of the universal cover
of the unit tangent bundle of the hyperbolic plane.

Reference: P. Scott, *The geometries of 3-manifolds*, Section 4, pp. 464–465
(descent of isometries to the hyperbolic base).
-/

public section

open Function
open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H H' G G' : Type*}
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

/-- A diffeomorphism carrying fibres onto fibres descends uniquely along smooth maps with
smooth sections. The bases and total spaces may have different models, and every
differentiability order is allowed. -/
theorem existsUnique_descend (f : M ≃ₘ^n⟮I, I'⟯ M')
    {p : M → N} {p' : M' → N'} {s : N → M} {s' : N' → M'}
    (hp : ContMDiff I J n p) (hp' : ContMDiff I' J' n p')
    (hs : ContMDiff J I n s) (hs' : ContMDiff J' I' n s')
    (hps : RightInverse s p) (hps' : RightInverse s' p')
    (hf : ∀ x y, p' (f x) = p' (f y) ↔ p x = p y) :
    ∃! g : N ≃ₘ^n⟮J, J'⟯ N', ∀ x, g (p x) = p' (f x) := by
  have hforward (x : M) : p' (f (s (p x))) = p' (f x) :=
    (hf _ _).mpr (hps _)
  have hbackward (x : M') : p (f.symm (s' (p' x))) = p (f.symm x) := by
    apply (hf _ _).mp
    simpa only [f.apply_symm_apply] using hps' (p' x)
  let g : N ≃ₘ^n⟮J, J'⟯ N' :=
    { toFun := p' ∘ f ∘ s
      invFun := p ∘ f.symm ∘ s'
      left_inv := fun y => by
        simpa only [Function.comp_apply, f.symm_apply_apply] using
          (hbackward (f (s y))).trans (by rw [f.symm_apply_apply]; exact hps y)
      right_inv := fun y => by
        simpa only [Function.comp_apply, f.apply_symm_apply] using
          (hforward (f.symm (s' y))).trans (by rw [f.apply_symm_apply]; exact hps' y)
      contMDiff_toFun := hp'.comp (f.contMDiff.comp hs)
      contMDiff_invFun := hp.comp (f.symm.contMDiff.comp hs') }
  refine ⟨g, hforward, ?_⟩
  intro g' hg'
  apply Diffeomorph.ext
  intro y
  rw [← hps y]
  exact (hg' (s y)).trans (hforward (s y)).symm

end Diffeomorph
