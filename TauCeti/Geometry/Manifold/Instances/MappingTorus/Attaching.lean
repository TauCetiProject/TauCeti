/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus

/-!
# Monodromy in prescribed attaching coordinates

Given lower and upper coordinate diffeomorphisms `θ₀` and `θ₁` and an attaching diffeomorphism
`g`, the monodromy `θ₀ ∘ g ∘ θ₁⁻¹` realizes the attachment in the smooth mapping torus:
`[1 + t, θ₁ z] = [t, θ₀ (g z)]`. The construction applies at every regularity and needs no
Hausdorffness, local compactness or manifold-regularity hypothesis.

The attaching-coordinate construction is adapted from
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture), with
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) as a
supporting formalization reference.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The monodromy realizing an attachment between two chosen coordinate diffeomorphisms. -/
def attachingMonodromy (θ₀ θ₁ g : M ≃ₘ^n⟮I, I⟯ M) : M ≃ₘ^n⟮I, I⟯ M :=
  θ₁.symm.trans (g.trans θ₀)

/-- The attaching monodromy changes from the upper coordinates to the prescribed lower ones. -/
@[simp]
theorem attachingMonodromy_apply (θ₀ θ₁ g : M ≃ₘ^n⟮I, I⟯ M) (z : M) :
    attachingMonodromy θ₀ θ₁ g z = θ₀ (g (θ₁.symm z)) := by
  simp only [attachingMonodromy, Diffeomorph.coe_trans, Function.comp_apply]

/-- The quotient seam follows the prescribed attachment in the chosen coordinates. -/
theorem mk_one_add_attachingMonodromy (θ₀ θ₁ g : M ≃ₘ^n⟮I, I⟯ M) (z : M) (t : ℝ) :
    mk (attachingMonodromy θ₀ θ₁ g) (1 + t) (θ₁ z) =
      mk (attachingMonodromy θ₀ θ₁ g) t (θ₀ (g z)) := by
  rw [add_comm 1 t, mk_add_one]
  simp only [attachingMonodromy_apply, Diffeomorph.symm_apply_apply]

end TauCeti.SmoothMappingTorus
