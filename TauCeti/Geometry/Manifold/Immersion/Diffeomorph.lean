/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Immersion

/-!
# Recognizing diffeomorphisms through immersions

A homeomorphism commuting with two immersions into a common manifold is a diffeomorphism.
This is useful for comparing smooth structures induced on the same topological subspace.
The smooth lifting property of immersions is `ContMDiff.iff_comp_isImmersion` in Mathlib.
-/

public section

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F V H G W : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [TopologicalSpace W]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {K : ModelWithCorners 𝕜 V W}
  {M N P : Type*} [TopologicalSpace M] [cM : ChartedSpace H M]
  [TopologicalSpace N] [cN : ChartedSpace G N] [TopologicalSpace P] [ChartedSpace W P]
  {n : ℕ∞ω} {i : M → P} {j : N → P}

namespace Homeomorph

/-- A homeomorphism commuting with two immersions into a common manifold is a `C^n`
diffeomorphism. No finite-dimensionality or separation hypotheses are required. -/
def diffeomorphOfImmersions (e : M ≃ₜ N)
    (hi : Manifold.IsImmersion I K n i) (hj : Manifold.IsImmersion J K n j)
    (h : j ∘ e = i) : M ≃ₘ^n⟮I, J⟯ N where
  toEquiv := e.toEquiv
  contMDiff_toFun := (ContMDiff.iff_comp_isImmersion hj).2
    ⟨e.continuous, h.symm ▸ hi.contMDiff⟩
  contMDiff_invFun := by
    refine (ContMDiff.iff_comp_isImmersion hi).2 ⟨e.symm.continuous, ?_⟩
    have h' : i ∘ e.symm = j := by
      ext y
      simpa only [Function.comp_apply, e.apply_symm_apply] using (congrFun h (e.symm y)).symm
    exact h'.symm ▸ hj.contMDiff

/-- Recognizing smoothness through immersions does not change the homeomorphism. -/
@[simp]
theorem diffeomorphOfImmersions_toHomeomorph (e : M ≃ₜ N)
    (hi : Manifold.IsImmersion I K n i) (hj : Manifold.IsImmersion J K n j)
    (h : j ∘ e = i) : (e.diffeomorphOfImmersions hi hj h).toHomeomorph = e := by
  ext x
  rfl

/-- The diffeomorphism acts by the original homeomorphism. -/
@[simp]
theorem diffeomorphOfImmersions_apply (e : M ≃ₜ N)
    (hi : Manifold.IsImmersion I K n i) (hj : Manifold.IsImmersion J K n j)
    (h : j ∘ e = i) (x : M) : e.diffeomorphOfImmersions hi hj h x = e x :=
  (rfl)

/-- The inverse diffeomorphism acts by the inverse homeomorphism. -/
@[simp]
theorem diffeomorphOfImmersions_symm_apply (e : M ≃ₜ N)
    (hi : Manifold.IsImmersion I K n i) (hj : Manifold.IsImmersion J K n j)
    (h : j ∘ e = i) (y : N) : (e.diffeomorphOfImmersions hi hj h).symm y = e.symm y :=
  (rfl)

end Homeomorph

namespace ChartedSpace

omit cM in
/-- Two atlases on the same topological space are diffeomorphic by the identity whenever the
same map into a common manifold is an immersion for both atlases. -/
theorem exists_diffeomorph_apply_eq_self (a : ChartedSpace H M) (b : ChartedSpace G M)
    (hi : letI := a; Manifold.IsImmersion I K n i)
    (hj : letI := b; Manifold.IsImmersion J K n i) :
    ∃ e : @Diffeomorph 𝕜 _ _ _ _ _ _ _ _ _ _ _ I J M _ a M _ b n, ∀ x, e x = x :=
  ⟨Homeomorph.diffeomorphOfImmersions (cM := a) (cN := b)
    (Homeomorph.refl _) hi hj rfl, fun _ ↦ rfl⟩

end ChartedSpace
