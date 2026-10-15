/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Diffeomorph
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linear splitting coordinates for distributions

A distribution on a finite-dimensional normed space can be put into product coordinates at any
chosen point. Its fibre at the point supplies the horizontal factor, while a complementary
subspace supplies the vertical factor. Pullback by the resulting continuous linear equivalence
preserves smoothness and involutivity, and the pulled-back fibre at the chosen point is exactly the
horizontal subspace.

This is the linear-coordinate step in the proof of the Frobenius theorem. In these coordinates the
distribution is transverse to the vertical factor at the base point, so it can subsequently be
written locally as a graph distribution.

## Main results

* TauCeti.distributionModelFiber: a tangent-space fibre transported to the model vector space.
* TauCeti.IsContMDiffDistribution.exists_splitCoordinates: product coordinates in which the
  pulled-back distribution has horizontal base fibre.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 19,
  proof of Theorem 19.12.
* S. Lang, *Fundamentals of Differential Geometry*, Springer GTM 191 (1999), Chapter VI, §1.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

section ModelFiber

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The fibre of a distribution on a normed space, transported from the tangent space to the model
vector space by its canonical identification. -/
noncomputable def distributionModelFiber
    (D : (x : E) → Submodule 𝕜 (TangentSpace 𝓘(𝕜, E) x)) (p : E) : Submodule 𝕜 E :=
  (D p).map (NormedSpace.fromTangentSpace (𝕜 := 𝕜) p).toLinearMap

/-- Membership in distributionModelFiber expressed in the original tangent-space fibre. -/
@[simp]
theorem mem_distributionModelFiber
    {D : (x : E) → Submodule 𝕜 (TangentSpace 𝓘(𝕜, E) x)} {p v : E} :
    v ∈ distributionModelFiber D p ↔
      (NormedSpace.fromTangentSpace (𝕜 := 𝕜) p).symm v ∈ D p := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro hv
    exact ⟨_, hv, (NormedSpace.fromTangentSpace (𝕜 := 𝕜) p).apply_symm_apply v⟩

private theorem distributionModelFiber_eq
    {D : (x : E) → Submodule 𝕜 (TangentSpace 𝓘(𝕜, E) x)} (p : E) :
    distributionModelFiber D p = D p := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hv
  · intro v hv
    exact ⟨v, hv, rfl⟩

end ModelFiber

section Splitting

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- A smooth involutive distribution on a finite-dimensional normed space admits linear product
coordinates at any chosen point in which its fibre is the horizontal subspace.

The horizontal factor is the fibre itself, transported to the model vector space, and the vertical
factor is a complementary subspace. The returned distribution is the pullback by the corresponding
continuous linear equivalence, with tangent fibres canonically identified with the product model
space. It retains the original rank, regularity, and involutivity. -/
theorem IsContMDiffDistribution.exists_splitCoordinates {k : ℕ}
    {D : (x : E) → Submodule 𝕜 (TangentSpace 𝓘(𝕜, E) x)}
    (hD : IsContMDiffDistribution 𝓘(𝕜, E) ∞ k D)
    (hinv : IsInvolutiveDistribution 𝓘(𝕜, E) D) (p : E) :
    ∃ (T : Submodule 𝕜 E) (hT : IsCompl (distributionModelFiber D p) T),
      let e : (distributionModelFiber D p × T) ≃L[𝕜] E :=
        (Submodule.prodEquivOfIsCompl (distributionModelFiber D p) T hT).toContinuousLinearEquiv
      let Dt : (q : distributionModelFiber D p × T) →
          Submodule 𝕜 (TangentSpace 𝓘(𝕜, distributionModelFiber D p × T) q) := fun q ↦
        (D (e.toDiffeomorph q)).comap
          (mfderiv 𝓘(𝕜, distributionModelFiber D p × T) 𝓘(𝕜, E)
            e.toDiffeomorph q).toLinearMap
      let D' : distributionModelFiber D p × T →
          Submodule 𝕜 (distributionModelFiber D p × T) := fun q ↦
        distributionModelFiber Dt q
      Module.finrank 𝕜 (distributionModelFiber D p) = k ∧
        IsContMDiffDistribution 𝓘(𝕜, distributionModelFiber D p × T) ∞ k D' ∧
        IsInvolutiveDistribution 𝓘(𝕜, distributionModelFiber D p × T) D' ∧
        D' (e.symm p) = Submodule.prod ⊤ ⊥ := by
  let _ : CompleteSpace E := FiniteDimensional.complete 𝕜 _
  obtain ⟨T, hT⟩ := (distributionModelFiber D p).exists_isCompl
  refine ⟨T, hT, ?_⟩
  let _ : CompleteSpace (distributionModelFiber D p) := FiniteDimensional.complete 𝕜 _
  let _ : CompleteSpace T := FiniteDimensional.complete 𝕜 _
  let e : (distributionModelFiber D p × T) ≃L[𝕜] E :=
    (Submodule.prodEquivOfIsCompl (distributionModelFiber D p) T hT).toContinuousLinearEquiv
  let Dt : (q : distributionModelFiber D p × T) →
      Submodule 𝕜 (TangentSpace 𝓘(𝕜, distributionModelFiber D p × T) q) := fun q ↦
    (D (e.toDiffeomorph q)).comap
      (mfderiv 𝓘(𝕜, distributionModelFiber D p × T) 𝓘(𝕜, E)
        e.toDiffeomorph q).toLinearMap
  let D' : distributionModelFiber D p × T →
      Submodule 𝕜 (distributionModelFiber D p × T) := fun q ↦
    distributionModelFiber Dt q
  have hD'eq : D' = Dt := by
    funext q
    exact distributionModelFiber_eq q
  have hsmooth : IsContMDiffDistribution 𝓘(𝕜, distributionModelFiber D p × T) ∞ k D' := by
    rw [hD'eq]
    exact hD.comap_mfderiv e.toDiffeomorph (by simp)
  have hinv' : IsInvolutiveDistribution 𝓘(𝕜, distributionModelFiber D p × T) D' := by
    rw [hD'eq]
    exact (e.toDiffeomorph.isInvolutiveDistribution_comap_mfderiv_iff (by simp) D).2 hinv
  have hfinrank : Module.finrank 𝕜 (distributionModelFiber D p) = k := by
    rw [distributionModelFiber, LinearEquiv.finrank_map_eq, hD.finrank_eq p]
  refine ⟨hfinrank, hsmooth, hinv', ?_⟩
  ext q
  rw [mem_distributionModelFiber]
  simp only [Submodule.mem_comap, Submodule.mem_prod, Submodule.mem_top, true_and,
    Submodule.mem_bot]
  have heq :
      mfderiv 𝓘(𝕜, distributionModelFiber D p × T) 𝓘(𝕜, E)
        e.toDiffeomorph (e.symm p)
          ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (e.symm p)).symm q) =
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (e.toDiffeomorph (e.symm p))).symm
          (e q) := by
    rw [mfderiv_eq_fderiv, ContinuousLinearEquiv.coe_toDiffeomorph,
      e.hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    have hq := (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (e.symm p)).apply_symm_apply q
    exact congrArg
      (fun x ↦ (NormedSpace.fromTangentSpace (𝕜 := 𝕜) (e (e.symm p))).symm (e x)) hq
  change mfderiv 𝓘(𝕜, distributionModelFiber D p × T) 𝓘(𝕜, E)
      e.toDiffeomorph (e.symm p)
        ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (e.symm p)).symm q) ∈
      D (e.toDiffeomorph (e.symm p)) ↔
      q.2 = 0
  rw [heq, ContinuousLinearEquiv.coe_toDiffeomorph, e.apply_symm_apply]
  have hmap (x : E) :
      (NormedSpace.fromTangentSpace (𝕜 := 𝕜) p).symm x ∈ D p ↔
        x ∈ distributionModelFiber D p := mem_distributionModelFiber.symm
  rw [hmap]
  simpa only [e, LinearEquiv.coe_toContinuousLinearEquiv',
    LinearEquiv.symm_apply_apply] using
    (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
      (distributionModelFiber D p) T hT (x := e q)).symm

end Splitting

end TauCeti
