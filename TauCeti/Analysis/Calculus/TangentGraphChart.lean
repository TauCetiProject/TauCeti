/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
-- Private: used only inside proofs.
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Calculus.TangentCone.Chart

/-!
# Graph coordinates over the tangent space

Let `F : E → V` be a `C^n` map, `1 ≤ n`, from an open subset `U` of a finite-dimensional real
normed space into a real inner product space, and let `u₀ ∈ U` be a point at which the
differential of `F` is injective. Its image `R` is the tangent space of `F` at `u₀`. The
orthogonal projection of `F` onto `R` is a local diffeomorphism near `u₀`, by the inverse
function theorem, so near `u₀` the map `F` is a graph over `R`: in the coordinate given by that
projection, `F = w + h(w)` with `h(w) ∈ Rᗮ`. This is the normal form of an immersion into an
inner product space used to perturb distance functions along immersed submanifolds.

## Main results

* `TauCeti.ContDiffOn.exists_openPartialHomeomorph_starProjection`: a chart `Φ` of `E` around
  `u₀`, `C^n` with invertible differential on its source and with `C^n` inverse, in which the
  orthogonal projection of `F` onto its tangent space at `u₀` is a fixed linear isomorphism.

## References

* V. Guillemin and A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 1, §3, for
  the local immersion theorem.
-/

public section

open Function

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {F : E → V} {U : Set E} {n : WithTop ℕ∞}

/-- **Graph coordinates.** Near a point `u₀` at which its differential is injective, a `C^n` map
`F` into an inner product space is a graph over its tangent space `R` at `u₀`: there is a chart
`Φ` of `E` around `u₀`, `C^n` with invertible differential on its source and with `C^n` inverse,
in which the orthogonal projection of `F` onto `R` is a fixed linear isomorphism `e₀ : E ≃ R`. -/
theorem ContDiffOn.exists_openPartialHomeomorph_starProjection (hF : ContDiffOn ℝ n F U)
    (hU : IsOpen U) (hn : 1 ≤ n) {u₀ : E} (hu₀ : u₀ ∈ U) (hinj : Injective (fderiv ℝ F u₀)) :
    ∃ (e₀ : E ≃L[ℝ] LinearMap.range (fderiv ℝ F u₀ : E →ₗ[ℝ] V))
      (Φ : OpenPartialHomeomorph E E), u₀ ∈ Φ.source ∧ Φ.source ⊆ U ∧
      (∀ u ∈ Φ.source,
        (e₀ (Φ u) : V) = (LinearMap.range (fderiv ℝ F u₀ : E →ₗ[ℝ] V)).starProjection (F u)) ∧
      (∀ u ∈ Φ.source, ContDiffAt ℝ n Φ u ∧ (fderiv ℝ Φ u).IsInvertible) ∧
      ∀ w ∈ Φ.target, ContDiffAt ℝ n Φ.symm w := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  -- The tangent space `R` at `u₀`, and the orthogonal projection `Pr` onto it.
  set R : Submodule ℝ V := LinearMap.range (fderiv ℝ F u₀ : E →ₗ[ℝ] V)
  set Pr : V →L[ℝ] R := R.orthogonalProjectionOnto
  -- At `u₀` the differential of `Pr ∘ F` is an isomorphism `e₀` onto `R`.
  have hPr : ∀ v, Pr (fderiv ℝ F u₀ v) = ⟨fderiv ℝ F u₀ v, LinearMap.mem_range_self _ v⟩ :=
    fun v ↦ R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨_, LinearMap.mem_range_self _ v⟩
  have hbij : Bijective (Pr ∘L fderiv ℝ F u₀) := by
    refine ⟨fun v w h ↦ hinj ?_, fun ⟨r, v, hv⟩ ↦ ⟨v, ?_⟩⟩
    · simpa [hPr] using h
    · simp only [ContinuousLinearMap.coe_comp, comp_apply, hPr]
      exact Subtype.ext hv
  let e₀ : E ≃L[ℝ] R :=
    (LinearEquiv.ofBijective (Pr ∘L fderiv ℝ F u₀ : E →ₗ[ℝ] R) hbij).toContinuousLinearEquiv
  -- The coordinate `σ = e₀⁻¹ ∘ Pr ∘ F` on `E`, whose differential at `u₀` is the identity.
  set σ : E → E := fun u ↦ e₀.symm (Pr (F u))
  have hσC : ContDiffOn ℝ n σ U := (e₀.symm.contDiff.comp Pr.contDiff).comp_contDiffOn hF
  have hσ₀ : ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) = fderiv ℝ σ u₀ := by
    have hFd := ((hF.differentiableOn hn0 u₀ hu₀).differentiableAt (hU.mem_nhds hu₀)).hasFDerivAt
    have hσd : HasFDerivAt σ ((e₀.symm : R →L[ℝ] E) ∘L Pr ∘L fderiv ℝ F u₀) u₀ :=
      e₀.symm.hasFDerivAt.comp u₀ (Pr.hasFDerivAt.comp u₀ hFd)
    rw [hσd.fderiv]
    ext v
    exact (e₀.symm_apply_apply v).symm
  -- The inverse function theorem makes `σ` a chart near `u₀` with source inside `U`; a chart
  -- that is differentiable with differentiable inverse has invertible differential.
  obtain ⟨Φ, hΦ, hu₀Φ, hΦU, hsymm⟩ := ContDiffOn.exists_openPartialHomeomorph hσC hU hu₀ hn hσ₀
  have hsymm' : ∀ w ∈ Φ.target, ContDiffAt ℝ n Φ.symm w := fun w hw ↦
    hsymm.contDiffAt (Φ.open_target.mem_nhds hw)
  have hΦC : ∀ u ∈ Φ.source, ContDiffAt ℝ n Φ u := fun u hu ↦
    hΦ ▸ hσC.contDiffAt (hU.mem_nhds (hΦU hu))
  refine ⟨e₀, Φ, hu₀Φ, hΦU, fun u _ ↦ ?_, fun u hu ↦ ⟨hΦC u hu, ?_⟩, hsymm'⟩
  · rw [hΦ, R.starProjection_apply]
    exact congrArg Subtype.val (e₀.apply_symm_apply _)
  · exact Φ.isInvertible_fderiv hu ((hΦC u hu).differentiableAt hn0)
      ((hsymm' _ (Φ.map_source hu)).differentiableAt hn0)

end TauCeti
