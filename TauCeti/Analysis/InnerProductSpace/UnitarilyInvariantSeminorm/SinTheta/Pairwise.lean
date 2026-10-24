/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Sylvester.Pairwise

/-!
# Pairwise Davis--Kahan sine theorem

For symmetric operators `A` and `B`, let `U` be invariant under `A` and `V`
invariant under `B`. If the spectra of `A` on `U` and `B` on `Vᗮ` are pairwise
separated by `delta`, then every unitarily invariant seminorm satisfies

`delta * N (P_(Vᗮ) P_U) <= (pi / 2) * N (B - A)`.

No interval ordering of the two spectral blocks is required. The proof
compresses the Sylvester equation to `U -> Vᗮ`, applies the existing pairwise
Sylvester bound, and zero-extends the resulting operator to compare its norm
with the ambient perturbation. The zero extension is private to this proof.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1--46.
* R. Bhatia, *Matrix Analysis*, Chapter VII.
* Adapted from the maintained Kitware DKPS formalization (Apache-2.0),
  `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`.
-/

public section

namespace TauCeti.UnitarilyInvariantSeminorm

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A spectral point of a restricted endomorphism also belongs to the
restricted point spectrum of the original endomorphism on its invariant block. -/
private theorem restrict_pointSpectrum_subset (A : E →ₗ[𝕜] E)
    {U : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U) :
    Module.End.restrictedPointSpectrum (A.restrict hU) ⊤ ⊆
      Module.End.restrictedPointSpectrum A U := by
  intro μ hμ
  obtain ⟨x, _, hx0, hx⟩ := Module.End.mem_restrictedPointSpectrum_iff.mp hμ
  have hx0' : (x : E) ≠ 0 := by
    intro hx'
    apply hx0
    apply Subtype.ext
    exact hx'
  exact Module.End.mem_restrictedPointSpectrum x.property hx0'
    (congrArg Subtype.val hx)

variable [FiniteDimensional 𝕜 E]

/-- The adjoint of a subspace's isometric inclusion is its orthogonal projection. -/
private theorem adjoint_subtype_is_projection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] :
    LinearMap.adjoint U.subtypeₗᵢ.toLinearMap =
      U.orthogonalProjectionOnto.toLinearMap := by
  rw [eq_comm]
  apply (LinearMap.eq_adjoint_iff
    U.orthogonalProjectionOnto.toLinearMap U.subtype).2
  intro x y
  change ⟪U.starProjection x, (y : E)⟫_𝕜 = ⟪x, (y : E)⟫_𝕜
  rw [U.inner_starProjection_left_eq_right, U.starProjection_eq_self_iff.mpr y.2]

/-- **The pairwise `pi/2` Davis--Kahan sine theorem.** If the spectra of
`A` on `U` and `B` on `Vᗮ` are at distance at least `delta`, then the
perturbation controls the directed sine in every unitarily invariant seminorm.
The conclusion also holds at zero or negative `delta`. -/
theorem mul_map_starProjection_comp_starProjection_le_pi_div_two_mul_map_sub
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    {U V : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (hV : ∀ x ∈ V, B x ∈ V) {δ : ℝ}
    (hgap : Module.End.PointSpectraSeparated (A : E →ₗ[𝕜] E) U
      (B : E →ₗ[𝕜] E) Vᗮ δ) :
    δ * N (Vᗮ.starProjection ∘L U.starProjection) ≤
      (Real.pi / 2) * N (B - A) := by
  let _ : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let W : Submodule 𝕜 E := Vᗮ
  have hW : ∀ x ∈ W, B x ∈ W := by
    intro x hx
    exact hB.orthogonalComplement_mem_invtSubmodule (p := V) hV hx
  let AU : U →L[𝕜] U := ((A : E →ₗ[𝕜] E).restrict hU).toContinuousLinearMap
  let BW : W →L[𝕜] W := ((B : E →ₗ[𝕜] E).restrict hW).toContinuousLinearMap
  let Y : U →L[𝕜] W := W.orthogonalProjectionOnto ∘L U.subtypeL
  let C : U →L[𝕜] W := W.orthogonalProjectionOnto ∘L (B - A) ∘L U.subtypeL
  have hAU : (AU : U →ₗ[𝕜] U).IsSymmetric := by
    change ((A : E →ₗ[𝕜] E).restrict hU).IsSymmetric
    exact hA.restrict_invariant hU
  have hBW : (BW : W →ₗ[𝕜] W).IsSymmetric := by
    change ((B : E →ₗ[𝕜] E).restrict hW).IsSymmetric
    exact hB.restrict_invariant hW
  have hgap' : Module.End.PointSpectraSeparated (BW : W →ₗ[𝕜] W) ⊤
      (AU : U →ₗ[𝕜] U) ⊤ δ := by
    refine Module.End.pointSpectraSeparated_iff.mpr ?_
    intro μ hμ ν hν
    have hμW : μ ∈ Module.End.restrictedPointSpectrum (B : E →ₗ[𝕜] E) W :=
      restrict_pointSpectrum_subset (B : E →ₗ[𝕜] E) hW hμ
    have hνU : ν ∈ Module.End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) U :=
      restrict_pointSpectrum_subset (A : E →ₗ[𝕜] E) hU hν
    exact (Module.End.PointSpectraSeparated.symm hgap).le_abs_sub hμW hνU
  have hcommW : ∀ x, W.starProjection (B x) = B (W.starProjection x) :=
    hB.starProjection_apply_comm hW
  have hSY : BW.sylvester AU Y = C := by
    ext x
    simp only [ContinuousLinearMap.sylvester_apply, sub_apply, ContinuousLinearMap.comp_apply]
    change B (W.starProjection (x : E)) - W.starProjection (A (x : E)) =
      W.starProjection ((B - A) (x : E))
    rw [← hcommW, sub_apply, map_sub]
  let extend : (U →ₗ[𝕜] W) →ₗ[𝕜] (E →ₗ[𝕜] E) :=
    { toFun := fun T => W.subtype ∘ₗ T ∘ₗ U.orthogonalProjectionOnto.toLinearMap
      map_add' := by
        intro T S
        ext x
        simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
      map_smul' := by
        intro c T
        ext x
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply] }
  have hsing (T : U →ₗ[𝕜] W) : (extend T).singularValues = T.singularValues := by
    change (W.subtype ∘ₗ T ∘ₗ U.orthogonalProjectionOnto.toLinearMap).singularValues =
      T.singularValues
    rw [← adjoint_subtype_is_projection U]
    change (W.subtypeₗᵢ.toLinearMap ∘ₗ T ∘ₗ
      LinearMap.adjoint U.subtypeₗᵢ.toLinearMap).singularValues = T.singularValues
    simp only [LinearMap.singularValues_linearIsometry_comp,
      LinearMap.singularValues_comp_adjoint_linearIsometry]
  let Nblock : UnitarilyInvariantSeminorm 𝕜 U W :=
    { toSeminorm := N.toSeminorm.comp extend
      map_linearIsometryEquiv_comp_comp' := by
        intro L R T
        change N (extend ((L : W →ₗ[𝕜] W) ∘ₗ T ∘ₗ (R : U →ₗ[𝕜] U))) =
          N (extend T)
        apply N.map_eq_of_singularValues_eq
        calc
          (extend ((L : W →ₗ[𝕜] W) ∘ₗ T ∘ₗ (R : U →ₗ[𝕜] U))).singularValues =
              ((L : W →ₗ[𝕜] W) ∘ₗ T ∘ₗ (R : U →ₗ[𝕜] U)).singularValues := hsing _
          _ = T.singularValues := by simp
          _ = (extend T).singularValues := (hsing T).symm }
  have hC : Nblock C ≤ N (B - A) := by
    change N (extend (C : U →ₗ[𝕜] W)) ≤ N (B - A)
    have hcomp : extend (C : U →ₗ[𝕜] W) =
        (((W.starProjection ∘L (B - A)) ∘L U.starProjection : E →L[𝕜] E) :
          E →ₗ[𝕜] E) := by
      ext x
      rfl
    rw [hcomp]
    exact (N.map_starProjection_comp_le W ((B - A) ∘L U.starProjection)).trans
      (N.map_comp_starProjection_le U (B - A))
  have hY : Nblock Y = N (W.starProjection ∘L U.starProjection) := by
    change N (extend (Y : U →ₗ[𝕜] W)) = N (W.starProjection ∘L U.starProjection)
    congr 1
  have hSylv : δ * Nblock Y ≤ (Real.pi / 2) * Nblock C := by
    have h := Nblock.mul_map_le_pi_div_two_mul_map_sylvester_apply hBW hAU hgap' Y
    rwa [hSY] at h
  calc
    δ * N (Vᗮ.starProjection ∘L U.starProjection) = δ * Nblock Y := by
      change δ * N (W.starProjection ∘L U.starProjection) = δ * Nblock Y
      rw [hY]
    _ ≤ (Real.pi / 2) * Nblock C := hSylv
    _ ≤ (Real.pi / 2) * N (B - A) :=
      mul_le_mul_of_nonneg_left hC (by positivity)

end TauCeti.UnitarilyInvariantSeminorm
