/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere.Isotopy
import TauCeti.Geometry.Diffeomorphism.Composition
import TauCeti.Geometry.Diffeomorphism.Congr
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.AddCircle
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Path
import TauCeti.Geometry.Manifold.Instances.AddCircle.Circle
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The path components of the diffeomorphism group of the circle

Every `C^m` diffeomorphism of the circle `S¹ ⊆ ℝ²`, `m ≠ 0`, is joined in the weak Whitney
topology to the restriction of an orthogonal transformation of `ℝ²`, namely to the identity or to
the reflection `(x, y) ↦ (x, -y)`. So the map `π₀ O(2) → π₀ Diff(S¹)` induced by the reference
inclusion `TauCeti.orthogonalToDiffSphere` is surjective; it is injective by
`TauCeti.joined_orthogonalToDiffSphere_iff`, and `Diff(S¹)` has exactly two path components. This
is the one-dimensional case of the isotopy classification of sphere diffeomorphisms whose
three-dimensional case is Cerf's theorem `TauCeti.CerfTheorem`, and the statement on path
components of the homotopy equivalence `O(2) ≃ Diff(S¹)`, which is not proved here.

The isotopy straightens a lift of the diffeomorphism to the identity lift. Read through the
parametrization `AddCircle.diffeomorphSphere` of `S¹` by `ℝ / ℤ`, `θ ↦ (cos 2πθ, sin 2πθ)`, a
diffeomorphism or its composite with the reflection `θ ↦ -θ` has a lift `F : ℝ → ℝ` with
`F (x + 1) = F x + 1` and `F' > 0`, and the convex combinations of `F` with the identity lift a
diffeotopy from the identity to it (`Diffeomorph.exists_diffeotopy_final_eq_or_final_eq_comp_neg`).
The reflection `θ ↦ -θ` of `ℝ / ℤ` is the reflection `(x, y) ↦ (x, -y)` of `S¹`.

## Main results

* `TauCeti.exists_joined_orthogonalToDiffSphere_circle`: every diffeomorphism of `S¹` is isotopic
  to an orthogonal transformation.
* `TauCeti.natCard_zerothHomotopy_diff_circle`: `Diff(S¹)` has two path components.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Section 2.1, for lifts of circle homeomorphisms and the two isotopy classes of homeomorphisms of
  the circle.
-/

public section

open Metric
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {m : ℕ∞ω}

/-- The parametrization `AddCircle.diffeomorphSphere` of `S¹` carries the reflection `θ ↦ -θ` of
`ℝ / ℤ` to the reflection `(x, y) ↦ (x, -y)`. -/
private lemma diffeomorphSphere_neg (θ : AddCircle (1 : ℝ)) :
    AddCircle.diffeomorphSphere 1 m (-θ) =
      orthogonalToDiffSphere 1 m (orthogonalDiagonalReflection ℝ 1)
        (AddCircle.diffeomorphSphere 1 m θ) := by
  ext i : 2
  simp only [orthogonalToDiffSphere_apply, LinearIsometryEquiv.unitSphereDiffHom_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, AddCircle.coe_diffeomorphSphere_apply,
    AddCircle.toCircle_neg]
  fin_cases i <;> simp [Complex.orthonormalBasisOneI_repr_apply, Matrix.mulVec_diagonal]

/-- **Diffeomorphisms of the circle are isotopic to orthogonal ones.** Every `C^m` diffeomorphism
of the circle `S¹ ⊆ ℝ²`, `m ≠ 0`, is joined in the weak Whitney topology to the restriction of an
orthogonal transformation of `ℝ²`. -/
theorem exists_joined_orthogonalToDiffSphere_circle (hm : m ≠ 0)
    (f : Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) m) :
    ∃ A : Matrix.orthogonalGroup (Fin 2) ℝ, Joined (orthogonalToDiffSphere 1 m A) f := by
  set ψ := AddCircle.diffeomorphSphere 1 m
  obtain ⟨Ψ, hΨ⟩ :=
    Diffeomorph.exists_diffeotopy_final_eq_or_final_eq_comp_neg (Diffeomorph.diffCongr ψ.symm f) hm
  -- Conjugating the diffeotopy back to `S¹` joins the identity to `ψ ∘ Ψ.final ∘ ψ⁻¹`.
  have hJ : Joined 1 (Diffeomorph.diffCongr ψ Ψ.final) := by
    simpa using Ψ.joined_one_final.map (Diffeomorph.continuous_diffCongr ψ)
  rcases hΨ with hΨ | hΨ
  · -- The diffeotopy ends at the conjugate of `f`, so `f` is joined to the identity.
    refine ⟨1, ?_⟩
    rw [map_one]
    convert hJ using 1
    refine Diffeomorph.ext fun x ↦ ?_
    rw [Diffeomorph.diffCongr_apply_apply, hΨ, Diffeomorph.diffCongr_apply_apply]
    simp only [Diffeomorph.symm_apply_apply, Diffeomorph.apply_symm_apply]
  · -- The diffeotopy ends at the conjugate of `f ∘ ρ`, for the reflection `ρ`, so `f ∘ ρ` is
    -- joined to the identity and `f` to `ρ⁻¹`.
    set ρ := orthogonalToDiffSphere 1 m (orthogonalDiagonalReflection ℝ 1)
    have hψ : ψ.symm.symm = ψ := Diffeomorph.toEquiv_injective <| by
      rw [Diffeomorph.symm_toEquiv, Diffeomorph.symm_toEquiv, Equiv.symm_symm]
    have hfρ : Diffeomorph.diffCongr ψ Ψ.final = f * ρ := by
      refine Diffeomorph.ext fun x ↦ ?_
      rw [Diffeomorph.diffCongr_apply_apply, hΨ, Function.comp_apply,
        Diffeomorph.diffCongr_apply_apply, hψ, diffeomorphSphere_neg,
        Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply, Diffeomorph.mul_apply]
    refine ⟨(orthogonalDiagonalReflection ℝ 1)⁻¹, ?_⟩
    rw [hfρ] at hJ
    rw [map_inv]
    simpa only [mul_inv_cancel_right, one_mul] using hJ.map (continuous_mul_const ρ⁻¹)

/-- **The diffeomorphism group of the circle has two path components**, for the weak Whitney
`C^m` topology, `m ≠ 0`: those of the identity and of a reflection. -/
theorem natCard_zerothHomotopy_diff_circle (hm : m ≠ 0) :
    Nat.card (ZerothHomotopy (Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) m)) = 2 :=
  forall_exists_joined_orthogonalToDiffSphere_iff_natCard_zerothHomotopy_eq_two.1
    (exists_joined_orthogonalToDiffSphere_circle hm)

end TauCeti
