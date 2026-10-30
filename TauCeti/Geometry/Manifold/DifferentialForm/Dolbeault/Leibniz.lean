/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.AlmostComplexType
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# Graded Leibniz rules for the Dolbeault operators

The operators `∂` and `∂bar` are graded derivations of the paired wedge of smooth forms on
an almost complex manifold. The pairing of coefficient spaces must be complex bilinear.
No integrability assumption is needed: taking the components of bidegrees `(1,0)` and
`(0,1)` in the Leibniz rule for `d` gives the two rules separately.

The sign is determined by the total degree of the first factor, not just its holomorphic
degree. These identities provide the differential compatibility needed for products in
Dolbeault cohomology once the relevant operator squares to zero.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Sections 1.3 and 2.6.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]
  {k l p q r s : ℕ} {J : SmoothAlmostComplexStructure I M}
  {μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃}
  (hμ₁ : ∀ (c : ℂ) a b, μ (c • a) b = c • μ a b)
  (hμ₂ : ∀ (c : ℂ) a b, μ a (c • b) = c • μ a b)

include hμ₁ hμ₂

namespace SmoothForm

/-- Projecting the exterior Leibniz rule onto any bidegree shift of total degree one. -/
private theorem IsOfType.typeProjection_mextDerivₗ_wedgeWith
    {φ : SmoothForm I M F₁ k} {ψ : SmoothForm I M F₂ l}
    (hφ : φ.IsOfType J p q) (hψ : ψ.IsOfType J r s) (a b : ℕ) (hab : a + b = 1) :
    J.typeProjection (p + r + a) (q + s + b)
        (mextDerivₗ I (k + l) (SmoothForm.wedgeWith μ φ ψ)) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega)
        (SmoothForm.wedgeWith μ (J.typeProjection (p + a) (q + b) (mextDerivₗ I k φ)) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega)
        (SmoothForm.wedgeWith μ φ (J.typeProjection (r + a) (s + b) (mextDerivₗ I l ψ))) := by
  have hleft := hψ.typeProjection_wedgeWith_left hμ₁ hμ₂
    (p := p + a) (q := q + b) (by rw [← hφ.add_eq]; omega) (mextDerivₗ I k φ)
  have hright := hφ.typeProjection_wedgeWith_right hμ₁ hμ₂
    (p' := r + a) (q' := s + b) (by rw [← hψ.add_eq]; omega) (mextDerivₗ I l ψ)
  -- Move the shift past the right factor's type in hleft and reassociate hright,
  -- so both projections have the target indices (p + r + a, q + s + b).
  rw [Nat.add_right_comm p a r, Nat.add_right_comm q b s] at hleft
  simp only [← Nat.add_assoc] at hright
  rw [mextDerivₗ_wedgeWith]
  simp only [map_add, LinearMap.map_smul_of_tower, J.typeProjection_cast, hleft, hright]

/-- The graded Leibniz rule for `∂` on a paired wedge of forms of pure type. -/
private theorem IsOfType.del_wedgeWith {φ : SmoothForm I M F₁ k} {ψ : SmoothForm I M F₂ l}
    (hφ : φ.IsOfType J p q) (hψ : ψ.IsOfType J r s) :
    J.del (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (J.del φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (J.del ψ)) := by
  rw [(hφ.wedgeWith hμ₁ hμ₂ hψ).del_eq, hφ.del_eq, hψ.del_eq]
  simpa only [Nat.add_zero] using
    hφ.typeProjection_mextDerivₗ_wedgeWith hμ₁ hμ₂ hψ 1 0 rfl

/-- The graded Leibniz rule for `∂bar` on a paired wedge of forms of pure type. -/
private theorem IsOfType.delBar_wedgeWith {φ : SmoothForm I M F₁ k} {ψ : SmoothForm I M F₂ l}
    (hφ : φ.IsOfType J p q) (hψ : ψ.IsOfType J r s) :
    J.delBar (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (J.delBar φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (J.delBar ψ)) := by
  rw [(hφ.wedgeWith hμ₁ hμ₂ hψ).delBar_eq, hφ.delBar_eq, hψ.delBar_eq]
  simpa only [Nat.add_zero] using
    hφ.typeProjection_mextDerivₗ_wedgeWith hμ₁ hμ₂ hψ 0 1 rfl

omit hμ₁ hμ₂ in
/-- An additive Leibniz identity is determined by pairs of pure-type forms. -/
private theorem leibniz_of_isOfType
    (D₁ : SmoothForm I M F₁ k →ₗ[ℂ] SmoothForm I M F₁ (k + 1))
    (D₂ : SmoothForm I M F₂ l →ₗ[ℂ] SmoothForm I M F₂ (l + 1))
    (D₃ : SmoothForm I M F₃ (k + l) →ₗ[ℂ] SmoothForm I M F₃ (k + l + 1))
    (hD : ∀ {p q r s} {φ : SmoothForm I M F₁ k} {ψ : SmoothForm I M F₂ l},
      φ.IsOfType J p q → ψ.IsOfType J r s →
      D₃ (SmoothForm.wedgeWith μ φ ψ) =
        LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
          (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (D₁ φ) ψ) +
        (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
          (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (D₂ ψ)))
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    D₃ (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (D₁ φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (D₂ ψ)) := by
  rw [← J.sum_typeProjection φ, ← J.sum_typeProjection ψ]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  exact hD (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hb) φ)
    (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 ha) ψ)

end SmoothForm

namespace SmoothAlmostComplexStructure

variable (J)

/-- On any almost complex manifold, `∂` is a graded derivation of paired wedges with a
complex-bilinear coefficient pairing. -/
theorem del_wedgeWith (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    J.del (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (J.del φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (J.del ψ)) := by
  exact SmoothForm.leibniz_of_isOfType J.del J.del J.del
    (fun hφ hψ ↦ hφ.del_wedgeWith hμ₁ hμ₂ hψ) φ ψ

/-- On any almost complex manifold, `∂bar` is a graded derivation of paired wedges with a
complex-bilinear coefficient pairing. -/
theorem delBar_wedgeWith (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    J.delBar (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (J.delBar φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (J.delBar ψ)) := by
  exact SmoothForm.leibniz_of_isOfType J.delBar J.delBar J.delBar
    (fun hφ hψ ↦ hφ.delBar_wedgeWith hμ₁ hμ₂ hψ) φ ψ

end SmoothAlmostComplexStructure

end TauCeti
