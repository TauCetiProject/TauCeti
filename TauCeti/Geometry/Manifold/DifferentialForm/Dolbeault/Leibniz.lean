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

/-- The graded Leibniz rule for `∂` on a paired wedge of forms of pure type. -/
private theorem IsOfType.del_wedgeWith {φ : SmoothForm I M F₁ k} {ψ : SmoothForm I M F₂ l}
    (hφ : φ.IsOfType J p q) (hψ : ψ.IsOfType J r s) :
    J.del (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (J.del φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (J.del ψ)) := by
  have hleft := hψ.typeProjection_wedgeWith_left hμ₁ hμ₂
    (p := p + 1) (q := q) (by rw [← hφ.add_eq]; omega) (mextDerivₗ I k φ)
  have hright := hφ.typeProjection_wedgeWith_right hμ₁ hμ₂
    (p' := r + 1) (q' := s) (by rw [← hψ.add_eq]; omega) (mextDerivₗ I l ψ)
  rw [(hφ.wedgeWith hμ₁ hμ₂ hψ).del_eq, mextDerivₗ_wedgeWith]
  simp only [map_add, LinearMap.map_smul_of_tower, J.typeProjection_cast, hφ.del_eq, hψ.del_eq]
  simp only [Nat.add_assoc, Nat.add_comm 1] at hleft hright ⊢
  rw [hleft, hright]

/-- The graded Leibniz rule for `∂bar` on a paired wedge of forms of pure type. -/
private theorem IsOfType.delBar_wedgeWith {φ : SmoothForm I M F₁ k} {ψ : SmoothForm I M F₂ l}
    (hφ : φ.IsOfType J p q) (hψ : ψ.IsOfType J r s) :
    J.delBar (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (J.delBar φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (J.delBar ψ)) := by
  have hleft := hψ.typeProjection_wedgeWith_left hμ₁ hμ₂
    (p := p) (q := q + 1) (by rw [← hφ.add_eq]; omega) (mextDerivₗ I k φ)
  have hright := hφ.typeProjection_wedgeWith_right hμ₁ hμ₂
    (p' := r) (q' := s + 1) (by rw [← hψ.add_eq]; omega) (mextDerivₗ I l ψ)
  rw [(hφ.wedgeWith hμ₁ hμ₂ hψ).delBar_eq, mextDerivₗ_wedgeWith]
  simp only [map_add, LinearMap.map_smul_of_tower, J.typeProjection_cast,
    hφ.delBar_eq, hψ.delBar_eq]
  simp only [Nat.add_assoc, Nat.add_comm 1] at hleft hright ⊢
  rw [hleft, hright]

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
  rw [← J.sum_typeProjection φ, ← J.sum_typeProjection ψ]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  exact (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hb) φ).del_wedgeWith hμ₁ hμ₂
    (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 ha) ψ)

/-- On any almost complex manifold, `∂bar` is a graded derivation of paired wedges with a
complex-bilinear coefficient pairing. -/
theorem delBar_wedgeWith (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    J.delBar (SmoothForm.wedgeWith μ φ ψ) =
      LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + 1 + l = k + l + 1 by omega) (SmoothForm.wedgeWith μ (J.delBar φ) ψ) +
      (-1 : ℝ) ^ k • LinearEquiv.cast (R := ℝ) (M := fun n ↦ SmoothForm I M F₃ n)
        (show k + (l + 1) = k + l + 1 by omega) (SmoothForm.wedgeWith μ φ (J.delBar ψ)) := by
  rw [← J.sum_typeProjection φ, ← J.sum_typeProjection ψ]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  exact (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hb) φ).delBar_wedgeWith hμ₁ hμ₂
    (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 ha) ψ)

end SmoothAlmostComplexStructure

end TauCeti
