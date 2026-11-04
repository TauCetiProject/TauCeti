/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.AlmostComplexType

/-!
# The `(p,q)` type of wedge products of smooth forms on an almost complex manifold

Let `J` be a smooth almost complex structure on a manifold `M`. This file shows that the type
decomposition of complex-valued smooth forms is compatible with the paired wedge
`TauCeti.SmoothForm.wedgeWith μ` for every complex-bilinear pairing `μ` of the coefficients, by
applying the fibrewise statements of
`TauCeti.Topology.Algebra.Module.Alternating.Wedge.AlmostComplexType` in every tangent space.

The derivation of smooth forms along a smooth endomorphism field `A` of the tangent bundle is a
derivation of the paired wedge, for every continuous real-bilinear pairing. For `A = J` and a
complex-bilinear pairing, it follows that the wedge of smooth forms of types `(p,q)` and
`(p',q')` has type `(p + p', q + q')`, and that the type-`(P,Q)` component of a wedge is the sum
of the wedges of the type components of the factors whose types add up to `(P,Q)`.

## Main declarations

* `ContMDiffSection.alternatingDerivation_wedgeWith`: the Leibniz rule for the derivation along a
  smooth endomorphism field.
* `TauCeti.SmoothForm.IsOfType.wedgeWith`: types add under the wedge of smooth forms.
* `TauCeti.SmoothAlmostComplexStructure.typeProjection_wedgeWith`: the type components of a
  wedge of smooth forms.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Sections 1.2 and 2.6.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

variable {E H M F₁ F₂ F₃ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] {k l : ℕ} (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)

namespace ContMDiffSection

open TauCeti

variable [IsManifold I 1 M]

/-- The derivation of smooth forms along a smooth endomorphism field `A` of the tangent bundle is
a derivation of the paired wedge: `D_A (φ ∧ ψ) = D_A φ ∧ ψ + φ ∧ D_A ψ`. -/
theorem alternatingDerivation_wedgeWith
    (A : ContMDiffSection I (E →L[ℝ] E) ∞ fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    A.alternatingDerivation (SmoothForm.wedgeWith μ φ ψ) =
      SmoothForm.wedgeWith μ (A.alternatingDerivation φ) ψ +
        SmoothForm.wedgeWith μ φ (A.alternatingDerivation ψ) :=
  Subtype.ext <| funext fun x ↦ by
    simp only [coe_alternatingDerivation, Submodule.coe_add, Pi.add_apply,
      SmoothForm.coe_wedgeWith, RoughForm.wedgeWith_apply']
    exact (A x).alternatingDerivation_pairedWedge μ μ.continuous₂ (φ.1 x) (ψ.1 x)

end ContMDiffSection

namespace TauCeti

variable [IsManifold I ∞ M] {μ} {J : SmoothAlmostComplexStructure I M}

namespace SmoothForm

variable {φ : SmoothForm I M F₁ k} {ψ : SmoothForm I M F₂ l} {p q p' q' : ℕ}

/-- For a complex-bilinear pairing, the wedge of smooth forms of types `(p,q)` and `(p',q')` has
type `(p + p', q + q')`. -/
theorem IsOfType.wedgeWith (hμ₁ : ∀ (c : ℂ) a b, μ (c • a) b = c • μ a b)
    (hμ₂ : ∀ (c : ℂ) a b, μ a (c • b) = c • μ a b) (hφ : φ.IsOfType J p q)
    (hψ : ψ.IsOfType J p' q') : (wedgeWith μ φ ψ).IsOfType J (p + p') (q + q') :=
  isOfType_iff_forall.2 ⟨by rw [← hφ.add_eq, ← hψ.add_eq]; ring, fun x ↦ by
    simp only [coe_wedgeWith, RoughForm.wedgeWith_apply']
    exact (hφ.apply x).pairedWedge hμ₁ hμ₂ (hψ.apply x)⟩

/-- If the right factor has pure type, projecting the wedge shifts the type projection of
its left factor by that type. -/
theorem IsOfType.typeProjection_wedgeWith_left
    (hψ : ψ.IsOfType J p' q')
    (hμ₁ : ∀ (c : ℂ) a b, μ (c • a) b = c • μ a b)
    (hμ₂ : ∀ (c : ℂ) a b, μ a (c • b) = c • μ a b)
    (hpq : p + q = k) (φ : SmoothForm I M F₁ k) :
    J.typeProjection (p + p') (q + q') (SmoothForm.wedgeWith μ φ ψ) =
      SmoothForm.wedgeWith μ (J.typeProjection p q φ) ψ := by
  conv_lhs => rw [← J.sum_typeProjection φ]
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_eq_single (p, q)]
  · exact ((J.isOfType_typeProjection hpq φ).wedgeWith hμ₁ hμ₂ hψ).typeProjection_self
  · intro pq hpq' hne
    exact ((J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hpq') φ).wedgeWith
      hμ₁ hμ₂ hψ).typeProjection_of_ne (by
        intro h
        obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
        exact hne (Prod.ext (by omega) (by omega)))
  · exact fun h ↦ absurd (Finset.mem_antidiagonal.2 hpq) h

/-- If the left factor has pure type, projecting the wedge shifts the type projection of
its right factor by that type. -/
theorem IsOfType.typeProjection_wedgeWith_right
    (hφ : φ.IsOfType J p q)
    (hμ₁ : ∀ (c : ℂ) a b, μ (c • a) b = c • μ a b)
    (hμ₂ : ∀ (c : ℂ) a b, μ a (c • b) = c • μ a b)
    (hpq : p' + q' = l) (ψ : SmoothForm I M F₂ l) :
    J.typeProjection (p + p') (q + q') (SmoothForm.wedgeWith μ φ ψ) =
      SmoothForm.wedgeWith μ φ (J.typeProjection p' q' ψ) := by
  conv_lhs => rw [← J.sum_typeProjection ψ]
  simp only [map_sum]
  rw [Finset.sum_eq_single (p', q')]
  · exact (hφ.wedgeWith hμ₁ hμ₂ (J.isOfType_typeProjection hpq ψ)).typeProjection_self
  · intro pq hpq' hne
    exact (hφ.wedgeWith hμ₁ hμ₂
      (J.isOfType_typeProjection (Finset.mem_antidiagonal.1 hpq') ψ)).typeProjection_of_ne (by
        intro h
        obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
        exact hne (Prod.ext (by omega) (by omega)))
  · exact fun h ↦ absurd (Finset.mem_antidiagonal.2 hpq) h

end SmoothForm

namespace SmoothAlmostComplexStructure

variable (J)

/-- For a complex-bilinear pairing, the type-`(P,Q)` component of the wedge of smooth forms is
the sum of the wedges of the type-`(p,q)` component of the first factor with the type-`(p',q')`
component of the second, over the types with `(p + p', q + q') = (P,Q)`. -/
theorem typeProjection_wedgeWith (hμ₁ : ∀ (c : ℂ) a b, μ (c • a) b = c • μ a b)
    (hμ₂ : ∀ (c : ℂ) a b, μ a (c • b) = c • μ a b) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) (P Q : ℕ) :
    J.typeProjection P Q (SmoothForm.wedgeWith μ φ ψ) =
      ∑ x ∈ Finset.antidiagonal k ×ˢ Finset.antidiagonal l with x.1 + x.2 = (P, Q),
        SmoothForm.wedgeWith μ (J.typeProjection x.1.1 x.1.2 φ) (J.typeProjection x.2.1 x.2.2 ψ) :=
  Subtype.ext <| funext fun x ↦ by
    simp only [coe_typeProjection, Submodule.coe_sum, Finset.sum_apply, SmoothForm.coe_wedgeWith,
      RoughForm.wedgeWith_apply']
    exact ContinuousLinearMap.typeProjection_pairedWedge (J.apply_apply x) hμ₁ hμ₂ _ _ P Q

end SmoothAlmostComplexStructure

end TauCeti
