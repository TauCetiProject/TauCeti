/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Étale coordinates on smooth morphisms

A morphism `f : X ⟶ S` that is smooth of relative dimension `n` is, locally on `X`, étale over
the affine space `𝔸(Fin n; S)`: every point of `X` has an affine open neighbourhood `V` with an
étale morphism `V ⟶ 𝔸(Fin n; S)` over `S`. Without a fixed relative dimension, a smooth morphism is
étale over some affine space `𝔸(Fin n; S)` near each point, with `n` depending on the point.

This reduces local questions about smooth morphisms to affine space, for instance the computation
of the rank of the relative Frobenius of a smooth morphism.

## Main declarations

* `AlgebraicGeometry.SmoothOfRelativeDimension.exists_etale_affineSpace`: étale coordinates
  for a morphism smooth of relative dimension `n`.
* `AlgebraicGeometry.Smooth.exists_etale_affineSpace`: étale coordinates for a smooth morphism.

## References

* The Stacks Project, [Tag 054L](https://stacks.math.columbia.edu/tag/054L).

The ring-theoretic input is Mathlib's
`RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`: a standard smooth ring
map of relative dimension `n` factors through an étale map out of the polynomial ring in `n`
variables.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A chart of `f` on which the ring map factors étale through a polynomial ring gives étale
coordinates on the chart. -/
private theorem exists_etale_affineSpace_of_appLE {f} {U : S.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) {σ : Type u}
    (φ : MvPolynomial σ Γ(S, U) →+* Γ(X, V)) (hφC : φ.comp MvPolynomial.C = (f.appLE U V e).hom)
    (hφ : φ.Etale) :
    ∃ g : V.toScheme ⟶ 𝔸(σ; S), Etale g ∧ g ≫ 𝔸(σ; S) ↘ S = V.ι ≫ f := by
  refine ⟨hV.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ (AffineSpace.SpecIso _ _).inv ≫
    AffineSpace.map σ hU.fromSpec, ?_, ?_⟩
  · have : Etale (AffineSpace.map σ hU.fromSpec) :=
      MorphismProperty.of_isPullback (AffineSpace.isPullback_map hU.fromSpec).flip inferInstance
    have : Etale (Spec.map (CommRingCat.ofHom φ)) := by
      rwa [HasRingHomProperty.Spec_iff (P := @Etale)]
    infer_instance
  · simp only [Category.assoc, AffineSpace.map_over, AffineSpace.SpecIso_inv_over_assoc,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hφC, CommRingCat.ofHom_hom,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e, IsAffineOpen.isoSpec_hom_fromSpec_assoc]

/-- A chart of `f` on which the ring map factors étale through a polynomial ring in `n` variables
gives étale coordinates on the chart, valued in `𝔸(ULift (Fin n); S)` as for
`AffineSpace.smoothOfRelativeDimension_fin`. -/
private theorem exists_etale_affineSpace_ulift_of_appLE {f} {U : S.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) {n : ℕ}
    (φ : MvPolynomial (Fin n) Γ(S, U) →+* Γ(X, V))
    (hφC : φ.comp MvPolynomial.C = (f.appLE U V e).hom) (hφ : φ.Etale) :
    ∃ g : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); S), Etale g ∧
      g ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S = V.ι ≫ f := by
  let r := (MvPolynomial.renameEquiv Γ(S, U) (Equiv.ulift (α := Fin n))).toRingEquiv
  refine exists_etale_affineSpace_of_appLE hU hV e (φ.comp r.toRingHom) ?_
    (RingHom.Etale.respectsIso.2 φ r hφ)
  rw [← hφC]
  ext a
  simp [r]

/-- **Étale coordinates.** If `f : X ⟶ S` is smooth of relative dimension `n`, then every point
of `X` has an affine open neighbourhood `V` with an étale morphism `V ⟶ 𝔸(Fin n; S)` over `S`
(the variables are indexed by `ULift (Fin n)`, as in `AffineSpace.smoothOfRelativeDimension_fin`).
-/
theorem SmoothOfRelativeDimension.exists_etale_affineSpace (n : ℕ)
    [SmoothOfRelativeDimension n f] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∃ g : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); S), Etale g ∧
      g ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S = V.ι ≫ f := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  obtain ⟨φ, hφC, hφ⟩ := hf.exists_etale_mvPolynomial
  exact ⟨V, hV, hx, exists_etale_affineSpace_ulift_of_appLE hU hV e φ hφC hφ⟩

/-- **Étale coordinates.** If `f : X ⟶ S` is smooth, then every point of `X` has an affine open
neighbourhood `V` with an étale morphism `V ⟶ 𝔸(Fin n; S)` over `S`, for some `n` (the variables
are indexed by `ULift (Fin n)`, as in `AffineSpace.smoothOfRelativeDimension_fin`). -/
theorem Smooth.exists_etale_affineSpace [Smooth f] (x : X) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∃ n : ℕ,
      ∃ g : V.toScheme ⟶ 𝔸(ULift.{u} (Fin n); S), Etale g ∧
        g ≫ 𝔸(ULift.{u} (Fin n); S) ↘ S = V.ι ≫ f := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := (Smooth.iff_forall_exists_isStandardSmooth f).mp ‹_› x
  obtain ⟨n, φ, hφC, hφ⟩ := hf.exists_etale_mvPolynomial
  exact ⟨V, hV, hx, n, exists_etale_affineSpace_ulift_of_appLE hU hV e φ hφC hφ⟩

end AlgebraicGeometry
