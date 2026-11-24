/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricBaseChange
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.SchemePoints
public import TauCeti.Topology.Algebra.PointTopology.Scheme.ClosedImmersion
public import TauCeti.Topology.Algebra.PointTopology.Scheme.FiberProduct

/-!
# Complex points of projective schemes

Let `A` be a `ℂ`-algebra and `X` a scheme projective over `A`, in the sense of
`AlgebraicGeometry.Scheme.IsProjectiveOver`: a closed subscheme over `A` of `Proj (Sym_A M)` for a
finite `A`-module `M`. Give the complex points of `X` and of `Spec A`, the morphisms from
`Spec ℂ` over `Spec ℂ`, the chart topology `TauCeti.SchemePointTopology.topology`. Then the
structure morphism `X ⟶ Spec A` induces a proper map `X(ℂ) → (Spec A)(ℂ)`, in the sense of
Mathlib's `IsProperMap`. Over `A = ℂ` this says that the complex points of a projective
`ℂ`-scheme form a compact space.

The proof factors the structure morphism through closed immersions
`X ⟶ Proj (Sym_A M) ⟶ ℙⁿ_A`, where `ℙⁿ_A = Proj (Sym_A (A ⊗[ℂ] ℂ^{n+1}))` is induced by a
surjection `A ⊗[ℂ] ℂ^{n+1} → M`. Closed immersions induce closed embeddings of complex points
(`TauCeti.SchemePointTopology.isClosedEmbedding_of_isClosedImmersion`), and these are proper
maps. The projective space `ℙⁿ_A` is the base change of `ℙⁿ_ℂ` along `Spec A ⟶ Spec ℂ`
(`AlgebraicGeometry.Proj.isPullback_symmetricAlgebra_baseChange`), so its complex points are the
product of those of `ℙⁿ_ℂ` and of `Spec A`
(`TauCeti.SchemePointTopology.pointsProdHomeomorphOfIsPullback`). The projection from this
product is proper because `ℙⁿ(ℂ)` is compact (`TauCeti.Toric.compactSpace_points_projToSpec`).

## Main results

* `TauCeti.SchemePointTopology.isProperMap_map_projToSpec`: for a finite `A`-module `M`, the
  projection `Proj (Sym_A M)(ℂ) → (Spec A)(ℂ)` is proper.
* `TauCeti.SchemePointTopology.isProperMap_map_of_isProjectiveOver`: a projective scheme over a
  `ℂ`-algebra `A` has a proper map of complex points to `Spec A`.
* `TauCeti.SchemePointTopology.compactSpace_of_isProjectiveOver`: the complex points of a
  projective `ℂ`-scheme are compact.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII, Propositions
  3.1(viii) and 3.2(v).
* J.-P. Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.SymmetricAlgebra
open scoped TensorProduct

namespace TauCeti.SchemePointTopology

attribute [local instance] topology

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The projection from `ℙⁿ_A = Proj (Sym_A (A ⊗[ℂ] ℂ^{n+1}))` is proper on complex points: these
points are the product of those of `ℙⁿ_ℂ`, which are compact, and those of `Spec A`. -/
private theorem isProperMap_map_projToSpec_tensorProduct (n : ℕ) :
    IsProperMap (map (R := ℂ) (projToSpec A (A ⊗[ℂ] (Option (Fin n) → ℂ)))
      (fX := projToSpec A (A ⊗[ℂ] (Option (Fin n) → ℂ)) ≫ Spec.algebraMap ℂ A) rfl) := by
  have hP := Proj.isPullback_symmetricAlgebra_baseChange ℂ A (Option (Fin n) → ℂ)
  let e := pointsProdHomeomorphOfIsPullback (R := ℂ) hP hP.w
  have he : map (R := ℂ) (projToSpec A (A ⊗[ℂ] (Option (Fin n) → ℂ)))
      (fX := projToSpec A (A ⊗[ℂ] (Option (Fin n) → ℂ)) ≫ Spec.algebraMap ℂ A) rfl =
        Prod.snd ∘ e := by
    funext x
    simp [e]
  rw [he]
  exact isProperMap_snd_of_compactSpace.comp e.isProperMap

/-- **Projective space over a `ℂ`-algebra is proper on complex points.** For a finite module `M`
over a `ℂ`-algebra `A`, the structure morphism of `Proj (Sym_A M)` induces a proper map of
complex points `Proj (Sym_A M)(ℂ) → (Spec A)(ℂ)`. -/
theorem isProperMap_map_projToSpec (M : Type) [AddCommMonoid M] [Module A M]
    [Module.Finite A M] :
    IsProperMap (map (R := ℂ) (projToSpec A M)
      (fX := projToSpec A M ≫ Spec.algebraMap ℂ A) rfl) := by
  -- A surjection `A ⊗[ℂ] ℂ^{n+1} → M` embeds `Proj (Sym_A M)` as a closed subscheme of `ℙⁿ_A`.
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' A M
  let ψ : A ⊗[ℂ] (Option (Fin n) → ℂ) →ₗ[A] M := φ ∘ₗ LinearMap.funLeft A A Option.some ∘ₗ
    (TensorProduct.piScalarRight ℂ A A (Option (Fin n))).toLinearMap
  have hψ : Function.Surjective ψ := hφ.comp <|
    (LinearMap.funLeft_surjective_of_injective A A _ (Option.some_injective _)).comp
      (TensorProduct.piScalarRight ℂ A A (Option (Fin n))).surjective
  have hsurj : Function.Surjective (SymmetricAlgebra.gradedMap A ψ) := by
    simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
      SymmetricAlgebra.map_surjective A ψ hψ
  let q := Proj.map (SymmetricAlgebra.gradedMap A ψ)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ hsurj)
  have : IsClosedImmersion q := Proj.isClosedImmersion_map _ _ hsurj
  have hqP : q ≫ projToSpec A (A ⊗[ℂ] (Option (Fin n) → ℂ)) = projToSpec A M :=
    Proj.map_gradedMap_projToSpec A ψ _
  have hq : q ≫ projToSpec A (A ⊗[ℂ] (Option (Fin n) → ℂ)) ≫ Spec.algebraMap ℂ A =
      projToSpec A M ≫ Spec.algebraMap ℂ A := by
    rw [← Category.assoc, hqP]
  have hcomp : map (R := ℂ) (projToSpec A M) (fX := projToSpec A M ≫ Spec.algebraMap ℂ A) rfl =
      map (R := ℂ) (projToSpec A (A ⊗[ℂ] (Option (Fin n) → ℂ))) rfl ∘ map q hq := by
    funext x
    rw [Function.comp_apply, map_map]
    congr 1
    rw [hqP]
  rw [hcomp]
  exact (isProperMap_map_projToSpec_tensorProduct n).comp
    (isClosedEmbedding_of_isClosedImmersion q hq).isProperMap

/-- **Projective schemes are proper on complex points.** If `X` is projective over a
`ℂ`-algebra `A`, its structure morphism induces a proper map of complex points
`X(ℂ) → (Spec A)(ℂ)`. -/
theorem isProperMap_map_of_isProjectiveOver {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [X.IsProjectiveOver A] :
    IsProperMap (map (R := ℂ) (X ↘ Spec (.of A))
      (fX := (X ↘ Spec (.of A)) ≫ Spec.algebraMap ℂ A) rfl) := by
  obtain ⟨M, _, _, _, j, hj, hjA⟩ := Scheme.IsProjectiveOver.exists_isClosedImmersion (R := A)
    (X := X)
  have hjq : j ≫ projToSpec A M = X ↘ Spec (.of A) := by
    rw [← over_eq_projToSpec, comp_over]
  have hj' : j ≫ projToSpec A M ≫ Spec.algebraMap ℂ A = (X ↘ Spec (.of A)) ≫
      Spec.algebraMap ℂ A := by
    rw [← Category.assoc, hjq]
  have hcomp : map (R := ℂ) (X ↘ Spec (.of A)) (fX := (X ↘ Spec (.of A)) ≫ Spec.algebraMap ℂ A)
      rfl = map (R := ℂ) (projToSpec A M) rfl ∘ map j hj' := by
    funext x
    rw [Function.comp_apply, map_map]
    congr 1
    rw [hjq]
  rw [hcomp]
  exact (isProperMap_map_projToSpec M).comp
    (isClosedEmbedding_of_isClosedImmersion j hj').isProperMap

/-- **The complex points of a projective `ℂ`-scheme are compact.** -/
instance compactSpace_of_isProjectiveOver {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [X.IsProjectiveOver ℂ] : CompactSpace (Points (R := ℂ) (X ↘ Spec (.of ℂ))) := by
  have hid : Spec.algebraMap ℂ ℂ = 𝟙 _ := by simp
  have : IsIso (Spec.algebraMap ℂ ℂ) := by rw [hid]; infer_instance
  -- The complex points of `Spec ℂ` form a single point, so properness over it is compactness.
  have hc := (isProperMap_map_of_isProjectiveOver (A := ℂ) (X := X)).isCompact_preimage
    isCompact_univ
  have h : CompactSpace (Points (R := ℂ) ((X ↘ Spec (.of ℂ)) ≫ Spec.algebraMap ℂ ℂ)) :=
    ⟨by simpa using hc⟩
  rwa [hid, Category.comp_id] at h

end TauCeti.SchemePointTopology
