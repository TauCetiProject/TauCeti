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
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Projective.Space

/-!
# Points of projective schemes over a topological field

Let `K` be a topological field and `A` a `K`-algebra, and let `X` be a scheme projective over `A`,
in the sense of `AlgebraicGeometry.Scheme.IsProjectiveOver`: a closed subscheme over `A` of
`Proj (Sym_A M)` for a finite `A`-module `M`. Give the `K`-points of `X` and of `Spec A`, the
morphisms from `Spec K` over `Spec K`, the chart topology `TauCeti.SchemePointTopology.topology`.
Suppose that the `K`-points of every projective space `ℙⁿ_K = Proj (Sym_K K^{n+1})` form a
compact space. Then the structure morphism `X ⟶ Spec A` induces a proper map
`X(K) → (Spec A)(K)`, in the sense of Mathlib's `IsProperMap`. Over `A = K` this says that the
`K`-points of a projective `K`-scheme form a compact space.

The compactness of `ℙⁿ(K)` holds for `K = ℂ`
(`TauCeti.Toric.compactSpace_points_projToSpec`, through toric geometry) and for every
nonarchimedean local field `K : Type`
(`TauCeti.SchemePointTopology.compactSpace_points_projToSpec_of_isNonarchimedeanLocalField`, by
normalizing homogeneous coordinates), so both cases are covered.

The proof factors the structure morphism through closed immersions
`X ⟶ Proj (Sym_A M) ⟶ ℙⁿ_A`, where `ℙⁿ_A = Proj (Sym_A (A ⊗[K] K^{n+1}))` is induced by a
surjection `A ⊗[K] K^{n+1} → M`. Closed immersions induce closed embeddings of `K`-points
(`TauCeti.SchemePointTopology.isClosedEmbedding_of_isClosedImmersion`), and these are proper
maps. The projective space `ℙⁿ_A` is the base change of `ℙⁿ_K` along `Spec A ⟶ Spec K`
(`AlgebraicGeometry.Proj.isPullback_symmetricAlgebra_baseChange`), so its `K`-points are the
product of those of `ℙⁿ_K` and of `Spec A`
(`TauCeti.SchemePointTopology.pointsProdHomeomorphOfIsPullback`). The projection from this
product is proper because `ℙⁿ(K)` is compact.

## Main results

All three assume that the `K`-points of every `ℙⁿ_K` are compact.

* `TauCeti.SchemePointTopology.isProperMap_map_projToSpec`: for a finite `A`-module `M`, the
  projection `Proj (Sym_A M)(K) → (Spec A)(K)` is proper.
* `TauCeti.SchemePointTopology.isProperMap_map_of_isProjectiveOver`: a projective scheme over a
  `K`-algebra `A` has a proper map of `K`-points to `Spec A`.
* `TauCeti.SchemePointTopology.compactSpace_of_isProjectiveOver`: the `K`-points of a
  projective `K`-scheme are compact; in particular the complex points of a projective
  `ℂ`-scheme and the `K`-points of a projective scheme over a nonarchimedean local field
  `K : Type`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII, Propositions
  3.1(viii) and 3.2(v).
* J.-P. Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2.
* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  proof of Prop. 4.4, p. 11, and Cor. 5.6, p. 16.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.SymmetricAlgebra
open scoped TensorProduct

namespace TauCeti.SchemePointTopology

attribute [local instance] topology

universe u

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T1Space K]
  [∀ n : ℕ, CompactSpace (Points (R := K) (projToSpec K (Option (Fin n) → K)))]
  {A : Type u} [CommRing A] [Algebra K A]

/-- The projection from `ℙⁿ_A = Proj (Sym_A (A ⊗[K] K^{n+1}))` is proper on `K`-points: these
points are the product of those of `ℙⁿ_K`, which are compact, and those of `Spec A`. -/
private theorem isProperMap_map_projToSpec_tensorProduct (n : ℕ) :
    IsProperMap (map (R := K) (projToSpec A (A ⊗[K] (Option (Fin n) → K)))
      (fX := projToSpec A (A ⊗[K] (Option (Fin n) → K)) ≫ Spec.algebraMap K A) rfl) := by
  have hP := Proj.isPullback_symmetricAlgebra_baseChange K A (Option (Fin n) → K)
  let e := pointsProdHomeomorphOfIsPullback (R := K) hP hP.w
  have he : map (R := K) (projToSpec A (A ⊗[K] (Option (Fin n) → K)))
      (fX := projToSpec A (A ⊗[K] (Option (Fin n) → K)) ≫ Spec.algebraMap K A) rfl =
        Prod.snd ∘ e := by
    funext x
    simp [e]
  rw [he]
  exact isProperMap_snd_of_compactSpace.comp e.isProperMap

/-- **Projective space over a `K`-algebra is proper on `K`-points.** When the `K`-points of every
`ℙⁿ_K` are compact, for a finite module `M` over a `K`-algebra `A`, the structure morphism of
`Proj (Sym_A M)` induces a proper map of `K`-points `Proj (Sym_A M)(K) → (Spec A)(K)`. -/
theorem isProperMap_map_projToSpec (M : Type u) [AddCommMonoid M] [Module A M]
    [Module.Finite A M] :
    IsProperMap (map (R := K) (projToSpec A M)
      (fX := projToSpec A M ≫ Spec.algebraMap K A) rfl) := by
  -- A surjection `A ⊗[K] K^{n+1} → M` embeds `Proj (Sym_A M)` as a closed subscheme of `ℙⁿ_A`.
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' A M
  let ψ : A ⊗[K] (Option (Fin n) → K) →ₗ[A] M := φ ∘ₗ LinearMap.funLeft A A Option.some ∘ₗ
    (TensorProduct.piScalarRight K A A (Option (Fin n))).toLinearMap
  have hψ : Function.Surjective ψ := hφ.comp <|
    (LinearMap.funLeft_surjective_of_injective A A _ (Option.some_injective _)).comp
      (TensorProduct.piScalarRight K A A (Option (Fin n))).surjective
  have hsurj : Function.Surjective (SymmetricAlgebra.gradedMap A ψ) := by
    simpa only [Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
      SymmetricAlgebra.map_surjective A ψ hψ
  let q := Proj.map (SymmetricAlgebra.gradedMap A ψ)
    (HomogeneousIdeal.irrelevant_le_map_of_surjective _ hsurj)
  have : IsClosedImmersion q := Proj.isClosedImmersion_map _ _ hsurj
  have hqP : q ≫ projToSpec A (A ⊗[K] (Option (Fin n) → K)) = projToSpec A M :=
    Proj.map_gradedMap_projToSpec A ψ _
  have hq : q ≫ projToSpec A (A ⊗[K] (Option (Fin n) → K)) ≫ Spec.algebraMap K A =
      projToSpec A M ≫ Spec.algebraMap K A := by
    rw [← Category.assoc, hqP]
  have hcomp : map (R := K) (projToSpec A M) (fX := projToSpec A M ≫ Spec.algebraMap K A) rfl =
      map (R := K) (projToSpec A (A ⊗[K] (Option (Fin n) → K))) rfl ∘ map q hq := by
    funext x
    rw [Function.comp_apply, map_map]
    congr 1
    rw [hqP]
  rw [hcomp]
  exact (isProperMap_map_projToSpec_tensorProduct n).comp
    (isClosedEmbedding_of_isClosedImmersion q hq).isProperMap

/-- **Projective schemes are proper on `K`-points.** When the `K`-points of every `ℙⁿ_K` are
compact, if `X` is projective over a `K`-algebra `A`, its structure morphism induces a proper map
of `K`-points `X(K) → (Spec A)(K)`. -/
theorem isProperMap_map_of_isProjectiveOver {X : Scheme.{u}} [X.Over (Spec (.of A))]
    [X.IsProjectiveOver A] :
    IsProperMap (map (R := K) (X ↘ Spec (.of A))
      (fX := (X ↘ Spec (.of A)) ≫ Spec.algebraMap K A) rfl) := by
  obtain ⟨M, _, _, _, j, hj, hjA⟩ := Scheme.IsProjectiveOver.exists_isClosedImmersion (R := A)
    (X := X)
  have hjq : j ≫ projToSpec A M = X ↘ Spec (.of A) := by
    rw [← over_eq_projToSpec, comp_over]
  have hj' : j ≫ projToSpec A M ≫ Spec.algebraMap K A = (X ↘ Spec (.of A)) ≫
      Spec.algebraMap K A := by
    rw [← Category.assoc, hjq]
  have hcomp : map (R := K) (X ↘ Spec (.of A)) (fX := (X ↘ Spec (.of A)) ≫ Spec.algebraMap K A)
      rfl = map (R := K) (projToSpec A M) rfl ∘ map j hj' := by
    funext x
    rw [Function.comp_apply, map_map]
    congr 1
    rw [hjq]
  rw [hcomp]
  exact (isProperMap_map_projToSpec M).comp
    (isClosedEmbedding_of_isClosedImmersion j hj').isProperMap

/-- **The `K`-points of a projective `K`-scheme are compact.** When the `K`-points of every `ℙⁿ_K`
are compact, the `K`-points of a projective `K`-scheme are compact. This applies to `K = ℂ` and to
every nonarchimedean local field `K : Type`. -/
instance compactSpace_of_isProjectiveOver {X : Scheme.{u}} [X.Over (Spec (.of K))]
    [X.IsProjectiveOver K] : CompactSpace (Points (R := K) (X ↘ Spec (.of K))) := by
  have hid : Spec.algebraMap K K = 𝟙 _ := by simp
  have : IsIso (Spec.algebraMap K K) := by rw [hid]; infer_instance
  -- The `K`-points of `Spec K` form a single point, so properness over it is compactness.
  have hc := (isProperMap_map_of_isProjectiveOver (K := K) (A := K) (X := X)).isCompact_preimage
    isCompact_univ
  have h : CompactSpace (Points (R := K) ((X ↘ Spec (.of K)) ≫ Spec.algebraMap K K)) :=
    ⟨by simpa using hc⟩
  rwa [hid, Category.comp_id] at h

end TauCeti.SchemePointTopology
