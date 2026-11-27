/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.CompletedAlgClosure.Galois
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Completion

import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map

/-!
# Changing the algebraic closure and the base field of `σ ↦ σ_C`

Let `K` be a field complete for a nontrivial ultrametric absolute value, `K^alg` its algebraic
closure with the spectral norm, `C` the completion of `K^alg` and `σ ↦ σ_C` the extension of
elements of the absolute Galois group `G_K` to `C`
(`Field.absoluteGaloisGroup.toContinuousAlgEquiv`). This file shows that the extension is
compatible with the two choices made in defining it.

* **The algebraic closure.** For another normed field `E` algebraic over `K` and a `K`-isomorphism
  `τ : K^alg ≃ₐ[K] E`, the completion `τ_C` of `τ` is an isometric isomorphism of `C` onto the
  completion of `E` (`AlgEquiv.isometry_completion`), and it intertwines `σ_C` with the extension
  of the conjugate `τ σ τ⁻¹`.
* **The base field.** Let `L` be a second complete ultrametric field, a normed `K`-algebra, with
  algebraic closures embedded compatibly, `K^alg → L^alg` over `K`. The embedding is an isometry
  for the spectral norms, so it extends to the completions `C_K → C_L`, and this extension
  intertwines the action of `g ∈ G_L` on `C_L` with that of its restriction
  `Field.absoluteGaloisGroup.mapOfAlgebra K L g ∈ G_K` on `C_K`. When `L` is algebraic over `K`,
  for instance a finite extension inside `K^alg`, the embedding of algebraic closures is bijective,
  so `C_K` is also the completed algebraic closure of `L`, and the extension of `g` computed over
  `L` is the extension of its restriction computed over `K`.

## Main definitions

* `TauCeti.SpectralAlgClosure.mapOfAlgebra K L`: the embedding `K^alg → L^alg` given by the
  `AlgebraicClosure K`-algebra structure of `AlgebraicClosure L`, on the normed synonyms, and
  `TauCeti.SpectralAlgClosure.mapOfAlgebraEquiv K L` the same map as a ring isomorphism when `L`
  is algebraic over `K`.
* `TauCeti.SpectralAlgClosure.completionMapOfAlgebra K L`: its extension `C_K →+* C_L`, and
  `TauCeti.SpectralAlgClosure.completionMapOfAlgebraEquiv K L` the isomorphism `C_K ≃+* C_L` when
  `L` is algebraic over `K`.

## Main results

* `Field.absoluteGaloisGroup.completion_toContinuousAlgEquiv_apply`: change of algebraic closure,
  `τ_C ∘ σ_C = (τ σ τ⁻¹)_C ∘ τ_C`.
* `TauCeti.SpectralAlgClosure.mapOfAlgebra_algebraMap` and
  `TauCeti.SpectralAlgClosure.completionMapOfAlgebra_algebraMap`: the embedding `K^alg → L^alg`
  and its extension `C_K → C_L` are `K`-linear;
  `TauCeti.SpectralAlgClosure.isometry_mapOfAlgebra`: the embedding is an isometry;
  `TauCeti.SpectralAlgClosure.mapOfAlgebra_bijective` and
  `TauCeti.SpectralAlgClosure.completionMapOfAlgebra_bijective`: it and its extension `C_K → C_L`
  are bijective when `L` is algebraic over `K`.
* `Field.absoluteGaloisGroup.completionMapOfAlgebra_toContinuousAlgEquiv_mapOfAlgebra`: change of
  base field, the extension `C_K → C_L` of the embedding intertwines `(g|_{K^alg})_C` with `g_C`
  for `g ∈ G_L`.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
-/

public section

noncomputable section

open TauCeti UniformSpace SpectralAlgClosure

namespace Field.absoluteGaloisGroup

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **Change of algebraic closure.** Let `E` be a normed field algebraic over `K` and
`τ : K^alg ≃ₐ[K] E` a `K`-isomorphism. The completion `τ_C` of `τ` intertwines `σ_C` with the
extension to the completion of `E` of the conjugate `τ σ τ⁻¹`: `τ_C (σ_C x) = (τ σ τ⁻¹)_C (τ_C x)`.
-/
theorem completion_toContinuousAlgEquiv_apply {E : Type*} [NormedField E] [NormedAlgebra K E]
    [Algebra.IsAlgebraic K E] (σ : Field.absoluteGaloisGroup K)
    (τ : SpectralAlgClosure K ≃ₐ[K] E) (x : CompletedAlgClosure K) :
    τ.completion (σ.toContinuousAlgEquiv x) =
      (AlgEquiv.autCongr τ (absoluteGaloisGroupEquiv K σ)).completion (τ.completion x) := by
  rw [AlgEquiv.completion_autCongr_apply, ContinuousAlgEquiv.symm_apply_apply,
    toContinuousAlgEquiv_eq_completion]

end Field.absoluteGaloisGroup

namespace TauCeti.SpectralAlgClosure

section Field

variable (K L : Type*) [Field K] [Field L] [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]

/-- The embedding `K^alg → L^alg` given by the `AlgebraicClosure K`-algebra structure of
`AlgebraicClosure L`, as a ring homomorphism of the normed synonyms `SpectralAlgClosure K →+*
SpectralAlgClosure L`. -/
def mapOfAlgebra : SpectralAlgClosure K →+* SpectralAlgClosure L :=
  (algEquiv L).toRingHom.comp <|
    (algebraMap (AlgebraicClosure K) (AlgebraicClosure L)).comp (algEquiv K).symm.toRingHom

/-- `SpectralAlgClosure.mapOfAlgebra K L` is the algebra map `AlgebraicClosure K →
AlgebraicClosure L`, read through the canonical isomorphisms `SpectralAlgClosure.algEquiv`. -/
theorem mapOfAlgebra_apply (x : SpectralAlgClosure K) :
    mapOfAlgebra K L x =
      algEquiv L (algebraMap (AlgebraicClosure K) (AlgebraicClosure L) ((algEquiv K).symm x)) :=
  (rfl)

/-- `SpectralAlgClosure.mapOfAlgebra K L` is `K`-linear: it sends the image of `c : K` in `K^alg`
to the image of `c` in `L^alg`, through `L`. -/
@[simp]
theorem mapOfAlgebra_algebraMap [Algebra K L]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)] (c : K) :
    mapOfAlgebra K L (algebraMap K (SpectralAlgClosure K) c) =
      algebraMap L (SpectralAlgClosure L) (algebraMap K L c) := by
  rw [mapOfAlgebra_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply K L (AlgebraicClosure L), AlgEquiv.commutes]

variable [Algebra K L] [Algebra.IsAlgebraic K L]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- `SpectralAlgClosure.mapOfAlgebra K L` is bijective when `L` is algebraic over `K`
(`TauCeti.algebraMap_algebraicClosure_bijective`). -/
theorem mapOfAlgebra_bijective : Function.Bijective (mapOfAlgebra K L) :=
  (algEquiv L).bijective.comp <|
    (algebraMap_algebraicClosure_bijective K L).comp (algEquiv K).symm.bijective

/-- `SpectralAlgClosure.mapOfAlgebra K L` as a ring isomorphism `SpectralAlgClosure K ≃+*
SpectralAlgClosure L`, when `L` is algebraic over `K`. -/
def mapOfAlgebraEquiv : SpectralAlgClosure K ≃+* SpectralAlgClosure L :=
  RingEquiv.ofBijective (mapOfAlgebra K L) (mapOfAlgebra_bijective K L)

/-- `SpectralAlgClosure.mapOfAlgebraEquiv K L` is `SpectralAlgClosure.mapOfAlgebra K L`. -/
@[simp]
theorem coe_mapOfAlgebraEquiv : ⇑(mapOfAlgebraEquiv K L) = mapOfAlgebra K L :=
  (rfl)

/-- `SpectralAlgClosure.mapOfAlgebra K L` undoes the inverse of
`SpectralAlgClosure.mapOfAlgebraEquiv K L`. -/
@[simp]
theorem mapOfAlgebra_mapOfAlgebraEquiv_symm (b : SpectralAlgClosure L) :
    mapOfAlgebra K L ((mapOfAlgebraEquiv K L).symm b) = b :=
  (mapOfAlgebraEquiv K L).apply_symm_apply b

/-- The inverse of `SpectralAlgClosure.mapOfAlgebraEquiv K L` undoes
`SpectralAlgClosure.mapOfAlgebra K L`. -/
@[simp]
theorem mapOfAlgebraEquiv_symm_mapOfAlgebra (a : SpectralAlgClosure K) :
    (mapOfAlgebraEquiv K L).symm (mapOfAlgebra K L a) = a :=
  (mapOfAlgebraEquiv K L).symm_apply_apply a

end Field

variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [NormedAlgebra K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- **The embedding `K^alg → L^alg` is an isometry** for the spectral norms over `K` and over `L`.
Through the embedding, `L^alg` is a normed `K`-algebra, since the norm of `L` restricts to that of
`K`, and a `K`-algebra map out of the algebraic extension `K^alg` preserves the norm
(`AlgHom.isometry`). -/
theorem isometry_mapOfAlgebra : Isometry (mapOfAlgebra K L) := by
  -- `L^alg` is a normed `K`-algebra through `L`: the algebra map of
  -- `NormedAlgebra.restrictScalars` is `algebraMap L _ ∘ algebraMap K L` by definition, which is
  -- the scalar tower `K → L → L^alg`.
  let := NormedAlgebra.restrictScalars K L (SpectralAlgClosure L)
  have : IsScalarTower K L (SpectralAlgClosure L) := .of_algebraMap_eq fun _ ↦ rfl
  let f : SpectralAlgClosure K →ₐ[K] SpectralAlgClosure L :=
    { toRingHom := mapOfAlgebra K L
      commutes' := fun c ↦
        (mapOfAlgebra_algebraMap K L c).trans (IsScalarTower.algebraMap_apply K L _ c).symm }
  exact f.isometry

/-- The extension `C_K →+* C_L` of the embedding `K^alg → L^alg`: the completion of
`SpectralAlgClosure.mapOfAlgebra K L`, which is an isometry (`isometry_mapOfAlgebra`). -/
def completionMapOfAlgebra : CompletedAlgClosure K →+* CompletedAlgClosure L :=
  Completion.mapRingHom (mapOfAlgebra K L) (isometry_mapOfAlgebra K L).continuous

/-- `SpectralAlgClosure.completionMapOfAlgebra K L` is the completion of the embedding. -/
theorem completionMapOfAlgebra_apply (x : CompletedAlgClosure K) :
    completionMapOfAlgebra K L x = Completion.map (mapOfAlgebra K L) x :=
  Completion.mapRingHom_apply _ _

/-- `SpectralAlgClosure.completionMapOfAlgebra K L` extends the embedding `K^alg → L^alg`. -/
@[simp]
theorem completionMapOfAlgebra_coe (a : SpectralAlgClosure K) :
    completionMapOfAlgebra K L a = (mapOfAlgebra K L a : CompletedAlgClosure L) := by
  rw [completionMapOfAlgebra_apply,
    Completion.map_coe (isometry_mapOfAlgebra K L).uniformContinuous]

/-- `SpectralAlgClosure.completionMapOfAlgebra K L` is `K`-linear: it sends the image of `c : K`
in `C_K` to the image of `c` in `C_L`, through `L`. -/
@[simp]
theorem completionMapOfAlgebra_algebraMap (c : K) :
    completionMapOfAlgebra K L (algebraMap K (CompletedAlgClosure K) c) =
      algebraMap L (CompletedAlgClosure L) (algebraMap K L c) := by
  rw [Completion.algebraMap_def, completionMapOfAlgebra_coe, mapOfAlgebra_algebraMap,
    Completion.algebraMap_def]

/-- `SpectralAlgClosure.completionMapOfAlgebra K L` is an isometry. -/
theorem isometry_completionMapOfAlgebra : Isometry (completionMapOfAlgebra K L) :=
  funext (completionMapOfAlgebra_apply K L) ▸ (isometry_mapOfAlgebra K L).completion_map

section Algebraic

variable [Algebra.IsAlgebraic K L]

/-- **`C_K` is also the completed algebraic closure of `L`** when `L` is algebraic over `K`: the
isomorphism `C_K ≃+* C_L` extending `SpectralAlgClosure.mapOfAlgebraEquiv K L`, an isometry in
both directions. -/
def completionMapOfAlgebraEquiv : CompletedAlgClosure K ≃+* CompletedAlgClosure L :=
  Completion.mapRingEquiv (mapOfAlgebraEquiv K L) (isometry_mapOfAlgebra K L).continuous
    ((isometry_mapOfAlgebra K L).right_inv (mapOfAlgebraEquiv K L).apply_symm_apply).continuous

/-- The isomorphism `C_K ≃+* C_L` is `SpectralAlgClosure.completionMapOfAlgebra K L`. -/
@[simp]
theorem coe_completionMapOfAlgebraEquiv :
    ⇑(completionMapOfAlgebraEquiv K L) = completionMapOfAlgebra K L :=
  funext fun x ↦ (Completion.mapRingEquiv_apply _ _ _ x).trans
    (completionMapOfAlgebra_apply K L x).symm

/-- The inverse of the isomorphism `C_K ≃+* C_L` extends the inverse of
`SpectralAlgClosure.mapOfAlgebraEquiv K L`. -/
@[simp]
theorem completionMapOfAlgebraEquiv_symm_coe (b : SpectralAlgClosure L) :
    (completionMapOfAlgebraEquiv K L).symm b =
      ((mapOfAlgebraEquiv K L).symm b : CompletedAlgClosure K) := by
  rw [RingEquiv.symm_apply_eq, coe_completionMapOfAlgebraEquiv, completionMapOfAlgebra_coe,
    mapOfAlgebra_mapOfAlgebraEquiv_symm]

/-- The extension `C_K → C_L` of the embedding `K^alg → L^alg` is bijective when `L` is algebraic
over `K`. -/
theorem completionMapOfAlgebra_bijective : Function.Bijective (completionMapOfAlgebra K L) :=
  coe_completionMapOfAlgebraEquiv K L ▸ (completionMapOfAlgebraEquiv K L).bijective

end Algebraic

end TauCeti.SpectralAlgClosure

namespace Field.absoluteGaloisGroup

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [NormedAlgebra K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- **Change of base field.** For `g ∈ G_L`, the extension `C_K → C_L` of the embedding
`K^alg → L^alg` intertwines the extension to `C_K` of the restriction
`Field.absoluteGaloisGroup.mapOfAlgebra K L g ∈ G_K` with the extension `g_C` of `g` to `C_L`. -/
theorem completionMapOfAlgebra_toContinuousAlgEquiv_mapOfAlgebra
    (g : Field.absoluteGaloisGroup L) (x : CompletedAlgClosure K) :
    completionMapOfAlgebra K L
        ((Field.absoluteGaloisGroup.mapOfAlgebra K L g).toContinuousAlgEquiv x) =
      g.toContinuousAlgEquiv (completionMapOfAlgebra K L x) := by
  have hc := (isometry_completionMapOfAlgebra K L).continuous
  refine Completion.induction_on x (isClosed_eq (hc.comp (ContinuousAlgEquiv.continuous _))
    ((ContinuousAlgEquiv.continuous _).comp hc)) fun a ↦ ?_
  rw [toContinuousAlgEquiv_coe, completionMapOfAlgebra_coe, completionMapOfAlgebra_coe,
    toContinuousAlgEquiv_coe, absoluteGaloisGroupEquiv_apply, absoluteGaloisGroupEquiv_apply]
  simp only [SpectralAlgClosure.mapOfAlgebra_apply, AlgEquiv.symm_apply_apply]
  -- `σ.toAlgHom` is the coercion of `σ` as an element of `Gal(AlgebraicClosure K/K)`, the form in
  -- which `absoluteGaloisGroup_mapOfAlgebra_commutes` states the intertwining.
  exact congrArg (fun y ↦ ((algEquiv L y : SpectralAlgClosure L) : CompletedAlgClosure L))
    (absoluteGaloisGroup_mapOfAlgebra_commutes K L g ((algEquiv K).symm a))

end Field.absoluteGaloisGroup
