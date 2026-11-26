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
  `AlgebraicClosure K`-algebra structure of `AlgebraicClosure L`, on the normed synonyms.

## Main results

* `Field.absoluteGaloisGroup.toContinuousAlgEquiv_eq_completion`: `σ_C` is the completion of `σ`.
* `Field.absoluteGaloisGroup.completion_toContinuousAlgEquiv_apply`: change of algebraic closure,
  `τ_C ∘ σ_C = (τ σ τ⁻¹)_C ∘ τ_C`.
* `TauCeti.SpectralAlgClosure.isometry_mapOfAlgebra`: the embedding `K^alg → L^alg` is an
  isometry; `TauCeti.SpectralAlgClosure.bijective_mapOfAlgebra` and
  `TauCeti.SpectralAlgClosure.bijective_completion_map_mapOfAlgebra`: it and its extension
  `C_K → C_L` are bijective when `L` is algebraic over `K`.
* `Field.absoluteGaloisGroup.map_toContinuousAlgEquiv_mapOfAlgebra`: change of base field, the
  extension `C_K → C_L` of the embedding intertwines `(g|_{K^alg})_C` with `g_C` for `g ∈ G_L`.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
-/

public section

noncomputable section

open TauCeti UniformSpace SpectralAlgClosure

namespace Field.absoluteGaloisGroup

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- `σ_C` is the completion `AlgEquiv.completion` of `σ`, viewed as an automorphism of
`SpectralAlgClosure K`. -/
theorem toContinuousAlgEquiv_eq_completion (σ : Field.absoluteGaloisGroup K) :
    σ.toContinuousAlgEquiv = (absoluteGaloisGroupEquiv K σ).completion :=
  ContinuousAlgEquiv.ext <| funext fun x ↦ by
    rw [toContinuousAlgEquiv_apply, AlgEquiv.completion_apply]

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

/-- `SpectralAlgClosure.mapOfAlgebra K L` is bijective when `L` is algebraic over `K`: then
`AlgebraicClosure L` is algebraic over the algebraically closed field `AlgebraicClosure K`. -/
theorem bijective_mapOfAlgebra [Algebra K L] [Algebra.IsAlgebraic K L]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)] :
    Function.Bijective (mapOfAlgebra K L) := by
  have : Algebra.IsIntegral K (AlgebraicClosure L) := Algebra.IsIntegral.trans L
  have : Algebra.IsIntegral (AlgebraicClosure K) (AlgebraicClosure L) :=
    Algebra.IsIntegral.tower_top K
  exact (algEquiv L).bijective.comp <|
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := AlgebraicClosure K)).comp
      (algEquiv K).symm.bijective

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
  -- `SpectralAlgClosure L` is a synonym of `AlgebraicClosure L`, whose `K`-algebra structure
  -- comes from that of `L`.
  let : Algebra K (SpectralAlgClosure L) := inferInstanceAs (Algebra K (AlgebraicClosure L))
  let : NormedAlgebra K (SpectralAlgClosure L) :=
    { norm_smul_le c x := by
        -- `K` acts on `L^alg` through `L`, and `‖algebraMap L L^alg l‖ = ‖l‖`.
        have h : algebraMap K (SpectralAlgClosure L) c =
            algebraMap L (SpectralAlgClosure L) (algebraMap K L c) :=
          IsScalarTower.algebraMap_apply K L (AlgebraicClosure L) c
        rw [Algebra.smul_def, norm_mul, h, norm_algebraMap', norm_algebraMap'] }
  let f : SpectralAlgClosure K →ₐ[K] SpectralAlgClosure L :=
    { mapOfAlgebra K L with
      commutes' c := by
        simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_ofClass, mapOfAlgebra_apply, algEquiv_symm_apply, algEquiv_apply]
        exact (IsScalarTower.algebraMap_apply K (AlgebraicClosure K) (AlgebraicClosure L) c).symm }
  exact f.isometry

/-- **`C_K` is also the completed algebraic closure of `L`** when `L` is algebraic over `K`: the
extension `C_K → C_L` of the embedding `K^alg → L^alg` is bijective, as the completion
`UniformSpace.Completion.mapEquiv` of a uniform isomorphism. It is an isometry by
`isometry_mapOfAlgebra` and `Isometry.completion_map`. -/
theorem bijective_completion_map_mapOfAlgebra [Algebra.IsAlgebraic K L] :
    Function.Bijective (Completion.map (mapOfAlgebra K L)) := by
  let e : SpectralAlgClosure K ≃ᵤ SpectralAlgClosure L :=
    { Equiv.ofBijective _ (bijective_mapOfAlgebra K L) with
      uniformContinuous_toFun := (isometry_mapOfAlgebra K L).uniformContinuous
      uniformContinuous_invFun := ((isometry_mapOfAlgebra K L).right_inv
        (Equiv.ofBijective _ (bijective_mapOfAlgebra K L)).apply_symm_apply).uniformContinuous }
  have h : Completion.map (mapOfAlgebra K L) = Completion.mapEquiv e :=
    Completion.ext Completion.continuous_map (Completion.mapEquiv e).continuous fun a ↦ by
      -- `e` is `mapOfAlgebra K L` as a function, by construction.
      rw [Completion.mapEquiv_coe,
        Completion.map_coe (isometry_mapOfAlgebra K L).uniformContinuous]
      rfl
  exact h ▸ (Completion.mapEquiv e).bijective

end TauCeti.SpectralAlgClosure

namespace Field.absoluteGaloisGroup

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] [NormedAlgebra K L]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]

/-- **Change of base field.** For `g ∈ G_L`, the extension `C_K → C_L` of the embedding
`K^alg → L^alg` intertwines the extension to `C_K` of the restriction
`Field.absoluteGaloisGroup.mapOfAlgebra K L g ∈ G_K` with the extension `g_C` of `g` to `C_L`. -/
theorem map_toContinuousAlgEquiv_mapOfAlgebra (g : Field.absoluteGaloisGroup L)
    (x : CompletedAlgClosure K) :
    Completion.map (SpectralAlgClosure.mapOfAlgebra K L)
        ((Field.absoluteGaloisGroup.mapOfAlgebra K L g).toContinuousAlgEquiv x) =
      g.toContinuousAlgEquiv (Completion.map (SpectralAlgClosure.mapOfAlgebra K L) x) := by
  have hu := (isometry_mapOfAlgebra K L).uniformContinuous
  refine Completion.induction_on x (isClosed_eq
    (Completion.continuous_map.comp (ContinuousAlgEquiv.continuous _))
    ((ContinuousAlgEquiv.continuous _).comp Completion.continuous_map)) fun a ↦ ?_
  rw [toContinuousAlgEquiv_coe, Completion.map_coe hu, Completion.map_coe hu,
    toContinuousAlgEquiv_coe, absoluteGaloisGroupEquiv_apply, absoluteGaloisGroupEquiv_apply]
  simp only [SpectralAlgClosure.mapOfAlgebra_apply, AlgEquiv.symm_apply_apply]
  -- `σ.toAlgHom` is the coercion of `σ` as an element of `Gal(AlgebraicClosure K/K)`, the form in
  -- which `absoluteGaloisGroup_mapOfAlgebra_commutes` states the intertwining.
  exact congrArg (fun y ↦ ((algEquiv L y : SpectralAlgClosure L) : CompletedAlgClosure L))
    (absoluteGaloisGroup_mapOfAlgebra_commutes K L g ((algEquiv K).symm a))

end Field.absoluteGaloisGroup
