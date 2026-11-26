/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.Analysis.Normed.Field.CompletedAlgClosure.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.AlgEquiv
public import TauCeti.Topology.Algebra.UniformRing

import TauCeti.FieldTheory.KrullTopology
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import Mathlib.Topology.MetricSpace.Completion

/-!
# Galois automorphisms of the completed algebraic closure

Let `K` be a field complete for a nontrivial ultrametric absolute value, `K^alg` its algebraic
closure with the spectral norm and `C` the completion of `K^alg`. Every `σ ∈ G_K` is an isometry
of `K^alg` (`AlgHom.isometry`), so it extends to a continuous `K`-algebra
automorphism `σ_C` of `C`. This file proves that `σ ↦ σ_C` identifies `G_K` with the continuous
`K`-algebra automorphisms of `C`, compatibly with composition, and that the action map
`G_K × C → C` is jointly continuous for the Krull topology.

## Main definitions

* `TauCeti.SpectralAlgClosure.absoluteGaloisGroupEquiv K`: `G_K` as the `K`-algebra automorphisms
  of `K^alg`, transported along `SpectralAlgClosure.algEquiv K`.
* `Field.absoluteGaloisGroup.toContinuousAlgEquiv σ`: the extension `σ_C : C ≃A[K] C` of
  `σ ∈ G_K`.

## Main results

* `Field.absoluteGaloisGroup.toContinuousAlgEquiv_coe`: `σ_C` extends `σ`.
* `Field.absoluteGaloisGroup.eq_toContinuousAlgEquiv_of_continuous`: `σ_C` is the unique
  continuous map `C → C` extending `σ`.
* `Field.absoluteGaloisGroup.toContinuousAlgEquiv_mul`, `toContinuousAlgEquiv_one`,
  `toContinuousAlgEquiv_symm`: `(στ)_C = σ_C ∘ τ_C`, `1_C = id` and `(σ_C)⁻¹ = (σ⁻¹)_C`.
* `Field.absoluteGaloisGroup.isometry_toContinuousAlgEquiv`: `σ_C` is an isometry.
* `ContinuousAlgHom.exists_eq_absoluteGaloisGroup_toContinuousAlgEquiv`: every continuous
  `K`-algebra endomorphism of `C` is some `σ_C`.
* `Field.absoluteGaloisGroup.continuous_toContinuousAlgEquiv_apply`: `(σ, x) ↦ σ_C x` is jointly
  continuous.
* `TauCeti.CompletedAlgClosure.exists_galois_continuousAut_equiv`: `G_K ≅ Aut_cont(C/K)`: the
  map `σ ↦ σ_C` extends `σ`, respects composition, is bijective, and the action of `G_K` on `C`
  is jointly continuous.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
-/

public section

noncomputable section

namespace TauCeti

universe u

/-- The group isomorphism between the absolute Galois group `G_K` and the group of `K`-algebra
automorphisms of `SpectralAlgClosure K`. `Field.absoluteGaloisGroup K` is by definition
`AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` (`Field.absoluteGaloisGroup.toAlgEquiv`), and this
transports it along the canonical isomorphism `SpectralAlgClosure.algEquiv K`. -/
def SpectralAlgClosure.absoluteGaloisGroupEquiv (K : Type u) [Field K] :
    Field.absoluteGaloisGroup K ≃* (SpectralAlgClosure K ≃ₐ[K] SpectralAlgClosure K) :=
  Field.absoluteGaloisGroup.toAlgEquiv.trans (AlgEquiv.autCongr (SpectralAlgClosure.algEquiv K))

/-- `SpectralAlgClosure.absoluteGaloisGroupEquiv K σ` acts as `σ` through the canonical
isomorphism `SpectralAlgClosure.algEquiv K`. -/
@[simp]
theorem SpectralAlgClosure.absoluteGaloisGroupEquiv_apply (K : Type u) [Field K]
    (σ : Field.absoluteGaloisGroup K) (x : SpectralAlgClosure K) :
    absoluteGaloisGroupEquiv K σ x = algEquiv K (σ.toAlgHom ((algEquiv K).symm x)) :=
  (rfl)

/-- The inverse of `SpectralAlgClosure.absoluteGaloisGroupEquiv K` transports an automorphism of
`SpectralAlgClosure K` back along `SpectralAlgClosure.algEquiv K`. -/
@[simp]
theorem SpectralAlgClosure.absoluteGaloisGroupEquiv_symm_apply (K : Type u) [Field K]
    (φ : SpectralAlgClosure K ≃ₐ[K] SpectralAlgClosure K) (x : AlgebraicClosure K) :
    ((absoluteGaloisGroupEquiv K).symm φ).toAlgHom x = (algEquiv K).symm (φ (algEquiv K x)) :=
  (rfl)

/-- `SpectralAlgClosure.absoluteGaloisGroupEquiv K σ` is `σ` on the underlying type of
`AlgebraicClosure K`, the boundary between `G_K` and the automorphisms of the normed synonym. -/
theorem SpectralAlgClosure.absoluteGaloisGroupEquiv_apply_eq_toAlgHom (K : Type u) [Field K]
    (σ : Field.absoluteGaloisGroup K) (x : SpectralAlgClosure K) :
    absoluteGaloisGroupEquiv K σ x = σ.toAlgHom x := by
  rw [absoluteGaloisGroupEquiv_apply, algEquiv_symm_apply, algEquiv_apply]

/-- `SpectralAlgClosure.absoluteGaloisGroupEquiv K` is continuous for the Krull topologies. -/
theorem SpectralAlgClosure.continuous_absoluteGaloisGroupEquiv (K : Type u) [Field K] :
    Continuous (absoluteGaloisGroupEquiv K) :=
  -- `Field.absoluteGaloisGroup K` carries the Krull topology of `AlgebraicClosure K / K`, so the
  -- first factor `Field.absoluteGaloisGroup.toAlgEquiv` is the identity.
  continuous_autCongr_algEquiv K

end TauCeti

namespace Field.absoluteGaloisGroup

open TauCeti UniformSpace SpectralAlgClosure

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The extension `σ_C : C ≃A[K] C` of an element `σ` of the absolute Galois group of `K` to the
completed algebraic closure `C = CompletedAlgClosure K`: the completion of `σ`, which is an
isometry of `K^alg` (`AlgHom.isometry`). -/
def toContinuousAlgEquiv (σ : Field.absoluteGaloisGroup K) :
    CompletedAlgClosure K ≃A[K] CompletedAlgClosure K where
  toAlgEquiv := Completion.mapAlgEquiv (absoluteGaloisGroupEquiv K σ)
    (absoluteGaloisGroupEquiv K σ).toAlgHom.isometry.continuous
    (absoluteGaloisGroupEquiv K σ).symm.toAlgHom.isometry.continuous
  continuous_toFun := Completion.continuous_mapAlgEquiv _ _ _
  continuous_invFun := Completion.continuous_mapAlgEquiv_symm _ _ _

/-- `σ_C` is the completion of `σ`. -/
theorem toContinuousAlgEquiv_apply (σ : Field.absoluteGaloisGroup K)
    (x : CompletedAlgClosure K) :
    σ.toContinuousAlgEquiv x = Completion.map (absoluteGaloisGroupEquiv K σ) x :=
  Completion.mapAlgEquiv_apply (absoluteGaloisGroupEquiv K σ) _ _ x

/-- `σ_C` extends `σ`. -/
@[simp]
theorem toContinuousAlgEquiv_coe (σ : Field.absoluteGaloisGroup K) (x : SpectralAlgClosure K) :
    σ.toContinuousAlgEquiv x = ((absoluteGaloisGroupEquiv K σ) x : CompletedAlgClosure K) :=
  Completion.mapAlgEquiv_coe (absoluteGaloisGroupEquiv K σ) _ _ x

/-- **Uniqueness of the extension**: a continuous map `C → C` extending `σ` is `σ_C`. -/
theorem eq_toContinuousAlgEquiv_of_continuous (σ : Field.absoluteGaloisGroup K)
    {f : CompletedAlgClosure K → CompletedAlgClosure K} (hf : Continuous f)
    (h : ∀ x : SpectralAlgClosure K,
      f x = ((absoluteGaloisGroupEquiv K σ) x : CompletedAlgClosure K)) :
    f = σ.toContinuousAlgEquiv :=
  Completion.ext hf σ.toContinuousAlgEquiv.continuous fun x ↦ by
    rw [h, toContinuousAlgEquiv_coe]

/-- `σ ↦ σ_C` is compatible with composition: `(στ)_C = σ_C ∘ τ_C`. -/
theorem toContinuousAlgEquiv_mul (σ τ : Field.absoluteGaloisGroup K) :
    (σ * τ).toContinuousAlgEquiv = τ.toContinuousAlgEquiv.trans σ.toContinuousAlgEquiv := by
  have h : absoluteGaloisGroupEquiv K (σ * τ) =
      (absoluteGaloisGroupEquiv K τ).trans (absoluteGaloisGroupEquiv K σ) := map_mul _ σ τ
  refine ContinuousAlgEquiv.toAlgEquiv_injective ?_
  rw [ContinuousAlgEquiv.trans_toAlgEquiv]
  simp only [toContinuousAlgEquiv, h]
  exact Completion.mapAlgEquiv_trans _ _ _ _ _ _

/-- `(στ)_C x = σ_C (τ_C x)`. -/
@[simp]
theorem toContinuousAlgEquiv_mul_apply (σ τ : Field.absoluteGaloisGroup K)
    (x : CompletedAlgClosure K) :
    (σ * τ).toContinuousAlgEquiv x = σ.toContinuousAlgEquiv (τ.toContinuousAlgEquiv x) := by
  rw [toContinuousAlgEquiv_mul, ContinuousAlgEquiv.trans_apply]

/-- The extension of the identity is the identity. -/
@[simp]
theorem toContinuousAlgEquiv_one :
    (1 : Field.absoluteGaloisGroup K).toContinuousAlgEquiv =
      ContinuousAlgEquiv.refl K (CompletedAlgClosure K) := by
  have h : absoluteGaloisGroupEquiv K 1 = AlgEquiv.refl := map_one _
  refine ContinuousAlgEquiv.toAlgEquiv_injective (?_ : _ = AlgEquiv.refl)
  simp only [toContinuousAlgEquiv, h]
  exact Completion.mapAlgEquiv_refl

/-- The inverse of `σ_C` is the extension of `σ⁻¹`. -/
@[simp]
theorem toContinuousAlgEquiv_symm (σ : Field.absoluteGaloisGroup K) :
    σ.toContinuousAlgEquiv.symm = σ⁻¹.toContinuousAlgEquiv :=
  ContinuousAlgEquiv.ext <| funext fun x ↦ by
    rw [ContinuousAlgEquiv.symm_apply_eq, ← toContinuousAlgEquiv_mul_apply, mul_inv_cancel,
      toContinuousAlgEquiv_one, ContinuousAlgEquiv.refl_apply]

/-- `(σ_C)⁻¹ x = (σ⁻¹)_C x`. -/
theorem toContinuousAlgEquiv_symm_apply (σ : Field.absoluteGaloisGroup K)
    (x : CompletedAlgClosure K) :
    σ.toContinuousAlgEquiv.symm x = σ⁻¹.toContinuousAlgEquiv x := by
  rw [toContinuousAlgEquiv_symm]

/-- `σ_C` is an isometry. -/
theorem isometry_toContinuousAlgEquiv (σ : Field.absoluteGaloisGroup K) :
    Isometry σ.toContinuousAlgEquiv := by
  have h : ⇑σ.toContinuousAlgEquiv = Completion.map (absoluteGaloisGroupEquiv K σ) :=
    funext (toContinuousAlgEquiv_apply σ)
  rw [h]
  exact (absoluteGaloisGroupEquiv K σ).toAlgHom.isometry.completion_map

/-- `σ_C` preserves the norm. -/
@[simp]
theorem norm_toContinuousAlgEquiv (σ : Field.absoluteGaloisGroup K) (x : CompletedAlgClosure K) :
    ‖σ.toContinuousAlgEquiv x‖ = ‖x‖ := by
  simpa using (isometry_toContinuousAlgEquiv σ).norm_map_of_map_zero (map_zero _) x

/-- `σ ↦ σ_C` is injective: `σ_C` restricts to `σ` on `K^alg`. -/
theorem toContinuousAlgEquiv_injective :
    Function.Injective (toContinuousAlgEquiv (K := K)) := fun σ τ h ↦
  (absoluteGaloisGroupEquiv K).injective <| AlgEquiv.ext fun x : SpectralAlgClosure K ↦
    Completion.coe_injective _ <| by simpa using congr($h (x : CompletedAlgClosure K))

/-- **Every continuous `K`-algebra endomorphism of `C` is some `σ_C`.** -/
theorem _root_.ContinuousAlgHom.exists_eq_absoluteGaloisGroup_toContinuousAlgEquiv
    (τ : CompletedAlgClosure K →A[K] CompletedAlgClosure K) :
    ∃ σ : Field.absoluteGaloisGroup K, ⇑τ = σ.toContinuousAlgEquiv :=
  -- `τ` preserves the normal subextension `K^alg` of `C / K`; its restriction is `σ`.
  ⟨(absoluteGaloisGroupEquiv K).symm
      ((τ : CompletedAlgClosure K →ₐ[K] CompletedAlgClosure K).restrictNormal'
        (SpectralAlgClosure K)),
    eq_toContinuousAlgEquiv_of_continuous _ τ.continuous fun a ↦ by
      rw [MulEquiv.apply_symm_apply]
      exact ((τ : CompletedAlgClosure K →ₐ[K] CompletedAlgClosure K).restrictNormal_commutes
        (SpectralAlgClosure K) a).symm⟩

/-- Every continuous `K`-algebra automorphism of `C` is some `σ_C`. -/
theorem toContinuousAlgEquiv_surjective :
    Function.Surjective (toContinuousAlgEquiv (K := K)) := fun τ ↦
  (ContinuousAlgHom.exists_eq_absoluteGaloisGroup_toContinuousAlgEquiv
    (τ : CompletedAlgClosure K →A[K] CompletedAlgClosure K)).imp
    fun _ h ↦ ContinuousAlgEquiv.ext h.symm

/-- `σ ↦ σ_C` is a bijection from `G_K` onto the continuous `K`-algebra automorphisms of `C`. -/
theorem toContinuousAlgEquiv_bijective :
    Function.Bijective (toContinuousAlgEquiv (K := K)) :=
  ⟨toContinuousAlgEquiv_injective, toContinuousAlgEquiv_surjective⟩

/-- **Joint continuity**: the action map `G_K × C → C`, `(σ, x) ↦ σ_C x`, is continuous for the
Krull topology. Each `σ_C` is an isometry, and on the dense subset `K^alg` the orbit maps are
locally constant (`IsIntegral.isLocallyConstant_apply`). -/
theorem continuous_toContinuousAlgEquiv_apply :
    Continuous fun p : Field.absoluteGaloisGroup K × CompletedAlgClosure K ↦
      p.1.toContinuousAlgEquiv p.2 := by
  refine continuous_prod_of_dense_continuous_lipschitzWith' _ 1 Completion.denseRange_coe
    (fun σ ↦ (isometry_toContinuousAlgEquiv σ).lipschitzWith) ?_
  rintro _ ⟨a, rfl⟩
  simp only [toContinuousAlgEquiv_coe]
  exact (Completion.continuous_coe _).comp <|
    (Algebra.IsIntegral.isIntegral (R := K) a).isLocallyConstant_apply.continuous.comp
      (continuous_absoluteGaloisGroupEquiv K)

end Field.absoluteGaloisGroup

namespace TauCeti.CompletedAlgClosure

open Field.absoluteGaloisGroup

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **`G_K ≅ Aut_cont(C/K)`** (de Jong–van der Put, §3.6). Let `K` be a field complete for a
nontrivial ultrametric absolute value, of any characteristic. The map `σ ↦ σ_C` from the absolute
Galois group of `K` to the continuous `K`-algebra automorphisms of the completed algebraic
closure `C` extends `σ` on `K^alg`, is compatible with composition and bijective, and the action
map `G_K × C → C` is jointly continuous. Mathlib's `ContinuousAlgEquiv` has no group structure,
so the group law is stated as composition. -/
theorem exists_galois_continuousAut_equiv :
    ∃ e : Field.absoluteGaloisGroup K → (CompletedAlgClosure K ≃A[K] CompletedAlgClosure K),
      (∀ (σ : Field.absoluteGaloisGroup K) (x : SpectralAlgClosure K),
        e σ (algebraMap (SpectralAlgClosure K) (CompletedAlgClosure K) x) =
          algebraMap (SpectralAlgClosure K) (CompletedAlgClosure K) (σ.toAlgHom x)) ∧
      (∀ (σ τ : Field.absoluteGaloisGroup K) (x : CompletedAlgClosure K),
        e (σ * τ) x = e σ (e τ x)) ∧
      Function.Bijective e ∧
      Continuous (fun p : Field.absoluteGaloisGroup K × CompletedAlgClosure K ↦ e p.1 p.2) :=
  ⟨toContinuousAlgEquiv, fun σ x ↦ by
      rw [UniformSpace.Completion.algebraMap_def, Algebra.algebraMap_self_apply,
        toContinuousAlgEquiv_coe, SpectralAlgClosure.absoluteGaloisGroupEquiv_apply_eq_toAlgHom]
      -- The right side is the coercion `K^alg → C` of `σ x`.
      rfl,
    toContinuousAlgEquiv_mul_apply,
    toContinuousAlgEquiv_bijective, continuous_toContinuousAlgEquiv_apply⟩

end TauCeti.CompletedAlgClosure
