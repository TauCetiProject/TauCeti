/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.Analysis.Normed.Field.CompletedAlgClosure.Basic
public import TauCeti.Topology.Algebra.UniformRing

import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.MetricSpace.Completion

/-!
# Galois automorphisms of the completed algebraic closure

Let `K` be a field complete for a nontrivial ultrametric absolute value, `K^alg` its algebraic
closure with the spectral norm and `C` the completion of `K^alg`. Every `σ ∈ G_K` is an isometry
of `K^alg` (Mathlib's `spectralNorm_eq_of_equiv`), so it extends to a continuous `K`-algebra
automorphism `σ_C` of `C`. This file proves that `σ ↦ σ_C` identifies `G_K` with the continuous
`K`-algebra automorphisms of `C`, compatibly with composition, and that the action map
`G_K × C → C` is jointly continuous for the Krull topology.

## Main definitions

* `TauCeti.CompletedAlgClosure.galoisExtension σ`: the extension `σ_C : C ≃A[K] C` of `σ ∈ G_K`.

## Main results

* `TauCeti.CompletedAlgClosure.galoisExtension_coe`: `σ_C` extends `σ`.
* `TauCeti.CompletedAlgClosure.eq_galoisExtension_of_continuous`: `σ_C` is the unique continuous
  map `C → C` extending `σ`.
* `TauCeti.CompletedAlgClosure.galoisExtension_mul`, `galoisExtension_one`: `(στ)_C = σ_C ∘ τ_C`
  and `1_C = id`.
* `TauCeti.CompletedAlgClosure.isometry_galoisExtension`: `σ_C` is an isometry.
* `TauCeti.CompletedAlgClosure.exists_galoisExtension_eq`: every continuous `K`-algebra
  endomorphism of `C` is some `σ_C`.
* `TauCeti.CompletedAlgClosure.continuous_galoisExtension_apply`: `(σ, x) ↦ σ_C x` is jointly
  continuous.
* `TauCeti.CompletedAlgClosure.exists_galois_continuousAut_equiv`: `G_K ≅ Aut_cont(C/K)`, the
  end theorem of §0.2 of the roadmap.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*, Documenta Math.
  1 (1996), §3.6.
* TauCetiRoadmap, `GaloisActionOnEtaleCohomology/README.md`, §0.2.
-/

@[expose] public section

noncomputable section

namespace TauCeti

universe u

/-- An element of the absolute Galois group `G_K`, viewed as a `K`-algebra automorphism of
`SpectralAlgClosure K`. -/
abbrev SpectralAlgClosure.absoluteGaloisGroupEquiv (K : Type u) [Field K] :
    Field.absoluteGaloisGroup K ≃* (SpectralAlgClosure K ≃ₐ[K] SpectralAlgClosure K) :=
  MulEquiv.refl _

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- A `K`-algebra automorphism of `K^alg` is an isometry for the spectral norm. -/
theorem SpectralAlgClosure.isometry_algEquiv
    (σ : SpectralAlgClosure K ≃ₐ[K] SpectralAlgClosure K) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ fun x ↦ (spectralNorm_eq_of_equiv σ x).symm

namespace CompletedAlgClosure

open UniformSpace SpectralAlgClosure

/-- The extension `σ_C : C ≃A[K] C` of an element `σ` of the absolute Galois group of `K` to the
completed algebraic closure: the completion of `σ`, an isometry of `K^alg`. -/
def galoisExtension (σ : Field.absoluteGaloisGroup K) :
    CompletedAlgClosure K ≃A[K] CompletedAlgClosure K where
  toAlgEquiv := Completion.mapAlgEquiv (absoluteGaloisGroupEquiv K σ)
    (isometry_algEquiv (absoluteGaloisGroupEquiv K σ)).continuous
    (isometry_algEquiv (absoluteGaloisGroupEquiv K σ).symm).continuous
  continuous_toFun := Completion.continuous_mapAlgEquiv _ _ _
  continuous_invFun := Completion.continuous_mapAlgEquiv_symm _ _ _

/-- `σ_C` is the completion of `σ`. -/
theorem galoisExtension_apply (σ : Field.absoluteGaloisGroup K) (x : CompletedAlgClosure K) :
    galoisExtension σ x =
      Completion.map (absoluteGaloisGroupEquiv K σ) x :=
  Completion.mapAlgEquiv_apply (absoluteGaloisGroupEquiv K σ) _ _ x

/-- `σ_C` extends `σ`. -/
@[simp]
theorem galoisExtension_coe (σ : Field.absoluteGaloisGroup K) (x : SpectralAlgClosure K) :
    galoisExtension σ x =
      ((absoluteGaloisGroupEquiv K σ) x : CompletedAlgClosure K) :=
  Completion.mapAlgEquiv_coe (absoluteGaloisGroupEquiv K σ) _ _ x

/-- **Uniqueness of the extension**: a continuous map `C → C` extending `σ` is `σ_C`. -/
theorem eq_galoisExtension_of_continuous (σ : Field.absoluteGaloisGroup K)
    {f : CompletedAlgClosure K → CompletedAlgClosure K} (hf : Continuous f)
    (h : ∀ x : SpectralAlgClosure K,
      f x = ((absoluteGaloisGroupEquiv K σ) x : CompletedAlgClosure K)) :
    f = galoisExtension σ :=
  Completion.ext hf (galoisExtension σ).continuous fun x ↦ by rw [h, galoisExtension_coe]

/-- `σ ↦ σ_C` is compatible with composition: `(στ)_C = σ_C ∘ τ_C`. -/
theorem galoisExtension_mul (σ τ : Field.absoluteGaloisGroup K) :
    galoisExtension (σ * τ) = (galoisExtension τ).trans (galoisExtension σ) :=
  ContinuousAlgEquiv.ext <| funext fun x ↦ congr($(Completion.mapAlgEquiv_trans
    (absoluteGaloisGroupEquiv K τ) (absoluteGaloisGroupEquiv K σ)
    (isometry_algEquiv _).continuous (isometry_algEquiv _).continuous
    (isometry_algEquiv _).continuous (isometry_algEquiv _).continuous) x)

/-- `(στ)_C x = σ_C (τ_C x)`. -/
theorem galoisExtension_mul_apply (σ τ : Field.absoluteGaloisGroup K)
    (x : CompletedAlgClosure K) :
    galoisExtension (σ * τ) x = galoisExtension σ (galoisExtension τ x) := by
  rw [galoisExtension_mul]
  rfl

/-- The extension of the identity is the identity. -/
@[simp]
theorem galoisExtension_one :
    galoisExtension (1 : Field.absoluteGaloisGroup K) =
      ContinuousAlgEquiv.refl K (CompletedAlgClosure K) :=
  ContinuousAlgEquiv.ext <| funext fun x ↦ congr($(Completion.mapAlgEquiv_refl
    (α := SpectralAlgClosure K) (R := K)) x)

/-- `σ_C` is an isometry. -/
theorem isometry_galoisExtension (σ : Field.absoluteGaloisGroup K) :
    Isometry (galoisExtension σ) := by
  rw [show ⇑(galoisExtension σ) = _ from funext (galoisExtension_apply σ)]
  exact (isometry_algEquiv (absoluteGaloisGroupEquiv K σ)).completion_map

/-- `σ_C` preserves the norm. -/
@[simp]
theorem norm_galoisExtension (σ : Field.absoluteGaloisGroup K) (x : CompletedAlgClosure K) :
    ‖galoisExtension σ x‖ = ‖x‖ := by
  simpa using (isometry_galoisExtension σ).norm_map_of_map_zero (map_zero _) x

/-- `σ ↦ σ_C` is injective: `σ_C` restricts to `σ` on `K^alg`. -/
theorem galoisExtension_injective :
    Function.Injective (galoisExtension (K := K)) := fun σ τ h ↦
  (absoluteGaloisGroupEquiv K).injective <| AlgEquiv.ext fun x : SpectralAlgClosure K ↦
    Completion.coe_injective _ <| by simpa using congr($h (x : CompletedAlgClosure K))

/-- **Every continuous `K`-algebra endomorphism of `C` is some `σ_C`.** It sends each `a ∈ K^alg` to
a root of the minimal polynomial of `a`, which splits in `K^alg`, so it preserves `K^alg`; its
restriction to `K^alg` is an automorphism because `K^alg / K` is algebraic. -/
theorem exists_galoisExtension_eq (τ : CompletedAlgClosure K →A[K] CompletedAlgClosure K) :
    ∃ σ : Field.absoluteGaloisGroup K, ⇑τ = galoisExtension σ := by
  let ι := IsScalarTower.toAlgHom K (SpectralAlgClosure K) (CompletedAlgClosure K)
  have hι : Function.Injective ι := ι.toRingHom.injective
  let φ := (τ : CompletedAlgClosure K →ₐ[K] CompletedAlgClosure K).comp ι
  have hφ (a : SpectralAlgClosure K) : φ a ∈ ι.range := by
    refine (Algebra.IsIntegral.isIntegral (R := K) a |>.map φ).mem_range_algHom_of_minpoly_splits
      (K := SpectralAlgClosure K) (L := CompletedAlgClosure K) ?_ ι
    rw [minpoly.algHom_eq φ φ.toRingHom.injective]
    exact IsAlgClosed.splits _
  let ρ := (AlgEquiv.ofInjective ι hι).symm.toAlgHom.comp (φ.codRestrict ι.range hφ)
  have hρ (a : SpectralAlgClosure K) : ι (ρ a) = φ a :=
    congr($((AlgEquiv.ofInjective ι hι).apply_symm_apply ⟨φ a, hφ a⟩).val)
  refine ⟨AlgEquiv.ofBijective ρ (Algebra.IsAlgebraic.algHom_bijective ρ),
    eq_galoisExtension_of_continuous _ τ.continuous fun a ↦ (hρ a).symm⟩

/-- Every continuous `K`-algebra automorphism of `C` is some `σ_C`. -/
theorem galoisExtension_surjective (τ : CompletedAlgClosure K ≃A[K] CompletedAlgClosure K) :
    ∃ σ : Field.absoluteGaloisGroup K, galoisExtension σ = τ :=
  (exists_galoisExtension_eq (τ : CompletedAlgClosure K →A[K] CompletedAlgClosure K)).imp
    fun _ h ↦ ContinuousAlgEquiv.ext h.symm

/-- `σ ↦ σ_C` is a bijection from `G_K` onto the continuous `K`-algebra automorphisms of `C`. -/
theorem galoisExtension_bijective : Function.Bijective (galoisExtension (K := K)) :=
  ⟨galoisExtension_injective, galoisExtension_surjective⟩

/-- **Joint continuity**: the action map `G_K × C → C`, `(σ, x) ↦ σ_C x`, is continuous for the
Krull topology. -/
theorem continuous_galoisExtension_apply :
    Continuous fun p : Field.absoluteGaloisGroup K × CompletedAlgClosure K ↦
      galoisExtension p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun ⟨σ₀, x⟩ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨a, ha⟩ := Completion.denseRange_coe.exists_dist_lt x (by positivity : 0 < ε / 3)
  have hS : IsOpen (absoluteGaloisGroupEquiv K ⁻¹'
      (MulAction.stabilizer (SpectralAlgClosure K ≃ₐ[K] SpectralAlgClosure K) a : Set _)) :=
    stabilizer_isOpen_of_isIntegral (K := K) a
  have hU := hS.preimage
    (continuous_const.mul continuous_id : Continuous fun σ : Field.absoluteGaloisGroup K ↦ σ₀⁻¹ * σ)
  filter_upwards [prod_mem_nhds (hU.mem_nhds (by simp)) (Metric.ball_mem_nhds x
    (by positivity : 0 < ε / 3))] with ⟨σ, y⟩ ⟨hσ, hy⟩
  have hσa : (absoluteGaloisGroupEquiv K σ) a = (absoluteGaloisGroupEquiv K σ₀) a := by
    simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, AlgEquiv.aut_mul,
      AlgEquiv.symm_apply_eq] using hσ
  have h1 : dist (galoisExtension σ y) (galoisExtension σ a) < 2 * (ε / 3) := by
    rw [(isometry_galoisExtension σ).dist_eq]
    linarith [dist_triangle y x a, Metric.mem_ball.1 hy]
  have h2 : galoisExtension σ a = galoisExtension σ₀ a := by
    simp only [galoisExtension_coe, hσa]
  have h3 : dist (galoisExtension σ₀ a) (galoisExtension σ₀ x) < ε / 3 := by
    rwa [(isometry_galoisExtension σ₀).dist_eq, dist_comm]
  calc dist (galoisExtension σ y) (galoisExtension σ₀ x)
      ≤ dist (galoisExtension σ y) (galoisExtension σ a) +
        dist (galoisExtension σ₀ a) (galoisExtension σ₀ x) := h2 ▸ dist_triangle _ _ _
    _ < ε := by linarith

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
  ⟨galoisExtension, fun σ x ↦ galoisExtension_coe σ x, galoisExtension_mul_apply,
    galoisExtension_bijective, continuous_galoisExtension_apply⟩

end CompletedAlgClosure

end TauCeti
