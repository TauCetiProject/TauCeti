/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MatlisDuality.Finite
import TauCeti.Algebra.Module.Dual.Bidual

/-!
# Matlis duality for Artinian modules over a complete local ring

Let `R` be a Noetherian local ring, complete for its maximal ideal, and let `E` be an injective
hull of its residue field, with Matlis dual `D(M) = Hom_R(M, E)`. For an Artinian module `M`, this
file proves that `D(M)` is finitely generated, that evaluation `M → D(D(M))` is bijective, and
that `Hom_R(-, E)` is bijective on morphisms into `M`. With the finitely generated case of
`TauCeti/RingTheory/MatlisDuality/Finite.lean`, the dual exchanges the two classes: `M` is Artinian
exactly when `D(M)` is finitely generated, and finitely generated exactly when `D(M)` is Artinian.
The residue field may be infinite.

Finiteness of `D(M)` is `TauCeti.finite_linearMap_of_isArtinian`, since completeness makes every
endomorphism of `E` a scalar. For biduality, evaluation on `M` is injective because `E` is a
cogenerator. Evaluation on `D(M)` is bijective, by finite biduality, and a functional on
`D(D(M))` vanishing on the image of `M` is evaluation at some `f ∈ D(M)` that vanishes on `M`;
so no nonzero functional vanishes on that image, and evaluation on `M` is surjective.

## Main declarations

* `TauCeti.IsInjectiveEnvelope.finite_linearMap_of_isArtinian`: the dual of an Artinian module is
  finitely generated.
* `TauCeti.IsInjectiveEnvelope.bijective_applyₗ_of_isArtinian` and
  `TauCeti.IsInjectiveEnvelope.evalEquivOfIsArtinian`: biduality for Artinian modules.
* `TauCeti.IsInjectiveEnvelope.bijective_lcomp_of_isArtinian`: `Hom_R(-, E)` is bijective on
  morphisms into any Artinian module.
* `TauCeti.IsInjectiveEnvelope.isArtinian_iff_finite_linearMap` and
  `TauCeti.IsInjectiveEnvelope.finite_iff_isArtinian_linearMap`: the dual exchanges Artinian and
  finitely generated modules.

## References

* The Stacks Project, Proposition 47.7.8, Tag 08Z9.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 3.2.13.
-/

public section

noncomputable section

universe u v w z

namespace TauCeti.IsInjectiveEnvelope

open IsLocalRing LinearMap

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)
  (M : Type w) [AddCommGroup M] [Module R M]

include hι

/-- The Matlis dual of an Artinian module over a complete Noetherian local ring is finitely
generated. -/
theorem finite_linearMap_of_isArtinian [IsArtinian R M] : Module.Finite R (M →ₗ[R] E) := by
  have := hι.moduleInjective
  have := hι.finite_end
  exact TauCeti.finite_linearMap_of_isArtinian R hι.injective

/-- **Matlis biduality for Artinian modules** over a complete Noetherian local ring: the canonical
evaluation map is bijective. -/
theorem bijective_applyₗ_of_isArtinian [IsArtinian R M] :
    Function.Bijective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have := hι.moduleInjective
  have := hι.finite_linearMap_of_isArtinian M
  refine ⟨injective_applyₗ_of_injective hι.injective, fun Ψ ↦ ?_⟩
  by_contra hΨ
  -- A functional `φ` on the double dual vanishing on the image of `M` but not at `Ψ`.
  obtain ⟨φ, hφ, hφN⟩ := exists_apply_ne_zero_of_notMem
    (nontrivial_quotient_linearMap_of_injective hι.injective)
    (N := range (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E)) (m := Ψ) fun h ↦ hΨ (mem_range.mp h)
  -- By biduality for the finite module `D(M)`, `φ` is evaluation at some `f`, and `f = 0`.
  obtain ⟨f, hf⟩ := (hι.bijective_applyₗ_of_finite (M →ₗ[R] E)).2 φ
  have hf0 : f = 0 := LinearMap.ext fun m ↦ by
    simpa [hφN _ (mem_range_self _ m)] using LinearMap.congr_fun hf (applyₗ m)
  exact hφ (by simpa [hf0] using (LinearMap.congr_fun hf Ψ).symm)

/-- Evaluation identifies an Artinian module over a complete Noetherian local ring with its double
Matlis dual. -/
def evalEquivOfIsArtinian [IsArtinian R M] : M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective applyₗ (hι.bijective_applyₗ_of_isArtinian M)

/-- Biduality for Artinian modules is evaluation. -/
@[simp]
theorem evalEquivOfIsArtinian_apply_apply [IsArtinian R M] (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivOfIsArtinian M m f = f m := (rfl)

/-- The inverse of biduality for Artinian modules sends a functional on the dual to the element at
which it evaluates. -/
@[simp]
theorem evalEquivOfIsArtinian_symm_apply_apply [IsArtinian R M] (φ : (M →ₗ[R] E) →ₗ[R] E)
    (f : M →ₗ[R] E) : f ((hι.evalEquivOfIsArtinian M).symm φ) = φ f := by
  simpa only [evalEquivOfIsArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivOfIsArtinian M).apply_symm_apply φ)

/-- Over a complete Noetherian local ring, a module is Artinian exactly when its Matlis dual is
finitely generated. -/
theorem isArtinian_iff_finite_linearMap : IsArtinian R M ↔ Module.Finite R (M →ₗ[R] E) := by
  have := hι.moduleInjective
  exact ⟨fun _ ↦ hι.finite_linearMap_of_isArtinian M,
    fun _ ↦ isArtinian_of_isNoetherian_linearMap R hι.injective⟩

/-- Over a complete Noetherian local ring, a module is finitely generated exactly when its Matlis
dual is Artinian. -/
theorem finite_iff_isArtinian_linearMap : Module.Finite R M ↔ IsArtinian R (M →ₗ[R] E) := by
  have := hι.moduleInjective
  refine ⟨fun _ ↦ hι.isArtinian_linearMap_of_finite M, fun _ ↦ ?_⟩
  -- `M` embeds by evaluation into its double dual, which is finitely generated.
  have := hι.finite_linearMap_of_isArtinian (M →ₗ[R] E)
  exact Module.Finite.of_injective _ (injective_applyₗ_of_injective (M := M) hι.injective)

/-- `evalEquivOfIsArtinian` is natural with respect to `R`-linear maps. -/
@[simp]
theorem lcomp_lcomp_evalEquivOfIsArtinian {M : Type w} [AddCommGroup M] [Module R M]
    [IsArtinian R M] {N : Type z} [AddCommGroup N] [Module R N] [IsArtinian R N]
    (f : M →ₗ[R] N) (m : M) :
    (f.lcomp R E).lcomp R E (hι.evalEquivOfIsArtinian M m) =
      hι.evalEquivOfIsArtinian N (f m) := by
  ext g
  simp

/-- Over a complete Noetherian local ring, Matlis duality is bijective on morphisms into any
Artinian module. -/
theorem bijective_lcomp_of_isArtinian
    (N : Type z) [AddCommGroup N] [Module R N] [IsArtinian R N] :
    Function.Bijective (fun f : M →ₗ[R] N ↦ f.lcomp R E) :=
  bijective_lcomp_of_bijective_applyₗ (hι.bijective_applyₗ_of_isArtinian N)

end TauCeti.IsInjectiveEnvelope
