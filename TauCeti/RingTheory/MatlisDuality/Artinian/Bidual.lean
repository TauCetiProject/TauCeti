/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MatlisDuality.Artinian.Basic
public import TauCeti.RingTheory.MatlisDuality.Finite
import TauCeti.Algebra.Module.Dual.Bidual

/-!
# Matlis biduality for Artinian modules over a complete local ring

Let `R` be a complete Noetherian local ring with injective hull `E` of its residue field `κ`.
Combining finite-module biduality (`TauCeti.RingTheory.MatlisDuality.Finite`) with the
Artinian dual-finiteness results (`TauCeti.RingTheory.MatlisDuality.Artinian.Basic`) yields:
- `Hom_R(M, E)` is Artinian iff `M` is finitely generated over `R`
  (`TauCeti.IsInjectiveEnvelope.isArtinian_linearMap_iff_finite`);
- evaluation `M → Hom_R(Hom_R(M, E), E)` is bijective for every Artinian `R`-module `M`
  (`TauCeti.IsInjectiveEnvelope.bijective_applyₗ_of_isArtinian`,
  `TauCeti.IsInjectiveEnvelope.evalEquivOfIsArtinian`);
- `Hom_R(-, E)` is bijective on morphisms into any Artinian `R`-module
  (`TauCeti.IsInjectiveEnvelope.bijective_lcomp_of_isArtinian`).

## References

* The Stacks Project, Proposition 47.7.8, Tag 08Z9.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Theorem 3.2.13.
-/

public section

noncomputable section

namespace TauCeti.IsInjectiveEnvelope

open IsLocalRing LinearMap

universe u v w z

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)
  [IsAdicComplete (maximalIdeal R) R]

include hι

/-- Over a complete Noetherian local ring, the Matlis dual of a module is Artinian iff the module
is finitely generated over `R`. -/
theorem isArtinian_linearMap_iff_finite (M : Type w) [AddCommGroup M] [Module R M] :
    IsArtinian R (M →ₗ[R] E) ↔ Module.Finite R M := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ hι.isArtinian_linearMap_of_finite M⟩
  have := hι.moduleInjective
  have : Module.Finite R ((M →ₗ[R] E) →ₗ[R] E) := hι.finite_linearMap_of_isArtinian (M →ₗ[R] E)
  have : IsNoetherian R M :=
    isNoetherian_of_injective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E)
      (injective_applyₗ_of_injective hι.injective)
  exact Module.finite_def.mpr (IsNoetherian.noetherian (⊤ : Submodule R M))

/-- **Matlis biduality for Artinian modules over a complete Noetherian local ring**: the canonical
evaluation map `M → Hom_R(Hom_R(M, E), E)` is bijective. -/
theorem bijective_applyₗ_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    Function.Bijective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have := hι.moduleInjective
  refine ⟨injective_applyₗ_of_injective hι.injective, fun φ ↦ ?_⟩
  -- It suffices to show that the cokernel `C` of `applyₗ` admits no nonzero map to `E`.
  let K := LinearMap.range (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E)
  have hzero : ∀ g : (((M →ₗ[R] E) →ₗ[R] E) ⧸ K) →ₗ[R] E, g = 0 := fun g ↦ by
    have : Module.Finite R (M →ₗ[R] E) := hι.finite_linearMap_of_isArtinian M
    obtain ⟨f, hf⟩ := (hι.bijective_applyₗ_of_finite (M →ₗ[R] E)).2 (g.comp K.mkQ)
    have hf0 : f = 0 := LinearMap.ext fun m ↦ by
      have hm := LinearMap.congr_fun hf (applyₗ m)
      have hmem : applyₗ m ∈ K := ⟨m, rfl⟩
      simpa only [applyₗ_apply_apply, comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
        (Submodule.Quotient.mk_eq_zero K).mpr hmem, map_zero] using hm
    refine LinearMap.ext fun y ↦ ?_
    obtain ⟨ψ, rfl⟩ := K.mkQ_surjective y
    have hψ := LinearMap.congr_fun hf ψ
    simpa [hf0] using hψ.symm
  have hq : K.mkQ φ = 0 :=
    (injective_iff_map_eq_zero _).mp (injective_applyₗ_of_injective hι.injective) (K.mkQ φ)
      (LinearMap.ext fun g ↦ by simp [hzero g])
  exact (Submodule.Quotient.mk_eq_zero K).mp hq

/-- Evaluation identifies an Artinian module over a complete Noetherian local ring with its double
Matlis dual. -/
def evalEquivOfIsArtinian (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective applyₗ (hι.bijective_applyₗ_of_isArtinian M)

@[simp]
theorem evalEquivOfIsArtinian_apply_apply (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivOfIsArtinian M m f = f m := (rfl)

@[simp]
theorem evalEquivOfIsArtinian_symm_apply_apply (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] (φ : (M →ₗ[R] E) →ₗ[R] E) (f : M →ₗ[R] E) :
    f ((hι.evalEquivOfIsArtinian M).symm φ) = φ f := by
  simpa only [evalEquivOfIsArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[R] E ↦ ψ f) ((hι.evalEquivOfIsArtinian M).apply_symm_apply φ)

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
theorem bijective_lcomp_of_isArtinian (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type z) [AddCommGroup N] [Module R N] [IsArtinian R N] :
    Function.Bijective (fun f : M →ₗ[R] N ↦ f.lcomp R E) :=
  bijective_lcomp_of_bijective_applyₗ (hι.bijective_applyₗ_of_isArtinian N)

end TauCeti.IsInjectiveEnvelope
