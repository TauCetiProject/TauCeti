/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Bidual
public import TauCeti.RingTheory.MatlisDuality.Artinian
public import TauCeti.RingTheory.MatlisDuality.Endomorphism

/-!
# Matlis duality for finitely generated modules

Let `R` be a Noetherian local ring and `E` an injective hull of its residue field.
The hull and the Matlis dual `Hom_R(M, E)` of every finitely generated `R`-module `M`
are Artinian. If `R` is complete, evaluation identifies `M` with its double Matlis dual.
The residue field may be infinite.

Completeness identifies the existing endomorphism algebra `End_R(E) ≅ R̂` with `R`.
Surjectivity of evaluation then follows from finite free covers and injectivity of `E`;
injectivity follows from the cogenerator property. Artinianness of the hull follows from
the annihilator embedding and Noetherianity of its endomorphisms over the completion;
the dual of a finite module embeds in a finite power of the hull.

## References

* The Stacks Project, Lemma 47.7.6 and Proposition 47.7.8, Tags 08Z7 and 08Z9.
-/

public section

noncomputable section

universe u v w

namespace TauCeti.IsInjectiveEnvelope

open IsLocalRing LinearMap

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

/-- The injective hull of the residue field of a Noetherian local ring is Artinian.
The ring need not be complete. -/
theorem isArtinian : IsArtinian R E := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  let f := LinearMap.toSpanSingleton (_root_.AdicCompletion (maximalIdeal R) R)
    (Module.End R E) LinearMap.id
  have hf : Function.Surjective f := by
    intro φ
    refine ⟨hι.adicCompletionEquivEnd.symm φ, LinearMap.ext fun x ↦ ?_⟩
    simpa [f] using
      (hι.adicCompletionEquivEnd_apply hι.mem_primaryComponent
        (hι.adicCompletionEquivEnd.symm φ) x).symm
  have := Module.Finite.of_surjective f hf
  exact hι.isArtinian_of_finite_adicCompletion_linearMap inferInstance

/-- The Matlis dual of a finitely generated module over a Noetherian local ring is Artinian.
Completeness and finiteness of the residue field are unnecessary. -/
theorem isArtinian_linearMap_of_finite (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsArtinian R (M →ₗ[R] E) := by
  classical
  have := hι.isArtinian
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let e := LinearEquiv.piRing R E (Fin n) R
  exact isArtinian_of_injective (e.toLinearMap.comp (f.lcomp R E))
    (e.injective.comp (LinearMap.lcomp_injective_of_surjective f hf))

variable [IsAdicComplete (maximalIdeal R) R]

variable (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Matlis biduality for finitely generated modules over a complete Noetherian local ring:
the canonical evaluation map is bijective. -/
theorem bijective_applyₗ_of_finite :
    Function.Bijective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have := hι.moduleInjective
  exact ⟨injective_applyₗ_of_injective hι.injective,
    surjective_applyₗ_of_finite_of_end_eq_smul hι.exists_eq_smul_id M⟩

/-- Evaluation identifies a finitely generated module over a complete Noetherian local ring
with its double Matlis dual. -/
def evalEquivOfFinite : M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective applyₗ (hι.bijective_applyₗ_of_finite M)

@[simp]
theorem evalEquivOfFinite_apply_apply (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivOfFinite M m f = f m := (rfl)

@[simp]
theorem evalEquivOfFinite_symm_apply_apply (φ : (M →ₗ[R] E) →ₗ[R] E) (f : M →ₗ[R] E) :
    f ((hι.evalEquivOfFinite M).symm φ) = φ f := by
  simpa only [evalEquivOfFinite_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivOfFinite M).apply_symm_apply φ)

end TauCeti.IsInjectiveEnvelope
