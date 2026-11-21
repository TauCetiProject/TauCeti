/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Artinian.LocalRing
public import TauCeti.RingTheory.MatlisDuality.Finite
import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Matlis duality for Artinian modules

Let `E` be an injective envelope of the residue field of a Noetherian local ring `R`, with
`𝔪`-adic completion `R̂` acting canonically on `E`. Every Artinian `R`-module `M` embeds into a
finite power `E^r` (`TauCeti.exists_injective_linearMap_pi_of_isArtinian`), so injectivity of `E`
presents `Hom_R(M, E)` as a quotient of `Hom_R(E^r, E) ≅ R̂^r`. Combined with the annihilator
order embedding (`TauCeti.matlisAnnihilatorOrderEmbedding`), `M` is Artinian over `R` if and only
if `Hom_R(M, E)` is finitely generated over `R̂`, with no torsion or completeness assumption on `M`
or `R`.

When `R` is complete for its maximal ideal, `Hom_R(M, E)` is finitely generated over `R` whenever
`M` is Artinian, and the canonical evaluation map `M → Hom_R(Hom_R(M, E), E)` is an isomorphism:
surjectivity on `E^r` follows from `End_R(E) ≅ R` (`TauCeti.IsInjectiveEnvelope.exists_eq_smul_id`)
and descends along `M ↪ E^r` via `LinearMap.surjective_applyₗ_of_injective`. Combined with
finite-module biduality, evaluation is bijective on products `M × P` of a finitely generated module
and an Artinian module. No finiteness of the residue field is required.

## Main declarations

* `TauCeti.IsInjectiveEnvelope.finite_adicCompletion_linearMap_of_artinian` and
  `TauCeti.IsInjectiveEnvelope.isArtinian_iff_finite_adicCompletion_linearMap`: over a Noetherian
  local ring `R`, `M` is Artinian over `R` if and only if `Hom_R(M, E)` is finite over `R̂`.
* `TauCeti.IsInjectiveEnvelope.finite_linearMap_of_artinian` and
  `TauCeti.IsInjectiveEnvelope.bijective_applyₗ_of_artinian`: over a complete Noetherian local ring,
  the Matlis dual of an Artinian module is finite and evaluation into the double Matlis dual is
  bijective (`TauCeti.IsInjectiveEnvelope.evalEquivOfArtinian`).
* `TauCeti.IsInjectiveEnvelope.bijective_applyₗ_prod_of_finite_of_artinian`: over a complete
  Noetherian local ring, evaluation into the double Matlis dual is bijective on `M × P` when `M` is
  finitely generated and `P` is Artinian.

## References

* [Stacks Project, Section 47.7](https://stacks.math.columbia.edu/tag/08Z1),
  [Proposition 47.7.8](https://stacks.math.columbia.edu/tag/08Z9), and
  [Remark 47.7.9](https://stacks.math.columbia.edu/tag/0EGL).
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing LinearMap

universe u v w z

namespace IsInjectiveEnvelope

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

/-- A module whose Matlis dual is finite over the completion of a Noetherian local ring is
Artinian. The completion acts on the injective hull through its canonical torsion-module action.
Neither the original ring nor the original module is required to be complete. -/
theorem isArtinian_of_finite_adicCompletion_linearMap {M : Type w} [AddCommGroup M] [Module R M]
    (hfinite : letI := AdicCompletion.torsionModule (fun _ : E ↦
        hι.isEssential_range.primaryComponent_maximalIdeal_eq_top.ge Submodule.mem_top)
      Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E)) :
    IsArtinian R M := by
  let := AdicCompletion.torsionModule (fun _ : E ↦
    hι.isEssential_range.primaryComponent_maximalIdeal_eq_top.ge Submodule.mem_top)
  have := hfinite
  have : IsScalarTower R (_root_.AdicCompletion (maximalIdeal R) R) E :=
    AdicCompletion.torsionModule_isScalarTower _
  have := hι.moduleInjective
  exact isArtinian_of_isNoetherian_linearMap
    (_root_.AdicCompletion (maximalIdeal R) R) hι.injective

/-- Over a Noetherian local ring, the Matlis dual of an Artinian module is finitely generated over
the `𝔪`-adic completion, acting via `TauCeti.AdicCompletion.torsionModule`. Neither completeness of
`R` nor finiteness of the residue field is required. -/
@[stacks 0EGL]
theorem finite_adicCompletion_linearMap_of_artinian (M : Type w) [AddCommGroup M] [Module R M]
    [IsArtinian R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.moduleInjective
  obtain ⟨r, j, hj⟩ := exists_injective_linearMap_pi_of_isArtinian (M := M) hι.injective
  -- Every functional on `E^r` is an `A`-linear combination of coordinate projections.
  let Φ : (Fin r → A) →ₗ[A] ((Fin r → E) →ₗ[R] E) :=
    { toFun s := ∑ i, s i • proj i
      map_add' s₁ s₂ := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' a s := by simp [mul_smul, Finset.smul_sum] }
  have hΦ_apply (s : Fin r → A) : Φ s = ∑ i, s i • proj i := rfl
  have hΦ : Function.Surjective Φ := by
    intro f
    refine ⟨fun i ↦ hι.adicCompletionEquivEnd.symm (f ∘ₗ single R (fun _ : Fin r ↦ E) i), ?_⟩
    apply LinearMap.ext
    intro x
    conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
    rw [hΦ_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.smul_apply, proj_apply, ← hι.adicCompletionEquivEnd_apply hι.mem_primaryComponent,
      AlgEquiv.apply_symm_apply, comp_apply]
    rfl
  have hj_surj : Function.Surjective (j.lcomp A E) := fun g ↦ by
    obtain ⟨g', hg'⟩ := Module.Injective.extension_property R E M (Fin r → E) j hj g
    exact ⟨g', hg'⟩
  exact Module.Finite.of_surjective ((j.lcomp A E) ∘ₗ Φ) (hj_surj.comp hΦ)

/-- Over a Noetherian local ring, an `R`-module is Artinian if and only if its Matlis dual is
finitely generated over the `𝔪`-adic completion. -/
theorem isArtinian_iff_finite_adicCompletion_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsArtinian R M ↔ Module.Finite (_root_.AdicCompletion (maximalIdeal R) R) (M →ₗ[R] E) :=
  ⟨fun _ ↦ hι.finite_adicCompletion_linearMap_of_artinian M,
    hι.isArtinian_of_finite_adicCompletion_linearMap⟩

section Complete

variable [IsAdicComplete (maximalIdeal R) R]

/-- Over a complete Noetherian local ring, the Matlis dual of an Artinian module is finitely
generated. -/
@[stacks 08Z9]
theorem finite_linearMap_of_artinian (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M] :
    Module.Finite R (M →ₗ[R] E) := by
  let A := _root_.AdicCompletion (maximalIdeal R) R
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have : Module.Finite R A := .of_surjective (Algebra.ofId R A).toLinearMap
    (_root_.AdicCompletion.of_bijective (maximalIdeal R) R).surjective
  have : Module.Finite A (M →ₗ[R] E) := hι.finite_adicCompletion_linearMap_of_artinian M
  exact Module.Finite.trans A (M →ₗ[R] E)

/-- Over a complete Noetherian local ring, a module is Artinian if and only if its Matlis dual is
finitely generated. -/
theorem isArtinian_iff_finite_linearMap (M : Type w) [AddCommGroup M] [Module R M] :
    IsArtinian R M ↔ Module.Finite R (M →ₗ[R] E) := by
  refine ⟨fun _ ↦ hι.finite_linearMap_of_artinian M, fun _ ↦ ?_⟩
  have := hι.moduleInjective
  exact isArtinian_of_isNoetherian_linearMap R hι.injective

section

variable (M : Type w) [AddCommGroup M] [Module R M] [IsArtinian R M]

/-- Matlis biduality for Artinian modules over a complete Noetherian local ring: the canonical
evaluation map into the double Matlis dual is bijective. -/
@[stacks 08Z9]
theorem bijective_applyₗ_of_artinian :
    Function.Bijective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  have := hι.moduleInjective
  obtain ⟨r, j, hj⟩ := exists_injective_linearMap_pi_of_isArtinian (M := M) hι.injective
  exact ⟨injective_applyₗ_of_injective hι.injective,
    j.surjective_applyₗ_of_injective hj (injective_applyₗ_of_injective hι.injective)
      (surjective_applyₗ_pi_self_of_end_eq_smul hι.exists_eq_smul_id (Fin r))⟩

/-- Evaluation identifies an Artinian module over a complete Noetherian local ring with its double
Matlis dual. -/
def evalEquivOfArtinian : M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearEquiv.ofBijective applyₗ (hι.bijective_applyₗ_of_artinian M)

@[simp]
theorem evalEquivOfArtinian_apply_apply (m : M) (f : M →ₗ[R] E) :
    hι.evalEquivOfArtinian M m f = f m :=
  (rfl)

@[simp]
theorem evalEquivOfArtinian_symm_apply_apply (φ : (M →ₗ[R] E) →ₗ[R] E) (f : M →ₗ[R] E) :
    f ((hι.evalEquivOfArtinian M).symm φ) = φ f := by
  simpa only [evalEquivOfArtinian_apply_apply] using
    congrArg (fun ψ : (M →ₗ[R] E) →ₗ[R] E ↦ ψ f)
      ((hι.evalEquivOfArtinian M).apply_symm_apply φ)

end

/-- Over a complete Noetherian local ring, evaluation into the double Matlis dual is bijective on
any product `M × P` of a finitely generated module `M` and an Artinian module `P` (such as
`R × E`, which is neither finite nor Artinian when `dim R ≥ 1`). -/
theorem bijective_applyₗ_prod_of_finite_of_artinian
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (P : Type z) [AddCommGroup P] [Module R P] [IsArtinian R P] :
    Function.Bijective (applyₗ : (M × P) →ₗ[R] ((M × P) →ₗ[R] E) →ₗ[R] E) :=
  bijective_applyₗ_prod_iff.mpr ⟨hι.bijective_applyₗ_of_finite M, hι.bijective_applyₗ_of_artinian P⟩

end Complete

end IsInjectiveEnvelope

end TauCeti
