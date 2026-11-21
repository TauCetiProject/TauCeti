/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Evaluation into a double Hom

For an injective module `E`, surjectivity of the evaluation map into the double `E`-dual
passes to quotients. If every endomorphism of `E` is scalar, evaluation is surjective for
finite free modules, and hence for every finitely generated module. Together with a
cogenerator condition, this gives biduality without requiring the original module to be
projective. The principal application is Matlis duality over a complete local ring.

The argument uses Mathlib's `LinearEquiv.piRing` to identify the dual of a finite free
module, and `Module.Injective.extension_property` to dualize an injection.

## References

* The Stacks Project, Proposition 47.7.8, Matlis duality, Tag 08Z9.
-/

public section

noncomputable section

universe u v w z

namespace LinearMap

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type z} [AddCommGroup N] [Module R N]

/-- Surjectivity of evaluation into the double dual with injective coefficients passes to
quotients. -/
theorem surjective_applyₗ_of_surjective [Small.{v} R] [Module.Injective R E]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hM : Function.Surjective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E)) :
    Function.Surjective (applyₗ : N →ₗ[R] (N →ₗ[R] E) →ₗ[R] E) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := Module.Injective.extension_property R E _ _ (f.lcomp R E)
    (lcomp_injective_of_surjective f hf) φ
  obtain ⟨m, hm⟩ := hM ψ
  refine ⟨f m, LinearMap.ext fun g ↦ ?_⟩
  have h := LinearMap.congr_fun hψ g
  simpa [← hm] using h

end LinearMap

namespace TauCeti

open LinearMap

section Semiring

variable {R : Type u} [CommSemiring R] {E : Type v} [AddCommMonoid E] [Module R E]

/-- If every endomorphism of `E` is scalar, evaluation into the double `E`-dual of a finite
free module is surjective. -/
theorem surjective_applyₗ_pi_of_end_eq_smul
    (hE : ∀ f : Module.End R E, ∃ r : R, f = r • LinearMap.id)
    (ι : Type*) [Finite ι] :
    Function.Surjective (applyₗ : (ι → R) →ₗ[R] ((ι → R) →ₗ[R] E) →ₗ[R] E) := by
  classical
  let := Fintype.ofFinite ι
  intro φ
  let e := LinearEquiv.piRing R E ι R
  let ψ := φ.comp e.symm.toLinearMap
  choose r hr using fun i ↦ hE (ψ.comp (LinearMap.single R (fun _ : ι ↦ E) i))
  refine ⟨r, LinearMap.ext fun f ↦ ?_⟩
  have hψ : ψ (e f) = ∑ i, r i • e f i := by
    conv_lhs => rw [← Finset.univ_sum_single (e f), map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ LinearMap.congr_fun (hr i) (e f i)
  have hf : f r = ∑ i, r i • e f i := by
    simpa only [e, LinearEquiv.piRing_symm_apply] using
      congrArg (fun g : (ι → R) →ₗ[R] E ↦ g r) (e.symm_apply_apply f).symm
  simpa only [LinearMap.applyₗ_apply_apply] using
    hf.trans (by simpa [ψ] using hψ.symm)

end Semiring

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- If `E` is injective and every endomorphism of `E` is scalar, every finitely generated
module maps surjectively onto its double `E`-dual by evaluation. -/
theorem surjective_applyₗ_of_finite_of_end_eq_smul [Small.{v} R] [Module.Injective R E]
    (hE : ∀ f : Module.End R E, ∃ r : R, f = r • LinearMap.id)
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (applyₗ : M →ₗ[R] (M →ₗ[R] E) →ₗ[R] E) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact f.surjective_applyₗ_of_surjective hf (surjective_applyₗ_pi_of_end_eq_smul hE (Fin n))

end TauCeti
